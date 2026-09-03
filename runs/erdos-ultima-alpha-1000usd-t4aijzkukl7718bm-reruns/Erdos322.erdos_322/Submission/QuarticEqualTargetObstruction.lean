import Submission.QuarticBilinearObstruction

/-! Equal-target multilinear norm formulas still imply forbidden generic
quartic norm products. This does not bound the representation count. -/
namespace Erdos322Research.QuarticEqualTarget

private def qnorm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := ∑ i, x i^4

private lemma qnorm_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ qnorm x := by
  unfold qnorm
  positivity

private lemma qnorm_eq_zero {ι : Type*} [Fintype ι] {x : ι → ℝ} :
    qnorm x=0 ↔ x=0 := by
  constructor
  · intro h
    funext i
    have hh := Finset.single_le_sum (f := fun i ↦ x i^4)
      (fun _ _ ↦ by positivity) (Finset.mem_univ i)
    change x i^4 ≤ qnorm x at hh
    rw [h] at hh
    exact eq_zero_of_pow_eq_zero (le_antisymm hh (by positivity))
  · rintro rfl
    simp [qnorm]

private lemma qnorm_smul {ι : Type*} [Fintype ι] (c : ℝ) (x : ι → ℝ) :
    qnorm (c • x)=c^4*qnorm x := by
  simp only [qnorm,Pi.smul_apply,smul_eq_mul,mul_pow,Finset.mul_sum]

/-- For a multilinear map, a product formula on equal-norm inputs already
implies the full product formula on unrestricted inputs. -/
theorem equal_target_extends_to_product
    {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (F : MultilinearMap ℝ (fun _ : ι ↦ κ → ℝ) (ν → ℝ))
    (h : ∀ (x : ι → κ → ℝ) (n : ℝ),
      (∀ j, ∑ i, x j i^4=n) → ∑ i, F x i^4=n^(Fintype.card ι)) :
    ∀ x : ι → κ → ℝ, ∑ i, F x i^4=∏ j, (∑ i, x j i^4) := by
  classical
  intro x
  change qnorm (F x)=∏ j, qnorm (x j)
  by_cases hz : ∃ j, x j=0
  · obtain ⟨j,hj⟩ := hz
    rw [F.map_coord_zero j hj]
    have hp : ∏ j, qnorm (x j)=0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (qnorm_eq_zero.mpr hj)
    rw [hp]
    simp [qnorm]
  · have hx (j : ι) : 0 < qnorm (x j) := by
      apply lt_of_le_of_ne (qnorm_nonneg _)
      intro he
      exact hz ⟨j,qnorm_eq_zero.mp he.symm⟩
    let c (j : ι) := Real.sqrt (Real.sqrt (qnorm (x j)))
    have hc (j : ι) : 0 < c j := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (hx j))
    have hpow (j : ι) : c j^4=qnorm (x j) := by
      change (Real.sqrt (Real.sqrt (qnorm (x j))))^4=_
      calc
        (Real.sqrt (Real.sqrt (qnorm (x j))))^4 =
            ((Real.sqrt (Real.sqrt (qnorm (x j))))^2)^2 := by ring
        _ = qnorm (x j) := by
          rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (qnorm_nonneg _)]
    let y (j : ι) := (c j)⁻¹ • x j
    have hy (j : ι) : qnorm (y j)=1 := by
      dsimp [y]
      rw [qnorm_smul,inv_pow,hpow]
      exact inv_mul_cancel₀ (hx j).ne'
    have hyF : qnorm (F y)=1 := by
      have hh := h y 1 hy
      simpa only [one_pow] using hh
    have hxy : x = fun j ↦ c j • y j := by
      funext j
      simp [y,smul_smul,(hc j).ne']
    calc
      qnorm (F x) = qnorm (F (fun j ↦ c j • y j)) := by rw [←hxy]
      _ = qnorm ((∏ j, c j) • F y) := by rw [F.map_smul_univ]
      _ = (∏ j, c j)^4 := by rw [qnorm_smul,hyF,mul_one]
      _ = ∏ j, qnorm (x j) := by rw [← Finset.prod_pow]; simp only [hpow]

private def basisVector (j : Fin 4) : Fin 4 → ℝ := fun i ↦ if i=j then 1 else 0

private lemma basisVector_norm (j : Fin 4) : ∑ i, basisVector j i^4=1 := by
  simp [basisVector]

private lemma basis_expansion (x : Fin 4 → ℝ) : x=∑ j, x j • basisVector j := by
  funext i
  simp [basisVector]

private lemma first_expansion
    (F : MultilinearMap ℝ (fun _ : Fin 4 ↦ Fin 4 → ℝ) (Fin 4 → ℝ))
    (x y z w : Fin 4 → ℝ) :
    F ![x,y,z,w] = ∑ j, x j • F ![basisVector j,y,z,w] := by
  calc
    F ![x,y,z,w] = (F.curryLeft (∑ j, x j • basisVector j)) ![y,z,w] := by
      rw [← basis_expansion x]
      rfl
    _ = ∑ j, x j • F ![basisVector j,y,z,w] := by
      simp only [map_sum,map_smul,MultilinearMap.sum_apply,MultilinearMap.smul_apply]
      rfl

private lemma second_expansion
    (F : MultilinearMap ℝ (fun _ : Fin 4 ↦ Fin 4 → ℝ) (Fin 4 → ℝ))
    (x y z w : Fin 4 → ℝ) :
    F ![x,y,z,w] = ∑ j, y j • F ![x,basisVector j,z,w] := by
  calc
    F ![x,y,z,w] = ((F.curryLeft x).curryLeft (∑ j, y j • basisVector j)) ![z,w] := by
      rw [← basis_expansion y]
      rfl
    _ = ∑ j, y j • F ![x,basisVector j,z,w] := by
      simp only [map_sum,map_smul,MultilinearMap.sum_apply,MultilinearMap.smul_apply]
      rfl

/-- Four equal-target inputs cannot be compressed into four output coordinates
by a multilinear map with the critical fourth-power target growth. -/
theorem no_four_input_equal_target_formula
    (F : MultilinearMap ℝ (fun _ : Fin 4 ↦ Fin 4 → ℝ) (Fin 4 → ℝ)) :
    ¬ (∀ (x : Fin 4 → Fin 4 → ℝ) (n : ℝ),
      (∀ j, ∑ i, x j i^4=n) → ∑ i, F x i^4=n^4) := by
  intro h
  have hp := equal_target_extends_to_product F (by simpa using h)
  let M (i j l : Fin 4) := F ![basisVector j,basisVector l,basisVector 0,basisVector 0] i
  apply QuarticBilinear.no_four_coordinate_product M
  intro x y
  have he (i : Fin 4) : F ![x,y,basisVector 0,basisVector 0] i =
      ∑ j, ∑ l, M i j l*x j*y l := by
    have hh := first_expansion F x y (basisVector 0) (basisVector 0)
    rw [hh]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    have hl := second_expansion F (basisVector j) y (basisVector 0) (basisVector 0)
    rw [hl]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    dsimp only [M]
    ring
  have hh := hp ![x,y,basisVector 0,basisVector 0]
  simp only [Fin.prod_univ_four] at hh
  change (∑ i, F ![x,y,basisVector 0,basisVector 0] i^4) =
    (∑ i, x i^4)*(∑ i, y i^4)*(∑ i, basisVector 0 i^4)*(∑ i, basisVector 0 i^4) at hh
  rw [basisVector_norm,mul_one,mul_one] at hh
  simpa only [he] using hh

end Erdos322Research.QuarticEqualTarget
