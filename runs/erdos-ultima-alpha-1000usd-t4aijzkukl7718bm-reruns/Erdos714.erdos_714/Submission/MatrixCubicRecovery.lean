import FormalConjecturesUtil

/-!
A verified cubic recovery argument for independent matrix constraints, and
its limitation as a full-rank-only construction strategy. These theorems
neither prove nor disprove Erdős 714.
-/

open Polynomial SimpleGraph

namespace Erdos714MatrixCubicRecovery

variable {F : Type*} [Field F]

abbrev M := Matrix (Fin 2) (Fin 2) F

/-- The mixed coefficient of the determinant of a matrix pencil. -/
def mixed (A B : M (F := F)) : F :=
  A 0 0 * B 1 1 + B 0 0 * A 1 1 - A 0 1 * B 1 0 - B 0 1 * A 1 0

lemma pencil_det (A B : M (F := F)) (t : F) :
    (t • A + B).det = A.det*t^2 + mixed A B*t + B.det := by
  simp [Matrix.det_fin_two, mixed, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The constant term is always -1, so this eliminant cannot vanish identically. -/
noncomputable def cubic (A B : M (F := F)) : F[X] :=
  C A.det * X^3 + C (mixed A B) * X^2 + C B.det * X - 1

lemma eval_cubic (A B : M (F := F)) (t : F) :
    (cubic A B).eval t = t*(t • A+B).det-1 := by
  simp [cubic, pencil_det]
  ring

lemma cubic_ne_zero (A B : M (F := F)) : cubic A B ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval (0 : F)) h
  simpa [cubic] using he

lemma cubic_degree (A B : M (F := F)) : (cubic A B).natDegree ≤ 3 := by
  unfold cubic
  compute_degree!

lemma recover (e : M (F := F) ≃ₗ[F] (Fin 4 → F))
    (u v : Fin 4 → F) (H : M (F := F))
    (he : e H = H.det^2 • u + H.det • v) :
    H = H.det^2 • e.symm u + H.det • e.symm v := by
  calc
    H = e.symm (e H) := (e.symm_apply_apply H).symm
    _ = H.det^2 • e.symm u + H.det • e.symm v := by
      rw [he, map_add, map_smul, map_smul]

lemma determinant_is_root (A B H : M (F := F)) (hD : H.det ≠ 0)
    (hH : H = H.det^2 • A + H.det • B) :
    (cubic A B).eval H.det = 0 := by
  have hp : H = H.det • (H.det • A + B) := by
    calc
      H = H.det^2 • A + H.det • B := hH
      _ = H.det • (H.det • A + B) := by
        simp only [smul_add, smul_smul, pow_two]
  have hd : H.det^2 * (H.det • A+B).det = H.det := by
    calc
      H.det^2 * (H.det • A+B).det = (H.det • (H.det • A+B)).det := by
        rw [Matrix.det_smul]
        simp only [Fintype.card_fin]
      _ = H.det := congrArg Matrix.det hp.symm
  apply (mul_eq_zero.mp (show H.det * (cubic A B).eval H.det = 0 from ?_)).resolve_left hD
  rw [eval_cubic]
  linear_combination hd

/-- Both recovery and the nonzero eliminant are proved, not assumed from a generic degree count. -/
theorem solution_card_le_three
    (e : M (F := F) ≃ₗ[F] (Fin 4 → F)) (u v : Fin 4 → F)
    (S : Finset (M (F := F)))
    (hS : ∀ H ∈ S, H.det ≠ 0 ∧ e H = H.det^2 • u + H.det • v) :
    S.card ≤ 3 := by
  classical
  let A := e.symm u
  let B := e.symm v
  have hrec (H : M (F := F)) (hH : H ∈ S) :
      H = H.det^2 • A + H.det • B := recover e u v H (hS H hH).2
  have hi : Set.InjOn Matrix.det (S : Set (M (F := F))) := by
    intro H hH J hJ hdet
    rw [hrec H hH, hrec J hJ, hdet]
  have hsub : S.image Matrix.det ⊆ (cubic A B).roots.toFinset := by
    intro t ht
    obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp ht
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (cubic_ne_zero A B)]
    exact determinant_is_root A B H (hS H hH).1 (hrec H hH)
  calc
    S.card = (S.image Matrix.det).card := (Finset.card_image_of_injOn hi).symm
    _ ≤ (cubic A B).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ (cubic A B).roots.card := Multiset.toFinset_card_le _
    _ ≤ (cubic A B).natDegree := Polynomial.card_roots' _
    _ ≤ 3 := cubic_degree A B

/-- The row matrices specify the actual trace constraints. -/
def constraintMap (R : Fin 4 → M (F := F)) : M (F := F) →ₗ[F] (Fin 4 → F) where
  toFun H i := (R i * H).trace
  map_add' := by
    intro H J
    ext i
    simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' := by
    intro a H
    ext i
    simp [Matrix.mul_smul, Matrix.trace_smul]

/-- Apply the cubic argument to trace equals determinant-squared plus determinant. -/
theorem trace_det_common_bound (R : Fin 4 → M (F := F))
    (he : Function.Bijective (constraintMap R)) (S : Finset (M (F := F)))
    (hS : ∀ H ∈ S, H.det ≠ 0 ∧ ∀ i,
      (R i * H).trace = (R i * H).det^2 + (R i * H).det) : S.card ≤ 3 := by
  let e := LinearEquiv.ofBijective (constraintMap R) he
  apply solution_card_le_three e (fun i => (R i).det^2) (fun i => (R i).det) S
  intro H hH
  refine ⟨(hS H hH).1, ?_⟩
  ext i
  change (R i * H).trace = H.det^2 * (R i).det^2 + H.det * (R i).det
  rw [(hS H hH).2 i, Matrix.det_mul]
  ring

/-- Four matrices with the same first row cannot give four independent trace constraints. -/
lemma same_first_row_not_injective (R : Fin 4 → M (F := F)) (a b : F)
    (ha : ∀ i, R i 0 0 = a) (hb : ∀ i, R i 0 1 = b) :
    ¬ Function.Injective (constraintMap R) := by
  intro hinj
  by_cases ha0 : a = 0
  · by_cases hb0 : b = 0
    · let H : M (F := F) := !![1,0;0,0]
      have he : constraintMap R H = constraintMap R 0 := by
        ext i
        simp [constraintMap, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, H, ha, ha0]
      have hzero := congrArg (fun H : M (F := F) => H 0 0) (hinj he)
      simpa [H] using hzero
    · let H : M (F := F) := !![b,0;-a,0]
      have he : constraintMap R H = constraintMap R 0 := by
        ext i
        simp [constraintMap, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, H, ha, hb]
      <;> ring
      have hzero := congrArg (fun H : M (F := F) => H 0 0) (hinj he)
      exact hb0 (by simpa [H] using hzero)
  · let H : M (F := F) := !![b,0;-a,0]
    have he : constraintMap R H = constraintMap R 0 := by
      ext i
      simp [constraintMap, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, H, ha, hb]
      <;> ring
    have hzero := congrArg (fun H : M (F := F) => H 1 0) (hinj he)
    apply ha0
    simpa [H] using hzero

/-- A full-rank-only row family has at most 3*q² members, far short of q⁴. -/
theorem independent_rows_card_bound {V : Type*} [Fintype V] [Fintype F]
    (R : V → M (F := F))
    (hR : ∀ f : Fin 4 ↪ V, Function.Injective (constraintMap (fun i => R (f i)))) :
    Fintype.card V ≤ 3 * Fintype.card F^2 := by
  classical
  by_contra! hn
  let obs (v : V) : F × F := (R v 0 0, R v 0 1)
  obtain ⟨p, hp⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card obs (n := 3) (by
    simpa only [Fintype.card_prod, pow_two, mul_comm] using hn)
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 4) (s := Finset.univ.filter (fun v => obs v = p)) (by
      simp only [Fintype.card_fin]
      omega)
  have hobs (i : Fin 4) : obs (f i) = p := (Finset.mem_filter.mp (hf ⟨i, rfl⟩)).2
  exact same_first_row_not_injective (fun i => R (f i)) p.1 p.2
    (fun i => congrArg Prod.fst (hobs i)) (fun i => congrArg Prod.snd (hobs i)) (hR f)

#print axioms cubic_ne_zero
#print axioms solution_card_le_three
#print axioms trace_det_common_bound
#print axioms same_first_row_not_injective
#print axioms independent_rows_card_bound

end Erdos714MatrixCubicRecovery
