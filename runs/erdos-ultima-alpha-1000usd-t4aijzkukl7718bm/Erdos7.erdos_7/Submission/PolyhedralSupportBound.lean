import Submission.PositiveLPDirection

/-! A support bound for vertices of a finite nonnegative linear polyhedron.
This is a general auxiliary theorem, not an odd-cover obstruction. -/
namespace Erdos7PolyhedralSupportBound
open scoped BigOperators
open Erdos7PositiveLPDirection
set_option autoImplicit false

noncomputable def feasible {I E J : Type*} [Fintype J]
    (A : I → J → ℝ) (b : I → ℝ) (L : E → J → ℝ) (c : E → ℝ) : Set (J → ℝ) :=
  {x | (∀ j, 0 ≤ x j) ∧ (∀ i, row (A i) x ≤ b i) ∧ (∀ e, row (L e) x = c e)}

/-- Directions annihilating every active constraint can be followed in both
signs for some common positive step. -/
theorem symmetric_feasible_step {I E J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℝ) (b : I → ℝ) (L : E → J → ℝ) (c : E → ℝ)
    (x d : J → ℝ) (hx : x ∈ feasible A b L c)
    (hz : ∀ j, x j = 0 → d j = 0)
    (ha : ∀ i, row (A i) x = b i → row (A i) d = 0)
    (he : ∀ e, row (L e) d = 0) :
    ∃ ε : ℝ, 0 < ε ∧
      (fun j => x j + ε * d j) ∈ feasible A b L c ∧
      (fun j => x j - ε * d j) ∈ feasible A b L c := by
  classical
  let v : J ⊕ I → ℝ := Sum.elim x (fun i => b i - row (A i) x)
  let w : J ⊕ I → ℝ := Sum.elim (fun j => -|d j|) (fun i => -|row (A i) d|)
  have hv : ∀ k, 0 ≤ v k := by
    rintro (j | i)
    · exact hx.1 j
    · exact sub_nonneg.mpr (hx.2.1 i)
  have hw : ∀ k, v k = 0 → 0 ≤ w k := by
    rintro (j | i) hk
    · have h := hz j hk
      simp [w, h]
    · have h : row (A i) x = b i := by
        change b i - row (A i) x = 0 at hk
        linarith
      simp [w, ha i h]
  obtain ⟨ε, hε, hp⟩ := exists_positive_step v w hv hw
  have hn (j : J) : 0 ≤ x j - ε * |d j| := by
    simpa [v, w] using hp (.inl j)
  have hr (i : I) : ε * |row (A i) d| ≤ b i - row (A i) x := by
    have h := hp (.inr i)
    simp only [v, w, Sum.elim_inr, mul_neg] at h
    linarith
  have hplus : (fun j => x j + ε * d j) ∈ feasible A b L c := by
    refine ⟨fun j => ?_, fun i => ?_, fun e => ?_⟩
    · have h := mul_le_mul_of_nonneg_left (neg_abs_le (d j)) hε.le
      linarith [hn j]
    · rw [row_step]
      have h := mul_le_mul_of_nonneg_left (le_abs_self (row (A i) d)) hε.le
      linarith [hr i]
    · rw [row_step, he, mul_zero, add_zero]
      exact hx.2.2 e
  have hminus : (fun j => x j - ε * d j) ∈ feasible A b L c := by
    have hstep (a : J → ℝ) : row a (fun j => x j - ε * d j) =
        row a x - ε * row a d := by
      convert row_step a x d (-ε) using 1 <;> simp [sub_eq_add_neg]
    refine ⟨fun j => ?_, fun i => ?_, fun e => ?_⟩
    · have h := mul_le_mul_of_nonneg_left (le_abs_self (d j)) hε.le
      linarith [hn j]
    · rw [hstep]
      have h := mul_le_mul_of_nonneg_left (neg_abs_le (row (A i) d)) hε.le
      linarith [hr i]
    · rw [hstep, he, mul_zero, sub_zero]
      exact hx.2.2 e
  exact ⟨ε, hε, hplus, hminus⟩

/-- At an extreme point, the only vector supported on positive coordinates
and annihilating all active rows and equality rows is zero. -/
theorem extreme_kernel_trivial {I E J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℝ) (b : I → ℝ) (L : E → J → ℝ) (c : E → ℝ)
    (x : J → ℝ) (hx : x ∈ (feasible A b L c).extremePoints ℝ)
    (d : J → ℝ) (hz : ∀ j, x j = 0 → d j = 0)
    (ha : ∀ i, row (A i) x = b i → row (A i) d = 0)
    (he : ∀ e, row (L e) d = 0) : d = 0 := by
  obtain ⟨ε, hε, hp, hm⟩ := symmetric_feasible_step A b L c x d hx.1 hz ha he
  have hs : x ∈ openSegment ℝ (fun j => x j + ε * d j) (fun j => x j - ε * d j) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have heq := hx.2 hp hm hs
  ext j
  have hj := congrFun heq j
  change d j = 0
  have hmul : ε * d j = 0 := by linarith
  exact (mul_eq_zero.mp hmul).resolve_left hε.ne'

/-- The ambient number of coordinates is at most the number of equality
rows plus the number of active inequality rows plus the number of zero
coordinates. Redundant rows only weaken this bound. -/
theorem extreme_dimension_bound {I E J : Type*} [Fintype I] [Fintype E] [Fintype J]
    (A : I → J → ℝ) (b : I → ℝ) (L : E → J → ℝ) (c : E → ℝ)
    (x : J → ℝ) (hx : x ∈ (feasible A b L c).extremePoints ℝ) :
    Fintype.card J ≤ Fintype.card E +
      (Finset.univ.filter (fun i => row (A i) x = b i)).card +
      (Finset.univ.filter (fun j => x j = 0)).card := by
  classical
  let T := E ⊕ {i : I // row (A i) x = b i} ⊕ {j : J // x j = 0}
  let M : Matrix T J ℝ := fun t j => match t with
    | .inl e => L e j
    | .inr (.inl i) => A i.val j
    | .inr (.inr k) => if j = k.val then 1 else 0
  let F : (J → ℝ) →ₗ[ℝ] (T → ℝ) := M.mulVecLin
  have hinj : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro d hd
    apply extreme_kernel_trivial A b L c x hx d
    · intro k hk
      have h := congrFun hd (.inr (.inr ⟨k, hk⟩))
      simpa [F, M, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using h
    · intro i hi
      have h := congrFun hd (.inr (.inl ⟨i, hi⟩))
      simpa [F, M, row, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using h
    · intro e
      have h := congrFun hd (.inl e)
      simpa [F, M, row, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using h
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fintype_fun_eq_card, T, Fintype.card_sum,
    Fintype.card_subtype] at hdim
  omega

/-- A vertex has at most as many positive coordinates as equality rows and
active inequality rows together. This is the support-count step used in a
simplex-product cap subdivision. -/
theorem extreme_support_bound {I E J : Type*} [Fintype I] [Fintype E] [Fintype J]
    (A : I → J → ℝ) (b : I → ℝ) (L : E → J → ℝ) (c : E → ℝ)
    (x : J → ℝ) (hx : x ∈ (feasible A b L c).extremePoints ℝ) :
    (Finset.univ.filter (fun j => x j ≠ 0)).card ≤ Fintype.card E +
      (Finset.univ.filter (fun i => row (A i) x = b i)).card := by
  classical
  have h := extreme_dimension_bound A b L c x hx
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset J)) (fun j => x j = 0)
  simp only [Finset.card_univ, ← ne_eq] at hc
  omega

#print axioms symmetric_feasible_step
#print axioms extreme_kernel_trivial
#print axioms extreme_support_bound
end Erdos7PolyhedralSupportBound
