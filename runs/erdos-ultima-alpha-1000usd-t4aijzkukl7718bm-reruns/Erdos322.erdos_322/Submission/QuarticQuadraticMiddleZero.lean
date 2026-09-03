import FormalConjecturesUtil

/-! A Chevalley–Warning incidence lemma for quadratic forms over F_5.
This is a construction lemma, not an unrestricted representation-count bound. -/
namespace Erdos322Research.QuarticQuadraticMiddleZero

open Finset MvPolynomial
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev K := ZMod 5
abbrev V := Fin 4 → K

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def supportCount (x : V) : ℕ := (univ.filter (fun i => x i ≠ 0)).card

def axis (i : Fin 4) : V := Pi.single i 1

private lemma small_support_card (a : Fin 4 → Bool) (j : Fin 4) :
    (univ.filter (fun x : V => x j = 0 ∧ supportCount x ≤ 1 ∧
      ∀ i, x i ≠ 0 → a i = true)).card =
      1 + 4*(univ.filter (fun i : Fin 4 => i ≠ j ∧ a i = true)).card := by
  revert a j
  decide +kernel

private lemma impossible_axis_counts (a : Fin 4 → Bool) :
    ∃ j : Fin 4, ¬ 5 ∣ 1+4*(univ.filter (fun i : Fin 4 => i ≠ j ∧ a i = true)).card := by
  revert a
  decide +kernel

private lemma support_le_three {x : V} {j : Fin 4} (hx : x j = 0) :
    supportCount x ≤ 3 := by
  have hs : univ.filter (fun i => x i ≠ 0) ⊆ univ.erase j := by
    intro i hi
    exact mem_erase.mpr ⟨by intro he; subst i; exact (mem_filter.mp hi).2 hx, mem_univ _⟩
  have hc := card_le_card hs
  simpa [supportCount] using hc

private lemma eq_smul_axis {x : V} (h : supportCount x ≤ 1) {i : Fin 4}
    (hi : x i ≠ 0) : x = x i • axis i := by
  have hs := card_le_one.mp h
  funext j
  by_cases hji : j = i
  · subst j
    simp [axis]
  · have hj : x j = 0 := by
      by_contra hj
      exact hji (hs j (mem_filter.mpr ⟨mem_univ _, hj⟩)
        i (mem_filter.mpr ⟨mem_univ _, hi⟩))
    simp [axis, hji, hj]

/-- No homogeneous quadratic polynomial in four variables over F_5 can
avoid all nonzero zeros of support two or three. Homogeneity is expressed
here by its scalar-evaluation identity. -/
theorem exists_middle_zero_of_scaling
    (P : MvPolynomial (Fin 4) K) (hdeg : P.totalDegree ≤ 2)
    (hscale : ∀ (c : K) (x : V), eval (c • x) P = c^2 * eval x P) :
    ∃ x : V, (supportCount x = 2 ∨ supportCount x = 3) ∧ eval x P = 0 := by
  classical
  by_contra h
  have hno (x : V) (hz : eval x P = 0) :
      supportCount x ≠ 2 ∧ supportCount x ≠ 3 := by
    constructor <;> intro hc
    · exact h ⟨x, Or.inl hc, hz⟩
    · exact h ⟨x, Or.inr hc, hz⟩
  have hzero : eval (0 : V) P = 0 := by
    simpa using hscale 0 (0 : V)
  let a : Fin 4 → Bool := fun i => decide (eval (axis i) P = 0)
  obtain ⟨j,hj⟩ := impossible_axis_counts a
  have hcard : (univ.filter (fun x : V => eval x P = 0 ∧ x j = 0)).card =
      1+4*(univ.filter (fun i : Fin 4 => i ≠ j ∧ a i = true)).card := by
    rw [← small_support_card a j]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hz,hxj⟩
      have hb := support_le_three hxj
      have hn := hno x hz
      have hs : supportCount x ≤ 1 := by omega
      refine ⟨hxj, hs, ?_⟩
      intro i hi
      have he := eq_smul_axis hs hi
      have hp : eval (axis i) P = 0 := by
        rw [he, hscale] at hz
        exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hi)
      simpa [a] using hp
    · rintro ⟨hxj,hs,ha⟩
      refine ⟨?_,hxj⟩
      by_cases hx : x = 0
      · simpa [hx] using hzero
      · obtain ⟨i,hi⟩ : ∃ i, x i ≠ 0 := by
          by_contra hh
          push_neg at hh
          exact hx (funext hh)
        have hp : eval (axis i) P = 0 := by simpa [a] using ha i hi
        rw [eq_smul_axis hs hi, hscale, hp, mul_zero]
  have hd : P.totalDegree + (X j : MvPolynomial (Fin 4) K).totalDegree <
      Fintype.card (Fin 4) := by
    simpa using (show P.totalDegree + 1 < 4 by omega)
  have hw := char_dvd_card_solutions_of_add_lt (K := K) 5 hd
  have hw' : 5 ∣ (univ.filter (fun x : V => eval x P = 0 ∧ x j = 0)).card := by
    simpa only [eval_X, Fintype.card_subtype] using hw
  exact hj (hcard ▸ hw')

private lemma homogeneous_eval_smul (P : MvPolynomial (Fin 4) K)
    (hP : P.IsHomogeneous 2) (c : K) (x : V) :
    eval (c • x) P = c^2 * eval x P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum, Finset.mul_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro d hd
  have hd2 : d.degree = 2 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (mem_support_iff.mp hd)
  have hsum : ∑ i ∈ d.support, d i = 2 := by
    simpa only [Finsupp.degree_apply] using hd2
  simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
  ring

/-- The homogeneous-polynomial version, with no separately assumed scaling
law. The conclusion holds even when the polynomial is identically zero. -/
theorem exists_middle_zero (P : MvPolynomial (Fin 4) K)
    (hP : P.IsHomogeneous 2) :
    ∃ x : V, (supportCount x = 2 ∨ supportCount x = 3) ∧ eval x P = 0 :=
  exists_middle_zero_of_scaling P hP.totalDegree_le (homogeneous_eval_smul P hP)

private lemma norm_four_nonzero : ∀ v : V,
    (∑ i, v i^4) = 4 → v 0 ≠ 0 := by decide +kernel

private lemma middle_norm_square : ∀ x : V,
    (supportCount x = 2 ∨ supportCount x = 3) → (∑ i, x i^4)^2 = 4 := by
  decide +kernel

/-- There is no homogeneous quadratic norm-square formula with multiplier
one over F_5. This concerns polynomial formulas, not integer counts. -/
theorem no_homogeneous_square_multiplier_one
    (P : Fin 4 → MvPolynomial (Fin 4) K)
    (hP : ∀ i, (P i).IsHomogeneous 2) :
    ¬ (∀ x : V, ∑ i, (eval x (P i))^4 = (∑ i, x i^4)^2) := by
  intro h
  obtain ⟨x,hx,hzero⟩ := exists_middle_zero (P 0) (hP 0)
  have he : ∑ i, (eval x (P i))^4 = 4 := (h x).trans (middle_norm_square x hx)
  exact norm_four_nonzero (fun i => eval x (P i)) he hzero

end Erdos322Research.QuarticQuadraticMiddleZero
