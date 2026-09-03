import Submission.FiveDistinctExceptions

/-! Small repairs whose first group avoids actual moduli five and seven.
These are auxiliary obstructions, not a settlement of the odd covering problem. -/
namespace Erdos7SixExceptionWeights
open scoped BigOperators
open Erdos7FourExceptionWeight Erdos7FiveExceptionWeights
open Erdos7FourExceptionScalar (cap)
open Erdos7FourExceptionArithmetic Erdos7MinimumTernaryClass
set_option autoImplicit false
set_option maxHeartbeats 4000000

lemma weight_without_five_seven (d : ℕ) (hd : 1 < d) (ho : Odd d)
    (h3 : ¬ 3 ∣ d) (h5 : d≠5) (h7 : d≠7) : weight d ≤ (5/44 : ℚ) := by
  by_cases h11 : d=11
  · subst d; norm_num [prime_weight 11 (by decide),cap]
  exact (weight_outside d hd ho h3 h5 h7 h11).trans (by norm_num)

lemma weight_le_four_fifteenths (d : ℕ) (hd : 1 < d) (ho : Odd d)
    (h3 : ¬ 3 ∣ d) : weight d ≤ (4/15 : ℚ) := by
  by_cases h5 : d=5
  · subst d; norm_num [prime_weight 5 (by decide),cap]
  exact (weight_le_without_five d hd ho h3 h5).trans (by norm_num)

lemma sum_weight_le_card_mul {K : Type*} [Fintype K]
    (d : K → ℕ) (c : ℚ) (hc : ∀ k, weight (d k) ≤ c) :
    (∑ k, weight (d k)) ≤ Fintype.card K*c := by
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
    (Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => hc k))

lemma two_group_weight {K U : Type*} [Fintype K] [Fintype U]
    (d : K → ℕ) (hd : ∀ k, 1 < d k ∧ Odd (d k)) (hd3 : ∀ k, ¬ 3 ∣ d k)
    (hd5 : ∀ k, d k≠5) (hd7 : ∀ k, d k≠7) (hK : Fintype.card K ≤ 3)
    (n : U → ℕ) (hni : Function.Injective n)
    (hn : ∀ u, 1 < n u ∧ Odd (n u)) (hn3 : ∀ u, ¬ 3 ∣ n u)
    (hU : Fintype.card U ≤ 2) (hshape : Fintype.card U ≤ 1 ∨ Fintype.card K ≤ 1) :
    (∑ k, weight (d k))+(∑ u, weight (n u)) ≤ (649/1000 : ℚ) := by
  have hfirst := sum_weight_le_card_mul d (5/44) (fun k =>
    weight_without_five_seven (d k) (hd k).1 (hd k).2 (hd3 k) (hd5 k) (hd7 k))
  rcases hshape with hu | hk
  · have hsecond := sum_weight_le_card_mul n (4/15) (fun u =>
      weight_le_four_fifteenths (n u) (hn u).1 (hn u).2 (hn3 u))
    have hk' : (Fintype.card K : ℚ) ≤ 3 := by exact_mod_cast hK
    have hu' : (Fintype.card U : ℚ) ≤ 1 := by exact_mod_cast hu
    linarith
  · have hsecond := two_distinct_weight n hni hn hn3 hU
    have hk' : (Fintype.card K : ℚ) ≤ 1 := by exact_mod_cast hk
    linarith

lemma not_cover_groups_no_three {I K U : Type*} [Fintype I] [Fintype K] [Fintype U]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : K → ℕ) (b : K → ℤ) (hd : ∀ k, 1 < d k ∧ Odd (d k))
    (hd3 : ∀ k, ¬ 3 ∣ d k) (hd5 : ∀ k, d k≠5) (hd7 : ∀ k, d k≠7)
    (hK : Fintype.card K ≤ 3)
    (n : U → ℕ) (c : U → ℤ) (hni : Function.Injective n)
    (hn : ∀ u, 1 < n u ∧ Odd (n u)) (hn3 : ∀ u, ¬ 3 ∣ n u)
    (hU : Fintype.card U ≤ 2) (hshape : Fintype.card U ≤ 1 ∨ Fintype.card K ≤ 1) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨
      (∃ k, (d k : ℤ) ∣ x-b k) ∨ ∃ u, (n u : ℤ) ∣ x-c u) := by
  classical
  let D : K ⊕ U → ℕ := Sum.elim d n
  let B : K ⊕ U → ℤ := Sum.elim b c
  have hD (j : K ⊕ U) : 0 < D j ∧ Odd (D j) := by
    cases j with
    | inl j =>
      change 0 < d j ∧ Odd (d j)
      exact ⟨by have := (hd j).1; omega,(hd j).2⟩
    | inr j =>
      change 0 < n j ∧ Odd (n j)
      exact ⟨by have := (hn j).1; omega,(hn j).2⟩
  have hD3 (j : K ⊕ U) : ¬ 3 ∣ D j := by
    cases j with
    | inl j => exact hd3 j
    | inr j => exact hn3 j
  have hw : (∑ j, weight (D j)) ≤ (649/1000 : ℚ) := by
    simpa only [D,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr] using
      two_group_weight d hd hd3 hd5 hd7 hK n hni hn hn3 hU hshape
  intro hcover
  apply not_cover_with_weighted_exceptions m a hinj hm h3 D B hD hD3 hw
  intro x
  rcases hcover x with hi | ⟨k,hk⟩ | ⟨u,hu⟩
  · exact Or.inl hi
  · exact Or.inr ⟨Sum.inl k,hk⟩
  · exact Or.inr ⟨Sum.inr u,hu⟩

/-- Up to three no-three exceptions missing five and seven, together with
one further odd class, cannot repair a distinct no-three base. Alternatively,
one such restricted exception and two mutually distinct odd classes cannot.
The restricted exceptions need not be distinct. -/
theorem not_cover_small_groups {I K U : Type*} [Fintype I] [Fintype K] [Fintype U]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : K → ℕ) (b : K → ℤ) (hd : ∀ k, 1 < d k ∧ Odd (d k))
    (hd3 : ∀ k, ¬ 3 ∣ d k) (hd5 : ∀ k, d k≠5) (hd7 : ∀ k, d k≠7)
    (hK : Fintype.card K ≤ 3)
    (n : U → ℕ) (c : U → ℤ) (hni : Function.Injective n)
    (hn : ∀ u, 1 < n u ∧ Odd (n u))
    (hU : Fintype.card U ≤ 2) (hshape : Fintype.card U ≤ 1 ∨ Fintype.card K ≤ 1) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨
      (∃ k, (d k : ℤ) ∣ x-b k) ∨ ∃ u, (n u : ℤ) ∣ x-c u) := by
  classical
  by_cases hno : ∀ u, ¬ 3 ∣ n u
  · exact not_cover_groups_no_three m a hinj hm h3 d b hd hd3 hd5 hd7 hK n c hni hn hno hU hshape
  push_neg at hno
  obtain ⟨u₀,hu₀⟩ := hno
  let V := {u : U // ¬ 3 ∣ n u}
  have hV : Fintype.card V ≤ 1 := by
    have hh := Fintype.card_subtype_lt (p := fun u : U => ¬ 3 ∣ n u) (x := u₀) (by simpa using hu₀)
    simp only [V,Fintype.card_subtype] at hh ⊢
    omega
  obtain ⟨r,hr⟩ := Erdos7SmallTernaryBranches.free_ternary_residue c hU
  choose a' ha' using fun i => affine_residue (m i) (h3 i) (a i) r
  choose b' hb' using fun k => affine_residue (d k) (hd3 k) (b k) r
  choose c' hc' using fun u : V => affine_residue (n u) u.property (c u) r
  intro hcover
  apply not_cover_groups_no_three m a' hinj hm h3 d b' hd hd3 hd5 hd7 hK
    (fun u : V => n u) c' (hni.comp Subtype.val_injective)
    (fun u => hn u) (fun u => u.property) (by omega) (Or.inl hV)
  intro x
  rcases hcover (3*x+r) with ⟨i,hi⟩ | ⟨k,hk⟩ | ⟨u,hu⟩
  · exact Or.inl ⟨i,ha' i x hi⟩
  · exact Or.inr (Or.inl ⟨k,hb' k x hk⟩)
  · have hu3 : ¬ 3 ∣ n u := by
      intro hh
      have hz := (Int.natCast_dvd_natCast.mpr hh).trans hu
      exact hr u (by omega)
    exact Or.inr (Or.inr ⟨⟨u,hu3⟩,hc' ⟨u,hu3⟩ x hu⟩)

#print axioms not_cover_small_groups
end Erdos7SixExceptionWeights
