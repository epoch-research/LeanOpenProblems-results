import Submission.SixExceptionWeights

/-! Small repairs whose first group avoids actual modulus five.
These are auxiliary obstructions, not a settlement of the odd covering problem. -/
namespace Erdos7SixExceptionWithoutFiveWeights
open scoped BigOperators
open Erdos7FourExceptionWeight Erdos7FiveExceptionWeights
open Erdos7FourExceptionScalar (cap)
open Erdos7FourExceptionArithmetic Erdos7MinimumTernaryClass
set_option autoImplicit false
set_option maxHeartbeats 4000000

open Erdos7SixExceptionWeights (weight_le_four_fifteenths sum_weight_le_card_mul)

lemma three_missing_five_weight {K : Type*} [Fintype K]
    (d : K → ℕ) (hdi : Function.Injective d)
    (hd : ∀ k, 1 < d k ∧ Odd (d k)) (hd3 : ∀ k, ¬ 3 ∣ d k)
    (hd5 : ∀ k, d k≠5) (hK : Fintype.card K ≤ 3) :
    (∑ k, weight (d k)) ≤ (6/35+5/44+5/52 : ℚ) := by
  classical
  have hb (k : K) : weight (d k) ≤ (5/52 : ℚ)+
      (if d k=7 then 6/35-5/52 else 0)+(if d k=11 then 5/44-5/52 else 0) := by
    by_cases h7 : d k=7
    · rw [h7]; norm_num [prime_weight 7 (by decide),cap]
    by_cases h11 : d k=11
    · rw [h11]; norm_num [prime_weight 11 (by decide),cap]
    simpa only [if_neg h7,if_neg h11,add_zero] using
      weight_outside (d k) (hd k).1 (hd k).2 (hd3 k) (hd5 k) h7 h11
  have hh := Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => hb k)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have h7 := indicator_sum_le d hdi 7 (6/35-5/52) (by norm_num)
  have h11 := indicator_sum_le d hdi 11 (5/44-5/52) (by norm_num)
  have hk' : (Fintype.card K : ℚ) ≤ 3 := by exact_mod_cast hK
  linarith

lemma six_missing_five_weight {K : Type*} [Fintype K]
    (d : K → ℕ) (hdi : Function.Injective d)
    (hd : ∀ k, 1 < d k ∧ Odd (d k)) (hd3 : ∀ k, ¬ 3 ∣ d k)
    (hd5 : ∀ k, d k≠5) (hK : Fintype.card K ≤ 6) :
    (∑ k, weight (d k)) ≤ (649/1000 : ℚ) := by
  classical
  have hb (k : K) : weight (d k) ≤ (5/68 : ℚ)+
      (if d k=7 then 6/35-5/68 else 0)+(if d k=11 then 5/44-5/68 else 0)+
      (if d k=13 then 5/52-5/68 else 0) := by
    by_cases h7 : d k=7
    · rw [h7]; norm_num [prime_weight 7 (by decide),cap]
    by_cases h11 : d k=11
    · rw [h11]; norm_num [prime_weight 11 (by decide),cap]
    by_cases h13 : d k=13
    · rw [h13]; norm_num [prime_weight 13 (by decide),cap]
    simpa only [if_neg h7,if_neg h11,if_neg h13,add_zero] using
      weight_outside_four (d k) (hd k).1 (hd k).2 (hd3 k) (hd5 k) h7 h11 h13
  have hh := Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => hb k)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have h7 := indicator_sum_le d hdi 7 (6/35-5/68) (by norm_num)
  have h11 := indicator_sum_le d hdi 11 (5/44-5/68) (by norm_num)
  have h13 := indicator_sum_le d hdi 13 (5/52-5/68) (by norm_num)
  have hk' : (Fintype.card K : ℚ) ≤ 6 := by exact_mod_cast hK
  linarith

lemma two_group_weight {K U : Type*} [Fintype K] [Fintype U]
    (d : K → ℕ) (hdi : Function.Injective d) (hd : ∀ k, 1 < d k ∧ Odd (d k)) (hd3 : ∀ k, ¬ 3 ∣ d k)
    (hd5 : ∀ k, d k≠5) (hK : Fintype.card K ≤ 3)
    (n : U → ℕ) (hni : Function.Injective n)
    (hn : ∀ u, 1 < n u ∧ Odd (n u)) (hn3 : ∀ u, ¬ 3 ∣ n u)
    (hU : Fintype.card U ≤ 2) (hshape : Fintype.card U ≤ 1 ∨ Fintype.card K ≤ 1) :
    (∑ k, weight (d k))+(∑ u, weight (n u)) ≤ (649/1000 : ℚ) := by
  rcases hshape with hu | hk
  · have hfirst := three_missing_five_weight d hdi hd hd3 hd5 hK
    have hsecond := sum_weight_le_card_mul n (4/15) (fun u =>
      weight_le_four_fifteenths (n u) (hn u).1 (hn u).2 (hn3 u))
    have hu' : (Fintype.card U : ℚ) ≤ 1 := by exact_mod_cast hu
    linarith
  · have hfirst := sum_weight_le_card_mul d (6/35) (fun k =>
      weight_le_without_five (d k) (hd k).1 (hd k).2 (hd3 k) (hd5 k))
    have hsecond := two_distinct_weight n hni hn hn3 hU
    have hk' : (Fintype.card K : ℚ) ≤ 1 := by exact_mod_cast hk
    linarith

lemma not_cover_groups_no_three {I K U : Type*} [Fintype I] [Fintype K] [Fintype U]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : K → ℕ) (b : K → ℤ) (hdi : Function.Injective d) (hd : ∀ k, 1 < d k ∧ Odd (d k))
    (hd3 : ∀ k, ¬ 3 ∣ d k) (hd5 : ∀ k, d k≠5)
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
      two_group_weight d hdi hd hd3 hd5 hK n hni hn hn3 hU hshape
  intro hcover
  apply not_cover_with_weighted_exceptions m a hinj hm h3 D B hD hD3 hw
  intro x
  rcases hcover x with hi | ⟨k,hk⟩ | ⟨u,hu⟩
  · exact Or.inl hi
  · exact Or.inr ⟨Sum.inl k,hk⟩
  · exact Or.inr ⟨Sum.inr u,hu⟩

/-- Up to three distinct no-three exceptions missing five, together with
one further odd class, cannot repair a distinct no-three base. Alternatively,
one such restricted exception and two mutually distinct odd classes cannot.
Both groups are separately distinct, but may overlap. -/
theorem not_cover_small_groups {I K U : Type*} [Fintype I] [Fintype K] [Fintype U]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : K → ℕ) (b : K → ℤ) (hdi : Function.Injective d) (hd : ∀ k, 1 < d k ∧ Odd (d k))
    (hd3 : ∀ k, ¬ 3 ∣ d k) (hd5 : ∀ k, d k≠5)
    (hK : Fintype.card K ≤ 3)
    (n : U → ℕ) (c : U → ℤ) (hni : Function.Injective n)
    (hn : ∀ u, 1 < n u ∧ Odd (n u))
    (hU : Fintype.card U ≤ 2) (hshape : Fintype.card U ≤ 1 ∨ Fintype.card K ≤ 1) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨
      (∃ k, (d k : ℤ) ∣ x-b k) ∨ ∃ u, (n u : ℤ) ∣ x-c u) := by
  classical
  by_cases hno : ∀ u, ¬ 3 ∣ n u
  · exact not_cover_groups_no_three m a hinj hm h3 d b hdi hd hd3 hd5 hK n c hni hn hno hU hshape
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
  apply not_cover_groups_no_three m a' hinj hm h3 d b' hdi hd hd3 hd5 hK
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
end Erdos7SixExceptionWithoutFiveWeights
