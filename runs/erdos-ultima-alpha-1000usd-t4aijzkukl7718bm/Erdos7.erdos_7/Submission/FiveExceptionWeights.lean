import Submission.FourDistinctExceptions

/-! Restrictions on small exceptional families from the verified mixed-cap
hole law. These do not exclude unrestricted odd covers. -/
namespace Erdos7FiveExceptionWeights
open scoped BigOperators
open Erdos7FourExceptionWeight
open Erdos7FourExceptionScalar (cap)
open Erdos7Reduction Erdos7MinimumTernaryClass Erdos7DoubleExceptionOdd
set_option autoImplicit false
set_option maxHeartbeats 4000000

lemma indicator_sum_le {J : Type*} [Fintype J] (d : J → ℕ) (hinj : Function.Injective d)
    (p : ℕ) (c : ℚ) (hc : 0 ≤ c) : (∑ j : J, if d j=p then c else 0) ≤ c := by
  classical
  have hcard : (Finset.univ.filter (fun j : J => d j=p)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro j hj k hk
    exact hinj ((Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hk).2.symm)
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  have hcard' : ((Finset.univ.filter (fun j : J => d j=p)).card : ℚ) ≤ 1 := by exact_mod_cast hcard
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hcard' hc

lemma weight_le_without_five (d : ℕ) (hd : 1 < d) (ho : Odd d) (h3 : ¬ 3 ∣ d)
    (h5 : d≠5) : weight d ≤ (6/35 : ℚ) := by
  by_cases h7 : d=7
  · subst d; norm_num [prime_weight 7 (by decide),cap]
  by_cases h11 : d=11
  · subst d; norm_num [prime_weight 11 (by decide),cap]
  exact (weight_outside d hd ho h3 h5 h7 h11).trans (by norm_num)

lemma two_distinct_weight {J : Type*} [Fintype J]
    (d : J → ℕ) (hinj : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (h3 : ∀ j, ¬ 3 ∣ d j)
    (hJ : Fintype.card J ≤ 2) : (∑ j, weight (d j)) ≤ (46/105 : ℚ) := by
  classical
  have hb (j : J) : weight (d j) ≤ (6/35 : ℚ)+(if d j=5 then 4/15-6/35 else 0) := by
    by_cases h5 : d j=5
    · rw [h5]; norm_num [prime_weight 5 (by decide),cap]
    · simpa only [if_neg h5,add_zero] using weight_le_without_five (d j) (hd j).1 (hd j).2 (h3 j) h5
  have hh := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hb j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have h5 := indicator_sum_le d hinj 5 (4/15-6/35) (by norm_num)
  have hJ' : (Fintype.card J : ℚ) ≤ 2 := by exact_mod_cast hJ
  linarith

/-- In addition to two DISTINCT no-three exceptions, a single nontrivial
odd exception repairing coverage must have modulus five. -/
theorem singleton_repair_is_five {I K : Type*} [Fintype I] [Fintype K]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : K → ℕ) (b : K → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (hd3 : ∀ j, ¬ 3 ∣ d j)
    (hK : Fintype.card K ≤ 2) (q : ℕ) (hq : 1 < q ∧ Odd q) (c : ℤ)
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨
      (∃ j, (d j : ℤ) ∣ x-b j) ∨ (q : ℤ) ∣ x-c) : q=5 := by
  classical
  by_contra hn
  by_cases hq3 : 3 ∣ q
  · choose a' ha' using fun i => affine_residue (m i) (h3 i) (a i) (c+1)
    choose b' hb' using fun j => affine_residue (d j) (hd3 j) (b j) (c+1)
    apply not_cover_with_at_most_two_odd_exceptions m a' hinj hm h3 d hd b' hK
    intro x
    rcases hcover (3*x+(c+1)) with ⟨i,hi⟩ | ⟨j,hj⟩ | hh
    · exact Or.inl ⟨i,ha' i x hi⟩
    · exact Or.inr ⟨j,hb' j x hj⟩
    · have h := (Int.natCast_dvd_natCast.mpr hq3).trans hh
      omega
  · let d' : K ⊕ Unit → ℕ := Sum.elim d (fun _ => q)
    let b' : K ⊕ Unit → ℤ := Sum.elim b (fun _ => c)
    have hd' (j : K ⊕ Unit) : 0 < d' j ∧ Odd (d' j) := by
      cases j with
      | inl j =>
        change 0 < d j ∧ Odd (d j)
        exact ⟨by have := (hd j).1; omega,(hd j).2⟩
      | inr j =>
        change 0 < q ∧ Odd q
        exact ⟨by omega,hq.2⟩
    have hd3' (j : K ⊕ Unit) : ¬ 3 ∣ d' j := by
      cases j with
      | inl j => exact hd3 j
      | inr j => exact hq3
    apply Erdos7FourExceptionArithmetic.not_cover_with_weighted_exceptions
      m a hinj hm h3 d' b' hd' hd3'
    · have hh := two_distinct_weight d hdi hd hd3 hK
      have hq' := weight_le_without_five q hq.1 hq.2 hq3 hn
      simp only [d',Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.sum_unique]
      linarith
    · intro x
      rcases hcover x with hi | ⟨j,hj⟩ | hh
      · exact Or.inl hi
      · exact Or.inr ⟨Sum.inl j,hj⟩
      · exact Or.inr ⟨Sum.inr (),hh⟩

lemma weight_outside_four (d : ℕ) (hd : 1 < d) (ho : Odd d) (h3 : ¬ 3 ∣ d)
    (h5 : d≠5) (h7 : d≠7) (h11 : d≠11) (h13 : d≠13) : weight d ≤ (5/68 : ℚ) := by
  by_cases hp : d.Prime
  · have hge : 17 ≤ d := by
      by_contra hn
      interval_cases d <;> norm_num at *
    have hc : cap d=(5/4 : ℚ) := by simp [cap,h5,h7]
    rw [prime_weight d hp,hc]
    have hge' : (17 : ℚ) ≤ d := by exact_mod_cast hge
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < d)).mpr
    linarith
  · have hh := (weight_le_old d).trans (mul_le_mul_of_nonneg_left
        (Erdos7ThreeDistinctExceptions.composite_weight_le d hd ho h3 hp)
        (by norm_num : (0 : ℚ) ≤ 16/15))
    linarith

lemma five_missing_five_weight {J : Type*} [Fintype J]
    (d : J → ℕ) (hinj : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (h3 : ∀ j, ¬ 3 ∣ d j)
    (h5 : ∀ j, d j≠5) (hJ : Fintype.card J ≤ 5) :
    (∑ j, weight (d j)) ≤ (649/1000 : ℚ) := by
  classical
  have hb (j : J) : weight (d j) ≤ (5/52 : ℚ)+
      (if d j=7 then 6/35-5/52 else 0)+(if d j=11 then 5/44-5/52 else 0) := by
    by_cases h7 : d j=7
    · rw [h7]; norm_num [prime_weight 7 (by decide),cap]
    by_cases h11 : d j=11
    · rw [h11]; norm_num [prime_weight 11 (by decide),cap]
    simpa only [if_neg h7,if_neg h11,add_zero] using
      weight_outside (d j) (hd j).1 (hd j).2 (h3 j) (h5 j) h7 h11
  have hh := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hb j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have hh7 := indicator_sum_le d hinj 7 (6/35-5/52) (by norm_num)
  have hh11 := indicator_sum_le d hinj 11 (5/44-5/52) (by norm_num)
  have hJ' : (Fintype.card J : ℚ) ≤ 5 := by exact_mod_cast hJ
  linarith

lemma five_missing_seven_weight {J : Type*} [Fintype J]
    (d : J → ℕ) (hinj : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (h3 : ∀ j, ¬ 3 ∣ d j)
    (h7 : ∀ j, d j≠7) (hJ : Fintype.card J ≤ 5) :
    (∑ j, weight (d j)) ≤ (649/1000 : ℚ) := by
  classical
  have hb (j : J) : weight (d j) ≤ (5/68 : ℚ)+
      (if d j=5 then 4/15-5/68 else 0)+
      (if d j=11 then 5/44-5/68 else 0)+(if d j=13 then 5/52-5/68 else 0) := by
    by_cases h5 : d j=5
    · rw [h5]; norm_num [prime_weight 5 (by decide),cap]
    by_cases h11 : d j=11
    · rw [h11]; norm_num [prime_weight 11 (by decide),cap]
    by_cases h13 : d j=13
    · rw [h13]; norm_num [prime_weight 13 (by decide),cap]
    simpa only [if_neg h5,if_neg h11,if_neg h13,add_zero] using
      weight_outside_four (d j) (hd j).1 (hd j).2 (h3 j) h5 (h7 j) h11 h13
  have hh := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hb j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have hh5 := indicator_sum_le d hinj 5 (4/15-5/68) (by norm_num)
  have hh11 := indicator_sum_le d hinj 11 (5/44-5/68) (by norm_num)
  have hh13 := indicator_sum_le d hinj 13 (5/52-5/68) (by norm_num)
  have hJ' : (Fintype.card J : ℚ) ≤ 5 := by exact_mod_cast hJ
  linarith

#print axioms singleton_repair_is_five
#print axioms five_missing_five_weight
#print axioms five_missing_seven_weight
end Erdos7FiveExceptionWeights
