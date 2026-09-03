import Submission.ReciprocalTotientTwo

/-!
# Reciprocal totient mass on even cofactors

The even part of every prefix has at most twice the odd part, hence at
most two thirds of the total reciprocal-totient mass.
-/

open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.Sieve
set_option maxHeartbeats 3000000

noncomputable def evenReciprocalTotient (A : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 A with Even n, 1/(n.totient : ℝ)

noncomputable def oddReciprocalTotient (A : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 A with ¬Even n, 1/(n.totient : ℝ)

lemma even_add_odd_reciprocal_totient (A : ℕ) :
    evenReciprocalTotient A + oddReciprocalTotient A =
      ∑ n ∈ Icc 1 A, 1/(n.totient : ℝ) := by
  exact Finset.sum_filter_add_sum_filter_not _ _ _

lemma even_reciprocal_totient_recurrence (A : ℕ) :
    evenReciprocalTotient A = oddReciprocalTotient (A/2) + (1/2)*evenReciprocalTotient (A/2) := by
  have himage : (Icc 1 A).filter (fun n => Even n) = (Icc 1 (A/2)).image (fun n => 2*n) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnI,hne⟩ := mem_filter.mp hn
      have hnmod : n % 2 = 0 := Nat.even_iff.mp hne
      refine mem_image.mpr ⟨n/2,mem_Icc.mpr ⟨?_,?_⟩,?_⟩
      · have := (mem_Icc.mp hnI).1
        omega
      · have := (mem_Icc.mp hnI).2
        omega
      · omega
    · intro hn
      obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
      obtain ⟨hm1,hmA⟩ := mem_Icc.mp hm
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,⟨m,by omega⟩⟩
  unfold evenReciprocalTotient oddReciprocalTotient
  rw [himage, sum_image (by intro n hn m hm h; dsimp at h; omega)]
  rw [Finset.mul_sum, sum_filter, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  by_cases he : Even n
  · rw [if_pos he, if_neg (not_not.mpr he), Nat.totient_two_mul_of_even he]
    push_cast
    ring
  · rw [if_neg he, if_pos he, Nat.totient_two_mul_of_odd (Nat.not_even_iff_odd.mp he)]
    ring

lemma odd_reciprocal_totient_mono : Monotone oddReciprocalTotient := by
  intro A B hAB
  apply sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  intro n hn
  obtain ⟨hnI,hne⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hnI).1,(mem_Icc.mp hnI).2.trans hAB⟩,hne⟩

lemma even_reciprocal_totient_le_twice_odd (A : ℕ) :
    evenReciprocalTotient A ≤ 2*oddReciprocalTotient A := by
  induction A using Nat.strong_induction_on with
  | h A ih =>
    by_cases hA : A = 0
    · subst A
      simp [evenReciprocalTotient,oddReciprocalTotient]
    have hB : A/2 < A := Nat.div_lt_self (by omega) (by norm_num)
    have hh := ih (A/2) hB
    rw [even_reciprocal_totient_recurrence]
    have hm := odd_reciprocal_totient_mono (Nat.div_le_self A 2)
    linarith

lemma even_reciprocal_totient_le_two_thirds (A : ℕ) :
    evenReciprocalTotient A ≤ (2/3 : ℝ)*(∑ n ∈ Icc 1 A, 1/(n.totient : ℝ)) := by
  have he := even_reciprocal_totient_le_twice_odd A
  have hs := even_add_odd_reciprocal_totient A
  linarith

theorem even_reciprocal_totient_le_four_thirds_harmonic (A : ℕ) :
    evenReciprocalTotient A ≤ (4/3 : ℝ)*(harmonic A : ℝ) := by
  have h := sum_reciprocal_totient_le_two_harmonic A
  have he := even_reciprocal_totient_le_two_thirds A
  linarith

end Erdos821.Sieve
