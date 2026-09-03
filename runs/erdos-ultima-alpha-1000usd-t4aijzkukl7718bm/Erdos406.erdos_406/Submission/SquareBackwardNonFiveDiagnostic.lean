import FormalConjecturesUtil

/-! Excluding the prime five does not rescue an unqualified square-input
backward digit rule. These fixed examples do not handle arbitrary valuation
thresholds or cutoffs, and do not settle Erdős 406. -/
namespace Erdos406SquareBackwardNonFive

private lemma not_power_of_two_of_nineteen_dvd {n : ℕ} (hn : 19 ∣ n) :
    ¬ n.isPowerOfTwo := by
  rintro ⟨k, hk⟩
  have hd : 19 ∣ (2 : ℕ)^k := by simpa only [← hk] using hn
  have hp : Nat.Prime 19 := by decide
  have h := hp.dvd_of_dvd_pow hd
  norm_num at h

lemma residue_one_certificate :
    (698896 : ℕ) = 836^2 ∧ 16 ∣ (698896 : ℕ) ∧
    698896 % 9 = 1 ∧ ¬ 5 ∣ (698896 : ℕ) ∧
    Nat.digits 3 (64*698896) ⊆ [0,1] ∧
    ¬ Nat.digits 3 698896 ⊆ [0,1] ∧ 19 ∣ (698896 : ℕ) := by
  decide +kernel

lemma residue_four_certificate :
    (57183844 : ℕ) = 7562^2 ∧ 4 ∣ (57183844 : ℕ) ∧
    57183844 % 9 = 4 ∧ ¬ 5 ∣ (57183844 : ℕ) ∧
    Nat.digits 3 (64*57183844) ⊆ [0,1] ∧
    ¬ Nat.digits 3 57183844 ⊆ [0,1] ∧ 19 ∣ (57183844 : ℕ) := by
  decide +kernel

/-- Fixed counterexamples in each difficult residue class. No claim of
arbitrarily high valuation or arbitrarily large size is made here. -/
theorem non_five_square_failures (r : ℕ) (hr : r = 1 ∨ r = 4) :
    ∃ n : ℕ, IsSquare n ∧ 4 ∣ n ∧ n % 9 = r ∧ ¬ 5 ∣ n ∧
      Nat.digits 3 (64*n) ⊆ [0,1] ∧ ¬ Nat.digits 3 n ⊆ [0,1] ∧
      ¬ n.isPowerOfTwo ∧ ¬ (64*n).isPowerOfTwo := by
  have hn : ∃ n : ℕ, IsSquare n ∧ 4 ∣ n ∧ n % 9 = r ∧ ¬ 5 ∣ n ∧
      Nat.digits 3 (64*n) ⊆ [0,1] ∧ ¬ Nat.digits 3 n ⊆ [0,1] ∧ 19 ∣ n := by
    rcases hr with rfl | rfl
    · obtain ⟨hs, hd, hm, h5, hg, hng, h19⟩ := residue_one_certificate
      exact ⟨698896, ⟨836, by nlinarith⟩,
        dvd_trans (by decide : 4 ∣ 16) hd, hm, h5, hg, hng, h19⟩
    · obtain ⟨hs, hd, hm, h5, hg, hng, h19⟩ := residue_four_certificate
      exact ⟨57183844, ⟨7562, by nlinarith⟩, hd, hm, h5, hg, hng, h19⟩
  obtain ⟨n, hs, hd, hm, h5, hg, hng, h19⟩ := hn
  exact ⟨n, hs, hd, hm, h5, hg, hng,
    not_power_of_two_of_nineteen_dvd h19,
    not_power_of_two_of_nineteen_dvd (dvd_mul_of_dvd_right h19 64)⟩

/-- This negates only a proposed non-five square descent rule. -/
theorem non_five_square_backward_goodness_false (r : ℕ) (hr : r = 1 ∨ r = 4) :
    ¬ (∀ n : ℕ, IsSquare n → 4 ∣ n → n % 9 = r → ¬ 5 ∣ n →
      Nat.digits 3 (64*n) ⊆ [0,1] → Nat.digits 3 n ⊆ [0,1]) := by
  intro h
  obtain ⟨n, hs, hd, hm, h5, hg, hng, _, _⟩ := non_five_square_failures r hr
  exact hng (h n hs hd hm h5 hg)

#print axioms residue_one_certificate
#print axioms residue_four_certificate
#print axioms non_five_square_failures
#print axioms non_five_square_backward_goodness_false
end Erdos406SquareBackwardNonFive
