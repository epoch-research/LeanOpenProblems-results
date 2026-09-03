import Submission.ExponentDensity

/-! Uniform sparsity in translated exponent intervals. These results do not
assert an eventual cutoff and do not settle Erdős 406. -/

namespace Erdos406UniformSparsity
open Erdos406Work Erdos406Density Filter
open scoped Topology

lemma four_pow_mod_injective_shift (M r : ℕ) {a b : ℕ}
    (ha : a < 3 ^ r) (hb : b < 3 ^ r)
    (h : 4 ^ (M + a) % 3 ^ (r + 1) = 4 ^ (M + b) % 3 ^ (r + 1)) :
    a = b := by
  have hc : Nat.Coprime (3 ^ (r + 1)) (4 ^ M) :=
    ((by decide : Nat.Coprime 3 4).pow_left (r + 1)).pow_right M
  have hm : Nat.ModEq (3 ^ (r + 1)) (4 ^ M * 4 ^ a) (4 ^ M * 4 ^ b) := by
    simpa only [pow_add] using h
  exact four_pow_mod_injective ha hb (hm.cancel_left_of_coprime hc)

/-- At most `2^r` good powers occur in any interval of `3^r` exponents.
The starting point is unrestricted. -/
theorem good_four_shift_card_le (M r : ℕ) :
    countBelow (fun j => Nat.digits 3 (4 ^ (M + j)) ⊆ [0, 1]) (3 ^ r) ≤ 2 ^ r := by
  classical
  unfold countBelow
  calc
    _ ≤ (List.fixedLengthDigits (b := 2) (by decide) r).card := by
      apply Finset.card_le_card_of_injOn (fun j => ternaryPrefix r (4 ^ (M + j) / 3))
      · intro j hj
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
        have hd := hj.2
        rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3)
          (by positivity : 0 < 4 ^ (M + j))] at hd
        have hdt : Nat.digits 3 (4 ^ (M + j) / 3) ⊆ [0, 1] := by
          intro d hd'
          exact hd (List.mem_cons_of_mem _ hd')
        exact (List.mem_fixedLengthDigits_iff (by decide : 1 < 2)).mpr
          ⟨ternaryPrefix_length _ _, ternaryPrefix_lt_two hdt⟩
      · intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
        have hm := congrArg (Nat.ofDigits 3) hab
        rw [ofDigits_ternaryPrefix, ofDigits_ternaryPrefix] at hm
        change Nat.ModEq (3 ^ r) (4 ^ (M + a) / 3) (4 ^ (M + b) / 3) at hm
        have hh := (hm.mul_left' 3).add_left 1
        rw [← four_pow_eq_one_add, ← four_pow_eq_one_add, ← pow_succ'] at hh
        exact four_pow_mod_injective_shift M r ha.1 hb.1 hh
    _ = 2 ^ r := List.card_fixedLengthDigits (by decide) r

/-- A bound uniform in the left endpoint of the exponent interval. -/
theorem good_four_shift_ratio_bound (M N : ℕ) :
    (countBelow (fun j => Nat.digits 3 (4 ^ (M + j)) ⊆ [0, 1]) N : ℝ) / N ≤
      2 * (2 / 3 : ℝ) ^ Nat.log 3 N :=
  count_ratio_bound _ (good_four_shift_card_le M) N

/-- Even if the left endpoint varies arbitrarily with the interval length,
the proportion of good powers tends to zero. -/
theorem good_four_moving_intervals_density_zero (start : ℕ → ℕ) :
    Tendsto (fun N : ℕ =>
      (countBelow (fun j => Nat.digits 3 (4 ^ (start N + j)) ⊆ [0, 1]) N : ℝ) / N)
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun r : ℕ => (2 / 3 : ℝ) ^ r) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlimit : Tendsto (fun N : ℕ => 2 * (2 / 3 : ℝ) ^ Nat.log 3 N) atTop (𝓝 0) := by
    simpa using (hpow.comp nat_log_three_tendsto).const_mul 2
  exact squeeze_zero (fun N => by positivity)
    (fun N => good_four_shift_ratio_bound (start N) N) hlimit

/-- The quantifiers express uniformity, not just a separate density-zero
statement for each fixed left endpoint. -/
theorem good_four_uniform_density_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ,
      (countBelow (fun j => Nat.digits 3 (4 ^ (M + j)) ⊆ [0, 1]) N : ℝ) / N < ε := by
  have hpow : Tendsto (fun r : ℕ => (2 / 3 : ℝ) ^ r) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlimit : Tendsto (fun N : ℕ => 2 * (2 / 3 : ℝ) ^ Nat.log 3 N) atTop (𝓝 0) := by
    simpa using (hpow.comp nat_log_three_tendsto).const_mul 2
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlimit.eventually (gt_mem_nhds hε))
  exact ⟨N₀, fun N hN M => lt_of_le_of_lt (good_four_shift_ratio_bound M N) (hN₀ N hN)⟩

/-- In every interval of `2 * 3^r` exponents of two, at most `2^r`
exponents meet the digit condition. The parity restriction is included. -/
theorem good_two_shift_card_le (M r : ℕ) :
    countBelow (fun j => Nat.digits 3 (2 ^ (M + j)) ⊆ [0, 1]) (2 * 3 ^ r) ≤
      2 ^ r := by
  classical
  apply le_trans _ (good_four_shift_card_le ((M + 1) / 2) r)
  unfold countBelow
  apply Finset.card_le_card_of_injOn (fun j => j / 2)
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨u, hu⟩ := even_exponent hj.2
    have hu' : (M + 1) / 2 + j / 2 = u := by omega
    have hp : 4 ^ ((M + 1) / 2 + j / 2) = 2 ^ (M + j) := by
      rw [hu', show M + j = 2 * u by omega, pow_mul]
      rfl
    exact ⟨by omega, by simpa only [hp] using hj.2⟩
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    obtain ⟨u, hu⟩ := even_exponent ha.2
    obtain ⟨v, hv⟩ := even_exponent hb.2
    change a / 2 = b / 2 at hab
    omega

lemma good_two_shift_geometric_bound (M r : ℕ) :
    countBelow (fun j => Nat.digits 3 (2 ^ (M + j)) ⊆ [0, 1]) (3 ^ r) ≤ 2 ^ r :=
  (countBelow_mono _ (by omega : 3 ^ r ≤ 2 * 3 ^ r)).trans (good_two_shift_card_le M r)

/-- Uniform sparsity for powers of two, with an explicit upper bound. -/
theorem good_two_shift_ratio_bound (M N : ℕ) :
    (countBelow (fun j => Nat.digits 3 (2 ^ (M + j)) ⊆ [0, 1]) N : ℝ) / N ≤
      2 * (2 / 3 : ℝ) ^ Nat.log 3 N :=
  count_ratio_bound _ (good_two_shift_geometric_bound M) N

theorem good_two_moving_intervals_density_zero (start : ℕ → ℕ) :
    Tendsto (fun N : ℕ =>
      (countBelow (fun j => Nat.digits 3 (2 ^ (start N + j)) ⊆ [0, 1]) N : ℝ) / N)
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun r : ℕ => (2 / 3 : ℝ) ^ r) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlimit : Tendsto (fun N : ℕ => 2 * (2 / 3 : ℝ) ^ Nat.log 3 N) atTop (𝓝 0) := by
    simpa using (hpow.comp nat_log_three_tendsto).const_mul 2
  exact squeeze_zero (fun N => by positivity)
    (fun N => good_two_shift_ratio_bound (start N) N) hlimit

theorem good_two_uniform_density_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ,
      (countBelow (fun j => Nat.digits 3 (2 ^ (M + j)) ⊆ [0, 1]) N : ℝ) / N < ε := by
  have hpow : Tendsto (fun r : ℕ => (2 / 3 : ℝ) ^ r) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlimit : Tendsto (fun N : ℕ => 2 * (2 / 3 : ℝ) ^ Nat.log 3 N) atTop (𝓝 0) := by
    simpa using (hpow.comp nat_log_three_tendsto).const_mul 2
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlimit.eventually (gt_mem_nhds hε))
  exact ⟨N₀, fun N hN M => lt_of_le_of_lt (good_two_shift_ratio_bound M N) (hN₀ N hN)⟩

#print axioms good_two_shift_card_le
#print axioms good_two_moving_intervals_density_zero
#print axioms good_two_uniform_density_zero

#print axioms good_four_shift_card_le
#print axioms good_four_moving_intervals_density_zero
#print axioms good_four_uniform_density_zero
end Erdos406UniformSparsity
