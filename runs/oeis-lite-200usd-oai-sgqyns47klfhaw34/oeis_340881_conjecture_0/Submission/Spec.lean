import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
Row sums of A340880.
$$a(n) = \sum_{k = 0}^{n-1} 2^{k(k+1)/2} \cdot \left( \prod_{j = k+1}^{n-1} (2^j - 1) \right)$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k ↦
    (2 ^ Nat.choose (k + 1) 2) *
    (Finset.prod (Finset.Ico (k + 1) n) fun j ↦ (2 ^ j - 1))

/--
Conjectures: 1) For prime p, the sequence taken modulo p is purely periodic with
minimum period dividing 2*(p - 1).
-/
lemma choose_pair_shift (r k : ℕ) :
    Nat.choose (2 * r + k + 1) 2 = Nat.choose (k + 1) 2 + r * (2 * k + 2 * r + 1) := by
  have choose_succ_two (n : ℕ) : Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
    rw [show n + 1 = Nat.succ n by omega]
    rw [Nat.choose_succ_succ]
    simp [Nat.add_comm]
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show 2 * (r + 1) + k + 1 = (2 * r + k + 1) + 2 by omega]
    rw [show (2 * r + k + 1) + 2 = (2 * r + k + 1 + 1) + 1 by omega]
    rw [choose_succ_two (2 * r + k + 1 + 1)]
    rw [choose_succ_two (2 * r + k + 1)]
    rw [ih]
    ring_nf

lemma pow_period_of_pow_eq_one {R : Type*} [Monoid R] (x : R) (r j : ℕ) (h : x ^ r = 1) :
    x ^ (2 * r + j) = x ^ j := by
  rw [show 2 * r + j = j + r * 2 by omega]
  rw [pow_add, pow_mul, h]
  simp

lemma summand_period_zmod (p r n k : ℕ) (hpow : (2 : ZMod p) ^ r = 1) :
    ((2 : ZMod p) ^ Nat.choose (2 * r + k + 1) 2) *
        (∏ j ∈ Finset.Ico (2 * r + k + 1) (n + 2 * r), ((2 : ZMod p) ^ j - 1)) =
      ((2 : ZMod p) ^ Nat.choose (k + 1) 2) *
        (∏ j ∈ Finset.Ico (k + 1) n, ((2 : ZMod p) ^ j - 1)) := by
  congr 1
  · rw [choose_pair_shift]
    rw [pow_add, pow_mul, hpow]
    simp
  · rw [show 2 * r + k + 1 = k + 1 + 2 * r by omega]
    rw [← Finset.prod_Ico_add (fun j ↦ ((2 : ZMod p) ^ j - 1)) (k + 1) n (2 * r)]
    apply Finset.prod_congr rfl
    intro j hj
    rw [pow_period_of_pow_eq_one (x := (2 : ZMod p)) r j hpow]

theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  intro n hn
  by_cases hp2 : p = 2
  · subst hp2
    have hconst (m : ℕ) (hm : 1 ≤ m) :
        ((a m : ℕ) : ZMod 2) = 1 := by
      simp [a, Nat.cast_sum, Nat.cast_prod, Nat.cast_mul, Nat.cast_pow]
      rw [Finset.sum_eq_single (a := 0)]
      · have hlead : (2 : ZMod 2) ^ Nat.choose (0 + 1) 2 = 1 := by norm_num
        rw [hlead, one_mul]
        apply Finset.prod_eq_one
        intro j hj
        simp at hj
        have h2 : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
        rw [h2]
        cases j with
        | zero => omega
        | succ j => simp
      · intro k hk hk0
        have hk1 : 1 ≤ k := by omega
        have hpow0 : ((2 : ZMod 2) ^ Nat.choose (k + 1) 2) = 0 := by
          have hchoose : 0 < Nat.choose (k + 1) 2 := by
            apply Nat.choose_pos
            omega
          have h2 : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
          rw [h2]
          exact zero_pow (Nat.ne_of_gt hchoose)
        simp [hpow0]
      · intro h0
        simp at h0
        omega
    have hz : ((a (n + 2 * (2 - 1)) : ℕ) : ZMod 2) = ((a n : ℕ) : ZMod 2) := by
      rw [hconst (n + 2 * (2 - 1)) (by omega), hconst n hn]
    exact (ZMod.natCast_eq_natCast_iff' (a (n + 2 * (2 - 1))) (a n) 2).mp hz
  · let r := p - 1
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    have hne : (2 : ZMod p) ≠ 0 := by
      intro h
      have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
      have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      exact hp2 (le_antisymm hple hp.two_le)
    have hpow : (2 : ZMod p) ^ r = 1 := by
      simpa [r] using (ZMod.pow_card_sub_one_eq_one (p := p) hne)
    have hpow2 : (2 : ZMod p) ^ (2 * r) = 1 := by
      rw [show 2 * r = r * 2 by omega, pow_mul, hpow]
      simp
    have hz : ((a (n + 2 * r) : ℕ) : ZMod p) = ((a n : ℕ) : ZMod p) := by
      simp [a, Nat.cast_sum, Nat.cast_prod, Nat.cast_mul, Nat.cast_pow]
      rw [show n + 2 * r = 2 * r + n by omega]
      rw [Finset.sum_range_add]
      have hfirst :
          (∑ k ∈ Finset.range (2 * r),
            ((2 : ZMod p) ^ Nat.choose (k + 1) 2) *
              (∏ j ∈ Finset.Ico (k + 1) (2 * r + n), ((2 : ZMod p) ^ j - 1))) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hmem : 2 * r ∈ Finset.Ico (k + 1) (2 * r + n) := by
          simp at hk ⊢
          omega
        have hprod :
            (∏ j ∈ Finset.Ico (k + 1) (2 * r + n), ((2 : ZMod p) ^ j - 1)) = 0 := by
          apply Finset.prod_eq_zero (i := 2 * r)
          · exact hmem
          · simp [hpow2]
        simp [hprod]
      rw [hfirst, zero_add]
      apply Finset.sum_congr rfl
      intro k hk
      simpa [show 2 * r + n = n + 2 * r by omega] using
        (summand_period_zmod p r n k hpow)
    have hmod := (ZMod.natCast_eq_natCast_iff' (a (n + 2 * r)) (a n) p).mp hz
    simpa [r] using hmod
