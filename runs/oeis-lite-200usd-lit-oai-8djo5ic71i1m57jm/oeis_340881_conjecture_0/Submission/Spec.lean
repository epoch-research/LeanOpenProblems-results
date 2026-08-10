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

private def zterm (p N k : ℕ) : ZMod p :=
  ((2 : ZMod p) ^ Nat.choose (k + 1) 2) *
    (Finset.prod (Finset.Ico (k + 1) N) fun j ↦ ((2 : ZMod p) ^ j - 1))

private lemma cast_a (p n : ℕ) :
    ((a n : ℕ) : ZMod p) = ∑ k ∈ Finset.range n, zterm p n k := by
  simp [a, zterm, Nat.cast_sum, Nat.cast_prod, Nat.cast_mul, Nat.cast_pow]

private lemma a_mod_two_zmod (n : ℕ) (hn : n ≥ 1) : ((a n : ℕ) : ZMod 2) = 1 := by
  rw [cast_a]
  rw [Finset.sum_eq_single (a := 0)]
  · simp only [zterm]
    norm_num
    intro i hi hin
    change (0 : ZMod 2) ^ i - 1 = 1
    rw [zero_pow (by omega : i ≠ 0)]
    decide
  · intro k hk hk0
    have hc : Nat.choose (k + 1) 2 ≠ 0 := by
      exact Nat.ne_of_gt (Nat.choose_pos (by omega : 2 ≤ k + 1))
    change ((2 : ZMod 2) ^ Nat.choose (k + 1) 2) *
        (Finset.prod (Finset.Ico (k + 1) n) fun j ↦ ((2 : ZMod 2) ^ j - 1)) = 0
    rw [show (2 : ZMod 2) = 0 by decide, zero_pow hc, zero_mul]
  · intro h0
    rw [Finset.mem_range] at h0
    omega

private lemma choose_shift_two_mul (q r : ℕ) :
    Nat.choose (2*q + r + 1) 2 = Nat.choose (r+1) 2 + q*(2*r + 2*q + 1) := by
  rw [Nat.choose_two_right, Nat.choose_two_right]
  apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
  rw [Nat.mul_add]
  rw [Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one (2*q+r+1))]
  rw [Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one (r+1))]
  simp
  ring_nf

private lemma two_ne_zero_zmod_of_prime_ne_two {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  change ¬ ((2 : ℕ) : ZMod p) = 0
  rw [CharP.cast_eq_zero_iff (ZMod p) p]
  intro h
  have hp_le_two : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
  exact hp2 (le_antisymm hp_le_two hp.two_le)

private lemma pow_two_period {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) (e t : ℕ) :
    (2 : ZMod p) ^ (e + (p - 1) * t) = (2 : ZMod p) ^ e := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [pow_add, pow_mul]
  rw [ZMod.pow_card_sub_one_eq_one (two_ne_zero_zmod_of_prime_ne_two hp hp2)]
  simp

private lemma pow_two_q {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    (2 : ZMod p) ^ (p - 1) = 1 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  exact ZMod.pow_card_sub_one_eq_one (two_ne_zero_zmod_of_prime_ne_two hp hp2)

private lemma zterm_shift {p n r : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    zterm p (n + 2*(p-1)) (2*(p-1) + r) = zterm p n r := by
  let q := p - 1
  have hchoose : Nat.choose (2*q + r + 1) 2 =
      Nat.choose (r+1) 2 + q*(2*r + 2*q + 1) := choose_shift_two_mul q r
  have hpow : (2 : ZMod p) ^ Nat.choose (2*q + r + 1) 2 =
      (2 : ZMod p) ^ Nat.choose (r+1) 2 := by
    rw [hchoose]
    exact pow_two_period hp hp2 (Nat.choose (r+1) 2) (2*r + 2*q + 1)
  have hfac : ∀ j, (2 : ZMod p) ^ (2*q + j) - 1 = (2 : ZMod p) ^ j - 1 := by
    intro j
    have h : (2 : ZMod p) ^ (j + q*2) = (2 : ZMod p) ^ j :=
      pow_two_period hp hp2 j 2
    rw [show 2*q + j = j + q*2 by omega]
    exact congrArg (fun x : ZMod p => x - 1) h
  unfold zterm
  change ((2 : ZMod p) ^ Nat.choose (2 * (p - 1) + r + 1) 2) *
      (∏ j ∈ Ico (2 * (p - 1) + r + 1) (n + 2 * (p - 1)), ((2 : ZMod p) ^ j - 1)) =
    ((2 : ZMod p) ^ Nat.choose (r + 1) 2) *
      (∏ j ∈ Ico (r + 1) n, ((2 : ZMod p) ^ j - 1))
  rw [show 2 * (p - 1) = 2*q by rfl]
  rw [hpow]
  congr 1
  calc
    (∏ j ∈ Ico (2 * q + r + 1) (n + 2 * q), ((2 : ZMod p) ^ j - 1))
        = ∏ j ∈ Ico (r + 1) n, ((2 : ZMod p) ^ (2*q + j) - 1) := by
          rw [Finset.prod_Ico_add (f := fun j => ((2 : ZMod p) ^ j - 1))
            (a := r+1) (b := n) (c := 2*q)]
          simp [add_comm, add_left_comm, add_assoc]
    _ = ∏ j ∈ Ico (r + 1) n, ((2 : ZMod p) ^ j - 1) := by
          apply Finset.prod_congr rfl
          intro j hj
          exact hfac j

private lemma zterm_initial_zero {p n k : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) (hn : n ≥ 1)
    (hk : k < 2*(p-1)) : zterm p (n + 2*(p-1)) k = 0 := by
  let q := p - 1
  have hp3 : 3 ≤ p := by omega
  have hqpos : 0 < q := by omega
  let l := if k < q then q else 2*q
  have hl_mem : l ∈ Ico (k+1) (n + 2*(p-1)) := by
    rw [Finset.mem_Ico]
    by_cases hkq : k < q
    · simp [l, hkq]
      omega
    · simp [l, hkq]
      omega
  have hfactor : ((2 : ZMod p) ^ l - 1) = 0 := by
    by_cases hkq : k < q
    · simp [l, hkq]
      rw [pow_two_q hp hp2]
      simp
    · simp [l, hkq]
      rw [show 2*q = q + (p-1)*1 by omega]
      rw [pow_two_period hp hp2 q 1]
      rw [pow_two_q hp hp2]
      simp
  unfold zterm
  rw [Finset.prod_eq_zero hl_mem hfactor, mul_zero]

private lemma a_period_zmod_odd {p n : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) (hn : n ≥ 1) :
    ((a (n + 2*(p-1)) : ℕ) : ZMod p) = ((a n : ℕ) : ZMod p) := by
  rw [cast_a, cast_a]
  rw [show n + 2*(p-1) = 2*(p-1) + n by omega]
  rw [Finset.sum_range_add]
  have hzero : (∑ k ∈ range (2 * (p - 1)), zterm p (2 * (p - 1) + n) k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    convert zterm_initial_zero hp hp2 hn (by simpa [Finset.mem_range] using hk) using 2
    omega
  have hshift : (∑ r ∈ range n, zterm p (2 * (p - 1) + n) (2 * (p - 1) + r)) =
      ∑ r ∈ range n, zterm p n r := by
    apply Finset.sum_congr rfl
    intro r hr
    convert zterm_shift hp hp2 using 2
    omega
  rw [hzero, zero_add, hshift]

/--
Conjectures: 1) For prime p, the sequence taken modulo p is purely periodic with
minimum period dividing 2*(p - 1).
-/
theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  intro n hn
  change Nat.ModEq p (a (n + 2 * (p - 1))) (a n)
  by_cases hp2 : p = 2
  · subst p
    have hleft : ((a (n + 2 * (2 - 1)) : ℕ) : ZMod 2) = 1 := by
      apply a_mod_two_zmod
      omega
    have hright : ((a n : ℕ) : ZMod 2) = 1 := a_mod_two_zmod n hn
    have hz : ((a (n + 2 * (2 - 1)) : ℕ) : ZMod 2) = ((a n : ℕ) : ZMod 2) := by
      rw [hleft, hright]
    exact (ZMod.natCast_eq_natCast_iff (a (n + 2 * (2 - 1))) (a n) 2).mp hz
  · have hz : ((a (n + 2 * (p - 1)) : ℕ) : ZMod p) = ((a n : ℕ) : ZMod p) :=
      a_period_zmod_odd hp hp2 hn
    exact (ZMod.natCast_eq_natCast_iff (a (n + 2 * (p - 1))) (a n) p).mp hz
