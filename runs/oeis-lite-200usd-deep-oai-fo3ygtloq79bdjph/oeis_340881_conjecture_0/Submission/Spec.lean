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

lemma cast_two_pow_sub_one (p n : ℕ) :
    ((2^n - 1 : ℕ) : ZMod p) = (2 : ZMod p)^n - 1 := by
  rw [Nat.cast_sub]
  · simp
  · exact Nat.one_le_pow n 2 (by norm_num : 0 < 2)

lemma two_ne_zero_zmod_of_prime_ne_two {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  change ((2 : ℕ) : ZMod p) = 0 at h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)

lemma fermat_two_zmod {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    (2 : ZMod p) ^ (p - 1) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  exact ZMod.pow_card_sub_one_eq_one (two_ne_zero_zmod_of_prime_ne_two hp hp2)

lemma choose_succ_two (x : ℕ) : Nat.choose (x+1) 2 = Nat.choose x 2 + x := by
  rw [show x+1 = x.succ by omega]
  rw [Nat.choose_succ_succ]
  simp [Nat.choose_one_right]
  omega

lemma choose_add_two (x : ℕ) : Nat.choose (x+2) 2 = Nat.choose x 2 + x + (x+1) := by
  rw [show x+2 = (x+1)+1 by omega]
  rw [choose_succ_two, choose_succ_two]

lemma choose_shift_even (m n : ℕ) : Nat.choose (n + 2*m + 1) 2 = Nat.choose (n+1) 2 + m*(2*n+2*m+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show n + 2*(m+1) + 1 = (n + 2*m + 1) + 2 by omega]
      rw [choose_add_two]
      rw [ih]
      ring

lemma choose_two_odd (m : ℕ) : Nat.choose (2*m + 1) 2 = m * (2*m + 1) := by
  simpa using choose_shift_even m 0

lemma base_odd (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    (a (2*(p-1)+1) : ZMod p) = 1 := by
  let m := p - 1
  let T := 2 * m
  have hfermat : (2 : ZMod p) ^ m = 1 := by simpa [m] using fermat_two_zmod hp hp2
  have hpowT : (2 : ZMod p) ^ T = 1 := by
    have hT : T = m * 2 := by simp [T]; ring
    rw [hT, pow_mul, hfermat, one_pow]
  have hzero_m : (((2^m - 1 : ℕ) : ZMod p)) = 0 := by
    rw [cast_two_pow_sub_one, hfermat]
    simp
  have hzero_T : (((2^T - 1 : ℕ) : ZMod p)) = 0 := by
    rw [cast_two_pow_sub_one, hpowT]
    simp
  have hsumzero :
      (∑ x ∈ Finset.range T,
        (((2 ^ Nat.choose (x + 1) 2) *
          (Finset.prod (Finset.Ico (x + 1) (T + 1)) fun j ↦ (2 ^ j - 1))) : ℕ) : ZMod p) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkT : k < T := Finset.mem_range.mp hk
    simp only [Nat.cast_mul]
    apply mul_eq_zero_of_right
    simp only [Nat.cast_prod]
    by_cases hkm : k < m
    · apply Finset.prod_eq_zero (i := m)
      · rw [Finset.mem_Ico]
        constructor <;> omega
      · exact hzero_m
    · apply Finset.prod_eq_zero (i := T)
      · rw [Finset.mem_Ico]
        constructor <;> omega
      · exact hzero_T
  change ((Finset.sum (Finset.range (T+1)) fun k ↦
    (2 ^ Nat.choose (k + 1) 2) *
    (Finset.prod (Finset.Ico (k + 1) (T+1)) fun j ↦ (2 ^ j - 1)) : ℕ) : ZMod p) = 1
  rw [Finset.sum_range_succ]
  simp only [Finset.Ico_self, Finset.prod_empty, mul_one, Nat.cast_add]
  rw [Nat.cast_sum]
  rw [hsumzero]
  simp only [zero_add]
  have hchoose : Nat.choose (T + 1) 2 = m * (T + 1) := by
    subst T
    simpa [mul_comm, mul_left_comm, mul_assoc] using choose_two_odd m
  rw [hchoose]
  simp only [Nat.cast_pow]
  rw [pow_mul]
  change ((2 : ZMod p) ^ m) ^ (T + 1) = 1
  rw [hfermat, one_pow]

lemma a_succ (n : ℕ) :
    a (n+1) = (2^n - 1) * a n + 2 ^ Nat.choose (n+1) 2 := by
  simp only [a, Finset.sum_range_succ]
  simp only [Finset.Ico_self, Finset.prod_empty, mul_one]
  congr 1
  calc
    ∑ x ∈ range n, 2 ^ (x + 1).choose 2 * ∏ j ∈ Ico (x + 1) (n + 1), (2 ^ j - 1)
        = ∑ x ∈ range n, 2 ^ (x + 1).choose 2 * (∏ j ∈ Ico (x + 1) n, (2 ^ j - 1)) * (2^n - 1) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxle : x + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hx)
          rw [Finset.prod_Ico_succ_top hxle]
          ring
    _ = (∑ x ∈ range n, 2 ^ (x + 1).choose 2 * ∏ j ∈ Ico (x + 1) n, (2 ^ j - 1)) * (2^n - 1) := by
          rw [Finset.sum_mul]
    _ = (2^n - 1) * ∑ x ∈ range n, 2 ^ (x + 1).choose 2 * ∏ j ∈ Ico (x + 1) n, (2 ^ j - 1) := by
          rw [mul_comm]

lemma a_succ_zmod (p n : ℕ) :
    (a (n+1) : ZMod p) = ((2^n -1 : ℕ) : ZMod p) * (a n : ZMod p) + (((2^Nat.choose (n+1) 2 : ℕ) : ZMod p)) := by
  rw [a_succ]
  simp

lemma pow_shift_period (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) (n : ℕ) :
    (2 : ZMod p) ^ (n + 2*(p-1)) = (2 : ZMod p) ^ n := by
  let m := p - 1
  have hfermat : (2 : ZMod p) ^ m = 1 := by simpa [m] using fermat_two_zmod hp hp2
  rw [show n + 2*(p-1) = n + m*2 by simp [m, mul_comm]]
  rw [pow_add, pow_mul, hfermat, one_pow, mul_one]

lemma pow_choose_period (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) (n : ℕ) :
    (2 : ZMod p) ^ Nat.choose (n + 2*(p-1) + 1) 2 =
    (2 : ZMod p) ^ Nat.choose (n + 1) 2 := by
  let m := p - 1
  have hfermat : (2 : ZMod p) ^ m = 1 := by simpa [m] using fermat_two_zmod hp hp2
  have harg : n + 2*(p-1) + 1 = n + 2*m + 1 := by simp [m]
  rw [harg, choose_shift_even]
  rw [pow_add, pow_mul, hfermat, one_pow, mul_one]

lemma coeff_period (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) (n : ℕ) :
    (((2 ^ (n + 2*(p-1)) - 1 : ℕ) : ZMod p)) = (((2 ^ n - 1 : ℕ) : ZMod p)) := by
  rw [cast_two_pow_sub_one, cast_two_pow_sub_one]
  rw [pow_shift_period p hp hp2 n]

lemma force_period (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) (n : ℕ) :
    (((2 ^ Nat.choose (n + 2*(p-1) + 1) 2 : ℕ) : ZMod p)) =
    (((2 ^ Nat.choose (n + 1) 2 : ℕ) : ZMod p)) := by
  simp only [Nat.cast_pow]
  change (2 : ZMod p) ^ Nat.choose (n + 2*(p-1) + 1) 2 =
    (2 : ZMod p) ^ Nat.choose (n + 1) 2
  rw [pow_choose_period p hp hp2 n]

lemma a_period_zmod_odd (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    ∀ n : ℕ, 1 ≤ n → (a (n + 2*(p-1)) : ZMod p) = (a n : ZMod p) := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero =>
          rw [show (a 1 : ZMod p) = 1 by simp [a]]
          rw [show 1 + 2 * (p - 1) = 2 * (p - 1) + 1 by omega]
          exact base_odd p hp hp2
      | succ n =>
          let r := n + 1
          have ih' : (a (r + 2*(p-1)) : ZMod p) = (a r : ZMod p) := ih (by omega)
          rw [show (n + 1 + 1) + 2*(p-1) = (r + 2*(p-1)) + 1 by omega]
          rw [a_succ_zmod, a_succ_zmod]
          rw [coeff_period p hp hp2 r]
          rw [force_period p hp hp2 r]
          rw [ih']

lemma choose_pos_succ_succ (n : ℕ) : 0 < Nat.choose (n+2) 2 := by
  exact Nat.choose_pos (by omega)

lemma a_zmod_two (n : ℕ) (hn : 1 ≤ n) : (a n : ZMod 2) = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => simp [a]
      | succ n =>
          rw [a_succ]
          have ih' : (a (n+1) : ZMod 2) = 1 := ih (by omega)
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
          rw [cast_two_pow_sub_one]
          rw [ih']
          have hpow : (2 : ZMod 2) ^ (n+1) = 0 := by
            change (0 : ZMod 2) ^ (n+1) = 0
            exact zero_pow (by omega)
          have hterm : (((2 : ℕ) : ZMod 2) ^ Nat.choose (n + 1 + 1) 2) = 0 := by
            change (0 : ZMod 2) ^ Nat.choose (n + 1 + 1) 2 = 0
            exact zero_pow (_root_.ne_of_gt (by simpa [Nat.add_assoc] using choose_pos_succ_succ n))
          rw [hpow, hterm]
          decide

lemma zmod_eq_mod {p x y : ℕ} (h : (x : ZMod p) = (y : ZMod p)) : x % p = y % p := by
  have hv := congrArg ZMod.val h
  simpa [ZMod.val_natCast] using hv


/--
Conjectures: 1) For prime p, the sequence taken modulo p is purely periodic with
minimum period dividing 2*(p - 1).
-/
theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  intro n hn
  by_cases hp2 : p = 2
  · subst p
    exact zmod_eq_mod (by
      rw [a_zmod_two (n + 2 * (2 - 1)) (by omega), a_zmod_two n hn])
  · exact zmod_eq_mod (a_period_zmod_odd p hp hp2 n hn)
