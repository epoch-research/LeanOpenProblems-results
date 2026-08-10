import FormalConjectures.Util.ProblemImports
open Nat

noncomputable def a_Q (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 =>
    let n_idx := k + 2
    let n_q : ℚ := n_idx
    let a_prev : ℚ := a_Q (n_idx - 1)
    let term1 : ℚ := 32 * n_q ^ 3 * a_prev
    let P_n : ℚ := 21 * n_q ^ 3 + 22 * n_q ^ 2 + 8 * n_q + 1
    let binom_pow4 : ℚ := (Nat.choose (2 * n_idx - 1) n_idx : ℚ) ^ 4
    let numerator : ℚ := term1 + P_n * binom_pow4
    let denominator : ℚ := (2 * n_q + 1) ^ 3
    numerator / denominator

noncomputable def a (n : ℕ) : ℕ := (a_Q n).floor.toNat

/-- The defining recurrence, unfolded over ℚ. -/
lemma a_Q_rec (k : ℕ) :
    a_Q (k+2) =
      (32 * ((k+2:ℚ)) ^ 3 * a_Q (k+1)
        + (21 * ((k+2:ℚ)) ^ 3 + 22 * ((k+2:ℚ)) ^ 2 + 8 * ((k+2:ℚ)) + 1)
          * (Nat.choose (2 * (k+2) - 1) (k+2) : ℚ) ^ 4)
      / (2 * ((k+2:ℚ)) + 1) ^ 3 := by
  conv_lhs => rw [a_Q]
  show _ = _
  have h : k + 2 - 1 = k + 1 := rfl
  rw [h]; push_cast; ring

/-- Positivity: `a_Q (n+1) ≥ 1`. -/
lemma a_Q_ge_one : ∀ n : ℕ, (1:ℚ) ≤ a_Q (n+1) := by
  intro n
  induction n with
  | zero => rw [a_Q]; norm_num
  | succ k ih =>
    rw [a_Q_rec k]
    have hden : (0:ℚ) < (2 * ((k+2:ℚ)) + 1) ^ 3 := by positivity
    rw [le_div_iff₀ hden, one_mul]
    have hk2 : (1:ℚ) ≤ (k+2:ℚ) := by exact_mod_cast Nat.le_add_left 1 (k+1)
    have hC : (1:ℚ) ≤ (Nat.choose (2 * (k+2) - 1) (k+2) : ℚ) := by
      have : 1 ≤ Nat.choose (2 * (k+2) - 1) (k+2) := by apply Nat.choose_pos; omega
      exact_mod_cast this
    have hpoly : (2 * ((k+2:ℚ)) + 1) ^ 3 ≤ 32 * ((k+2:ℚ)) ^ 3 := by
      nlinarith [hk2, sq_nonneg ((k:ℚ)), sq_nonneg ((k:ℚ)+2)]
    nlinarith [ih, hC, hk2, hpoly, pow_pos (by linarith : (0:ℚ) < (k+2:ℚ)) 3,
      pow_nonneg (by linarith : (0:ℚ) ≤ (Nat.choose (2 * (k+2) - 1) (k+2) : ℚ)) 4,
      mul_le_mul_of_nonneg_left ih (by positivity : (0:ℚ) ≤ 32 * ((k+2:ℚ))^3)]

lemma a_pos (n : ℕ) (hn : n ≥ 1) : a n > 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
  simp only [a, gt_iff_lt]
  have h1 : (1:ℚ) ≤ a_Q (m+1) := a_Q_ge_one m
  have hfloor : (1:ℤ) ≤ (a_Q (m+1)).floor := by
    rw [Rat.le_floor_iff]; exact_mod_cast h1
  omega

/- ### Binomial parity chain -/

lemma digitsum_two_mul (n : ℕ) (hn : 1 ≤ n) :
    (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum := by
  rw [Nat.digits_def' (by norm_num : 2 ≤ 2) (by omega : 0 < 2*n)]
  simp [Nat.mul_div_cancel_left n (by norm_num : 0 < 2), Nat.mul_mod_right]

lemma digitsum_eq_zero (n : ℕ) : (Nat.digits 2 n).sum = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hne
    have hd : Nat.digits 2 n ≠ [] := (Nat.digits_ne_nil_iff_ne_zero).mpr hne
    have hlast := Nat.getLast_digit_ne_zero 2 hne
    have hmem : (Nat.digits 2 n).getLast hd ∈ Nat.digits 2 n := List.getLast_mem hd
    have hpos : 0 < (Nat.digits 2 n).getLast hd := Nat.pos_of_ne_zero hlast
    have := List.single_le_sum (by intro x _; exact Nat.zero_le x) _ hmem
    omega
  · rintro rfl; simp

lemma val_centralBinom (n : ℕ) (hn : 1 ≤ n) :
    padicValNat 2 (Nat.centralBinom n) = (Nat.digits 2 n).sum := by
  have hkey : Nat.centralBinom n * (n ! * n !) = (2 * n)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2*n by omega)
    have h2 : 2 * n - n = n := by omega
    rw [h2] at h; simp only [Nat.centralBinom]; rw [← h]; ring
  have hcb : Nat.centralBinom n ≠ 0 := Nat.centralBinom_ne_zero n
  have hf : (n ! : ℕ) ≠ 0 := Nat.factorial_ne_zero n
  have hadd : padicValNat 2 (Nat.centralBinom n) + (padicValNat 2 (n !) + padicValNat 2 (n !))
      = padicValNat 2 ((2 * n)!) := by
    rw [← hkey, padicValNat.mul hcb (by positivity), padicValNat.mul hf hf]
  have hL : ∀ m, padicValNat 2 (m !) = m - (Nat.digits 2 m).sum := by
    intro m; have := sub_one_mul_padicValNat_factorial (p := 2) m; simpa using this
  rw [hL, hL] at hadd
  rw [digitsum_two_mul n hn] at hadd
  have hle : (Nat.digits 2 n).sum ≤ n := Nat.digit_sum_le 2 n
  omega

lemma centralBinom_eq (n : ℕ) (hn : 1 ≤ n) :
    Nat.centralBinom n = 2 * Nat.choose (2 * n - 1) n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.centralBinom]
  have e2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have e1 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
  rw [e2, e1, Nat.choose_succ_succ (2 * m + 1) m]
  have hsymm : (2 * m + 1).choose m = (2 * m + 1).choose (m + 1) := by
    rw [← Nat.choose_symm (by omega : m ≤ 2 * m + 1)]; congr 1; omega
  rw [hsymm]; ring

lemma val_choose (n : ℕ) (hn : 1 ≤ n) :
    padicValNat 2 (Nat.choose (2 * n - 1) n) = (Nat.digits 2 n).sum - 1 := by
  have hc : Nat.choose (2 * n - 1) n ≠ 0 := (Nat.choose_pos (show n ≤ 2*n-1 by omega)).ne'
  have hcb := val_centralBinom n hn
  rw [centralBinom_eq n hn, padicValNat.mul (by norm_num) hc] at hcb
  have hv2 : padicValNat 2 2 = 1 := by simp [padicValNat.self]
  rw [hv2] at hcb; omega

lemma digitsum_eq_one (n : ℕ) : (Nat.digits 2 n).sum = 1 ↔ ∃ j, n = 2 ^ j := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      constructor
      · intro h; simp at h
      · rintro ⟨j, hj⟩; exact absurd hj.symm (Nat.two_pow_pos j).ne'
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨m, rfl⟩ := he
      have hm : 1 ≤ m := by omega
      rw [show m + m = 2 * m by ring, digitsum_two_mul m hm, ih m (by omega)]
      constructor
      · rintro ⟨j, rfl⟩; exact ⟨j+1, by ring⟩
      · rintro ⟨j, hj⟩
        cases j with
        | zero => simp at hj
        | succ k => exact ⟨k, by rw [pow_succ] at hj; omega⟩
    · obtain ⟨m, rfl⟩ := ho
      rw [Nat.digits_def' (by norm_num : 2 ≤ 2) (by omega), show (2*m+1)/2 = m by omega,
        show (2*m+1)%2 = 1 by omega]
      simp only [List.sum_cons]
      constructor
      · intro h
        have hz : (Nat.digits 2 m).sum = 0 := by omega
        rw [digitsum_eq_zero] at hz; subst hz; exact ⟨0, by norm_num⟩
      · rintro ⟨j, hj⟩
        cases j with
        | zero => obtain rfl : m = 0 := by simp only [pow_zero] at hj; omega
                  simp
        | succ k => rw [pow_succ] at hj; omega

lemma odd_choose_iff (n : ℕ) (hn : 1 ≤ n) :
    Odd (Nat.choose (2 * n - 1) n) ↔ ∃ j, n = 2 ^ j := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.choose (2 * n - 1) n ≠ 0 := (Nat.choose_pos (show n ≤ 2*n-1 by omega)).ne'
  have hodd : Odd (Nat.choose (2 * n - 1) n) ↔ ¬ (2 ∣ Nat.choose (2 * n - 1) n) := by
    rw [Nat.odd_iff, Nat.two_dvd_ne_zero.symm]
  rw [hodd, dvd_iff_padicValNat_ne_zero hc, not_ne_iff, val_choose n hn]
  have hs1 : 1 ≤ (Nat.digits 2 n).sum := by
    rcases Nat.eq_zero_or_pos ((Nat.digits 2 n).sum) with h | h
    · rw [digitsum_eq_zero] at h; omega
    · omega
  rw [← digitsum_eq_one n]
  omega

/- ### Integrality (the open Z.-W. Sun supercongruence) -/

/-- **Integrality of `a_Q`.** Each `a_Q n` is an integer.  This is Zhi-Wei Sun's
integrality conjecture for A176477.  It is equivalent to the supercongruence
`Σ_{k=0}^{(p-1)/2} (3k+1)(7k²+5k+1) C(2k,k)⁷ / 256^k ≡ 0  (mod p³)` for primes
`p = 2n+1` together with the corresponding prime-power versions, a deep
supercongruence with no current elementary proof and no supporting
infrastructure in Mathlib. -/
lemma aQ_int : ∀ n, ∃ z : ℤ, a_Q n = (z : ℚ) := by
  sorry

/- ### Parity, given integrality -/

lemma z_mod2 (k : ℕ) (z z' : ℤ) (hz : a_Q (k+2) = (z:ℚ)) (hz' : a_Q (k+1) = (z':ℚ)) :
    (z : ZMod 2) = ((k : ZMod 2) + 1) * ((Nat.choose (2*(k+2)-1) (k+2) : ℕ) : ZMod 2) := by
  have hr := a_Q_rec k
  rw [hz, hz'] at hr
  have hden : ((2 * ((k+2:ℚ)) + 1) ^ 3) ≠ 0 := by positivity
  rw [eq_div_iff hden] at hr
  have hZ : z * (2 * ((k:ℤ)+2) + 1) ^ 3
      = 32 * ((k:ℤ)+2)^3 * z'
        + (21 * ((k:ℤ)+2)^3 + 22*((k:ℤ)+2)^2 + 8*((k:ℤ)+2) + 1)
          * (Nat.choose (2*(k+2)-1) (k+2) : ℤ)^4 := by
    have : ((z * (2 * ((k:ℤ)+2) + 1) ^ 3 : ℤ) : ℚ)
        = (((32 * ((k:ℤ)+2)^3 * z' + (21 * ((k:ℤ)+2)^3 + 22*((k:ℤ)+2)^2 + 8*((k:ℤ)+2) + 1)
            * (Nat.choose (2*(k+2)-1) (k+2) : ℤ)^4) : ℤ) : ℚ) := by
      push_cast; linarith [hr]
    exact_mod_cast this
  have h2 : (z:ZMod 2) * (2 * ((k:ZMod 2)+2) + 1) ^ 3
      = 32 * ((k:ZMod 2)+2)^3 * (z':ZMod 2)
        + (21 * ((k:ZMod 2)+2)^3 + 22*((k:ZMod 2)+2)^2 + 8*((k:ZMod 2)+2) + 1)
          * ((Nat.choose (2*(k+2)-1) (k+2) : ℕ) : ZMod 2)^4 := by
    have := congrArg (Int.cast : ℤ → ZMod 2) hZ
    push_cast at this ⊢
    convert this using 2
  have key : ∀ Z Z' K Cc : ZMod 2,
      Z * (2 * (K + 2) + 1) ^ 3 = 32 * (K + 2)^3 * Z' + (21*(K+2)^3+22*(K+2)^2+8*(K+2)+1)*Cc^4
      → Z = (K + 1) * Cc := by decide
  exact key _ _ _ _ h2

/-- Parity characterisation of `a n`. -/
lemma parity (n : ℕ) (hn : n ≥ 1) : Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m := by
  -- handle n = 1 and n = k+2 separately
  match n, hn with
  | 1, _ =>
    constructor
    · intro h
      -- a 1 = 2, which is even, contradiction
      have ha1 : a 1 = 2 := by
        simp only [a]
        rw [show a_Q 1 = ((2:ℤ):ℚ) by rw [a_Q]; norm_num, Rat.floor_intCast]
        rfl
      rw [ha1] at h; exact absurd h (by decide)
    · rintro ⟨m, hm, hm2⟩
      -- 1 = 2^m with m ≥ 1 is impossible
      have : 2 ≤ 2^m := by calc 2 = 2^1 := by norm_num
                                _ ≤ 2^m := Nat.pow_le_pow_right (by norm_num) hm
      omega
  | (k+2), _ =>
    -- get integers for a_Q(k+2) and a_Q(k+1)
    obtain ⟨z, hz⟩ := aQ_int (k+2)
    obtain ⟨z', hz'⟩ := aQ_int (k+1)
    -- a (k+2) = z.toNat
    have hge : (1:ℚ) ≤ a_Q (k+2) := a_Q_ge_one (k+1)
    have hzpos : (1:ℤ) ≤ z := by rw [hz] at hge; exact_mod_cast hge
    have haz : a (k+2) = z.toNat := by
      simp only [a, hz, Rat.floor_intCast]
    rw [haz]
    -- Odd z.toNat ↔ Odd z
    have hOddTo : Odd z.toNat ↔ Odd z := by
      rw [← Int.odd_coe_nat, Int.toNat_of_nonneg (by omega : 0 ≤ z)]
    rw [hOddTo]
    -- Odd z ↔ (z : ZMod 2) = 1
    have hOddZ : Odd z ↔ (z : ZMod 2) = 1 := by
      rw [Int.odd_iff, show (1 : ZMod 2) = ((1:ℤ):ZMod 2) by norm_num,
        ZMod.intCast_eq_intCast_iff, Int.ModEq]; norm_num
    rw [hOddZ, z_mod2 k z z' hz hz']
    -- ((k:ZMod2)+1)*C = 1 ↔ (k:ZMod2)=0 ∧ C=1
    have hsplit : ∀ K Cc : ZMod 2, ((K + 1) * Cc = 1) ↔ (K = 0 ∧ Cc = 1) := by decide
    rw [hsplit]
    -- (k : ZMod 2) = 0 ↔ Even k ; (C : ZMod 2) = 1 ↔ Odd C
    have hkeven : ((k : ZMod 2) = 0) ↔ Even k := by
      rw [ZMod.natCast_eq_zero_iff k 2, even_iff_two_dvd]
    have hCodd : (((Nat.choose (2*(k+2)-1) (k+2) : ℕ) : ZMod 2) = 1)
        ↔ Odd (Nat.choose (2*(k+2)-1) (k+2)) := by
      rw [Nat.odd_iff, show (1 : ZMod 2) = ((1:ℕ):ZMod 2) by norm_num,
        ZMod.natCast_eq_natCast_iff, Nat.ModEq]
    rw [hkeven, hCodd, odd_choose_iff (k+2) (by omega)]
    -- Even k ∧ (∃ j, k+2 = 2^j) ↔ ∃ m ≥ 1, k+2 = 2^m
    constructor
    · rintro ⟨hev, j, hj⟩
      refine ⟨j, ?_, hj⟩
      -- k+2 = 2^j is ≥ 2, so j ≥ 1
      rcases Nat.eq_zero_or_pos j with h0 | h1
      · subst h0; simp only [pow_zero] at hj; omega
      · exact h1
    · rintro ⟨m, hm, hm2⟩
      refine ⟨?_, m, hm2⟩
      -- k+2 = 2^m with m ≥ 1 means k+2 even, so k even
      obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m-1, by omega⟩
      rw [pow_succ] at hm2
      exact ⟨2^t - 1, by omega⟩

theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) :=
  ⟨a_pos n hn, parity n hn⟩
