import Mathlib

open Nat

set_option maxHeartbeats 0

def IsWX (m : ℕ) : Prop := ∃ w x : ℕ, w ^ 2 + 2 * x ^ 2 = m

lemma isWX_zero : IsWX 0 := ⟨0, 0, by simp⟩
lemma isWX_one : IsWX 1 := ⟨1, 0, by simp⟩
lemma isWX_two : IsWX 2 := ⟨0, 1, by simp⟩

lemma isWX_mul_two {n : ℕ} (h : IsWX n) : IsWX (2 * n) := by
  obtain ⟨w, x, rfl⟩ := h
  exact ⟨2 * x, w, by ring⟩

lemma even_of_sq_add_two_sq_even {w x n : ℕ}
    (h : w ^ 2 + 2 * x ^ 2 = 2 * n) : Even w := by
  have hx : x ^ 2 ≤ n := by
    have : 2 * x ^ 2 ≤ 2 * n := by
      have h' : 2 * x ^ 2 ≤ w ^ 2 + 2 * x ^ 2 := Nat.le_add_left _ _
      simpa [h] using h'
    omega
  have hw2 : w ^ 2 = 2 * (n - x ^ 2) := by
    zify [hx] at h ⊢
    linarith
  have he : Even (w ^ 2) := ⟨n - x ^ 2, by
    -- Even m means ∃ k, m = k + k
    simpa [two_mul] using hw2⟩
  exact (Nat.even_pow (n := 2)).mp he |>.1

lemma isWX_of_mul_two {n : ℕ} (h : IsWX (2 * n)) : IsWX n := by
  obtain ⟨w, x, hw⟩ := h
  obtain ⟨k, hk⟩ := even_of_sq_add_two_sq_even hw
  refine ⟨x, k, ?_⟩
  have hw' : (k + k) ^ 2 + 2 * x ^ 2 = 2 * n := by simpa [hk] using hw
  nlinarith

lemma isWX_two_mul_iff (n : ℕ) : IsWX (2 * n) ↔ IsWX n :=
  ⟨isWX_of_mul_two, isWX_mul_two⟩

def oddPart (n : ℕ) : ℕ := n / 2 ^ padicValNat 2 n

lemma oddPart_zero : oddPart 0 = 0 := by simp [oddPart]

lemma oddPart_odd {n : ℕ} (h : Odd n) : oddPart n = n := by
  have : padicValNat 2 n = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun hd =>
      (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr hd))
  simp [oddPart, this]

lemma oddPart_pos {n : ℕ} (hn : n ≠ 0) : 0 < oddPart n := by
  have hpow : 0 < 2 ^ padicValNat 2 n := pow_pos (by decide) _
  have hle : 2 ^ padicValNat 2 n ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd
  exact Nat.div_pos hle hpow

lemma two_pow_mul_oddPart (n : ℕ) : 2 ^ padicValNat 2 n * oddPart n = n :=
  Nat.mul_div_cancel' pow_padicValNat_dvd

lemma not_two_dvd_oddPart {n : ℕ} (hn : n ≠ 0) : ¬ 2 ∣ oddPart n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have hne : oddPart n ≠ 0 := (oddPart_pos hn).ne'
  have hpos : padicValNat 2 (oddPart n) ≠ 0 :=
    (dvd_iff_padicValNat_ne_zero hne).1 h
  have heq : padicValNat 2 (oddPart n) = 0 := by
    have hne2 : 2 ^ padicValNat 2 n ≠ 0 := pow_ne_zero _ (by decide)
    have hv : padicValNat 2 n =
        padicValNat 2 (2 ^ padicValNat 2 n * oddPart n) := by
      rw [two_pow_mul_oddPart]
    rw [padicValNat.mul hne2 hne, padicValNat.prime_pow] at hv
    omega
  exact hpos heq

lemma odd_oddPart {n : ℕ} (hn : n ≠ 0) : Odd (oddPart n) :=
  Nat.odd_iff.mpr (by
    have : ¬ Even (oddPart n) := fun he =>
      not_two_dvd_oddPart hn (even_iff_two_dvd.mp he)
    exact Nat.not_even_iff.mp this)

lemma padicValNat_two_two : padicValNat 2 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact padicValNat_self

lemma oddPart_two_mul {n : ℕ} (hn : n ≠ 0) : oddPart (2 * n) = oddPart n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold oddPart
  have hv : padicValNat 2 (2 * n) = 1 + padicValNat 2 n := by
    rw [padicValNat.mul (by decide) hn, padicValNat_two_two]
  rw [hv, pow_add, pow_one]
  -- 2*n / (2 * 2^v) = n / 2^v
  have hpos : 0 < 2 := by decide
  rw [Nat.mul_div_mul_left n (2 ^ padicValNat 2 n) hpos]

lemma isWX_pow_two {v n : ℕ} (h : IsWX n) : IsWX (2 ^ v * n) := by
  induction v with
  | zero => simpa using h
  | succ v ih =>
    rw [pow_succ', mul_assoc]
    exact isWX_mul_two ih

lemma isWX_of_pow_two {v n : ℕ} (h : IsWX (2 ^ v * n)) : IsWX n := by
  induction v generalizing n with
  | zero => simpa using h
  | succ v ih =>
    rw [pow_succ', mul_assoc] at h
    exact ih (isWX_of_mul_two h)

lemma isWX_oddPart_iff (n : ℕ) : IsWX n ↔ IsWX (oddPart n) := by
  constructor
  · intro h
    have h' : IsWX (2 ^ padicValNat 2 n * oddPart n) := by
      simpa [two_pow_mul_oddPart] using h
    exact isWX_of_pow_two h'
  · intro h
    have h' : IsWX (2 ^ padicValNat 2 n * oddPart n) := isWX_pow_two h
    simpa [two_pow_mul_oddPart] using h'

#check isWX_two_mul_iff
#check isWX_oddPart_iff
#check odd_oddPart
#check oddPart_two_mul

lemma padicValNat_eq_one_of_lt_sq {q n : ℕ} [hq : Fact q.Prime]
    (hn : n ≠ 0) (hdvd : q ∣ n) (hlt : n < q * q) : padicValNat q n = 1 := by
  have hge : 1 ≤ padicValNat q n := one_le_padicValNat_of_dvd hn hdvd
  have hlt2 : padicValNat q n < 2 := by
    by_contra hge2
    have : 2 ≤ padicValNat q n := le_of_not_gt hge2
    have hd : q ^ 2 ∣ n :=
      (pow_dvd_pow q this).trans pow_padicValNat_dvd
    have : q * q ≤ n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (by simpa [pow_two] using hd)
    exact (lt_irrefl _ (this.trans_lt hlt))
  omega

lemma isWX_mod8_ne {n : ℕ} (h : IsWX n) : n % 8 ≠ 5 ∧ n % 8 ≠ 7 := by
  obtain ⟨w, x, rfl⟩ := h
  have ha : w ^ 2 % 8 = 0 ∨ w ^ 2 % 8 = 1 ∨ w ^ 2 % 8 = 4 := by
    have : w % 8 < 8 := Nat.mod_lt _ (by decide)
    have heq : w ^ 2 % 8 = (w % 8) ^ 2 % 8 := by rw [pow_two, pow_two, Nat.mul_mod]
    rw [heq]; interval_cases w % 8 <;> simp
  have hb : (2 * x ^ 2) % 8 = 0 ∨ (2 * x ^ 2) % 8 = 2 := by
    by_cases he : Even x
    · obtain ⟨c, hc⟩ := he
      have : 2 * x ^ 2 = 8 * c ^ 2 := by rw [hc]; ring
      left; rw [this, Nat.mul_mod]; simp
    · have : x ^ 2 % 8 = 1 := by
        have : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by
          have hm : x % 8 < 8 := Nat.mod_lt _ (by decide)
          have : x % 2 = 1 := Nat.odd_iff.mp (Nat.odd_iff_not_even.mpr he)
          interval_cases x % 8 <;> omega
        have heq : x ^ 2 % 8 = (x % 8) ^ 2 % 8 := by rw [pow_two, pow_two, Nat.mul_mod]
        rw [heq]; rcases this with h | h | h | h <;> simp [h]
      right
      have : 2 * x ^ 2 % 8 = 2 * (x ^ 2 % 8) % 8 := Nat.mul_mod _ _ _
      omega
  have heq : (w ^ 2 + 2 * x ^ 2) % 8 = (w ^ 2 % 8 + (2 * x ^ 2) % 8) % 8 :=
    Nat.add_mod _ _ _
  refine ⟨?_, ?_⟩
  · intro h5; rw [heq] at h5; rcases ha with ha | ha | ha <;> rcases hb with hb | hb <;> omega
  · intro h7; rw [heq] at h7; rcases ha with ha | ha | ha <;> rcases hb with hb | hb <;> omega

lemma isWX_of_odd_mod8_large_bad {K : ℕ}
    (hWX : IsWX K ↔ ∀ q, q.Prime → (q % 8 = 5 ∨ q % 8 = 7) → Even (padicValNat q K))
    (hodd : Odd K) (h13 : K % 8 = 1 ∨ K % 8 = 3)
    (hsmall : ∀ q, q.Prime → (q % 8 = 5 ∨ q % 8 = 7) → q ∣ K → K < q * q) :
    IsWX K := by
  rw [hWX]
  intro q hq h8
  by_cases hdvd : q ∣ K
  · have : Fact q.Prime := ⟨hq⟩
    have hK0 : K ≠ 0 := Nat.ne_of_gt (Odd.pos hodd)
    have hv1 : padicValNat q K = 1 :=
      padicValNat_eq_one_of_lt_sq hK0 hdvd (hsmall q hq h8 hdvd)
    have hwrite : K = (K / q) * q := (Nat.div_mul_cancel hdvd).symm
    have hsodd : Odd (K / q) := by
      have : Odd ((K / q) * q) := by simpa [hwrite] using hodd
      exact Odd.of_mul_right this
    have hno : ∀ r, r.Prime → (r % 8 = 5 ∨ r % 8 = 7) → r ≠ q → ¬ r ∣ K := by
      intro r hr h8r hne hd
      have hcop : Nat.Coprime r q := Nat.coprime_primes hr hq hne
      have hmul : r * q ∣ K := hcop.mul_dvd_of_dvd_of_dvd hd hdvd
      have hge : r * q ≤ K := Nat.le_of_dvd (Nat.pos_of_ne_zero hK0) hmul
      have hr2 : K < r * r := hsmall r hr h8r hd
      have hq2 : K < q * q := hsmall q hq h8 hdvd
      have h1 : q < r :=
        lt_of_mul_lt_mul_left (hge.trans_lt hr2) (Nat.zero_le _)
      have h2 : r < q :=
        lt_of_mul_lt_mul_right (hge.trans_lt hq2) (Nat.zero_le _)
      exact lt_asymm h1 h2
    have hsWX : IsWX (K / q) := by
      rw [hWX]
      intro r hr h8r
      by_cases hrd : r ∣ K / q
      · have hrK : r ∣ K := hrd.trans (Nat.div_dvd_of_dvd hdvd)
        have hrq : r = q := by
          by_contra hne; exact hno r hr h8r hne hrK
        subst hrq
        have hqq : q ∣ K / q := hrd
        have : q ^ 2 ∣ K := by
          have := (Nat.dvd_div_iff_mul_dvd hdvd).mp hqq
          simpa [pow_two, mul_comm] using this
        have h2le : 2 ≤ padicValNat q K :=
          le_padicValNat_of_dvd (by decide : 2 ≠ 0) this
        omega
      · have : Fact r.Prime := ⟨hr⟩
        rw [padicValNat.eq_zero_of_not_dvd hrd]
        exact even_zero
    have hmod : (K / q) % 8 = 1 ∨ (K / q) % 8 = 3 := by
      have hne57 := isWX_mod8_ne hsWX
      have hm : (K / q) % 8 < 8 := Nat.mod_lt _ (by decide)
      have hodd8 : (K / q) % 2 = 1 := Nat.odd_iff.mp hsodd
      interval_cases hsq : (K / q) % 8 <;> omega
    have hK8 : K % 8 = ((K / q) % 8 * (q % 8)) % 8 := by
      rw [hwrite, Nat.mul_mod]
    rcases hmod with hm1 | hm3 <;> rcases h8 with hq5 | hq7
    · simp [hK8, hm1, hq5] at h13
    · simp [hK8, hm1, hq7] at h13
    · simp [hK8, hm3, hq5] at h13
    · simp [hK8, hm3, hq7] at h13
  · have : Fact q.Prime := ⟨hq⟩
    rw [padicValNat.eq_zero_of_not_dvd hdvd]
    exact even_zero

#check isWX_of_odd_mod8_large_bad
