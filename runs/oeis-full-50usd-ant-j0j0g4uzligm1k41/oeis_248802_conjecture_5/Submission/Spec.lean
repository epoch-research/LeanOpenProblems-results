import FormalConjectures.Util.ProblemImports

/--
A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.
-/
def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac

/--
Conjecture 5: a(138n+6) = 1669 for n >= 0 and n <> 2 mod 5.

This conjecture is FALSE. A counterexample is `n = 51` (note `51 % 5 = 1 ≠ 2`):
the prime `1399 < 1669` divides `2 ^ (2 ^ 7044 + 2) + 3` (where `7044 = 138 * 51 + 6`),
so the smallest prime factor `a (138 * 51 + 6) = 1399 ≠ 1669`.
-/
theorem oeis_248802_conjecture_5.disproof :
    ¬ ∀ (n : ℕ), n % 5 ≠ 2 → a (138 * n + 6) = 1669 := by
  intro H
  -- The smallest prime factor of `2^(2^7044+2)+3` is `1399`, not `1669`,
  -- and `7044 = 138 * 51 + 6` with `51 % 5 = 1 ≠ 2`.
  have h51 : (51 : ℕ) % 5 ≠ 2 := by decide
  have hcontra := H 51 h51
  have h7044 : (138 * 51 + 6 : ℕ) = 7044 := by norm_num
  rw [h7044] at hcontra
  -- Key divisibility fact: `1399 ∣ 2 ^ (2 ^ 7044 + 2) + 3`.
  have key : (1399 : ℕ) ∣ 2 ^ (2 ^ 7044 + 2) + 3 := by
    set E : ℕ := 2 ^ 7044 + 2 with hE
    -- Reduce the inner exponent `2^7044` modulo `233` (the order of `2` mod `1399`),
    -- using that the order of `2` mod `233` is `29`.
    have h29 : (2 : ℕ) ^ 29 ≡ 1 [MOD 233] := by unfold Nat.ModEq; decide
    have hexp : (29 * 242 + 26 : ℕ) = 7044 := by norm_num
    have hsplit : (2 : ℕ) ^ 7044 = (2 ^ 29) ^ 242 * 2 ^ 26 := by
      rw [← pow_mul, ← pow_add, hexp]
    have hexp7044 : (2 : ℕ) ^ 7044 ≡ 204 [MOD 233] := by
      rw [hsplit]
      have h := (h29.pow 242).mul_right (2 ^ 26)
      rw [one_pow, one_mul] at h
      have h26 : (2 : ℕ) ^ 26 ≡ 204 [MOD 233] := by unfold Nat.ModEq; decide
      exact h.trans h26
    have hE233 : E ≡ 206 [MOD 233] := by
      rw [hE]
      have := hexp7044.add_right 2
      simpa using this
    -- `E ≥ 206`.
    have hle206 : 206 ≤ E := by
      rw [hE]
      have h2 : (256 : ℕ) ≤ 2 ^ 7044 := by
        calc (256 : ℕ) = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ 7044 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      omega
    -- Write `E = 206 + 233 * t`.
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle206).mp hE233.symm
    have hEeq : E = 206 + 233 * t := by omega
    -- `2 ^ 233 ≡ 1 [MOD 1399]`, hence `2 ^ E ≡ 2 ^ 206 ≡ 1396 ≡ -3 [MOD 1399]`.
    have hord : (2 : ℕ) ^ 233 ≡ 1 [MOD 1399] := by unfold Nat.ModEq; decide
    have hrw : (2 : ℕ) ^ E = 2 ^ 206 * (2 ^ 233) ^ t := by
      rw [hEeq, pow_add, pow_mul]
    have e1 : (2 : ℕ) ^ E ≡ 2 ^ 206 [MOD 1399] := by
      rw [hrw]
      have h := (hord.pow t).mul_left (2 ^ 206)
      rw [one_pow, mul_one] at h
      exact h
    have e2 : (2 : ℕ) ^ 206 ≡ 1396 [MOD 1399] := by unfold Nat.ModEq; decide
    have efull : (2 : ℕ) ^ E ≡ 1396 [MOD 1399] := e1.trans e2
    have hzero : (2 : ℕ) ^ E + 3 ≡ 0 [MOD 1399] := by
      have h := efull.add_right 3
      have h0 : (1396 + 3 : ℕ) ≡ 0 [MOD 1399] := by unfold Nat.ModEq; decide
      exact h.trans h0
    exact (Nat.modEq_zero_iff_dvd).mp hzero
  -- Hence the minimal prime factor is `≤ 1399 < 1669`, contradicting the conjecture.
  have hle : (2 ^ (2 ^ 7044 + 2) + 3).minFac ≤ 1399 :=
    Nat.minFac_le_of_dvd (by norm_num) key
  unfold a at hcontra
  rw [hcontra] at hle
  norm_num at hle
