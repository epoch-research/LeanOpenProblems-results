import FormalConjectures.Util.ProblemImports

open Nat Classical

/--
Riesel problem: let $k=2n-1$; then $a(n)=$smallest $m \ge 1$ such that $k \cdot 2^m-1$ is prime, or $-1$ if no such prime exists.
We use PNat for the exponent $m$ to correctly model $m \ge 1$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 0
  else
    let k : ℕ := 2 * n - 1
    -- The predicate P(m) for m in PNat (m >= 1).
    let P (m : PNat) : Prop := (k * (2 ^ (m : ℕ)) - 1).Prime

    -- Use classical choice to find the minimum, or return -1 if no such prime exists.
    dite (∃ m : PNat, P m)
    (fun h_exists : ∃ m : PNat, P m =>
      -- PNat.find returns the minimum element. We coerce it to ℕ, then to ℤ.
      let m_min := PNat.find h_exists
      (m_min : ℕ)
    )
    (fun _ : ¬ ∃ m : PNat, P m =>
      (-1 : ℤ)
    )


namespace Riesel509203

lemma dvd_of_modEq_one {p k m : ℕ} (hp : 2 ≤ p) (h : k * 2 ^ m ≡ 1 [MOD p]) :
    p ∣ k * 2 ^ m - 1 := by
  have hle : 1 ≤ k * 2 ^ m := by
    by_contra hnot
    have hz : k * 2 ^ m = 0 := by omega
    rw [hz] at h
    have hEq : (0:ℕ) % p = 1 % p := h
    have hz0 : (0:ℕ) % p = 0 := Nat.zero_mod p
    have h1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
    omega
  exact (Nat.modEq_iff_dvd' hle).mp h.symm

lemma mod_509203_3 {m : ℕ} (hm : m % 2 = 0) :
    509203 * 2 ^ m ≡ 1 [MOD 3] := by
  have hm' : m = 2 * (m / 2) + 0 := by omega
  rw [hm', pow_add, pow_mul]
  have h1 : (2^2)^(m/2) ≡ 1 [MOD 3] := by
    simpa using ((by norm_num [Nat.ModEq] : 2^2 ≡ 1 [MOD 3]).pow (m/2))
  have h2 : 509203 * ((2^2)^(m/2) * 2^0) ≡ 509203 * (1 * 2^0) [MOD 3] := by
    exact (Nat.ModEq.refl 509203).mul (h1.mul (Nat.ModEq.refl (2^0)))
  exact h2.trans (by norm_num [Nat.ModEq])

lemma mod_509203_5 {m : ℕ} (hm : m % 4 = 1) :
    509203 * 2 ^ m ≡ 1 [MOD 5] := by
  have hm' : m = 4 * (m / 4) + 1 := by omega
  rw [hm', pow_add, pow_mul]
  have h1 : (2^4)^(m/4) ≡ 1 [MOD 5] := by
    simpa using ((by norm_num [Nat.ModEq] : 2^4 ≡ 1 [MOD 5]).pow (m/4))
  have h2 : 509203 * ((2^4)^(m/4) * 2^1) ≡ 509203 * (1 * 2^1) [MOD 5] := by
    exact (Nat.ModEq.refl 509203).mul (h1.mul (Nat.ModEq.refl (2^1)))
  exact h2.trans (by norm_num [Nat.ModEq])

lemma mod_509203_7 {m : ℕ} (hm : m % 3 = 2) :
    509203 * 2 ^ m ≡ 1 [MOD 7] := by
  have hm' : m = 3 * (m / 3) + 2 := by omega
  rw [hm', pow_add, pow_mul]
  have h1 : (2^3)^(m/3) ≡ 1 [MOD 7] := by
    simpa using ((by norm_num [Nat.ModEq] : 2^3 ≡ 1 [MOD 7]).pow (m/3))
  have h2 : 509203 * ((2^3)^(m/3) * 2^2) ≡ 509203 * (1 * 2^2) [MOD 7] := by
    exact (Nat.ModEq.refl 509203).mul (h1.mul (Nat.ModEq.refl (2^2)))
  exact h2.trans (by norm_num [Nat.ModEq])

lemma mod_509203_13 {m : ℕ} (hm : m % 12 = 7) :
    509203 * 2 ^ m ≡ 1 [MOD 13] := by
  have hm' : m = 12 * (m / 12) + 7 := by omega
  rw [hm', pow_add, pow_mul]
  have h1 : (2^12)^(m/12) ≡ 1 [MOD 13] := by
    simpa using ((by norm_num [Nat.ModEq] : 2^12 ≡ 1 [MOD 13]).pow (m/12))
  have h2 : 509203 * ((2^12)^(m/12) * 2^7) ≡ 509203 * (1 * 2^7) [MOD 13] := by
    exact (Nat.ModEq.refl 509203).mul (h1.mul (Nat.ModEq.refl (2^7)))
  exact h2.trans (by norm_num [Nat.ModEq])

lemma mod_509203_17 {m : ℕ} (hm : m % 8 = 7) :
    509203 * 2 ^ m ≡ 1 [MOD 17] := by
  have hm' : m = 8 * (m / 8) + 7 := by omega
  rw [hm', pow_add, pow_mul]
  have h1 : (2^8)^(m/8) ≡ 1 [MOD 17] := by
    simpa using ((by norm_num [Nat.ModEq] : 2^8 ≡ 1 [MOD 17]).pow (m/8))
  have h2 : 509203 * ((2^8)^(m/8) * 2^7) ≡ 509203 * (1 * 2^7) [MOD 17] := by
    exact (Nat.ModEq.refl 509203).mul (h1.mul (Nat.ModEq.refl (2^7)))
  exact h2.trans (by norm_num [Nat.ModEq])

lemma mod_509203_241 {m : ℕ} (hm : m % 24 = 3) :
    509203 * 2 ^ m ≡ 1 [MOD 241] := by
  have hm' : m = 24 * (m / 24) + 3 := by omega
  rw [hm', pow_add, pow_mul]
  have h1 : (2^24)^(m/24) ≡ 1 [MOD 241] := by
    simpa using ((by norm_num [Nat.ModEq] : 2^24 ≡ 1 [MOD 241]).pow (m/24))
  have h2 : 509203 * ((2^24)^(m/24) * 2^3) ≡ 509203 * (1 * 2^3) [MOD 241] := by
    exact (Nat.ModEq.refl 509203).mul (h1.mul (Nat.ModEq.refl (2^3)))
  exact h2.trans (by norm_num [Nat.ModEq])

lemma cover_residue (m : ℕ) :
    m % 2 = 0 ∨ m % 4 = 1 ∨ m % 3 = 2 ∨
      m % 12 = 7 ∨ m % 8 = 7 ∨ m % 24 = 3 := by
  let r := m % 24
  have hrlt : r < 24 := Nat.mod_lt _ (by norm_num)
  interval_cases r <;> simp at * <;> omega

lemma divisor_lt_term (m : PNat) {p : ℕ} (hp : p ≤ 241) :
    p < 509203 * 2 ^ (m : ℕ) - 1 := by
  have hm1 : 1 ≤ (m : ℕ) := m.2
  have hpow : 2 ≤ 2 ^ (m : ℕ) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (m : ℕ) := Nat.pow_le_pow_right (by norm_num) hm1
  have hmul : 1018406 ≤ 509203 * 2 ^ (m : ℕ) := by nlinarith
  have hbig : 241 < 509203 * 2 ^ (m : ℕ) - 1 := by omega
  exact lt_of_le_of_lt hp hbig

lemma composite_509203 (m : PNat) : ¬ (509203 * 2 ^ (m : ℕ) - 1).Prime := by
  rcases cover_residue (m : ℕ) with h3 | h5 | h7 | h13 | h17 | h241
  · exact Nat.not_prime_of_dvd_of_lt (dvd_of_modEq_one (by norm_num) (mod_509203_3 h3)) (by norm_num) (divisor_lt_term m (by norm_num))
  · exact Nat.not_prime_of_dvd_of_lt (dvd_of_modEq_one (by norm_num) (mod_509203_5 h5)) (by norm_num) (divisor_lt_term m (by norm_num))
  · exact Nat.not_prime_of_dvd_of_lt (dvd_of_modEq_one (by norm_num) (mod_509203_7 h7)) (by norm_num) (divisor_lt_term m (by norm_num))
  · exact Nat.not_prime_of_dvd_of_lt (dvd_of_modEq_one (by norm_num) (mod_509203_13 h13)) (by norm_num) (divisor_lt_term m (by norm_num))
  · exact Nat.not_prime_of_dvd_of_lt (dvd_of_modEq_one (by norm_num) (mod_509203_17 h17)) (by norm_num) (divisor_lt_term m (by norm_num))
  · exact Nat.not_prime_of_dvd_of_lt (dvd_of_modEq_one (by norm_num) (mod_509203_241 h241)) (by norm_num) (divisor_lt_term m (by norm_num))

lemma a_254602_eq_neg_one : a 254602 = -1 := by
  simp [a]
  intro m hm
  exact composite_509203 m hm

end Riesel509203

/--
It is conjectured that the integer k = 509203 is the smallest Riesel number,
that is, the first n such that a(n) = -1 is 254602.
-/
theorem oeis_a108129_conjecture_0 :
  a 254602 = -1 ∧ (∀ n : ℕ, 1 ≤ n ∧ n < 254602 → a n ≠ -1) :=
by
  constructor
  · exact Riesel509203.a_254602_eq_neg_one
  · sorry
