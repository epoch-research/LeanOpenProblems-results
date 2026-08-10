import FormalConjectures.Util.ProblemImports

namespace A078590

/--
Helper definition for A078590, indexed from 0.
a_val 0 corresponds to A078590(1).
a_val 1 corresponds to A078590(2).
a_val (n+2) corresponds to A078590(n+3).
The definition uses standard natural number division, relying on the conjecture that the division is exact.
-/
private noncomputable def a_val : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 =>
  let a_n_minus_2 : ℕ := a_val n
  let a_n_minus_1 : ℕ := a_val (n + 1)

  -- The division is Nat.div, which is integer division.
  -- The terms are positive, so we do not fear division by zero.
  (2 ^ a_n_minus_1 + 1) / a_n_minus_2

lemma aval_4 : a_val 4 = 171 := rfl

lemma aval_5_rel : 9 * a_val 5 = 2 ^ 171 + 1 := by
  have h5 : a_val 5 = (2 ^ 171 + 1) / 9 := by
    change a_val (3 + 2) = _
    rw [a_val]
    rfl
  have hmod : (2 ^ 171 + 1) % 9 = 0 := by rfl
  rw [h5]
  exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)

end A078590

open A078590

/--
A078590: $a(1)=1$, $a(2)=1$, $a(n)=(2^{a(n-1)} + 1)/a(n-2)$.
Are all terms integers?
-/
noncomputable def A078590 (n : ℕ) : ℕ :=
  if n ≥ 1 then
    a_val (n - 1)
  else
    0

lemma A078590_5 : A078590 5 = 171 := by
  change (if 5 ≥ 1 then a_val 4 else 0) = 171
  have hdec : 5 ≥ 1 := by decide
  rw [if_pos hdec]
  exact aval_4

lemma A078590_6 : A078590 6 = a_val 5 := by
  change (if 6 ≥ 1 then a_val 5 else 0) = a_val 5
  have hdec : 6 ≥ 1 := by decide
  rw [if_pos hdec]

lemma test_omega (x : ℕ) : (9 * x) % 81 = 27 → x % 9 = 3 := by
  intro h
  omega

lemma test_odd (x : ℕ) (h : 9 * x = 2 ^ 171 + 1) : x % 2 = 1 := by
  have h2 : (9 * x) % 2 = (2 ^ 171 + 1) % 2 := by rw [h]
  have h3 : (9 * x) % 2 = x % 2 := by omega
  have h4 : (2 ^ 171 + 1) % 2 = 1 := by decide
  omega

lemma test_mod18 (x : ℕ) : x % 9 = 3 → x % 2 = 1 → x % 18 = 3 := by
  intro h1 h2
  omega

lemma test_zmod19_pow_eighteen : (2 : ZMod 19) ^ 18 = 1 := by
  decide

lemma test_pow_mod18 (x : ℕ) (h : x % 18 = 3) : (2 : ZMod 19) ^ x = 8 := by
  have h_div : x = 18 * (x / 18) + 3 := by
    have := Nat.div_add_mod x 18
    omega
  rw [h_div]
  rw [pow_add, pow_mul]
  rw [test_zmod19_pow_eighteen]
  simp
  decide

lemma disproof_helper {x : ℕ} (h_dvd : 171 ∣ 2 ^ x + 1) (h_pow : (2 : ZMod 19) ^ x = 8) : False := by
  rcases h_dvd with ⟨k, hk⟩
  have hk_cast : ((2 ^ x + 1 : ℕ) : ZMod 19) = ((171 * k : ℕ) : ZMod 19) := by rw [hk]
  push_cast at hk_cast
  have h171 : (171 : ZMod 19) = 0 := by decide
  rw [h171, zero_mul] at hk_cast
  rw [h_pow] at hk_cast
  revert hk_cast
  decide

theorem oeis_A078590_conjecture.disproof : ¬ (∀ (n : ℕ), 3 ≤ n → A078590 (n-2) ∣ (2 ^ A078590 (n-1) + 1)) := by
  intro h_conj
  have h7 : 3 ≤ 7 := by decide
  have h_dvd := h_conj 7 h7
  -- h_dvd : A078590 5 ∣ 2 ^ A078590 6 + 1
  rw [A078590_5] at h_dvd
  -- h_dvd : 171 ∣ 2 ^ A078590 6 + 1
  have h_pow : (2 : ZMod 19) ^ A078590 6 = 8 := by
    rw [A078590_6]
    have h_mod9 : a_val 5 % 9 = 3 := by
      apply test_omega
      rw [aval_5_rel]
      rfl
    have h_odd : a_val 5 % 2 = 1 := by
      apply test_odd
      exact aval_5_rel
    have h_mod18 : a_val 5 % 18 = 3 := test_mod18 (a_val 5) h_mod9 h_odd
    exact test_pow_mod18 (a_val 5) h_mod18
  exact disproof_helper h_dvd h_pow

