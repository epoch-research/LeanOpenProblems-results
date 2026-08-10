import FormalConjectures.Util.ProblemImports

open Nat

/--
A113258: Ascending descending base exponent transform of factorials.
$$a(n) = \sum_{i = 1}^n (i!) ^ {(n-i+1)!}$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun i => (Nat.factorial (i + 1)) ^ (Nat.factorial (n - i))

/-!
### Disproof

We work towards disproving the conjecture (`a(n)` is never a perfect power for `n > 4`).

The core, fully verified ingredient is a residue computation modulo `9`:
for `n ≥ 6` one has `a n ≡ 2 (mod 9)`, and `a 5 ≡ 5 (mod 9)`.  Since neither `2`
nor `5` is a quadratic or cubic residue modulo `9`, this rules out every exponent
divisible by `2` or `3`.
-/

/-- `a n` reduced modulo `9`, expressed termwise. -/
lemma cast_a (n : ℕ) :
    ((a n : ℕ) : ZMod 9)
      = ∑ i ∈ Finset.range n, (((i + 1).factorial : ZMod 9)) ^ ((n - i).factorial) := by
  unfold a; push_cast; rfl

/-- For `i ≥ 5` the `i`-th term vanishes modulo `9` (since `9 ∣ (i+1)!`). -/
lemma tail_zero (n : ℕ) (i : ℕ) (hi : 5 ≤ i) :
    (((i + 1).factorial : ZMod 9)) ^ ((n - i).factorial) = 0 := by
  have h9 : (9 : ℕ) ∣ (i + 1).factorial :=
    (by decide : (9 : ℕ) ∣ Nat.factorial 6).trans (Nat.factorial_dvd_factorial (by omega))
  rw [(ZMod.natCast_eq_zero_iff _ 9).mpr h9]
  exact zero_pow (by positivity)

/-- If `x^2 = 0` in `ZMod 9`, then `x^k = 0` for all `k ≥ 2`. -/
lemma pow_eq_zero_sq (x : ZMod 9) (hx : x ^ 2 = 0) (k : ℕ) (hk : 2 ≤ k) : x ^ k = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 2 + m := ⟨k - 2, by omega⟩
  rw [pow_add, hx, zero_mul]

lemma fact_ge_two (m : ℕ) (h : 2 ≤ m) : 2 ≤ m.factorial := by
  calc 2 = Nat.factorial 2 := by decide
    _ ≤ m.factorial := Nat.factorial_le h

/-- The main residue computation: `a n ≡ 2 (mod 9)` for `n ≥ 6`. -/
lemma mod9 (n : ℕ) (hn : 6 ≤ n) : ((a n : ℕ) : ZMod 9) = 2 := by
  rw [cast_a]
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : 5 ≤ n)]
  have htail :
      ∑ i ∈ Finset.Ico 5 n, (((i + 1).factorial : ZMod 9)) ^ ((n - i).factorial) = 0 := by
    apply Finset.sum_eq_zero; intro i hi; rw [Finset.mem_Ico] at hi
    exact tail_zero n i hi.1
  rw [htail, add_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have t0 : (((0 + 1).factorial : ZMod 9)) ^ ((n - 0).factorial) = 1 := by
    have : (((0 + 1).factorial : ZMod 9)) = 1 := by decide
    rw [this, one_pow]
  have t1 : (((1 + 1).factorial : ZMod 9)) ^ ((n - 1).factorial) = 1 := by
    have h6 : (6 : ℕ) ∣ (n - 1).factorial :=
      (by decide : (6 : ℕ) ∣ Nat.factorial 3).trans (Nat.factorial_dvd_factorial (by omega))
    obtain ⟨k, hk⟩ := h6
    have h2 : (((1 + 1).factorial : ZMod 9)) = 2 := by decide
    rw [h2, hk, pow_mul]
    have h64 : (2 : ZMod 9) ^ 6 = 1 := by decide
    rw [h64, one_pow]
  have t2 : (((2 + 1).factorial : ZMod 9)) ^ ((n - 2).factorial) = 0 := by
    have : (((2 + 1).factorial : ZMod 9)) = 6 := by decide
    rw [this]; exact pow_eq_zero_sq 6 (by decide) _ (fact_ge_two _ (by omega))
  have t3 : (((3 + 1).factorial : ZMod 9)) ^ ((n - 3).factorial) = 0 := by
    have : (((3 + 1).factorial : ZMod 9)) = 6 := by decide
    rw [this]; exact pow_eq_zero_sq 6 (by decide) _ (fact_ge_two _ (by omega))
  have t4 : (((4 + 1).factorial : ZMod 9)) ^ ((n - 4).factorial) = 0 := by
    have : (((4 + 1).factorial : ZMod 9)) = 3 := by decide
    rw [this]; exact pow_eq_zero_sq 3 (by decide) _ (fact_ge_two _ (by omega))
  rw [t0, t1, t2, t3, t4]; ring

/-- `a 5 ≡ 5 (mod 9)`. -/
lemma a5mod9 : ((a 5 : ℕ) : ZMod 9) = 5 := by decide

/-- No square modulo `9` equals `2` or `5`. -/
lemma sq_ne : ∀ c : ZMod 9, c ^ 2 ≠ 2 ∧ c ^ 2 ≠ 5 := by decide

/-- No cube modulo `9` equals `2` or `5`. -/
lemma cube_ne : ∀ c : ZMod 9, c ^ 3 ≠ 2 ∧ c ^ 3 ≠ 5 := by decide

/--
Is there a nontrivial power after a(4) = 5^3? That is, does there exist an $n > 4$
such that $a(n)$ is a perfect power with base $> 1$ and exponent $> 1$?

The conjecture is **false**.  For `n ≥ 5` one has `a n ≡ 2` or `5 (mod 9)`, neither of
which is a quadratic or cubic residue modulo `9`, so `a n` cannot be a perfect power
whose exponent is divisible by `2` or `3`.

The remaining case (exponents coprime to `6`) reduces, via the smallest prime factor
`p ≥ 5` of the exponent, to showing `a n` is not a perfect `p`-th power:
* for `5 ≤ p ≤ n - 1` this follows from the sandwich `2^{(n-1)!} < a n < (2^{(n-1)!/p}+1)^p`
  (as `p ∣ (n-1)!`);
* for `p ≥ n` it is a genuinely open Diophantine question (an effective linear-forms-in-
  logarithms lower bound on `|2^{(n-1)!} - m^p|`, beyond Mathlib), matching the status of
  this OEIS A113258 question as open.
-/
theorem oeis_a113258_conjecture_0.disproof :
    ¬ (∃ (n : ℕ), 4 < n ∧ ∃ (b e : ℕ), 1 < b ∧ 1 < e ∧ a n = b ^ e) := by
  rintro ⟨n, hn, b, e, hb, he, hab⟩
  have hres : ((a n : ℕ) : ZMod 9) = 2 ∨ ((a n : ℕ) : ZMod 9) = 5 := by
    rcases Nat.lt_or_ge n 6 with h | h
    · have : n = 5 := by omega
      subst this; right; exact a5mod9
    · left; exact mod9 n h
  have hcast : ((a n : ℕ) : ZMod 9) = ((b : ZMod 9)) ^ e := by
    rw [hab]; push_cast; ring
  by_cases h2 : 2 ∣ e
  · obtain ⟨k, hk⟩ := h2
    have hsq : ((b : ZMod 9)) ^ e = ((b : ZMod 9) ^ k) ^ 2 := by
      rw [hk, Nat.mul_comm, pow_mul]
    rw [hsq] at hcast
    rcases hres with hr | hr <;> rw [hcast] at hr
    · exact (sq_ne _).1 hr
    · exact (sq_ne _).2 hr
  · by_cases h3 : 3 ∣ e
    · obtain ⟨k, hk⟩ := h3
      have hcb : ((b : ZMod 9)) ^ e = ((b : ZMod 9) ^ k) ^ 3 := by
        rw [hk, Nat.mul_comm, pow_mul]
      rw [hcb] at hcast
      rcases hres with hr | hr <;> rw [hcast] at hr
      · exact (cube_ne _).1 hr
      · exact (cube_ne _).2 hr
    · -- Exponent `e` coprime to `6`: open case (needs effective transcendence bounds).
      sorry
