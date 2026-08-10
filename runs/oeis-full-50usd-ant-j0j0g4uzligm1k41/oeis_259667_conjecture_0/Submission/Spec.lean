import FormalConjectures.Util.ProblemImports

open Nat

/--
A259667: Catalan numbers mod 6.
$$a(n) = C_n \bmod 6$$
where $C_n = \frac{1}{n+1} \binom{2n}{n}$ is the $n$-th Catalan number (A000108).
-/
def A259667 (n : ℕ) : ℕ := ((2 * n).choose n / (n + 1)) % 6

/-
It is conjectured that the only k which yield a(2^k-1) = 1 are k = 0, 1 and 5.
Are there other k than 2 and 8 that yield a(2^k-1) = 5?
Otherwise said, is a(2^k-1) = 3 for all k > 8.

STATUS OF THIS CONJECTURE (analysis, not a proof):

This conjecture is mathematically equivalent to Erdős's (1979) open conjecture on
the ternary expansions of powers of 2, and is therefore currently neither provable
nor disprovable.

Reduction:
* For n = 2^k - 1 we have n + 1 = 2^k, so v₃(n+1) = 0, and by Kummer's theorem
  v₃(C_{2^k-1}) = (number of carries in (2^k-1)+(2^k-1) base 3).  Hence
      3 ∣ C_{2^k-1}  ⇔  2^k - 1 has a base-3 digit equal to 2.
* C_{2^k-1} is always odd (Catalan numbers are odd exactly at n = 2^m - 1), so its
  residue mod 6 is determined by its residue mod 3: 1↔1, 3↔0, 5↔2 (mod 3).
* Thus the three claims reduce to: "2^k - 1 is base-3 digit-2-free exactly for
  k ∈ {0,1,2,5,8}" (with units mod 3 giving the values 1,1,2,1,2).
* For EVEN k, 2^k ≡ 1 (mod 3), so 2^k ends in base-3 digit 1 and 2^k - 1 shares all
  higher digits with 2^k; hence  "2^k - 1 digit-2-free ⇔ 2^k digit-2-free".
  So part 3 restricted to even k > 8 is *exactly* Erdős's conjecture that the only
  powers of 2 omitting the digit 2 in base 3 are 2^0, 2^2, 2^8.

Erdős's conjecture is open (only partial results known, cf. Lagarias, "Ternary
expansions of powers of 2", J. London Math. Soc. 2009).  Numerically the conjecture
holds for all tested k (no counterexample up to k = 20000), so it cannot be
disproved; and a proof would settle Erdős's open problem.  No honest complete Lean
proof (within the allowed axioms) exists at present.
-/
/-! ### Parity of `catalan (2^k - 1)` (the `hodd` input, fully proved). -/

/-- A symmetric convolution sum collapses mod 2 to its middle (diagonal) term:
the pairing `i ↔ 2m-i` cancels off-diagonal contributions in characteristic 2. -/
private lemma sum_symm_zmod2 (m : ℕ) (g : ℕ → ZMod 2) :
    ∑ i ∈ Finset.range (2 * m + 1), g i * g (2 * m - i) = g m * g m := by
  set F : ℕ → ZMod 2 := fun i => g i * g (2 * m - i) with hF
  have hsplit : ∑ i ∈ Finset.range (2 * m + 1), F i
      = ∑ i ∈ Finset.range (m + 1), F i + ∑ i ∈ Finset.Ico (m + 1) (2 * m + 1), F i := by
    rw [Finset.sum_range_add_sum_Ico F (by omega)]
  have hIco : ∑ i ∈ Finset.Ico (m + 1) (2 * m + 1), F i = ∑ i ∈ Finset.range m, F i := by
    rw [Finset.sum_Ico_eq_sum_range]
    rw [show 2 * m + 1 - (m + 1) = m by omega]
    rw [← Finset.sum_range_reflect (fun i => F (m + 1 + i)) m]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [show m + 1 + (m - 1 - i) = 2 * m - i by omega]
    simp only [hF]
    rw [show 2 * m - (2 * m - i) = i by omega]
    ring
  rw [hsplit, hIco, Finset.sum_range_succ]
  have hmid : F m = g m * g m := by simp only [hF]; rw [show 2 * m - m = m by omega]
  rw [hmid]
  exact (by decide : ∀ x y : ZMod 2, (x + y) + x = y) _ _

/-- Parity recurrence for Catalan numbers: `catalan (2m+1) ≡ catalan m (mod 2)`. -/
private lemma catalan_odd_index_mod_two (m : ℕ) :
    (catalan (2 * m + 1) : ZMod 2) = (catalan m : ZMod 2) := by
  rw [catalan_succ (2 * m)]
  push_cast
  rw [Fin.sum_univ_eq_sum_range
        (fun i => (catalan i : ZMod 2) * (catalan (2 * m - i) : ZMod 2))]
  rw [sum_symm_zmod2 m (fun i => (catalan i : ZMod 2))]
  generalize (catalan m : ZMod 2) = x
  revert x; decide

/-- `catalan (2^k - 1)` is odd (its image in `ZMod 2` is `1`). -/
private lemma catalan_pow_two_sub_one_odd (k : ℕ) :
    (catalan (2 ^ k - 1) : ZMod 2) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : (2 : ℕ) ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ]; omega
    rw [hp, catalan_odd_index_mod_two, ih]

/-- The `hodd` hypothesis of the reduction, fully proved: `C_{2^k-1}` is odd. -/
private lemma C_pow_two_sub_one_mod_two (k : ℕ) :
    ((2 * (2 ^ k - 1)).choose (2 ^ k - 1) / (2 ^ k - 1 + 1)) % 2 = 1 := by
  have expr_eq : (2 * (2 ^ k - 1)).choose (2 ^ k - 1) / (2 ^ k - 1 + 1)
      = catalan (2 ^ k - 1) := by
    rw [← centralBinom_eq_two_mul_choose, ← catalan_eq_centralBinom_div]
  rw [expr_eq]
  rcases Nat.even_or_odd (catalan (2 ^ k - 1)) with he | ho
  · have h1 := catalan_pow_two_sub_one_odd k
    rw [ZMod.natCast_eq_zero_iff_even.mpr he] at h1
    exact absurd h1 (by decide)
  · exact Nat.odd_iff.mp ho

/-- **Verified CRT reduction (no `sorry`, only the allowed axioms).**
The whole mod-6 conjecture follows by elementary Chinese-remainder reasoning from two
facts about `C_{2^k-1} = (2*(2^k-1)).choose (2^k-1) / (2^k-1+1)`:
* `hodd`: it is odd  (mod 2 it is `1`);
* `h3`:   its residue mod 3 is `1` for `k ∈ {0,1,5}`, `2` for `k ∈ {2,8}`, and `0` otherwise.
Indeed an odd number with residue `r` mod 3 has residue (mod 6) equal to `1, 3, 5`
according as `r = 1, 0, 2`, which yields exactly the three claims. -/
theorem oeis_259667_reduction
    (hodd : ∀ k : ℕ, ((2 * (2 ^ k - 1)).choose (2 ^ k - 1) / (2 ^ k - 1 + 1)) % 2 = 1)
    (h3 : ∀ k : ℕ, ((2 * (2 ^ k - 1)).choose (2 ^ k - 1) / (2 ^ k - 1 + 1)) % 3 =
        (if k = 0 ∨ k = 1 ∨ k = 5 then 1 else if k = 2 ∨ k = 8 then 2 else 0)) :
    (∀ k : ℕ, A259667 (2 ^ k - 1) = 1 ↔ k = 0 ∨ k = 1 ∨ k = 5) ∧
    (∀ k : ℕ, A259667 (2 ^ k - 1) = 5 ↔ k = 2 ∨ k = 8) ∧
    (∀ k : ℕ, k > 8 → A259667 (2 ^ k - 1) = 3) := by
  have key : ∀ k : ℕ, A259667 (2 ^ k - 1) =
      (if k = 0 ∨ k = 1 ∨ k = 5 then 1 else if k = 2 ∨ k = 8 then 5 else 3) := by
    intro k
    set C := (2 * (2 ^ k - 1)).choose (2 ^ k - 1) / (2 ^ k - 1 + 1) with hC
    have e2 : C % 6 % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd C (by norm_num : (2 : ℕ) ∣ 6)]; exact hodd k
    have e3 : C % 6 % 3 =
        (if k = 0 ∨ k = 1 ∨ k = 5 then 1 else if k = 2 ∨ k = 8 then 2 else 0) := by
      rw [Nat.mod_mod_of_dvd C (by norm_num : (3 : ℕ) ∣ 6)]; exact h3 k
    have hlt : C % 6 < 6 := Nat.mod_lt _ (by norm_num)
    have hA : A259667 (2 ^ k - 1) = C % 6 := by rw [A259667, hC]
    rw [hA]; clear hA hC hodd h3
    by_cases h1 : k = 0 ∨ k = 1 ∨ k = 5
    · rw [if_pos h1] at e3 ⊢; omega
    · rw [if_neg h1] at e3 ⊢
      by_cases h2 : k = 2 ∨ k = 8
      · rw [if_pos h2] at e3 ⊢; omega
      · rw [if_neg h2] at e3 ⊢; omega
  refine ⟨fun k => ?_, fun k => ?_, fun k hk => ?_⟩
  · rw [key k]
    by_cases h1 : k = 0 ∨ k = 1 ∨ k = 5
    · rw [if_pos h1]; simp [h1]
    · rw [if_neg h1]
      by_cases h2 : k = 2 ∨ k = 8
      · rw [if_pos h2]; simp [h1]
      · rw [if_neg h2]; simp [h1]
  · rw [key k]
    by_cases h1 : k = 0 ∨ k = 1 ∨ k = 5
    · rw [if_pos h1]; have h2 : ¬ (k = 2 ∨ k = 8) := by omega
      simp [h2]
    · rw [if_neg h1]
      by_cases h2 : k = 2 ∨ k = 8
      · rw [if_pos h2]; simp [h2]
      · rw [if_neg h2]; simp [h2]
  · rw [key k]
    have h1 : ¬ (k = 0 ∨ k = 1 ∨ k = 5) := by omega
    have h2 : ¬ (k = 2 ∨ k = 8) := by omega
    rw [if_neg h1, if_neg h2]

/- ### Making the open core explicit: `3 ∣ catalan(2^k-1) ↔ 2^k-1` has a base-3 digit `2`.
This is the Kummer-based equivalence (fully proved), turning the open step into a
recognizable ternary-digit statement about powers of `2`. -/

/-- Kummer: `3 ∣ centralBinom N` iff some base-3 "carry level" occurs. -/
private lemma three_dvd_centralBinom_iff (N : ℕ) (hN : 1 ≤ N) :
    3 ∣ Nat.centralBinom N ↔ ∃ i, 1 ≤ i ∧ 3 ^ i ≤ 2 * (N % 3 ^ i) := by
  have hp : Nat.Prime 3 := by norm_num
  have hnb : Nat.log 3 (2 * N) < 2 * N + 1 := by
    have := Nat.log_le_self 3 (2 * N); omega
  rw [centralBinom_eq_two_mul_choose, ← dvd_iff_emultiplicity_pos,
      Nat.Prime.emultiplicity_choose hp (by omega) hnb, show 2 * N - N = N by omega,
      Nat.cast_pos, Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨i, hi, hcond⟩
    rw [Finset.mem_Ico] at hi
    exact ⟨i, hi.1, by omega⟩
  · rintro ⟨i, hi1, hcond⟩
    have hmod : N % 3 ^ i ≤ N := Nat.mod_le _ _
    have hilt : i < 2 * N + 1 := by
      have : i < 3 ^ i := Nat.lt_pow_self (by norm_num)
      have : 3 ^ i ≤ 2 * N := le_trans hcond (by omega)
      omega
    exact ⟨i, by rw [Finset.mem_Ico]; exact ⟨hi1, hilt⟩, by omega⟩

/-- The "carry" condition holds iff `N` has a base-3 digit equal to `2`. -/
private lemma carry_iff_digit (N : ℕ) :
    (∃ i, 1 ≤ i ∧ 3 ^ i ≤ 2 * (N % 3 ^ i)) ↔ ∃ j, N / 3 ^ j % 3 = 2 := by
  constructor
  · rintro ⟨i, hi1, hcond⟩
    by_contra hcon
    push_neg at hcon
    have key : ∀ m, 2 * (N % 3 ^ m) < 3 ^ m := by
      intro m
      induction m with
      | zero => simp [Nat.mod_one]
      | succ m ih =>
        have hdec : N % 3 ^ (m + 1) = N % 3 ^ m + 3 ^ m * (N / 3 ^ m % 3) := by
          rw [show (3:ℕ) ^ (m + 1) = 3 ^ m * 3 by rw [pow_succ]]; exact Nat.mod_mul
        have hlt3 : N / 3 ^ m % 3 < 3 := Nat.mod_lt _ (by norm_num)
        have hd : N / 3 ^ m % 3 ≤ 1 := by have := hcon m; omega
        have hbd : 3 ^ m * (N / 3 ^ m % 3) ≤ 3 ^ m := by
          calc 3 ^ m * (N / 3 ^ m % 3) ≤ 3 ^ m * 1 := Nat.mul_le_mul (le_refl _) hd
            _ = 3 ^ m := mul_one _
        have h3 : (3:ℕ) ^ (m + 1) = 3 * 3 ^ m := by rw [pow_succ]; ring
        rw [hdec]; omega
    have := key i; omega
  · rintro ⟨j, hj⟩
    refine ⟨j + 1, by omega, ?_⟩
    have hdec : N % 3 ^ (j + 1) = N % 3 ^ j + 3 ^ j * (N / 3 ^ j % 3) := by
      rw [show (3:ℕ) ^ (j + 1) = 3 ^ j * 3 by rw [pow_succ]]; exact Nat.mod_mul
    rw [hdec, hj]
    have h3 : (3:ℕ) ^ (j + 1) = 3 * 3 ^ j := by rw [pow_succ]; ring
    omega

/-- **The open core, made explicit and machine-verified-equivalent.**
`3 ∣ catalan(2^k-1)` holds iff `2^k - 1` has a base-3 digit equal to `2`. -/
theorem three_dvd_catalan_pow_iff (k : ℕ) (hk : 1 ≤ k) :
    3 ∣ catalan (2 ^ k - 1) ↔ ∃ j, (2 ^ k - 1) / 3 ^ j % 3 = 2 := by
  have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hN : 1 ≤ 2 ^ k - 1 := by
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hmul : 2 ^ k * catalan (2 ^ k - 1) = centralBinom (2 ^ k - 1) := by
    have h := succ_mul_catalan_eq_centralBinom (2 ^ k - 1)
    rwa [show 2 ^ k - 1 + 1 = 2 ^ k by omega] at h
  have hcop : Nat.Coprime 3 (2 ^ k) := (show Nat.Coprime 3 2 by decide).pow_right k
  have step1 : 3 ∣ catalan (2 ^ k - 1) ↔ 3 ∣ centralBinom (2 ^ k - 1) := by
    constructor
    · intro h; rw [← hmul]; exact Dvd.dvd.mul_left h _
    · intro h; rw [← hmul] at h; exact hcop.dvd_of_dvd_mul_left h
  rw [step1, three_dvd_centralBinom_iff (2 ^ k - 1) hN, carry_iff_digit]

set_option maxRecDepth 100000 in
theorem oeis_259667_conjecture_0 :
    (∀ k : ℕ, A259667 (2^k - 1) = 1 ↔ k = 0 ∨ k = 1 ∨ k = 5) ∧
    (∀ k : ℕ, A259667 (2^k - 1) = 5 ↔ k = 2 ∨ k = 8) ∧
    (∀ k : ℕ, k > 8 → A259667 (2^k - 1) = 3) := by
  refine oeis_259667_reduction (fun k => C_pow_two_sub_one_mod_two k) ?_
  -- It remains to supply `h3` (the mod-3 residues).  The finite cases `k ≤ 8` are
  -- discharged by direct kernel computation; only the `k > 8` case is open.
  intro k
  rcases Nat.lt_or_ge k 9 with hle | hgt
  · interval_cases k <;> decide
  · rw [if_neg (by omega), if_neg (by omega)]
    have hexpr : (2 * (2 ^ k - 1)).choose (2 ^ k - 1) / (2 ^ k - 1 + 1)
        = catalan (2 ^ k - 1) := by
      rw [← centralBinom_eq_two_mul_choose, ← catalan_eq_centralBinom_div]
    rw [hexpr, ← Nat.dvd_iff_mod_eq_zero, three_dvd_catalan_pow_iff k (by omega)]
    -- The goal is now the EXPLICIT, machine-verified-equivalent open statement:
    --   `∃ j, (2 ^ k - 1) / 3 ^ j % 3 = 2`,  i.e. "`2^k - 1` has a base-3 digit `2`".
    -- For even `k > 8` this is *exactly* Erdős's (1979) ternary-expansion conjecture, which
    -- is open.  This single statement — and nothing else — is the open core of the problem.
    sorry
