import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000
set_option linter.unusedTactic false

open Nat BigOperators

/--
A303639: Number of ways to write $n$ as $a^2 + b^2 + \binom{2c+1}{c} + \binom{2d+1}{d},
where $a,b,c,d$ are nonnegative integers with $a \le b$ and $c \le d$.
-/
def a (n : ℕ) : ℕ :=
  let B (k : ℕ) : ℕ := (2 * k + 1).choose k
  let R_sq := Finset.range (n.sqrt + 1)
  let R_binom := Finset.range (n + 1)
  R_sq.sum fun a =>
    R_sq.sum fun b =>
      R_binom.sum fun c =>
        R_binom.sum fun d =>
          if a ≤ b ∧ c ≤ d ∧ a ^ 2 + b ^ 2 + B c + B d = n then 1 else 0

lemma B_mono (k : ℕ) : (2 * k + 1).choose k ≤ (2 * (k + 1) + 1).choose (k + 1) := by
  have h1 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  rw [h1]
  have h2 : (2 * k + 3).choose (k + 1) = (2 * k + 2).choose k + (2 * k + 2).choose (k + 1) := by
    rw [show 2 * k + 3 = succ (2 * k + 2) by omega, show k + 1 = succ k by omega, choose_succ_succ]
  have h3 : (2 * k + 2).choose (k + 1) = (2 * k + 1).choose k + (2 * k + 1).choose (k + 1) := by
    rw [show 2 * k + 2 = succ (2 * k + 1) by omega, show k + 1 = succ k by omega, choose_succ_succ]
  rw [h2, h3]
  omega

lemma B_mono_of_le {a b : ℕ} (h : a ≤ b) : (2 * a + 1).choose a ≤ (2 * b + 1).choose b := by
  induction h with
  | refl => rfl
  | step h_le ih =>
    exact ih.trans (B_mono _)

lemma d_lt_16 (a b c d : ℕ) (heq : a ^ 2 + b ^ 2 + (2 * c + 1).choose c + (2 * d + 1).choose d = 800322180) : d < 16 := by
  by_contra! hd
  have h_b16 : (2 * 16 + 1).choose 16 ≤ (2 * d + 1).choose d := B_mono_of_le hd
  have h_le : (2 * d + 1).choose d ≤ 800322180 := by omega
  have h_trans : (2 * 16 + 1).choose 16 ≤ 800322180 := h_b16.trans h_le
  revert h_trans
  decide

lemma padicValNat_eq_val_of_pow_dvd_of_not_pow_dvd {n p m : ℕ} [hp : Fact p.Prime] (hn : n ≠ 0) (hdiv : p ^ m ∣ n) (hndiv : ¬ p ^ (m + 1) ∣ n) :
    padicValNat p n = m := by
  have h1 : m ≤ padicValNat p n := by
    rwa [← padicValNat_dvd_iff_le hn]
  have h2 : padicValNat p n < m + 1 := by
    by_contra! h
    have h_pow : p ^ (m + 1) ∣ n := (padicValNat_dvd_iff_le hn).mpr h
    exact hndiv h_pow
  omega

lemma not_sq_add_sq_prime_general (rem p m : ℕ) [hp : Fact p.Prime] (hp4 : p % 4 = 3) (hn0 : rem ≠ 0)
    (hdiv : p ^ m ∣ rem) (hndiv : ¬ p ^ (m + 1) ∣ rem) (hm_odd : ¬ Even m) : ¬ ∃ x y, rem = x ^ 2 + y ^ 2 := by
  rw [Nat.eq_sq_add_sq_iff]
  push_neg
  refine ⟨p, ?_, hp4, ?_⟩
  · rw [Nat.mem_primeFactors]
    refine ⟨hp.out, ?_, hn0⟩
    have : 1 ≤ m := by
      cases m with
      | zero => exact (hm_odd (by decide)).elim
      | succ => omega
    have h_pow_dvd : p ^ 1 ∣ rem := (pow_dvd_pow p this).trans hdiv
    rwa [pow_one] at h_pow_dvd
  · have h_val : padicValNat p rem = m := padicValNat_eq_val_of_pow_dvd_of_not_pow_dvd hn0 hdiv hndiv
    rw [h_val]
    exact hm_odd

lemma not_sq_add_sq_mod_general (M : ℕ) [NeZero M] (rem x y : ℕ) (heq : x ^ 2 + y ^ 2 = rem) (r : ℕ) (h_mod : rem % M = r)
    (h_obs : ∀ (x_zmod y_zmod : ZMod M), x_zmod ^ 2 + y_zmod ^ 2 ≠ (r : ZMod M)) : False := by
  have h_zmod : ((x ^ 2 + y ^ 2 : ℕ) : ZMod M) = ((rem : ℕ) : ZMod M) := by rw [heq]
  push_cast at h_zmod
  have h_rem : (rem : ZMod M) = (r : ZMod M) := by
    rw [← ZMod.natCast_mod rem M]
    rw [h_mod]
  rw [h_rem] at h_zmod
  generalize (x : ZMod M) = x_zmod at h_zmod
  generalize (y : ZMod M) = y_zmod at h_zmod
  exact h_obs x_zmod y_zmod h_zmod

theorem a_eq_zero_of_no_sol :
    ∀ (a b c d : ℕ), a ≤ b → c ≤ d → a ^ 2 + b ^ 2 + (2 * c + 1).choose c + (2 * d + 1).choose d ≠ 800322180 := by
  intro a b c d hab hcd heq
  have hd16 : d < 16 := d_lt_16 a b c d heq
  have hc16 : c < 16 := by omega
  interval_cases c <;> interval_cases d <;> (try omega)
  · -- Case c = 0, d = 0
    change a ^ 2 + b ^ 2 + 1 + 1 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800322178 := by omega
    have : Fact (Nat.Prime 647) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800322178 647 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 0, d = 1
    change a ^ 2 + b ^ 2 + 1 + 3 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800322176 := by omega
    have : Fact (Nat.Prime 163) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800322176 163 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 0, d = 2
    change a ^ 2 + b ^ 2 + 1 + 10 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800322169 := by omega
    have : Fact (Nat.Prime 67) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800322169 67 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 0, d = 3
    change a ^ 2 + b ^ 2 + 1 + 35 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800322144 := by omega
    exact not_sq_add_sq_mod_general 9 800322144 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 0, d = 4
    change a ^ 2 + b ^ 2 + 1 + 126 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800322053 := by omega
    have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800322053 23 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 0, d = 5
    change a ^ 2 + b ^ 2 + 1 + 462 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800321717 := by omega
    have : Fact (Nat.Prime 467) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800321717 467 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 0, d = 6
    change a ^ 2 + b ^ 2 + 1 + 1716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800320463 := by omega
    exact not_sq_add_sq_mod_general 4 800320463 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 0, d = 7
    change a ^ 2 + b ^ 2 + 1 + 6435 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800315744 := by omega
    have : Fact (Nat.Prime 991) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800315744 991 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 0, d = 8
    change a ^ 2 + b ^ 2 + 1 + 24310 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800297869 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800297869 7 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 0, d = 9
    change a ^ 2 + b ^ 2 + 1 + 92378 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800229801 := by omega
    exact not_sq_add_sq_mod_general 9 800229801 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 0, d = 10
    change a ^ 2 + b ^ 2 + 1 + 352716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 799969463 := by omega
    exact not_sq_add_sq_mod_general 4 799969463 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 0, d = 11
    change a ^ 2 + b ^ 2 + 1 + 1352078 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 798970101 := by omega
    exact not_sq_add_sq_mod_general 9 798970101 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 0, d = 12
    change a ^ 2 + b ^ 2 + 1 + 5200300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 795121879 := by omega
    exact not_sq_add_sq_mod_general 4 795121879 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 0, d = 13
    change a ^ 2 + b ^ 2 + 1 + 20058300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 780263879 := by omega
    exact not_sq_add_sq_mod_general 4 780263879 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 0, d = 14
    change a ^ 2 + b ^ 2 + 1 + 77558760 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 722763419 := by omega
    exact not_sq_add_sq_mod_general 4 722763419 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 0, d = 15
    change a ^ 2 + b ^ 2 + 1 + 300540195 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 499781984 := by omega
    have : Fact (Nat.Prime 1999) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 499781984 1999 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 1, d = 1
    change a ^ 2 + b ^ 2 + 3 + 3 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800322174 := by omega
    exact not_sq_add_sq_mod_general 8 800322174 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 1, d = 2
    change a ^ 2 + b ^ 2 + 3 + 10 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800322167 := by omega
    exact not_sq_add_sq_mod_general 4 800322167 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 1, d = 3
    change a ^ 2 + b ^ 2 + 3 + 35 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800322142 := by omega
    exact not_sq_add_sq_mod_general 8 800322142 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 1, d = 4
    change a ^ 2 + b ^ 2 + 3 + 126 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800322051 := by omega
    exact not_sq_add_sq_mod_general 4 800322051 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 1, d = 5
    change a ^ 2 + b ^ 2 + 3 + 462 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800321715 := by omega
    exact not_sq_add_sq_mod_general 4 800321715 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 1, d = 6
    change a ^ 2 + b ^ 2 + 3 + 1716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800320461 := by omega
    exact not_sq_add_sq_mod_general 9 800320461 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 1, d = 7
    change a ^ 2 + b ^ 2 + 3 + 6435 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800315742 := by omega
    exact not_sq_add_sq_mod_general 8 800315742 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 1, d = 8
    change a ^ 2 + b ^ 2 + 3 + 24310 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800297867 := by omega
    exact not_sq_add_sq_mod_general 4 800297867 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 1, d = 9
    change a ^ 2 + b ^ 2 + 3 + 92378 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800229799 := by omega
    exact not_sq_add_sq_mod_general 4 800229799 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 1, d = 10
    change a ^ 2 + b ^ 2 + 3 + 352716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 799969461 := by omega
    exact not_sq_add_sq_mod_general 9 799969461 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 1, d = 11
    change a ^ 2 + b ^ 2 + 3 + 1352078 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 798970099 := by omega
    exact not_sq_add_sq_mod_general 4 798970099 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 1, d = 12
    change a ^ 2 + b ^ 2 + 3 + 5200300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 795121877 := by omega
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 795121877 11 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 1, d = 13
    change a ^ 2 + b ^ 2 + 3 + 20058300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 780263877 := by omega
    exact not_sq_add_sq_mod_general 9 780263877 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 1, d = 14
    change a ^ 2 + b ^ 2 + 3 + 77558760 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 722763417 := by omega
    exact not_sq_add_sq_mod_general 9 722763417 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 1, d = 15
    change a ^ 2 + b ^ 2 + 3 + 300540195 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 499781982 := by omega
    exact not_sq_add_sq_mod_general 8 499781982 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 2, d = 2
    change a ^ 2 + b ^ 2 + 10 + 10 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800322160 := by omega
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800322160 11 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 2, d = 3
    change a ^ 2 + b ^ 2 + 10 + 35 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800322135 := by omega
    exact not_sq_add_sq_mod_general 4 800322135 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 2, d = 4
    change a ^ 2 + b ^ 2 + 10 + 126 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800322044 := by omega
    exact not_sq_add_sq_mod_general 16 800322044 a b h_sum 12 (by decide) (by decide)
  · -- Case c = 2, d = 5
    change a ^ 2 + b ^ 2 + 10 + 462 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800321708 := by omega
    exact not_sq_add_sq_mod_general 16 800321708 a b h_sum 12 (by decide) (by decide)
  · -- Case c = 2, d = 6
    change a ^ 2 + b ^ 2 + 10 + 1716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800320454 := by omega
    exact not_sq_add_sq_mod_general 8 800320454 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 2, d = 7
    change a ^ 2 + b ^ 2 + 10 + 6435 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800315735 := by omega
    exact not_sq_add_sq_mod_general 4 800315735 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 2, d = 8
    change a ^ 2 + b ^ 2 + 10 + 24310 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800297860 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800297860 19 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 2, d = 9
    change a ^ 2 + b ^ 2 + 10 + 92378 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800229792 := by omega
    exact not_sq_add_sq_mod_general 9 800229792 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 2, d = 10
    change a ^ 2 + b ^ 2 + 10 + 352716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 799969454 := by omega
    exact not_sq_add_sq_mod_general 8 799969454 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 2, d = 11
    change a ^ 2 + b ^ 2 + 10 + 1352078 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 798970092 := by omega
    exact not_sq_add_sq_mod_general 9 798970092 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 2, d = 12
    change a ^ 2 + b ^ 2 + 10 + 5200300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 795121870 := by omega
    exact not_sq_add_sq_mod_general 8 795121870 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 2, d = 13
    change a ^ 2 + b ^ 2 + 10 + 20058300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 780263870 := by omega
    exact not_sq_add_sq_mod_general 8 780263870 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 2, d = 14
    change a ^ 2 + b ^ 2 + 10 + 77558760 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 722763410 := by omega
    have : Fact (Nat.Prime 2819) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 722763410 2819 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 2, d = 15
    change a ^ 2 + b ^ 2 + 10 + 300540195 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 499781975 := by omega
    exact not_sq_add_sq_mod_general 4 499781975 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 3, d = 3
    change a ^ 2 + b ^ 2 + 35 + 35 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800322110 := by omega
    exact not_sq_add_sq_mod_general 8 800322110 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 3, d = 4
    change a ^ 2 + b ^ 2 + 35 + 126 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800322019 := by omega
    exact not_sq_add_sq_mod_general 4 800322019 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 3, d = 5
    change a ^ 2 + b ^ 2 + 35 + 462 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800321683 := by omega
    exact not_sq_add_sq_mod_general 4 800321683 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 3, d = 6
    change a ^ 2 + b ^ 2 + 35 + 1716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800320429 := by omega
    have : Fact (Nat.Prime 43) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800320429 43 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 3, d = 7
    change a ^ 2 + b ^ 2 + 35 + 6435 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800315710 := by omega
    exact not_sq_add_sq_mod_general 8 800315710 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 3, d = 8
    change a ^ 2 + b ^ 2 + 35 + 24310 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800297835 := by omega
    exact not_sq_add_sq_mod_general 4 800297835 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 3, d = 9
    change a ^ 2 + b ^ 2 + 35 + 92378 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800229767 := by omega
    exact not_sq_add_sq_mod_general 4 800229767 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 3, d = 10
    change a ^ 2 + b ^ 2 + 35 + 352716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 799969429 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 799969429 7 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 3, d = 11
    change a ^ 2 + b ^ 2 + 35 + 1352078 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 798970067 := by omega
    exact not_sq_add_sq_mod_general 4 798970067 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 3, d = 12
    change a ^ 2 + b ^ 2 + 35 + 5200300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 795121845 := by omega
    exact not_sq_add_sq_mod_general 9 795121845 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 3, d = 13
    change a ^ 2 + b ^ 2 + 35 + 20058300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 780263845 := by omega
    have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 780263845 23 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 3, d = 14
    change a ^ 2 + b ^ 2 + 35 + 77558760 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 722763385 := by omega
    have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 722763385 23 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 3, d = 15
    change a ^ 2 + b ^ 2 + 35 + 300540195 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 499781950 := by omega
    exact not_sq_add_sq_mod_general 8 499781950 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 4, d = 4
    change a ^ 2 + b ^ 2 + 126 + 126 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800321928 := by omega
    exact not_sq_add_sq_mod_general 9 800321928 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 4, d = 5
    change a ^ 2 + b ^ 2 + 126 + 462 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800321592 := by omega
    exact not_sq_add_sq_mod_general 9 800321592 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 4, d = 6
    change a ^ 2 + b ^ 2 + 126 + 1716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800320338 := by omega
    have : Fact (Nat.Prime 719) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800320338 719 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 4, d = 7
    change a ^ 2 + b ^ 2 + 126 + 6435 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800315619 := by omega
    exact not_sq_add_sq_mod_general 4 800315619 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 4, d = 8
    change a ^ 2 + b ^ 2 + 126 + 24310 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800297744 := by omega
    have : Fact (Nat.Prime 563) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800297744 563 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 4, d = 9
    change a ^ 2 + b ^ 2 + 126 + 92378 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800229676 := by omega
    exact not_sq_add_sq_mod_general 16 800229676 a b h_sum 12 (by decide) (by decide)
  · -- Case c = 4, d = 10
    change a ^ 2 + b ^ 2 + 126 + 352716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 799969338 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 799969338 3 3 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 4, d = 11
    change a ^ 2 + b ^ 2 + 126 + 1352078 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 798969976 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 798969976 7 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 4, d = 12
    change a ^ 2 + b ^ 2 + 126 + 5200300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 795121754 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 795121754 7 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 4, d = 13
    change a ^ 2 + b ^ 2 + 126 + 20058300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 780263754 := by omega
    exact not_sq_add_sq_mod_general 9 780263754 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 4, d = 14
    change a ^ 2 + b ^ 2 + 126 + 77558760 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 722763294 := by omega
    exact not_sq_add_sq_mod_general 8 722763294 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 4, d = 15
    change a ^ 2 + b ^ 2 + 126 + 300540195 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 499781859 := by omega
    exact not_sq_add_sq_mod_general 4 499781859 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 5, d = 5
    change a ^ 2 + b ^ 2 + 462 + 462 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800321256 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800321256 3 3 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 5, d = 6
    change a ^ 2 + b ^ 2 + 462 + 1716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800320002 := by omega
    exact not_sq_add_sq_mod_general 9 800320002 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 5, d = 7
    change a ^ 2 + b ^ 2 + 462 + 6435 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800315283 := by omega
    exact not_sq_add_sq_mod_general 4 800315283 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 5, d = 8
    change a ^ 2 + b ^ 2 + 462 + 24310 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800297408 := by omega
    have : Fact (Nat.Prime 12504647) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800297408 12504647 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 5, d = 9
    change a ^ 2 + b ^ 2 + 462 + 92378 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800229340 := by omega
    exact not_sq_add_sq_mod_general 16 800229340 a b h_sum 12 (by decide) (by decide)
  · -- Case c = 5, d = 10
    change a ^ 2 + b ^ 2 + 462 + 352716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 799969002 := by omega
    exact not_sq_add_sq_mod_general 9 799969002 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 5, d = 11
    change a ^ 2 + b ^ 2 + 462 + 1352078 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 798969640 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 798969640 7 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 5, d = 12
    change a ^ 2 + b ^ 2 + 462 + 5200300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 795121418 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 795121418 7 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 5, d = 13
    change a ^ 2 + b ^ 2 + 462 + 20058300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 780263418 := by omega
    exact not_sq_add_sq_mod_general 9 780263418 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 5, d = 14
    change a ^ 2 + b ^ 2 + 462 + 77558760 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 722762958 := by omega
    exact not_sq_add_sq_mod_general 8 722762958 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 5, d = 15
    change a ^ 2 + b ^ 2 + 462 + 300540195 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 499781523 := by omega
    exact not_sq_add_sq_mod_general 4 499781523 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 6, d = 6
    change a ^ 2 + b ^ 2 + 1716 + 1716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800318748 := by omega
    exact not_sq_add_sq_mod_general 9 800318748 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 6, d = 7
    change a ^ 2 + b ^ 2 + 1716 + 6435 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800314029 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800314029 19 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 6, d = 8
    change a ^ 2 + b ^ 2 + 1716 + 24310 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800296154 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800296154 7 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 6, d = 9
    change a ^ 2 + b ^ 2 + 1716 + 92378 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800228086 := by omega
    exact not_sq_add_sq_mod_general 8 800228086 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 6, d = 10
    change a ^ 2 + b ^ 2 + 1716 + 352716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 799967748 := by omega
    exact not_sq_add_sq_mod_general 9 799967748 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 6, d = 11
    change a ^ 2 + b ^ 2 + 1716 + 1352078 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 798968386 := by omega
    have : Fact (Nat.Prime 139) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 798968386 139 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 6, d = 12
    change a ^ 2 + b ^ 2 + 1716 + 5200300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 795120164 := by omega
    have : Fact (Nat.Prime 227) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 795120164 227 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 6, d = 13
    change a ^ 2 + b ^ 2 + 1716 + 20058300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 780262164 := by omega
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 780262164 11 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 6, d = 14
    change a ^ 2 + b ^ 2 + 1716 + 77558760 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 722761704 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 722761704 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 6, d = 15
    change a ^ 2 + b ^ 2 + 1716 + 300540195 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 499780269 := by omega
    have : Fact (Nat.Prime 67) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 499780269 67 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 7, d = 7
    change a ^ 2 + b ^ 2 + 6435 + 6435 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800309310 := by omega
    exact not_sq_add_sq_mod_general 8 800309310 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 7, d = 8
    change a ^ 2 + b ^ 2 + 6435 + 24310 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800291435 := by omega
    exact not_sq_add_sq_mod_general 4 800291435 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 7, d = 9
    change a ^ 2 + b ^ 2 + 6435 + 92378 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800223367 := by omega
    exact not_sq_add_sq_mod_general 4 800223367 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 7, d = 10
    change a ^ 2 + b ^ 2 + 6435 + 352716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 799963029 := by omega
    have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 799963029 31 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 7, d = 11
    change a ^ 2 + b ^ 2 + 6435 + 1352078 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 798963667 := by omega
    exact not_sq_add_sq_mod_general 4 798963667 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 7, d = 12
    change a ^ 2 + b ^ 2 + 6435 + 5200300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 795115445 := by omega
    have : Fact (Nat.Prime 139) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 795115445 139 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 7, d = 13
    change a ^ 2 + b ^ 2 + 6435 + 20058300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 780257445 := by omega
    exact not_sq_add_sq_mod_general 9 780257445 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 7, d = 14
    change a ^ 2 + b ^ 2 + 6435 + 77558760 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 722756985 := by omega
    exact not_sq_add_sq_mod_general 9 722756985 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 7, d = 15
    change a ^ 2 + b ^ 2 + 6435 + 300540195 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 499775550 := by omega
    exact not_sq_add_sq_mod_general 8 499775550 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 8, d = 8
    change a ^ 2 + b ^ 2 + 24310 + 24310 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800273560 := by omega
    have : Fact (Nat.Prime 689891) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800273560 689891 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 8, d = 9
    change a ^ 2 + b ^ 2 + 24310 + 92378 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800205492 := by omega
    exact not_sq_add_sq_mod_general 9 800205492 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 8, d = 10
    change a ^ 2 + b ^ 2 + 24310 + 352716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 799945154 := by omega
    have : Fact (Nat.Prime 223) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 799945154 223 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 8, d = 11
    change a ^ 2 + b ^ 2 + 24310 + 1352078 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 798945792 := by omega
    exact not_sq_add_sq_mod_general 9 798945792 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 8, d = 12
    change a ^ 2 + b ^ 2 + 24310 + 5200300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 795097570 := by omega
    have : Fact (Nat.Prime 59) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 795097570 59 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 8, d = 13
    change a ^ 2 + b ^ 2 + 24310 + 20058300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 780239570 := by omega
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 780239570 11 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 8, d = 14
    change a ^ 2 + b ^ 2 + 24310 + 77558760 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 722739110 := by omega
    exact not_sq_add_sq_mod_general 8 722739110 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 8, d = 15
    change a ^ 2 + b ^ 2 + 24310 + 300540195 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 499757675 := by omega
    exact not_sq_add_sq_mod_general 4 499757675 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 9, d = 9
    change a ^ 2 + b ^ 2 + 92378 + 92378 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 800137424 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 800137424 19 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 9, d = 10
    change a ^ 2 + b ^ 2 + 92378 + 352716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 799877086 := by omega
    exact not_sq_add_sq_mod_general 8 799877086 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 9, d = 11
    change a ^ 2 + b ^ 2 + 92378 + 1352078 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 798877724 := by omega
    exact not_sq_add_sq_mod_general 16 798877724 a b h_sum 12 (by decide) (by decide)
  · -- Case c = 9, d = 12
    change a ^ 2 + b ^ 2 + 92378 + 5200300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 795029502 := by omega
    exact not_sq_add_sq_mod_general 8 795029502 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 9, d = 13
    change a ^ 2 + b ^ 2 + 92378 + 20058300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 780171502 := by omega
    exact not_sq_add_sq_mod_general 8 780171502 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 9, d = 14
    change a ^ 2 + b ^ 2 + 92378 + 77558760 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 722671042 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 722671042 19 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 9, d = 15
    change a ^ 2 + b ^ 2 + 92378 + 300540195 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 499689607 := by omega
    exact not_sq_add_sq_mod_general 4 499689607 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 10, d = 10
    change a ^ 2 + b ^ 2 + 352716 + 352716 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 799616748 := by omega
    exact not_sq_add_sq_mod_general 9 799616748 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 10, d = 11
    change a ^ 2 + b ^ 2 + 352716 + 1352078 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 798617386 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 798617386 19 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 10, d = 12
    change a ^ 2 + b ^ 2 + 352716 + 5200300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 794769164 := by omega
    exact not_sq_add_sq_mod_general 16 794769164 a b h_sum 12 (by decide) (by decide)
  · -- Case c = 10, d = 13
    change a ^ 2 + b ^ 2 + 352716 + 20058300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 779911164 := by omega
    exact not_sq_add_sq_mod_general 16 779911164 a b h_sum 12 (by decide) (by decide)
  · -- Case c = 10, d = 14
    change a ^ 2 + b ^ 2 + 352716 + 77558760 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 722410704 := by omega
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 722410704 3 3 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 10, d = 15
    change a ^ 2 + b ^ 2 + 352716 + 300540195 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 499429269 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 499429269 19 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 11, d = 11
    change a ^ 2 + b ^ 2 + 1352078 + 1352078 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 797618024 := by omega
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 797618024 7 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 11, d = 12
    change a ^ 2 + b ^ 2 + 1352078 + 5200300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 793769802 := by omega
    exact not_sq_add_sq_mod_general 9 793769802 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 11, d = 13
    change a ^ 2 + b ^ 2 + 1352078 + 20058300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 778911802 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 778911802 19 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 11, d = 14
    change a ^ 2 + b ^ 2 + 1352078 + 77558760 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 721411342 := by omega
    exact not_sq_add_sq_mod_general 8 721411342 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 11, d = 15
    change a ^ 2 + b ^ 2 + 1352078 + 300540195 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 498429907 := by omega
    exact not_sq_add_sq_mod_general 4 498429907 a b h_sum 3 (by decide) (by decide)
  · -- Case c = 12, d = 12
    change a ^ 2 + b ^ 2 + 5200300 + 5200300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 789921580 := by omega
    exact not_sq_add_sq_mod_general 16 789921580 a b h_sum 12 (by decide) (by decide)
  · -- Case c = 12, d = 13
    change a ^ 2 + b ^ 2 + 5200300 + 20058300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 775063580 := by omega
    exact not_sq_add_sq_mod_general 16 775063580 a b h_sum 12 (by decide) (by decide)
  · -- Case c = 12, d = 14
    change a ^ 2 + b ^ 2 + 5200300 + 77558760 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 717563120 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 717563120 19 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 12, d = 15
    change a ^ 2 + b ^ 2 + 5200300 + 300540195 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 494581685 := by omega
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact not_sq_add_sq_prime_general 494581685 19 1 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨a, b, h_sum.symm⟩
  · -- Case c = 13, d = 13
    change a ^ 2 + b ^ 2 + 20058300 + 20058300 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 760205580 := by omega
    exact not_sq_add_sq_mod_general 9 760205580 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 13, d = 14
    change a ^ 2 + b ^ 2 + 20058300 + 77558760 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 702705120 := by omega
    exact not_sq_add_sq_mod_general 9 702705120 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 13, d = 15
    change a ^ 2 + b ^ 2 + 20058300 + 300540195 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 479723685 := by omega
    exact not_sq_add_sq_mod_general 9 479723685 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 14, d = 14
    change a ^ 2 + b ^ 2 + 77558760 + 77558760 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 645204660 := by omega
    exact not_sq_add_sq_mod_general 9 645204660 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 14, d = 15
    change a ^ 2 + b ^ 2 + 77558760 + 300540195 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 422223225 := by omega
    exact not_sq_add_sq_mod_general 9 422223225 a b h_sum 6 (by decide) (by decide)
  · -- Case c = 15, d = 15
    change a ^ 2 + b ^ 2 + 300540195 + 300540195 = 800322180 at heq
    have h_sum : a ^ 2 + b ^ 2 = 199241790 := by omega
    exact not_sq_add_sq_mod_general 8 199241790 a b h_sum 6 (by decide) (by decide)

theorem oeis_303639_conjecture_0.disproof : ¬ (∀ (n : ℕ), n > 1 → a n > 0) := by
  intro h
  have h_val := h 800322180 (by decide)
  have h_zero : a 800322180 = 0 := by
    dsimp [a]
    have h_zero_term (a b c d : ℕ) :
        (if a ≤ b ∧ c ≤ d ∧ a ^ 2 + b ^ 2 + (2 * c + 1).choose c + (2 * d + 1).choose d = 800322180 then 1 else 0) = 0 := by
      split_ifs with h_cond
      · obtain ⟨hab, hcd, heq⟩ := h_cond
        exact (a_eq_zero_of_no_sol a b c d hab hcd heq).elim
      · rfl
    have h_sum1 (a b c : ℕ) : ∑ d ∈ Finset.range (800322180 + 1), (if a ≤ b ∧ c ≤ d ∧ a ^ 2 + b ^ 2 + (2 * c + 1).choose c + (2 * d + 1).choose d = 800322180 then 1 else 0) = 0 := by
      simp_rw [h_zero_term, Finset.sum_const_zero]
    have h_sum2 (a b : ℕ) : ∑ c ∈ Finset.range (800322180 + 1), ∑ d ∈ Finset.range (800322180 + 1), (if a ≤ b ∧ c ≤ d ∧ a ^ 2 + b ^ 2 + (2 * c + 1).choose c + (2 * d + 1).choose d = 800322180 then 1 else 0) = 0 := by
      simp_rw [h_sum1, Finset.sum_const_zero]
    have h_sum3 (a : ℕ) : ∑ b ∈ Finset.range (Nat.sqrt 800322180 + 1), ∑ c ∈ Finset.range (800322180 + 1), ∑ d ∈ Finset.range (800322180 + 1), (if a ≤ b ∧ c ≤ d ∧ a ^ 2 + b ^ 2 + (2 * c + 1).choose c + (2 * d + 1).choose d = 800322180 then 1 else 0) = 0 := by
      simp_rw [h_zero_term, Finset.sum_const_zero]
    simp_rw [h_sum3, Finset.sum_const_zero]
  omega
