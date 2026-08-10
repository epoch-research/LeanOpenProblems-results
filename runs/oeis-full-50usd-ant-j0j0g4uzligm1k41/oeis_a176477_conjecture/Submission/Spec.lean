import FormalConjectures.Util.ProblemImports

open Nat

/-- Helper function for the recurrence relation, defined over $\mathbb{Q}$. -/
noncomputable def a_Q (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 => -- Index $n = k+2$, $n \ge 2$
    let n_idx := k + 2
    let n_q : ℚ := n_idx
    -- The subtraction n_idx - 1 is safe since n_idx ≥ 2
    let a_prev : ℚ := a_Q (n_idx - 1)

    -- Numerator Term 1: $32n^3 a(n-1)$
    let term1 : ℚ := 32 * n_q ^ 3 * a_prev

    -- Polynomial coefficient Term 2
    let P_n : ℚ := 21 * n_q ^ 3 + 22 * n_q ^ 2 + 8 * n_q + 1

    -- Binomial Term 2: $\binom{2n-1}{n}^4$. Subtraction is safe since $2n-1 \ge 3$
    let binom_pow4 : ℚ := (Nat.choose (2 * n_idx - 1) n_idx : ℚ) ^ 4

    let numerator : ℚ := term1 + P_n * binom_pow4
    let denominator : ℚ := (2 * n_q + 1) ^ 3

    numerator / denominator

/-- The recurrence unfolded for n ≥ 2. -/
theorem a_Q_succ_succ (k : ℕ) :
    a_Q (k + 2) =
      (32 * ((k:ℚ)+2) ^ 3 * a_Q (k+1)
        + (21 * ((k:ℚ)+2) ^ 3 + 22 * ((k:ℚ)+2) ^ 2 + 8 * ((k:ℚ)+2) + 1)
          * (Nat.choose (2 * (k+2) - 1) (k+2) : ℚ) ^ 4)
      / (2 * ((k:ℚ)+2) + 1) ^ 3 := by
  conv_lhs => rw [a_Q]
  norm_num

/-- Polynomial `P_n = 21 n^3 + 22 n^2 + 8 n + 1`. -/
def Pnat (n : ℕ) : ℕ := 21 * n^3 + 22 * n^2 + 8 * n + 1

/-- The central-ish binomial `B_n = C(2n-1, n)`. -/
def Bnat (n : ℕ) : ℕ := Nat.choose (2 * n - 1) n

/-- KEY LEMMA (Zhi-Wei Sun's integrality conjecture, A176477): the divisibility that
makes the recurrence produce integers. Here `m'` is constrained to be the value `a(k+1)`.
This is the crux supercongruence:
`(2n+1)^3 ∣ 32 n^3 a(n-1) + P_n B_n^4`. -/
theorem key_dvd (k : ℕ) (m' : ℤ) (hm' : a_Q (k + 1) = (m' : ℚ)) :
    ((2 * (k:ℤ) + 5) ^ 3) ∣
      (32 * ((k:ℤ) + 2) ^ 3 * m'
        + (21 * ((k:ℤ) + 2) ^ 3 + 22 * ((k:ℤ) + 2) ^ 2 + 8 * ((k:ℤ) + 2) + 1)
          * (Bnat (k + 2) : ℤ) ^ 4) := by
  sorry

/-- Positivity of `a_Q` (does not need integrality). -/
theorem a_Q_pos (n : ℕ) : 0 ≤ a_Q n ∧ (1 ≤ n → 0 < a_Q n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact ⟨by rw [a_Q], by intro h; omega⟩
    | 1 => refine ⟨by rw [a_Q]; norm_num, fun _ => by rw [a_Q]; norm_num⟩
    | (k + 2) =>
      have hprev : 0 ≤ a_Q (k+1) := (ih (k+1) (by omega)).1
      have hBpos : 0 < Nat.choose (2 * (k+2) - 1) (k+2) := Nat.choose_pos (by omega)
      have hval : 0 < a_Q (k+2) := by
        rw [a_Q_succ_succ]
        apply _root_.div_pos
        · have h1 : 0 ≤ 32 * ((k:ℚ)+2)^3 * a_Q (k+1) := mul_nonneg (by positivity) hprev
          have h2 : 0 < (21 * ((k:ℚ)+2)^3 + 22*((k:ℚ)+2)^2 + 8*((k:ℚ)+2) + 1)
              * (Nat.choose (2*(k+2)-1) (k+2) : ℚ)^4 := by
            apply mul_pos
            · positivity
            · have : (0:ℚ) < (Nat.choose (2*(k+2)-1) (k+2) : ℚ) := by exact_mod_cast hBpos
              positivity
          linarith
        · positivity
      exact ⟨le_of_lt hval, fun _ => hval⟩

/-- Integrality and positivity of `a_Q`. -/
theorem a_Q_int (n : ℕ) : ∃ m : ℤ, a_Q n = (m : ℚ) ∧ 0 ≤ m ∧ (1 ≤ n → 1 ≤ m) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact ⟨0, by rw [a_Q]; simp, le_refl 0, by intro h; omega⟩
    | 1 => exact ⟨2, by rw [a_Q]; norm_num, by norm_num, by intro _; norm_num⟩
    | (k + 2) =>
      obtain ⟨m', hm'eq, hm'nn, hm'pos⟩ := ih (k+1) (by omega)
      set B : ℤ := (Bnat (k+2) : ℤ) with hB
      set num : ℤ := 32 * ((k:ℤ)+2)^3 * m'
        + (21*((k:ℤ)+2)^3 + 22*((k:ℤ)+2)^2 + 8*((k:ℤ)+2) + 1) * B^4 with hnum
      obtain ⟨q, hq⟩ := key_dvd k m' hm'eq
      have hval : a_Q (k+2) = (q : ℚ) := by
        rw [a_Q_succ_succ, hm'eq]
        have hqQ := congrArg (fun z : ℤ => (z : ℚ)) hq
        simp only [Bnat] at hqQ ⊢
        push_cast at hqQ ⊢
        rw [div_eq_iff (by positivity)]
        linear_combination hqQ
      have hpos : 0 < a_Q (k+2) := (a_Q_pos (k+2)).2 (by omega)
      rw [hval] at hpos
      have hq0 : 0 < q := by exact_mod_cast hpos
      exact ⟨q, hval, by omega, fun _ => by omega⟩

/-- The integer value of the sequence. -/
noncomputable def Aint (n : ℕ) : ℤ := (a_Q_int n).choose

theorem Aint_eq (n : ℕ) : a_Q n = (Aint n : ℚ) := (a_Q_int n).choose_spec.1
theorem Aint_nonneg (n : ℕ) : 0 ≤ Aint n := (a_Q_int n).choose_spec.2.1
theorem Aint_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ Aint n := (a_Q_int n).choose_spec.2.2 hn

/-- The integer recurrence (no division). -/
theorem Aint_rec (k : ℕ) :
    ((2 * (k:ℤ) + 5) ^ 3) * Aint (k + 2)
      = 32 * ((k:ℤ) + 2) ^ 3 * Aint (k + 1)
        + (21 * ((k:ℤ) + 2) ^ 3 + 22 * ((k:ℤ) + 2) ^ 2 + 8 * ((k:ℤ) + 2) + 1)
          * (Bnat (k + 2) : ℤ) ^ 4 := by
  have h := a_Q_succ_succ k
  rw [Aint_eq (k+2), Aint_eq (k+1)] at h
  have hden : (2 * ((k:ℚ)+2) + 1) ^ 3 ≠ 0 := by positivity
  rw [eq_div_iff hden] at h
  have : (((2 * (k:ℤ) + 5) ^ 3) * Aint (k+2) : ℚ)
      = (32 * ((k:ℤ) + 2) ^ 3 * Aint (k + 1)
        + (21 * ((k:ℤ) + 2) ^ 3 + 22 * ((k:ℤ) + 2) ^ 2 + 8 * ((k:ℤ) + 2) + 1)
          * (Bnat (k + 2) : ℤ) ^ 4 : ℤ) := by
    push_cast
    simp only [Bnat]
    linear_combination h
  exact_mod_cast this

/-- Parity of `Aint n`, from the recurrence mod 2. -/
theorem Aint_parity (n : ℕ) (hn : 1 ≤ n) :
    (Aint n : ZMod 2) = ((n : ZMod 2) + 1) * (Bnat n : ZMod 2) := by
  match n, hn with
  | 0, h => exact absurd h (by norm_num)
  | 1, _ =>
    have h1 : Aint 1 = 2 := by
      have h := Aint_eq 1
      rw [a_Q] at h
      exact_mod_cast h.symm
    rw [h1]
    simp only [Bnat]
    norm_num
  | (k + 2), _ =>
    have hrec := Aint_rec k
    have hz := congrArg (fun z : ℤ => (z : ZMod 2)) hrec
    push_cast at hz
    have key : ∀ x A1 A2 B : ZMod 2,
        (2 * x + 5) ^ 3 * A2
          = 32 * (x + 2) ^ 3 * A1
            + (21 * (x + 2) ^ 3 + 22 * (x + 2) ^ 2 + 8 * (x + 2) + 1) * B ^ 4
        → A2 = (x + 2 + 1) * B := by decide
    push_cast
    exact key _ _ _ _ hz

/-- Digit sum base 2 is invariant under multiplication by 2. -/
theorem digits2_two_mul (n : ℕ) : (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [Nat.digits_def' (by norm_num) (by omega)]
    simp [Nat.mul_mod_right, Nat.mul_div_cancel_left n (by norm_num : 0 < 2)]

/-- The digit sum of a power of two is 1. -/
theorem digits2_pow (m : ℕ) : (Nat.digits 2 (2 ^ m)).sum = 1 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_comm]
    rw [digits2_two_mul]
    exact ih

/-- Positive numbers have positive base-2 digit sum. -/
theorem digits2_sum_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ (Nat.digits 2 n).sum := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [Nat.digits_def' (by norm_num : (1:ℕ) < 2) (by omega)]
    simp only [List.sum_cons]
    rcases Nat.eq_zero_or_pos (n % 2) with h0 | h0
    · have hnd : 1 ≤ n / 2 := by omega
      have := ih (n / 2) (Nat.div_lt_self (by omega) (by norm_num)) hnd
      omega
    · omega

/-- Base-2 digit sum equals 1 iff the number is a power of two. -/
theorem digits2_eq_one_iff (n : ℕ) (hn : 1 ≤ n) :
    (Nat.digits 2 n).sum = 1 ↔ ∃ m : ℕ, n = 2 ^ m := by
  constructor
  · intro hs
    have forward : ∀ N, 1 ≤ N → (Nat.digits 2 N).sum = 1 → ∃ m : ℕ, N = 2 ^ m := by
      intro N
      induction N using Nat.strong_induction_on with
      | _ N ih =>
        intro hN hsN
        rw [Nat.digits_def' (by norm_num : (1:ℕ) < 2) (by omega)] at hsN
        simp only [List.sum_cons] at hsN
        rcases Nat.eq_zero_or_pos (N % 2) with h0 | h0
        · rw [h0, zero_add] at hsN
          have hnd : 1 ≤ N / 2 := by
            by_contra hc
            have hz : N / 2 = 0 := by omega
            rw [hz] at hsN; simp at hsN
          obtain ⟨m, hm⟩ := ih (N / 2) (Nat.div_lt_self (by omega) (by norm_num)) hnd hsN
          refine ⟨m + 1, ?_⟩
          have hN2 : N = 2 * (N / 2) := by omega
          rw [hN2, hm, pow_succ, mul_comm]
        · have hmod : N % 2 = 1 := by omega
          rw [hmod] at hsN
          have hz : N / 2 = 0 := by
            by_contra hc
            have := digits2_sum_pos (N / 2) (by omega)
            omega
          exact ⟨0, by omega⟩
    exact forward n hn hs
  · rintro ⟨m, rfl⟩
    exact digits2_pow m

/-- 2-adic valuation of the central binomial coefficient equals the base-2 digit sum. -/
theorem padicVal_centralBinom (n : ℕ) :
    padicValNat 2 ((2 * n).choose n) = (Nat.digits 2 n).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits' (p := 2) (n := n) (k := n)
  simp only [Nat.reduceSub, one_mul] at h
  rw [two_mul]
  rw [h]
  have hd : (Nat.digits 2 (n + n)).sum = (Nat.digits 2 n).sum := by
    rw [← two_mul]; exact digits2_two_mul n
  rw [hd]
  omega

/-- Kummer's criterion: `C(2n-1, n)` is odd iff `n` is a power of two. -/
theorem Bnat_odd_iff (n : ℕ) (hn : 1 ≤ n) : Odd (Bnat n) ↔ ∃ m : ℕ, n = 2 ^ m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBpos : 0 < Bnat n := Nat.choose_pos (by omega)
  have hpascal : (2 * n).choose n = 2 * Bnat n := by
    show (2 * n).choose n = 2 * ((2 * n - 1).choose n)
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have e1 : 2 * (t + 1) = (2 * t + 1) + 1 := by ring
    have e2 : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
    rw [e2, e1, Nat.choose_succ_succ (2 * t + 1) t]
    have hsym : (2 * t + 1).choose t = (2 * t + 1).choose (t + 1) := by
      have h := Nat.choose_symm (n := 2 * t + 1) (k := t) (by omega)
      rw [show 2 * t + 1 - t = t + 1 by omega] at h
      omega
    rw [hsym]; ring
  have hval : padicValNat 2 ((2 * n).choose n) = 1 + padicValNat 2 (Bnat n) := by
    rw [hpascal, padicValNat.mul (by norm_num) hBpos.ne', padicValNat_self]
  have hcb := padicVal_centralBinom n
  rw [hval] at hcb
  have hsumpos := digits2_sum_pos n hn
  have hodd : Odd (Bnat n) ↔ padicValNat 2 (Bnat n) = 0 := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd,
      dvd_iff_padicValNat_ne_zero hBpos.ne']
    tauto
  rw [hodd]
  have hiff : padicValNat 2 (Bnat n) = 0 ↔ (Nat.digits 2 n).sum = 1 := by omega
  rw [hiff]
  exact digits2_eq_one_iff n hn

/--
A176477: $a(1)=2$; for $n \ge 2$,
$$(2n+1)^3 a(n) = 32n^3 a(n-1) + (21n^3 + 22n^2 + 8n + 1) \binom{2n-1}{n}^4.$$
The sequence terms are non-negative integers. We compute the result using the rational recurrence and cast the result to $\mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ := (a_Q n).floor.toNat

theorem a_eq (n : ℕ) : a n = (Aint n).toNat := by
  unfold a
  rw [Aint_eq n]
  simp

theorem int_cast_zmod2_eq_one (x : ℤ) : (x : ZMod 2) = 1 ↔ Odd x := by
  have h2 : ∀ y : ZMod 2, (y = 1) ↔ ¬ (y = 0) := by decide
  rw [h2, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.odd_iff]
  omega

theorem nat_cast_zmod2_eq_one (x : ℕ) : (x : ZMod 2) = 1 ↔ Odd x := by
  have h2 : ∀ y : ZMod 2, (y = 1) ↔ ¬ (y = 0) := by decide
  rw [h2, ZMod.natCast_eq_zero_iff, Nat.odd_iff]
  omega

theorem nat_cast_zmod2_eq_zero (x : ℕ) : (x : ZMod 2) = 0 ↔ Even x :=
  ZMod.natCast_eq_zero_iff_even

/--
Conjecture of Zhi-Wei Sun (A176477):
Each term $a(n)$ is a positive integer.
Also, $a(n)$ is odd if and only if $n = 2^m$ for some $m \in \mathbb{Z}_{>0}$.
-/
theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  have hnn : 0 ≤ Aint n := Aint_nonneg n
  have hpos : 1 ≤ Aint n := Aint_pos n hn
  rw [a_eq n]
  have htn : ((Aint n).toNat : ℤ) = Aint n := Int.toNat_of_nonneg hnn
  refine ⟨?_, ?_⟩
  · have : (0:ℤ) < ((Aint n).toNat : ℤ) := by rw [htn]; omega
    exact_mod_cast this
  · have hodd_iff : Odd ((Aint n).toNat) ↔ Odd (Aint n) := by
      rw [← Int.odd_coe_nat, htn]
    rw [hodd_iff, ← int_cast_zmod2_eq_one, Aint_parity n hn]
    have hkey : ∀ a b : ZMod 2, (a + 1) * b = 1 ↔ (a = 0 ∧ b = 1) := by decide
    rw [hkey, nat_cast_zmod2_eq_zero, nat_cast_zmod2_eq_one]
    rw [Bnat_odd_iff n hn]
    constructor
    · rintro ⟨hev, m, rfl⟩
      refine ⟨m, ?_, rfl⟩
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp at hev
      · exact hm
    · rintro ⟨m, hm1, rfl⟩
      refine ⟨?_, m, rfl⟩
      exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
