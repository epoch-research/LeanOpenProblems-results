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

/--
A176477: $a(1)=2$; for $n \ge 2$,
$$(2n+1)^3 a(n) = 32n^3 a(n-1) + (21n^3 + 22n^2 + 8n + 1) \binom{2n-1}{n}^4.$$
The sequence terms are non-negative integers. We compute the result using the rational recurrence and cast the result to $\mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ := (a_Q n).floor.toNat

/-- Unfolding lemma for the rational recurrence at index `n = k + 2`. -/
theorem a_Q_rec (k : ℕ) : a_Q (k + 2) =
    (32 * ((k + 2 : ℚ)) ^ 3 * a_Q (k + 1) +
        (21 * ((k + 2 : ℚ)) ^ 3 + 22 * ((k + 2 : ℚ)) ^ 2 + 8 * ((k + 2 : ℚ)) + 1) *
          ((Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ)) ^ 4) /
      ((2 * ((k + 2 : ℚ)) + 1) ^ 3) := by
  conv_lhs => rw [a_Q]
  have : k + 2 - 1 = k + 1 := by omega
  rw [this]; push_cast; ring

/-- The rational sequence `a_Q` is at least `1` for every `n ≥ 1`.  This is proved
directly from the recurrence (all terms are positive and the numerator dominates
the denominator), and does *not* require the (open) integrality of the sequence. -/
theorem a_Q_pos : ∀ n, 1 ≤ n → 1 ≤ a_Q n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    match n, hn with
    | 1, _ => rw [show a_Q 1 = 2 from rfl]; norm_num
    | (k + 2), _ =>
      rw [a_Q_rec]
      have hprev : 1 ≤ a_Q (k + 1) := ih (k + 1) (by omega) (by omega)
      have hm : (2 : ℚ) ≤ (k : ℚ) + 2 := by
        have : (0 : ℚ) ≤ (k : ℚ) := by positivity
        linarith
      rw [le_div_iff₀ (by positivity)]
      have hbinom : (0 : ℚ) ≤ ((Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ)) ^ 4 := by positivity
      have hterm1 : 32 * ((k + 2 : ℚ)) ^ 3 * 1 ≤ 32 * ((k + 2 : ℚ)) ^ 3 * a_Q (k + 1) := by
        apply mul_le_mul_of_nonneg_left hprev; positivity
      have key : (1 : ℚ) * (2 * ((k + 2 : ℚ)) + 1) ^ 3 ≤ 32 * ((k + 2 : ℚ)) ^ 3 * 1 := by
        nlinarith [hm, sq_nonneg ((k : ℚ) + 2)]
      have hpos2 : (0 : ℚ) ≤ (21 * ((k + 2 : ℚ)) ^ 3 + 22 * ((k + 2 : ℚ)) ^ 2 + 8 * ((k + 2 : ℚ)) + 1) *
          ((Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ)) ^ 4 := by positivity
      linarith [hterm1, key, hpos2]

/-- Consequently every term `a n` is a positive natural number (for `n ≥ 1`). -/
theorem a_pos (n : ℕ) (hn : n ≥ 1) : 0 < a n := by
  have h1 : (1 : ℚ) ≤ a_Q n := a_Q_pos n hn
  have hfloor : (1 : ℤ) ≤ (a_Q n).floor := by
    rw [Rat.le_floor]; exact_mod_cast h1
  unfold a
  omega


section Kummer
open Finset

theorem v2_centralBinom (n : ℕ) :
    (Nat.centralBinom n).factorization 2 = (Nat.digits 2 n).sum := by
  have hfac : Nat.centralBinom n * (n ! * n !) = (2 * n)! := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 2 * n) (k := n) (by omega)
    rw [Nat.centralBinom]
    have h2 : 2 * n - n = n := by omega
    rw [h2] at this
    linarith [this]
  -- take factorization at 2
  have hne : Nat.centralBinom n ≠ 0 := Nat.centralBinom_ne_zero n
  have hnf : n ! ≠ 0 := Nat.factorial_ne_zero n
  have key : (Nat.centralBinom n).factorization 2 + ((n !).factorization 2 + (n !).factorization 2)
      = ((2 * n)!).factorization 2 := by
    have := congrArg (fun m => m.factorization 2) hfac
    simp only at this
    rw [Nat.factorization_mul hne (by positivity), Nat.factorization_mul hnf hnf] at this
    simpa [Finsupp.add_apply] using this
  have hmul : ((2 * n)!).factorization 2 = (n !).factorization 2 + n :=
    Nat.factorization_factorial_mul (by norm_num)
  have hsub : (1 : ℕ) * (n !).factorization 2 = n - (Nat.digits 2 n).sum := by
    have := Nat.sub_one_mul_factorization_factorial (n := n) (p := 2) (by norm_num)
    simpa using this
  rw [one_mul] at hsub
  -- combine
  have hle : (Nat.digits 2 n).sum ≤ n := Nat.digit_sum_le 2 n
  omega

theorem ofDigits_zero_of_all_zero : ∀ (L : List ℕ), (∀ x ∈ L, x = 0) →
    Nat.ofDigits 2 L = 0 := by
  intro L
  induction L with
  | nil => intro _; simp [Nat.ofDigits]
  | cons a t ih =>
    intro h
    simp only [Nat.ofDigits_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- The binary digit sum is zero iff the number is zero. -/
theorem digitsum_eq_zero_iff (k : ℕ) : (Nat.digits 2 k).sum = 0 ↔ k = 0 := by
  constructor
  · intro h
    have hall : ∀ x ∈ Nat.digits 2 k, x = 0 := (List.sum_eq_zero_iff).mp h
    have : Nat.ofDigits 2 (Nat.digits 2 k) = 0 := ofDigits_zero_of_all_zero _ hall
    rwa [Nat.ofDigits_digits] at this
  · rintro rfl; simp

/-- `2 * C(2n-1, n) = C(2n, n)` for `n ≥ 1`. -/
theorem two_mul_choose (n : ℕ) (hn : 1 ≤ n) :
    2 * Nat.choose (2 * n - 1) n = Nat.centralBinom n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.centralBinom]
  have e2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e1 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
  rw [e2, e1, Nat.choose_succ_succ (2 * k + 1) k]
  simp only [Nat.succ_eq_add_one]
  have esym : Nat.choose (2 * k + 1) k = Nat.choose (2 * k + 1) (k + 1) := by
    have := Nat.choose_symm (n := 2 * k + 1) (k := k) (by omega)
    rw [show 2 * k + 1 - k = k + 1 by omega] at this
    omega
  omega

/-- Binary digit sum equals one iff the number is a power of two. -/
theorem digitsum_eq_one_iff (n : ℕ) (hn : 1 ≤ n) :
    (Nat.digits 2 n).sum = 1 ↔ ∃ m : ℕ, n = 2 ^ m := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hd : Nat.digits 2 n = n % 2 :: Nat.digits 2 (n / 2) :=
      Nat.digits_def' (by norm_num) (by omega)
    rw [hd, List.sum_cons]
    rcases Nat.even_or_odd n with ⟨i, hi⟩ | ⟨j, hj⟩
    · -- n even, n ≥ 2
      have hmod : n % 2 = 0 := by omega
      have hn2 : 1 ≤ n / 2 := by omega
      have hlt : n / 2 < n := by omega
      rw [hmod, zero_add]
      rw [ih (n / 2) hlt hn2]
      constructor
      · rintro ⟨m, hm⟩
        refine ⟨m + 1, ?_⟩
        have : n = 2 ^ m * 2 := by omega
        rw [pow_succ]; omega
      · rintro ⟨m, hm⟩
        refine ⟨m - 1, ?_⟩
        have hm1 : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with h0 | hp
          · rw [h0, pow_zero] at hm; omega
          · exact hp
        have hnn : n = 2 ^ (m - 1) * 2 := by
          rw [hm, ← pow_succ]; congr 1; omega
        omega
    · -- n odd
      have hmod : n % 2 = 1 := by omega
      rw [hmod]
      constructor
      · intro h
        have h0 : (Nat.digits 2 (n / 2)).sum = 0 := by omega
        have hz : n / 2 = 0 := (digitsum_eq_zero_iff _).mp h0
        exact ⟨0, by rw [pow_zero]; omega⟩
      · rintro ⟨m, hm⟩
        -- n odd power of two ⟹ n = 1
        have hm0 : m = 0 := by
          by_contra hne
          have hm1 : 1 ≤ m := by omega
          have hev : n = 2 ^ (m - 1) * 2 := by
            rw [hm, ← pow_succ]; congr 1; omega
          omega
        rw [hm, hm0, pow_zero]
        simp

/-- Kummer-type oddness: `C(2n-1, n)` is odd iff `n` is a power of two. -/
theorem odd_choose_iff (n : ℕ) (hn : 1 ≤ n) :
    Odd (Nat.choose (2 * n - 1) n) ↔ ∃ m : ℕ, n = 2 ^ m := by
  have hc : 2 * Nat.choose (2 * n - 1) n = Nat.centralBinom n := two_mul_choose n hn
  have hcpos : 0 < Nat.choose (2 * n - 1) n := Nat.choose_pos (by omega)
  have hv : (Nat.choose (2 * n - 1) n).factorization 2 + 1 = (Nat.digits 2 n).sum := by
    have h1 : (2 * Nat.choose (2 * n - 1) n).factorization 2 = (Nat.centralBinom n).factorization 2 := by
      rw [hc]
    rw [Nat.factorization_mul (by norm_num) (by omega), v2_centralBinom] at h1
    have h2 : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self (by norm_num)
    rw [Finsupp.add_apply] at h1
    rw [h2] at h1
    omega
  rw [← digitsum_eq_one_iff n hn, ← hv]
  have hdvd : (2 ∣ Nat.choose (2 * n - 1) n) ↔ 1 ≤ (Nat.choose (2 * n - 1) n).factorization 2 := by
    have := (Nat.Prime.pow_dvd_iff_le_factorization (p := 2) (n := Nat.choose (2 * n - 1) n)
      (k := 1) (by norm_num) (by omega))
    simpa using this
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd, hdvd]
  omega

end Kummer

theorem int_rec (k : ℕ) (z zp : ℤ)
    (hz : a_Q (k + 2) = (z : ℚ)) (hzp : a_Q (k + 1) = (zp : ℚ)) :
    (2 * (k + 2) + 1) ^ 3 * z =
      32 * (k + 2) ^ 3 * zp +
        (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) *
          (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℤ) ^ 4 := by
  have hrec := a_Q_rec k
  have hD : ((2 * ((k : ℚ) + 2) + 1) ^ 3) ≠ 0 := by positivity
  rw [hz, hzp, eq_div_iff hD] at hrec
  have hq : (((2 * (k + 2) + 1) ^ 3 * z : ℤ)) =
      ((32 * (k + 2) ^ 3 * zp +
        (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) *
          (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℤ) ^ 4 : ℤ)) := by
    have : ((((2 * (k + 2) + 1) ^ 3 * z : ℤ)) : ℚ) =
        ((32 * (k + 2) ^ 3 * zp +
          (21 * (k + 2) ^ 3 + 22 * (k + 2) ^ 2 + 8 * (k + 2) + 1) *
            (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℤ) ^ 4 : ℤ) : ℚ) := by
      push_cast
      push_cast at hrec
      linarith [hrec]
    exact_mod_cast this
  exact hq

theorem evenQaux (n : ℤ) : Even (21 * n ^ 3 + 22 * n ^ 2 + 7 * n) := by
  rcases Int.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact ⟨84 * t ^ 3 + 44 * t ^ 2 + 7 * t, by ring⟩
  · exact ⟨84 * t ^ 3 + 170 * t ^ 2 + 114 * t + 25, by ring⟩

/-- Parity step: from the integer recurrence, `z` has the same parity as `(n+1)·C^4`. -/
theorem parity_step (k : ℕ) (z zp : ℤ)
    (heq : (2 * ((k : ℤ) + 2) + 1) ^ 3 * z =
      32 * ((k : ℤ) + 2) ^ 3 * zp +
        (21 * ((k : ℤ) + 2) ^ 3 + 22 * ((k : ℤ) + 2) ^ 2 + 8 * ((k : ℤ) + 2) + 1) *
          (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℤ) ^ 4) :
    Odd z ↔ Odd (((k : ℤ) + 2 + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℤ)) := by
  set n : ℤ := (k : ℤ) + 2 with hn
  set C : ℤ := (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℤ) with hC
  clear_value n C
  have hid : z - (n + 1) * C ^ 4 =
      32 * n ^ 3 * zp - ((2 * n + 1) ^ 3 - 1) * z + (21 * n ^ 3 + 22 * n ^ 2 + 7 * n) * C ^ 4 := by
    linear_combination heq
  have h1 : Even (32 * n ^ 3 * zp) := ⟨16 * n ^ 3 * zp, by ring⟩
  have h2 : Even (((2 * n + 1) ^ 3 - 1) * z) := by
    have hb : Odd (2 * n + 1) := ⟨n, by ring⟩
    have hodd : Odd ((2 * n + 1) ^ 3) := hb.pow
    exact (hodd.sub_odd odd_one).mul_right z
  have h3 : Even ((21 * n ^ 3 + 22 * n ^ 2 + 7 * n) * C ^ 4) := (evenQaux n).mul_right _
  have heven : Even (z - (n + 1) * C ^ 4) := by
    rw [hid]; exact ((h1.sub h2).add h3)
  have hEE : Even z ↔ Even ((n + 1) * C ^ 4) := Int.even_sub.mp heven
  have hpar : Odd z ↔ Odd ((n + 1) * C ^ 4) := by
    constructor
    · intro hz
      rw [← Int.not_even_iff_odd] at hz ⊢
      exact fun h => hz (hEE.mpr h)
    · intro hz
      rw [← Int.not_even_iff_odd] at hz ⊢
      exact fun h => hz (hEE.mp h)
  have hpc : Odd (C ^ 4) ↔ Odd C := by
    have hCC : C ^ 4 = C * C ^ 3 := by ring
    rw [hCC, Int.odd_mul]
    constructor
    · rintro ⟨h, _⟩; exact h
    · intro h; exact ⟨h, h.pow⟩
  rw [hpar, Int.odd_mul, Int.odd_mul, hpc]

/--
**Integrality of the sequence (the open crux).**
`a_Q n` is a genuine integer for every `n ≥ 1`.  Equivalently
`16 (2n+1)^3 \binom{2n}{n}^3 ∣ F(n)` where `F(n) = Σ_{k≤n} 256^{n-k} Q(k) \binom{2k}{k}^7`,
`Q(k) = 21k^3+22k^2+8k+1`.  This is a *rank-7 supercongruence*, the p-adic dual of
Gourevich's conjectural series `Σ (168k^3+76k^2+14k+1)\binom{2k}{k}^7/2^{20k} = 32/π^3`;
it is an open conjecture of Zhi-Wei Sun (A176477).  Every other part of this file is
proved unconditionally; this single fact is the one remaining gap.
-/
theorem a_Q_int (n : ℕ) (hn : 1 ≤ n) : ∃ z : ℤ, a_Q n = (z : ℚ) := by
  sorry

/--
Conjecture of Zhi-Wei Sun (A176477):
Each term $a(n)$ is a positive integer.
Also, $a(n)$ is odd if and only if $n = 2^m$ for some $m \in \mathbb{Z}_{>0}$.
-/
theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  refine ⟨a_pos n hn, ?_⟩
  match n, hn with
  | 1, _ =>
    have h1 : a 1 = 2 := by rfl
    rw [h1]
    constructor
    · intro h; exact absurd h (by decide)
    · rintro ⟨m, hm1, hm2⟩
      have hlt : (2 : ℕ) ≤ 2 ^ m := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
      omega
  | (k + 2), _ =>
    obtain ⟨z, hz⟩ := a_Q_int (k + 2) (by omega)
    obtain ⟨zp, hzp⟩ := a_Q_int (k + 1) (by omega)
    -- `a (k+2) = z.toNat`, and `z ≥ 1`.
    have hzpos : (1 : ℚ) ≤ a_Q (k + 2) := a_Q_pos (k + 2) (by omega)
    have hz1 : 1 ≤ z := by rw [hz] at hzpos; exact_mod_cast hzpos
    have hfloor : (a_Q (k + 2)).floor = z := by rw [hz]; simp
    have haz : a (k + 2) = z.toNat := by unfold a; rw [hfloor]
    rw [haz]
    -- reduce oddness of `z.toNat` to oddness of `z`
    have hcast : ((z.toNat : ℤ)) = z := Int.toNat_of_nonneg (by omega)
    have hoddtoNat : Odd (z.toNat) ↔ Odd z := by rw [← Int.odd_coe_nat, hcast]
    rw [hoddtoNat]
    -- integer recurrence and the mod-2 parity step
    have heq := int_rec k z zp hz hzp
    rw [parity_step k z zp heq]
    -- unwind the product oddness into the final characterisation
    rw [Int.odd_mul]
    have hcoe : ((k : ℤ) + 2 + 1) = ((k + 3 : ℕ) : ℤ) := by push_cast; ring
    rw [hcoe, Int.odd_coe_nat, Int.odd_coe_nat]
    rw [odd_choose_iff (k + 2) (by omega)]
    have hoe : Odd (k + 3) ↔ Even (k + 2) := by
      rw [Nat.odd_iff, Nat.even_iff]; omega
    rw [hoe]
    constructor
    · rintro ⟨_, m, hm⟩
      refine ⟨m, ?_, hm⟩
      rcases Nat.eq_zero_or_pos m with h0 | hp
      · subst h0; rw [pow_zero] at hm; omega
      · exact hp
    · rintro ⟨m, hm1, hm⟩
      refine ⟨?_, m, hm⟩
      rw [hm]
      exact Nat.even_pow.mpr ⟨even_two, by omega⟩
