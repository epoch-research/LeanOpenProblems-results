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

/-- Positivity of the rational recurrence: `a_Q n ≥ 1` for `n ≥ 1`.
This is unconditional (all terms in the recurrence are positive). -/
theorem a_Q_ge_one (n : ℕ) (hn : 1 ≤ n) : (1:ℚ) ≤ a_Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn with
    | 1, _ => norm_num [a_Q]
    | (k+2), _ =>
      have hprev : (1:ℚ) ≤ a_Q (k+1) := ih (k+1) (by omega) (by omega)
      have hidx : (k + 2 - 1) = (k+1) := by omega
      rw [a_Q, hidx]
      rw [le_div_iff₀ (by positivity)]
      have h1 : (32:ℚ) * ((k:ℚ)+2)^3 * a_Q (k+1) ≥ 32 * ((k:ℚ)+2)^3 := by
        nlinarith [hprev, pow_pos (by positivity : (0:ℚ) < (k:ℚ)+2) 3]
      have h2 : (0:ℚ) ≤ (21 * ((k:ℚ)+2)^3 + 22*((k:ℚ)+2)^2 + 8*((k:ℚ)+2) + 1)
          * ((Nat.choose (2*(k+2)-1) (k+2)):ℚ)^4 := by positivity
      push_cast
      push_cast at h1 h2
      nlinarith [h1, h2, sq_nonneg ((k:ℚ)+2)]

/-- The positivity half of the conjecture. -/
theorem pos_conjunct (n : ℕ) (hn : 1 ≤ n) : 0 < a n := by
  have h1 : (1:ℚ) ≤ a_Q n := a_Q_ge_one n hn
  have hf : (1:ℤ) ≤ (a_Q n).floor := Int.le_floor.mpr (by exact_mod_cast h1)
  unfold a
  omega

/-- Recurrence identity in `ℚ` (multiplied out to avoid division). -/
theorem a_Q_rec (k : ℕ) :
    a_Q (k+2) * (2 * ((k:ℚ)+2) + 1) ^ 3
      = 32 * ((k:ℚ)+2) ^ 3 * a_Q (k+1)
        + (21 * ((k:ℚ)+2)^3 + 22 * ((k:ℚ)+2)^2 + 8 * ((k:ℚ)+2) + 1)
          * ((Nat.choose (2*(k+2)-1) (k+2) : ℚ)) ^ 4 := by
  have hidx : (k + 2 - 1) = (k+1) := by omega
  rw [a_Q, hidx]
  have hden : (2 * ((k:ℚ)+2) + 1) ^ 3 ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- Integer recurrence for the numerators, given integrality of the two previous values. -/
theorem int_rec (k : ℕ) (z1 z2 : ℤ)
    (h1 : a_Q (k+1) = (z1 : ℚ)) (h2 : a_Q (k+2) = (z2 : ℚ)) :
    z2 * (2 * ((k:ℤ)+2) + 1) ^ 3
      = 32 * ((k:ℤ)+2) ^ 3 * z1
        + (21 * ((k:ℤ)+2)^3 + 22 * ((k:ℤ)+2)^2 + 8 * ((k:ℤ)+2) + 1)
          * ((Nat.choose (2*(k+2)-1) (k+2) : ℤ)) ^ 4 := by
  have hrec := a_Q_rec k
  rw [h1, h2] at hrec
  have : ((z2 * (2 * ((k:ℤ)+2) + 1) ^ 3 : ℤ) : ℚ)
      = (((32 * ((k:ℤ)+2) ^ 3 * z1
        + (21 * ((k:ℤ)+2)^3 + 22 * ((k:ℤ)+2)^2 + 8 * ((k:ℤ)+2) + 1)
          * ((Nat.choose (2*(k+2)-1) (k+2) : ℤ)) ^ 4) : ℤ) : ℚ) := by
    push_cast
    linarith [hrec]
  exact_mod_cast this

/-- Reducing the recurrence mod 2: `a(k+2) ≡ (k+1)·C(2k+3,k+2) (mod 2)`. -/
theorem zmod2_cong (k : ℕ) (z1 z2 : ℤ)
    (h1 : a_Q (k+1) = (z1 : ℚ)) (h2 : a_Q (k+2) = (z2 : ℚ)) :
    (z2 : ZMod 2) = ((k : ZMod 2) + 1) * ((Nat.choose (2*(k+2)-1) (k+2) : ℕ) : ZMod 2) := by
  have h := congrArg (fun t : ℤ => (t : ZMod 2)) (int_rec k z1 z2 h1 h2)
  simp only at h
  push_cast at h
  have e2 : (2 : ZMod 2) = 0 := by decide
  have e8 : (8 : ZMod 2) = 0 := by decide
  have e21 : (21 : ZMod 2) = 1 := by decide
  have e22 : (22 : ZMod 2) = 0 := by decide
  have e32 : (32 : ZMod 2) = 0 := by decide
  have hcube : ∀ y : ZMod 2, y ^ 3 = y := by decide
  have hquart : ∀ y : ZMod 2, y ^ 4 = y := by decide
  simp only [e2, e8, e21, e22, e32, zero_mul, mul_zero, add_zero, zero_add,
    one_mul, mul_one, one_pow] at h
  rw [hcube, hquart] at h
  exact h

theorem nat_odd_zmod (m : ℕ) : Odd m ↔ (m : ZMod 2) = 1 := by
  rw [← Nat.not_even_iff_odd, ← ZMod.natCast_eq_zero_iff_even]
  have : ∀ x : ZMod 2, ¬ (x = 0) ↔ x = 1 := by decide
  exact this _

theorem odd_toNat_iff (z : ℤ) (hz : 1 ≤ z) : Odd (z.toNat) ↔ (z : ZMod 2) = 1 := by
  have hz0 : (0:ℤ) ≤ z := by linarith
  have hcast : ((z.toNat : ℤ)) = z := Int.toNat_of_nonneg hz0
  have hz2 : ((z.toNat : ZMod 2)) = (z : ZMod 2) := by
    rw [show ((z.toNat : ZMod 2)) = (((z.toNat : ℤ)) : ZMod 2) from (Int.cast_natCast _).symm,
      hcast]
  rw [nat_odd_zmod, hz2]

/--
Integrality of the sequence. This is the crux of Zhi-Wei Sun's A176477 conjecture.

It is equivalent to the supercongruence, for every odd prime `p`,
`∑_{m=0}^{(p-1)/2} (21m³+22m²+8m+1) C(2m,m)⁷ / 256ᵐ ≡ p³ (mod p³)`
(numerically the valuation is exactly `p⁷`), together with its prime-power
refinements. This is the "divergent dual" of Guillera's `1/π³` Ramanujan-type
series `∑ (1/2)ₘ⁷/m!⁷ (168m³+76m²+14m+1)/64ᵐ = 32/π³`. It is a seventh-power
central-binomial supercongruence, one level beyond the proven fourth-power
frontier (Kilbourn), and is an open conjecture.
-/
theorem integrality (n : ℕ) : ∃ z : ℤ, a_Q n = (z : ℚ) := by
  sorry

-- Standard (Kummer / Legendre): `C(2n-1,n)` is odd iff `n` is a power of 2.
theorem digitsum_pos_aux (m : ℕ) (hm : m ≠ 0) : (Nat.digits 2 m).sum ≠ 0 := by
  have hne : Nat.digits 2 m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hm
  have hlast : (Nat.digits 2 m).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 2 hm
  have hmem : (Nat.digits 2 m).getLast hne ∈ Nat.digits 2 m := List.getLast_mem hne
  have hle : (Nat.digits 2 m).getLast hne ≤ (Nat.digits 2 m).sum := List.le_sum_of_mem hmem
  intro hs
  rw [hs] at hle
  exact hlast (Nat.le_zero.mp hle)

theorem digits_sum_pow (j : ℕ) : (Nat.digits 2 (2 ^ j)).sum = 1 := by
  induction j with
  | zero => rw [pow_zero, Nat.digits_def' (by norm_num : (1:ℕ) < 2) (by norm_num)]; simp
  | succ j ih =>
    rw [pow_succ, mul_comm, Nat.digits_base_mul (by norm_num) (by positivity), List.sum_cons]
    simpa using ih

theorem digits_sum_one_forward : ∀ m : ℕ, (Nat.digits 2 m).sum = 1 → ∃ j, m = 2 ^ j := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro h
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp at h
    rw [Nat.digits_def' (by norm_num : (1:ℕ) < 2) hpos, List.sum_cons] at h
    have hm2 : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases hm2 with he | ho
    · rw [he] at h
      simp only [zero_add] at h
      have hd2 : m / 2 < m := Nat.div_lt_self hpos (by norm_num)
      obtain ⟨j, hj⟩ := ih (m / 2) hd2 h
      refine ⟨j + 1, ?_⟩
      rw [pow_succ, ← hj]
      omega
    · rw [ho] at h
      have hsum0 : (Nat.digits 2 (m / 2)).sum = 0 := by omega
      rcases Nat.eq_zero_or_pos (m / 2) with hz | hpos2
      · refine ⟨0, ?_⟩
        simp only [pow_zero]
        omega
      · exact absurd hsum0 (digitsum_pos_aux (m / 2) (by omega))

theorem binom_odd_iff (n : ℕ) (hn : 1 ≤ n) :
    Odd (Nat.choose (2*n-1) n) ↔ ∃ j : ℕ, n = 2^j := by
  have hp2 : Nat.Prime 2 := Nat.prime_two
  have hc' : Nat.choose (2*n-1) n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hc : Nat.choose (2*n) n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hfacn : Nat.factorial n ≠ 0 := Nat.factorial_ne_zero n
  have key : Nat.choose (2*n) n = 2 * Nat.choose (2*n-1) n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have e1 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    have e2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [e2, e1, Nat.choose_succ_succ']
    have hsym : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m := by
      have hs := Nat.choose_symm (n := 2 * m + 1) (k := m + 1) (by omega)
      rw [show (2 * m + 1) - (m + 1) = m by omega] at hs
      exact hs.symm
    rw [hsym]; ring
  have hf : (Nat.factorial n).factorization 2 = n - (Nat.digits 2 n).sum := by
    have h := Nat.sub_one_mul_factorization_factorial (n := n) hp2
    simpa using h
  have hmul : (Nat.factorial (2*n)).factorization 2
            = (Nat.factorial n).factorization 2 + n := by
    have h := Nat.factorization_factorial_mul (n := n) hp2
    simpa using h
  have prod : Nat.choose (2*n) n * Nat.factorial n * Nat.factorial n = Nat.factorial (2*n) := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := 2*n) (k := n) (by omega)
    simpa [show 2*n - n = n by omega] using h
  have hprod : (Nat.choose (2*n) n).factorization 2
             + (Nat.factorial n).factorization 2
             + (Nat.factorial n).factorization 2
             = (Nat.factorial (2*n)).factorization 2 := by
    have h2 : (Nat.choose (2*n) n * Nat.factorial n * Nat.factorial n).factorization 2
            = (Nat.factorial (2*n)).factorization 2 := by rw [prod]
    rw [Nat.factorization_mul (mul_ne_zero hc hfacn) hfacn,
        Nat.factorization_mul hc hfacn] at h2
    simpa [Finsupp.add_apply] using h2
  have hrel : (Nat.choose (2*n) n).factorization 2
            = 1 + (Nat.choose (2*n-1) n).factorization 2 := by
    rw [key, Nat.factorization_mul (by norm_num) hc', Finsupp.add_apply,
        Nat.Prime.factorization_self hp2]
  have hodd : Odd (Nat.choose (2*n-1) n) ↔ (Nat.choose (2*n-1) n).factorization 2 = 0 := by
    rw [← not_even_iff_odd, even_iff_two_dvd,
        Nat.Prime.dvd_iff_one_le_factorization hp2 hc']
    omega
  have hDle : (Nat.digits 2 n).sum ≤ n := Nat.digit_sum_le 2 n
  have hfact : (Nat.choose (2*n) n).factorization 2 = (Nat.digits 2 n).sum := by omega
  have hBD : (Nat.choose (2*n-1) n).factorization 2 = 0 ↔ (Nat.digits 2 n).sum = 1 := by omega
  rw [hodd, hBD]
  constructor
  · exact digits_sum_one_forward n
  · rintro ⟨j, rfl⟩
    exact digits_sum_pow j

/--
Conjecture of Zhi-Wei Sun (A176477):
Each term $a(n)$ is a positive integer.
Also, $a(n)$ is odd if and only if $n = 2^m$ for some $m \in \mathbb{Z}_{>0}$.
-/
theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  refine ⟨pos_conjunct n hn, ?_⟩
  match n, hn with
  | 1, _ =>
    have hq : a_Q 1 = (2:ℚ) := rfl
    have ha1 : a 1 = 2 := by
      unfold a; rw [hq]; decide
    rw [ha1]
    constructor
    · intro h; exact absurd h (by decide)
    · rintro ⟨m, hm, he⟩
      have h2m : (2:ℕ)^m ≥ 2 := by
        calc (2:ℕ)^m ≥ 2^1 := Nat.pow_le_pow_right (by norm_num) hm
          _ = 2 := by norm_num
      omega
  | (k+2), _ =>
    obtain ⟨z2, hz2eq⟩ := integrality (k+2)
    obtain ⟨z1, hz1eq⟩ := integrality (k+1)
    have hz2ge : (1:ℚ) ≤ a_Q (k+2) := a_Q_ge_one (k+2) (by omega)
    have hz2ge1 : 1 ≤ z2 := by rw [hz2eq] at hz2ge; exact_mod_cast hz2ge
    have haval : a (k+2) = z2.toNat := by
      unfold a; rw [hz2eq]; simp
    rw [haval, odd_toNat_iff z2 hz2ge1, zmod2_cong k z1 z2 hz1eq hz2eq]
    have hd1 : ∀ x y : ZMod 2, x * y = 1 ↔ x = 1 ∧ y = 1 := by decide
    have hd2 : ∀ x : ZMod 2, (x + 1 = 1 ↔ x = 0) := by decide
    rw [hd1, hd2]
    rw [ZMod.natCast_eq_zero_iff_even, ← nat_odd_zmod,
        binom_odd_iff (k+2) (by omega)]
    -- goal: (Even k ∧ ∃ j, k+2 = 2^j) ↔ ∃ m, m ≥ 1 ∧ k+2 = 2^m
    constructor
    · rintro ⟨hev, j, hj⟩
      refine ⟨j, ?_, hj⟩
      rcases j with _ | j
      · rw [pow_zero] at hj; omega
      · omega
    · rintro ⟨m, hm, he⟩
      have hev2 : Even (k+2) := by
        rw [he]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
      obtain ⟨r, hr⟩ := hev2
      exact ⟨⟨r - 1, by omega⟩, m, he⟩
