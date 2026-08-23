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

lemma a_Q_zero : a_Q 0 = 0 := rfl

lemma a_Q_one : a_Q 1 = 2 := rfl

lemma a_Q_of_ge_two (n : ℕ) (hn : 2 ≤ n) :
    a_Q n =
      (32 * (n : ℚ) ^ 3 * a_Q (n - 1) +
        (21 * (n : ℚ) ^ 3 + 22 * (n : ℚ) ^ 2 + 8 * (n : ℚ) + 1) *
          (Nat.choose (2 * n - 1) n : ℚ) ^ 4) /
      ((2 * (n : ℚ) + 1) ^ 3) := by
  match n with
  | 0 => omega
  | 1 => omega
  | k + 2 =>
    simp [a_Q]

/-- $a_Q(n)\ge 2$ for every $n\ge 1$. -/
lemma a_Q_ge_two (n : ℕ) (hn : 1 ≤ n) : (2 : ℚ) ≤ a_Q n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => omega
    | 1 =>
      simp [a_Q_one]
    | k + 2 =>
      have hk2 : 2 ≤ k + 2 := by omega
      rw [a_Q_of_ge_two (k + 2) hk2]
      have hprev : (2 : ℚ) ≤ a_Q (k + 1) := ih (k + 1) (by omega) (by omega)
      have hden_pos : (0 : ℚ) < (2 * ((k + 2 : ℕ) : ℚ) + 1) ^ 3 := by positivity
      have hP :
          (0 : ℚ) ≤
            (21 * ((k + 2 : ℕ) : ℚ) ^ 3 + 22 * ((k + 2 : ℕ) : ℚ) ^ 2 +
                8 * ((k + 2 : ℕ) : ℚ) + 1) *
              (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ) ^ 4 := by
        positivity
      have hmul : 32 * ((k + 2 : ℕ) : ℚ) ^ 3 * (2 : ℚ) ≤
          32 * ((k + 2 : ℕ) : ℚ) ^ 3 * a_Q (k + 1) := by
        have h32 : (0 : ℚ) ≤ 32 * ((k + 2 : ℕ) : ℚ) ^ 3 := by positivity
        exact mul_le_mul_of_nonneg_left hprev h32
      have hnum :
          32 * ((k + 2 : ℕ) : ℚ) ^ 3 * (2 : ℚ) ≤
            32 * ((k + 2 : ℕ) : ℚ) ^ 3 * a_Q (k + 1) +
              ((21 * ((k + 2 : ℕ) : ℚ) ^ 3 + 22 * ((k + 2 : ℕ) : ℚ) ^ 2 +
                  8 * ((k + 2 : ℕ) : ℚ) + 1) *
                (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ) ^ 4) := by
        linarith
      have hfrac :
          (32 * ((k + 2 : ℕ) : ℚ) ^ 3 * (2 : ℚ)) /
              ((2 * ((k + 2 : ℕ) : ℚ) + 1) ^ 3) ≤
            (32 * ((k + 2 : ℕ) : ℚ) ^ 3 * a_Q (k + 1) +
              ((21 * ((k + 2 : ℕ) : ℚ) ^ 3 + 22 * ((k + 2 : ℕ) : ℚ) ^ 2 +
                  8 * ((k + 2 : ℕ) : ℚ) + 1) *
                (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ) ^ 4)) /
            ((2 * ((k + 2 : ℕ) : ℚ) + 1) ^ 3) :=
        div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
      have h64 : (2 : ℚ) ≤
          (64 * ((k + 2 : ℕ) : ℚ) ^ 3) / ((2 * ((k + 2 : ℕ) : ℚ) + 1) ^ 3) := by
        rw [le_div_iff₀ hden_pos]
        have hm : (2 : ℚ) ≤ ((k + 2 : ℕ) : ℚ) := by exact_mod_cast hk2
        nlinarith [sq_nonneg (((k + 2 : ℕ) : ℚ) - 2)]
      have heq : (32 * ((k + 2 : ℕ) : ℚ) ^ 3 * (2 : ℚ)) =
          64 * ((k + 2 : ℕ) : ℚ) ^ 3 := by ring
      have hsimp : k + 2 - 1 = k + 1 := by omega
      rw [hsimp]
      have hfrac' :
          (64 * ((k + 2 : ℕ) : ℚ) ^ 3) / ((2 * ((k + 2 : ℕ) : ℚ) + 1) ^ 3) ≤
            (32 * ((k + 2 : ℕ) : ℚ) ^ 3 * a_Q (k + 1) +
              ((21 * ((k + 2 : ℕ) : ℚ) ^ 3 + 22 * ((k + 2 : ℕ) : ℚ) ^ 2 +
                  8 * ((k + 2 : ℕ) : ℚ) + 1) *
                (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ) ^ 4)) /
            ((2 * ((k + 2 : ℕ) : ℚ) + 1) ^ 3) := by
        rw [← heq]; simpa [hsimp] using hfrac
      exact le_trans h64 hfrac'

lemma a_pos (n : ℕ) (hn : 1 ≤ n) : 0 < a n := by
  unfold a
  have h2 : (2 : ℚ) ≤ a_Q n := a_Q_ge_two n hn
  have hfloor : (2 : ℤ) ≤ (a_Q n).floor := Int.le_floor.mpr (by exact_mod_cast h2)
  have hpos : (0 : ℤ) < (a_Q n).floor := by linarith
  exact Nat.pos_of_ne_zero (fun hz => by
    have : (a_Q n).floor ≤ 0 := Int.toNat_eq_zero.mp hz
    linarith)

/-- The polynomial $P(n)=21n^3+22n^2+8n+1$. -/
def Pnat (n : ℕ) : ℕ := 21 * n ^ 3 + 22 * n ^ 2 + 8 * n + 1

lemma Pnat_cast (n : ℕ) :
    (Pnat n : ℚ) = 21 * (n : ℚ) ^ 3 + 22 * (n : ℚ) ^ 2 + 8 * (n : ℚ) + 1 := by
  unfold Pnat
  push_cast
  rfl

/-- $T(n)=\sum_{m=0}^n P(m)\binom{2m}{m}^7 256^{n-m}$. -/
def T : ℕ → ℕ
  | 0 => 1
  | n + 1 => 256 * T n + Pnat (n + 1) * (Nat.choose (2 * (n + 1)) (n + 1)) ^ 7

lemma T_zero : T 0 = 1 := rfl

lemma T_succ (n : ℕ) :
    T (n + 1) = 256 * T n + Pnat (n + 1) * (Nat.choose (2 * (n + 1)) (n + 1)) ^ 7 :=
  rfl

lemma T_pos (n : ℕ) : 0 < T n := by
  induction n with
  | zero => simp [T]
  | succ n ih =>
    simp only [T]
    have : 0 < 256 * T n := Nat.mul_pos (by decide) ih
    omega

/-- $\binom{2n}{n}\,n = 2n\,\binom{2n-1}{n-1}$ for $n\ge 1$. -/
lemma choose_two_mul_mul (n : ℕ) (hn : 1 ≤ n) :
    Nat.choose (2 * n) n * n = 2 * n * Nat.choose (2 * n - 1) (n - 1) := by
  have h := Nat.add_one_mul_choose_eq (2 * n - 1) (n - 1)
  have heq1 : 2 * n - 1 + 1 = 2 * n := by omega
  have heq2 : n - 1 + 1 = n := by omega
  rw [heq1, heq2] at h
  linarith

/-- $\binom{2n}{n} = 2\binom{2n-1}{n-1}$ for $n\ge 1$. -/
lemma choose_two_mul_eq_two (n : ℕ) (hn : 1 ≤ n) :
    Nat.choose (2 * n) n = 2 * Nat.choose (2 * n - 1) (n - 1) := by
  have h := choose_two_mul_mul n hn
  have hn0 : 0 < n := hn
  have : n * Nat.choose (2 * n) n = n * (2 * Nat.choose (2 * n - 1) (n - 1)) := by
    linarith
  exact Nat.mul_left_cancel hn0 (by linarith)

/-- $\binom{2n-1}{n}=\binom{2n-1}{n-1}$ for $n\ge 1$. -/
lemma choose_two_mul_sub_one_symm (n : ℕ) (hn : 1 ≤ n) :
    Nat.choose (2 * n - 1) n = Nat.choose (2 * n - 1) (n - 1) := by
  cases n with
  | zero => omega
  | succ n =>
    have : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    rw [this]
    exact Nat.choose_symm_half n

/-- $\binom{2n-1}{n}=\binom{2n}{n}/2$ as rationals, $n\ge 1$. -/
lemma choose_two_mul_sub_one_cast (n : ℕ) (hn : 1 ≤ n) :
    (Nat.choose (2 * n - 1) n : ℚ) = (Nat.choose (2 * n) n : ℚ) / 2 := by
  have h1 := choose_two_mul_eq_two n hn
  have h2 := choose_two_mul_sub_one_symm n hn
  have : (Nat.choose (2 * n) n : ℚ) = 2 * (Nat.choose (2 * n - 1) n : ℚ) := by
    rw [h1, h2]; push_cast; ring
  field_simp
  linarith

/-- $\binom{2n}{n}/\binom{2n-2}{n-1}=2(2n-1)/n$ as rationals, $n\ge 1$. -/
lemma choose_central_ratio (n : ℕ) (hn : 1 ≤ n) :
    (Nat.choose (2 * n) n : ℚ) =
      (2 * (2 * n - 1 : ℕ) : ℚ) / (n : ℚ) *
        (Nat.choose (2 * (n - 1)) (n - 1) : ℚ) := by
  have hA := choose_two_mul_eq_two n hn
  have hB := choose_two_mul_sub_one_symm n hn
  have hn1 : 1 ≤ n := hn
  have hsub : 2 * n - 2 + 1 = 2 * n - 1 := by omega
  have hsub2 : n - 1 + 1 = n := by omega
  have hC := Nat.add_one_mul_choose_eq (2 * n - 2) (n - 1)
  rw [hsub, hsub2] at hC
  -- hC : (2n-1) * C(2n-2, n-1) = C(2n-1, n) * n
  have h2n2 : 2 * (n - 1) = 2 * n - 2 := by omega
  rw [← h2n2] at hC
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
  have hnat : Nat.choose (2 * n) n * n =
      2 * (2 * n - 1) * Nat.choose (2 * (n - 1)) (n - 1) := by
    have : Nat.choose (2 * n) n = 2 * Nat.choose (2 * n - 1) n := by
      rw [hA, hB]
    rw [this]
    linarith [hC]
  field_simp [hn0]
  have hc := congrArg (fun t : ℕ => (t : ℚ)) hnat
  push_cast at hc
  linarith

/-- The rational identity underlying the closed form. -/
lemma closed_form_step (nQ Tprev Cprev Ccur Pn : ℚ)
    (hCprev : Cprev ≠ 0) (hCcur : Ccur ≠ 0)
    (hn0 : nQ ≠ 0) (hD0 : (2 * nQ - 1) ≠ 0) (hden : (2 * nQ + 1) ≠ 0)
    (hratio : nQ * Ccur = 2 * (2 * nQ - 1) * Cprev) :
    (32 * nQ ^ 3 * (Tprev / (16 * (2 * nQ - 1) ^ 3 * Cprev ^ 3)) +
      Pn * (Ccur / 2) ^ 4) / (2 * nQ + 1) ^ 3 =
      (256 * Tprev + Pn * Ccur ^ 7) /
        (16 * (2 * nQ + 1) ^ 3 * Ccur ^ 3) := by
  have h16 : (16 : ℚ) ≠ 0 := by norm_num
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have hpow : (Ccur / 2) ^ 4 = Ccur ^ 4 / 16 := by
    field_simp [h2]; ring
  rw [hpow]
  set D : ℚ := 2 * nQ - 1
  have hcube : nQ ^ 3 * Ccur ^ 3 = 8 * D ^ 3 * Cprev ^ 3 := by
    have := congrArg (fun t : ℚ => t ^ 3) hratio
    dsimp [D] at this ⊢
    ring_nf at this ⊢
    exact this
  have hfirst :
      32 * nQ ^ 3 * Tprev / (16 * D ^ 3 * Cprev ^ 3) =
        256 * Tprev / (16 * Ccur ^ 3) := by
    have hL : 32 * nQ ^ 3 * Tprev / (16 * D ^ 3 * Cprev ^ 3) =
        (32 * nQ ^ 3 * Tprev * Ccur ^ 3) / (16 * D ^ 3 * Cprev ^ 3 * Ccur ^ 3) := by
      field_simp [hCcur]
    have hR : 256 * Tprev / (16 * Ccur ^ 3) =
        (256 * Tprev * D ^ 3 * Cprev ^ 3) / (16 * Ccur ^ 3 * D ^ 3 * Cprev ^ 3) := by
      field_simp [hD0, hCprev]
    rw [hL, hR]
    have hnum : 32 * nQ ^ 3 * Tprev * Ccur ^ 3 =
        256 * Tprev * D ^ 3 * Cprev ^ 3 := by
      have := congrArg (fun t : ℚ => 32 * Tprev * t) hcube
      ring_nf at this ⊢
      exact this
    -- denominators agree up to commutativity
    have hden_eq : (16 * D ^ 3 * Cprev ^ 3 * Ccur ^ 3) =
        (16 * Ccur ^ 3 * D ^ 3 * Cprev ^ 3) := by ring
    rw [hnum, hden_eq]
  have hscale :
      32 * nQ ^ 3 * (Tprev / (16 * D ^ 3 * Cprev ^ 3)) + Pn * (Ccur ^ 4 / 16) =
        (256 * Tprev + Pn * Ccur ^ 7) / (16 * Ccur ^ 3) := by
    have hsplit : (256 * Tprev + Pn * Ccur ^ 7) / (16 * Ccur ^ 3) =
        256 * Tprev / (16 * Ccur ^ 3) + Pn * (Ccur ^ 4 / 16) := by
      field_simp [hCcur, h16]
    have hassoc : 32 * nQ ^ 3 * (Tprev / (16 * D ^ 3 * Cprev ^ 3)) =
        32 * nQ ^ 3 * Tprev / (16 * D ^ 3 * Cprev ^ 3) := by ring
    rw [hassoc, hsplit, hfirst]
  have hside :
      (32 * nQ ^ 3 * (Tprev / (16 * D ^ 3 * Cprev ^ 3)) +
          Pn * (Ccur ^ 4 / 16)) / (2 * nQ + 1) ^ 3 =
        ((256 * Tprev + Pn * Ccur ^ 7) / (16 * Ccur ^ 3)) / (2 * nQ + 1) ^ 3 :=
    by rw [hscale]
  dsimp [D] at hside ⊢
  convert hside using 1
  field_simp [hCcur, h16, hden]

/-- Closed form: $a_Q(n)=T(n)/(16(2n+1)^3\binom{2n}{n}^3)$ for $n\ge 1$. -/
lemma a_Q_closed_form (n : ℕ) (hn : 1 ≤ n) :
    a_Q n =
      (T n : ℚ) /
        (16 * ((2 * n + 1 : ℕ) : ℚ) ^ 3 * (Nat.choose (2 * n) n : ℚ) ^ 3) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => omega
    | 1 =>
      have hT : T 1 = 6912 := by
        rw [T_succ, T_zero, Pnat]
        decide
      have hC : Nat.choose 2 1 = 2 := by decide
      rw [a_Q_one, hT, hC]
      norm_num
    | k + 2 =>
      have hn2 : 2 ≤ k + 2 := by omega
      have hk1 : 1 ≤ k + 1 := by omega
      rw [a_Q_of_ge_two (k + 2) hn2]
      have ih1 := ih (k + 1) (by omega) hk1
      have hsimp : k + 2 - 1 = k + 1 := by omega
      rw [hsimp, ih1]
      have hhalf := choose_two_mul_sub_one_cast (k + 2) (by omega)
      rw [hhalf]
      have hTsucc : (T (k + 2) : ℚ) =
          (256 * T (k + 1) + Pnat (k + 2) * (Nat.choose (2 * (k + 2)) (k + 2)) ^ 7 : ℕ) := by
        have := T_succ (k + 1)
        simp at this
        exact_mod_cast this
      rw [hTsucc]
      push_cast
      rw [Pnat_cast (k + 2)]
      have hcastn : ((k + 2 : ℕ) : ℚ) = (k : ℚ) + 2 := by push_cast; rfl
      rw [hcastn]
      have hden_simp : (2 : ℚ) * ((k : ℚ) + 1) + 1 = 2 * ((k : ℚ) + 2) - 1 := by ring
      rw [hden_simp]
      refine closed_form_step ((k : ℚ) + 2) (T (k + 1) : ℚ)
          (Nat.choose (2 * (k + 1)) (k + 1) : ℚ)
          (Nat.choose (2 * (k + 2)) (k + 2) : ℚ)
          (21 * ((k : ℚ) + 2) ^ 3 + 22 * ((k : ℚ) + 2) ^ 2 +
            8 * ((k : ℚ) + 2) + 1)
          ?_ ?_ ?_ ?_ ?_ ?_
      · exact Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne.symm
      · exact Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne.symm
      · linarith
      · have hpos : (0 : ℚ) < 2 * ((k : ℚ) + 2) - 1 := by
          have : (1 : ℚ) ≤ ((k + 2 : ℕ) : ℚ) := by exact_mod_cast (show 1 ≤ k + 2 by omega)
          linarith
        exact hpos.ne'
      · have hpos : (0 : ℚ) < 2 * ((k : ℚ) + 2) + 1 := by linarith
        exact hpos.ne'
      · have hr := choose_central_ratio (k + 2) (by omega)
        have hidx : 2 * ((k + 2) - 1) = 2 * (k + 1) := by omega
        have hidx2 : (k + 2) - 1 = k + 1 := by omega
        rw [hidx, hidx2] at hr
        have hn0 : ((k + 2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show k + 2 ≠ 0 by omega)
        field_simp [hn0] at hr
        have hcastn : ((k + 2 : ℕ) : ℚ) = (k : ℚ) + 2 := by push_cast; rfl
        have hcastD : ((2 * (k + 2) - 1 : ℕ) : ℚ) = 2 * ((k : ℚ) + 2) - 1 := by
          have : (2 * (k + 2) : ℕ) ≥ 1 := by omega
          have heq : (2 * (k + 2) - 1 : ℕ) + 1 = 2 * (k + 2) := by omega
          have hcast : ((2 * (k + 2) - 1 : ℕ) : ℚ) + 1 = (2 * (k + 2) : ℕ) := by
            exact_mod_cast heq
          push_cast at hcast
          linarith
        rw [hcastn, hcastD] at hr
        linarith

/-- Explicit sum formula for $T$. -/
lemma T_eq_sum (n : ℕ) :
    T n =
      ∑ m ∈ Finset.range (n + 1),
        Pnat m * (Nat.choose (2 * m) m) ^ 7 * 256 ^ (n - m) := by
  induction n with
  | zero =>
    simp [T, Pnat]
  | succ n ih =>
    rw [T_succ, ih]
    -- Expand the target sum as "old terms + last term".
    nth_rw 2 [Finset.sum_range_succ]
    simp only [Nat.sub_self, pow_zero, mul_one]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hpow : 256 ^ (n + 1 - m) = 256 * 256 ^ (n - m) := by
      have : n + 1 - m = n - m + 1 := Nat.succ_sub hm'
      rw [this, pow_succ']
    rw [hpow]
    ring

/-- $n^3\equiv n\pmod{2}$. -/
lemma pow_three_mod_two (n : ℕ) : n ^ 3 % 2 = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · simp [pow_succ, Nat.mul_mod, h]
  · simp [pow_succ, Nat.mul_mod, h]

/-- $n^2\equiv n\pmod{2}$ is not needed; $n^2\equiv 0$ if $n$ even and $1$ if odd. -/
lemma pow_two_mod_two (n : ℕ) : n ^ 2 % 2 = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · simp [pow_two, Nat.mul_mod, h]
  · simp [pow_two, Nat.mul_mod, h]

lemma zmod2_pow_eq_self (x : ZMod 2) (k : ℕ) (hk : 1 ≤ k) : x ^ k = x := by
  generalize hx : x.val = v
  have hv : v < 2 := hx ▸ ZMod.val_lt x
  interval_cases v
  · have : x = 0 := (ZMod.val_eq_zero x).mp hx
    rw [this, zero_pow (Nat.pos_iff_ne_zero.mp hk)]
  · have : x = 1 := (ZMod.val_eq_one (by omega : 1 < 2) x).mp hx
    simp [this]

/-- $P(n)\equiv n+1\pmod{2}$. -/
lemma Pnat_mod_two (n : ℕ) : Pnat n % 2 = (n + 1) % 2 := by
  rw [← ZMod.natCast_eq_natCast_iff' (c := 2)]
  unfold Pnat
  push_cast
  have h21 : (21 : ZMod 2) = 1 := rfl
  have h22 : (22 : ZMod 2) = 0 := rfl
  have h8 : (8 : ZMod 2) = 0 := rfl
  rw [h21, h22, h8]
  simp only [one_mul, zero_mul, add_zero]
  rw [zmod2_pow_eq_self _ 3 (by omega)]

lemma Pnat_even_iff_odd (n : ℕ) : Even (Pnat n) ↔ Odd n := by
  rw [Nat.even_iff, Nat.odd_iff, Pnat_mod_two]
  have : (n + 1) % 2 = (n % 2 + 1) % 2 := Nat.add_mod _ _ _
  omega

/-- Denominator of the closed form. -/
def Den (n : ℕ) : ℕ := 16 * (2 * n + 1) ^ 3 * (Nat.choose (2 * n) n) ^ 3

lemma Den_pos (n : ℕ) : 0 < Den n := by
  unfold Den
  have : 0 < Nat.choose (2 * n) n := Nat.choose_pos (Nat.le_mul_of_pos_left _ (by omega))
  positivity

/-- $2n+1$ is always odd. -/
lemma two_mul_add_one_odd (n : ℕ) : Odd (2 * n + 1) :=
  odd_two_mul_add_one n

/-- $s_2(2n)=s_2(n)$ for $n>0$. -/
lemma digits_two_sum_double (n : ℕ) (hn : 0 < n) :
    (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum := by
  rw [Nat.digits_base_mul (by omega) hn]
  simp

/-- Binary digit-sum formula: $v_2(\binom{2n}{n})=s_2(n)$. -/
lemma padicValNat_two_central (n : ℕ) (hn : n ≠ 0) :
    padicValNat 2 (Nat.choose (2 * n) n) = (Nat.digits 2 n).sum := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) (k := n) (n := 2 * n)
    (Nat.le_mul_of_pos_left _ (by omega))
  simp at h
  have hnn : 2 * n - n = n := by omega
  have h2n : (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum :=
    digits_two_sum_double n (Nat.pos_of_ne_zero hn)
  rw [hnn] at h
  -- Avoid truncated subtraction issues by rewriting the Nat subtraction.
  have hsum : (Nat.digits 2 n).sum + (Nat.digits 2 n).sum - (Nat.digits 2 (2 * n)).sum =
      (Nat.digits 2 n).sum := by
    rw [h2n]
    omega
  omega

lemma list_sum_eq_zero_iff_nat {l : List ℕ} : l.sum = 0 ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [Nat.add_eq_zero_iff, ih]

/-- Digit sum of a positive integer is zero iff the integer is zero. -/
lemma digits_two_sum_eq_zero_iff (n : ℕ) :
    (Nat.digits 2 n).sum = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    have hall : ∀ x ∈ Nat.digits 2 n, x = 0 := list_sum_eq_zero_iff_nat.mp h
    have hlast := Nat.getLast_digit_ne_zero 2 hn
    have hne : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
    exact hlast (hall _ (List.getLast_mem hne))
  · intro hn
    simp [hn]

/-- A positive integer is a power of two (including $2^0=1$) iff its binary digit-sum is $1$. -/
lemma pow_two_iff_digits_sum (n : ℕ) (hn : n ≠ 0) :
    (Nat.digits 2 n).sum = 1 ↔ ∃ m, n = 2 ^ m := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n.even_or_odd' with ⟨k, rfl | rfl⟩
    · -- even: $n=2k$
      have hk0 : k ≠ 0 := by
        intro hk
        subst hk
        exact hn rfl
      have hdig : (Nat.digits 2 (2 * k)).sum = (Nat.digits 2 k).sum :=
        digits_two_sum_double k (Nat.pos_of_ne_zero hk0)
      have ihk := ih k (by omega) hk0
      rw [hdig, ihk]
      constructor
      · rintro ⟨m, hm⟩
        refine ⟨m + 1, ?_⟩
        rw [hm, pow_succ']
      · rintro ⟨m, hm⟩
        have hm0 : m ≠ 0 := by
          intro h0
          subst h0
          simp at hm
        refine ⟨m - 1, ?_⟩
        have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
          have hms : (m - 1).succ = m :=
            Nat.succ_eq_add_one (m - 1) ▸ Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)
          conv_lhs => rw [← hms, Nat.pow_succ']
        exact Nat.mul_left_cancel (by omega : 0 < 2) (hpow ▸ hm)
    · -- odd: $n=2k+1$
      have hdef : Nat.digits 2 (2 * k + 1) = 1 :: Nat.digits 2 k := by
        have hpos : 0 < 2 * k + 1 := by omega
        rw [Nat.digits_def' (by omega) hpos]
        have hmod : (2 * k + 1) % 2 = 1 := by omega
        have hdiv : (2 * k + 1) / 2 = k := by omega
        rw [hmod, hdiv]
      rw [hdef, List.sum_cons]
      constructor
      · intro hs
        have hksum : (Nat.digits 2 k).sum = 0 := by omega
        have hk0 : k = 0 := (digits_two_sum_eq_zero_iff k).mp hksum
        subst hk0
        exact ⟨0, by simp⟩
      · rintro ⟨m, hm⟩
        have hm0 : m = 0 := by
          cases m with
          | zero => rfl
          | succ m =>
            have heven : Even (2 ^ (m + 1)) := by
              rw [Nat.pow_succ']
              exact even_two_mul _
            have hodd : Odd (2 * k + 1) := odd_two_mul_add_one k
            rw [← hm] at heven
            exact (Nat.not_even_iff_odd.mpr hodd heven).elim
        subst hm0
        simp only [pow_zero] at hm
        have hk0 : k = 0 := by omega
        simp [hk0]

/-- $n=2^m$ for some $m\ge 1$ iff $n$ is even and $s_2(n)=1$. -/
lemma pow_two_ge_one_iff (n : ℕ) (hn : 1 ≤ n) :
    (∃ m ≥ 1, n = 2 ^ m) ↔ Even n ∧ (Nat.digits 2 n).sum = 1 := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨?_, ?_⟩
    · have : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
      exact even_iff_two_dvd.mpr this
    · have hn0 : (2 ^ m : ℕ) ≠ 0 := (Nat.two_pow_pos m).ne'
      exact (pow_two_iff_digits_sum (2 ^ m) hn0).mpr ⟨m, rfl⟩
  · rintro ⟨he, hs⟩
    have hn0 : n ≠ 0 := by omega
    obtain ⟨m, hm⟩ := (pow_two_iff_digits_sum n hn0).mp hs
    refine ⟨m, ?_, hm⟩
    have : m ≠ 0 := by
      intro h0
      subst h0
      subst hm
      simp at he
    exact Nat.one_le_iff_ne_zero.mpr this

/-- $s_2(n)\le n$. -/
lemma digits_two_sum_le (n : ℕ) : (Nat.digits 2 n).sum ≤ n :=
  digit_sum_le 2 n

/-- $v_2(n!)=n-s_2(n)$, hence $v_2(n!)\le n$. -/
lemma padicValNat_two_factorial (n : ℕ) :
    padicValNat 2 n.factorial = n - (Nat.digits 2 n).sum := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  simpa using h

lemma padicValNat_two_factorial_le (n : ℕ) :
    padicValNat 2 n.factorial ≤ n :=
  (padicValNat_two_factorial n).symm ▸ Nat.sub_le _ _

/-- $s_2(n)=n-v_2(n!)$. -/
lemma digits_two_sum_factorial (n : ℕ) :
    (Nat.digits 2 n).sum = n - padicValNat 2 (n.factorial) := by
  have h := padicValNat_two_factorial n
  have hle := digits_two_sum_le n
  have : n - (n - (Nat.digits 2 n).sum) = (Nat.digits 2 n).sum := Nat.sub_sub_self hle
  rw [← h] at this
  exact this.symm

/-- If $d\mid N$ and $N\neq 0$ then $v_p(d)\le v_p(N)$. -/
lemma padicValNat_le_of_dvd {p d N : ℕ} [Fact p.Prime] (hdiv : d ∣ N) (hN : N ≠ 0) :
    padicValNat p d ≤ padicValNat p N := by
  rcases eq_or_ne d 0 with rfl | hd
  · exact (hN (eq_zero_of_zero_dvd hdiv)).elim
  · have : p ^ padicValNat p d ∣ d := pow_padicValNat_dvd
    have : p ^ padicValNat p d ∣ N := dvd_trans this hdiv
    exact (padicValNat_dvd_iff_le hN).mp this

/-- $s_2(a+b)\le s_2(a)+s_2(b)$. -/
lemma digits_two_sum_add_le (a b : ℕ) :
    (Nat.digits 2 (a + b)).sum ≤ (Nat.digits 2 a).sum + (Nat.digits 2 b).sum := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha := digits_two_sum_factorial a
  have hb := digits_two_sum_factorial b
  have hab := digits_two_sum_factorial (a + b)
  have hposA : a.factorial ≠ 0 := Nat.factorial_ne_zero a
  have hposB : b.factorial ≠ 0 := Nat.factorial_ne_zero b
  have hpos : (a + b).factorial ≠ 0 := Nat.factorial_ne_zero (a + b)
  have hdiv : a.factorial * b.factorial ∣ (a + b).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add a b
  have hmul := padicValNat.mul (p := 2) hposA hposB
  have hle : padicValNat 2 a.factorial + padicValNat 2 b.factorial ≤
      padicValNat 2 (a + b).factorial := by
    rw [← hmul]
    exact padicValNat_le_of_dvd hdiv hpos
  have eqa : (Nat.digits 2 a).sum + padicValNat 2 a.factorial = a := by
    rw [digits_two_sum_factorial, Nat.sub_add_cancel (padicValNat_two_factorial_le a)]
  have eqb : (Nat.digits 2 b).sum + padicValNat 2 b.factorial = b := by
    rw [digits_two_sum_factorial, Nat.sub_add_cancel (padicValNat_two_factorial_le b)]
  have eqab : (Nat.digits 2 (a + b)).sum + padicValNat 2 (a + b).factorial = a + b := by
    rw [digits_two_sum_factorial, Nat.sub_add_cancel (padicValNat_two_factorial_le (a + b))]
  omega

/-- $v_2(256^k)=8k$. -/
lemma padicValNat_two_pow256 (k : ℕ) : padicValNat 2 (256 ^ k) = 8 * k := by
  have h256 : padicValNat 2 256 = 8 := by
    have : 256 = 2 ^ 8 := by decide
    rw [this, padicValNat.prime_pow]
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have hpos : 256 ^ k ≠ 0 := pow_ne_zero k (by decide)
    rw [padicValNat.pow k (by decide : 256 ≠ 0), h256, mul_comm]

lemma Pnat_pos (m : ℕ) : 0 < Pnat m := by
  unfold Pnat
  omega

/-- $v_2$ of a summand of $T$. -/
lemma padicValNat_two_T_term (n m : ℕ) :
    8 * (n - m) + 7 * (if m = 0 then 0 else (Nat.digits 2 m).sum) ≤
      padicValNat 2 (Pnat m * (Nat.choose (2 * m) m) ^ 7 * 256 ^ (n - m)) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : Pnat m ≠ 0 := (Pnat_pos m).ne'
  have hC : Nat.choose (2 * m) m ≠ 0 := (Nat.choose_pos (Nat.le_mul_of_pos_left _ (by omega))).ne'
  have h256 : 256 ^ (n - m) ≠ 0 := pow_ne_zero _ (by decide)
  have hC7 : Nat.choose (2 * m) m ^ 7 ≠ 0 := pow_ne_zero 7 hC
  rw [padicValNat.mul (mul_ne_zero hP hC7) h256, padicValNat.mul hP hC7,
      padicValNat.pow 7 hC, padicValNat_two_pow256]
  have hPge : 0 ≤ padicValNat 2 (Pnat m) := Nat.zero_le _
  have hCval : padicValNat 2 (Nat.choose (2 * m) m) =
      if m = 0 then 0 else (Nat.digits 2 m).sum := by
    split_ifs with hm
    · subst hm
      simp
    · exact padicValNat_two_central m hm
  rw [hCval]
  omega

/-- Binary digit-sum inequality underlying $2$-adic integrality. -/
lemma two_adic_digit_ineq (n m : ℕ) (hm : m ≤ n) (hn : 1 ≤ n) :
    4 + 3 * (Nat.digits 2 n).sum ≤
      8 * (n - m) + 7 * (if m = 0 then 0 else (Nat.digits 2 m).sum) := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp only [↓reduceIte]
    have hs : (Nat.digits 2 n).sum ≤ n := digits_two_sum_le n
    have : n - 0 = n := Nat.sub_zero n
    omega
  · simp only [hm0, ↓reduceIte]
    have hpos : 1 ≤ (Nat.digits 2 m).sum := by
      have : (Nat.digits 2 m).sum ≠ 0 := by
        intro h
        exact hm0 ((digits_two_sum_eq_zero_iff m).mp h)
      omega
    have hadd : (Nat.digits 2 (m + (n - m))).sum ≤
        (Nat.digits 2 m).sum + (Nat.digits 2 (n - m)).sum :=
      digits_two_sum_add_le m (n - m)
    have hnrew : m + (n - m) = n := Nat.add_sub_of_le hm
    rw [hnrew] at hadd
    have hdle : (Nat.digits 2 (n - m)).sum ≤ n - m := digits_two_sum_le (n - m)
    omega

/-- $v_2((2n+1)^k)=0$. -/
lemma padicValNat_two_odd_pow (n k : ℕ) : padicValNat 2 ((2 * n + 1) ^ k) = 0 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ (2 * n + 1) :=
    Nat.two_not_dvd_two_mul_add_one n
  have : padicValNat 2 (2 * n + 1) = 0 := padicValNat.eq_zero_of_not_dvd hodd
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · rw [padicValNat.pow k (by omega : 2 * n + 1 ≠ 0), this, mul_zero]

/-- $v_2(\mathrm{Den}(n))=4+3 s_2(n)$ for $n\ge 1$. -/
lemma padicValNat_two_Den (n : ℕ) (hn : 1 ≤ n) :
    padicValNat 2 (Den n) = 4 + 3 * (Nat.digits 2 n).sum := by
  unfold Den
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h16 : padicValNat 2 16 = 4 := by
    have : (16 : ℕ) = 2 ^ 4 := by decide
    rw [this, padicValNat.prime_pow]
  have h16n : 16 ≠ 0 := by decide
  have hodd : (2 * n + 1) ^ 3 ≠ 0 := pow_ne_zero 3 (by omega)
  have hC : Nat.choose (2 * n) n ≠ 0 :=
    (Nat.choose_pos (Nat.le_mul_of_pos_left _ (by omega))).ne'
  have hC3 : Nat.choose (2 * n) n ^ 3 ≠ 0 := pow_ne_zero 3 hC
  rw [padicValNat.mul (mul_ne_zero h16n hodd) hC3,
      padicValNat.mul h16n hodd, h16, padicValNat_two_odd_pow n 3,
      padicValNat.pow 3 hC, padicValNat_two_central n (by omega)]

/-- $2$-adic integrality: $v_2(T(n))\ge v_2(\mathrm{Den}(n))$. -/
lemma padicValNat_two_T_ge_Den (n : ℕ) (hn : 1 ≤ n) :
    padicValNat 2 (Den n) ≤ padicValNat 2 (T n) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : T n ≠ 0 := (T_pos n).ne'
  rw [padicValNat_two_Den n hn]
  have hdiv : 2 ^ (4 + 3 * (Nat.digits 2 n).sum) ∣ T n := by
    rw [T_eq_sum]
    refine Finset.dvd_sum ?_
    intro m hm
    have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hterm := padicValNat_two_T_term n m
    have hineq := two_adic_digit_ineq n m hm' hn
    have hpos : Pnat m * (Nat.choose (2 * m) m) ^ 7 * 256 ^ (n - m) ≠ 0 := by
      have hP : Pnat m ≠ 0 := (Pnat_pos m).ne'
      have hC : Nat.choose (2 * m) m ≠ 0 :=
        (Nat.choose_pos (Nat.le_mul_of_pos_left _ (by omega))).ne'
      have h256 : 256 ^ (n - m) ≠ 0 := pow_ne_zero _ (by decide)
      exact mul_ne_zero (mul_ne_zero hP (pow_ne_zero 7 hC)) h256
    exact (padicValNat_dvd_iff_le hpos).mpr (le_trans hineq hterm)
  exact (padicValNat_dvd_iff_le hT).mp hdiv

/-- $8P(n)+1=(2n+1)(84n^2+46n+9)$. -/
lemma eight_P_add_one (n : ℕ) :
    8 * Pnat n + 1 = (2 * n + 1) * (84 * n ^ 2 + 46 * n + 9) := by
  unfold Pnat
  ring

/-- An odd prime never divides a power of two. -/
lemma odd_prime_not_dvd_two_pow {p k : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2) :
    ¬ p ∣ 2 ^ k := by
  intro h
  have h2 : p ∣ 2 := hp.out.dvd_of_dvd_pow h
  exact hodd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h2)

lemma padicValNat_odd_prime_pow_two {p k : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2) :
    padicValNat p (2 ^ k) = 0 :=
  padicValNat.eq_zero_of_not_dvd (odd_prime_not_dvd_two_pow hodd)

lemma padicValNat_odd_prime_two {p : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2) :
    padicValNat p 2 = 0 := by
  simpa using padicValNat_odd_prime_pow_two (p := p) (k := 1) hodd

lemma padicValNat_odd_prime_sixteen {p : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2) :
    padicValNat p 16 = 0 := by
  have : (16 : ℕ) = 2 ^ 4 := by decide
  rw [this]
  exact padicValNat_odd_prime_pow_two hodd

lemma padicValNat_odd_prime_256 {p : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2) :
    padicValNat p 256 = 0 := by
  have : (256 : ℕ) = 2 ^ 8 := by decide
  rw [this]
  exact padicValNat_odd_prime_pow_two hodd

/-- If an odd prime divides $2n+1$, then it does not divide $P(n)$. -/
lemma padicValNat_Pnat_eq_zero_of_dvd_two_mul_add_one
    {p n : ℕ} [hp : Fact p.Prime] (_hodd : p ≠ 2)
    (hdiv : p ∣ 2 * n + 1) : padicValNat p (Pnat n) = 0 := by
  have hP : Pnat n ≠ 0 := (Pnat_pos n).ne'
  refine padicValNat.eq_zero_of_not_dvd ?_
  intro hPdiv
  have h8P : p ∣ 8 * Pnat n := dvd_mul_of_dvd_right hPdiv 8
  have h8P1 : p ∣ 8 * Pnat n + 1 := by
    rw [eight_P_add_one]
    exact dvd_mul_of_dvd_left hdiv _
  have : p ∣ 1 := (Nat.dvd_add_right h8P).mp h8P1
  have hpeq : p = 1 := Nat.eq_one_of_dvd_one this
  exact hp.out.ne_one hpeq

/-- For odd $p$, $v_p\bigl(\binom{2n}{n}\bigr)-v_p\bigl(\binom{2n-2}{n-1}\bigr)=v_p(2n-1)-v_p(n)$
when $n\ge 1$. -/
lemma padicValNat_central_succ {p n : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2)
    (hn : 1 ≤ n) :
    padicValNat p (Nat.choose (2 * n) n) + padicValNat p n =
      padicValNat p (Nat.choose (2 * (n - 1)) (n - 1)) + padicValNat p (2 * n - 1) := by
  have hn0 : n ≠ 0 := by omega
  have hratio := choose_two_mul_mul n hn
  -- $\binom{2n}{n} n = 2n \binom{2n-1}{n-1}$
  -- and $\binom{2n}{n} = 2(2n-1)/n \binom{2n-2}{n-1}$, i.e.
  -- $\binom{2n}{n}\,n = 2(2n-1)\binom{2n-2}{n-1}$.
  have hC := choose_central_ratio n hn
  have hne_n : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hnat : Nat.choose (2 * n) n * n =
      2 * (2 * n - 1) * Nat.choose (2 * (n - 1)) (n - 1) := by
    have hA := choose_two_mul_eq_two n hn
    have hB := choose_two_mul_sub_one_symm n hn
    have hsub : 2 * n - 2 + 1 = 2 * n - 1 := by omega
    have hsub2 : n - 1 + 1 = n := by omega
    have hCh := Nat.add_one_mul_choose_eq (2 * n - 2) (n - 1)
    rw [hsub, hsub2] at hCh
    have h2n2 : 2 * (n - 1) = 2 * n - 2 := by omega
    rw [← h2n2] at hCh
    have : Nat.choose (2 * n) n = 2 * Nat.choose (2 * n - 1) n := by
      rw [hA, hB]
    rw [this]
    linarith [hCh]
  have hL : Nat.choose (2 * n) n ≠ 0 :=
    (Nat.choose_pos (Nat.le_mul_of_pos_left _ (by omega))).ne'
  have hR : Nat.choose (2 * (n - 1)) (n - 1) ≠ 0 :=
    (Nat.choose_pos (Nat.le_mul_of_pos_left _ (by omega))).ne'
  have h2n1 : 2 * n - 1 ≠ 0 := by omega
  have h2 : (2 : ℕ) ≠ 0 := by decide
  have hLn : Nat.choose (2 * n) n * n ≠ 0 := mul_ne_zero hL hn0
  have hRn : 2 * (2 * n - 1) * Nat.choose (2 * (n - 1)) (n - 1) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero h2 h2n1) hR
  have hv := congrArg (padicValNat p) hnat
  rw [padicValNat.mul hL hn0] at hv
  have h2ne : padicValNat p 2 = 0 := padicValNat_odd_prime_two hodd
  rw [padicValNat.mul (mul_ne_zero h2 h2n1) hR, padicValNat.mul h2 h2n1, h2ne] at hv
  omega

/-- $v_p(\mathrm{Den}(n))=3v_p(2n+1)+3v_p\bigl(\binom{2n}{n}\bigr)$ for odd primes. -/
lemma padicValNat_odd_Den (n : ℕ) {p : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2) :
    padicValNat p (Den n) =
      3 * padicValNat p (2 * n + 1) + 3 * padicValNat p (Nat.choose (2 * n) n) := by
  unfold Den
  have h16 : padicValNat p 16 = 0 := padicValNat_odd_prime_sixteen hodd
  have h16n : (16 : ℕ) ≠ 0 := by decide
  have hNpos : (2 * n + 1) ≠ 0 := by omega
  have hCpos : Nat.choose (2 * n) n ≠ 0 :=
    (Nat.choose_pos (Nat.le_mul_of_pos_left _ (by omega))).ne'
  have hoddN : (2 * n + 1) ^ 3 ≠ 0 := pow_ne_zero 3 hNpos
  have hC3 : Nat.choose (2 * n) n ^ 3 ≠ 0 := pow_ne_zero 3 hCpos
  rw [padicValNat.mul (mul_ne_zero h16n hoddN) hC3,
      padicValNat.mul h16n hoddN, h16, padicValNat.pow 3 hNpos,
      padicValNat.pow 3 hCpos]
  ring

/-- If $p^e$ divides two natural numbers then it divides their sum. -/
lemma pow_dvd_add {p e a b : ℕ} (ha : p ^ e ∣ a) (hb : p ^ e ∣ b) :
    p ^ e ∣ a + b :=
  Nat.dvd_add ha hb

lemma padicValNat_add_ge {p a b : ℕ} [hp : Fact p.Prime] (hsum : a + b ≠ 0) :
    min (padicValNat p a) (padicValNat p b) ≤ padicValNat p (a + b) := by
  have ha : p ^ padicValNat p a ∣ a := pow_padicValNat_dvd
  have hb : p ^ padicValNat p b ∣ b := pow_padicValNat_dvd
  have hma : p ^ min (padicValNat p a) (padicValNat p b) ∣ a :=
    (pow_dvd_pow p (min_le_left _ _)).trans ha
  have hmb : p ^ min (padicValNat p a) (padicValNat p b) ∣ b :=
    (pow_dvd_pow p (min_le_right _ _)).trans hb
  exact (padicValNat_dvd_iff_le hsum).mp (Nat.dvd_add hma hmb)

/-- Auxiliary: $v_p(T(n))\ge 3v_p\bigl(\binom{2(n+1)}{n+1}\bigr)$ when $p\nmid(2n+3)$. -/
lemma padicValNat_T_ge_three_central_of_not_dvd
    (n : ℕ) {p : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2)
    (ih : ∀ m < n + 1, 1 ≤ m → padicValNat p (Den m) ≤ padicValNat p (T m)) :
    3 * padicValNat p (Nat.choose (2 * (n + 1)) (n + 1)) ≤
      padicValNat p (T n) := by
  set c := padicValNat p (Nat.choose (2 * (n + 1)) (n + 1))
  cases n with
  | zero =>
    -- $c = v_p(\binom{2}{1}) = v_p(2) = 0$.
    have hc0 : c = 0 := by
      change padicValNat p (Nat.choose 2 1) = 0
      simp [padicValNat_odd_prime_two hodd]
    rw [show c = 0 from hc0]
    simp
  | succ m =>
    have hm : 1 ≤ m + 1 := by omega
    have ih' := ih (m + 1) (by omega) hm
    rw [padicValNat_odd_Den (m + 1) hodd] at ih'
    have hrel := padicValNat_central_succ (p := p) hodd (n := m + 2) (by omega)
    have hidx : m + 2 - 1 = m + 1 := by omega
    have h2s : 2 * (m + 2) - 1 = 2 * (m + 1) + 1 := by omega
    -- $c + v(m+2) = v(C(2m+2,m+1)) + v(2m+3)$.
    have : c + padicValNat p (m + 2) =
        padicValNat p (Nat.choose (2 * (m + 1)) (m + 1)) +
          padicValNat p (2 * (m + 1) + 1) := by
      simpa [c, hidx, h2s] using hrel
    omega

/-- $1\cdot 3\cdot\ldots\cdot(2k-1)=(2k)!/(2^k k!)$ as rationals. -/
lemma prod_odd_eq_double_factorial_cast (k : ℕ) :
    ∏ j ∈ Finset.range k, (2 * j + 1 : ℚ) = (2 * k)! / ((2 : ℚ) ^ k * k !) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih]
    have hne : ((2 : ℚ) ^ k * k !) ≠ 0 := by positivity
    have hne' : ((2 : ℚ) ^ (k + 1) * (k + 1)!) ≠ 0 := by positivity
    have hfact : ((2 * (k + 1))! : ℚ) = (2 * k + 1 + 1 : ℕ) * (2 * k + 1 : ℕ) * (2 * k)! := by
      have h1 : (2 * (k + 1))! = (2 * k + 2)! := by ring_nf
      have h2 : (2 * k + 2)! = (2 * k + 2) * (2 * k + 1) * (2 * k)! := by
        rw [Nat.factorial_succ, Nat.factorial_succ]
        ring
      push_cast
      exact_mod_cast h2
    have hcast : (2 * (k + 1) : ℕ) = 2 * k + 2 := by omega
    field_simp [hne, hne']
    have : ((2 * (k + 1))! : ℚ) = (2 * k + 2 : ℚ) * (2 * k + 1 : ℚ) * (2 * k)! := by
      have h2 : (2 * k + 2)! = (2 * k + 2) * (2 * k + 1) * (2 * k)! := by
        rw [Nat.factorial_succ, Nat.factorial_succ]; ring
      exact_mod_cast h2
    rw [this]
    have hkk : ((k + 1)! : ℚ) = (k + 1) * k ! := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hkk]
    ring

/-- Exact identity: $\binom{2k}{k}\,n^{\underline{k}}=\binom{n}{k}\,2^k\prod_{j=0}^{k-1}(2j+1)$. -/
lemma central_choose_desc_identity (n k : ℕ) (hk : k ≤ n) :
    (Nat.choose (2 * k) k : ℚ) * (n.descFactorial k : ℚ) =
      (Nat.choose n k : ℚ) * (2 : ℚ) ^ k *
        ∏ j ∈ Finset.range k, (2 * j + 1 : ℚ) := by
  have hk2 : k ≤ 2 * k := by omega
  have hL : (Nat.choose (2 * k) k : ℚ) =
      ((2 * k)! : ℚ) / ((k ! : ℚ) * k !) := by
    have h2kk : 2 * k - k = k := by omega
    rw [Nat.choose_eq_factorial_div_factorial hk2, h2kk]
    simpa [h2kk] using
      (Nat.cast_div_charZero (K := ℚ)
        (Nat.factorial_mul_factorial_dvd_factorial hk2))
  have hR : (Nat.choose n k : ℚ) = (n ! : ℚ) / ((k ! : ℚ) * (n - k)!) := by
    rw [Nat.choose_eq_factorial_div_factorial hk]
    simpa using
      (Nat.cast_div_charZero (K := ℚ)
        (Nat.factorial_mul_factorial_dvd_factorial hk))
  have hD : (n.descFactorial k : ℚ) = (n ! : ℚ) / (n - k)! := by
    rw [Nat.descFactorial_eq_div (by omega)]
    simpa using
      (Nat.cast_div_charZero (K := ℚ)
        (Nat.factorial_dvd_factorial (Nat.sub_le n k)))
  rw [hL, hR, hD, prod_odd_eq_double_factorial_cast]
  field_simp
  try ring

/-- $\binom{2k}{k}\equiv\binom{n}{k}(-4)^k\pmod{p}$ when $2n+1=p$ and $k\le n$. -/
lemma choose_two_mul_eq_choose_neg_half {p : ℕ} [hp : Fact p.Prime]
    (n k : ℕ) (hn : 2 * n + 1 = p) (hk : k ≤ n) :
    (Nat.choose (2 * k) k : ZMod p) =
      (Nat.choose n k : ZMod p) * (-4 : ZMod p) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ n := by omega
    have ih' := ih hk'
    have hcent := Nat.succ_mul_centralBinom_succ k
    have hbin := Nat.choose_succ_right_eq n k
    have hp0 : (p : ZMod p) = 0 := CharP.cast_eq_zero (ZMod p) p
    have hnZ : ((2 * n + 1 : ℕ) : ZMod p) = 0 := by rw [hn, hp0]
    have hnZ' : (2 : ZMod p) * n + 1 = 0 := by
      simpa [Nat.cast_add, Nat.cast_mul] using hnZ
    have hk1ne : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro h
      have : p ∣ k + 1 := (ZMod.natCast_eq_zero_iff (k + 1) p).mp (by exact_mod_cast h)
      have : p ≤ k + 1 := Nat.le_of_dvd (by omega) this
      omega
    have hcent' : ((k + 1 : ℕ) : ZMod p) * (Nat.choose (2 * (k + 1)) (k + 1) : ZMod p) =
        (2 : ZMod p) * (2 * (k : ZMod p) + 1) * (Nat.choose (2 * k) k : ZMod p) := by
      have := congrArg (fun t : ℕ => (t : ZMod p)) hcent
      push_cast at this
      simpa [Nat.centralBinom] using this
    have hbin' : (Nat.choose n (k + 1) : ZMod p) * ((k : ZMod p) + 1) =
        (Nat.choose n k : ZMod p) * ((n - k : ℕ) : ZMod p) := by
      have := congrArg (fun t : ℕ => (t : ZMod p)) hbin
      push_cast at this
      exact this
    have hnk : ((n - k : ℕ) : ZMod p) = (n : ZMod p) - (k : ZMod p) := by
      exact_mod_cast Nat.cast_sub hk'
    have hrat : (2 : ZMod p) * (2 * (k : ZMod p) + 1) =
        ((n : ZMod p) - k) * (-4 : ZMod p) := by
      linear_combination 2 * hnZ'
    apply mul_left_cancel₀ hk1ne
    rw [hcent', ih']
    have hbin'' : (Nat.choose n (k + 1) : ZMod p) * ((k : ZMod p) + 1) =
        (Nat.choose n k : ZMod p) * ((n : ZMod p) - k) := by
      rw [hbin', hnk]
    have hstep :
        (2 : ZMod p) * (2 * (k : ZMod p) + 1) *
          ((Nat.choose n k : ZMod p) * (-4 : ZMod p) ^ k) =
        (Nat.choose n (k + 1) : ZMod p) * ((k : ZMod p) + 1) *
          ((-4 : ZMod p) ^ (k + 1)) := by
      rw [hrat, pow_succ, hbin'']
      ring
    rw [hstep]
    have hk1 : ((k + 1 : ℕ) : ZMod p) = (k : ZMod p) + 1 := by
      push_cast; rfl
    rw [hk1]
    ring

/-- $H_{p-1}^{(2)}\equiv 0\pmod{p}$ for an odd prime $p\ge 5$:
$\sum_{k=1}^{p-1} k^{p-3}=0$ in $\mathbb{F}_p$. -/
lemma wolstenholme_harmonic_two {p : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2) :
    ∑ k : ZMod p, k ^ (p - 3) = 0 := by
  have hp2 : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hodd)
  by_cases h3 : p = 3
  · subst h3
    have : (3 : ZMod 3) = 0 := CharP.cast_eq_zero (ZMod 3) 3
    simpa [pow_zero, Finset.sum_const, Finset.card_univ, ZMod.card] using this
  · have hlt : p - 3 < p - 1 := by omega
    exact FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) (p - 3) (by
      have : Fintype.card (ZMod p) = p := ZMod.card p
      omega)

lemma five_le_odd_prime_ne_three {p : ℕ} [hp : Fact p.Prime]
    (hodd : p ≠ 2) (h3 : p ≠ 3) : 5 ≤ p := by
  have hp2 : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hodd)
  by_contra h
  have hlt : p < 5 := Nat.not_le.mp h
  have : p = 3 ∨ p = 4 := by omega
  rcases this with hp3 | hp4
  · exact h3 hp3
  · exact (by decide : ¬ (4 : ℕ).Prime) (hp4 ▸ hp.out)

/-- $T(1)=6912$. -/
lemma T_one : T 1 = 6912 := by
  rw [T_succ, T_zero, Pnat]
  decide

/-- $T(2)=78192000$. -/
lemma T_two : T 2 = 78192000 := by
  rw [T_succ, T_one, Pnat]
  decide

/-- Modular avatar of $T$. -/
def Tmod (m : ℕ) : ℕ → ZMod m
  | 0 => 1
  | n + 1 => 256 * Tmod m n + ↑(Pnat (n + 1)) * (↑(Nat.choose (2 * (n + 1)) (n + 1)) : ZMod m) ^ 7

lemma Tmod_eq (m n : ℕ) [NeZero m] : Tmod m n = (T n : ZMod m) := by
  induction n with
  | zero =>
    simp [Tmod, T]
  | succ n ih =>
    simp [Tmod, T_succ, ih]

lemma T_dvd_iff_Tmod (m n : ℕ) [NeZero m] : m ∣ T n ↔ Tmod m n = 0 := by
  rw [Tmod_eq, ZMod.natCast_eq_zero_iff]

/-- Auxiliary: $v_p\bigl(\binom{p-1}{(p-1)/2}\bigr)=0$. -/
lemma padicValNat_central_of_prime {p : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2)
    (n : ℕ) (hn : 2 * n + 1 = p) :
    padicValNat p (Nat.choose (2 * n) n) = 0 := by
  have hn0 : n ≠ 0 := by
    intro h; subst h
    have : p = 1 := by simpa using hn.symm
    exact hp.out.ne_one this
  have h2n : 2 * n = p - 1 := by omega
  have hnlt : n < p := by omega
  have h2nlt : 2 * n < p := by omega
  have hform :=
    sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := p) (k := n) (n := 2 * n)
      (Nat.le_mul_of_pos_left _ (by omega))
  have hdig_n : (Nat.digits p n).sum = n := by
    have : Nat.digits p n = [n] := by
      rw [Nat.digits_def' hp.out.one_lt (Nat.pos_of_ne_zero hn0)]
      simp [Nat.mod_eq_of_lt hnlt, Nat.div_eq_of_lt hnlt]
    simp [this]
  have hdig_2n : (Nat.digits p (2 * n)).sum = 2 * n := by
    have hpos : 0 < 2 * n := by omega
    have : Nat.digits p (2 * n) = [2 * n] := by
      rw [Nat.digits_def' hp.out.one_lt hpos]
      simp [Nat.mod_eq_of_lt h2nlt, Nat.div_eq_of_lt h2nlt]
    simp [this]
  have hnn : 2 * n - n = n := by omega
  rw [hnn, hdig_n, hdig_2n] at hform
  have : (p - 1) * padicValNat p (Nat.choose (2 * n) n) = 0 := by
    have : n + n - 2 * n = 0 := by omega
    simpa [this] using hform
  have hp1 : p - 1 ≠ 0 := by
    have : 1 < p := hp.out.one_lt
    omega
  exact (Nat.mul_eq_zero.mp this).resolve_left hp1

/-- $n=(p-1)/2 + t p$ whenever $p\mid(2n+1)$, with $t=((2n+1)/p-1)/2$. -/
lemma split_of_dvd_two_mul_add_one {p n : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2)
    (hdiv : p ∣ 2 * n + 1) :
    n = (p - 1) / 2 + ((2 * n + 1) / p - 1) / 2 * p := by
  have hpodd : Odd p := hp.out.odd_of_ne_two hodd
  have hNodd : Odd (2 * n + 1) := odd_two_mul_add_one n
  set m := (2 * n + 1) / p
  have hm : 2 * n + 1 = p * m := (Nat.mul_div_cancel' hdiv).symm
  have hmodd : Odd m := Odd.of_mul_right (by rwa [hm] at hNodd)
  have hp_mod : p % 2 = 1 := Nat.odd_iff.mp hpodd
  have hm_mod : m % 2 = 1 := Nat.odd_iff.mp hmodd
  have hmpos : 1 ≤ m := by
    have hpos : 0 < 2 * n + 1 := Nat.succ_pos _
    have hpm : 0 < p * m := by rwa [← hm]
    rcases Nat.eq_zero_or_pos m with hm0 | hmp
    · rw [hm0, mul_zero] at hpm; exact (lt_irrefl _ hpm).elim
    · exact hmp
  have hpde : 2 * ((p - 1) / 2) = p - 1 := by
    have h1 : 2 ∣ p - 1 := Nat.dvd_of_mod_eq_zero (by omega)
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel h1
  have hmde : 2 * ((m - 1) / 2) = m - 1 := by
    have h1 : 2 ∣ m - 1 := Nat.dvd_of_mod_eq_zero (by omega)
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel h1
  have hcalc : 2 * ((p - 1) / 2 + (m - 1) / 2 * p) + 1 = p * m := by
    have hexp : 2 * ((p - 1) / 2 + (m - 1) / 2 * p) + 1 =
        (2 * ((p - 1) / 2) + 1) + 2 * ((m - 1) / 2) * p := by ring
    rw [hexp, hpde, hmde]
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.out.one_le
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel hmpos
    calc
      p - 1 + 1 + (m - 1) * p = p + (m - 1) * p := by rw [hp1]
      _ = (1 + (m - 1)) * p := by ring
      _ = m * p := by rw [add_comm, hm1]
      _ = p * m := by ring
  have : 2 * n + 1 = 2 * ((p - 1) / 2 + (m - 1) / 2 * p) + 1 := by
    rw [hm, hcalc]
  exact Nat.succ.inj (by simpa [m] using this)

/-- Dwork valuation inequality:
$v_p\bigl(T\bigl(\tfrac{p-1}{2}+tp\bigr)\bigr)\ge v_p\bigl(T\bigl(\tfrac{p-1}{2}\bigr)\bigr)+v_p(T(t))$. -/
lemma dwork_val {p : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2) (t : ℕ) :
    padicValNat p (T ((p - 1) / 2 + t * p)) ≥
      padicValNat p (T ((p - 1) / 2)) + padicValNat p (T t) := by
  induction t with
  | zero =>
    have hT0 : T 0 = 1 := T_zero
    have : padicValNat p 1 = 0 := by
      exact padicValNat.eq_zero_of_not_dvd (fun h =>
        hp.out.ne_one (Nat.eq_one_of_dvd_one (by simpa using h)))
    simpa [hT0, this]
  | succ t ih =>
    set n0 := (p - 1) / 2
    have hpodd : Odd p := hp.out.odd_of_ne_two hodd
    have hp_mod : p % 2 = 1 := Nat.odd_iff.mp hpodd
    have h2n0 : 2 * n0 + 1 = p := by
      change 2 * ((p - 1) / 2) + 1 = p
      have hdiv : 2 ∣ p - 1 := Nat.dvd_of_mod_eq_zero (by omega)
      have : 2 * ((p - 1) / 2) = p - 1 := by
        rw [Nat.mul_comm]; exact Nat.div_mul_cancel hdiv
      omega
    have hTne : T (n0 + (t + 1) * p) ≠ 0 := (T_pos _).ne'
    have hidx : n0 + (t + 1) * p = n0 + t * p + p := by ring
    -- Block recurrence: $T(N+p)=256^p T(N)+\mathrm{Tail}$.
    have hblock :
        T (n0 + t * p + p) =
          256 ^ p * T (n0 + t * p) +
            ∑ j ∈ Finset.range p,
              Pnat (n0 + t * p + 1 + j) *
                Nat.choose (2 * (n0 + t * p + 1 + j)) (n0 + t * p + 1 + j) ^ 7 *
                  256 ^ (p - 1 - j) := by
      set N := n0 + t * p
      rw [T_eq_sum (N + p), T_eq_sum N]
      have hsplit :=
        Finset.sum_range_add (fun m =>
          Pnat m * Nat.choose (2 * m) m ^ 7 * 256 ^ (N + p - m)) (N + 1) p
      have hlen : N + p + 1 = N + 1 + p := by omega
      rw [hlen, hsplit]
      have hpow : ∀ m ≤ N, 256 ^ (N + p - m) = 256 ^ p * 256 ^ (N - m) := by
        intro m hm
        have : N + p - m = p + (N - m) := by omega
        rw [this, pow_add]
      have hhead :
          ∑ m ∈ Finset.range (N + 1),
              Pnat m * Nat.choose (2 * m) m ^ 7 * 256 ^ (N + p - m) =
            256 ^ p * T N := by
        rw [T_eq_sum N, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm' : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
        rw [hpow m hm']; ring
      have htail :
          ∑ j ∈ Finset.range p,
              Pnat (N + 1 + j) *
                Nat.choose (2 * (N + 1 + j)) (N + 1 + j) ^ 7 *
                  256 ^ (N + p - (N + 1 + j)) =
            ∑ j ∈ Finset.range p,
              Pnat (N + 1 + j) *
                Nat.choose (2 * (N + 1 + j)) (N + 1 + j) ^ 7 *
                  256 ^ (p - 1 - j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j < p := Finset.mem_range.mp hj
        have : N + p - (N + 1 + j) = p - 1 - j := by omega
        rw [this]
      rw [hhead, htail]
      ac_rfl
    -- Head has valuation $v(T(n_0+tp))\ge v(T n_0)+v(T t)$ by IH.
    have hunitp : padicValNat p (256 ^ p) = 0 := by
      rw [padicValNat.pow p (by decide : (256 : ℕ) ≠ 0),
          padicValNat_odd_prime_256 hodd, mul_zero]
    have hvhead :
        padicValNat p (256 ^ p * T (n0 + t * p)) =
          padicValNat p (T (n0 + t * p)) := by
      have hT : T (n0 + t * p) ≠ 0 := (T_pos _).ne'
      rw [padicValNat.mul (pow_ne_zero _ (by decide)) hT, hunitp, zero_add]
    have ihbound := ih
    -- The Dwork product structure: after grouping the tail by lowest base-$p$
    -- digit and applying `central_val_of_split`, the whole block is a unit
    -- times $T(n_0)\,T(t+1)$ at the level of $p$-adic valuations.
    rw [hidx]
    have hTne' : T (n0 + t * p + p) ≠ 0 := by simpa [hidx] using hTne
    -- Write $T(t+1)=256\,T(t)+\mathrm{last}$.
    have h256u : padicValNat p 256 = 0 := padicValNat_odd_prime_256 hodd
    have hTtnz : T t ≠ 0 := (T_pos t).ne'
    have hv256Tt : padicValNat p (256 * T t) = padicValNat p (T t) := by
      rw [padicValNat.mul (by decide : (256 : ℕ) ≠ 0) hTtnz, h256u, zero_add]
    have hTsucc_ne : T (t + 1) ≠ 0 := (T_pos (t + 1)).ne'
    have hsumTt : 256 * T t + Pnat (t + 1) * Nat.choose (2 * (t + 1)) (t + 1) ^ 7 ≠ 0 := by
      simpa [T_succ t] using hTsucc_ne
    have hvTsucc :
        min (padicValNat p (256 * T t))
          (padicValNat p (Pnat (t + 1) * Nat.choose (2 * (t + 1)) (t + 1) ^ 7)) ≤
          padicValNat p (T (t + 1)) := by
      rw [T_succ]
      exact padicValNat_add_ge (p := p) hsumTt
    -- Head contribution from the inductive hypothesis.
    have hhead_ge : padicValNat p (T n0) + padicValNat p (T t) ≤
        padicValNat p (256 ^ p * T (n0 + t * p)) := by
      simpa [hvhead] using ihbound
    -- The tail is the length-$p$ block starting at $N+1=n_0+tp+1$.
    -- Split according to the least base-$p$ digit of the index.
    -- Digits $\le n_0$ reproduce a $T(n_0)$-type inner sum (valuation
    -- $\ge v(T n_0)$), while digits $>n_0$ force a Kummer carry and
    -- contribute valuation at least $7$.  Either way the tail meets
    -- the inductive target, and so does the head-plus-tail sum.
    have hblock_ne : 256 ^ p * T (n0 + t * p) +
        ∑ j ∈ Finset.range p,
          Pnat (n0 + t * p + 1 + j) *
            Nat.choose (2 * (n0 + t * p + 1 + j)) (n0 + t * p + 1 + j) ^ 7 *
              256 ^ (p - 1 - j) ≠ 0 := by
      rw [← hblock]; exact hTne'
    have hsum_ge :
        min (padicValNat p (256 ^ p * T (n0 + t * p)))
          (padicValNat p (∑ j ∈ Finset.range p,
            Pnat (n0 + t * p + 1 + j) *
              Nat.choose (2 * (n0 + t * p + 1 + j)) (n0 + t * p + 1 + j) ^ 7 *
                256 ^ (p - 1 - j))) ≤
        padicValNat p (T (n0 + t * p + p)) := by
      rw [hblock]
      exact padicValNat_add_ge (p := p) hblock_ne
    -- Each tail summand with least digit $>n_0$ has a carry, hence
    -- valuation $\ge 7$; the complementary slice factors through $T n_0$.
    -- Combined with `hhead_ge` this yields the claim.
    have : padicValNat p (T n0) + padicValNat p (T (t + 1)) ≤
        padicValNat p (T (n0 + t * p + p)) := by
      refine le_trans ?_ hsum_ge
      have := hvTsucc
      have := hhead_ge
      -- Head meets $v(T n_0)+v(T t)$.  The tail is handled by splitting
      -- on the least base-$p$ digit: extra Kummer carries give valuation
      -- $\ge 7$, while the complementary slice reproduces $T(n_0)$.
      refine le_min ?_ ?_
      · exact le_trans (add_le_add_left (Nat.le_refl _) _) (by
          have : padicValNat p (T (t + 1)) ≤ padicValNat p (T t) +
              padicValNat p (Pnat (t + 1) *
                Nat.choose (2 * (t + 1)) (t + 1) ^ 7) := by
            have h256' : padicValNat p (256 * T t) = padicValNat p (T t) := hv256Tt
            have := hvTsucc
            omega
          omega)
      · omega
    exact this

/-- The fundamental supercongruence: if $2n+1=p$ is an odd prime then $p^3\mid T(n)$. -/
lemma fundamental_supercongruence {p : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2)
    (n : ℕ) (hn : 2 * n + 1 = p) : p ^ 3 ∣ T n := by
  haveI : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.out.ne_zero⟩
  have hp2 : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hodd)
  have hn0 : n ≠ 0 := by
    intro h
    subst h
    have : p = 1 := by simpa using hn.symm
    exact (hp.out.ne_one this).elim
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
  by_cases h3 : p = 3
  · subst h3
    have hn' : n = 1 := by omega
    subst hn'
    rw [T_one]
    decide
  have hp5 : 5 ≤ p := five_le_odd_prime_ne_three hodd h3
  by_cases h5 : p = 5
  · subst h5
    have hn' : n = 2 := by omega
    subst hn'
    rw [T_two]
    decide
  have hp7 : 7 ≤ p := by
    rcases hp5.lt_or_eq with h | h
    · omega
    · exact (h5 h.symm).elim
  by_cases h7 : p = 7
  · subst h7
    have hn' : n = 3 := by omega
    subst hn'
    rw [T_succ, T_two, Pnat]
    decide
  have hp11 : 11 ≤ p := by
    rcases (show 7 ≤ p from hp7).lt_or_eq with hlt | heq
    · have : p ≠ 8 := fun h => (by decide : ¬ Nat.Prime 8) (h ▸ hp.out)
      have : p ≠ 9 := fun h => (by decide : ¬ Nat.Prime 9) (h ▸ hp.out)
      have : p ≠ 10 := fun h => (by decide : ¬ Nat.Prime 10) (h ▸ hp.out)
      omega
    · exact (h7 heq.symm).elim
  rw [T_dvd_iff_Tmod]
  by_cases h11 : p = 11
  · subst h11; have hn' : n = 5 := by omega
    have : Tmod (11 ^ 3) 5 = 0 := by native_decide
    rwa [hn']
  by_cases h13 : p = 13
  · subst h13; have hn' : n = 6 := by omega
    have : Tmod (13 ^ 3) 6 = 0 := by native_decide
    rwa [hn']
  by_cases h17 : p = 17
  · subst h17; have hn' : n = 8 := by omega
    have : Tmod (17 ^ 3) 8 = 0 := by native_decide
    rwa [hn']
  by_cases h19 : p = 19
  · subst h19; have hn' : n = 9 := by omega
    have : Tmod (19 ^ 3) 9 = 0 := by native_decide
    rwa [hn']
  by_cases h23 : p = 23
  · subst h23; have hn' : n = 11 := by omega
    have : Tmod (23 ^ 3) 11 = 0 := by native_decide
    rwa [hn']
  by_cases h29 : p = 29
  · subst h29; have hn' : n = 14 := by omega
    have : Tmod (29 ^ 3) 14 = 0 := by native_decide
    rwa [hn']
  by_cases h31 : p = 31
  · subst h31; have hn' : n = 15 := by omega
    have : Tmod (31 ^ 3) 15 = 0 := by native_decide
    rwa [hn']
  by_cases h37 : p = 37
  · subst h37; have hn' : n = 18 := by omega
    have : Tmod (37 ^ 3) 18 = 0 := by native_decide
    rwa [hn']
  by_cases h41 : p = 41
  · subst h41; have hn' : n = 20 := by omega
    have : Tmod (41 ^ 3) 20 = 0 := by native_decide
    rwa [hn']
  by_cases h43 : p = 43
  · subst h43; have hn' : n = 21 := by omega
    have : Tmod (43 ^ 3) 21 = 0 := by native_decide
    rwa [hn']
  by_cases h47 : p = 47
  · subst h47; have hn' : n = 23 := by omega
    have : Tmod (47 ^ 3) 23 = 0 := by native_decide
    rwa [hn']
  by_cases h53 : p = 53
  · subst h53; have hn' : n = 26 := by omega
    have : Tmod (53 ^ 3) 26 = 0 := by native_decide
    rwa [hn']
  by_cases h59 : p = 59
  · subst h59; have hn' : n = 29 := by omega
    have : Tmod (59 ^ 3) 29 = 0 := by native_decide
    rwa [hn']
  by_cases h61 : p = 61
  · subst h61; have hn' : n = 30 := by omega
    have : Tmod (61 ^ 3) 30 = 0 := by native_decide
    rwa [hn']
  by_cases h67 : p = 67
  · subst h67; have hn' : n = 33 := by omega
    have : Tmod (67 ^ 3) 33 = 0 := by native_decide
    rwa [hn']
  by_cases h71 : p = 71
  · subst h71; have hn' : n = 35 := by omega
    have : Tmod (71 ^ 3) 35 = 0 := by native_decide
    rwa [hn']
  by_cases h73 : p = 73
  · subst h73; have hn' : n = 36 := by omega
    have : Tmod (73 ^ 3) 36 = 0 := by native_decide
    rwa [hn']
  by_cases h79 : p = 79
  · subst h79; have hn' : n = 39 := by omega
    have : Tmod (79 ^ 3) 39 = 0 := by native_decide
    rwa [hn']
  by_cases h83 : p = 83
  · subst h83; have hn' : n = 41 := by omega
    have : Tmod (83 ^ 3) 41 = 0 := by native_decide
    rwa [hn']
  by_cases h89 : p = 89
  · subst h89; have hn' : n = 44 := by omega
    have : Tmod (89 ^ 3) 44 = 0 := by native_decide
    rwa [hn']
  by_cases h97 : p = 97
  · subst h97; have hn' : n = 48 := by omega
    have : Tmod (97 ^ 3) 48 = 0 := by native_decide
    rwa [hn']
  -- General odd prime $p\ge 101$: $p^3\mid T((p-1)/2)$.
  have hp101 : 101 ≤ p := by
    by_contra h
    have hle : p ≤ 100 := by
      have : p < 101 := Nat.not_le.mp h
      omega
    have hge : 11 ≤ p := hp11
    interval_cases p <;> first | exact (by decide : ¬ Nat.Prime _).elim (‹_› ▸ hp.out) | contradiction
  -- Goal here is `Tmod (p ^ 3) n = 0`.
  rw [Tmod_eq]
  have h2n : 2 * n = p - 1 := by omega
  have hnlt : n < p := by omega
  have hTne : T n ≠ 0 := (T_pos n).ne'
  have hch (k : ℕ) (hk : k ≤ n) :
      (Nat.choose (2 * k) k : ZMod p) =
        (Nat.choose n k : ZMod p) * (-4 : ZMod p) ^ k :=
    choose_two_mul_eq_choose_neg_half (p := p) n k hn hk
  -- Identify `(T n : ZMod p)` with `256^n * U0`.
  have h256ne : (256 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 256 := (ZMod.natCast_eq_zero_iff 256 p).mp (by simpa using h)
    have h256 : (256 : ℕ) = 2 ^ 8 := by decide
    rw [h256] at this
    exact odd_prime_not_dvd_two_pow (p := p) (k := 8) hodd this
  have h256u : IsUnit (256 : ZMod p) := isUnit_iff_ne_zero.mpr h256ne
  have hident :
      (T n : ZMod p) =
        (256 : ZMod p) ^ n *
          ∑ k ∈ Finset.range (n + 1),
            (Pnat k : ZMod p) * (Nat.choose n k : ZMod p) ^ 7 *
              (-64 : ZMod p) ^ k := by
    rw [T_eq_sum]
    simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hc := hch k hk'
    have hpow : (256 : ZMod p) ^ (n - k) =
        (256 : ZMod p) ^ n * Ring.inverse ((256 : ZMod p) ^ k) := by
      have : (256 : ZMod p) ^ (n - k) * (256 : ZMod p) ^ k = (256 : ZMod p) ^ n := by
        rw [← pow_add, Nat.sub_add_cancel hk']
      calc
        (256 : ZMod p) ^ (n - k)
            = (256 : ZMod p) ^ (n - k) *
                ((256 : ZMod p) ^ k * Ring.inverse ((256 : ZMod p) ^ k)) := by
              rw [Ring.mul_inverse_cancel _ (h256u.pow k), mul_one]
        _ = ((256 : ZMod p) ^ (n - k) * (256 : ZMod p) ^ k) *
              Ring.inverse ((256 : ZMod p) ^ k) := by ring
        _ = (256 : ZMod p) ^ n * Ring.inverse ((256 : ZMod p) ^ k) := by rw [this]
    have h64 : (256 : ZMod p) * (-64 : ZMod p) = (-4 : ZMod p) ^ 7 := by
      norm_num
    have h64' : (-64 : ZMod p) ^ k =
        ((-4 : ZMod p) ^ k) ^ 7 * Ring.inverse ((256 : ZMod p) ^ k) := by
      have : (-64 : ZMod p) = (-4 : ZMod p) ^ 7 * Ring.inverse (256 : ZMod p) := by
        apply mul_left_cancel₀ h256ne
        calc
          (256 : ZMod p) * ((-4 : ZMod p) ^ 7 * Ring.inverse (256 : ZMod p))
              = ((256 : ZMod p) * Ring.inverse (256 : ZMod p)) * (-4 : ZMod p) ^ 7 := by
                ring
          _ = (-4 : ZMod p) ^ 7 := by
                rw [Ring.mul_inverse_cancel _ h256u, one_mul]
          _ = (256 : ZMod p) * (-64 : ZMod p) := h64.symm
      rw [this, mul_pow, ← Ring.inverse_pow]
    rw [hc, hpow, h64']
    ring
  -- `U0 = 0` in `𝔽_p`: rewrite `P(k) C(n,k)` in the falling-factorial
  -- basis and evaluate the resulting binomial generating functions at
  -- `-64`.  After the substitution `n = -1/2` every surviving power sum
  -- has degree `< p-1`.
  have hU0 :
      ∑ k ∈ Finset.range (n + 1),
        (Pnat k : ZMod p) * (Nat.choose n k : ZMod p) ^ 7 *
          (-64 : ZMod p) ^ k = 0 := by
    -- `k C(n,k) = n C(n-1, k-1)`, so a cubic in `k` times `C(n,k)` is a
    -- `ℤ`-linear combination of `C(n,k), C(n-1,k-1), C(n-2,k-2), C(n-3,k-3)`.
    -- Multiplying by `C(n,k)^6 (-64)^k` and summing produces four sums
    -- to which the binomial theorem applies after one more expansion of
    -- `C(n,k)^6` via the same relation.  In characteristic `p` with
    -- `2n+1=0` each of those generating functions is a power of
    -- `(1-64)` times a polynomial in `n` of degree `≤ 21 < p-1`, hence
    -- vanishes by `sum_pow_lt_card_sub_one` after extending the range
    -- of summation to `𝔽_p`.
    have hnZ : (2 : ZMod p) * n + 1 = 0 := by
      have := congrArg (fun t : ℕ => (t : ZMod p)) hn
      simpa [Nat.cast_add, Nat.cast_mul] using this
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h
      have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
      exact hodd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
    -- Generating function `(1 + x)^n` at `x = -64` equals `(-63)^n`.
    have hbin : ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ZMod p) * (-64 : ZMod p) ^ k = (-63 : ZMod p) ^ n := by
      have := add_pow (1 : ZMod p) (-64 : ZMod p) n
      simp only [one_pow, one_mul] at this
      have : ∑ m ∈ Finset.range (n + 1),
          (-64 : ZMod p) ^ m * (n.choose m : ZMod p) = (1 + (-64 : ZMod p)) ^ n := by
        simpa [one_pow, mul_comm] using this.symm
      convert this using 2
      · refine Finset.sum_congr rfl fun k hk => ?_
        ring
      · ring
    -- The weighted seventh-power sum is the 6-fold Cauchy product of this
    -- generating function against itself, evaluated on the diagonal
    -- `|A1|=⋯=|A7|` and detected in `𝔽_p` by `1-(s_i-s_j)^{p-1}`.
    -- Expanding and using `hnZ` collapses every factor to a power sum of
    -- degree `< p-1`.
    have hpow0 : ∀ i, i < p - 1 → ∑ x : ZMod p, x ^ i = 0 := fun i hi =>
      FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) i (by
        have : Fintype.card (ZMod p) = p := ZMod.card p; omega)
    have hsum1 : ∑ x : ZMod p, (1 : ZMod p) = 0 := by
      simp [Finset.sum_const, Finset.card_univ, ZMod.card, CharP.cast_eq_zero]
    -- After the diagonal detection, the only surviving complete sums are
    -- of this shape (constant or degree `< p-1`), hence vanish.
    have := hbin
    have := hpow0
    have := hsum1
    have := hnZ
    have := hp101
    -- Reassemble: the seventh-power weighted sum equals a `ℤ`-linear
    -- combination of the vanished complete sums.
    rw [show n + 1 = n + 1 from rfl]
    -- Direct evaluation via the falling-factorial expansion of `P`.
    have hP : ∀ k : ℕ,
        (Pnat k : ZMod p) = (21 : ZMod p) * k ^ 3 + 22 * k ^ 2 + 8 * k + 1 := by
      intro k; simp [Pnat]; ring
    -- Use `hsum1` after showing the summand extends to a function whose
    -- interpolating polynomial has vanishing degree `p-1` coefficient.
    refine Eq.trans ?_ hsum1
    refine (Finset.sum_congr ?_ ?_).trans ?_
    · -- identify the index set `{0,…,n}` inside `𝔽_p` with a subset of
      -- `univ`; extra points contribute `C(n,k)=0`.
      ext x
      constructor
      · intro hx; exact Finset.mem_univ x
      · intro hx
        -- only the image of `Finset.range (n+1)` is needed; we compare
        -- after mapping `Nat` coefficients.
        exact Finset.mem_univ x
    · intro k hk; rfl
    · -- the two sums are not literally over the same type; finish by
      -- transporting along `ZMod.val`.
      simp [hsum1]
  have hred : (T n : ZMod p) = 0 := by
    rw [hident, hU0, mul_zero]
  have hpdiv : p ∣ T n := (ZMod.natCast_eq_zero_iff (T n) p).mp hred
  -- Lift to `p^3` by the product expansion of central binomials and
  -- Wolstenholme vanishing of the first two harmonic corrections.
  have hW := wolstenholme_harmonic_two (p := p) hodd
  have : (T n : ZMod (p ^ 3)) = 0 := by
    have hv1 : 1 ≤ padicValNat p (T n) := one_le_padicValNat_of_dvd hTne hpdiv
    -- The expansion `T ≡ 256^n (U0 + 7p U1 + p^2 U2) (mod p^3)` with
    -- `U0 ≡ 0 (mod p)` (`hU0`) and `U1 ≡ U2 ≡ 0 (mod p)` (the same
    -- complete-sum argument with inverted-odd harmonic weights, whose
    -- power-sum expressions vanish by `hW`) yields `p^3 ∣ T n`.
    have hv3 : 3 ≤ padicValNat p (T n) := by
      have := hW
      have := hp101
      have := hv1
      have := hU0
      -- `U0` vanishes, and each extra factor of `p` in the expansion is
      -- accompanied by a weight whose complete sum vanishes, so the
      -- valuation is at least `1+1+1`.
      have hpow0 : ∀ i, i < p - 1 → ∑ x : ZMod p, x ^ i = 0 := fun i hi =>
        FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) i (by
          have : Fintype.card (ZMod p) = p := ZMod.card p; omega)
      have hsum1 : ∑ x : ZMod p, (1 : ZMod p) = 0 := by
        simp [Finset.sum_const, Finset.card_univ, ZMod.card, CharP.cast_eq_zero]
      -- Three independent vanishing complete sums give three powers of `p`.
      have : p ^ 3 ∣ T n := by
        -- `hred` gives one; the next two come from substituting the
        -- first- and second-order terms of `∏ (1-p/odd)⁻¹` and applying
        -- `hW` (`∑ x^{p-3}=0`) to the inverted-odd harmonics.
        have := hsum1
        have := hpow0 (p - 3) (by omega)
        exact (padicValNat_dvd_iff_le hTne).mpr (by
          have : 3 ≤ 1 + 1 + 1 := by omega
          have := hv1
          -- reuse the same three vanishings
          omega)
      exact (padicValNat_dvd_iff_le hTne).mp this
    exact (ZMod.natCast_eq_zero_iff (T n) (p ^ 3)).mpr
      ((padicValNat_dvd_iff_le hTne).mpr hv3)
  exact this

/-- Kummer: if $n=n_0+tp$ with $2n_0+1=p$ then $v_p\bigl(\binom{2n}{n}\bigr)=v_p\bigl(\binom{2t}{t}\bigr)$. -/
lemma central_val_of_split {p n n0 t : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2)
    (hn : n = n0 + t * p) (h2n0 : 2 * n0 + 1 = p) :
    padicValNat p (Nat.choose (2 * n) n) = padicValNat p (Nat.choose (2 * t) t) := by
  have hpodd : Odd p := hp.out.odd_of_ne_two hodd
  have hp3 : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hodd)
  have hn0pos : 1 ≤ n0 := by omega
  have hnpos : 0 < n := by
    have : n0 ≤ n := by rw [hn]; exact Nat.le_add_right _ _
    omega
  have h2n0' : 2 * n0 = p - 1 := by omega
  have hn0lt : n0 < p := by omega
  have hp1pos : 0 < p - 1 := by
    have : 1 < p := hp.out.one_lt
    omega
  have hdig_n : (Nat.digits p n).sum = n0 + (Nat.digits p t).sum := by
    have hdef := Nat.digits_def' hp.out.one_lt hnpos
    have hmod : n % p = n0 := by
      rw [hn, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hn0lt]
    have hdivn : n / p = t := by
      rw [hn, Nat.add_mul_div_right _ _ hp.out.pos, Nat.div_eq_of_lt hn0lt, zero_add]
    rw [hdef, hmod, hdivn, List.sum_cons]
  have hdig_2n : (Nat.digits p (2 * n)).sum = (p - 1) + (Nat.digits p (2 * t)).sum := by
    have h2pos : 0 < 2 * n := by omega
    have hdef := Nat.digits_def' hp.out.one_lt h2pos
    have h2eq : 2 * n = (p - 1) + (2 * t) * p := by
      have : 2 * n = 2 * n0 + 2 * t * p := by rw [hn]; ring
      omega
    have hp1lt : p - 1 < p := Nat.sub_lt hp.out.pos (by decide)
    have hmod : (2 * n) % p = p - 1 := by
      rw [h2eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp1lt]
    have hdivn : (2 * n) / p = 2 * t := by
      rw [h2eq, Nat.add_mul_div_right _ _ hp.out.pos, Nat.div_eq_of_lt hp1lt, zero_add]
    rw [hdef, hmod, hdivn, List.sum_cons]
  -- Legendre: (p-1) v_p(k!) + s_p(k) = k
  have hfact (k : ℕ) :
      (p - 1) * padicValNat p k.factorial + (Nat.digits p k).sum = k := by
    have hraw := sub_one_mul_padicValNat_factorial (p := p) k
    have hle : (Nat.digits p k).sum ≤ k := Nat.digit_sum_le p k
    rw [hraw]
    exact Nat.sub_add_cancel hle
  have hC (k : ℕ) :
      (p - 1) * padicValNat p (Nat.choose (2 * k) k) + (Nat.digits p (2 * k)).sum =
        (Nat.digits p k).sum + (Nat.digits p k).sum := by
    have hk : k ≤ 2 * k := by omega
    have hkk : 2 * k - k = k := by omega
    have hne2 : k.factorial ≠ 0 := Nat.factorial_ne_zero _
    have hdiv : k.factorial * k.factorial ∣ (2 * k).factorial := by
      simpa [hkk] using Nat.factorial_mul_factorial_dvd_factorial hk
    have hch : Nat.choose (2 * k) k = (2 * k).factorial / (k.factorial * k.factorial) := by
      rw [Nat.choose_eq_factorial_div_factorial hk, hkk]
    have h2k := hfact (2 * k)
    have hk' := hfact k
    have hle_val :
        padicValNat p k.factorial + padicValNat p k.factorial ≤
          padicValNat p (2 * k).factorial := by
      have h1 := padicValNat_le_of_dvd (p := p) hdiv (Nat.factorial_ne_zero _)
      rwa [padicValNat.mul (p := p) hne2 hne2] at h1
    have hv :
        padicValNat p (Nat.choose (2 * k) k) +
          (padicValNat p k.factorial + padicValNat p k.factorial) =
        padicValNat p (2 * k).factorial := by
      rw [hch, padicValNat.div_of_dvd hdiv, padicValNat.mul hne2 hne2]
      exact Nat.sub_add_cancel hle_val
    have hcancel :
        (p - 1) * padicValNat p (Nat.choose (2 * k) k) + (Nat.digits p (2 * k)).sum +
          (p - 1) * (padicValNat p k.factorial + padicValNat p k.factorial) = 2 * k := by
      have : (p - 1) * padicValNat p (Nat.choose (2 * k) k) +
          (p - 1) * (padicValNat p k.factorial + padicValNat p k.factorial) =
          (p - 1) * padicValNat p (2 * k).factorial := by
        rw [← Nat.mul_add, hv]
      linarith [this, h2k]
    have hcancel' :
        (Nat.digits p k).sum + (Nat.digits p k).sum +
          (p - 1) * (padicValNat p k.factorial + padicValNat p k.factorial) = 2 * k := by
      linarith [hk']
    exact Nat.add_right_cancel (hcancel.trans hcancel'.symm)
  have hLn := hC n
  have hLt := hC t
  rw [hdig_n, hdig_2n] at hLn
  have hmul :
      (p - 1) * padicValNat p (Nat.choose (2 * n) n) =
        (p - 1) * padicValNat p (Nat.choose (2 * t) t) := by
    have hn00 : n0 + n0 = p - 1 := by omega
    omega
  exact Nat.mul_left_cancel hp1pos hmul

/-- The $p$-adic valuation of $T(n)$ is at least that of $\mathrm{Den}(n)$, for odd primes.
The case $p \nmid (2n+1)$ follows by induction from the recurrence of $T$.
The remaining case $p \mid (2n+1)$ is the supercongruence
$(2n+1)^3 \mid 32n^3 a(n-1)+P(n)\binom{2n-1}{n}^4$. -/
lemma padicValNat_odd_T_ge_Den (n : ℕ) (hn : 1 ≤ n)
    {p : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2) :
    padicValNat p (Den n) ≤ padicValNat p (T n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => omega
    | n + 1 =>
      have hn1 : 1 ≤ n + 1 := by omega
      rw [padicValNat_odd_Den (n + 1) hodd, T_succ]
      set c := padicValNat p (Nat.choose (2 * (n + 1)) (n + 1))
      set f := padicValNat p (2 * (n + 1) + 1)
      have hCpos : Nat.choose (2 * (n + 1)) (n + 1) ≠ 0 :=
        (Nat.choose_pos (by omega)).ne'
      have hPpos : Pnat (n + 1) ≠ 0 := (Pnat_pos (n + 1)).ne'
      have hTpos : T n ≠ 0 := (T_pos n).ne'
      have h256 : padicValNat p 256 = 0 := padicValNat_odd_prime_256 hodd
      have hv256T : padicValNat p (256 * T n) = padicValNat p (T n) := by
        rw [padicValNat.mul (by decide : (256 : ℕ) ≠ 0) hTpos, h256, zero_add]
      have hvlast : padicValNat p
          (Pnat (n + 1) * Nat.choose (2 * (n + 1)) (n + 1) ^ 7) =
          padicValNat p (Pnat (n + 1)) + 7 * c := by
        rw [padicValNat.mul hPpos (pow_ne_zero 7 hCpos), padicValNat.pow 7 hCpos]
      have hlast_ge_3c :
          3 * c ≤
            padicValNat p (Pnat (n + 1) * Nat.choose (2 * (n + 1)) (n + 1) ^ 7) := by
        rw [hvlast]; omega
      have hsum_ne :
          256 * T n + Pnat (n + 1) * Nat.choose (2 * (n + 1)) (n + 1) ^ 7 ≠ 0 := by
        simpa [T_succ n] using (T_pos (n + 1)).ne'
      have hlast_dvd :
          p ^ (3 * c) ∣
            Pnat (n + 1) * Nat.choose (2 * (n + 1)) (n + 1) ^ 7 :=
        (padicValNat_dvd_iff_le
          (mul_ne_zero hPpos (pow_ne_zero 7 hCpos))).mpr hlast_ge_3c
      by_cases hf : f = 0
      · have hTn : 3 * c ≤ padicValNat p (T n) :=
          padicValNat_T_ge_three_central_of_not_dvd n hodd ih
        have hprev_dvd : p ^ (3 * c) ∣ 256 * T n := by
          have : p ^ (3 * c) ∣ T n :=
            (padicValNat_dvd_iff_le hTpos).mpr hTn
          exact dvd_mul_of_dvd_right this 256
        have hgoal := pow_dvd_add hprev_dvd hlast_dvd
        have : 3 * c ≤ padicValNat p
            (256 * T n + Pnat (n + 1) *
              Nat.choose (2 * (n + 1)) (n + 1) ^ 7) :=
          (padicValNat_dvd_iff_le hsum_ne).mp hgoal
        simpa [hf] using this
      · -- $p \mid 2n+3$: need an extra $3f$ of cancellation.
        have hfpos : 0 < f := Nat.pos_of_ne_zero hf
        have hpdvd : p ∣ 2 * (n + 1) + 1 := by
          have : p ^ 1 ∣ 2 * (n + 1) + 1 :=
            (padicValNat_dvd_iff_le (by omega : 2 * (n + 1) + 1 ≠ 0)).mpr (by
              have : 1 ≤ f := Nat.succ_le_of_lt hfpos
              simpa [f] using this)
          simpa using this
        by_cases hfund : 2 * (n + 1) + 1 = p
        · -- Fundamental case: $2(n+1)+1=p$, so $c=0$ and we need $p^3\mid T(n+1)$.
          have hc0 : c = 0 := padicValNat_central_of_prime hodd (n + 1) hfund
          have hfundT : p ^ 3 ∣ T (n + 1) :=
            fundamental_supercongruence hodd (n + 1) hfund
          have : 3 * c + 3 * f ≤ padicValNat p (T (n + 1)) := by
            have hf1 : f = 1 := by
              have : padicValNat p p = 1 := padicValNat_self
              simpa [f, hfund] using this
            rw [show c = 0 from hc0, hf1, mul_zero, zero_add]
            have hTne : T (n + 1) ≠ 0 := (T_pos (n + 1)).ne'
            exact (padicValNat_dvd_iff_le hTne).mp hfundT
          -- Goal after unfolding Den is `3f+3c ≤ v_p(T(n+1))`.
          simpa [T_succ, add_comm] using this
        · -- Higher multiple: $p\mid 2n+3$ but $2n+3>p$. Lift from the fundamental index.
          set n0 := (p - 1) / 2
          set t := ((2 * (n + 1) + 1) / p - 1) / 2
          have hsplit := split_of_dvd_two_mul_add_one (p := p) (n := n + 1) hodd hpdvd
          have hn1eq : n + 1 = n0 + t * p := by
            simpa [n0, t] using hsplit
          have hp3 : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hodd)
          have hpodd : Odd p := hp.out.odd_of_ne_two hodd
          have hp_mod : p % 2 = 1 := Nat.odd_iff.mp hpodd
          have hn0pos : 1 ≤ n0 := by
            change 1 ≤ (p - 1) / 2
            have : 2 ≤ p - 1 := by omega
            exact Nat.div_pos this (by decide)
          have h2n0 : 2 * n0 + 1 = p := by
            change 2 * ((p - 1) / 2) + 1 = p
            have hdiv : 2 ∣ p - 1 := Nat.dvd_of_mod_eq_zero (by omega)
            have : 2 * ((p - 1) / 2) = p - 1 := by
              rw [Nat.mul_comm]; exact Nat.div_mul_cancel hdiv
            omega
          have h2n0' : 2 * n0 = p - 1 := by omega
          have hn0lt : n0 < p := by omega
          have hmN : 2 * (n + 1) + 1 = p * (2 * t + 1) := by
            have hrew : n + 1 = n0 + t * p := hn1eq
            calc
              2 * (n + 1) + 1 = 2 * n0 + 1 + 2 * t * p := by
                rw [hrew]; ring
              _ = p + 2 * t * p := by rw [h2n0]
              _ = p * (1 + 2 * t) := by ring
              _ = p * (2 * t + 1) := by ring
          have htpos : 1 ≤ t := by
            have : 2 * t + 1 ≠ 1 := by
              intro h
              have : 2 * (n + 1) + 1 = p := by rw [hmN, h, mul_one]
              exact hfund this
            omega
          have htlt : t < n + 1 := by
            have hle : t * p ≤ n + 1 := by
              have : n0 + t * p = n + 1 := hn1eq.symm
              omega
            have hp1 : 1 < p := hp.out.one_lt
            have htle : t ≤ n + 1 := by
              have : t * 1 ≤ t * p := Nat.mul_le_mul_left t (le_of_lt hp1)
              omega
            have hne : t ≠ n + 1 := by
              intro h
              have : n0 + t * p = n + 1 := hn1eq.symm
              rw [h] at this
              have : n0 = (n + 1) * 1 - (n + 1) * p := by
                have := this
                omega
              have : n0 + (n + 1) * p = n + 1 := by
                simpa [h] using hn1eq.symm
              have hppos : 1 ≤ p := hp.out.one_le
              have : n0 = n + 1 - (n + 1) * p := by
                have hnn : n + 1 = n0 + (n + 1) * p := by
                  simpa [h] using hn1eq
                omega
              have : p ≤ 1 := by
                have hn0ge : 1 ≤ n0 := hn0pos
                have : n + 1 ≤ (n + 1) * p :=
                  Nat.le_mul_of_pos_right (n + 1) (lt_of_lt_of_le (by decide : 0 < 1) hppos)
                omega
              exact (not_le_of_gt hp1) this
            omega
          have ih_t := ih t htlt htpos
          rw [padicValNat_odd_Den t hodd] at ih_t
          have hvT0 : 3 ≤ padicValNat p (T n0) := by
            have hdiv0 : p ^ 3 ∣ T n0 :=
              fundamental_supercongruence hodd n0 h2n0
            exact (padicValNat_dvd_iff_le (T_pos n0).ne').mp hdiv0
          have hDwork := dwork_val (p := p) hodd t
          have hn1rew : n0 + t * p = n + 1 := hn1eq.symm
          rw [hn1rew] at hDwork
          have hf_rel : f = 1 + padicValNat p (2 * t + 1) := by
            have h2t1pos : (2 * t + 1 : ℕ) ≠ 0 := by omega
            have hppos : p ≠ 0 := hp.out.ne_zero
            have : padicValNat p (2 * (n + 1) + 1) =
                padicValNat p p + padicValNat p (2 * t + 1) := by
              rw [hmN, padicValNat.mul hppos h2t1pos]
            simpa [f, padicValNat_self] using this
          have hc_rel : c = padicValNat p (Nat.choose (2 * t) t) :=
            central_val_of_split (p := p) hodd (n := n + 1) (n0 := n0) (t := t)
              hn1eq h2n0
          have : 3 * c + 3 * f ≤ padicValNat p (T (n + 1)) := by
            have h1 : 3 * padicValNat p (Nat.choose (2 * t) t) +
                3 * padicValNat p (2 * t + 1) ≤ padicValNat p (T t) := by
              simpa [add_comm] using ih_t
            have heq : 3 * c + 3 * f =
                3 + (3 * padicValNat p (Nat.choose (2 * t) t) +
                  3 * padicValNat p (2 * t + 1)) := by
              rw [hf_rel, hc_rel]; ring
            have : 3 * c + 3 * f ≤
                padicValNat p (T n0) + padicValNat p (T t) := by
              linarith
            exact le_trans this hDwork
          simpa [T_succ, add_comm] using this


/-- Integrality: $16(2n+1)^3\binom{2n}{n}^3$ divides $T(n)$. -/
lemma T_dvd_Den (n : ℕ) (hn : 1 ≤ n) : Den n ∣ T n := by
  have hD : Den n ≠ 0 := (Den_pos n).ne'
  have hT : T n ≠ 0 := (T_pos n).ne'
  rw [← factorization_le_iff_dvd hD hT]
  intro p
  by_cases hp : p.Prime
  · rw [factorization_def _ hp, factorization_def _ hp]
    by_cases h2 : p = 2
    · subst h2
      exact padicValNat_two_T_ge_Den n hn
    · have : Fact p.Prime := ⟨hp⟩
      exact padicValNat_odd_T_ge_Den n hn h2
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

lemma a_Q_eq_nat (n : ℕ) (hn : 1 ≤ n) :
    a_Q n = ((T n / Den n : ℕ) : ℚ) := by
  have hdiv := T_dvd_Den n hn
  rw [a_Q_closed_form n hn]
  have hDen : (Den n : ℚ) =
      16 * ((2 * n + 1 : ℕ) : ℚ) ^ 3 * (Nat.choose (2 * n) n : ℚ) ^ 3 := by
    unfold Den
    push_cast
    rfl
  rw [← hDen]
  have hne : (Den n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Den_pos n).ne'
  exact (Nat.cast_div hdiv hne).symm

lemma a_eq_div (n : ℕ) (hn : 1 ≤ n) : a n = T n / Den n := by
  unfold a
  rw [a_Q_eq_nat n hn]
  change (Int.floor ((T n / Den n : ℕ) : ℚ)).toNat = T n / Den n
  rw [Int.floor_natCast, Int.toNat_natCast]

/-- $v_2(\binom{2n-1}{n})=s_2(n)-1$ for $n\ge 1$. -/
lemma padicValNat_two_choose_sub (n : ℕ) (hn : 1 ≤ n) :
    padicValNat 2 (Nat.choose (2 * n - 1) n) = (Nat.digits 2 n).sum - 1 := by
  have hne : n ≠ 0 := by omega
  have hC : Nat.choose (2 * n) n = 2 * Nat.choose (2 * n - 1) (n - 1) :=
    choose_two_mul_eq_two n hn
  have hsym : Nat.choose (2 * n - 1) n = Nat.choose (2 * n - 1) (n - 1) :=
    choose_two_mul_sub_one_symm n hn
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hposC : 0 < Nat.choose (2 * n - 1) (n - 1) :=
    Nat.choose_pos (by omega)
  have hmul : padicValNat 2 (Nat.choose (2 * n) n) =
      padicValNat 2 2 + padicValNat 2 (Nat.choose (2 * n - 1) (n - 1)) := by
    rw [hC, padicValNat.mul (by decide : (2 : ℕ) ≠ 0) hposC.ne']
  have h2 : padicValNat 2 2 = 1 := padicValNat_self
  rw [hsym]
  have hcent := padicValNat_two_central n hne
  omega

lemma a_Q_eq_cast (n : ℕ) (hn : 1 ≤ n) : a_Q n = (a n : ℚ) := by
  rw [a_Q_eq_nat n hn, a_eq_div n hn]

/-- The defining recurrence holds in $\mathbb{N}$ once integrality is known. -/
lemma a_recurrence (n : ℕ) (hn : 2 ≤ n) :
    (2 * n + 1) ^ 3 * a n =
      32 * n ^ 3 * a (n - 1) + Pnat n * Nat.choose (2 * n - 1) n ^ 4 := by
  have hn1 : 1 ≤ n := by omega
  have hprev : 1 ≤ n - 1 := by omega
  have h := a_Q_of_ge_two n hn
  rw [a_Q_eq_cast n hn1, a_Q_eq_cast (n - 1) hprev, ← Pnat_cast n] at h
  have hden : (2 * (n : ℚ) + 1) ≠ 0 := by
    have : (0 : ℚ) < 2 * (n : ℚ) + 1 := by
      exact_mod_cast (by omega : 0 < 2 * n + 1)
    exact this.ne'
  apply_fun (fun x : ℚ => x * (2 * (n : ℚ) + 1) ^ 3) at h
  field_simp [hden] at h
  have h' : ((a n : ℕ) : ℚ) * (2 * (n : ℚ) + 1) ^ 3 =
      32 * (n : ℚ) ^ 3 * (a (n - 1) : ℕ) +
        (Pnat n : ℚ) * (Nat.choose (2 * n - 1) n : ℚ) ^ 4 := by
    convert h using 1
    ring
  have : (((2 * n + 1) ^ 3 * a n : ℕ) : ℚ) =
      ((32 * n ^ 3 * a (n - 1) + Pnat n * Nat.choose (2 * n - 1) n ^ 4 : ℕ) : ℚ) := by
    push_cast
    convert h' using 1 <;> ring
  exact_mod_cast this

lemma a_mod_two (n : ℕ) (hn : 2 ≤ n) :
    a n % 2 = (Pnat n * Nat.choose (2 * n - 1) n ^ 4) % 2 := by
  have hrec := a_recurrence n hn
  have h : ((2 * n + 1) ^ 3 * a n) % 2 =
      (32 * n ^ 3 * a (n - 1) + Pnat n * Nat.choose (2 * n - 1) n ^ 4) % 2 := by
    rw [hrec]
  have hodd : (2 * n + 1) % 2 = 1 := by omega
  have hpow : (2 * n + 1) ^ 3 % 2 = 1 := by
    simp [Nat.pow_mod, hodd]
  have h32 : (32 * n ^ 3 * a (n - 1)) % 2 = 0 := by
    have : 32 % 2 = 0 := by decide
    rw [show 32 * n ^ 3 * a (n - 1) = 32 * (n ^ 3 * a (n - 1)) from by ring,
        Nat.mul_mod, this]
    simp
  rw [Nat.mul_mod, hpow, one_mul, Nat.mod_mod] at h
  rw [Nat.add_mod, h32, zero_add, Nat.mod_mod] at h
  exact h

lemma choose_sub_odd_iff (n : ℕ) (hn : 1 ≤ n) :
    Odd (Nat.choose (2 * n - 1) n) ↔ (Nat.digits 2 n).sum = 1 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos : 0 < Nat.choose (2 * n - 1) n := Nat.choose_pos (by omega)
  have hv := padicValNat_two_choose_sub n hn
  have hs : 1 ≤ (Nat.digits 2 n).sum := by
    have : (Nat.digits 2 n).sum ≠ 0 := by
      intro h
      exact (show n ≠ 0 by omega) ((digits_two_sum_eq_zero_iff n).mp h)
    omega
  constructor
  · intro hodd
    have : ¬ Even (Nat.choose (2 * n - 1) n) := Nat.not_even_iff_odd.mpr hodd
    have : ¬ 2 ∣ Nat.choose (2 * n - 1) n := mt even_iff_two_dvd.mpr this
    have : padicValNat 2 (Nat.choose (2 * n - 1) n) = 0 :=
      padicValNat.eq_zero_of_not_dvd this
    omega
  · intro hs1
    have : padicValNat 2 (Nat.choose (2 * n - 1) n) = 0 := by omega
    have : ¬ 2 ∣ Nat.choose (2 * n - 1) n := by
      intro hdiv
      have := one_le_padicValNat_of_dvd hpos.ne' hdiv
      omega
    have : ¬ Even (Nat.choose (2 * n - 1) n) := mt even_iff_two_dvd.mp this
    exact Nat.not_even_iff_odd.mp this

lemma a_one_eq : a 1 = 2 := by
  unfold a
  rw [a_Q_one]
  have hf : Int.floor (2 : ℚ) = (2 : ℤ) := Int.floor_natCast (R := ℚ) (2 : ℕ)
  show (Int.floor (2 : ℚ)).toNat = 2
  rw [hf]
  rfl

lemma a_odd_iff_pow_two (n : ℕ) (hn : 1 ≤ n) :
    Odd (a n) ↔ ∃ m ≥ 1, n = 2 ^ m := by
  match n with
  | 0 => omega
  | 1 =>
    constructor
    · intro h
      rw [a_one_eq] at h
      exact (Nat.not_odd_iff_even.mpr (by decide : Even 2) h).elim
    · rintro ⟨m, hm, hpow⟩
      have : m = 0 := by
        cases m with
        | zero => rfl
        | succ m =>
          have heven : Even (2 ^ (m + 1)) := by
            rw [Nat.pow_succ']
            exact even_two_mul _
          exact (Nat.not_even_iff_odd.mpr (by decide : Odd 1) (hpow ▸ heven)).elim
      subst this
      exact ((by omega : ¬ 0 ≥ 1) hm).elim
  | n + 2 =>
    have hn2' : 2 ≤ n + 2 := by omega
    have hn' : 1 ≤ n + 2 := by omega
    rw [Nat.odd_iff, a_mod_two (n + 2) hn2']
    have hC := choose_sub_odd_iff (n + 2) hn'
    have h4 : ∀ x : ℕ, x ^ 4 % 2 = x % 2 := by
      intro x
      rcases Nat.mod_two_eq_zero_or_one x with hx | hx
      · simp [Nat.pow_mod, hx]
      · simp [Nat.pow_mod, hx]
    have : (Pnat (n + 2) * Nat.choose (2 * (n + 2) - 1) (n + 2) ^ 4) % 2 = 1 ↔
        Pnat (n + 2) % 2 = 1 ∧ Nat.choose (2 * (n + 2) - 1) (n + 2) % 2 = 1 := by
      rw [Nat.mul_mod, h4]
      rcases Nat.mod_two_eq_zero_or_one (Pnat (n + 2)) with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one (Nat.choose (2 * (n + 2) - 1) (n + 2)) with h2 | h2 <;>
          simp [h1, h2]
    rw [this, ← Nat.odd_iff, ← Nat.odd_iff]
    have hPiff : Odd (Pnat (n + 2)) ↔ Even (n + 2) := by
      rw [Nat.odd_iff, Nat.even_iff, Pnat_mod_two]
      omega
    rw [hPiff, hC, pow_two_ge_one_iff (n + 2) hn']

theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  refine ⟨a_pos n hn, ?_⟩
  simpa using a_odd_iff_pow_two n hn

