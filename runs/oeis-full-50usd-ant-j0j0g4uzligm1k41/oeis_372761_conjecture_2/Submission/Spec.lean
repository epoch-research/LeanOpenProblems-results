import FormalConjectures.Util.ProblemImports

open Rat

/--
Recursive function to compute $A_k(n)$, the denominator tail $k - \frac{k+1}{A_{k+1}(n)}$.
The base case is at $k = n - 1$, where $A_{n-1} = (n-1) - \frac{n}{n+4}$.
-/
noncomputable def continued_fraction_tail (n : ℕ) : ℕ → ℚ
| k =>
  if n ≥ 4 then
    if k = n - 1 then
      (n - 1 : ℚ) - (n : ℚ) / (n + 4 : ℚ)
    else if 3 ≤ k ∧ k < n - 1 then
      let k_succ_val := continued_fraction_tail n (k + 1)
      -- Division by zero handling for total function definition
      if k_succ_val = 0 then 0 else
        (k : ℚ) - (k + 1 : ℚ) / k_succ_val
    else
      0
  else
    0
termination_by k => n - k

/--
The total value of the continued fraction $C_n$.
-/
noncomputable def continued_fraction_val (n : ℕ) : ℚ :=
  if n ≤ 2 then
    0
  else if n = 3 then
    -- Formula for n=3: 1 / (2 - 3 / (3 + 4)) = 7/11
    let val : ℚ := 2 - 3 / 7
    if val = 0 then 0 else 1 / val
  else -- n ≥ 4
    let A3 := continued_fraction_tail n 3
    let val : ℚ := 2 - 3 / A3

    -- Division by zero check for the final rational value
    if val = 0 then 0 else 1 / val

/--
A372761: Denominator of the continued fraction
$$ \frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{n+4}}}}}} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n < 3 then 0 -- Sequence starts at n=3.
  else (continued_fraction_val n).den

/--
Conjecture 2: Except for 3 and 5, all odd primes appear in the sequence once.
Formally: for every natural number $p$ that is an odd prime and $p \ne 3$ and $p \ne 5$,
there is exactly one index $n \ge 3$ such that $a(n) = p$.
-/

noncomputable def B (n : ℕ) : ℕ → ℤ
| k =>
  if k + 1 < n then
    (k : ℤ) * B n (k + 1) - ((k : ℤ) + 1) * B n (k + 2)
  else if k + 1 = n then
    (n : ℤ) ^ 2 + 2 * (n : ℤ) - 4
  else
    (k : ℤ) + 4
termination_by k => n - k
decreasing_by all_goals omega

-- unfolding lemmas
lemma B_rec (n k : ℕ) (h : k + 1 < n) :
    B n k = (k : ℤ) * B n (k + 1) - ((k : ℤ) + 1) * B n (k + 2) := by
  rw [B]; simp [h]

lemma B_base (n k : ℕ) (h : k + 1 = n) :
    B n k = (n : ℤ) ^ 2 + 2 * (n : ℤ) - 4 := by
  rw [B]
  have h1 : ¬ (k + 1 < n) := by omega
  simp [h1, h]

lemma B_top (n k : ℕ) (h : n ≤ k) :
    B n k = (k : ℤ) + 4 := by
  rw [B]
  have h1 : ¬ (k + 1 < n) := by omega
  have h2 : ¬ (k + 1 = n) := by omega
  simp [h1, h2]

/-- W-invariant, proved by induction on the "fuel" i = distance from the top n-1. -/
lemma Winv_aux (n : ℕ) (hn : 4 ≤ n) :
    ∀ i k, k + i = n - 1 → 2 ≤ k →
      ((k : ℤ) - 1) * B n k - (k : ℤ) * ((k : ℤ) - 2) * B n (k + 1) = 5 * (n : ℤ) - 4 := by
  intro i
  induction i with
  | zero =>
    intro k hk hk2
    -- k = n - 1
    have hkn : k = n - 1 := by omega
    have hk1 : k + 1 = n := by omega
    have e1 : B n k = (n : ℤ) ^ 2 + 2 * (n : ℤ) - 4 := B_base n k hk1
    have e2 : B n (k + 1) = (n : ℤ) + 4 := by
      rw [B_top n (k + 1) (by omega), hk1]
    rw [e1, e2]
    have : (k : ℤ) = (n : ℤ) - 1 := by
      have : k = n - 1 := hkn
      omega
    rw [this]; ring
  | succ i ih =>
    intro k hk hk2
    -- k + (i+1) = n-1, so k+1 ≤ n-1 and (k+1)+i = n-1
    have hkn : k + 1 < n := by omega
    have step : (k + 1) + i = n - 1 := by omega
    have ihk : (((k + 1 : ℕ) : ℤ) - 1) * B n (k + 1)
        - ((k + 1 : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ) - 2) * B n ((k + 1) + 1) = 5 * (n : ℤ) - 4 :=
      ih (k + 1) step (by omega)
    have hBk : B n k = (k : ℤ) * B n (k + 1) - ((k : ℤ) + 1) * B n (k + 2) := B_rec n k hkn
    push_cast at ihk ⊢
    rw [hBk]
    -- both reduce to same expression; use ihk
    have hkk : k + 1 + 1 = k + 2 := by ring
    rw [hkk] at ihk
    linear_combination ihk

lemma Winv (n : ℕ) (hn : 4 ≤ n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 1) :
    ((k : ℤ) - 1) * B n k - (k : ℤ) * ((k : ℤ) - 2) * B n (k + 1) = 5 * (n : ℤ) - 4 :=
  Winv_aux n hn (n - 1 - k) k (by omega) hk2

/-- B n 2 = 5n - 4. -/
lemma B2 (n : ℕ) (hn : 4 ≤ n) : B n 2 = 5 * (n : ℤ) - 4 := by
  have := Winv n hn 2 (le_refl 2) (by omega)
  simpa using this

/-- Positivity of B, by downward induction using the W-invariant. -/
lemma B_pos (n : ℕ) (hn : 4 ≤ n) :
    ∀ i k, k + i = n - 1 → 2 ≤ k → 0 < B n k := by
  intro i
  induction i with
  | zero =>
    intro k hk hk2
    have hk1 : k + 1 = n := by omega
    rw [B_base n k hk1]
    have : (2:ℤ) ≤ (n:ℤ) := by exact_mod_cast (by omega : 2 ≤ n)
    nlinarith [this]
  | succ i ih =>
    intro k hk hk2
    have hkn : k + 1 < n := by omega
    have hpos1 : 0 < B n (k + 1) := ih (k + 1) (by omega) (by omega)
    -- from W: (k-1) B k = 5n-4 + k(k-2) B(k+1)
    have hW := Winv n hn k hk2 (by omega)
    have hk1 : (1:ℤ) ≤ (k:ℤ) - 1 := by
      have : (2:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk2
      linarith
    have hk0 : (0:ℤ) ≤ (k:ℤ) * ((k:ℤ) - 2) := by
      have h2 : (2:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk2
      nlinarith
    have hn5 : (0:ℤ) < 5 * (n:ℤ) - 4 := by
      have : (4:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
      linarith
    -- (k-1) B k = 5n-4 + k(k-2) B(k+1) > 0, and k-1 ≥ 1 > 0, so B k > 0
    have key : ((k:ℤ) - 1) * B n k = (5 * (n:ℤ) - 4) + (k:ℤ) * ((k:ℤ) - 2) * B n (k+1) := by
      linarith [hW]
    have hrhs : 0 < ((k:ℤ) - 1) * B n k := by
      rw [key]
      have : 0 ≤ (k:ℤ) * ((k:ℤ) - 2) * B n (k+1) := by positivity
      linarith
    -- k-1 > 0 and product positive => B k > 0
    nlinarith [hrhs, hk1]

lemma B_pos' (n : ℕ) (hn : 4 ≤ n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 1) : 0 < B n k :=
  B_pos n hn (n - 1 - k) k (by omega) hk2

lemma B_pos_top (n : ℕ) (hn : 4 ≤ n) : 0 < B n n := by
  rw [B_top n n (le_refl n)]
  have : (0:ℤ) ≤ (n:ℤ) := by positivity
  linarith

lemma B_ne_zero (n : ℕ) (hn : 4 ≤ n) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n - 1) :
    (B n k : ℚ) ≠ 0 := by
  have := B_pos' n hn k hk2 hkn
  exact_mod_cast this.ne'

lemma B_top_ne_zero (n : ℕ) (hn : 4 ≤ n) : (B n n : ℚ) ≠ 0 := by
  have := B_pos_top n hn
  exact_mod_cast this.ne'

lemma B_ne_zero' (n : ℕ) (hn : 4 ≤ n) (j : ℕ) (hj2 : 2 ≤ j) (hjn : j ≤ n) :
    (B n j : ℚ) ≠ 0 := by
  rcases eq_or_lt_of_le hjn with h | h
  · rw [h]; exact B_top_ne_zero n hn
  · exact B_ne_zero n hn j hj2 (by omega)

/-- Connection: tail = ratio of consecutive B. -/
lemma tail_eq (n : ℕ) (hn : 4 ≤ n) :
    ∀ i k, k + i = n - 1 → 3 ≤ k →
      continued_fraction_tail n k = (B n k : ℚ) / (B n (k + 1) : ℚ) := by
  intro i
  induction i with
  | zero =>
    intro k hk hk3
    have hk1 : k + 1 = n := by omega
    have hkn1 : k = n - 1 := by omega
    rw [continued_fraction_tail, if_pos hn, if_pos hkn1]
    have e1 : (B n k : ℚ) = (n : ℚ) ^ 2 + 2 * (n : ℚ) - 4 := by
      rw [B_base n k hk1]; push_cast; ring
    have e2 : (B n (k + 1) : ℚ) = (n : ℚ) + 4 := by
      rw [B_top n (k + 1) (by omega), hk1]; push_cast; ring
    rw [e1, e2]
    have h4 : (n : ℚ) + 4 ≠ 0 := by
      have : (0:ℚ) ≤ (n:ℚ) := by positivity
      intro h; linarith
    field_simp
    ring
  | succ i ih =>
    intro k hk hk3
    have hkn : k + 1 < n := by omega
    have hklt : k < n - 1 := by omega
    have ihk : continued_fraction_tail n (k + 1) = (B n (k + 1) : ℚ) / (B n (k + 2) : ℚ) :=
      ih (k + 1) (by omega) (by omega)
    -- unfold tail at k
    have hcond : ¬ (k = n - 1) := by omega
    have hcond2 : 3 ≤ k ∧ k < n - 1 := ⟨hk3, hklt⟩
    rw [continued_fraction_tail, if_pos hn, if_neg hcond, if_pos hcond2]
    -- now it's: let ks := tail(k+1); if ks = 0 then 0 else k - (k+1)/ks
    have hb1 : (B n (k + 1) : ℚ) ≠ 0 := B_ne_zero' n hn (k + 1) (by omega) (by omega)
    have hb2 : (B n (k + 2) : ℚ) ≠ 0 := B_ne_zero' n hn (k + 2) (by omega) (by omega)
    have hks_ne : (B n (k + 1) : ℚ) / (B n (k + 2) : ℚ) ≠ 0 := div_ne_zero hb1 hb2
    simp only [ihk, if_neg hks_ne]
    -- goal: (k:ℚ) - (k+1)/(B(k+1)/B(k+2)) = B k / B(k+1)
    have hBk : (B n k : ℚ) = (k : ℚ) * (B n (k + 1) : ℚ) - ((k : ℚ) + 1) * (B n (k + 2) : ℚ) := by
      rw [B_rec n k hkn]; push_cast; ring
    rw [hBk]
    field_simp

/-- The full continued fraction value equals B(n,3)/(5n-4). -/
lemma val_eq (n : ℕ) (hn : 4 ≤ n) :
    continued_fraction_val n = (B n 3 : ℚ) / ((5 * (n : ℤ) - 4 : ℤ) : ℚ) := by
  have hA3 : continued_fraction_tail n 3 = (B n 3 : ℚ) / (B n 4 : ℚ) := by
    have := tail_eq n hn (n - 4) 3 (by omega) (by omega)
    simpa using this
  have hb3 : (B n 3 : ℚ) ≠ 0 := B_ne_zero' n hn 3 (by omega) (by omega)
  have hb4 : (B n 4 : ℚ) ≠ 0 := B_ne_zero' n hn 4 (by omega) (by omega)
  -- W at k=3: 2 B3 - 3 B4 = 5n-4
  have hW := Winv n hn 3 (by omega) (by omega)
  have hW' : 2 * (B n 3 : ℚ) - 3 * (B n 4 : ℚ) = 5 * (n : ℚ) - 4 := by
    have : ((2 : ℤ) * B n 3 - 3 * B n 4 : ℤ) = 5 * (n : ℤ) - 4 := by
      have : ((3:ℤ) - 1) * B n 3 - (3:ℤ) * ((3:ℤ) - 2) * B n 4 = 5 * (n:ℤ) - 4 := by
        simpa using hW
      linarith [this]
    have := congrArg (fun z : ℤ => (z : ℚ)) this
    push_cast at this
    linarith [this]
  rw [continued_fraction_val]
  have h1 : ¬ (n ≤ 2) := by omega
  have h2 : ¬ (n = 3) := by omega
  rw [if_neg h1, if_neg h2]
  simp only [hA3]
  -- val = 2 - 3/(B3/B4)
  have hval : (2 : ℚ) - 3 / ((B n 3 : ℚ) / (B n 4 : ℚ)) = (5 * (n:ℚ) - 4) / (B n 3 : ℚ) := by
    rw [div_div_eq_mul_div]
    field_simp
    linarith [hW']
  rw [hval]
  have hvpos : (5 * (n:ℚ) - 4) / (B n 3 : ℚ) ≠ 0 := by
    apply div_ne_zero
    · have : (4:ℚ) ≤ (n:ℚ) := by exact_mod_cast hn
      intro h; linarith
    · exact hb3
  rw [if_neg hvpos]
  rw [one_div_div]
  push_cast
  rfl

/-- Denominator formula: a n = (5n-4) / gcd(B n 3, 5n-4). -/
lemma a_eq (n : ℕ) (hn : 4 ≤ n) :
    a n = (5 * n - 4) / Nat.gcd (B n 3).natAbs (5 * n - 4) := by
  have hden : (continued_fraction_val n).den
      = (5 * (n : ℤ) - 4).natAbs / (5 * (n : ℤ) - 4).gcd (B n 3) := by
    rw [val_eq n hn, ← Rat.divInt_eq_div, Rat.den_divInt]
    have hb : (5 * (n : ℤ) - 4) ≠ 0 := by
      have : (4:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
      intro h; linarith
    rw [if_neg hb]
  unfold a
  rw [if_neg (by omega : ¬ n < 3)]
  rw [hden]
  have hnat : (5 * (n : ℤ) - 4).natAbs = 5 * n - 4 := by
    have : (5 * (n : ℤ) - 4) = ((5 * n - 4 : ℕ) : ℤ) := by
      have : 4 ≤ 5 * n := by omega
      push_cast [Nat.cast_sub this]; ring
    rw [this, Int.natAbs_natCast]
  rw [hnat]
  congr 1
  -- Int.gcd (5n-4) (B n 3) = Nat.gcd (B n 3).natAbs (5n-4)
  unfold Int.gcd
  rw [hnat, Nat.gcd_comm]

open Nat

/-- P k := (k-3)! * (k-1) * B n k.  Step difference. -/
lemma Pstep (n : ℕ) (hn : 5 ≤ n) (k : ℕ) (hk3 : 3 ≤ k) (hkn : k ≤ n - 2) :
    (((k - 3)! : ℕ) : ℤ) * ((k : ℤ) - 1) * B n k
      - (((k - 2)! : ℕ) : ℤ) * (k : ℤ) * B n (k + 1)
      = (((k - 3)! : ℕ) : ℤ) * (5 * (n : ℤ) - 4) := by
  have hW := Winv n (by omega) k (by omega) (by omega)
  -- (k-2)! = (k-2)*(k-3)!
  have hfac : ((k - 2)! : ℕ) = (k - 2) * (k - 3)! := by
    have h1 : k - 2 = (k - 3) + 1 := by omega
    rw [h1, Nat.factorial_succ]
  have hfac' : (((k - 2)! : ℕ) : ℤ) = ((k : ℤ) - 2) * (((k - 3)! : ℕ) : ℤ) := by
    rw [hfac]
    have h2 : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by
      have : 2 ≤ k := by omega
      push_cast [Nat.cast_sub this]; ring
    push_cast; rw [h2]
  rw [hfac']
  -- goal: (k-3)!*(k-1)*Bk - (k-2)*(k-3)!*k*B(k+1) = (k-3)!*(5n-4)
  have key : ((k : ℤ) - 1) * B n k - ((k : ℤ) - 2) * (k : ℤ) * B n (k + 1) = 5 * (n : ℤ) - 4 := by
    have h2 : (k : ℤ) * ((k : ℤ) - 2) = ((k : ℤ) - 2) * (k : ℤ) := by ring
    linarith [hW]
  linear_combination (((k - 3)! : ℕ) : ℤ) * key

/-- Divisibility form of identity (A): 5n-4 divides 2 B3 - (n-2)(n-4)!(n^2+2n-4). -/
lemma DA_aux (n : ℕ) (hn : 5 ≤ n) : ∀ i k, k + i = n - 1 → 3 ≤ k →
    (5 * (n : ℤ) - 4) ∣
      ((((k - 3)! : ℕ) : ℤ) * ((k : ℤ) - 1) * B n k
        - (((n - 4)! : ℕ) : ℤ) * ((n : ℤ) - 2) * ((n : ℤ) ^ 2 + 2 * (n : ℤ) - 4)) := by
  intro i
  induction i with
  | zero =>
    intro k hk hk3
    have hk1 : k + 1 = n := by omega
    have hb : B n k = (n : ℤ) ^ 2 + 2 * (n : ℤ) - 4 := B_base n k hk1
    have hk3n : k - 3 = n - 4 := by omega
    have hkm1 : ((k : ℤ) - 1) = (n : ℤ) - 2 := by
      have : k = n - 1 := by omega
      have h1 : 1 ≤ n := by omega
      omega
    rw [hb, hk3n, hkm1]
    convert dvd_zero (5 * (n : ℤ) - 4) using 1
    ring
  | succ i ih =>
    intro k hk hk3
    have hkn2 : k ≤ n - 2 := by omega
    have step := Pstep n hn k hk3 hkn2
    have ihk := ih (k + 1) (by omega) (by omega)
    -- P k - Pconst = (P k - P(k+1)) + (P(k+1) - Pconst)
    have hsplit :
        (((k - 3)! : ℕ) : ℤ) * ((k : ℤ) - 1) * B n k
          - (((n - 4)! : ℕ) : ℤ) * ((n : ℤ) - 2) * ((n : ℤ) ^ 2 + 2 * (n : ℤ) - 4)
        = ((((k - 3)! : ℕ) : ℤ) * ((k : ℤ) - 1) * B n k
            - (((k - 2)! : ℕ) : ℤ) * (k : ℤ) * B n (k + 1))
          + ((((k + 1 - 3)! : ℕ) : ℤ) * (((k : ℤ) + 1) - 1) * B n (k + 1)
            - (((n - 4)! : ℕ) : ℤ) * ((n : ℤ) - 2) * ((n : ℤ) ^ 2 + 2 * (n : ℤ) - 4)) := by
      have e : k + 1 - 3 = k - 2 := by omega
      rw [e]; push_cast; ring
    rw [hsplit]
    apply dvd_add
    · rw [step]; exact dvd_mul_left _ _
    · exact ihk

/-- Identity (A) as divisibility, at k=3. -/
lemma DA (n : ℕ) (hn : 5 ≤ n) :
    (5 * (n : ℤ) - 4) ∣
      (2 * B n 3 - (((n - 4)! : ℕ) : ℤ) * ((n : ℤ) - 2) * ((n : ℤ) ^ 2 + 2 * (n : ℤ) - 4)) := by
  have h := DA_aux n hn (n - 1 - 3) 3 (by omega) (by omega)
  norm_num at h
  convert h using 2

/-- Factorial expansion (n-1)! = (n-1)(n-2)(n-3)(n-4)!. -/
lemma fact_exp (n : ℕ) (hn : 5 ≤ n) :
    ((n - 1)! : ℕ) = (n - 1) * (n - 2) * (n - 3) * (n - 4)! := by
  have f1 : (n - 1)! = (n - 1) * (n - 2)! := by
    rw [show n - 1 = (n - 2) + 1 from by omega, Nat.factorial_succ]
  have f2 : (n - 2)! = (n - 2) * (n - 3)! := by
    rw [show n - 2 = (n - 3) + 1 from by omega, Nat.factorial_succ]
  have f3 : (n - 3)! = (n - 3) * (n - 4)! := by
    rw [show n - 3 = (n - 4) + 1 from by omega, Nat.factorial_succ]
  rw [f1, f2, f3]; ring

/-- Identity (B) as divisibility: 5n-4 divides 2(n-2) B3 - (n+4)(n-1)!. -/
lemma DB (n : ℕ) (hn : 5 ≤ n) :
    (5 * (n : ℤ) - 4) ∣
      (2 * ((n : ℤ) - 2) * B n 3 - ((n : ℤ) + 4) * (((n - 1)! : ℕ) : ℤ)) := by
  have hDA := (DA n hn).mul_left ((n : ℤ) - 2)
  -- polynomial identity relating the two
  have hfe : (((n - 1)! : ℕ) : ℤ) = ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) * (((n - 4)! : ℕ) : ℤ) := by
    rw [fact_exp n hn]
    have c1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
    have c2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by push_cast [Nat.cast_sub (by omega : 2 ≤ n)]; ring
    have c3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by push_cast [Nat.cast_sub (by omega : 3 ≤ n)]; ring
    push_cast [c1, c2, c3]; ring
  -- the extra divisible term
  have hextra : (5 * (n : ℤ) - 4) ∣
      (((n : ℤ) - 2) * ((((n - 4)! : ℕ) : ℤ) * ((n : ℤ) - 2) * ((n : ℤ) ^ 2 + 2 * (n : ℤ) - 4))
        - ((n : ℤ) + 4) * (((n - 1)! : ℕ) : ℤ)) := by
    rw [hfe]
    exact ⟨((n : ℤ) - 2) * (((n - 4)! : ℕ) : ℤ), by ring⟩
  have := dvd_add hDA hextra
  convert this using 1
  ring

lemma pow7_bound : ∀ e, 3 ≤ e → 5 * e ≤ 7 ^ (e - 1) := by
  intro e he
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih =>
    have h1 : e - 1 + 1 = e := by omega
    have : (7:ℕ) ^ (e + 1 - 1) = 7 * 7 ^ (e - 1) := by
      rw [show e + 1 - 1 = (e - 1) + 1 from by omega, pow_succ]; ring
    rw [this]
    have : 5 * e ≤ 7 ^ (e - 1) := ih
    nlinarith [this]

/-- Key Lemma: for prime p ≥ 7 with p^e | 5n-4, p ≤ n-1, n ≥ 5, we have p^e | (n-1)!. -/
lemma KL (p n e : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hn : 5 ≤ n) (hpn : p ≤ n - 1)
    (hdvd : p ^ e ∣ (5 * n - 4)) : p ^ e ∣ (n - 1)! := by
  rcases Nat.eq_zero_or_pos e with he0 | he1
  · simp [he0]
  -- Step 1: e ≤ (n-1)/p
  have hD : e ≤ (n - 1) / p := by
    by_contra hc
    push_neg at hc  -- (n-1)/p < e
    have hp0 : 0 < p := by omega
    have hlt : n - 1 < e * p := (Nat.div_lt_iff_lt_mul hp0).mp hc
    have hnep : n ≤ e * p := by omega
    have hpe_le : p ^ e ≤ 5 * n - 4 := Nat.le_of_dvd (by omega) hdvd
    have h5 : p ^ e < 5 * (e * p) := by omega
    -- p^e = p * p^(e-1)
    have hsplit : p ^ e = p * p ^ (e - 1) := by
      rw [← _root_.pow_succ']; congr 1; omega
    have hpe1 : p ^ (e - 1) < 5 * e := by
      rw [hsplit] at h5
      have heq : 5 * (e * p) = p * (5 * e) := by ring
      rw [heq] at h5
      exact Nat.lt_of_mul_lt_mul_left h5
    -- bound e
    have he2 : e ≤ 2 := by
      by_contra he3
      push_neg at he3  -- e ≥ 3
      have hb := pow7_bound e (by omega)
      have : (7:ℕ) ^ (e - 1) ≤ p ^ (e - 1) := Nat.pow_le_pow_left (by omega) _
      omega
    interval_cases e
    · -- e = 1: (n-1)/p < 1 → n-1 < p, contra
      have : n - 1 < p := by
        have := (Nat.div_lt_iff_lt_mul hp0).mp hc
        omega
      omega
    · -- e = 2
      have hp10 : p < 10 := by
        have : p ^ (2 - 1) = p := by norm_num
        omega
      have hp7' : p = 7 := by
        interval_cases p <;> first | rfl | (exact absurd hp (by decide))
      subst hp7'
      -- 49 | 5n-4, n ≤ 14, n ≥ 8
      have hn14 : n ≤ 14 := by
        have : n ≤ 2 * 7 := hnep
        omega
      have hn8 : 8 ≤ n := by omega
      interval_cases n <;> omega
  -- Step 2: e ≤ (n-1)/p → p^e | (n-1)!
  have hlog : Nat.log p (n - 1) < n := by
    have := Nat.log_le_self p (n - 1)
    omega
  rw [hp.pow_dvd_factorial_iff hlog]
  calc e ≤ (n - 1) / p := hD
    _ = (n - 1) / p ^ 1 := by rw [pow_one]
    _ ≤ ∑ i ∈ Finset.Ico 1 n, (n - 1) / p ^ i := by
        apply Finset.single_le_sum (f := fun i => (n - 1) / p ^ i) (fun i _ => Nat.zero_le _)
        simp only [Finset.mem_Ico]; omega

/-- Exact identity (A), auxiliary form with the factorial sum tracked. -/
lemma Asum_aux (n : ℕ) (hn : 5 ≤ n) : ∀ i k, k + i = n - 1 → 3 ≤ k →
    (((k - 3)! : ℕ) : ℤ) * ((k : ℤ) - 1) * B n k
      - (((n - 4)! : ℕ) : ℤ) * ((n : ℤ) - 2) * ((n : ℤ) ^ 2 + 2 * (n : ℤ) - 4)
    = (5 * (n : ℤ) - 4) * (∑ j ∈ Finset.range i, (((k - 3 + j)! : ℕ) : ℤ)) := by
  intro i
  induction i with
  | zero =>
    intro k hk hk3
    have hk1 : k + 1 = n := by omega
    have hb : B n k = (n : ℤ) ^ 2 + 2 * (n : ℤ) - 4 := B_base n k hk1
    have hk3n : k - 3 = n - 4 := by omega
    have hkm1 : ((k : ℤ) - 1) = (n : ℤ) - 2 := by
      have hh : k = n - 1 := by omega
      have h1 : 1 ≤ n := by omega
      omega
    rw [hb, hk3n, hkm1]
    simp
  | succ i ih =>
    intro k hk hk3
    have hkn2 : k ≤ n - 2 := by omega
    have step := Pstep n hn k hk3 hkn2
    have ihk := ih (k + 1) (by omega) (by omega)
    -- normalize factorial indices in ihk
    have hf1 : ((k + 1 - 3)! : ℕ) = ((k - 2)! : ℕ) := by rw [show k + 1 - 3 = k - 2 from by omega]
    have hcast1 : (((k + 1 : ℕ)) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
    rw [hf1, hcast1] at ihk
    -- normalize the sum index in ihk
    have hsumeq : (∑ j ∈ Finset.range i, (((k + 1 - 3 + j)! : ℕ) : ℤ))
        = (∑ j ∈ Finset.range i, (((k - 2 + j)! : ℕ) : ℤ)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show k + 1 - 3 + j = k - 2 + j from by omega]
    rw [hsumeq] at ihk
    -- expand the target sum
    rw [Finset.sum_range_succ']
    -- rewrite each term of the shifted sum
    have hsumeq2 : (∑ j ∈ Finset.range i, (((k - 3 + (j + 1))! : ℕ) : ℤ))
        = (∑ j ∈ Finset.range i, (((k - 2 + j)! : ℕ) : ℤ)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show k - 3 + (j + 1) = k - 2 + j from by omega]
    rw [hsumeq2]
    have hf0 : ((k - 3 + 0)! : ℕ) = ((k - 3)! : ℕ) := by rw [Nat.add_zero]
    rw [hf0]
    -- Now combine: LHS = step LHS + ihk LHS
    linear_combination step + ihk

/-- Exact identity (A): `2 B3 = (n-4)!(n-2)(n²+2n-4) + (5n-4) * S`, S = Σ_{j<n-4} j!. -/
lemma identityA_exact (n : ℕ) (hn : 5 ≤ n) :
    2 * B n 3 = (((n - 4)! : ℕ) : ℤ) * ((n : ℤ) - 2) * ((n : ℤ) ^ 2 + 2 * (n : ℤ) - 4)
      + (5 * (n : ℤ) - 4) * (∑ j ∈ Finset.range (n - 4), ((j ! : ℕ) : ℤ)) := by
  have h := Asum_aux n hn (n - 4) 3 (by omega) (by omega)
  simp only [show (3:ℕ) - 3 = 0 from rfl, Nat.factorial_zero, Nat.zero_add] at h
  linear_combination h

/-- 2 divides the factorial sum Σ_{j<m} j! for m ≥ 2. -/
lemma two_dvd_factsum (m : ℕ) (hm : 2 ≤ m) : 2 ∣ (∑ j ∈ Finset.range m, j !) := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [Finset.sum_range_succ]
    have h1 : 2 ∣ (∑ j ∈ Finset.range m, j !) := ih
    have h2 : 2 ∣ m ! := Nat.dvd_factorial (by norm_num) (by omega)
    exact Nat.dvd_add h1 h2

/-- p does not divide n-2 when p ≥ 7 prime and p | 5n-4. -/
lemma p_not_dvd_nm2 (p n : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hpm : p ∣ (5 * n - 4)) (hn : 5 ≤ n) :
    ¬ p ∣ (n - 2) := by
  intro h
  -- 5*(n-2) = (5n-4) - 6
  have h5 : 5 * (n - 2) = (5 * n - 4) - 6 := by omega
  have hd1 : p ∣ 5 * (n - 2) := Dvd.dvd.mul_left h 5
  rw [h5] at hd1
  -- p | (5n-4) and p | (5n-4)-6 ⇒ p | 6
  have h6 : p ∣ 6 := by
    have := Nat.dvd_sub hpm hd1
    have heq : (5 * n - 4) - ((5 * n - 4) - 6) = 6 := by omega
    rwa [heq] at this
  have := Nat.le_of_dvd (by norm_num) h6
  omega

/-- p does not divide n+4 when p ≥ 7 prime and p | 5n-4. -/
lemma p_not_dvd_np4 (p n : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hpm : p ∣ (5 * n - 4)) (hn : 5 ≤ n) :
    ¬ p ∣ (n + 4) := by
  intro h
  -- 5*(n+4) = (5n-4) + 24
  have h5 : 5 * (n + 4) = (5 * n - 4) + 24 := by omega
  have hd1 : p ∣ 5 * (n + 4) := Dvd.dvd.mul_left h 5
  rw [h5] at hd1
  have h24 : p ∣ 24 := (Nat.dvd_add_right hpm).mp hd1
  have hle := Nat.le_of_dvd (by norm_num) h24
  -- p | 24, p ≥ 7 prime ⇒ p ∈ {8,12,24}, none prime
  interval_cases p <;> first | (exact absurd h24 (by decide)) | (exact absurd hp (by decide))

/-- Cast of m = 5n-4 to ℤ divisibility. -/
lemma pm_cast (p n : ℕ) (hn : 5 ≤ n) (hpm : p ∣ (5 * n - 4)) :
    (p : ℤ) ∣ (5 * (n : ℤ) - 4) := by
  have he : (5 * (n : ℤ) - 4) = ((5 * n - 4 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (by omega : 4 ≤ 5 * n)]; ring
  rw [he]; exact_mod_cast hpm

/-- For `5 ≤ n ≤ p-1` and `p | 5n-4`: `p ∤ B n 3` (as ℤ). -/
lemma p_not_dvd_B3_small (p n : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hn : 5 ≤ n)
    (hnp : n ≤ p - 1) (hpm : p ∣ (5 * n - 4)) : ¬ (p : ℤ) ∣ B n 3 := by
  intro hpB3
  have hDB := DB n (by omega)
  have hpmZ := pm_cast p n hn hpm
  -- p | (2(n-2)B3 - (n+4)(n-1)!)
  have hpdiff : (p : ℤ) ∣ (2 * ((n : ℤ) - 2) * B n 3 - ((n : ℤ) + 4) * (((n - 1)! : ℕ) : ℤ)) :=
    hpmZ.trans hDB
  -- p | 2(n-2)B3
  have hp2 : (p : ℤ) ∣ 2 * ((n : ℤ) - 2) * B n 3 := Dvd.dvd.mul_left hpB3 _
  -- so p | (n+4)(n-1)!
  have hpprod : (p : ℤ) ∣ ((n : ℤ) + 4) * (((n - 1)! : ℕ) : ℤ) := by
    have hh := dvd_sub hp2 hpdiff
    have heq : 2 * ((n : ℤ) - 2) * B n 3
        - (2 * ((n : ℤ) - 2) * B n 3 - ((n : ℤ) + 4) * (((n - 1)! : ℕ) : ℤ))
        = ((n : ℤ) + 4) * (((n - 1)! : ℕ) : ℤ) := by ring
    rwa [heq] at hh
  -- p prime in ℤ
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpZ.dvd_mul.mp hpprod with hc | hc
  · -- p | n+4
    have hnat : p ∣ (n + 4) := by
      have : (p : ℤ) ∣ ((n + 4 : ℕ) : ℤ) := by push_cast; exact hc
      exact_mod_cast this
    exact p_not_dvd_np4 p n hp hp7 hpm hn hnat
  · -- p | (n-1)!
    have hnat : p ∣ ((n - 1)! : ℕ) := by exact_mod_cast hc
    have := (hp.dvd_factorial).mp hnat
    omega

/-- Key: for `p ≤ n-1` prime `≥7` with `p | 5n-4`, `p ∤ a n`. -/
lemma no_divide (p n : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hn : 5 ≤ n)
    (hpn : p ≤ n - 1) (hpm : p ∣ (5 * n - 4)) : ¬ p ∣ a n := by
  haveI : Fact p.Prime := ⟨hp⟩
  set m := 5 * n - 4 with hm
  have hm0 : m ≠ 0 := by omega
  set e := padicValNat p m with he
  have hpe_m : p ^ e ∣ m := pow_padicValNat_dvd
  have hpe1_m : ¬ p ^ (e + 1) ∣ m := pow_succ_padicValNat_not_dvd hm0
  have hKL : p ^ e ∣ (n - 1)! := KL p n e hp hp7 hn hpn hpe_m
  -- work in ℤ to get p^e | B3
  have hmZ : (5 * (n : ℤ) - 4) = ((m : ℕ) : ℤ) := by
    rw [hm]; push_cast [Nat.cast_sub (by omega : 4 ≤ 5 * n)]; ring
  have hpeZ_m : ((p : ℤ) ^ e) ∣ (5 * (n : ℤ) - 4) := by rw [hmZ]; exact_mod_cast hpe_m
  have hDB := DB n (by omega)
  have hpediff : ((p : ℤ) ^ e) ∣
      (2 * ((n : ℤ) - 2) * B n 3 - ((n : ℤ) + 4) * (((n - 1)! : ℕ) : ℤ)) := hpeZ_m.trans hDB
  have hpeY : ((p : ℤ) ^ e) ∣ ((n : ℤ) + 4) * (((n - 1)! : ℕ) : ℤ) := by
    have hpef : ((p : ℤ) ^ e) ∣ (((n - 1)! : ℕ) : ℤ) := by exact_mod_cast hKL
    exact Dvd.dvd.mul_left hpef _
  have hpeX : ((p : ℤ) ^ e) ∣ 2 * ((n : ℤ) - 2) * B n 3 := by
    have hh := dvd_add hpediff hpeY
    have heq : (2 * ((n : ℤ) - 2) * B n 3 - ((n : ℤ) + 4) * (((n - 1)! : ℕ) : ℤ))
        + ((n : ℤ) + 4) * (((n - 1)! : ℕ) : ℤ) = 2 * ((n : ℤ) - 2) * B n 3 := by ring
    rwa [heq] at hh
  -- coprimality
  have hcop_nat : Nat.Coprime p (2 * (n - 2)) := by
    apply Nat.Coprime.mul_right
    · exact (hp.coprime_iff_not_dvd).mpr (by
        intro h; have := Nat.le_of_dvd (by norm_num) h; omega)
    · exact (hp.coprime_iff_not_dvd).mpr (p_not_dvd_nm2 p n hp hp7 hpm hn)
  have hcop_int : IsCoprime (p : ℤ) ((2 * (n - 2) : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop_nat
  have hcast2 : ((2 * (n - 2) : ℕ) : ℤ) = 2 * ((n : ℤ) - 2) := by
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)]; ring
  rw [hcast2] at hcop_int
  have hcop_pow : IsCoprime ((p : ℤ) ^ e) (2 * ((n : ℤ) - 2)) := hcop_int.pow_left
  have hpeB3 : ((p : ℤ) ^ e) ∣ B n 3 := by
    apply hcop_pow.dvd_of_dvd_mul_left
    have : 2 * ((n : ℤ) - 2) * B n 3 = (2 * ((n : ℤ) - 2)) * B n 3 := by ring
    rwa [this] at hpeX
  -- transfer to natAbs
  have hB3pos : 0 < B n 3 := B_pos' n (by omega) 3 (by omega) (by omega)
  have hb3eq : B n 3 = ((B n 3).natAbs : ℤ) := (Int.natAbs_of_nonneg hB3pos.le).symm
  have hpe_b3 : p ^ e ∣ (B n 3).natAbs := by
    have : ((p : ℤ) ^ e) ∣ (((B n 3).natAbs : ℕ) : ℤ) := by rw [← hb3eq]; exact hpeB3
    exact_mod_cast this
  -- p^e | gcd(b3, m)
  set g := Nat.gcd (B n 3).natAbs m with hg
  have hpe_g : p ^ e ∣ g := Nat.dvd_gcd hpe_b3 hpe_m
  -- suppose p | a n
  intro hdivp
  rw [a_eq n (by omega)] at hdivp
  -- a n = m / g
  have hgm : g ∣ m := Nat.gcd_dvd_right _ _
  have hdivmg : p ∣ (m / g) := hdivp
  -- p^(e+1) | m
  have hcontra : p ^ (e + 1) ∣ m := by
    have hmul : p ^ e * p ∣ g * (m / g) := mul_dvd_mul hpe_g hdivmg
    rw [Nat.mul_div_cancel' hgm] at hmul
    rw [pow_succ]; exact hmul
  exact hpe1_m hcontra

/-- Existence: for `5 ≤ n ≤ p-1` prime `≥7` with `p | 5n-4`, `a n = p`. -/
lemma a_eq_p_small (p n : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hn : 5 ≤ n)
    (hnp : n ≤ p - 1) (hpm : p ∣ (5 * n - 4)) : a n = p := by
  have hpodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left (by omega)
  -- b3 and positivity
  have hB3pos : 0 < B n 3 := B_pos' n (by omega) 3 (by omega) (by omega)
  set b3 := (B n 3).natAbs with hb3def
  have hb3Z : B n 3 = (b3 : ℤ) := (Int.natAbs_of_nonneg hB3pos.le).symm
  have hb3pos : 0 < b3 := by rw [hb3def]; exact Int.natAbs_pos.mpr (by omega)
  -- p ∤ b3
  have hpnB3 := p_not_dvd_B3_small p n hp hp7 hn hnp hpm
  have hp_b3 : ¬ p ∣ b3 := by
    intro h
    apply hpnB3
    rw [hb3Z]; exact_mod_cast h
  -- c
  obtain ⟨c, hc⟩ := hpm
  have hpc_pos : 0 < p := by omega
  have hc_ge1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, mul_zero] at hc; omega
    · exact h
  have hc_le4 : c ≤ 4 := by
    by_contra h
    push_neg at h
    have hmul : p * 5 ≤ p * c := Nat.mul_le_mul (le_refl p) h
    omega
  -- casework on c to show c ∣ b3
  have hcb3 : c ∣ b3 := by
    -- reduce to (c:ℤ) ∣ B n 3
    suffices hcB3 : (c : ℤ) ∣ B n 3 by
      rw [hb3Z] at hcB3; exact_mod_cast hcB3
    have hmZc : 5 * (n : ℤ) - 4 = (p : ℤ) * (c : ℤ) := by
      have := hc
      have h2 : ((5 * n - 4 : ℕ) : ℤ) = ((p * c : ℕ) : ℤ) := by exact_mod_cast this
      rw [Nat.cast_sub (by omega : 4 ≤ 5 * n)] at h2
      push_cast at h2 ⊢; linarith [h2]
    have hIA := identityA_exact n hn
    set term1 := (((n - 4)! : ℕ) : ℤ) * ((n : ℤ) - 2) * ((n : ℤ) ^ 2 + 2 * (n : ℤ) - 4) with ht1
    -- hIA : 2 * B n 3 = term1 + (5n-4) * Σ (↑j!)
    interval_cases c
    · -- c = 1
      exact one_dvd _
    · -- c = 2 : need 2 | B3
      have hn6 : 6 ≤ n := by omega
      have hSeven : (2 : ℤ) ∣ ∑ j ∈ Finset.range (n - 4), ((j ! : ℕ) : ℤ) := by
        have h := two_dvd_factsum (n - 4) (by omega)
        have hcast : ((∑ j ∈ Finset.range (n - 4), j ! : ℕ) : ℤ)
            = ∑ j ∈ Finset.range (n - 4), ((j ! : ℕ) : ℤ) := by push_cast; ring
        rw [← hcast]; exact_mod_cast h
      -- 4 | (n-2)
      have hnm2 : (4 : ℕ) ∣ (n - 2) := by omega
      have hnm2Z : (4 : ℤ) ∣ ((n : ℤ) - 2) := by
        have : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by push_cast [Nat.cast_sub (by omega : 2 ≤ n)]; ring
        rw [← this]; exact_mod_cast hnm2
      have h4term1 : (4 : ℤ) ∣ term1 := by
        rw [ht1]
        have : (((n - 4)! : ℕ) : ℤ) * ((n : ℤ) - 2) * ((n : ℤ) ^ 2 + 2 * (n : ℤ) - 4)
            = ((n : ℤ) - 2) * ((((n - 4)! : ℕ) : ℤ) * ((n : ℤ) ^ 2 + 2 * (n : ℤ) - 4)) := by ring
        rw [this]; exact hnm2Z.mul_right _
      -- 4 | 2*B3
      have h4_2B3 : (4 : ℤ) ∣ 2 * B n 3 := by
        rw [hIA, hmZc]
        apply dvd_add h4term1
        -- 4 | (p*2)*Ssum since 2|Ssum
        obtain ⟨t, ht⟩ := hSeven
        exact ⟨(p : ℤ) * t, by rw [ht]; ring⟩
      -- 2 | B3
      have : (2 * 2 : ℤ) ∣ 2 * B n 3 := by norm_num; exact h4_2B3
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp this
    · -- c = 3 : need 3 | B3
      have hn3div : (3 : ℕ) ∣ (n - 2) := by omega
      have hnm2Z : (3 : ℤ) ∣ ((n : ℤ) - 2) := by
        have : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by push_cast [Nat.cast_sub (by omega : 2 ≤ n)]; ring
        rw [← this]; exact_mod_cast hn3div
      have h3term1 : (3 : ℤ) ∣ term1 := by
        rw [ht1]
        have : (((n - 4)! : ℕ) : ℤ) * ((n : ℤ) - 2) * ((n : ℤ) ^ 2 + 2 * (n : ℤ) - 4)
            = ((n : ℤ) - 2) * ((((n - 4)! : ℕ) : ℤ) * ((n : ℤ) ^ 2 + 2 * (n : ℤ) - 4)) := by ring
        rw [this]; exact hnm2Z.mul_right _
      have h3_2B3 : (3 : ℤ) ∣ 2 * B n 3 := by
        rw [hIA, hmZc]
        apply dvd_add h3term1
        exact ⟨(p : ℤ) * ∑ j ∈ Finset.range (n - 4), ((j ! : ℕ) : ℤ), by ring⟩
      -- 3 | 2*B3, 3 ∤ 2 ⇒ 3 | B3
      have hpr3 : Prime (3 : ℤ) := Int.prime_three
      rcases hpr3.dvd_mul.mp h3_2B3 with h | h
      · exact absurd h (by decide)
      · exact h
    · -- c = 4 : need 4 | B3
      have hn8 : 8 ≤ n := by omega
      have hSeven : (2 : ℤ) ∣ ∑ j ∈ Finset.range (n - 4), ((j ! : ℕ) : ℤ) := by
        have h := two_dvd_factsum (n - 4) (by omega)
        have hcast : ((∑ j ∈ Finset.range (n - 4), j ! : ℕ) : ℤ)
            = ∑ j ∈ Finset.range (n - 4), ((j ! : ℕ) : ℤ) := by push_cast; ring
        rw [← hcast]; exact_mod_cast h
      -- 4 | n
      have hn4 : (4 : ℕ) ∣ n := by omega
      obtain ⟨j, hj⟩ := hn4
      have hjZ : (n : ℤ) = 4 * (j : ℤ) := by exact_mod_cast hj
      have h8factor : (8 : ℤ) ∣ ((n : ℤ) - 2) * ((n : ℤ) ^ 2 + 2 * (n : ℤ) - 4) := by
        refine ⟨(2 * (j : ℤ) - 1) * (4 * (j : ℤ) ^ 2 + 2 * (j : ℤ) - 1), ?_⟩
        rw [hjZ]; ring
      have h8term1 : (8 : ℤ) ∣ term1 := by
        rw [ht1]
        have : (((n - 4)! : ℕ) : ℤ) * ((n : ℤ) - 2) * ((n : ℤ) ^ 2 + 2 * (n : ℤ) - 4)
            = (((n - 4)! : ℕ) : ℤ) * (((n : ℤ) - 2) * ((n : ℤ) ^ 2 + 2 * (n : ℤ) - 4)) := by ring
        rw [this]; exact h8factor.mul_left _
      have h8_2B3 : (8 : ℤ) ∣ 2 * B n 3 := by
        rw [hIA, hmZc]
        apply dvd_add h8term1
        obtain ⟨t, ht⟩ := hSeven
        exact ⟨(p : ℤ) * t, by rw [ht]; ring⟩
      -- 8 = 2*4 | 2*B3 ⇒ 4 | B3
      have : (2 * 4 : ℤ) ∣ 2 * B n 3 := by norm_num; exact h8_2B3
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp this
  -- Now compute a n = p
  have hcoppb3 : p.Coprime b3 := (hp.coprime_iff_not_dvd).mpr hp_b3
  -- gcd(b3, m) = c
  have hgcd : Nat.gcd b3 (5 * n - 4) = c := by
    rw [hc]
    rw [show p * c = c * p from Nat.mul_comm p c, Nat.gcd_comm b3 (c * p),
        Nat.Coprime.gcd_mul_right_cancel c hcoppb3, Nat.gcd_comm c b3]
    exact Nat.gcd_eq_right hcb3
  rw [a_eq n (by omega), ← hb3def, hgcd, hc]
  exact Nat.mul_div_left p (by omega : 0 < c)

/-- Direct computation: a 3 = 11. -/
lemma a3 : a 3 = 11 := by
  unfold a
  rw [if_neg (by norm_num : ¬ (3 : ℕ) < 3)]
  unfold continued_fraction_val
  norm_num

/-- Direct computation: a 4 = 4. -/
lemma a4 : a 4 = 4 := by
  rw [a_eq 4 (by norm_num)]
  have hB : B 4 3 = 20 := by rw [B_base 4 3 (by norm_num)]; norm_num
  rw [hB]
  decide

/-- Existence of a residue witness `n₀` with `3 ≤ n₀ < p` and `p | 5 n₀ - 4`. -/
lemma exists_witness (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ n₀, 3 ≤ n₀ ∧ n₀ < p ∧ p ∣ (5 * n₀ - 4) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨by omega⟩
  -- 5 ≠ 0 and 4 ≠ 0 in ZMod p
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro h
    have hh : ((5 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at hh
    have := Nat.le_of_dvd (by norm_num) hh; omega
  have h4 : (4 : ZMod p) ≠ 0 := by
    intro h
    have hh : ((4 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at hh
    have := Nat.le_of_dvd (by norm_num) hh; omega
  set y : ZMod p := (4 : ZMod p) * (5 : ZMod p)⁻¹ with hy
  set n₀ := y.val with hn0
  have hylt : n₀ < p := ZMod.val_lt y
  have hyne : y ≠ 0 := mul_ne_zero h4 (inv_ne_zero h5)
  have hn0pos : 1 ≤ n₀ := by
    rw [hn0]
    rcases Nat.eq_zero_or_pos y.val with h | h
    · exact absurd ((ZMod.val_eq_zero y).mp h) hyne
    · exact h
  -- 5 * n₀ ≡ 4 (mod p)
  have hcastval : (↑n₀ : ZMod p) = y := ZMod.natCast_zmod_val y
  have h5y : (5 : ZMod p) * y = 4 := by
    rw [hy, show (5 : ZMod p) * (4 * 5⁻¹) = 4 * (5 * 5⁻¹) by ring, mul_inv_cancel₀ h5, mul_one]
  have hmod : 5 * n₀ ≡ 4 [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [hcastval, h5y]
  have hdvd : p ∣ (5 * n₀ - 4) := by
    have := (Nat.modEq_iff_dvd' (by omega : 4 ≤ 5 * n₀)).mp hmod.symm
    exact this
  refine ⟨n₀, ?_, hylt, hdvd⟩
  -- 3 ≤ n₀
  by_contra h
  push_neg at h
  have hpos : 0 < 5 * n₀ - 4 := by omega
  have := Nat.le_of_dvd hpos hdvd
  omega

/-- Residue uniqueness: two witnesses `< p` with `p | 5·-4` are equal. -/
lemma resid_unique (p a b : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (ha1 : 1 ≤ a) (hb1 : 1 ≤ b)
    (ha : a < p) (hb : b < p) (hda : p ∣ (5 * a - 4)) (hdb : p ∣ (5 * b - 4)) : a = b := by
  have hma : 5 * a ≡ 4 [MOD p] := ((Nat.modEq_iff_dvd' (by omega)).mpr hda).symm
  have hmb : 5 * b ≡ 4 [MOD p] := ((Nat.modEq_iff_dvd' (by omega)).mpr hdb).symm
  have hab : 5 * a ≡ 5 * b [MOD p] := hma.trans hmb.symm
  have hcop : p.gcd 5 = 1 := by
    have : ¬ p ∣ 5 := by intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    exact (hp.coprime_iff_not_dvd).mpr this
  have hab' : a ≡ b [MOD p] := Nat.ModEq.cancel_left_of_coprime hcop hab
  have : a % p = b % p := hab'
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- `a n ∣ 5n-4` for `n ≥ 4`. -/
lemma a_dvd_m (n : ℕ) (hn : 4 ≤ n) : a n ∣ (5 * n - 4) := by
  rw [a_eq n hn]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)

/-- If `a n = p` (p prime ≥ 7, n ≥ 3), then `n < p` and `p | 5n-4`. -/
lemma prop_of_val (p n : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hn3 : 3 ≤ n) (hval : a n = p) :
    n < p ∧ p ∣ (5 * n - 4) := by
  rcases Nat.lt_or_ge n 5 with h | h
  · -- n ∈ {3,4}
    interval_cases n
    · -- n = 3: a 3 = 11 = p
      rw [a3] at hval
      have hp11 : p = 11 := hval.symm
      subst hp11; exact ⟨by norm_num, by norm_num⟩
    · -- n = 4: a 4 = 4 = p, contradiction
      rw [a4] at hval; omega
  · -- n ≥ 5
    -- p | 5n-4
    have hpm : p ∣ (5 * n - 4) := by
      have := a_dvd_m n (by omega)
      rw [hval] at this; exact this
    refine ⟨?_, hpm⟩
    -- n < p
    by_contra hc
    push_neg at hc  -- p ≤ n
    have hne : n ≠ p := by
      intro he
      rw [he] at hpm
      have hmul : p ∣ 5 * p := Dvd.dvd.mul_left dvd_rfl 5
      have h4 : p ∣ 4 := by
        have := Nat.dvd_sub hmul hpm
        rwa [show 5 * p - (5 * p - 4) = 4 from by omega] at this
      have := Nat.le_of_dvd (by norm_num) h4; omega
    have hpn : p ≤ n - 1 := by omega
    have := no_divide p n hp hp7 (by omega) hpn hpm
    rw [hval] at this
    exact this dvd_rfl

theorem oeis_372761_conjecture_2 :
  ∀ p : ℕ, Nat.Prime p ∧ p % 2 = 1 ∧ p ≠ 3 ∧ p ≠ 5 →
    ∃! n, n ≥ 3 ∧ a n = p := by
  rintro p ⟨hp, hodd, hp3, hp5⟩
  have hp7 : 7 ≤ p := by have := hp.two_le; omega
  obtain ⟨n₀, hn03, hn0p, hn0dvd⟩ := exists_witness p hp hp7
  have hval : a n₀ = p := by
    rcases Nat.lt_or_ge n₀ 5 with h | h
    · interval_cases n₀
      · -- n₀ = 3
        have h11 : p ∣ 11 := by simpa using hn0dvd
        have hp11 : p = 11 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h11
        rw [hp11]; exact a3
      · -- n₀ = 4
        have h16 : p ∣ 16 := by simpa using hn0dvd
        rw [show (16 : ℕ) = 2 ^ 4 from rfl] at h16
        have hp2 := hp.dvd_of_dvd_pow h16
        have := Nat.le_of_dvd (by norm_num) hp2; omega
    · exact a_eq_p_small p n₀ hp hp7 h (by omega) hn0dvd
  refine ⟨n₀, ⟨hn03, hval⟩, ?_⟩
  rintro n' ⟨hn'3, hn'val⟩
  obtain ⟨hn'p, hn'dvd⟩ := prop_of_val p n' hp hp7 hn'3 hn'val
  exact resid_unique p n' n₀ hp hp7 (by omega) (by omega) hn'p hn0p hn'dvd hn0dvd
