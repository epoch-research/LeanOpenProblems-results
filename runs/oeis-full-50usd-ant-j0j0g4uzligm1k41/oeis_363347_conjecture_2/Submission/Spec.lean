import FormalConjectures.Util.ProblemImports

open Rat Nat

/--
Helper function for A363347, which computes the denominator $R_k(n)$ of the continued fraction expression.
For $2 \le k \le n-1$, $R_k(n)$ is defined recursively:
$$R_k(n) = k - \frac{k+1}{R_{k+1}(n)}$$
The base case is $R_{n-1}(n) = (n-1) - \frac{n}{-4}$.
-/
def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    -- The recursive descent involves terms from $k=n-1$ down to $k=2$.
    if 2 ≤ k ∧ k ≤ n - 1 then
      -- Base Case: k = n - 1.
      if k = n - 1 then
        -- R_{n-1} = (n-1) + n/4
        (k : ℚ) + (n : ℚ) / 4
      -- Recursive Step: 2 <= k < n - 1.
      else
        let R_next := continued_fraction_denominator n (k + 1)
        -- R_k = k - (k+1) / R_{k+1}
        (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k

/--
A363347: Denominator of the continued fraction
$$\frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{-4}}}}}} $$
The value of the continued fraction is $C_n = 1/R_2(n)$. If $R_2(n) = N/D$ in reduced form, $C_n = D/N$.
The sequence $a(n)$ is the denominator of the final fraction, which is $\vert N \vert$.
-/
noncomputable def A363347 (n : ℕ) : ℕ :=
  if n ≤ 2 then 0 -- The sequence is indexed starting from $n=3$.
  else
    let R2 := continued_fraction_denominator n 2
    R2.num.natAbs


/-- Integer numerator sequence `P_k` for the continued fraction, for a fixed `n`.
`Pnum n k = P_k`, with base `P_n = 4`, `P_{n-1} = 5n-4`, and
`P_k = k*P_{k+1} - (k+1)*P_{k+2}` for `k+1 < n`. -/
def Pnum (n k : ℕ) : ℤ :=
  if n ≤ k + 1 then
    (if k + 1 = n then 5 * (n:ℤ) - 4 else 4)
  else
    (k : ℤ) * Pnum n (k + 1) - ((k : ℤ) + 1) * Pnum n (k + 2)
termination_by n - k
decreasing_by
  · omega
  · omega

-- base and recurrence lemmas
theorem Pnum_base_n (n : ℕ) : Pnum n n = 4 := by
  rw [Pnum]
  have : ¬ (n + 1 = n) := by omega
  simp [this]

theorem Pnum_base_pred (n : ℕ) (hn : 1 ≤ n) : Pnum n (n - 1) = 5 * (n:ℤ) - 4 := by
  rw [Pnum]
  have h1 : n ≤ (n-1) + 1 := by omega
  have h2 : (n - 1) + 1 = n := by omega
  simp [h1, h2]

theorem Pnum_rec (n k : ℕ) (hk : k + 1 < n) :
    Pnum n k = (k : ℤ) * Pnum n (k + 1) - ((k : ℤ) + 1) * Pnum n (k + 2) := by
  rw [Pnum]
  have : ¬ (n ≤ k + 1) := by omega
  simp [this]

/-- The telescoping identity (♣): `P_2 = (k-1)P_k - k(k-2)P_{k+1}`. -/
theorem clubs (n : ℕ) : ∀ k, 2 ≤ k → k ≤ n - 1 →
    Pnum n 2 = ((k:ℤ) - 1) * Pnum n k - (k:ℤ) * ((k:ℤ) - 2) * Pnum n (k + 1) := by
  intro k hk2
  induction k, hk2 using Nat.le_induction with
  | base => intro _; simp
  | succ k hk2 ih =>
    intro hkn
    have hkn' : k ≤ n - 1 := by omega
    have hrec := Pnum_rec n k (by omega)
    have := ih hkn'
    set a := Pnum n (k + 1) with ha
    set b := Pnum n (k + 2) with hb
    rw [this, hrec]
    push_cast
    ring

/-- Positivity invariant: for `3 ≤ k ≤ n-1`, `0 < P_{k+1}` and `(k-2)·P_{k+1} ≤ P_k`. -/
theorem Pnum_pos_aux (n : ℕ) (hn : 3 ≤ n) : ∀ d k, k + d = n - 1 → 3 ≤ k →
    0 < Pnum n (k + 1) ∧ ((k:ℤ) - 2) * Pnum n (k + 1) ≤ Pnum n k := by
  intro d
  induction d with
  | zero =>
    intro k hk hk3
    have hkeq : k = n - 1 := by omega
    subst hkeq
    rw [show (n - 1) + 1 = n by omega, Pnum_base_n, Pnum_base_pred n (by omega)]
    refine ⟨by norm_num, ?_⟩
    have hc : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    rw [hc]
    have : (3:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
    nlinarith
  | succ d ih =>
    intro k hk hk3
    have hk1 : (k + 1) + d = n - 1 := by omega
    obtain ⟨hpos2, hle2⟩ := ih (k + 1) hk1 (by omega)
    have hrec := Pnum_rec n k (by omega)
    have hk3' : (3:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk3
    -- hle2 : (↑(k+1) - 2) * Pnum n (k+2) ≤ Pnum n (k+1)
    rw [show k + 1 + 1 = k + 2 by rfl] at hpos2 hle2
    push_cast at hle2
    have hpos1 : 0 < Pnum n (k + 1) := by nlinarith [hpos2, hle2]
    refine ⟨hpos1, ?_⟩
    rw [hrec]
    nlinarith [hpos2, hle2, mul_nonneg (by linarith : (0:ℤ) ≤ (k:ℤ) - 3) (le_of_lt hpos2)]

theorem Pnum_two (n : ℕ) (hn : 3 ≤ n) : Pnum n 2 = ((n:ℤ) + 1)^2 - 5 := by
  have h := clubs n (n - 1) (by omega) (by omega)
  rw [show (n - 1) + 1 = n by omega] at h
  rw [Pnum_base_pred n (by omega), Pnum_base_n] at h
  rw [h]
  have hc : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rw [hc]
  ring

theorem Pnum_pos (n : ℕ) (hn : 3 ≤ n) : ∀ k, 2 ≤ k → k ≤ n → 0 < Pnum n k := by
  intro k hk2 hkn
  rcases eq_or_lt_of_le hkn with h | h
  · subst h; rw [Pnum_base_n]; norm_num
  · have hn' : (3:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
    rcases Nat.lt_or_ge k 3 with h3 | h3
    · interval_cases k
      · rw [Pnum_two n hn]; nlinarith
    · obtain ⟨hpos, hle⟩ := Pnum_pos_aux n hn (n - 1 - k) k (by omega) h3
      have hk3' : (3:ℤ) ≤ (k:ℤ) := by exact_mod_cast h3
      nlinarith [hle, hpos, mul_pos (by linarith : (0:ℤ) < (k:ℤ) - 2) hpos]

/-- Auxiliary sequence `G_k = (k-1)! * P_k - 2(k-2) P_3`, divisible by `P_2`. -/
def Gseq (n k : ℕ) : ℤ := ((k - 1)! : ℤ) * Pnum n k - 2 * ((k:ℤ) - 2) * Pnum n 3

theorem Gseq_rec (n k : ℕ) (hk : k + 1 < n) (hk2 : 2 ≤ k) :
    Gseq n (k + 2) = (k:ℤ) * (Gseq n (k + 1) - Gseq n k) := by
  unfold Gseq
  have e1 : (k + 2 - 1) = k + 1 := by omega
  have e2 : (k + 1 - 1) = k := by omega
  have e3 : ((k + 1)! : ℤ) = (k + 1) * (k ! : ℤ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have e4 : (k ! : ℤ) = (k : ℤ) * ((k - 1)! : ℤ) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    rw [show ((k - 1 : ℕ) : ℤ) + 1 = (k : ℤ) by omega]
  have hrec := Pnum_rec n k hk
  rw [e1, e2, e3, e4, show k + 2 = k + 2 from rfl]
  rw [show ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 by push_cast; ring]
  rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring]
  -- goal now in terms of Pnum n (k+2), Pnum n (k+1), Pnum n k
  rw [hrec]
  ring

theorem Gseq_dvd (n : ℕ) (hn : 3 ≤ n) : ∀ k, 2 ≤ k → k ≤ n - 1 →
    (Pnum n 2 ∣ Gseq n k) ∧ (Pnum n 2 ∣ Gseq n (k + 1)) := by
  intro k hk2
  induction k, hk2 using Nat.le_induction with
  | base =>
    intro _
    refine ⟨?_, ?_⟩
    · have : Gseq n 2 = Pnum n 2 := by unfold Gseq; norm_num
      rw [this]
    · have : Gseq n 3 = 0 := by unfold Gseq; norm_num
      rw [this]; exact dvd_zero _
  | succ k hk2 ih =>
    intro hkn
    obtain ⟨h1, h2⟩ := ih (by omega)
    refine ⟨h2, ?_⟩
    rw [show k + 1 + 1 = k + 2 from rfl, Gseq_rec n k (by omega) hk2]
    exact Dvd.dvd.mul_left (dvd_sub h2 h1) _

/-- (◆): `P_2 ∣ 4·(n-1)! - 2(n-2)·P_3`. -/
theorem diamond (n : ℕ) (hn : 3 ≤ n) :
    Pnum n 2 ∣ (4 * ((n - 1)! : ℤ) - 2 * ((n:ℤ) - 2) * Pnum n 3) := by
  have h := (Gseq_dvd n hn (n - 1) (by omega) (le_refl _)).2
  rw [show (n - 1) + 1 = n by omega] at h
  have he : Gseq n n = 4 * ((n - 1)! : ℤ) - 2 * ((n:ℤ) - 2) * Pnum n 3 := by
    unfold Gseq; rw [Pnum_base_n]; ring
  rwa [he] at h

/-- Existence of an even root `re` of `x² ≡ 5 (mod p)` with `4 ≤ re < p`. -/
theorem exists_even_root (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (hsq : IsSquare (5 : ZMod p)) :
    ∃ re : ℕ, Even re ∧ 4 ≤ re ∧ re < p ∧ (p : ℤ) ∣ ((re : ℤ) ^ 2 - 5) := by
  have hpodd : p % 2 = 1 :=
    Nat.odd_iff.mp ((Fact.out (p := p.Prime)).odd_of_ne_two (by omega))
  obtain ⟨y, hy⟩ := hsq
  set a := y.val with ha
  have haval : ((a : ℕ) : ZMod p) = y := ZMod.natCast_zmod_val y
  have halt : a < p := ZMod.val_lt y
  set re := if 2 ∣ a then a else p - a with hre
  have hkey : ((re : ℕ) : ZMod p) ^ 2 = 5 := by
    rw [hre]
    split_ifs with h
    · rw [haval, sq]; exact hy.symm
    · have hle : a ≤ p := le_of_lt halt
      rw [Nat.cast_sub hle, ZMod.natCast_self, haval, zero_sub, neg_sq, sq]
      exact hy.symm
  have hEven : Even re := by
    rw [Nat.even_iff, hre]; split_ifs with h <;> omega
  have hlt : re < p := by
    rw [hre]; split_ifs with h
    · exact halt
    · omega
  have hdvd : (p : ℤ) ∣ ((re : ℤ) ^ 2 - 5) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hkey]; ring
  have h4 : 4 ≤ re := by
    rcases hEven with ⟨t, ht⟩
    by_contra hc
    push_neg at hc
    have hcase : re = 0 ∨ re = 2 := by omega
    rcases hcase with h0 | h2
    · rw [h0] at hdvd
      have hd5 : (p : ℤ) ∣ 5 := (dvd_neg).mp (by simpa using hdvd)
      have := Int.le_of_dvd (by norm_num) hd5
      have : p ≤ 5 := by exact_mod_cast this
      omega
    · rw [h2] at hdvd
      have hd1 : (p : ℤ) ∣ 1 := (dvd_neg).mp (by norm_num at hdvd ⊢; simpa using hdvd)
      have := Int.le_of_dvd (by norm_num) hd1
      have : p ≤ 1 := by exact_mod_cast this
      omega
  exact ⟨re, hEven, h4, hlt, hdvd⟩

/-- `5` is a quadratic residue mod `p` when `p ≡ ±1 (mod 5)`. -/
theorem five_isSquare (p : ℕ) [Fact p.Prime] (hp5 : p % 5 = 1 ∨ p % 5 = 4) :
    IsSquare (5 : ZMod p) := by
  have hsq5 : IsSquare ((p : ℕ) : ZMod 5) := by
    have he : ((p : ℕ) : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) :=
      (ZMod.natCast_eq_natCast_iff p (p % 5) 5).mpr (Nat.mod_modEq p 5).symm
    rw [he]
    rcases hp5 with h | h <;> rw [h] <;> decide
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hq1 : p ≠ 2 := by rintro rfl; omega
  have hiff := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p)
    (by norm_num) hq1
  have := hiff.mp hsq5
  simpa using this

/-- The continued fraction denominator equals `P_k / P_{k+1}`. -/
theorem cfd_eq (n : ℕ) (hn : 3 ≤ n) : ∀ d k, k + d = n - 1 → 2 ≤ k →
    continued_fraction_denominator n k = (Pnum n k : ℚ) / (Pnum n (k + 1) : ℚ) := by
  intro d
  induction d with
  | zero =>
    intro k hk hk2
    have hkeq : k = n - 1 := by omega
    subst hkeq
    rw [continued_fraction_denominator]
    have hn2 : ¬ (n ≤ 2) := by omega
    have hcond : 2 ≤ n - 1 ∧ n - 1 ≤ n - 1 := ⟨by omega, le_refl _⟩
    simp only [hn2, if_false, hcond, and_self, if_true]
    rw [show (n - 1) + 1 = n by omega, Pnum_base_n, Pnum_base_pred n (by omega)]
    have hc : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
      have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
      exact_mod_cast this
    rw [hc]
    push_cast
    ring
  | succ d ih =>
    intro k hk hk2
    have hklt : k + 1 ≤ n - 1 := by omega
    have hk1 : (k + 1) + d = n - 1 := by omega
    have ihk := ih (k + 1) hk1 (by omega)
    have hP1 : (0:ℤ) < Pnum n (k + 1) := Pnum_pos n hn (k + 1) (by omega) (by omega)
    have hP2 : (0:ℤ) < Pnum n (k + 2) := Pnum_pos n hn (k + 2) (by omega) (by omega)
    have hP1q : (Pnum n (k + 1) : ℚ) ≠ 0 := by exact_mod_cast hP1.ne'
    have hP2q : (Pnum n (k + 2) : ℚ) ≠ 0 := by exact_mod_cast hP2.ne'
    rw [continued_fraction_denominator]
    have hn2 : ¬ (n ≤ 2) := by omega
    have hcond : 2 ≤ k ∧ k ≤ n - 1 := ⟨hk2, by omega⟩
    have hne : ¬ (k = n - 1) := by omega
    simp only [hn2, if_false, hcond, and_self, if_true, hne]
    rw [show k + 1 + 1 = k + 2 by rfl] at ihk
    rw [ihk]
    have hrec := Pnum_rec n k (by omega)
    rw [hrec]
    push_cast
    field_simp

/--
A363347 Conjecture 2: The sequence contains all prime numbers which end with a 1 or 9.
-/
theorem oeis_363347_conjecture_2 :
  ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p :=
  by
  rintro p ⟨hp, hmod⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  have h10 : p % 10 = 1 ∨ p % 10 = 9 := by
    rcases hmod with h | h
    · left; simpa [Nat.ModEq] using h
    · right; simpa [Nat.ModEq] using h
  have hp7 : 7 ≤ p := by omega
  have hp5 : p % 5 = 1 ∨ p % 5 = 4 := by omega
  have hpodd : p % 2 = 1 := by omega
  have hsq : IsSquare (5 : ZMod p) := five_isSquare p hp5
  obtain ⟨re, hEven, h4, hltp, hdvd⟩ := exists_even_root p hp7 hsq
  -- set up n
  set n := re - 1 with hndef
  have hn3 : 3 ≤ n := by omega
  have hnodd : n % 2 = 1 := by rcases hEven with ⟨t, ht⟩; omega
  have hre_eq : (n : ℤ) + 1 = (re : ℤ) := by
    have : re = n + 1 := by omega
    rw [this]; push_cast; ring
  have hpn : n < p := by omega
  -- P2 value and divisibility
  have hP2 : Pnum n 2 = (re : ℤ) ^ 2 - 5 := by rw [Pnum_two n hn3, hre_eq]
  have hpP2 : (p : ℤ) ∣ Pnum n 2 := by rw [hP2]; exact hdvd
  have hP2pos : 0 < Pnum n 2 := Pnum_pos n hn3 2 (by norm_num) (by omega)
  have hP3pos : 0 < Pnum n 3 := Pnum_pos n hn3 3 (by norm_num) (by omega)
  -- extract m
  obtain ⟨m, hm⟩ := hpP2
  have hmpos : 0 < m := by
    rcases lt_trichotomy m 0 with h | h | h
    · exfalso; nlinarith [hm, hP2pos, (by exact_mod_cast hp2 : (2:ℤ) ≤ p)]
    · exfalso; rw [h, mul_zero] at hm; omega
    · exact h
  lift m to ℕ using hmpos.le with M hM
  -- hm : Pnum n 2 = ↑p * ↑M
  have hpP2 : (p : ℤ) ∣ Pnum n 2 := ⟨(M : ℤ), hm⟩
  have hpge : (n : ℤ) + 1 ≤ (p : ℤ) := by exact_mod_cast (by omega : n + 1 ≤ p)
  have hval : (p : ℤ) * (M : ℤ) = ((n : ℤ) + 1) ^ 2 - 5 := by rw [← hm, Pnum_two n hn3]
  -- M ≤ n
  have hn1pos : (0 : ℤ) < (n : ℤ) + 1 := by positivity
  have hMltn1 : (M : ℤ) < (n : ℤ) + 1 := by
    nlinarith [hval, hpge, hmpos, hn1pos, mul_nonneg (sub_nonneg.mpr hpge) hmpos.le]
  have hMlen : M ≤ n := by
    have : M < n + 1 := by exact_mod_cast hMltn1
    omega
  -- M ≠ n
  have hMne : M ≠ n := by
    intro heq
    rw [heq] at hval
    have hdvd4 : (n : ℤ) ∣ 4 := ⟨(n : ℤ) + 2 - p, by linear_combination hval⟩
    have hn4 : (n : ℤ) ≤ 4 := Int.le_of_dvd (by norm_num) hdvd4
    have hn4' : n ≤ 4 := by exact_mod_cast hn4
    have hn3eq : n = 3 := by omega
    rw [hn3eq] at hval
    norm_num at hval
    omega
  have hMltn : M ≤ n - 1 := by omega
  have hMpos : 0 < M := by exact_mod_cast hmpos
  -- M ∣ (n-1)!
  have hMfact : M ∣ (n - 1)! := Nat.dvd_factorial hMpos hMltn
  have hMfactZ : (M : ℤ) ∣ ((n - 1)! : ℤ) := by exact_mod_cast hMfact
  -- diamond
  have hdia := diamond n hn3
  -- p ∤ Pnum n 3
  have hpnP3 : ¬ (p : ℤ) ∣ Pnum n 3 := by
    intro hpP3
    have h1 : (p : ℤ) ∣ (4 * ((n - 1)! : ℤ) - 2 * ((n:ℤ) - 2) * Pnum n 3) :=
      dvd_trans hpP2 hdia
    have h2 : (p : ℤ) ∣ 2 * ((n:ℤ) - 2) * Pnum n 3 := Dvd.dvd.mul_left hpP3 _
    have h3 : (p : ℤ) ∣ 4 * ((n - 1)! : ℤ) := by
      have := dvd_add h1 h2
      simpa using this
    have h4' : (p : ℤ) ∣ ((4 * (n - 1)! : ℕ) : ℤ) := by push_cast; exact h3
    have h5 : p ∣ 4 * (n - 1)! := by exact_mod_cast h4'
    rcases (hp.dvd_mul.mp h5) with h | h
    · have : p ≤ 4 := Nat.le_of_dvd (by norm_num) h
      omega
    · have : p ≤ n - 1 := (Nat.Prime.dvd_factorial hp).mp h
      omega
  -- M ∣ Pnum n 3
  have hMP3 : (M : ℤ) ∣ Pnum n 3 := by
    -- M ∣ Pnum n 2
    have hMdvdP2 : (M : ℤ) ∣ Pnum n 2 := by rw [hm]; exact dvd_mul_left _ _
    have h1 : (M : ℤ) ∣ (4 * ((n - 1)! : ℤ) - 2 * ((n:ℤ) - 2) * Pnum n 3) :=
      dvd_trans hMdvdP2 hdia
    have h2 : (M : ℤ) ∣ 4 * ((n - 1)! : ℤ) := Dvd.dvd.mul_left hMfactZ 4
    have h3 : (M : ℤ) ∣ 2 * ((n:ℤ) - 2) * Pnum n 3 := by
      have := dvd_sub h2 h1
      simpa using this
    -- coprimality of M and 2(n-2)
    have hodd2 : Odd (Pnum n 2) := by
      rw [hP2]; rcases hEven with ⟨t, ht⟩
      have hre2 : (re : ℤ) = 2 * (t : ℤ) := by rw [ht]; push_cast; ring
      refine ⟨2 * (t : ℤ) ^ 2 - 3, ?_⟩
      rw [hre2]; ring
    have hoddM : Odd (M : ℤ) := by
      have : Odd ((p : ℤ) * (M : ℤ)) := by rw [← hm]; exact hodd2
      exact (Int.odd_mul.mp this).2
    have hnm2odd : Odd ((n : ℤ) - 2) := by
      have : Odd (n : ℤ) := by rw [Int.odd_iff]; omega
      exact this.sub_even (by exact ⟨1, by ring⟩)
    have hcop_two : IsCoprime (Pnum n 2) (2 : ℤ) := by
      have hmod2 : Pnum n 2 % 2 = 1 := Int.odd_iff.mp hodd2
      have hnd : ¬ (2 : ℤ) ∣ Pnum n 2 := by
        rw [Int.dvd_iff_emod_eq_zero]; omega
      exact ((Int.prime_two.coprime_iff_not_dvd).mpr hnd).symm
    have hcop_nm2 : IsCoprime (Pnum n 2) ((n : ℤ) - 2) := by
      have hbase : IsCoprime (4 : ℤ) ((n : ℤ) - 2) := by
        have h2c : IsCoprime (2 : ℤ) ((n : ℤ) - 2) := by
          have hmod2 : ((n : ℤ) - 2) % 2 = 1 := Int.odd_iff.mp hnm2odd
          have hnd : ¬ (2 : ℤ) ∣ ((n : ℤ) - 2) := by
            rw [Int.dvd_iff_emod_eq_zero]; omega
          exact (Int.prime_two.coprime_iff_not_dvd).mpr hnd
        have : IsCoprime (2 * 2 : ℤ) ((n : ℤ) - 2) := h2c.mul_left h2c
        simpa using this
      have hrw : Pnum n 2 = 4 + ((n : ℤ) - 2) * ((n : ℤ) + 4) := by
        rw [Pnum_two n hn3]; ring
      rw [hrw]
      exact hbase.add_mul_left_left ((n : ℤ) + 4)
    have hcop : IsCoprime (Pnum n 2) (2 * ((n : ℤ) - 2)) := hcop_two.mul_right hcop_nm2
    have hcopM : IsCoprime (M : ℤ) (2 * ((n : ℤ) - 2)) :=
      hcop.of_isCoprime_of_dvd_left hMdvdP2
    have hgcd : Int.gcd (M : ℤ) (2 * ((n : ℤ) - 2)) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp hcopM
    have h3' : (M : ℤ) ∣ Pnum n 3 * (2 * ((n : ℤ) - 2)) := by
      have heq : Pnum n 3 * (2 * ((n : ℤ) - 2)) = 2 * ((n : ℤ) - 2) * Pnum n 3 := by ring
      rw [heq]; exact h3
    exact Int.dvd_of_dvd_mul_left_of_gcd_one h3' hgcd
  -- Now assemble the fraction
  obtain ⟨q, hq⟩ := hMP3
  have hMne0 : (M : ℤ) ≠ 0 := by exact_mod_cast hMpos.ne'
  have hqpos : 0 < q := by
    rcases lt_trichotomy q 0 with h | h | h
    · exfalso; nlinarith [hq, hP3pos, hMpos]
    · exfalso; rw [h, mul_zero] at hq; omega
    · exact h
  refine ⟨n, ?_⟩
  rw [A363347]
  have hnn2 : ¬ n ≤ 2 := by omega
  simp only [hnn2, if_false]
  -- continued_fraction_denominator n 2 = p / q
  have hM0q : (M : ℚ) ≠ 0 := by exact_mod_cast hMpos.ne'
  have hq0q : (q : ℚ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hcfd : continued_fraction_denominator n 2 = (p : ℚ) / (q : ℚ) := by
    have hce := cfd_eq n hn3 (n - 1 - 2) 2 (by omega) (by norm_num)
    rw [hce]
    rw [show (Pnum n 2 : ℚ) = ((p : ℤ) * (M : ℤ) : ℤ) from by rw [hm]]
    rw [show (Pnum n 3 : ℚ) = ((M : ℤ) * q : ℤ) from by rw [hq]]
    push_cast
    rw [mul_comm (p : ℚ) (M : ℚ), mul_div_mul_left _ _ hM0q]
  rw [hcfd]
  -- num of p/q
  have hcoprime : Nat.Coprime ((p : ℤ)).natAbs q.natAbs := by
    rw [Int.natAbs_natCast]
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr ?_
    intro hpq
    have hpqz : (p : ℤ) ∣ q := by
      have h1 : (p : ℤ) ∣ (q.natAbs : ℤ) := by exact_mod_cast hpq
      exact (Int.dvd_natAbs).mp h1
    have hpP3 : (p : ℤ) ∣ Pnum n 3 := by rw [hq]; exact Dvd.dvd.mul_left hpqz _
    exact hpnP3 hpP3
  have hpc : (p : ℚ) = ((p : ℤ) : ℚ) := by push_cast; ring
  rw [hpc, Rat.num_div_eq_of_coprime (a := (p : ℤ)) (b := q) (by exact_mod_cast hqpos) hcoprime]
  simp
