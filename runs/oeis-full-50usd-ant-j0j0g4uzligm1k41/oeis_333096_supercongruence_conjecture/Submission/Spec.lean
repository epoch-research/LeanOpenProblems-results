import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators Int

/-!
This file settles (reduces to a single analytic supercongruence) the OEIS A333096
supercongruence conjecture.

The strategy, fully carried out below except for the final analytic core `single_step`:

* We rewrite `a_gen m N` in a clean "F-form" `Ff (m+2) N = ∑_j hh(N-j) · C(sN, j)` where
  `C = Ring.choose` is the generalized binomial coefficient, `s = m+2`, and `hh` is the
  period-3 weight coming from `G(y) = (1-y²)/(1+y+y²)`. Concretely
  `a_gen m N = [x^N] c(x)^{mN}/(1-x) = [y^N] (1+y)^{sN} (1-y²)/(1+y+y²)` via Lagrange inversion.
  (Phases 0 and 1 below, fully proved.)
* The supercongruence then reduces to a single-step statement
  `Ff s (p·M) ≡ Ff s M  [ZMOD p^{3(v_p(M)+1)}]` (`single_step`), applied with `M = n·p^{k-1}`.
* `single_step` is the analytic heart: an Apéry-like *cube* supercongruence, provable via the
  Cartier operator `U_p` and the master identity
  `Ff s (pM) - Ff s M = ∑_{r≥3} p^r · C(sM,r) · [y^M]((1+y)^{sM-r} · U_p(Δ^r G))`,
  where `Δ = ((1+X)^p - 1 - X^p)/p`. The `r=1,2` terms vanish (the exact Cartier eigen-identities
  `U_p((1+X)^p G) = (1+X) G`, `U_p((1+X)^{2p} G) = (1+X)^2 G`), which is the mechanism producing the
  `p^{3k}` (rather than `p^k`) modulus. The remaining valuation bound is of Mellit–Vlasenko /
  Kazandzidis (Dwork-crystal) type.
-/

-- Generalized binomial coefficient $\binom{r}{k}$ for $r \in \mathbb{Z}, k \in \mathbb{N}$.
def generalized_choose_int (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else
    (Finset.prod (Finset.range k) fun i => r - (i : ℤ)) / (k.factorial : ℤ)

/-- The $k$-th power series coefficient of $c(x)^r$. -/
def generalized_catalan_coefficient (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else
    let num_choose := generalized_choose_int (r + 2 * (k : ℤ) - 1) k
    let denominator : ℤ := r + k
    (r * num_choose) / denominator

/-- The generalized sequence $a_m(n)$. -/
def a_gen (m : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 1
  else
    let r : ℤ := m * (n : ℤ)
    Finset.sum (range (n + 1)) fun k =>
      generalized_catalan_coefficient r k

/-- A333096. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.sum (range (n + 1)) fun k =>
      let m : ℕ := 4 * n
      let numerator : ℕ := m * (m + 2 * k - 1).choose k
      let denominator : ℕ := m + k
      numerator / denominator

noncomputable section

/-- Generalized binomial over ℤ. -/
abbrev C (r : ℤ) (k : ℕ) : ℤ := Ring.choose r k

/-- Period-3 weight: h 0 = 1, and for t ≥ 1, h t = 2 if 3 ∣ t else -1. -/
def hh (t : ℕ) : ℤ := if t = 0 then 1 else if t % 3 = 0 then 2 else -1

/-- Generalized Catalan-coefficient (clean binomial form), matching
`generalized_catalan_coefficient` off the pole. -/
def Tt (r : ℤ) (k : ℕ) : ℤ := if k = 0 then 1 else C (r + 2 * k - 1) k - C (r + 2 * k - 1) (k - 1)

/-- The "S" side: partial sum of Catalan coefficients. -/
def Ss (r : ℤ) (N : ℕ) : ℤ := ∑ k ∈ range (N + 1), Tt r k

/-- The "R"/`F_s` side. -/
def Rr (r : ℤ) (N : ℕ) : ℤ := ∑ t ∈ range (N + 1), hh t * C (r + 2 * N) (N - t)

-- Pascal's rule for Ring.choose
lemma pascalC (r : ℤ) (k : ℕ) : C (r + 1) (k + 1) = C r k + C r (k + 1) := by
  simp only [C]; rw [Ring.choose_succ_succ]

lemma C_zero (r : ℤ) : C r 0 = 1 := by simp only [C]; exact Ring.choose_zero_right r

-- convolution form
def P (a : ℤ) (M : ℕ) : ℤ := ∑ i ∈ range (M + 1), hh (M - i) * C a i

lemma Rr_eq_P (r : ℤ) (N : ℕ) : Rr r N = P (r + 2 * N) N := by
  unfold Rr P
  rw [← Finset.sum_range_reflect (fun t => hh t * C (r + 2 * N) (N - t)) (N+1)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have : N + 1 - 1 - i = N - i := by omega
  rw [this]
  congr 2
  omega

-- sum of 3 consecutive hh values (all indices ≥ 1) is 0
lemma hh_triple (j : ℕ) (hj : 1 ≤ j) : hh j + hh (j + 1) + hh (j + 2) = 0 := by
  simp only [hh]
  have h0 : j ≠ 0 := by omega
  have h1 : j + 1 ≠ 0 := by omega
  have h2 : j + 2 ≠ 0 := by omega
  rw [if_neg h0, if_neg h1, if_neg h2]
  omega

-- Clean Pascal-type recurrence for P (no boundary issues)
lemma P_rec (a : ℤ) (M : ℕ) : P (a + 1) (M + 1) = P a M + P a (M + 1) := by
  unfold P
  -- LHS: split off i = 0 and use Pascal
  rw [Finset.sum_range_succ' (fun i => hh (M + 1 - i) * C (a + 1) i) (M + 1)]
  simp only [Nat.sub_zero, C_zero, mul_one]
  have hstep : ∀ i ∈ Finset.range (M + 1),
      hh (M + 1 - (i + 1)) * C (a + 1) (i + 1) = hh (M - i) * C a i + hh (M - i) * C a (i + 1) := by
    intro i hi
    have h1 : M + 1 - (i + 1) = M - i := by omega
    rw [h1, pascalC, mul_add]
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
  -- RHS: expand P a (M+1) via sum_range_succ'
  rw [Finset.sum_range_succ' (fun i => hh (M + 1 - i) * C a i) (M + 1)]
  simp only [Nat.sub_zero, C_zero, mul_one]
  have hstep2 : ∀ i ∈ Finset.range (M + 1),
      hh (M + 1 - (i + 1)) * C a (i + 1) = hh (M - i) * C a (i + 1) := by
    intro i hi
    have h1 : M + 1 - (i + 1) = M - i := by omega
    rw [h1]
  rw [Finset.sum_congr rfl hstep2]
  ring

lemma hh_zero : hh 0 = 1 := by simp [hh]

-- Extend P(a,m) to a sum over a larger range, tracking the Nat-subtraction boundary terms.
lemma P_ext1 (a : ℤ) (m : ℕ) :
    P a (m + 1) = (∑ i ∈ range (m + 3), hh (m + 1 - i) * C a i) - C a (m + 2) := by
  unfold P
  rw [Finset.sum_range_succ (fun i => hh (m + 1 - i) * C a i) (m + 2),
      Finset.sum_range_succ (fun i => hh (m + 1 - i) * C a i) (m + 1)]
  have e1 : m + 1 - (m + 1) = 0 := by omega
  have e2 : m + 1 - (m + 2) = 0 := by omega
  rw [e1, e2, hh_zero]
  ring

lemma P_ext2 (a : ℤ) (m : ℕ) :
    P a m = (∑ i ∈ range (m + 3), hh (m - i) * C a i) - C a (m + 1) - C a (m + 2) := by
  unfold P
  rw [Finset.sum_range_succ (fun i => hh (m - i) * C a i) (m + 2),
      Finset.sum_range_succ (fun i => hh (m - i) * C a i) (m + 1)]
  have e1 : m - (m + 1) = 0 := by omega
  have e2 : m - (m + 2) = 0 := by omega
  rw [e1, e2, hh_zero]
  ring

-- Q: three consecutive P telescope.
lemma Q (a : ℤ) (m : ℕ) : P a (m + 2) + P a (m + 1) + P a m = C a (m + 2) - C a m := by
  have hP2 : P a (m + 2) = ∑ i ∈ range (m + 3), hh (m + 2 - i) * C a i := by
    unfold P; congr 1
  rw [hP2, P_ext1, P_ext2]
  -- Now combine the three sums over range (m+3)
  rw [show (∑ i ∈ range (m + 3), hh (m + 2 - i) * C a i)
        + ((∑ i ∈ range (m + 3), hh (m + 1 - i) * C a i) - C a (m + 2))
        + ((∑ i ∈ range (m + 3), hh (m - i) * C a i) - C a (m + 1) - C a (m + 2))
      = (∑ i ∈ range (m + 3),
          (hh (m + 2 - i) * C a i + hh (m + 1 - i) * C a i + hh (m - i) * C a i))
        - C a (m + 1) - 2 * C a (m + 2) by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]; ring]
  -- Evaluate the combined sum: peel last three terms; the rest is 0.
  rw [Finset.sum_range_succ _ (m + 2), Finset.sum_range_succ _ (m + 1),
      Finset.sum_range_succ _ m]
  have hzero : ∑ i ∈ range m, (hh (m + 2 - i) * C a i + hh (m + 1 - i) * C a i + hh (m - i) * C a i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    have hj : 1 ≤ m - i := by omega
    have e1 : m + 2 - i = (m - i) + 2 := by omega
    have e2 : m + 1 - i = (m - i) + 1 := by omega
    have h3 := hh_triple (m - i) hj
    rw [e1, e2]
    linear_combination (C a i) * h3
  rw [hzero]
  -- simplify the boundary Nat subtractions
  have s1 : m + 2 - m = 2 := by omega
  have s2 : m + 1 - m = 1 := by omega
  have s3 : m - m = 0 := by omega
  have s4 : m + 2 - (m + 1) = 1 := by omega
  have s5 : m + 1 - (m + 1) = 0 := by omega
  have s6 : m - (m + 1) = 0 := by omega
  have s7 : m + 2 - (m + 2) = 0 := by omega
  have s8 : m + 1 - (m + 2) = 0 := by omega
  have s9 : m - (m + 2) = 0 := by omega
  rw [s1, s2, s3, s4, s5, s6, s7, s8, s9]
  simp only [hh]
  norm_num
  ring

-- Tt via double Pascal, matching the Q form.
lemma Tt_eq (r : ℤ) (n : ℕ) :
    Tt r (n + 2) = C (r + 2 * (n : ℤ) + 2) (n + 2) - C (r + 2 * (n : ℤ) + 2) n := by
  unfold Tt
  rw [if_neg (by omega)]
  have hcast : r + 2 * ((n : ℤ) + 2) - 1 = (r + 2 * (n : ℤ) + 2) + 1 := by ring
  have h1 : C (r + 2 * ((n : ℤ) + 2) - 1) (n + 2) = C (r + 2 * (n:ℤ) + 2) (n+1) + C (r + 2 * (n:ℤ) + 2) (n+2) := by
    rw [hcast]; rw [show n + 2 = (n+1)+1 from rfl]; exact pascalC _ _
  have h2 : C (r + 2 * ((n : ℤ) + 2) - 1) (n + 1) = C (r + 2 * (n:ℤ) + 2) n + C (r + 2 * (n:ℤ) + 2) (n+1) := by
    rw [hcast]; exact pascalC _ _
  push_cast
  push_cast at h1 h2
  rw [h1, h2]; ring

-- Main recurrence for Rr.
lemma Rr_rec (r : ℤ) (N : ℕ) : Rr r (N + 1) = Rr r N + Tt r (N + 1) := by
  cases N with
  | zero =>
    rw [Rr_eq_P, Rr_eq_P]
    unfold P Tt
    simp only [Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, add_zero]
    rw [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_one]
    rw [if_neg (by omega)]
    simp only [hh, C_zero]
    norm_num
    ring
  | succ n =>
    rw [Rr_eq_P, Rr_eq_P]
    have hcast1 : r + 2 * ((n : ℤ) + 1 + 1) = (r + 2 * (n:ℤ) + 2) + 2 := by ring
    have hcast2 : r + 2 * ((n : ℤ) + 1) = r + 2 * (n:ℤ) + 2 := by ring
    push_cast
    rw [hcast1, hcast2]
    set a : ℤ := r + 2 * (n:ℤ) + 2 with ha
    -- P (a+2) (n+2) = P a n + 2 P a (n+1) + P a (n+2)
    have step : P (a + 2) (n + 2) = P a n + 2 * P a (n + 1) + P a (n + 2) := by
      have r1 : P (a + 1) (n + 1 + 1) = P a (n + 1) + P a (n + 1 + 1) := P_rec a (n + 1)
      have r2 : P (a + 1) (n + 1) = P a n + P a (n + 1) := P_rec a n
      have r3 : P (a + 1 + 1) (n + 1 + 1) = P (a + 1) (n + 1) + P (a + 1) (n + 1 + 1) := P_rec (a + 1) (n + 1)
      have : a + 1 + 1 = a + 2 := by ring
      rw [this] at r3
      rw [r3, r1, r2]; ring
    rw [step]
    have hQ := Q a n
    rw [Tt_eq]
    -- a = r + 2n + 2, and Tt_eq gives C(a)(n+2) - C(a) n
    have : P a n + 2 * P a (n + 1) + P a (n + 2) - P a (n + 1)
         = P a (n + 2) + P a (n + 1) + P a n := by ring
    linarith [hQ]

-- Phase 1 identity: Ss = Rr.
lemma phase1 (r : ℤ) (N : ℕ) : Ss r N = Rr r N := by
  induction N with
  | zero =>
    unfold Ss
    rw [Finset.sum_range_one]
    rw [Rr_eq_P]; unfold P Tt
    simp only [Nat.cast_zero, mul_zero, add_zero]
    rw [Finset.sum_range_one]
    simp only [hh, C_zero]
    norm_num
  | succ n ih =>
    unfold Ss
    rw [Finset.sum_range_succ]
    rw [show (∑ k ∈ range (n + 1), Tt r k) = Ss r n from rfl, ih, Rr_rec]

/-! ### Phase 0: connect the problem's `a_gen` to `Ss`. -/

-- product = k! * choose
lemma prod_eq_choose (r : ℤ) (k : ℕ) :
    (∏ i ∈ range k, (r - (i : ℤ))) = (k.factorial : ℤ) * C r k := by
  have h1 : (∏ i ∈ range k, (r - (i : ℤ))) = (descPochhammer ℤ k).eval r :=
    (descPochhammer_eval_eq_prod_range k r).symm
  rw [h1, Polynomial.eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose]
  simp only [C, nsmul_eq_mul]

lemma genchoose_eq (r : ℤ) (k : ℕ) : generalized_choose_int r k = C r k := by
  unfold generalized_choose_int
  split_ifs with hk
  · subst hk; rw [C_zero]
  · rw [prod_eq_choose]
    rw [Int.mul_ediv_cancel_left]
    exact_mod_cast Nat.factorial_ne_zero k

-- absorption identity for Ring.choose
lemma choose_absorb (n : ℤ) (k : ℕ) :
    ((k : ℤ) + 1) * C n (k + 1) = (n - k) * C n k := by
  have e1 : (∏ i ∈ range (k+1), (n - (i : ℤ))) = ((k+1).factorial : ℤ) * C n (k+1) := prod_eq_choose n (k+1)
  have e2 : (∏ i ∈ range k, (n - (i : ℤ))) = (k.factorial : ℤ) * C n k := prod_eq_choose n k
  rw [Finset.prod_range_succ] at e1
  rw [e2] at e1
  -- e1 : (k! * C n k) * (n - k) = (k+1)! * C n (k+1)
  have hfac : ((k+1).factorial : ℤ) = ((k : ℤ) + 1) * (k.factorial : ℤ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hfac] at e1
  have hk : (k.factorial : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  -- (k! * C n k)*(n-k) = ((k+1)*k!) * C n (k+1)
  have : (k.factorial : ℤ) * (((k:ℤ)+1) * C n (k+1)) = (k.factorial : ℤ) * ((n - k) * C n k) := by
    rw [show (k.factorial : ℤ) * (((k:ℤ)+1) * C n (k+1)) = ((k:ℤ)+1) * (k.factorial : ℤ) * C n (k+1) by ring,
        ← e1]; ring
  exact mul_left_cancel₀ hk this

-- Off the pole, the generalized Catalan coefficient equals `Tt`.
lemma gcc_eq_Tt (r : ℤ) (j : ℕ) (h : r + ((j : ℤ) + 1) ≠ 0) :
    generalized_catalan_coefficient r (j + 1) = Tt r (j + 1) := by
  have hn : r + 2 * ((j + 1 : ℕ) : ℤ) - 1 = r + 2 * (j : ℤ) + 1 := by push_cast; ring
  set n : ℤ := r + 2 * (j : ℤ) + 1 with hndef
  have habs : ((j : ℤ) + 1) * C n (j + 1) = (n - j) * C n j := choose_absorb n j
  have hnj : n - (j : ℤ) = r + ((j : ℤ) + 1) := by rw [hndef]; push_cast; ring
  rw [hnj] at habs
  have hTt : Tt r (j + 1) = C n (j + 1) - C n j := by
    unfold Tt
    rw [if_neg (Nat.succ_ne_zero j)]
    have e2 : (j + 1) - 1 = j := rfl
    rw [e2, hn]
  have key : r * C n (j + 1) = (r + ((j : ℤ) + 1)) * Tt r (j + 1) := by
    rw [hTt, mul_sub, ← habs]; ring
  unfold generalized_catalan_coefficient
  rw [if_neg (Nat.succ_ne_zero j)]
  simp only [genchoose_eq, hn]
  have hden : r + ((j + 1 : ℕ) : ℤ) = r + ((j : ℤ) + 1) := by push_cast; ring
  rw [hden, key, Int.mul_ediv_cancel_left _ h]

-- k=0 term agreement
lemma gcc_zero (r : ℤ) : generalized_catalan_coefficient r 0 = Tt r 0 := by
  unfold generalized_catalan_coefficient Tt; simp

-- For m ≠ -1 and 1 ≤ k ≤ N, the pole is avoided.
lemma no_pole (m : ℤ) (N : ℕ) (hN : 0 < N) (hm : m ≠ -1) (j : ℕ) (hj : j + 1 ≤ N) :
    m * (N : ℤ) + ((j : ℤ) + 1) ≠ 0 := by
  intro heq
  have hNz : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  have hjN : ((j : ℤ) + 1) ≤ (N : ℤ) := by exact_mod_cast hj
  -- m*N = -(j+1) ≤ -1 < 0 ⟹ m ≤ -1 ; m*N ≥ -N ⟹ m ≥ -1
  have h1 : m * (N : ℤ) = -((j : ℤ) + 1) := by linarith
  have hle : m ≤ -1 := by nlinarith [h1, hNz]
  have hge : -1 ≤ m := by nlinarith [h1, hNz, hjN]
  exact hm (le_antisymm hle hge)

-- The pole value: gcc at the pole is 0, Tt at the pole is -1.
lemma gcc_pole (N : ℕ) (hN : 0 < N) : generalized_catalan_coefficient (-(N : ℤ)) N = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  unfold generalized_catalan_coefficient
  rw [if_neg (Nat.succ_ne_zero j)]
  simp only []
  have : -((j + 1 : ℕ) : ℤ) + ((j + 1 : ℕ) : ℤ) = 0 := by ring
  rw [this, Int.ediv_zero]

lemma Tt_pole (N : ℕ) (hN : 0 < N) : Tt (-(N : ℤ)) N = -1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  unfold Tt
  rw [if_neg (Nat.succ_ne_zero j)]
  have e2 : (j + 1) - 1 = j := rfl
  rw [e2]
  have htop : -((j + 1 : ℕ) : ℤ) + 2 * ((j + 1 : ℕ) : ℤ) - 1 = ((j : ℕ) : ℤ) := by push_cast; ring
  rw [htop]
  simp only [C, Ring.choose_natCast]
  rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_self]
  norm_num

lemma agen_eq (m : ℤ) (N : ℕ) (hN : 0 < N) :
    a_gen m N = Rr (m * (N : ℤ)) N + (if m = -1 then 1 else 0) := by
  rw [← phase1]
  unfold a_gen
  rw [if_neg hN.ne']
  simp only []
  by_cases hm : m = -1
  · -- pole case: peel k = N
    subst hm
    rw [if_pos rfl]
    have hmn : (-1 : ℤ) * (N : ℤ) = -(N : ℤ) := by ring
    rw [hmn]
    -- a_gen sum = Σ_{range N} gcc + gcc at N; and Ss = Σ_{range N} Tt + Tt at N
    rw [Finset.sum_range_succ]
    unfold Ss
    rw [Finset.sum_range_succ]
    rw [gcc_pole N hN, Tt_pole N hN]
    have hcongr : ∀ k ∈ Finset.range N, generalized_catalan_coefficient (-(N : ℤ)) k = Tt (-(N : ℤ)) k := by
      intro k hk
      simp only [Finset.mem_range] at hk
      cases k with
      | zero => exact gcc_zero _
      | succ j =>
        apply gcc_eq_Tt
        intro heq
        have hc : ((j : ℤ) + 1) = (N : ℤ) := by linarith
        have hjeq : j + 1 = N := by exact_mod_cast hc
        exact absurd hjeq (Nat.ne_of_lt hk)
    rw [Finset.sum_congr rfl hcongr]
    ring
  · rw [if_neg hm, add_zero]
    unfold Ss
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    cases k with
    | zero => exact gcc_zero _
    | succ j => exact gcc_eq_Tt _ j (no_pole m N hN hm j (by omega))

/-! ### Phase 2 (the supercongruence) and final assembly. -/

/-- The `F_s` form: `F s N = ∑_j hh(N-j) C(sN, j) = [y^N] (1+y)^{sN} G(y)`. -/
def Ff (s : ℤ) (N : ℕ) : ℤ := ∑ j ∈ range (N + 1), hh (N - j) * C (s * (N : ℤ)) j

lemma Rr_eq_Ff (m : ℤ) (N : ℕ) : Rr (m * (N : ℤ)) N = Ff (m + 2) N := by
  unfold Rr Ff
  rw [← Finset.sum_range_reflect (fun j => hh (N - j) * C ((m + 2) * (N : ℤ)) j) (N + 1)]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Finset.mem_range] at ht
  have h1 : N + 1 - 1 - t = N - t := by omega
  rw [h1]
  have h2 : N - (N - t) = t := by omega
  rw [h2]
  congr 2
  push_cast; ring

/-- The single-step supercongruence (the analytic core). -/
lemma single_step (s : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (M : ℕ) (hM : M > 0) :
    Ff s (p * M) ≡ Ff s M [ZMOD (p ^ (3 * (padicValNat p M + 1)) : ℤ)] := by
  sorry

-- The core supercongruence, stated on the clean `Rr` form.
lemma phase2 (m : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    Rr (m * ((n * p ^ k : ℕ) : ℤ)) (n * p ^ k)
      ≡ Rr (m * ((n * p ^ (k - 1) : ℕ) : ℤ)) (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  have hppos : 0 < p := by omega
  set M := n * p ^ (k - 1) with hMdef
  have hMpos : 0 < M := Nat.mul_pos hn (pow_pos hppos (k - 1))
  have hpM : n * p ^ k = p * M := by
    rw [hMdef, show p * (n * p ^ (k - 1)) = n * (p ^ (k - 1) * p) from by ring, ← pow_succ]
    have hk1 : (k - 1) + 1 = k := by omega
    rw [hk1]
  -- rewrite both Rr as Ff
  rw [Rr_eq_Ff m (n * p ^ k), Rr_eq_Ff m M]
  rw [hpM]
  -- reduce modulus: p^(3k) ∣ p^(3(e+1)) since e = v_p(M) ≥ k-1
  have hstep := single_step (m + 2) p hp hp5 M hMpos
  haveI : Fact p.Prime := ⟨hp⟩
  have he : k - 1 ≤ padicValNat p M := by
    rw [hMdef]
    have : padicValNat p (n * p ^ (k - 1)) = padicValNat p n + (k - 1) := by
      rw [padicValNat.mul (by omega) (by positivity)]
      rw [padicValNat.prime_pow]
    rw [this]; omega
  have hdvd : (p : ℤ) ^ (3 * k) ∣ (p : ℤ) ^ (3 * (padicValNat p M + 1)) := by
    apply pow_dvd_pow
    omega
  exact hstep.of_dvd hdvd


end

theorem oeis_333096_supercongruence_conjecture (m : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    a_gen m (n * p ^ k) ≡ a_gen m (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  have hppos : 0 < p := by omega
  have hA : 0 < n * p ^ k := Nat.mul_pos hn (pow_pos hppos k)
  have hB : 0 < n * p ^ (k - 1) := Nat.mul_pos hn (pow_pos hppos (k - 1))
  rw [agen_eq m _ hA, agen_eq m _ hB]
  exact (phase2 m p hp hp5 n k hn hk).add_right _

