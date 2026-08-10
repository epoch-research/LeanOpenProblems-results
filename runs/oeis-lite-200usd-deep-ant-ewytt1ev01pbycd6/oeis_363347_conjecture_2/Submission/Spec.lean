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

/--
A363347 Conjecture 2: The sequence contains all prime numbers which end with a 1 or 9.
-/

def aa (n : ℕ) : ℕ → ℤ
  | 0 => 4
  | 1 => 5 * (n : ℤ) - 4
  | (j+2) => ((n : ℤ) - (j+2)) * aa n (j+1) - ((n : ℤ) - (j+1)) * aa n j

/-- `pp n k = p_k`. -/
def pp (n k : ℕ) : ℤ := aa n (n - k)

lemma pp_top (n : ℕ) : pp n n = 4 := by
  simp [pp, aa]

lemma pp_top1 (n : ℕ) (hn : 1 ≤ n) : pp n (n-1) = 5 * (n:ℤ) - 4 := by
  have : n - (n-1) = 1 := by omega
  simp [pp, this, aa]

lemma aa_succ_succ (n j : ℕ) :
    aa n (j+2) = ((n : ℤ) - (j+2)) * aa n (j+1) - ((n : ℤ) - (j+1)) * aa n j := rfl

/-- The downward recursion in the `k` index. -/
lemma pp_rec (n k : ℕ) (hk : 2 ≤ k) (hkn : k + 2 ≤ n) :
    pp n k = (k:ℤ) * pp n (k+1) - (k+1) * pp n (k+2) := by
  set m := n - k - 2 with hm
  have e0 : n - k = m + 2 := by omega
  have e1 : n - (k+1) = m + 1 := by omega
  have e2 : n - (k+2) = m := by omega
  have hmz : (m : ℤ) = (n:ℤ) - k - 2 := by omega
  have c1 : (n : ℤ) - ((m:ℤ)+2) = k := by rw [hmz]; ring
  have c2 : (n : ℤ) - ((m:ℤ)+1) = k + 1 := by rw [hmz]; ring
  have hlhs : pp n k = ((n : ℤ) - ((m:ℤ)+2)) * aa n (m+1) - ((n : ℤ) - ((m:ℤ)+1)) * aa n m := by
    rw [pp, e0, aa_succ_succ]
  rw [hlhs, c1, c2]
  have r1 : aa n (m+1) = pp n (k+1) := by rw [pp, e1]
  have r2 : aa n m = pp n (k+2) := by rw [pp, e2]
  rw [r1, r2]

/-- A `k`-indexed sequence solves the recursion up to `n`. -/
def IsSol (n : ℕ) (X : ℕ → ℤ) : Prop :=
  ∀ k, 2 ≤ k → k + 2 ≤ n → X k = (k:ℤ) * X (k+1) - (k+1) * X (k+2)

lemma pp_isSol (n : ℕ) : IsSol n (pp n) := fun k hk hkn => pp_rec n k hk hkn

/-- Companion sequence, base `att n 0 = 0`, `att n 1 = 1`. -/
def att (n : ℕ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (j+2) => ((n : ℤ) - (j+2)) * att n (j+1) - ((n : ℤ) - (j+1)) * att n j

def pt (n k : ℕ) : ℤ := att n (n - k)

lemma att_succ_succ (n j : ℕ) :
    att n (j+2) = ((n : ℤ) - (j+2)) * att n (j+1) - ((n : ℤ) - (j+1)) * att n j := rfl

lemma pt_top (n : ℕ) : pt n n = 0 := by simp [pt, att]
lemma pt_top1 (n : ℕ) (hn : 1 ≤ n) : pt n (n-1) = 1 := by
  have : n - (n-1) = 1 := by omega
  simp [pt, this, att]

lemma pt_rec (n k : ℕ) (hk : 2 ≤ k) (hkn : k + 2 ≤ n) :
    pt n k = (k:ℤ) * pt n (k+1) - (k+1) * pt n (k+2) := by
  set m := n - k - 2 with hm
  have e0 : n - k = m + 2 := by omega
  have e1 : n - (k+1) = m + 1 := by omega
  have e2 : n - (k+2) = m := by omega
  have hmz : (m : ℤ) = (n:ℤ) - k - 2 := by omega
  have c1 : (n : ℤ) - ((m:ℤ)+2) = k := by rw [hmz]; ring
  have c2 : (n : ℤ) - ((m:ℤ)+1) = k + 1 := by rw [hmz]; ring
  have hlhs : pt n k = ((n : ℤ) - ((m:ℤ)+2)) * att n (m+1) - ((n : ℤ) - ((m:ℤ)+1)) * att n m := by
    rw [pt, e0, att_succ_succ]
  rw [hlhs, c1, c2]
  have r1 : att n (m+1) = pt n (k+1) := by rw [pt, e1]
  have r2 : att n m = pt n (k+2) := by rw [pt, e2]
  rw [r1, r2]

lemma pt_isSol (n : ℕ) : IsSol n (pt n) := fun k hk hkn => pt_rec n k hk hkn

/-! ### Casoratian telescoping. -/

/-- Casoratian of two sequences. -/
def Cas (X Y : ℕ → ℤ) (k : ℕ) : ℤ := X k * Y (k+1) - X (k+1) * Y k

/-- `cprod n k = k*(k+1)*...*(n-1)`. -/
def cprod (n k : ℕ) : ℤ := ∏ i ∈ Finset.Ico k n, (i:ℤ)

lemma Cas_step (n : ℕ) (X Y : ℕ → ℤ) (hX : IsSol n X) (hY : IsSol n Y)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k + 2 ≤ n) :
    Cas X Y k = (k+1 : ℤ) * Cas X Y (k+1) := by
  have hx := hX k hk hkn
  have hy := hY k hk hkn
  simp only [Cas]
  rw [hx, hy]; ring

/-- Telescoped Casoratian: `Cas X Y 2 = cprod n 3 * Cas X Y (n-1)`. -/
lemma Cas_telescope (n : ℕ) (X Y : ℕ → ℤ) (hX : IsSol n X) (hY : IsSol n Y)
    (hn : 3 ≤ n) :
    Cas X Y 2 = cprod n 3 * Cas X Y (n-1) := by
  -- prove: for 2 ≤ j ≤ n-1, Cas X Y 2 = (∏ i ∈ Ico 3 (j+1)) * Cas X Y j
  have key : ∀ j, 2 ≤ j → j ≤ n - 1 →
      Cas X Y 2 = (∏ i ∈ Finset.Ico 3 (j+1), (i:ℤ)) * Cas X Y j := by
    intro j
    induction j with
    | zero => intro hj _; omega
    | succ m ih =>
      intro hj hmn
      rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · -- m+1 = 2, so m = 1
        interval_cases m
        · omega
        · simp
      · -- m ≥ 2, use step
        have hmn' : m ≤ n - 1 := by omega
        have ihm := ih hm2 hmn'
        have hstep : Cas X Y m = (m+1 : ℤ) * Cas X Y (m+1) :=
          Cas_step n X Y hX hY m hm2 (by omega)
        rw [ihm, hstep]
        have : (∏ i ∈ Finset.Ico 3 (m+1+1), (i:ℤ))
            = (∏ i ∈ Finset.Ico 3 (m+1), (i:ℤ)) * (m+1 : ℤ) := by
          rw [Finset.prod_Ico_succ_top (by omega)]; push_cast; ring
        rw [this]; ring
  have hk := key (n-1) (by omega) (le_refl _)
  rw [hk, show n-1+1 = n from by omega]
  rfl

lemma cprod_rec (n k : ℕ) (h : k < n) : cprod n k = (k:ℤ) * cprod n (k+1) := by
  unfold cprod
  rw [← Finset.insert_Ico_add_one_left_eq_Ico h, Finset.prod_insert]
  simp

lemma cprod_pos (n k : ℕ) (hk : 1 ≤ k) : 0 < cprod n k := by
  unfold cprod
  apply Finset.prod_pos
  intro i hi
  simp only [Finset.mem_Ico] at hi
  have : 1 ≤ i := by omega
  exact_mod_cast this

/-- The explicit rational solution scaled to integers: `psiZ n k = (2-k) * cprod n k`. -/
def psiZ (n k : ℕ) : ℤ := (2 - (k:ℤ)) * cprod n k

lemma psiZ_isSol (n : ℕ) : IsSol n (psiZ n) := by
  intro k hk hkn
  have h1 : cprod n k = (k:ℤ) * cprod n (k+1) := cprod_rec n k (by omega)
  have h2 : cprod n (k+1) = ((k:ℤ)+1) * cprod n (k+2) := by
    have := cprod_rec n (k+1) (by omega); push_cast at this ⊢; linarith [this]
  simp only [psiZ]
  push_cast
  rw [h1, h2]
  ring

lemma cprod_self (n : ℕ) : cprod n n = 1 := by
  simp [cprod]

lemma cprod_pred (n : ℕ) (hn : 1 ≤ n) : cprod n (n-1) = ((n:ℤ) - 1) := by
  have h := cprod_rec n (n-1) (by omega)
  rw [show n-1+1 = n from by omega, cprod_self] at h
  rw [h]
  push_cast [Nat.cast_sub hn]
  ring

/-- Value of `psiZ` at the top. -/
lemma psiZ_top (n : ℕ) : psiZ n n = 2 - (n:ℤ) := by
  simp [psiZ, cprod_self]

lemma psiZ_pred (n : ℕ) (hn : 1 ≤ n) : psiZ n (n-1) = (3 - (n:ℤ)) * ((n:ℤ) - 1) := by
  simp only [psiZ, cprod_pred n hn]
  have : ((n-1 : ℕ) : ℤ) = (n:ℤ) - 1 := by omega
  rw [this]; ring

lemma psiZ_two (n : ℕ) : psiZ n 2 = 0 := by simp [psiZ]
lemma psiZ_three (n : ℕ) : psiZ n 3 = - cprod n 3 := by unfold psiZ; norm_num

/-! ### Key identities via Casoratian. -/

/-- `pt n 2 = n - 2` (companion value at bottom). -/
lemma pt_two (n : ℕ) (hn : 4 ≤ n) : pt n 2 = (n:ℤ) - 2 := by
  have hT := Cas_telescope n (pt n) (psiZ n) (pt_isSol n) (psiZ_isSol n) (by omega)
  -- LHS: Cas (pt n) (psiZ n) 2 = pt n 2 * psiZ n 3 - pt n 3 * psiZ n 2 = - pt n 2 * cprod n 3
  have hL : Cas (pt n) (psiZ n) 2 = - pt n 2 * cprod n 3 := by
    simp only [Cas]; rw [show (2:ℕ)+1=3 from rfl, psiZ_three, psiZ_two]; ring
  -- RHS endpoint: Cas (pt n) (psiZ n) (n-1) = pt n (n-1) * psiZ n n - pt n n * psiZ n (n-1)
  have hpm : n - 1 + 1 = n := by omega
  have hR : Cas (pt n) (psiZ n) (n-1) = (2 - (n:ℤ)) := by
    simp only [Cas, hpm]
    rw [pt_top1 n (by omega), pt_top n, psiZ_top n, psiZ_pred n (by omega)]
    ring
  rw [hL, hR] at hT
  have hc : (0:ℤ) < cprod n 3 := cprod_pos n 3 (by omega)
  -- - pt n 2 * cprod n 3 = cprod n 3 * (2 - n)
  have : - pt n 2 * cprod n 3 = cprod n 3 * (2 - (n:ℤ)) := hT
  have h2 : - pt n 2 = (2 - (n:ℤ)) := by
    have := mul_right_cancel₀ (ne_of_gt hc) (by linarith [this] : - pt n 2 * cprod n 3 = (2 - (n:ℤ)) * cprod n 3)
    linarith [this]
  linarith

/-- `pp n 2 = n^2 + 2n - 4`. -/
lemma pp_two (n : ℕ) (hn : 4 ≤ n) : pp n 2 = (n:ℤ)^2 + 2*(n:ℤ) - 4 := by
  have hT := Cas_telescope n (pp n) (psiZ n) (pp_isSol n) (psiZ_isSol n) (by omega)
  have hL : Cas (pp n) (psiZ n) 2 = - pp n 2 * cprod n 3 := by
    simp only [Cas]; rw [show (2:ℕ)+1=3 from rfl, psiZ_three, psiZ_two]; ring
  have hpm : n - 1 + 1 = n := by omega
  have hR : Cas (pp n) (psiZ n) (n-1) = -((n:ℤ)^2 + 2*(n:ℤ) - 4) := by
    simp only [Cas, hpm]
    rw [pp_top1 n (by omega), pp_top n, psiZ_top n, psiZ_pred n (by omega)]
    ring
  rw [hL, hR] at hT
  have hc : (0:ℤ) < cprod n 3 := cprod_pos n 3 (by omega)
  have h2 : - pp n 2 = -((n:ℤ)^2 + 2*(n:ℤ) - 4) := by
    have := mul_right_cancel₀ (ne_of_gt hc)
      (by linarith [hT] : - pp n 2 * cprod n 3 = (-((n:ℤ)^2 + 2*(n:ℤ) - 4)) * cprod n 3)
    exact this
  linarith

/-- Identity (2): `(n-2) * p_3 = p_2 * pt_3 + 4 * cprod n 3`. Note `4*cprod n 3 = 2*(n-1)!`. -/
lemma ident2 (n : ℕ) (hn : 4 ≤ n) :
    ((n:ℤ) - 2) * pp n 3 = pp n 2 * pt n 3 + 4 * cprod n 3 := by
  have hT := Cas_telescope n (pp n) (pt n) (pp_isSol n) (pt_isSol n) (by omega)
  have hL : Cas (pp n) (pt n) 2 = pp n 2 * pt n 3 - pp n 3 * ((n:ℤ) - 2) := by
    simp only [Cas]; rw [show (2:ℕ)+1=3 from rfl, pt_two n hn]
  have hpm : n - 1 + 1 = n := by omega
  have hR : Cas (pp n) (pt n) (n-1) = -4 := by
    simp only [Cas, hpm]
    rw [pp_top1 n (by omega), pp_top n, pt_top n, pt_top1 n (by omega)]
    ring
  rw [hL, hR] at hT
  -- pp2*pt3 - pp3*(n-2) = cprod n 3 * (-4)
  linarith [hT]

/-! ### Positivity of the sequence. -/

/-- Two-sided bound invariant, proved by (downward) induction. -/
lemma pp_inv (n : ℕ) (hn : 4 ≤ n) :
    ∀ i k, k + i = n - 2 → 3 ≤ k →
      0 < pp n (k+1) ∧ ((k:ℤ)-2) * pp n (k+1) < pp n k ∧ pp n k < (k:ℤ) * pp n (k+1) := by
  intro i
  induction i with
  | zero =>
    intro k hk hk3
    have hkn2 : k = n - 2 := by omega
    subst hkn2
    have hrec := pp_rec n (n-2) (by omega) (by omega)
    rw [show (n-2)+1 = n-1 from by omega, show (n-2)+2 = n from by omega] at hrec
    rw [pp_top1 n (by omega), pp_top n] at hrec
    have hc : ((n-2:ℕ):ℤ) = (n:ℤ) - 2 := by omega
    rw [hc] at hrec
    have he1 : (n-2)+1 = n-1 := by omega
    have hN : (4:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
    refine ⟨?_, ?_, ?_⟩
    · rw [he1, pp_top1 n (by omega)]; nlinarith [hN]
    · rw [he1, hrec, pp_top1 n (by omega), hc]; nlinarith [hN]
    · rw [he1, hrec, pp_top1 n (by omega), hc]; nlinarith [hN]
  | succ j ih =>
    intro k hk hk3
    have hIH := ih (k+1) (by omega) (by omega)
    obtain ⟨hpos2, hlo1, hhi1⟩ := hIH
    -- hpos2 : 0 < pp n (k+2), etc. with cast (k+1)
    have hrec := pp_rec n k (by omega) (by omega)
    set K := (k:ℤ) with hKdef
    have hK3 : 3 ≤ K := by rw [hKdef]; exact_mod_cast hk3
    have hcast : ((k+1:ℕ):ℤ) = K + 1 := by push_cast; ring
    rw [hcast] at hlo1 hhi1
    -- pp n (k+2) > 0, K-1 relation
    refine ⟨?_, ?_, ?_⟩
    · -- 0 < pp n (k+1): from hlo1 : (K-1)*pp(k+2) < pp(k+1)
      nlinarith [hpos2, hlo1, hK3]
    · rw [hrec]; nlinarith [hpos2, hlo1, hhi1, hK3]
    · rw [hrec]; nlinarith [hpos2, hlo1, hhi1, hK3]

lemma pp_pos (n : ℕ) (hn : 4 ≤ n) (k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) : 0 < pp n k := by
  rcases Nat.lt_or_ge k (n-1) with h | h
  · -- k ≤ n-2, use invariant at k
    have := (pp_inv n hn (n-2-k) k (by omega) hk).1
    -- gives 0 < pp n (k+1); need 0 < pp n k. Instead use lower bound.
    have h2 := (pp_inv n hn (n-2-k) k (by omega) hk).2.1
    have h3 := (pp_inv n hn (n-2-k) k (by omega) hk).1
    have hK : (3:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk
    nlinarith [h2, h3, hK]
  · -- k = n-1 or k = n
    have : k = n-1 ∨ k = n := by omega
    rcases this with h1 | h1
    · rw [h1, pp_top1 n (by omega)]; push_cast; omega
    · rw [h1, pp_top n]; norm_num

lemma pp_two_pos (n : ℕ) (hn : 4 ≤ n) : 0 < pp n 2 := by
  rw [pp_two n hn]; nlinarith [hn, (by exact_mod_cast hn : (4:ℤ) ≤ (n:ℤ))]

/-! ### Relating the continued fraction to the integer ratios. -/

lemma cfd_base (n : ℕ) (hn : 3 ≤ n) :
    continued_fraction_denominator n (n-1) = (↑(n-1) : ℚ) + ↑n / 4 := by
  rw [continued_fraction_denominator]
  have h1 : ¬ (n ≤ 2) := by omega
  have h2 : 2 ≤ n-1 ∧ n-1 ≤ n-1 := by omega
  simp only [h1, h2, if_true, and_self, if_false, if_pos]

lemma cfd_step (n k : ℕ) (hn : 3 ≤ n) (hk : 2 ≤ k) (hk2 : k < n - 1) :
    continued_fraction_denominator n k
      = (↑k : ℚ) - (↑k + 1) / continued_fraction_denominator n (k+1) := by
  rw [continued_fraction_denominator]
  have h1 : ¬ (n ≤ 2) := by omega
  have h2 : 2 ≤ k ∧ k ≤ n-1 := by omega
  have h3 : k ≠ n - 1 := by omega
  simp only [h1, h2, if_true, and_self, if_false, if_neg h3]

/-- The continued fraction equals the ratio of consecutive numerators. -/
lemma cfd_eq_ratio (n : ℕ) (hn : 3 ≤ n) :
    ∀ i k, k + i = n - 1 → 2 ≤ k →
      continued_fraction_denominator n k = (pp n k : ℚ) / (pp n (k+1) : ℚ) := by
  intro i
  induction i with
  | zero =>
    intro k hk hk2
    have hkeq : k = n - 1 := by omega
    subst hkeq
    rw [cfd_base n hn, pp_top1 n (by omega), show (n-1)+1 = n from by omega, pp_top n]
    rw [Nat.cast_sub (show 1 ≤ n by omega)]
    push_cast
    ring
  | succ j ih =>
    intro k hk hk2
    have hk3 : k < n - 1 := by omega
    have hn4 : 4 ≤ n := by omega
    have hIH := ih (k+1) (by omega) (by omega)
    rw [cfd_step n k hn hk2 hk3, hIH]
    -- pp(k+1)>0, pp(k+2)>0
    have hp1 : 0 < pp n (k+1) := pp_pos n hn4 (k+1) (by omega) (by omega)
    have hp2 : 0 < pp n (k+2) := pp_pos n hn4 (k+2) (by omega) (by omega)
    have hp1' : (pp n (k+1) : ℚ) ≠ 0 := by exact_mod_cast hp1.ne'
    have hp2' : (pp n (k+2) : ℚ) ≠ 0 := by exact_mod_cast hp2.ne'
    have hrec := pp_rec n k hk2 (by omega)
    have hrecQ : (pp n k : ℚ) = (k:ℚ) * (pp n (k+1):ℚ) - ((k:ℚ)+1) * (pp n (k+2):ℚ) := by
      exact_mod_cast hrec
    rw [show k+1+1 = k+2 from rfl, hrecQ]
    field_simp

/-! ### Factorial divisibility. -/

/-- If `a*q ≤ m` and `q` is prime, then `q^a ∣ m!`. -/
lemma pow_dvd_factorial (q a m : ℕ) (hq : q.Prime) (h : a * q ≤ m) : q ^ a ∣ m ! := by
  rw [Nat.Prime.pow_dvd_iff_le_factorization hq (Nat.factorial_ne_zero m)]
  have hq1 : 1 ≤ q := hq.one_lt.le
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · simp [ha0]
  · -- a ≥ 1, so m ≥ a*q ≥ q ≥ 2, so m ≥ 1
    have hm1 : 1 ≤ m := by nlinarith [hq.two_le, ha0]
    have hb : Nat.log q m < m + 1 := by
      have := Nat.log_le_self q m
      omega
    rw [Nat.factorization_factorial hq hb]
    have hmem : 1 ∈ Finset.Ico 1 (m+1) := by simp; omega
    have hterm : a ≤ m / q ^ 1 := by
      simp only [pow_one]
      rw [Nat.le_div_iff_mul_le (by omega)]
      exact h
    calc a ≤ m / q ^ 1 := hterm
      _ ≤ ∑ i ∈ Finset.Ico 1 (m+1), m / q ^ i :=
          Finset.single_le_sum (f := fun i => m / q ^ i) (by intro i _; exact Nat.zero_le _) hmem

/-- The nat product `∏ i ∈ Ico 3 n, i` equals `(n-1)! / 2` in the form `(n-1)! = 2 * prod`. -/
lemma factorial_eq_two_mul_prod (n : ℕ) (hn : 3 ≤ n) :
    (n-1)! = 2 * ∏ i ∈ Finset.Ico 3 n, i := by
  have h1 : (∏ x ∈ Finset.Ico 1 n, x) = (n-1)! := by
    have := Finset.prod_Ico_id_eq_factorial (n-1)
    rwa [show n-1+1 = n from by omega] at this
  have hsplit : Finset.Ico 1 n = insert 1 (insert 2 (Finset.Ico 3 n)) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  rw [← h1, hsplit]
  rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp)]
  ring

/-- Cast version: `4 * cprod n 3 = 2 * (n-1)!`. -/
lemma four_cprod_eq (n : ℕ) (hn : 3 ≤ n) :
    4 * cprod n 3 = 2 * ((n-1)! : ℤ) := by
  unfold cprod
  have hnat := factorial_eq_two_mul_prod n hn
  have : (∏ i ∈ Finset.Ico 3 n, (i:ℤ)) = ((∏ i ∈ Finset.Ico 3 n, i : ℕ) : ℤ) := by
    push_cast; rfl
  rw [this]
  have : ((n-1)! : ℤ) = 2 * ((∏ i ∈ Finset.Ico 3 n, i : ℕ) : ℤ) := by
    rw [hnat]; push_cast; ring
  rw [this]; ring

/-! ### Claim B: the large prime survives. -/

/-- Forward propagation: if a prime `p > n` divides `pp n 2` and `pp n 3`, it divides all `pp n k`. -/
lemma pp_forward (n p : ℕ) (hn : 4 ≤ n) (hp : p.Prime) (hpn : n < p)
    (h2 : (p:ℤ) ∣ pp n 2) (h3 : (p:ℤ) ∣ pp n 3) :
    ∀ k, 2 ≤ k → k ≤ n → (p:ℤ) ∣ pp n k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk2 hkn
    match k, hk2 with
    | 2, _ => exact h2
    | 3, _ => exact h3
    | (m+4), _ =>
      -- index k = m+4 ≥ 4. Use recursion at j = m+2.
      have hj := ih (m+2) (by omega) (by omega) (by omega)
      have hj1 := ih (m+3) (by omega) (by omega) (by omega)
      -- pp_rec n (m+2): pp n (m+2) = (m+2)*pp n (m+3) - (m+3)*pp n (m+4)
      have hrec := pp_rec n (m+2) (by omega) (by omega)
      -- so (m+3)*pp n (m+4) = (m+2)*pp n (m+3) - pp n (m+2)
      have hdvd : (p:ℤ) ∣ ((m+3 : ℤ)) * pp n (m+4) := by
        have : ((m+3:ℤ)) * pp n (m+4) = (m+2 : ℤ) * pp n (m+3) - pp n (m+2) := by
          have h' : pp n (m+2) = (↑(m+2)) * pp n (m+2+1) - (↑(m+2)+1) * pp n (m+2+2) := hrec
          push_cast at h' ⊢
          rw [show m+2+1 = m+3 from rfl, show m+2+2 = m+4 from rfl] at h'
          linarith [h']
        rw [this]
        exact dvd_sub (Dvd.dvd.mul_left hj1 _) hj
      -- p ∤ (m+3) since 0 < m+3 ≤ n < p
      have hp3 : ¬ (p:ℤ) ∣ ((m+3:ℤ)) := by
        intro hc
        have : (p:ℤ) ≤ (m+3:ℤ) := Int.le_of_dvd (by positivity) hc
        have : p ≤ m+3 := by exact_mod_cast this
        omega
      -- p prime divides product, doesn't divide first factor, so divides second
      have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
      rcases (hpp.dvd_mul.mp hdvd) with h | h
      · exact absurd h hp3
      · exact h

/-- Claim B: prime `p > n` dividing `pp n 2` does not divide `pp n 3`. -/
lemma claimB (n p : ℕ) (hn : 4 ≤ n) (hp : p.Prime) (hpn : n < p)
    (h2 : (p:ℤ) ∣ pp n 2) : ¬ (p:ℤ) ∣ pp n 3 := by
  intro h3
  have hall := pp_forward n p hn hp hpn h2 h3 n (by omega) (le_refl n)
  rw [pp_top n] at hall
  -- p | 4, p prime > n ≥ 4, contradiction
  have : (p:ℤ) ≤ 4 := Int.le_of_dvd (by norm_num) hall
  have : p ≤ 4 := by exact_mod_cast this
  omega



/-! ### Modular non-divisibility facts about `P2 = pp n 2`. -/

lemma not_dvd_3 (n : ℕ) (hn : 4 ≤ n) : ¬ (3:ℤ) ∣ pp n 2 := by
  rw [pp_two n hn]
  intro h
  have h3 : ((3:ℕ):ℤ) ∣ ((n:ℤ)^2 + 2*(n:ℤ) - 4) := by exact_mod_cast h
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h3
  push_cast at hz
  have hx : ∀ x : ZMod 3, x^2 + 2*x - 4 ≠ 0 := by decide
  exact hx (n : ZMod 3) hz

lemma not_dvd_7 (n : ℕ) (hn : 4 ≤ n) : ¬ (7:ℤ) ∣ pp n 2 := by
  rw [pp_two n hn]
  intro h
  have h3 : ((7:ℕ):ℤ) ∣ ((n:ℤ)^2 + 2*(n:ℤ) - 4) := by exact_mod_cast h
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr h3
  push_cast at hz
  have hx : ∀ x : ZMod 7, x^2 + 2*x - 4 ≠ 0 := by decide
  exact hx (n : ZMod 7) hz

lemma not_dvd_25 (n : ℕ) (hn : 4 ≤ n) : ¬ (25:ℤ) ∣ pp n 2 := by
  rw [pp_two n hn]
  intro h
  have h3 : ((25:ℕ):ℤ) ∣ ((n:ℤ)^2 + 2*(n:ℤ) - 4) := by exact_mod_cast h
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 25).mpr h3
  push_cast at hz
  have hx : ∀ x : ZMod 25, x^2 + 2*x - 4 ≠ 0 := by decide
  exact hx (n : ZMod 25) hz

/-! ### Growth inequality for the `a ≥ 3` case. -/

lemma pow_gt (q : ℕ) (hq : 11 ≤ q) : ∀ a, 3 ≤ a → (a*q+1)^2 < q^a := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base =>
    -- (3q+1)^2 < q^3
    nlinarith [hq, sq_nonneg q, Nat.mul_le_mul hq hq]
  | succ a ha ihv =>
    -- q^(a+1) = q * q^a > q * (a*q+1)^2 ≥ ((a+1)*q+1)^2
    have h1 : q * (a*q+1)^2 < q * q^a :=
      mul_lt_mul_of_pos_left ihv (by omega)
    have h2 : ((a+1)*q+1)^2 ≤ q * (a*q+1)^2 := by
      nlinarith [hq, ha, Nat.mul_le_mul hq (le_refl a)]
    calc ((a+1)*q+1)^2 ≤ q * (a*q+1)^2 := h2
      _ < q * q^a := h1
      _ = q^(a+1) := by rw [pow_succ]; ring

/-! ### The Diophantine bound `a*q ≤ n-1`. -/

/-- For an odd prime `q ≤ n` with `q^a ∣ P2`, we have `a*q ≤ n-1`. -/
lemma diophantine (n q a : ℕ) (hn : 4 ≤ n) (hq : q.Prime) (hqn : q ≤ n)
    (hqodd : q ≠ 2) (ha : (q:ℤ)^a ∣ pp n 2) : a * q ≤ n - 1 := by
  by_contra hcon
  push_neg at hcon  -- n - 1 < a * q
  have hP2 : pp n 2 = (n:ℤ)^2 + 2*(n:ℤ) - 4 := pp_two n hn
  have hP2pos : 0 < pp n 2 := pp_two_pos n hn
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    rcases hq.eq_two_or_odd with h | h
    · exact absurd h hqodd
    · omega
  have hqZ : (3:ℤ) ≤ (q:ℤ) := by exact_mod_cast hq3
  -- convenient: N1 = n+1
  set N1 : ℤ := (n:ℤ) + 1 with hN1
  have hN1P2 : pp n 2 = N1^2 - 5 := by rw [hP2, hN1]; ring
  -- match on a
  match a, ha with
  | 0, _ => simp only [Nat.zero_mul] at hcon; omega
  | 1, ha1 =>
    -- q | P2, and hcon: n-1 < q, q ≤ n ⟹ q = n
    have hqn' : q = n := by omega
    -- (n:ℤ) | P2
    have hdvd : (n:ℤ) ∣ pp n 2 := by
      have : (q:ℤ) ∣ pp n 2 := by simpa using ha1
      rwa [hqn'] at this
    rw [hP2] at hdvd
    have h4 : (n:ℤ) ∣ 4 := by
      have hnn : (n:ℤ) ∣ ((n:ℤ)^2 + 2*(n:ℤ)) := ⟨(n:ℤ)+2, by ring⟩
      have := dvd_sub hnn hdvd
      simpa using this
    have hn4 : n ∣ 4 := by exact_mod_cast h4
    have : n ≤ 4 := Nat.le_of_dvd (by norm_num) hn4
    have hn4' : n = 4 := by omega
    rw [hn4'] at hqn'
    rw [hqn'] at hq
    exact absurd hq (by decide)
  | 2, ha2 =>
    -- q^2 | P2, hcon: n-1 < 2q ⟹ n ≤ 2q
    have hn2q : (N1 : ℤ) ≤ 2*(q:ℤ) + 1 := by
      have : n ≤ 2*q := by omega
      have : (n:ℤ) ≤ 2*(q:ℤ) := by exact_mod_cast this
      rw [hN1]; linarith
    have hN1lo : (q:ℤ) + 1 ≤ N1 := by
      have : (q:ℤ) ≤ (n:ℤ) := by exact_mod_cast hqn
      rw [hN1]; linarith
    obtain ⟨d, hd⟩ := ha2
    -- pp n 2 = q^2 * d  and pp n 2 = N1^2 - 5
    have heq : N1^2 = (q:ℤ)^2 * d + 5 := by
      have := hN1P2.symm.trans hd
      linarith [this]
    have hdpos : 1 ≤ d := by nlinarith [hP2pos, hd, sq_nonneg (q:ℤ)]
    have hdle : d ≤ 4 := by nlinarith [heq, hn2q, hN1lo, hqZ]
    interval_cases d
    · -- d = 1 : N1^2 = q^2 + 5
      nlinarith [heq, hN1lo, hqZ]
    · -- d = 2 : N1^2 = 2 q^2 + 5, mod 8 with q odd
      obtain ⟨t, ht⟩ := (hq.odd_of_ne_two hqodd)
      have htZ : (q:ℤ) = 2*(t:ℤ) + 1 := by exact_mod_cast ht
      have h8 : N1^2 = 8*(t:ℤ)^2 + 8*(t:ℤ) + 7 := by rw [htZ] at heq; ring_nf at heq ⊢; linarith [heq]
      have hkey : (N1 : ZMod 8)^2 = 7 := by
        have h := congrArg (Int.cast : ℤ → ZMod 8) h8
        push_cast at h
        rw [h]
        simp only [show (8:ZMod 8) = 0 from by decide, zero_mul, zero_add]
      have hx : ∀ x : ZMod 8, x^2 ≠ 7 := by decide
      exact hx _ hkey
    · -- d = 3 : N1^2 = 3 q^2 + 5, mod 3
      have hkey : (N1 : ZMod 3)^2 = 2 := by
        have h := congrArg (Int.cast : ℤ → ZMod 3) heq
        push_cast at h
        rw [h]
        simp only [show (3:ZMod 3) = 0 from by decide, zero_mul, mul_zero, zero_add]
        decide
      have hx : ∀ x : ZMod 3, x^2 ≠ 2 := by decide
      exact hx _ hkey
    · -- d = 4 : N1^2 = 4 q^2 + 5
      rcases (by omega : N1 = 2*(q:ℤ)+1 ∨ N1 ≤ 2*(q:ℤ)) with h | h
      · rw [h] at heq; nlinarith [heq, hqZ]
      · nlinarith [heq, h, hN1lo, hqZ]
  | (k+3), hak =>
    -- a = k+3 ≥ 3. Get q ≥ 11 and use pow_gt.
    have hne3 : q ≠ 3 := by
      rintro rfl
      have : (3:ℤ) ∣ pp n 2 := dvd_trans (by norm_num) hak
      exact not_dvd_3 n hn this
    have hne7 : q ≠ 7 := by
      rintro rfl
      have : (7:ℤ) ∣ pp n 2 := dvd_trans (by norm_num) hak
      exact not_dvd_7 n hn this
    have hne5 : q ≠ 5 := by
      rintro rfl
      have h25 : (25:ℤ) ∣ pp n 2 := by
        have : ((5:ℤ)^2) ∣ (5:ℤ)^(k+3) := pow_dvd_pow 5 (by omega)
        have := dvd_trans this hak
        simpa using this
      exact not_dvd_25 n hn h25
    have hq11 : 11 ≤ q := by
      by_contra hlt
      push_neg at hlt
      have := hq.two_le
      interval_cases q <;> first
        | (exact absurd hq (by decide))
        | omega
    -- q^(k+3) ≤ P2 = N1^2 - 5 < N1^2 ≤ (a*q+1)^2, but (a*q+1)^2 < q^(k+3)
    have hqa_le : (q:ℤ)^(k+3) ≤ pp n 2 := Int.le_of_dvd hP2pos hak
    have hn_le : (n:ℤ) ≤ ((k+3)*q : ℕ) := by
      have : n ≤ (k+3)*q := by omega
      exact_mod_cast this
    have hgt := pow_gt q hq11 (k+3) (by omega)
    -- (( (k+3)*q + 1)^2 : ℕ) < q^(k+3)
    have hgtZ : (((k+3)*q + 1 : ℕ) : ℤ)^2 < ((q:ℤ))^(k+3) := by
      have : ((((k+3)*q+1)^2 : ℕ) : ℤ) < (((q^(k+3)) : ℕ) : ℤ) := by exact_mod_cast hgt
      push_cast at this ⊢
      convert this using 2 <;> push_cast <;> ring
    -- N1 ≤ (k+3)*q + 1
    have hN1_le : N1 ≤ (((k+3)*q + 1 : ℕ) : ℤ) := by
      rw [hN1]; push_cast; push_cast at hn_le; linarith [hn_le]
    have hN1pos : 0 < N1 := by rw [hN1]; positivity
    nlinarith [hqa_le, hN1P2, hgtZ, hN1_le, hN1pos]

/-! ### Smooth cancellation. -/

/-- For an odd prime `q ≤ n`, the exact power of `q` dividing `P2` also divides `P3`. -/
lemma smooth_cancel (n q : ℕ) (hn : 4 ≤ n) (hq : q.Prime) (hqn : q ≤ n) (hqodd : q ≠ 2) :
    (q:ℤ)^((pp n 2).natAbs.factorization q) ∣ pp n 3 := by
  set a := (pp n 2).natAbs.factorization q with ha_def
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    rcases hq.eq_two_or_odd with h | h
    · exact absurd h hqodd
    · omega
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · rw [ha0]; simp
  · have hP2pos : 0 < pp n 2 := pp_two_pos n hn
    have hcast : ((pp n 2).natAbs : ℤ) = pp n 2 := Int.natAbs_of_nonneg hP2pos.le
    -- q^a | pp n 2
    have hqa_P2 : (q:ℤ)^a ∣ pp n 2 := by
      have h2 : (q^a) ∣ (pp n 2).natAbs := Nat.ordProj_dvd (pp n 2).natAbs q
      have h3 : ((q^a : ℕ):ℤ) ∣ ((pp n 2).natAbs : ℤ) := Int.natCast_dvd_natCast.mpr h2
      rw [hcast] at h3
      push_cast at h3
      exact h3
    -- diophantine bound and q^a | 2*(n-1)!
    have hdioph : a * q ≤ n - 1 := diophantine n q a hn hq hqn hqodd hqa_P2
    have hfact : q^a ∣ (n-1)! := pow_dvd_factorial q a (n-1) hq hdioph
    have hqa_cprod : (q:ℤ)^a ∣ 4 * cprod n 3 := by
      rw [four_cprod_eq n (by omega)]
      have h3 : ((q^a:ℕ):ℤ) ∣ ((n-1)! : ℤ) := Int.natCast_dvd_natCast.mpr hfact
      push_cast at h3
      exact Dvd.dvd.mul_left h3 2
    -- q ∤ (n-2)
    have hqnd : ¬ (q:ℤ) ∣ ((n:ℤ)-2) := by
      intro hc
      have hqP2 : (q:ℤ) ∣ pp n 2 :=
        dvd_trans (dvd_pow_self (q:ℤ) (by omega : a ≠ 0)) hqa_P2
      have hform : pp n 2 = ((n:ℤ)-2)*((n:ℤ)+4) + 4 := by rw [pp_two n hn]; ring
      rw [hform] at hqP2
      have hq4 : (q:ℤ) ∣ 4 := by
        have h1 : (q:ℤ) ∣ ((n:ℤ)-2)*((n:ℤ)+4) := Dvd.dvd.mul_right hc _
        have := dvd_sub hqP2 h1
        simpa using this
      have hq4n : q ∣ 4 := by exact_mod_cast hq4
      have hq22 : q ∣ 2^2 := by norm_num; norm_num at hq4n; exact hq4n
      have hq2 : q ∣ 2 := hq.dvd_of_dvd_pow hq22
      have : q ≤ 2 := Nat.le_of_dvd (by norm_num) hq2
      omega
    -- coprimality and conclusion
    have hcop : IsCoprime ((q:ℤ)^a) ((n:ℤ)-2) :=
      (((Nat.prime_iff_prime_int.mp hq).coprime_iff_not_dvd).mpr hqnd).pow_left
    have hprod : (q:ℤ)^a ∣ ((n:ℤ)-2) * pp n 3 := by
      rw [ident2 n hn]
      exact dvd_add (Dvd.dvd.mul_right hqa_P2 _) hqa_cprod
    exact hcop.dvd_of_dvd_mul_left hprod

/-! ### Assembling `A363347 n = p`. -/

lemma P2_val (n : ℕ) (hn : 4 ≤ n) : (pp n 2).natAbs + 5 = (n+1)^2 := by
  have hpos : 0 < pp n 2 := pp_two_pos n hn
  have hc : ((pp n 2).natAbs : ℤ) = pp n 2 := Int.natAbs_of_nonneg hpos.le
  have : ((pp n 2).natAbs : ℤ) + 5 = ((n+1)^2 : ℤ) := by
    rw [hc, pp_two n hn]; push_cast; ring
  exact_mod_cast this

/-- The smooth part `s = P2/p` divides `P3`. -/
lemma s_dvd_P3 (n p : ℕ) (hn : 4 ≤ n) (hnodd : Odd n) (hp : p.Prime)
    (hpn : n < p) (hpP2 : p ∣ (pp n 2).natAbs) :
    ((pp n 2).natAbs / p) ∣ (pp n 3).natAbs := by
  set P2 := (pp n 2).natAbs with hP2def
  set P3 := (pp n 3).natAbs with hP3def
  set s := P2 / p with hsdef
  have hP2pos : 0 < pp n 2 := pp_two_pos n hn
  have hP3pos : 0 < pp n 3 := pp_pos n hn 3 (by norm_num) (by omega)
  have hP2pos' : 0 < P2 := by rw [hP2def]; exact Int.natAbs_pos.mpr hP2pos.ne'
  have hP3pos' : 0 < P3 := by rw [hP3def]; exact Int.natAbs_pos.mpr hP3pos.ne'
  have hPS : p * s = P2 := Nat.mul_div_cancel' hpP2
  have hP2nat : P2 + 5 = (n+1)^2 := P2_val n hn
  have hP2lt : P2 < (n+1)^2 := by omega
  have hplo : n+1 ≤ p := by omega
  have hpp_gt : P2 < p * p := by nlinarith [hplo, hP2lt]
  have hsP2 : s ∣ P2 := ⟨p, by rw [mul_comm]; exact hPS.symm⟩
  rw [Nat.dvd_iff_prime_pow_dvd_dvd P3 s]
  intro q k hqp hqk
  have hqNat : q.Prime := hqp
  have hqkP2 : q^k ∣ P2 := hqk.trans hsP2
  rcases eq_or_ne q p with hqeqp | hqnep
  · -- q = p : p^k | s, but p ∤ s
    subst hqeqp
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · rw [hk0]; simp
    · exfalso
      have hp_s : q ∣ s := dvd_trans (dvd_pow_self q (by omega : k ≠ 0)) hqk
      obtain ⟨s', hs'⟩ := hp_s
      have : q*q ∣ P2 := ⟨s', by rw [← hPS, hs']; ring⟩
      have := Nat.le_of_dvd hP2pos' this
      omega
  · -- q ≠ p
    rcases eq_or_ne q 2 with hq2 | hq2
    · -- q = 2 : P2 is odd (n odd)
      subst hq2
      rcases Nat.eq_zero_or_pos k with hk0 | hk1
      · rw [hk0]; simp
      · exfalso
        have h2P2 : 2 ∣ P2 := dvd_trans (dvd_pow_self 2 (by omega : k ≠ 0)) hqkP2
        -- P2 odd since n odd
        obtain ⟨m, hm⟩ := hnodd  -- n = 2m+1
        have : (n+1)^2 = (2*(m+1))^2 := by rw [hm]; ring
        -- (n+1)^2 even^2 divisible by 4, so P2 = (n+1)^2 - 5 is odd
        have h4 : 4 ∣ (n+1)^2 := by rw [this]; exact ⟨(m+1)^2, by ring⟩
        omega
    · -- q odd prime, q ≠ p
      rcases le_or_gt q n with hqle | hqgt
      · -- q ≤ n : use smooth cancellation
        have ha_le : k ≤ P2.factorization q :=
          (hqNat.pow_dvd_iff_le_factorization hP2pos'.ne').mp hqkP2
        have hsmooth := smooth_cancel n q hn hqNat hqle hq2
        rw [← hP2def] at hsmooth
        have hq_a_P3 : q^(P2.factorization q) ∣ P3 := by
          have hd := Int.natAbs_dvd_natAbs.mpr hsmooth
          rw [hP3def]
          simpa [Int.natAbs_pow, Int.natAbs_natCast] using hd
        exact dvd_trans (pow_dvd_pow q ha_le) hq_a_P3
      · -- q > n : only p among primes > n divides P2
        rcases Nat.eq_zero_or_pos k with hk0 | hk1
        · rw [hk0]; simp
        · exfalso
          have hqP2 : q ∣ P2 := dvd_trans (dvd_pow_self q (by omega : k ≠ 0)) hqkP2
          have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hqNat).mpr (Ne.symm hqnep)
          have hpq : p * q ∣ P2 := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpP2 hqP2
          have hle := Nat.le_of_dvd hP2pos' hpq
          have : (n+1)*(n+1) ≤ p * q := Nat.mul_le_mul hplo (by omega)
          nlinarith [hle, this, hP2lt]

/-- Main assembly: for odd `n ≥ 4`, prime `p > n` dividing `P2`, we get `A363347 n = p`. -/
lemma A363347_eq (n p : ℕ) (hn : 4 ≤ n) (hnodd : Odd n) (hp : p.Prime)
    (hpn : n < p) (hpP2Z : (p:ℤ) ∣ pp n 2) : A363347 n = p := by
  have hP2pos : 0 < pp n 2 := pp_two_pos n hn
  have hP3pos : 0 < pp n 3 := pp_pos n hn 3 (by norm_num) (by omega)
  have hP2cast : ((pp n 2).natAbs : ℤ) = pp n 2 := Int.natAbs_of_nonneg hP2pos.le
  have hP3cast : ((pp n 3).natAbs : ℤ) = pp n 3 := Int.natAbs_of_nonneg hP3pos.le
  set P2 := (pp n 2).natAbs with hP2def
  set P3 := (pp n 3).natAbs with hP3def
  have hpP2 : p ∣ P2 := by
    rw [hP2def]
    have := Int.natAbs_dvd_natAbs.mpr hpP2Z
    simpa using this
  set s := P2 / p with hsdef
  have hP2ps : P2 = p * s := (Nat.mul_div_cancel' hpP2).symm
  have hs_pos : 0 < s := by
    have hP2pos' : 0 < P2 := by rw [hP2def]; exact Int.natAbs_pos.mpr hP2pos.ne'
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h, mul_zero] at hP2ps; omega
    · exact h
  -- s | P3
  have hsP3 : s ∣ P3 := s_dvd_P3 n p hn hnodd hp hpn hpP2
  set D := P3 / s with hDdef
  have hP3SD : P3 = s * D := (Nat.mul_div_cancel' hsP3).symm
  have hD_pos : 0 < D := by
    have hP3pos' : 0 < P3 := by rw [hP3def]; exact Int.natAbs_pos.mpr hP3pos.ne'
    rcases Nat.eq_zero_or_pos D with h | h
    · rw [h, mul_zero] at hP3SD; omega
    · exact h
  -- p ∤ D
  have hclaimB : ¬ (p:ℤ) ∣ pp n 3 := claimB n p hn hp hpn hpP2Z
  have hpnD : ¬ p ∣ D := by
    intro hpd
    have hpP3 : p ∣ P3 := by rw [hP3SD]; exact hpd.mul_left s
    have : (p:ℤ) ∣ pp n 3 := by
      have h1 := Int.natCast_dvd_natCast.mpr hpP3
      rwa [hP3cast] at h1
    exact hclaimB this
  -- coprimality
  have hcop : Nat.Coprime p D := (hp.coprime_iff_not_dvd).mpr hpnD
  -- pp n 2 and pp n 3 as products
  have hppn2 : pp n 2 = (s:ℤ) * (p:ℤ) := by
    rw [← hP2cast, hP2ps]; push_cast; ring
  have hppn3 : pp n 3 = (s:ℤ) * (D:ℤ) := by
    rw [← hP3cast, hP3SD]; push_cast; ring
  -- the continued fraction ratio
  have hR : continued_fraction_denominator n 2 = (p:ℚ) / (D:ℚ) := by
    have h1 := cfd_eq_ratio n (by omega) (n-3) 2 (by omega) (by norm_num)
    rw [h1]
    have e2 : (pp n 2 : ℚ) = (s:ℚ) * (p:ℚ) := by rw [hppn2]; push_cast; ring
    have e3 : (pp n 3 : ℚ) = (s:ℚ) * (D:ℚ) := by rw [hppn3]; push_cast; ring
    rw [e2, e3, mul_div_mul_left _ _ (by exact_mod_cast hs_pos.ne' : (s:ℚ) ≠ 0)]
  -- compute A363347
  have hA : A363347 n = (continued_fraction_denominator n 2).num.natAbs := by
    unfold A363347
    rw [if_neg (by omega : ¬ n ≤ 2)]
  rw [hA, hR]
  have hqeq : ((p:ℚ)/(D:ℚ)) = (((p:ℤ):ℚ)/((D:ℤ):ℚ)) := by push_cast; ring
  rw [hqeq]
  have hDZpos : (0:ℤ) < (D:ℤ) := by exact_mod_cast hD_pos
  have hcop' : Nat.Coprime ((p:ℤ)).natAbs ((D:ℤ)).natAbs := by simpa using hcop
  rw [Rat.num_div_eq_of_coprime hDZpos hcop']
  simp

/-! ### Quadratic residue: 5 is a square mod p. -/

lemma five_is_square (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : p % 5 = 1 ∨ p % 5 = 4) : IsSquare (5 : ZMod p) := by
  haveI : Fact (5:ℕ).Prime := ⟨by norm_num⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hqr := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by norm_num) hp2
  have hsq5 : IsSquare ((p:ℕ) : ZMod 5) := by
    rw [← ZMod.natCast_mod p 5]
    rcases hmod with h | h <;> rw [h] <;> decide
  have h5 := hqr.mp hsq5
  simpa using h5

/-- Existence of an even root of `x^2 = 5` in `[0,p)`. -/
lemma even_root (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) (hp2 : p ≠ 2)
    (h : IsSquare (5 : ZMod p)) :
    ∃ e : ℕ, e < p ∧ 2 ∣ e ∧ ((e : ZMod p))^2 = 5 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := h
  have hy2 : y^2 = 5 := by rw [sq]; exact hy.symm
  have hyne : y ≠ 0 := by
    intro h0
    rw [h0] at hy2
    have : (5 : ZMod p) = 0 := by rw [← hy2]; ring
    have h5dvd : (p:ℕ) ∣ 5 := by
      have h0 : ((5:ℕ) : ZMod p) = 0 := by exact_mod_cast this
      exact (ZMod.natCast_eq_zero_iff 5 p).mp h0
    have : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5dvd
    exact hp5 this
  set v := y.val with hv
  have hv_pos : 0 < v := by
    rw [hv]; exact ZMod.val_pos.mpr hyne
  have hv_lt : v < p := ZMod.val_lt y
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  by_cases hpar : 2 ∣ v
  · refine ⟨v, hv_lt, hpar, ?_⟩
    rw [hv, ZMod.natCast_zmod_val]
    exact hy2
  · refine ⟨p - v, by omega, by omega, ?_⟩
    have hcast : ((p - v : ℕ) : ZMod p) = - y := by
      rw [Nat.cast_sub (le_of_lt hv_lt), ZMod.natCast_self, hv, ZMod.natCast_zmod_val]
      ring
    rw [hcast]
    rw [neg_pow, hy2]
    simp

/-! ### Main theorem. -/

theorem oeis_363347_conjecture_2 :
  ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p := by
  rintro p ⟨hp, hmod10⟩
  have hmod : p % 10 = 1 ∨ p % 10 = 9 := by
    rcases hmod10 with h | h
    · left; simpa [Nat.ModEq] using h
    · right; simpa [Nat.ModEq] using h
  have hp2 : p ≠ 2 := by omega
  have hp5 : p ≠ 5 := by omega
  have hp5mod : p % 5 = 1 ∨ p % 5 = 4 := by omega
  by_cases hp11 : p = 11
  · subst hp11
    refine ⟨3, ?_⟩
    have hcfd : continued_fraction_denominator 3 2 = 11/4 := by
      rw [continued_fraction_denominator]; norm_num
    have hA : A363347 3 = (continued_fraction_denominator 3 2).num.natAbs := by
      unfold A363347; rw [if_neg (by norm_num)]
    rw [hA, hcfd]; norm_num
  · have hsq := five_is_square p hp hp2 hp5mod
    obtain ⟨e, he_lt, he_even, he_sq⟩ := even_root p hp hp5 hp2 hsq
    have hpe : (p:ℤ) ∣ ((e:ℤ)^2 - 5) := by
      have hz : (((e:ℤ)^2 - 5 : ℤ) : ZMod p) = 0 := by
        push_cast; rw [he_sq]; ring
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz
    have he6 : 6 ≤ e := by
      by_contra hlt
      push_neg at hlt
      interval_cases e
      · norm_num at hpe
        have : p ∣ 5 := by exact_mod_cast hpe
        exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp this)
      · exact absurd he_even (by decide)
      · norm_num at hpe
        have : p ∣ 1 := by exact_mod_cast hpe
        exact absurd (Nat.dvd_one.mp this) hp.ne_one
      · exact absurd he_even (by decide)
      · norm_num at hpe
        have : p ∣ 11 := by exact_mod_cast hpe
        exact hp11 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp this)
      · exact absurd he_even (by decide)
    set n := e - 1 with hn
    have hn4 : 4 ≤ n := by omega
    have hnp : n < p := by omega
    have hnodd : Odd n := by
      obtain ⟨c, hc⟩ := he_even
      exact ⟨c - 1, by omega⟩
    have hpP2 : (p:ℤ) ∣ pp n 2 := by
      have hz : ((pp n 2 : ℤ) : ZMod p) = 0 := by
        rw [pp_two n hn4]
        push_cast
        have hen : (e : ZMod p) = (n:ZMod p) + 1 := by
          rw [hn, Nat.cast_sub (by omega : 1 ≤ e)]; push_cast; ring
        have hsq' : ((n:ZMod p)+1)^2 = 5 := by rw [← hen]; exact he_sq
        linear_combination hsq'
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (pp n 2) p).mp hz
    exact ⟨n, A363347_eq n p hn4 hnodd hp hnp hpP2⟩
