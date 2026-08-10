import FormalConjectures.Util.ProblemImports
open Nat Finset BigOperators Int

def generalized_choose_int (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else (Finset.prod (Finset.range k) fun i => r - (i : ℤ)) / (k.factorial : ℤ)

def generalized_catalan_coefficient (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else
    let num_choose := generalized_choose_int (r + 2 * (k : ℤ) - 1) k
    let denominator : ℤ := r + k
    (r * num_choose) / denominator

def a_gen (m : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 1
  else Finset.sum (range (n + 1)) fun k => generalized_catalan_coefficient (m * (n:ℤ)) k

def gcoef (j : ℕ) : ℤ := if j = 0 then 1 else if j % 3 = 0 then 2 else -1

open Polynomial in
/-- The descending Pochhammer product form. -/
lemma prodk (N : ℤ) (j : ℕ) :
    (∏ i ∈ range j, (N - (i:ℤ))) = (j.factorial : ℤ) * Ring.choose N j := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) N j
  rw [nsmul_eq_mul] at h
  rw [← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range] at h
  exact h

/-- (L0) `generalized_choose_int` agrees with `Ring.choose`. -/
lemma L0 (r : ℤ) (k : ℕ) : generalized_choose_int r k = Ring.choose r k := by
  rw [generalized_choose_int]
  split_ifs with hk
  · subst hk; rw [Ring.choose_zero_right]
  · rw [prodk, Int.mul_ediv_cancel_left]
    exact_mod_cast Nat.factorial_ne_zero k

/-- Absorption identity for `Ring.choose`. -/
lemma ABS (N : ℤ) (k : ℕ) :
    ((k + 1 : ℕ) : ℤ) * Ring.choose N (k + 1) = (N - (k:ℤ)) * Ring.choose N k := by
  have hk : ((k.factorial : ℤ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  apply mul_left_cancel₀ hk
  have e1 : (k.factorial : ℤ) * (((k + 1 : ℕ) : ℤ) * Ring.choose N (k + 1))
      = ∏ i ∈ range (k + 1), (N - (i:ℤ)) := by
    rw [prodk]
    have : ((k + 1).factorial : ℤ) = ((k + 1 : ℕ) : ℤ) * (k.factorial : ℤ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [this]; ring
  have e2 : (k.factorial : ℤ) * ((N - (k:ℤ)) * Ring.choose N k)
      = ∏ i ∈ range (k + 1), (N - (i:ℤ)) := by
    rw [Finset.prod_range_succ, prodk]; ring
  rw [e1, e2]

/-- (L1) Fuss–Catalan coefficient equals a difference of binomials. -/
lemma L1 (r : ℤ) (k : ℕ) (hk : 1 ≤ k) (hne : r + (k:ℤ) ≠ 0) :
    generalized_catalan_coefficient r k
      = Ring.choose (r + 2 * (k:ℤ) - 1) k - Ring.choose (r + 2 * (k:ℤ) - 1) (k - 1) := by
  have hk0 : k ≠ 0 := by omega
  rw [generalized_catalan_coefficient, if_neg hk0]
  simp only []
  rw [L0]
  set N : ℤ := r + 2 * (k:ℤ) - 1 with hNdef
  -- absorption specialized to (k-1)
  have habs := ABS N (k - 1)
  rw [Nat.sub_add_cancel hk] at habs
  have hcast : ((k - 1 : ℕ) : ℤ) = (k:ℤ) - 1 := by rw [Nat.cast_sub hk]; simp
  have hNk : N - ((k - 1 : ℕ) : ℤ) = r + (k:ℤ) := by
    rw [hcast, hNdef]; ring
  -- (r+k) * choose N (k-1) = k * choose N k
  have h2 : (r + (k:ℤ)) * Ring.choose N (k - 1) = (k:ℤ) * Ring.choose N k := by
    rw [← hNk, ← habs]
  have hmain : r * Ring.choose N k = (r + (k:ℤ)) * (Ring.choose N k - Ring.choose N (k - 1)) := by
    linear_combination h2
  rw [hmain, Int.mul_ediv_cancel_left _ hne]

def P (A : ℤ) (m : ℕ) : ℤ := ∑ j ∈ range (m + 1), gcoef j * Ring.choose A (m - j)

lemma P_def (A : ℤ) (m : ℕ) :
    P A m = ∑ j ∈ range (m + 1), gcoef j * Ring.choose A (m - j) := rfl

/-- Reflected form of `P` (choose index as summation variable). -/
lemma Preflect (A : ℤ) (m : ℕ) :
    P A m = ∑ i ∈ range (m + 1), gcoef (m - i) * Ring.choose A i := by
  rw [P_def, ← Finset.sum_range_reflect (fun j => gcoef j * Ring.choose A (m - j)) (m + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have h1 : m + 1 - 1 - i = m - i := by omega
  have h2 : m - (m - i) = i := by omega
  rw [h1, h2]

lemma gpos (t : ℕ) (ht : t ≠ 0) : gcoef t = if t % 3 = 0 then (2:ℤ) else -1 := by
  unfold gcoef; rw [if_neg ht]

lemma gsum3 (t : ℕ) (ht : 1 ≤ t) : gcoef t + gcoef (t + 1) + gcoef (t + 2) = 0 := by
  rw [gpos t (by omega), gpos (t + 1) (by omega), gpos (t + 2) (by omega)]
  rcases (by omega : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2) with h | h | h
  · rw [if_pos h, if_neg (show (t+1)%3 ≠ 0 by omega), if_neg (show (t+2)%3 ≠ 0 by omega)]; ring
  · rw [if_neg (show t%3 ≠ 0 by omega), if_neg (show (t+1)%3 ≠ 0 by omega),
        if_pos (show (t+2)%3 = 0 by omega)]; ring
  · rw [if_neg (show t%3 ≠ 0 by omega), if_pos (show (t+1)%3 = 0 by omega),
        if_neg (show (t+2)%3 ≠ 0 by omega)]; ring

/-- (COLLAPSE) three consecutive `P` values collapse (period-3 of `gcoef`). -/
lemma collapse (A : ℤ) (n : ℕ) :
    P A n + P A (n + 1) + P A (n + 2) = Ring.choose A (n + 2) - Ring.choose A n := by
  rw [Preflect A n, Preflect A (n + 1), Preflect A (n + 2)]
  -- peel the top terms
  rw [Finset.sum_range_succ (fun i => gcoef (n + 2 - i) * Ring.choose A i) (n + 2),
      Finset.sum_range_succ (fun i => gcoef (n + 2 - i) * Ring.choose A i) (n + 1)]
  rw [Finset.sum_range_succ (fun i => gcoef (n + 1 - i) * Ring.choose A i) (n + 1)]
  -- combine the three range (n+1) sums
  have hcomb : (∑ i ∈ range (n + 1), gcoef (n + 2 - i) * Ring.choose A i)
      + (∑ i ∈ range (n + 1), gcoef (n + 1 - i) * Ring.choose A i)
      + (∑ i ∈ range (n + 1), gcoef (n - i) * Ring.choose A i)
      = ∑ i ∈ range (n + 1),
          (gcoef (n + 2 - i) + gcoef (n + 1 - i) + gcoef (n - i)) * Ring.choose A i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i hi; ring
  -- evaluate the combined sum via sum_eq_single at i = n
  have hsingle : (∑ i ∈ range (n + 1),
        (gcoef (n + 2 - i) + gcoef (n + 1 - i) + gcoef (n - i)) * Ring.choose A i)
      = - Ring.choose A n := by
    rw [Finset.sum_eq_single n]
    · have : gcoef (n + 2 - n) + gcoef (n + 1 - n) + gcoef (n - n) = -1 := by
        simp only [Nat.add_sub_cancel_left, Nat.sub_self]
        decide
      rw [this]; ring
    · intro b hb hbn
      simp only [Finset.mem_range] at hb
      have e2 : n + 2 - b = (n - b) + 2 := by omega
      have e1 : n + 1 - b = (n - b) + 1 := by omega
      rw [e2, e1]
      have h3 := gsum3 (n - b) (by omega)
      linear_combination Ring.choose A b * h3
    · intro h; exact absurd (Finset.self_mem_range_succ n) h
  -- gcoef values at the boundary
  have g0 : gcoef 0 = 1 := rfl
  have g1 : gcoef 1 = -1 := rfl
  have hS : (∑ i ∈ range (n + 1), gcoef (n + 2 - i) * Ring.choose A i)
        + (∑ i ∈ range (n + 1), gcoef (n + 1 - i) * Ring.choose A i)
        + (∑ i ∈ range (n + 1), gcoef (n - i) * Ring.choose A i)
      = - Ring.choose A n := hcomb.trans hsingle
  have en1 : n + 2 - (n + 1) = 1 := by omega
  have en2 : n + 2 - (n + 2) = 0 := by omega
  have en3 : n + 1 - (n + 1) = 0 := by omega
  rw [en1, en2, en3, g0, g1]
  linear_combination hS

/-- (PP) Pascal-type recursion for `P`. -/
lemma PP (B : ℤ) (m : ℕ) : P (B + 1) (m + 1) = P B (m + 1) + P B m := by
  rw [P_def, P_def, P_def]
  rw [Finset.sum_range_succ (fun j => gcoef j * Ring.choose (B + 1) (m + 1 - j)) (m + 1)]
  rw [Finset.sum_range_succ (fun j => gcoef j * Ring.choose B (m + 1 - j)) (m + 1)]
  have hbdry1 : m + 1 - (m + 1) = 0 := by omega
  rw [hbdry1, Ring.choose_zero_right, Ring.choose_zero_right]
  -- pointwise Pascal on the range (m+1) part
  have hkey : (∑ j ∈ range (m + 1), gcoef j * Ring.choose (B + 1) (m + 1 - j))
      = (∑ j ∈ range (m + 1), gcoef j * Ring.choose B (m + 1 - j))
        + (∑ j ∈ range (m + 1), gcoef j * Ring.choose B (m - j)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hmj : m + 1 - j = (m - j) + 1 := by omega
    rw [hmj, Ring.choose_succ_succ]
    ring
  rw [hkey]; ring

/-- (GG) key binomial telescoping identity. -/
lemma GG (A : ℤ) (n : ℕ) :
    P A (n + 1) + P (A + 1) n = Ring.choose (A + 1) (n + 1) - Ring.choose (A + 1) n := by
  cases n with
  | zero =>
    -- P A 1 + P (A+1) 0
    rw [P_def, P_def]
    have g0 : gcoef 0 = 1 := rfl
    have g1 : gcoef 1 = -1 := rfl
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.sub_self, Nat.sub_zero,
      zero_add, g0, g1, Ring.choose_zero_right, Ring.choose_one_right]
    ring
  | succ t =>
    have hpp := PP A t  -- P (A+1)(t+1) = P A (t+1) + P A t
    have hcol := collapse A t  -- P A t + P A (t+1) + P A (t+2) = choose A (t+2) - choose A t
    -- Pascal to relate choose (A+1) to choose A
    have hp1 : Ring.choose (A + 1) (t + 2) = Ring.choose A (t + 1) + Ring.choose A (t + 2) := by
      have := Ring.choose_succ_succ A (t + 1); simpa using this
    have hp2 : Ring.choose (A + 1) (t + 1) = Ring.choose A t + Ring.choose A (t + 1) :=
      Ring.choose_succ_succ A t
    -- assemble
    rw [hpp, hp1, hp2]
    -- goal: P A (t+2) + (P A (t+1) + P A t) = ...
    linear_combination hcol

/-- (SI) step identity for the telescoping. -/
lemma SI (A : ℤ) (n : ℕ) :
    P (A + 2) (n + 1) - P A n = Ring.choose (A + 1) (n + 1) - Ring.choose (A + 1) n := by
  have hAA : A + 1 + 1 = A + 2 := by ring
  have e1 : P (A + 2) (n + 1) = P (A + 1) (n + 1) + P (A + 1) n := by
    have h := PP (A + 1) n
    rw [hAA] at h
    exact h
  have e2 : P (A + 1) (n + 1) = P A (n + 1) + P A n := PP A n
  rw [e1, e2]
  linear_combination GG A n

/-- Nonvanishing of the denominator when `m ≠ -1`. -/
lemma denom_ne (m : ℤ) (hm : m ≠ -1) (n k : ℕ) (hn : 1 ≤ n) (hk1 : 1 ≤ k) (hk2 : k ≤ n) :
    m * (n:ℤ) + (k:ℤ) ≠ 0 := by
  intro h
  have hn' : (1:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
  have hk1' : (1:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk1
  have hk2' : (k:ℤ) ≤ (n:ℤ) := by exact_mod_cast hk2
  rcases (by omega : m ≤ -2 ∨ 0 ≤ m) with hm' | hm'
  · have hprod : 0 ≤ (-(m + 2)) * (n:ℤ) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hprod]
  · have hprod : 0 ≤ m * (n:ℤ) := mul_nonneg hm' (by linarith)
    nlinarith [hprod]

/-- (telescoping) the running sum of Fuss–Catalan coefficients equals `P`. -/
lemma telescope (r : ℤ) (n : ℕ)
    (hpos : ∀ k, 1 ≤ k → k ≤ n → r + (k:ℤ) ≠ 0) :
    ∑ k ∈ range (n + 1), generalized_catalan_coefficient r k = P (r + 2 * (n:ℤ)) n := by
  induction n with
  | zero =>
    rw [P_def, show (0:ℕ) + 1 = 1 from rfl, Finset.sum_range_one, Finset.sum_range_one,
      generalized_catalan_coefficient, if_pos rfl]
    norm_num [gcoef, Ring.choose_zero_right]
  | succ t ih =>
    rw [Finset.sum_range_succ]
    rw [ih (fun k hk1 hk2 => hpos k hk1 (by omega))]
    -- gcc r (t+1) via L1
    have hne : r + ((t + 1 : ℕ):ℤ) ≠ 0 := by
      have := hpos (t + 1) (by omega) (le_refl _)
      simpa using this
    have hL1 := L1 r (t + 1) (by omega) hne
    have hsub : (t + 1) - 1 = t := by omega
    rw [hsub] at hL1
    have hNc : r + 2 * ((t + 1 : ℕ):ℤ) - 1 = (r + 2 * (t:ℤ)) + 1 := by push_cast; ring
    rw [hNc] at hL1
    rw [hL1]
    -- now use SI with A = r + 2 t
    have hSI := SI (r + 2 * (t:ℤ)) t
    have hA2 : (r + 2 * (t:ℤ)) + 2 = r + 2 * ((t + 1 : ℕ):ℤ) := by push_cast; ring
    rw [hA2] at hSI
    -- goal: P (r+2 t) t + (choose ((r+2t)+1)(t+1) - choose ((r+2t)+1) t)
    --       = P (r + 2 (t+1)) (t+1)
    linear_combination -hSI

theorem closed_form (m : ℤ) (hm : m ≠ -1) (n : ℕ) :
    a_gen m n = ∑ j ∈ range (n + 1), gcoef j * Ring.choose ((m + 2) * (n:ℤ)) (n - j) := by
  have hlhs : a_gen m n = ∑ k ∈ range (n + 1), generalized_catalan_coefficient (m * (n:ℤ)) k := by
    rw [a_gen]
    split_ifs with hn
    · subst hn
      rw [Finset.sum_range_one]
      simp [generalized_catalan_coefficient]
    · rfl
  rw [hlhs]
  have htel := telescope (m * (n:ℤ)) n
    (fun k hk1 hk2 => denom_ne m hm n k (le_trans hk1 hk2) hk1 hk2)
  rw [htel]
  have hval : m * (n:ℤ) + 2 * (n:ℤ) = (m + 2) * (n:ℤ) := by ring
  rw [hval, P_def]

#print axioms closed_form
