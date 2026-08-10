import Submission.reduce

open Nat Finset BigOperators Int

/-- Step 1: `a_gen (-1) N = P ((N:ℤ)-2) (N-1)` for `N ≥ 1`. -/
lemma step1 (N : ℕ) (hN : 1 ≤ N) :
    a_gen (-1) N = P ((N:ℤ) - 2) (N - 1) := by
  have hN0 : N ≠ 0 := by omega
  rw [a_gen, if_neg hN0]
  rw [Finset.sum_range_succ]
  set r : ℤ := (-1) * (N:ℤ) with hr
  -- last term vanishes
  have hzero : generalized_catalan_coefficient r N = 0 := by
    unfold generalized_catalan_coefficient
    rw [if_neg hN0]
    have hden : r + (N:ℤ) = 0 := by rw [hr]; ring
    simp only []
    rw [hden, Int.ediv_zero]
  rw [hzero, add_zero]
  -- telescope on range N = range ((N-1)+1)
  have htel := telescope r (N - 1) (by
    intro k hk1 hk2
    have h1 : (k:ℤ) ≤ ((N - 1 : ℕ):ℤ) := by exact_mod_cast hk2
    have hc : ((N - 1 : ℕ):ℤ) = (N:ℤ) - 1 := by rw [Nat.cast_sub hN]; push_cast; ring
    rw [hc] at h1
    rw [hr]
    intro hcon
    have : (k:ℤ) = (N:ℤ) := by linarith [hcon]
    linarith [h1])
  have hrng : Finset.range ((N - 1) + 1) = Finset.range N := by rw [Nat.sub_add_cancel hN]
  rw [hrng] at htel
  rw [htel]
  congr 1
  rw [hr]
  have hc : ((N - 1 : ℕ):ℤ) = (N:ℤ) - 1 := by rw [Nat.cast_sub hN]; push_cast; ring
  rw [hc]; ring

/-- Step 2: `P ((N:ℤ)-2) (N-1) = P (N:ℤ) N + 1` for `N ≥ 1`. -/
lemma step2 (N : ℕ) (hN : 1 ≤ N) :
    P ((N:ℤ) - 2) (N - 1) = P (N:ℤ) N + 1 := by
  have hSI := SI ((N:ℤ) - 2) (N - 1)
  have e1 : (N:ℤ) - 2 + 2 = (N:ℤ) := by ring
  have e2 : (N - 1) + 1 = N := by omega
  rw [e1, e2] at hSI
  have e3 : (N:ℤ) - 2 + 1 = (N:ℤ) - 1 := by ring
  rw [e3] at hSI
  have hc1 : Ring.choose ((N:ℤ) - 1) N = 0 := by
    have hcast : (N:ℤ) - 1 = ((N - 1 : ℕ):ℤ) := by rw [Nat.cast_sub hN]; push_cast; ring
    rw [hcast, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have hc2 : Ring.choose ((N:ℤ) - 1) (N - 1) = 1 := by
    have hcast : (N:ℤ) - 1 = ((N - 1 : ℕ):ℤ) := by rw [Nat.cast_sub hN]; push_cast; ring
    rw [hcast, Ring.choose_natCast, Nat.choose_self]
    simp
  rw [hc1, hc2] at hSI
  linarith [hSI]

/-- Step 3: `P (N:ℤ) N = 3 * Sfun N 0 - 2^N - 1`. -/
lemma step3 (N : ℕ) :
    P (N:ℤ) N = 3 * Sfun N 0 - 2 ^ N - 1 := by
  rw [P_def]
  have hconv : ∀ j ∈ Finset.range (N + 1),
      gcoef j * Ring.choose (N:ℤ) (N - j) = gcoef j * (Nat.choose N j : ℤ) := by
    intro j hj
    rw [mem_range] at hj
    rw [Ring.choose_natCast, Nat.choose_symm (show j ≤ N by omega)]
  rw [Finset.sum_congr rfl hconv]
  have hpt : ∀ j ∈ Finset.range (N + 1),
      gcoef j * (Nat.choose N j : ℤ)
        = (3 * (if ((j:ℕ):ZMod 3) = 0 then (Nat.choose N j : ℤ) else 0) - (Nat.choose N j : ℤ))
          - (if j = 0 then (1:ℤ) else 0) := by
    intro j _
    by_cases hj0 : j = 0
    · subst hj0
      rw [if_pos rfl]
      norm_num [gcoef]
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      rw [if_neg hj0, sub_zero]
      have hg : gcoef j = 3 * (if 3 ∣ j then (1:ℤ) else 0) - 1 := by
        rw [← gc_eq_gcoef]; exact gc_pos j hj1
      rw [hg]
      have hiff : (((j:ℕ):ZMod 3) = 0) ↔ (3 ∣ j) := ZMod.natCast_eq_zero_iff j 3
      by_cases hd : 3 ∣ j
      · rw [if_pos hd, if_pos (hiff.mpr hd)]; ring
      · rw [if_neg hd, if_neg (fun h => hd (hiff.mp h))]; ring
  rw [Finset.sum_congr rfl hpt]
  have hS : (∑ j ∈ range (N + 1),
      if ((j:ℕ):ZMod 3) = 0 then (Nat.choose N j : ℤ) else 0) = Sfun N 0 := by
    unfold Sfun; rfl
  have hC : (∑ j ∈ range (N + 1), (Nat.choose N j : ℤ)) = 2 ^ N := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
  have hE : (∑ j ∈ range (N + 1), if j = 0 then (1:ℤ) else 0) = 1 := by
    rw [Finset.sum_ite_eq' (range (N + 1)) 0 (fun _ => (1:ℤ))]
    rw [if_pos (by simp)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hS, hC, hE]

/-- Step 4: closed form of `a_gen (-1) N` for `N ≥ 1`. -/
lemma aneg1 (N : ℕ) (hN : 1 ≤ N) :
    a_gen (-1) N = 3 * Sfun N 0 - 2 ^ N := by
  rw [step1 N hN, step2 N hN, step3 N]; ring

/-- Period-6 for the closed form (all `N`). -/
lemma gper (N : ℕ) :
    3 * Sfun (N + 6) 0 - 2 ^ (N + 6) = 3 * Sfun N 0 - 2 ^ N := by
  have h1 := Sshift3 N 0
  have h2 := Sshift3 (N + 3) 0
  have e : N + 3 + 3 = N + 6 := by ring
  rw [e] at h2
  have p6 : (2:ℤ) ^ (N + 6) = 64 * 2 ^ N := by rw [pow_add]; ring
  have p3 : (2:ℤ) ^ (N + 3) = 8 * 2 ^ N := by rw [pow_add]; ring
  rw [h2, h1, p6, p3]; ring

/-- Explicit residue function. -/
def Gr (i : ℕ) : ℤ :=
  if i = 0 then 2 else if i = 1 then 1 else if i = 2 then -1
  else if i = 3 then -2 else if i = 4 then -1 else if i = 5 then 1 else 0

lemma gval : ∀ N : ℕ, 3 * Sfun N 0 - 2 ^ N = Gr (N % 6) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N 6 with h | h
    · interval_cases N <;> (unfold Gr Sfun; decide)
    · have hlt : N - 6 < N := by omega
      have hmod : N % 6 = (N - 6) % 6 := by omega
      have hp := gper (N - 6)
      rw [show N - 6 + 6 = N from by omega] at hp
      rw [hmod, hp]
      exact ih (N - 6) hlt

/-- `a_gen (-1) N` depends only on `N % 6` for `N ≥ 1`. -/
lemma aneg1_mod (N : ℕ) (hN : 1 ≤ N) : a_gen (-1) N = Gr (N % 6) := by
  rw [aneg1 N hN, gval N]

theorem mneg1_conj (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    a_gen (-1) (n * p ^ k) ≡ a_gen (-1) (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  -- positivity of arguments
  have hppos : 0 < p := by omega
  have hx1 : 1 ≤ n * p ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hy1 : 1 ≤ n * p ^ (k - 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- x = p * y
  have hxy : n * p ^ k = p * (n * p ^ (k - 1)) := by
    have : p ^ k = p * p ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 from by omega]
      rw [pow_succ]; ring
    rw [this]; ring
  -- residue of p mod 6 is 1 or 5
  have hp2 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · omega
    · exact hodd
  have hp3 : ¬ (3 ∣ p) := not_three_dvd_prime p hp hp5
  have hp3' : p % 3 ≠ 0 := by
    intro h; exact hp3 (Nat.dvd_of_mod_eq_zero h)
  have hp6 : p % 6 = 1 ∨ p % 6 = 5 := by omega
  set y := n * p ^ (k - 1) with hydef
  -- reduce to equality of Gr values
  have hxmod : (n * p ^ k) % 6 = (p % 6 * (y % 6)) % 6 := by
    rw [hxy, Nat.mul_mod]
  have key : a_gen (-1) (n * p ^ k) = a_gen (-1) y := by
    rw [aneg1_mod _ hx1, aneg1_mod _ hy1]
    rw [hxmod]
    rcases hp6 with h1 | h5
    · rw [h1, one_mul]; congr 1; omega
    · rw [h5]
      -- finite check over y % 6
      have hylt : y % 6 < 6 := Nat.mod_lt _ (by norm_num)
      set m := y % 6 with hm
      interval_cases m <;> decide
  rw [key]

#print axioms mneg1_conj

