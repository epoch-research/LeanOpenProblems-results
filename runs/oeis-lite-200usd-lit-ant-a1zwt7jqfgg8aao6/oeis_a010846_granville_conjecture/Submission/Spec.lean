import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A010846: Number of numbers $\le n$ whose set of prime factors is a subset of the set of prime factors of $n$.
-/
def a (n : ℕ) : ℕ :=
  (Icc 1 n).filter (fun k => primeFactors k ⊆ primeFactors n) |>.card

/--
The conjecture as literally stated is **false**.

For a prime `p`, the only numbers `k ≤ p` whose prime factors are a subset of the
prime factors of `p` (namely `{p}`) are `k = 1` and `k = p`, so `a p = 2`.  On the
other hand `(Real.log p) ^ (1 - ε) → ∞` along the primes.  Taking `ε = 1/2`, every
sufficiently large prime `p` satisfies `(Real.log p) ^ (1/2) > 2 = a p`, so no
threshold `N` can work.  (The genuine Granville/Goldfeld statement is not the
"for all sufficiently large `n`" claim formalized here.)
-/
theorem oeis_a010846_granville_conjecture.disproof :
  ¬ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Real.log n) ^ (1 - ε) ≤ a n) := by
  intro h
  obtain ⟨N, hN⟩ := h (1/2) (by norm_num)
  -- Pick a prime `p ≥ max N 81`.
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (max N 81)
  have hpN : N ≤ p := le_trans (le_max_left _ _) hpge
  have hp81 : (81 : ℕ) ≤ p := le_trans (le_max_right _ _) hpge
  -- Step 1: `a p ≤ 2`.
  have hap : a p ≤ 2 := by
    have hsub : (Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p) ⊆ {1, p} := by
      intro k hk
      simp only [mem_filter, mem_Icc] at hk
      obtain ⟨⟨hk1, hkp⟩, hsubset⟩ := hk
      simp only [mem_insert, mem_singleton]
      by_contra hcon
      push_neg at hcon
      obtain ⟨hne1, hnep⟩ := hcon
      have hk0 : k ≠ 0 := by omega
      obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne1
      have hqmem : q ∈ primeFactors k := Nat.mem_primeFactors.mpr ⟨hq, hqdvd, hk0⟩
      have hqp : q ∈ primeFactors p := hsubset hqmem
      rw [hp.primeFactors] at hqp
      simp only [mem_singleton] at hqp
      subst hqp
      have hple : q ≤ k := Nat.le_of_dvd (by omega) hqdvd
      exact hnep (le_antisymm hkp hple)
    have h3 : a p ≤ ({1, p} : Finset ℕ).card := card_le_card hsub
    exact le_trans h3 (le_trans (card_insert_le _ _) (by simp))
  -- Step 2: `4 < Real.log p`.
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hexp : Real.exp 4 < 81 := by
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hpos : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
    have e4 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [show (4 : ℝ) = 1 + 1 + 1 + 1 by norm_num,
        Real.exp_add, Real.exp_add, Real.exp_add]; ring
    rw [e4]
    calc Real.exp 1 ^ 4 < 2.7182818286 ^ 4 := by gcongr
      _ < 81 := by norm_num
  have hlog : (4 : ℝ) < Real.log p := by
    rw [Real.lt_log_iff_exp_lt hppos]
    have : (81 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp81
    linarith
  -- Step 3: `2 < (Real.log p) ^ (1/2)`.
  have h2 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hgt : 2 < (Real.log (p : ℝ)) ^ (1 / 2 : ℝ) := by
    have hr := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 4) hlog (by norm_num : (0 : ℝ) < 1 / 2)
    rwa [h2] at hr
  -- Step 4: contradiction with `hN`.
  have hkey := hN p hpN
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hkey
  have hcast : (a p : ℝ) ≤ 2 := by exact_mod_cast hap
  linarith

