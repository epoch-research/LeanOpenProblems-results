import Submission.Spec
import Mathlib

open Filter Asymptotics ZMod

theorem fals : ¬ (type_of% @oeis_363414_conjecture_type2_asymptotics) := by
  intro h
  have h_val := h 13 (by norm_num) (by dsimp [type_two_primes_conjectured]; exact ⟨by norm_num, rfl⟩)
  have h_val2 := IsEquivalent.isLittleO h_val
  rw [IsLittleO_def] at h_val2
  have h_val3 := h_val2 (by norm_num : (0:ℝ) < 1/2)
  rw [IsBigOWith_def, eventually_atTop] at h_val3
  rcases h_val3 with ⟨N, hN⟩
  
  -- We know for all p ≡ 1 mod 4, c = padicValInt p (a n)
  -- The conjecture says c ~ n / (p-1)
  -- But we know that c - n/(p-1) can be large.
  
  -- But wait, N can be arbitrarily large! M = max N 6 only shows it for M=6 if N <= 6.
  -- If N > 6, M = N, we don't know the value of a(M)!
  -- So we need to evaluate a(N) or prove a general bound for all n.
  -- Is there a general proof that c(n) is 0 for infinitely many n?
  sorry
