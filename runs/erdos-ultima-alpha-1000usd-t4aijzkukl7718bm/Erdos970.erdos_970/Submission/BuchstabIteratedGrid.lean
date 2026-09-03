import Submission.BuchstabGridMain

/-! Uniform transfer of finite grid refinements at every fixed depth.
The exact initial and lower-deficit tail allowances are retained. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg Erdos970.BuchstabGrid
set_option maxHeartbeats 0

lemma referenceLower_succ_ge (n k : ℕ) (D : ℝ) :
    referenceLower n k D ≤ referenceLower (n+1) k D :=
  lowerStep_succ_ge _ (fun i => (primeMarginal_pos i).le) _ _ n k D

lemma referenceLower_zero_le (n k : ℕ) (D : ℝ) : referenceLower 0 k D ≤ referenceLower n k D := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih.trans (referenceLower_succ_ge n k D)

noncomputable def primeDeficit (n : ℕ) (L : ℝ) (p : ℕ) : ℝ :=
  (1/(p : ℝ))*(1/eulerMass p.primesBelow-referenceLower n (primeIndex p) (exp L/(p : ℝ)))

lemma primeDeficit_nonneg (n : ℕ) (L : ℝ) (p : ℕ) (hp : p.Prime) : 0 ≤ primeDeficit n L p := by
  have hh := (reference_density_bounds n (primeIndex p) (exp L/(p : ℝ))).1
  rw [density_primeIndex p hp] at hh
  exact mul_nonneg (by positivity) (sub_nonneg.mpr hh)

lemma primeDeficit_le_zero (n : ℕ) (L : ℝ) (p : ℕ) : primeDeficit n L p ≤ primeLowerDeficit L p :=
  mul_le_mul_of_nonneg_left (sub_le_sub_left (referenceLower_zero_le n _ _) _) (by positivity)

lemma reference_deficit_sum_depth (n k : ℕ) (L : ℝ) :
    (∑ i : Fin k, primeMarginal i.val*(prefixDensity primeMarginal i.val-
      referenceLower n i.val (exp L*primeMarginal i.val))) =
      ∑ p ∈ (nthPrime k).primesBelow, primeDeficit n L p := by
  rw [← nthPrime_prefix_sum (primeDeficit n L) k]
  apply sum_congr rfl
  intro i hi
  simp only [primeDeficit,primeIndex_nthPrime,primeMarginal,nthPrime_prefix_density,mul_one_div]

lemma referenceUpper_succ_le_of_normalized_deficit (n k : ℕ) (L u : ℝ)
    (h : eulerMass (nthPrime k).primesBelow*(∑ p ∈ (nthPrime k).primesBelow,
      primeDeficit n L p) ≤ u-1) :
    referenceUpper (n+1) k (exp L) ≤ prefixDensity primeMarginal k*u := by
  apply upperMain_le_of_deficit _ _ _ n
  change (∑ i : Fin k, primeMarginal i.val*(prefixDensity primeMarginal i.val-
    referenceLower n i.val (exp L*primeMarginal i.val))) ≤ _
  rw [reference_deficit_sum_depth,nthPrime_prefix_density]
  have hE := eulerMass_pos (nthPrime k).primesBelow (fun p hp => (Nat.mem_primesBelow.mp hp).2)
  have hh : (∑ p ∈ (nthPrime k).primesBelow, primeDeficit n L p) ≤
      (u-1)/eulerMass (nthPrime k).primesBelow :=
    (le_div_iff₀ hE).mpr (by simpa only [mul_comm] using h)
  convert hh using 1
  ring

lemma exists_deficit_tail_depth (n : ℕ) : ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k →
    ∀ s : ℝ, 1 ≤ s → eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ smallPrimePart k (s*log (nthPrime k : ℝ)), primeDeficit n (s*log (nthPrime k : ℝ)) p) ≤
        lowerGridTail/s := by
  obtain ⟨N,hN⟩ := exists_reference_lower_deficit_tail
  refine ⟨N,fun k hk s hs => ?_⟩
  apply le_trans _ (hN k hk s hs)
  apply mul_le_mul_of_nonneg_left _ (eulerMass_pos _ (fun p hp => (Nat.mem_primesBelow.mp hp).2)).le
  exact sum_le_sum (fun p hp => primeDeficit_le_zero n _ p)

lemma primeDeficit_bin_bound (n : ℕ) (L B : ℝ) (j p : ℕ)
    (hp : p ∈ gridPrimeBin L j)
    (hnode : (1/eulerMass p.primesBelow)*B ≤
      referenceLower n (primeIndex p) (exp (((j : ℝ)/50)*log (p : ℝ)))) :
    primeDeficit n L p ≤ (1-B)*((1/(p : ℝ))*(1/eulerMass p.primesBelow)) := by
  have hh := hnode.trans ((referenceLower_monotone n (primeIndex p)) (gridPrimeBin_child_level L j p hp))
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_left hh (1/eulerMass p.primesBelow))
    (show (0 : ℝ) ≤ 1/(p : ℝ) by positivity)
  convert hm using 1 <;> ring

lemma eventually_lower_grid_bins_depth (n a b N : ℕ) (hb : b ≤ 600) (B : ℕ → ℝ)
    (hgrid : ∀ k : ℕ, N ≤ nthPrime k → ∀ j ∈ Ico a b,
      prefixDensity primeMarginal k*B j ≤ referenceLower n k (exp (((j : ℝ)/50)*log (nthPrime k : ℝ))))
    (s : ℝ) (hs : 0 < s) :
    ∀ᶠ L : ℝ in atTop, ∀ j ∈ Ico a b, ∀ p ∈ gridPrimeBin (s*L) j,
      primeDeficit n (s*L) p ≤ (1-B j)*((1/(p : ℝ))*(1/eulerMass p.primesBelow)) := by
  filter_upwards [eventually_grid_primes_large s hs N] with L hL j hj p hp
  have hpp := (mem_filter.mp hp).2
  apply primeDeficit_bin_bound n (s*L) (B j) j p hp
  have hh := hgrid (primeIndex p) (by
    rw [nthPrime_primeIndex p hpp]
    exact hL j ((mem_Ico.mp hj).2.trans_le hb) p hp) j hj
  simpa only [nthPrime_primeIndex p hpp,density_primeIndex p hpp] using hh

lemma exists_grid_lower_deficit_bound_depth (n a N : ℕ) (ha : 50 ≤ a) (ha' : a ≤ 650) (B : ℕ → ℝ)
    (hgrid : ∀ k : ℕ, N ≤ nthPrime k → ∀ j ∈ Ico (a-50) 600,
      prefixDensity primeMarginal k*B j ≤ referenceLower n k (exp (((j : ℝ)/50)*log (nthPrime k : ℝ))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ k : ℕ, M ≤ nthPrime k → eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ (nthPrime k).primesBelow, primeDeficit n (((a : ℝ)/50)*log (nthPrime k : ℝ)) p) <
      (lowerGridTail+(∑ j ∈ Ico (a-50) 600, (1-B j)/50))/((a : ℝ)/50)+ε := by
  have haR : (50 : ℝ) ≤ a := by exact_mod_cast ha
  have hs : (1 : ℝ) ≤ (a : ℝ)/50 := by linarith
  obtain ⟨N₀,hN₀⟩ := exists_deficit_tail_depth n
  exact exists_grid_total_bound a ha ha' (primeDeficit n) (primeDeficit_nonneg n)
    lowerGridTail (fun j => 1-B j) ⟨N₀,fun k hk => hN₀ k hk _ hs⟩
    (eventually_lower_grid_bins_depth n (a-50) 600 N le_rfl B hgrid _ (by linarith)) ε hε

/-- Uniform validity of all upper grid nodes used in the finite partition. -/
def UpperGridValid (n : ℕ) (U : ℕ → ℝ) : Prop := ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k →
    ∀ j : ℕ, 50 ≤ j → j < 601 →
      referenceUpper n k (exp (((j : ℝ)/50)*log (nthPrime k : ℝ))) ≤ prefixDensity primeMarginal k*U j

def LowerGridValid (n : ℕ) (L : ℕ → ℝ) : Prop := ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k →
    ∀ j : ℕ, j < 601 → prefixDensity primeMarginal k*L j ≤
      referenceLower n k (exp (((j : ℝ)/50)*log (nthPrime k : ℝ)))

/-- A finite list of numerical budgets gives actual lower nodes at any depth. -/
theorem lower_grid_from_upper (n : ℕ) (U L : ℕ → ℝ) (hU : UpperGridValid n U)
    (hbudget : ∀ a : ℕ, a < 601 → L a = 0 ∨ (100 ≤ a ∧
      initialGridTail+(∑ j ∈ Ico (a-50) 600, (U j-1)/50) ≤
        ((a : ℝ)/50)*(1-L a-1/100000))) : LowerGridValid n L := by
  obtain ⟨N,hN⟩ := hU
  have hnode (a : Fin 601) : ∃ M : ℕ, ∀ k : ℕ, M ≤ nthPrime k →
      prefixDensity primeMarginal k*L a.val ≤ referenceLower n k (exp (((a.val : ℝ)/50)*log (nthPrime k : ℝ))) := by
    rcases hbudget a.val a.isLt with hz | ⟨ha,hbudget⟩
    · exact ⟨0,fun k hk => by simpa only [hz,mul_zero] using referenceLower_nonneg n k _⟩
    have haR : (100 : ℝ) ≤ a.val := by exact_mod_cast ha
    have hs : (0 : ℝ) < (a.val : ℝ)/50 := by linarith
    obtain ⟨M,hM⟩ := exists_grid_upper_excess_bound n a.val N (by omega) (by omega) U (by
      intro k hk j hj
      exact hN k hk j (by have := (mem_Ico.mp hj).1; omega) (by have := (mem_Ico.mp hj).2; omega))
      (1/200000) (by norm_num)
    refine ⟨M,fun k hk => ?_⟩
    apply referenceLower_ge_of_normalized_excess n k _ _ (primeKeep_exp k _ (by linarith))
    have hh := hM k hk
    have hd : (initialGridTail+(∑ j ∈ Ico (a.val-50) 600, (U j-1)/50))/((a.val : ℝ)/50) ≤
        1-L a.val-1/100000 := (div_le_iff₀ hs).mpr (by nlinarith only [hbudget])
    linarith only [hh,hd]
  classical
  choose M hM using hnode
  refine ⟨univ.sup M,fun k hk j hj => hM ⟨j,hj⟩ k ?_⟩
  exact (le_sup (f := M) (mem_univ ⟨j,hj⟩)).trans hk

/-- The new upper main may use either the previous actual upper bound or the
new lower-child deficit budget. Every finite-sector error has slack. -/
theorem upper_grid_from_lower (n : ℕ) (U L V : ℕ → ℝ) (hU : UpperGridValid n U)
    (hL : LowerGridValid n L)
    (hbudget : ∀ a : ℕ, 50 ≤ a → a < 601 → V a = U a ∨
      lowerGridTail+(∑ j ∈ Ico (a-50) 600, (1-L j)/50) ≤
        ((a : ℝ)/50)*(V a-1-1/100000)) : UpperGridValid (n+1) V := by
  obtain ⟨N,hN⟩ := hU
  obtain ⟨N',hN'⟩ := hL
  have hnode (a : Fin 601) : ∃ M : ℕ, ∀ k : ℕ, M ≤ nthPrime k → 50 ≤ a.val →
      referenceUpper (n+1) k (exp (((a.val : ℝ)/50)*log (nthPrime k : ℝ))) ≤ prefixDensity primeMarginal k*V a.val := by
    by_cases ha : 50 ≤ a.val
    · rcases hbudget a.val ha a.isLt with hz | hbudget
      · refine ⟨N,fun k hk _ => ?_⟩
        rw [hz]
        exact (referenceUpper_succ_le n k _).trans (hN k hk a.val ha a.isLt)
      · have haR : (50 : ℝ) ≤ a.val := by exact_mod_cast ha
        have hs : (0 : ℝ) < (a.val : ℝ)/50 := by linarith
        obtain ⟨M,hM⟩ := exists_grid_lower_deficit_bound_depth n a.val N' (by omega) (by omega) L (by
          intro k hk j hj
          exact hN' k hk j (by have := (mem_Ico.mp hj).2; omega)) (1/200000) (by norm_num)
        refine ⟨M,fun k hk _ => ?_⟩
        apply referenceUpper_succ_le_of_normalized_deficit n
        have hh := hM k hk
        have hd : (lowerGridTail+(∑ j ∈ Ico (a.val-50) 600, (1-L j)/50))/((a.val : ℝ)/50) ≤
            V a.val-1-1/100000 := (div_le_iff₀ hs).mpr (by nlinarith only [hbudget])
        linarith only [hh,hd]
    · exact ⟨0,fun k hk hh => (ha hh).elim⟩
  classical
  choose M hM using hnode
  refine ⟨univ.sup M,fun k hk j hj0 hj => hM ⟨j,hj⟩ k ?_ hj0⟩
  exact (le_sup (f := M) (mem_univ ⟨j,hj⟩)).trans hk

#print axioms lower_grid_from_upper
#print axioms upper_grid_from_lower
end Erdos970.RecursiveSieve.Buchstab
