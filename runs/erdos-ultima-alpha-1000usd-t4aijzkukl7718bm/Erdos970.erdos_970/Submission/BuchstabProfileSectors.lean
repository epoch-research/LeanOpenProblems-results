import Submission.BuchstabVariableTail

/-! Arbitrary finite logarithmic-sector partitions, without a fixed mesh or
terminal cutoff. Exact prime-density telescope limits are retained. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg
set_option maxHeartbeats 1000000

noncomputable def profileCut (L x : ℝ) : ℕ := ⌊exp (L/(x+1))⌋₊
noncomputable def profileBin (L a b : ℝ) : Finset ℕ :=
  (Ioc (profileCut L b) (profileCut L a)).filter Nat.Prime

lemma profileCut_antitone (L a b : ℝ) (hL : 0 ≤ L) (ha : 0 ≤ a) (hab : a ≤ b) :
    profileCut L b ≤ profileCut L a := by
  apply Nat.floor_le_floor
  apply exp_le_exp.mpr
  exact div_le_div_of_nonneg_left hL (by linarith : 0 < a+1) (by linarith)

lemma profileCut_scaled (s L x : ℝ) : profileCut (s*L) x = expFloor (s/(x+1)) L := by
  unfold profileCut expFloor
  congr 2
  ring

lemma profileCut_root (s : ℝ) (hs : 0 < s) (p : ℕ) (hp : 0 < p) :
    profileCut (s*log (p : ℝ)) (s-1) = p := by
  rw [profileCut, sub_add_cancel, mul_div_cancel_left₀ _ hs.ne',
    exp_log (by exact_mod_cast hp), Nat.floor_natCast]

lemma profileBin_child_level (L a b : ℝ) (ha : 0 ≤ a) (p : ℕ) (hp : p ∈ profileBin L a b) :
    exp (a*log (p : ℝ)) ≤ exp L/(p : ℝ) := by
  obtain ⟨hpI,hpp⟩ := mem_filter.mp hp
  have hphi := (mem_Ioc.mp hpI).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hpexp : (p : ℝ) ≤ exp (L/(a+1)) :=
    (show (p : ℝ) ≤ profileCut L a by exact_mod_cast hphi).trans (Nat.floor_le (exp_pos _).le)
  have hlog := log_le_log hp0 hpexp
  rw [log_exp] at hlog
  have hm := (le_div_iff₀ (by linarith : 0 < a+1)).mp hlog
  rw [← exp_log hp0, ← exp_sub, log_exp]
  apply exp_le_exp.mpr
  nlinarith only [hm]

lemma profileBins_sum (L : ℝ) (hL : 0 ≤ L) (v : ℕ → ℝ)
    (hv : Monotone v) (hv0 : 0 ≤ v 0) (N : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ range N, ∑ p ∈ profileBin L (v j) (v (j+1)), f p) =
      ∑ p ∈ (Ioc (profileCut L (v N)) (profileCut L (v 0))).filter Nat.Prime, f p := by
  have hc : Antitone (fun j => profileCut L (v j)) := by
    intro i j hij
    exact profileCut_antitone L _ _ hL (hv0.trans (hv (Nat.zero_le i))) (hv hij)
  unfold profileBin
  simp_rw [sum_prime_Ioc_eq_sub f _ _ (hc (Nat.le_succ _))]
  rw [sum_prime_Ioc_eq_sub f _ _ (hc (Nat.zero_le N))]
  exact sum_range_sub' (fun j => ∑ p ∈ range (profileCut L (v j)+1), if p.Prime then f p else 0) N

lemma prime_prefix_le_terminal_add_profile (s M : ℝ) (hs : 1 ≤ s) (k : ℕ)
    (v : ℕ → ℝ) (hv : Monotone v) (hv0 : v 0=s-1) (N : ℕ) (hvN : v N=M-1)
    (f : ℕ → ℝ) (hf : ∀ p, p.Prime → 0 ≤ f p) :
    (∑ p ∈ (nthPrime k).primesBelow, f p) ≤
      (∑ p ∈ terminalPart M k (s*log (nthPrime k : ℝ)), f p)+
      ∑ j ∈ range N, ∑ p ∈ profileBin (s*log (nthPrime k : ℝ)) (v j) (v (j+1)), f p := by
  let L := s*log (nthPrime k : ℝ)
  have hL : 0 ≤ L := mul_nonneg (by linarith) (log_natCast_nonneg _)
  rw [profileBins_sum L hL v hv (by rw [hv0]; linarith) N f,hv0,hvN,
    profileCut_root s (by linarith) (nthPrime k) (nthPrime_prime k).pos]
  have he : profileCut L (M-1) = terminalCut M L := by simp [profileCut, terminalCut]
  rw [he]
  have hh := sum_filter_add_sum_filter_not (nthPrime k).primesBelow
    (fun p => p ≤ terminalCut M L) f
  change _ ≤ (∑ p ∈ (nthPrime k).primesBelow.filter (fun p => p ≤ terminalCut M L), f p)+_
  rw [← hh]
  apply add_le_add le_rfl
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp,hcut⟩ := mem_filter.mp hp
    obtain ⟨hpk,hpp⟩ := Nat.mem_primesBelow.mp hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,hpk.le⟩,hpp⟩
  · intro p hp _
    exact hf p (mem_filter.mp hp).2

lemma profile_sector_mass (s a b : ℝ) (hs : 0 < s) (ha : 0 ≤ a) (hab : a ≤ b) :
    1/(s/(b+1))-1/(s/(a+1)) = (b-a)/s := by
  have ha0 : a+1 ≠ 0 := by linarith
  have hb0 : b+1 ≠ 0 := by linarith
  field_simp
  ring

lemma eventually_profile_sector_upper (s : ℝ) (hs : 0 < s) (v : ℕ → ℝ)
    (hv : Monotone v) (hv0 : 0 ≤ v 0) (N : ℕ) (c : ℕ → ℝ) (f : ℝ → ℕ → ℝ)
    (hbound : ∀ᶠ L : ℝ in atTop, ∀ j ∈ range N, ∀ p ∈ profileBin (s*L) (v j) (v (j+1)),
      f L p ≤ c j*((1/(p : ℝ))*(1/eulerMass p.primesBelow)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, initialEulerMass (expFloor 1 L)*
      (∑ j ∈ range N, ∑ p ∈ profileBin (s*L) (v j) (v (j+1)), f L p) <
      (∑ j ∈ range N, c j*(v (j+1)-v j))/s+ε := by
  have hvnonneg (j : ℕ) : 0 ≤ v j := hv0.trans (hv (Nat.zero_le j))
  have hh := eventually_step_profile_upper (range N) 1 (by norm_num)
    (fun j => s/(v (j+1)+1)) (fun j => s/(v j+1)) c
    (fun j _ => div_pos hs (by linarith [hvnonneg (j+1)]))
    (fun j _ => div_le_div_of_nonneg_left hs.le (by linarith [hvnonneg j])
      (by linarith [hv (Nat.le_succ j)])) f
    (by simpa only [profileBin,profileCut_scaled] using hbound) ε hε
  have he : (∑ j ∈ range N, c j*(1/(s/(v (j+1)+1))-1/(s/(v j+1)))) =
      (∑ j ∈ range N, c j*(v (j+1)-v j))/s := by
    rw [sum_div]
    apply sum_congr rfl
    intro j hj
    rw [profile_sector_mass s _ _ hs (hvnonneg j) (hv (Nat.le_succ j))]
    ring
  rw [he] at hh
  simpa only [profileBin,profileCut_scaled] using hh

#print axioms prime_prefix_le_terminal_add_profile
#print axioms eventually_profile_sector_upper
end Erdos970.RecursiveSieve.Buchstab
