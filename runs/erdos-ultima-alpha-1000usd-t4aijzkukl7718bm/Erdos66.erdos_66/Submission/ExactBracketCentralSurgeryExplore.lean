import Submission.SparseCentralDeletionExplore
import Submission.SimultaneousRankRestorationExplore

/-! Sparse central surgery of an exact-bracket joint host: normalized holes
on one remote dyadic sequence, with sublogarithmic change everywhere else.
This is a counterexample to an auxiliary sufficiency principle, not to the
existential conjecture. -/
namespace Erdos66ExactBracketCentralSurgery
open Filter AdditiveCombinatorics Erdos66RemoteCentralDeletion Erdos66SparseCentralDeletion
  Erdos66SquareExponentSchedule Erdos66SimultaneousRankRestoration
  Erdos66ExactBracketHostEnvelope Erdos66ClampedPrefixContinuation Erdos66Fractional
  Erdos66CentralTripleDeletion Erdos66CentralTripleCounts Erdos66BoundaryCorrectionEligibility
  Erdos66BoundaryPairCounts Erdos66BoundaryPairPotential Erdos66JointBoundaryTripleCounts
  Erdos66InsertionIncrementComparison Erdos66DyadicDeletion Erdos66Counting Erdos66Explore
open scoped Classical Topology
set_option maxHeartbeats 3500000

lemma boundary_core_ratio (A : Set ℕ) (j n : ℕ) (hn : 2 ≤ n)
    (hB : ((j : ℝ)+1)*((boundary A (cutoff j) n).card : ℝ) ≤ 20*Real.log ((n : ℝ)+1)) :
    (sumRep (A\(upperEndpoints A (n/(cutoff j)^2) n : Set ℕ)) n : ℝ)/Real.log n ≤
      80/((j : ℝ)+1)+1/Real.log n := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0<Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlog := Real.log_le_log (show 0<(n : ℝ)+1 by linarith)
    (show (n : ℝ)+1 ≤ (n : ℝ)^2 by nlinarith)
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hj : 0<(j : ℝ)+1 := by positivity
  have hcap := central_residual A (cutoff j) n (cutoff_ge_two j)
  have hcap' : (sumRep (A\(upperEndpoints A (n/(cutoff j)^2) n : Set ℕ)) n : ℝ) ≤
      2*((boundary A (cutoff j) n).card : ℝ)+1 := by exact_mod_cast hcap
  have hb : ((boundary A (cutoff j) n).card : ℝ) ≤ 40*Real.log n/((j : ℝ)+1) :=
    (le_div_iff₀ hj).mpr (by nlinarith)
  apply (div_le_iff₀ hl).mpr
  have he : (80/((j : ℝ)+1)+1/Real.log n)*Real.log n=
      2*(40*Real.log n/((j : ℝ)+1))+1 := by field_simp; ring
  rw [he]
  linarith

/-- One B keeps every exact harmonic prefix bracket, has normalized holes
on a strictly increasing dyadic sequence, and differs from the input host
by o(log n) away from precisely that sequence. -/
theorem exists_central_surgery
    (A : Set ℕ) (K : ℝ) (NB : ℕ → ℕ) (NT : ℕ → ℕ → ℕ)
    (hK : 0 ≤ K) (hbr : ∀ L, PrefixBrackets profile A L)
    (henv : ∀ n, (sumRep A n : ℝ) ≤ K+34*Real.log ((n : ℝ)+2))
    (hB : ∀ j n, NB j ≤ n → ((j : ℝ)+1)*((boundary A (cutoff j) n).card : ℝ) ≤
      20*Real.log ((n : ℝ)+1))
    (hT : ∀ C h N n z, NT C h ≤ N → n ≤ C*N → z ≤ N^h → n≠z →
      (fiber A N n z).card ≤ tripleCap h) :
    ∃ (B : Set ℕ) (k : ℕ → ℕ), StrictMono k ∧ (∀ j, (j+1)^2 ≤ k j) ∧
      (∀ L, PrefixBrackets profile B L) ∧
      Tendsto (fun j ↦ (sumRep B (2^(k j)) : ℝ)/Real.log (2^(k j) : ℕ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ ↦ if ∃ j, n=2^(k j) then 0 else
        ((sumRep B n : ℝ)-sumRep A n)/Real.log n) atTop (𝓝 0) ∧
      ∃ KB : ℝ, 0 ≤ KB ∧ ∀ n, (sumRep B n : ℝ) ≤ KB+35*Real.log ((n : ℝ)+2) := by
  have ht (j : ℕ) : ∃ T : ℕ, ∀ n, T ≤ n → 2 ≤ n ∧ NB j ≤ n ∧
      ∀ z, z≠n → (hits A (upperEndpoints A (n/(cutoff j)^2) n) z).card ≤ max (tripleCap 66) 3 := by
    have hh := eventually_bounded_central_packet A hbr NT hT (cutoff j) (cutoff_ge_two j)
    obtain ⟨T,hT'⟩ := eventually_atTop.mp hh
    exact ⟨max T (max 2 (NB j)),fun n hn ↦
      ⟨(le_max_left _ _).trans ((le_max_right _ _).trans hn),
       (le_max_right _ _).trans ((le_max_right _ _).trans hn),
       hT' n ((le_max_left _ _).trans hn)⟩⟩
  choose T hT' using ht
  obtain ⟨k,hkm,hks⟩ := exists_dominating_schedule T
  let s : ℕ → ℕ := fun j ↦ 2^(k j)
  let D : ℕ → Finset ℕ := fun j ↦ upperEndpoints A (s j/(cutoff j)^2) (s j)
  have hs (j : ℕ) := hT' j (s j) (hks j).2
  have hloc : ∀ j a, a∈D j → 2^(k j)<2*a := by
    intro j a ha
    exact (mem_upperEndpoints.mp ha).2.2.2.2.2
  have hremoved : ∀ j, D j ⊆ removed A (k j) := by
    intro j a ha
    obtain ⟨han,_,_,haA,hbA,hlt⟩ := mem_upperEndpoints.mp ha
    exact mem_removed.mpr ⟨s j-a,hbA,haA,by dsimp [s] at *; omega,by omega⟩
  have hDA : packetUnion D ⊆ A := by
    rintro a ⟨j,hj⟩
    exact (mem_upperEndpoints.mp hj).2.2.2.1
  have hdec := packetUnion_negligible A k D hremoved K 34 hK (by norm_num) henv
  obtain ⟨B,hcore,hBbr,hinc⟩ := exists_simultaneous_sparse_restoration A hbr (packetUnion D) hDA hdec
  have hsTop : Tendsto s atTop atTop := by
    have hkTop : Tendsto k atTop atTop := hkm.tendsto_atTop
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1<(2 : ℕ))).comp hkTop
  have hcorelim : Tendsto (fun j ↦ (sumRep (A\packetUnion D) (s j) : ℝ)/Real.log (s j)) atTop (𝓝 0) := by
    have hsmall := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 80
    have hinv := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hsTop)).const_div_atTop 1
    have hb := hsmall.add hinv
    simp only [mul_zero,add_zero] at hb
    apply squeeze_zero (fun j ↦ div_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)) ?_ hb
    intro j
    have hm := sumRep_mono (show A\packetUnion D ⊆ A\(D j : Set ℕ) from by
      rintro a ⟨ha,hd⟩
      exact ⟨ha,fun hj ↦ hd ⟨j,hj⟩⟩) (s j)
    have hm' : (sumRep (A\packetUnion D) (s j) : ℝ) ≤ sumRep (A\(D j : Set ℕ)) (s j) := by exact_mod_cast hm
    have hh := (div_le_div_of_nonneg_right hm' (Real.log_natCast_nonneg _)).trans
      (boundary_core_ratio A j (s j) (hs j).1 (hB j (s j) (hs j).2.1))
    convert hh using 1
    simp only [Function.comp_apply]
    ring
  have hholes := (hinc.comp hsTop).add hcorelim
  simp only [add_zero] at hholes
  have hholes' : Tendsto (fun j ↦ (sumRep B (s j) : ℝ)/Real.log (s j)) atTop (𝓝 0) := by
    convert hholes using 1
    funext j
    dsimp only [Function.comp_apply]
    ring
  have hloss := off_center_loss_limit A k D (fun j ↦ (hks j).1) hloc (max (tripleCap 66) 3)
    (fun j z hz ↦ (hs j).2.2 z hz)
  let f : ℕ → ℝ := fun n ↦ if ∃ j, n=2^(k j) then 0 else
    (sumRep A n : ℝ)-sumRep (A\packetUnion D) n
  have hf (n : ℕ) : 0 ≤ f n := by
    dsimp only [f]
    split_ifs
    · rfl
    · have hm := sumRep_mono (show A\packetUnion D ⊆ A from Set.diff_subset) n
      exact sub_nonneg.mpr (by exact_mod_cast hm)
  have hloss' : Tendsto (fun n ↦ f n/Real.log n) atTop (𝓝 0) := by
    apply log_zero_unshift f hf
    convert hloss using 1
    funext n
    dsimp only [f]
    split_ifs <;> simp
  have hmi : Tendsto (fun n : ℕ ↦ if ∃ j, n=2^(k j) then 0 else
      ((sumRep B n : ℝ)-sumRep (A\packetUnion D) n)/Real.log n) atTop (𝓝 0) := by
    have hi (n : ℕ) : 0 ≤ ((sumRep B n : ℝ)-sumRep (A\packetUnion D) n)/Real.log n :=
      div_nonneg (sub_nonneg.mpr (by exact_mod_cast sumRep_mono hcore n)) (Real.log_natCast_nonneg _)
    apply squeeze_zero ?_ ?_ hinc
    · intro n; split_ifs <;> simp_all only [le_refl]
    · intro n; split_ifs <;> simp_all only [le_refl]
  have hdiff := hmi.sub hloss'
  simp only [sub_zero] at hdiff
  have henvB : ∃ KB : ℝ, 0 ≤ KB ∧ ∀ n, (sumRep B n : ℝ) ≤ KB+35*Real.log ((n : ℝ)+2) := by
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hinc.eventually_lt_const (by norm_num : (0 : ℝ)<1))
    refine ⟨K+(N+2 : ℕ),by positivity,?_⟩
    intro n
    have hl2 : 0 ≤ Real.log ((n : ℝ)+2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    by_cases hn : max N 2 ≤ n
    · have hnN : N ≤ n := (le_max_left _ _).trans hn
      have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
      have hl : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
      have hh := (div_lt_iff₀ hl).mp (hN n hnN)
      have hm : (sumRep (A\packetUnion D) n : ℝ) ≤ sumRep A n := by
        exact_mod_cast Erdos66Explore.sumRep_mono (show A\packetUnion D ⊆ A from Set.diff_subset) n
      have hlshift := Real.log_le_log (by exact_mod_cast (show 0<n by omega) : (0 : ℝ)<n)
        (show (n : ℝ) ≤ (n : ℝ)+2 by linarith)
      have ha := henv n
      have hNpos := Nat.cast_nonneg (α := ℝ) (N+2)
      linarith
    · have hh : (sumRep B n : ℝ) ≤ (N+2 : ℕ) := by
        exact_mod_cast (show sumRep B n ≤ N+2 from (sumRep_le_succ B n).trans (by omega))
      linarith
  refine ⟨B,k,hkm,fun j ↦ (hks j).1,hBbr,hholes',?_,henvB⟩
  convert hdiff using 1
  funext n
  dsimp only [f]
  split_ifs <;> simp
  ring

end Erdos66ExactBracketCentralSurgery
