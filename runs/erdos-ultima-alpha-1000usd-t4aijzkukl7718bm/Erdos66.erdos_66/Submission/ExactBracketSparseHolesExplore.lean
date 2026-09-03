import Submission.ExactBracketCentralSurgeryExplore
import Submission.SparseMaskedPerturbationExplore

/-! Exact harmonic brackets, a global logarithmic upper envelope, and
power-saving exceptions still do not force a pointwise representation limit.
The exceptional set and each fixed-tolerance saving concern the same set. -/
namespace Erdos66ExactBracketSparseHoles
open Filter AdditiveCombinatorics Erdos66ExactBracketHostEnvelope
  Erdos66ExactBracketCentralSurgery Erdos66SparseMaskedPerturbation
  Erdos66PowerExceptionalProfile Erdos66PowerExceptionalCounting
  Erdos66SummableExceptionalSet Erdos66SummableScaleCounting
  Erdos66DensityOneLogLimit Erdos66DensityOneNoLimit
  Erdos66ClampedPrefixContinuation Erdos66Fractional Erdos66Counting
open scoped Classical Topology
set_option maxHeartbeats 2500000

/-- This witnesses failure of an auxiliary sufficiency principle. It does
not exclude any other set from satisfying the original existential limit. -/
theorem exists_exact_brackets_and_sparse_holes :
    ∃ (B E : Set ℕ) (K : ℝ) (k : ℕ → ℕ),
      0 ≤ K ∧ StrictMono k ∧ (∀ j, (j+1)^2 ≤ k j) ∧
      (∀ L, PrefixBrackets profile B L) ∧
      (∀ n, (sumRep B n : ℝ) ≤ K+35*Real.log ((n : ℝ)+2)) ∧
      Summable (fun n : ℕ ↦ if n∈E then 1/((n : ℝ)+2) else 0) ∧
      Tendsto (fun N ↦ (count E N : ℝ)/N) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ if n∈E then (1 : ℝ) else (sumRep B n : ℝ)/Real.log n) atTop (𝓝 1) ∧
      (∀ ε : ℝ, 0<ε → ∃ α : ℝ, 0<α ∧ α<1 ∧
        Summable (fun n : ℕ ↦ if ε ≤ |(sumRep B n : ℝ)/Real.log n-1| then
          1/((n : ℝ)+2)^(1-α : ℝ) else 0) ∧
        Tendsto (fun N ↦ (count {n | ε ≤ |(sumRep B n : ℝ)/Real.log n-1|} N : ℝ)/
          ((N : ℝ)+2)^(1-α : ℝ)) atTop (𝓝 0)) ∧
      Tendsto (fun j ↦ (sumRep B (2^(k j)) : ℝ)/Real.log (2^(k j) : ℕ)) atTop (𝓝 0) ∧
      ¬∃ d : ℝ, Tendsto (fun n ↦ (sumRep B n : ℝ)/Real.log n) atTop (𝓝 d) := by
  obtain ⟨A,K,NB,NT,hK,hbr,henv,hcost,hB,hT⟩ := exists_exact_bracket_host
  obtain ⟨B,k,hkm,hks,hBbr,hholes,hchange,KB,hKB,henvB⟩ :=
    exists_central_surgery A K NB NT hK hbr henv hB hT
  have hchange' : Tendsto (fun n : ℕ ↦ if n∈Set.range (fun j ↦ 2^(k j)) then 0 else
      (sumRep B n : ℝ)/Real.log n-(sumRep A n : ℝ)/Real.log n) atTop (𝓝 0) := by
    convert hchange using 1
    funext n
    have he : (n∈Set.range (fun j ↦ 2^(k j))) ↔ ∃ j, n=2^(k j) := by
      simp only [Set.mem_range,eq_comm]
    rw [he,sub_div]
  have hpow := power_exception_transfer
    (fun n ↦ (sumRep A n : ℝ)/Real.log n) (fun n ↦ (sumRep B n : ℝ)/Real.log n)
    (Set.range (fun j ↦ 2^(k j))) 1 hchange'
    (sparse_dyadic_power_summable k hkm hks)
    (power_exceptions_of_potentials A 1 (by norm_num) hcost)
  have hharm : ∀ ε : ℝ, 0<ε → Summable (fun n : ℕ ↦
      if ε ≤ |(sumRep B n : ℝ)/Real.log n-1| then 1/((n : ℝ)+2) else 0) := by
    intro ε hε
    obtain ⟨α,hα,_,hs⟩ := hpow ε hε
    exact harmonic_of_power_weight _ α hα.le hs
  obtain ⟨E,hE,hlim⟩ := exists_exceptional_set
    (fun n ↦ (sumRep B n : ℝ)/Real.log n) 1 (fun n ↦ 1/((n : ℝ)+2)) (fun _ ↦ by positivity) hharm
  refine ⟨B,E,KB,k,hKB,hkm,hks,hBbr,henvB,hE,density_zero_of_harmonic_summable E hE,hlim,?_,hholes,?_⟩
  · intro ε hε
    obtain ⟨α,hα,hα1,hs⟩ := hpow ε hε
    exact ⟨α,hα,hα1,hs,count_div_power_zero _ (1-α) (by linarith) hs⟩
  · rintro ⟨d,hd⟩
    have hsTop : Tendsto (fun j ↦ 2^(k j)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1<(2 : ℕ))).comp hkm.tendsto_atTop
    have hd0 : d=0 := tendsto_nhds_unique (hd.comp hsTop) hholes
    have hd1 : d=1 := tendsto_nhds_unique_of_frequently_eq hd hlim
      ((frequently_outside E hE).mono (fun n hn ↦ (if_neg hn).symm))
    linarith

end Erdos66ExactBracketSparseHoles
