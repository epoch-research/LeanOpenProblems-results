import Submission.UniformMixedCyclicRelativeExplore
import Submission.OddLogTuningExplore

/-! Independently selected odd cyclic mixed-flat families at a prescribed
logarithmic base mean. No natural-number prefix compatibility is asserted. -/
namespace Erdos66LogarithmicMixedFamily
open Filter Erdos66OuterCarryProfile Erdos66UniformMixedCyclicRelative Erdos66OddLogTuning
open scoped Topology Classical
set_option maxHeartbeats 1800000

theorem exists_logarithmic_mixed_family (c τ η : ℝ) (hc : 0 < c) (hτ : 0 < τ)
    (hη : 0 < η) (hη1 : η ≤ 1) (H N₀ : ℕ) :
    ∃ M : ℕ, N₀ < M ∧ Odd M ∧ ∃ hM : NeZero M,
      ∃ μ : ℝ, 0 < μ ∧ |μ/Real.log M-c| < τ ∧
        ∃ C : ℕ → Finset (ZMod M), C 0=∅ ∧ Monotone C ∧
          ∀ i ≤ H, ∀ j ≤ H, ∀ z,
            |(cyclicCount M (C i) (C j) z : ℝ)-μ*i*j| ≤ η*(μ*i*j) := by
  obtain ⟨D,K₀,hD,hK₀,hfamily⟩ := every_prime_mixed_cyclic_family η hη hη1 H
  let d : ℝ := 8*(D : ℝ)^2/c
  have hd : 0 < d := by dsimp [d]; positivity
  let K := oddThickness d
  let M : ℕ → ℕ := fun p ↦ (p*K p)^2
  let μ : ℕ → ℝ := fun p ↦ 4*(D : ℝ)^2*(K p : ℝ)^2
  have hlim : Tendsto (fun p ↦ μ p/Real.log (M p)) atTop (𝓝 c) := by
    have hh := (tuned_odd_mean hd).const_mul c
    simp only [mul_one] at hh
    convert hh using 1
    funext p
    dsimp [μ,M,K,d]
    field_simp
    ring
  have hev := ((oddThickness_atTop hd).eventually_ge_atTop K₀).and
    (((odd_period_atTop hd).eventually_gt_atTop N₀).and
      (hlim.eventually (Metric.ball_mem_nhds c hτ)))
  obtain ⟨L,hL⟩ := eventually_atTop.mp hev
  let P := max (8*(D*H)+2) (2*(D*H)^2)
  obtain ⟨p,hpbound,hp⟩ := Nat.exists_infinite_primes (max L (P+1))
  have hpL : L ≤ p := (le_max_left _ _).trans hpbound
  have hpP : P < p := lt_of_lt_of_le (Nat.lt_succ_self P) ((le_max_right _ _).trans hpbound)
  have hp2 : 2 < p := by dsimp [P] at hpP; omega
  obtain ⟨hK,hMlarge,hmean⟩ := hL p hpL
  change dist (μ p/Real.log (M p)) c < τ at hmean
  rw [Real.dist_eq] at hmean
  obtain ⟨C,hC0,hCmono,hC⟩ := hfamily p hp hpP (K p) hK
  have hKpos : 0 < K p := oddThickness_pos d p
  have hModd : Odd (M p) := (hp.odd_of_ne_two (by omega)).mul (oddThickness_odd d p) |>.pow
  have hMpos : 0 < M p := by dsimp [M]; positivity
  have hμpos : 0 < μ p := by dsimp [μ]; positivity
  refine ⟨M p,hMlarge,hModd,⟨hMpos.ne'⟩,μ p,hμpos,hmean,C,hC0,hCmono,?_⟩
  intro i hi j hj z
  exact hC i hi j hj z

end Erdos66LogarithmicMixedFamily
