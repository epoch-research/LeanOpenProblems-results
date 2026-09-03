import Submission.PrimePowerWindowMass
import Submission.SharpPrimeBlockMeanOscillation
import Submission.QuadraticScoreTailBounds
import Submission.UpperTripleCubeScale

/-! Vanishing moving-center oscillation on fixed power windows for finite
reciprocal-prime square energy. No score separating collisions is supplied. -/
namespace Erdos1206.PowerWindowMeanOscillation
open Finset Filter PrimeBlockVariance SharpPrimeBlockVariance
  SharpPrimeBlockMeanOscillation QuadraticScoreTailBounds PrimeBlockMeanOscillation
open scoped Classical Topology

noncomputable def prefixMean (w : ℕ → ℝ) (U : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesBelow (U+1),w p/p

noncomputable def center (w : ℕ → ℝ) (n : ℕ) : ℝ := prefixMean w (cutoff n)

noncomputable def window (U V : ℕ) : Finset ℕ :=
  (Nat.primesBelow (V+1)).filter (fun p => U < p)

lemma mem_window {U V p : ℕ} : p ∈ window U V ↔ p.Prime ∧ U < p ∧ p ≤ V := by
  by_cases hp : p.Prime <;> simp [window,mem_filter,Nat.mem_primesBelow,hp]
  omega

lemma prefix_difference (w : ℕ → ℝ) {U V : ℕ} (hUV : U ≤ V) :
    prefixMean w V-prefixMean w U=∑p∈window U V,w p/p := by
  have he : (Nat.primesBelow (V+1)).filter (fun p => ¬ U < p) = Nat.primesBelow (U+1) := by
    ext p
    by_cases hp : p.Prime <;> simp [mem_filter,Nat.mem_primesBelow,hp]
    omega
  have hh := sum_filter_add_sum_filter_not (Nat.primesBelow (V+1))
    (fun p => U < p) (fun p => w p/(p:ℝ))
  rw [he] at hh
  exact sub_eq_iff_eq_add.mpr hh.symm

lemma window_energy (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0)) (U V : ℕ) :
    mass (window U V) w ≤ ∑'p,if p.Prime ∧ U ≤ p then w p^2/p else 0 := by
  have ht := tail_summable (fun p => w p^2) (fun p => sq_nonneg _) hs U
  have hh := ht.sum_le_tsum (window U V) (fun p _ => show
      0 ≤ (if p.Prime ∧ U ≤ p then w p^2/p else 0) by split_ifs <;> positivity)
  have he (p : ℕ) (hp : p ∈ window U V) :
      (if p.Prime ∧ U ≤ p then w p^2/p else 0)=w p^2/p :=
    if_pos ⟨(mem_window.mp hp).1,(mem_window.mp hp).2.1.le⟩
  simpa only [sum_congr rfl he,mass] using hh

/-- The oscillation estimate is uniform over the upper endpoint of a power window. -/
theorem prefix_power_oscillation (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0))
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hk : 0 < k) :
    ∃ H : ℕ,∀ U V : ℕ,H ≤ U → U ≤ V → V ≤ U^k →
      |prefixMean w V-prefixMean w U| < ε := by
  obtain ⟨D,hD,H,hH⟩ := PrimePowerWindowMass.eventually_window_mass
  have hden : 0 < D*k+1 := by positivity
  have ht := tail_tendsto (fun p => w p^2) (fun p => sq_nonneg _) hs
  have hevent : ∀ᶠ U : ℕ in atTop,
      (∑'p,if p.Prime ∧ U ≤ p then w p^2/p else 0) < ε^2/(D*k+1) :=
    (tendsto_order.mp ht).2 _ (by positivity)
  obtain ⟨H',hH'⟩ := eventually_atTop.mp hevent
  refine ⟨max H H',fun U V hU hUV hVk => ?_⟩
  have hmass := hH U ((le_max_left H H').trans hU) k hk (window U V) (fun p hp =>
    ⟨(mem_window.mp hp).1,(mem_window.mp hp).2.1,(mem_window.mp hp).2.2.trans hVk⟩)
  have henergy := window_energy w hs U V
  have htail := hH' U ((le_max_right H H').trans hU)
  rw [prefix_difference w hUV]
  have hcs := harmonic_cauchy (window U V) w (fun p hp => (mem_window.mp hp).1.pos)
  have hm0 : 0 ≤ mass (window U V) w := mass_nonneg _ _
  have hsmall : mass (window U V) w*(D*k+1) < ε^2 :=
    (lt_div_iff₀ hden).mp (henergy.trans_lt htail)
  have hupper := mul_le_mul_of_nonneg_left hmass hm0
  have hsq : (∑p∈window U V,w p/(p:ℝ))^2 < ε^2 := by nlinarith
  apply (sq_lt_sq₀ (abs_nonneg _) hε.le).mp
  simpa only [sq_abs] using hsq

lemma cutoff_power_comparable {n m : ℕ} (hn : 0 < n) (hm0 : 0 < m)
    (hpow : m^2 ≤ n^3) : cutoff m ≤ (cutoff n)^3 := by
  have hn1 : 1 ≤ n := hn
  have h34 : n^3 ≤ n^4 := Nat.pow_le_pow_right hn1 (by decide : 3 ≤ 4)
  have hm : m ≤ n^2 := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    simpa only [←pow_mul] using hpow.trans h34
  have hu2 : 2 ≤ cutoff n := by
    dsimp [cutoff]
    rw [pow_succ]
    have hh : 1 ≤ 2^(Nat.log 4 n) := Nat.one_le_pow _ _ (by decide)
    omega
  have hu4 : 4 ≤ (cutoff n)^2 := by nlinarith
  have hum : n ≤ (cutoff n)^2 := (cutoff_lower n).le
  have hms : (cutoff m)^2 ≤ 4*m := cutoff_upper hm0
  have hh : (cutoff m)^2 ≤ ((cutoff n)^3)^2 := by
    calc
      _ ≤ 4*m := hms
      _ ≤ 4*n^2 := Nat.mul_le_mul_left 4 hm
      _ ≤ 4*((cutoff n)^2)^2 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hum 2)
      _ ≤ (cutoff n)^2*((cutoff n)^2)^2 :=
        Nat.mul_le_mul_right _ hu4
      _ = _ := by ring
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hh

/-- In particular, the centers at the largest three roots of a strict cubic
collision have uniformly vanishing pairwise oscillation as the middle root grows. -/
theorem center_power_oscillation (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℕ,∀ m n : ℕ,H ≤ m → H ≤ n → m^2 ≤ n^3 → n^2 ≤ m^3 →
      |center w m-center w n| < ε := by
  obtain ⟨H,hH⟩ := prefix_power_oscillation w hs hε 3 (by decide)
  refine ⟨H^2+1,fun m n hm hn hmn hnm => ?_⟩
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  have hl (a : ℕ) (ha : H^2+1 ≤ a) : H ≤ cutoff a := by
    have hs : H^2 ≤ (cutoff a)^2 := by have := cutoff_lower a; omega
    exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hs
  rcases le_total m n with h | h
  · have hh := hH (cutoff m) (cutoff n) (hl m hm) (cutoff_mono h)
      (cutoff_power_comparable hm0 hn0 hnm)
    simpa only [center,abs_sub_comm] using hh
  · exact hH (cutoff n) (cutoff m) (hl n hn) (cutoff_mono h)
      (cutoff_power_comparable hn0 hm0 hmn)

/-- Uniformly small pairwise center differences throughout the interval from
 the second root to the largest root of any sufficiently large collision. -/
theorem collision_center_oscillation (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℕ,∀ a b c d : ℕ,H ≤ b → c < d → a^3+d^3=b^3+c^3 →
      ∀ m n : ℕ,b ≤ m → m ≤ d → b ≤ n → n ≤ d →
        |center w m-center w n| < ε := by
  obtain ⟨H,hH⟩ := center_power_oscillation w hs hε
  refine ⟨H,fun a b c d hb hcd he m n hbm hmd hbn hnd => ?_⟩
  obtain ⟨hmn,hnm⟩ := UpperTripleCubeScale.upper_interval_power_comparable hcd he
    ⟨hbm,hmd⟩ ⟨hbn,hnd⟩
  exact hH m n (hb.trans hbm) (hb.trans hbn) hmn hnm

#print axioms prefix_power_oscillation
#print axioms cutoff_power_comparable
#print axioms center_power_oscillation
#print axioms collision_center_oscillation
end Erdos1206.PowerWindowMeanOscillation
