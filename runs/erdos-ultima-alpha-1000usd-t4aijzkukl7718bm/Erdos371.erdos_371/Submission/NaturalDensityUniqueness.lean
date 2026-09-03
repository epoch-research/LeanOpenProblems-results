import Submission.HarmonicLargestPrimeHalf

/-! The established harmonic limit determines the value of any existing
natural density. Existence of that natural density is not proved here. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

lemma harmonicMean_const (N : ℕ) (c : ℝ) :
    harmonicMean (N+1) (fun _ => c) = c := by
  have h := harmonicMean_const_mul (N+1) c (fun _ => (1 : ℝ))
  simpa only [mul_one,harmonicMean_one] using h

lemma harmonicMean_limit_of_prefixMean_limit (F : ℕ → ℝ)
    (hF : ∀ n, 0 ≤ F n ∧ F n ≤ 1) (d : ℝ) (hd : 0 ≤ d ∧ d ≤ 1)
    (ht : Tendsto (fun N => prefixMean N F) atTop (𝓝 d)) :
    Tendsto (fun N => harmonicMean (N+1) F) atTop (𝓝 d) := by
  let G := fun n => F n-d
  have hG : ∀ n, |G n| ≤ 1 := by
    intro n
    rw [abs_le]
    dsimp [G]
    constructor <;> linarith [(hF n).1,(hF n).2,hd.1,hd.2]
  have hzero : Tendsto (fun N => prefixMean N G) atTop (𝓝 0) := by
    have h := ht.sub_const d
    rw [sub_self] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [show G = (fun n => F n-d) from rfl,prefixMean_sub]
    simp [prefixMean,hNr]
  have hh := (harmonicMean_zero_of_prefixMean_zero G hG hzero).add_const d
  simp only [zero_add] at hh
  convert hh using 1
  funext N
  simp only [G,harmonicMean_sub,harmonicMean_const,sub_add_cancel]

/-- If the rise set has a natural density, its value is necessarily one half.
The hypothesis that a natural density exists is essential to this deduction. -/
theorem largest_prime_rises_density_value (d : ℝ)
    (hd : {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity d) :
    d = 1/2 := by
  let R (n : ℕ) : ℝ := if Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n then 1 else 0
  have hR : ∀ n, 0 ≤ R n ∧ R n ≤ 1 := by
    intro n
    dsimp [R]
    split_ifs <;> norm_num
  have hd1 : d ≤ 1 := le_of_tendsto hd (Eventually.of_forall fun N =>
    Set.partialDensity_le_one {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n} Set.univ N)
  have ht : Tendsto (fun N => prefixMean N R) atTop (𝓝 d) := by
    rw [density_iff_count] at hd
    simpa [prefixMean,R,← sum_filter] using hd
  exact tendsto_nhds_unique
    (harmonicMean_limit_of_prefixMean_limit R hR d ⟨hd.nonneg,hd1⟩ ht)
    largest_prime_rises_harmonic_half

/-- Given the harmonic theorem, the natural-density conjecture is equivalent
to existence of any natural density for the set in question. -/
theorem largest_prime_rises_half_iff_density_exists :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      ∃ d : ℝ, {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity d := by
  constructor
  · intro h
    exact ⟨1/2,h⟩
  · rintro ⟨d,hd⟩
    rwa [largest_prime_rises_density_value d hd] at hd

#print axioms largest_prime_rises_density_value
#print axioms largest_prime_rises_half_iff_density_exists
end Erdos371
