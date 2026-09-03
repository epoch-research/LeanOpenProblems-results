import FormalConjecturesUtil
import Submission.RescalingDiagnostic
import Submission.ExactIntegerPower

/-! An exact dilation law and a nonzero pure-power asymptotic force exact
agreement with that power on a tail. For integer sequences in the interval
[1,2), this forces exponent one. No dilation law for extremal numbers of
arbitrary forbidden graphs is asserted. -/
open Filter Asymptotics Set
open scoped Topology
namespace Erdos713ExactDilationExponent
open Erdos713PolynomialRate Erdos713RescalingDiagnostic
set_option maxHeartbeats 1000000

lemma multiplier_eq_power {f : ℕ → ℝ} {α c b : ℝ} {a : ℕ}
    (ha : 1 ≤ a) (hc : c ≠ 0)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (hrec : ∀ᶠ n : ℕ in atTop, f (a*n) = b*f n) :
    b = (a : ℝ)^α := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hscale : Tendsto (fun n : ℕ => f (a*n)/(n : ℝ)^α)
      atTop (𝓝 (c*(a : ℝ)^α)) := by
    simpa only [← Nat.cast_mul, Nat.floor_natCast] using scaled_power_ratio haR hf
  have hmult : Tendsto (fun n : ℕ => f (a*n)/(n : ℝ)^α)
      atTop (𝓝 (b*c)) := by
    apply ((ratio_limit hf).const_mul b).congr'
    filter_upwards [hrec] with n hn
    rw [hn, mul_div_assoc]
  have he := tendsto_nhds_unique hscale hmult
  apply (mul_right_cancel₀ hc)
  simpa only [mul_comm] using he.symm

/-- Iteration along a fixed multiplicative ray. The ray must tend to infinity,
which is why a genuine dilation a>=2 is required. -/
theorem eventually_exact_power {f : ℕ → ℝ} {α c b : ℝ} {a : ℕ}
    (ha : 2 ≤ a) (hc : c ≠ 0)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (hrec : ∀ᶠ n : ℕ in atTop, f (a*n) = b*f n) :
    ∀ᶠ n : ℕ in atTop, f n = c*(n : ℝ)^α := by
  have hb := multiplier_eq_power (by omega : 1 ≤ a) hc hf hrec
  have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hbpos : 0 < b := hb ▸ Real.rpow_pos_of_pos haR α
  obtain ⟨N,hN⟩ := eventually_atTop.mp hrec
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnpos : 0 < n := (le_max_right _ _).trans hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hiter (j : ℕ) : f (a^j*n) = b^j*f n := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hj : N ≤ a^j*n := by
        have hh := Nat.mul_le_mul_right n (Nat.one_le_pow j a (by omega))
        simp only [one_mul] at hh
        exact hnN.trans hh
      calc
        f (a^(j+1)*n) = f (a*(a^j*n)) := by rw [pow_succ']; congr 1; ring
        _ = b*f (a^j*n) := hN _ hj
        _ = b^(j+1)*f n := by rw [ih,pow_succ']; ring
  have htop : Tendsto (fun j : ℕ => a^j*n) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (show 1 < a by omega)).atTop_mul_const' hnpos
  have hratio (j : ℕ) : f (a^j*n)/((a^j*n : ℕ) : ℝ)^α = f n/(n : ℝ)^α := by
    rw [hiter, Nat.cast_mul, Nat.cast_pow, Real.mul_rpow (by positivity) (Nat.cast_nonneg n)]
    have hp : ((a : ℝ)^j)^α = b^j := by
      rw [← Real.rpow_natCast_mul haR.le, mul_comm, Real.rpow_mul_natCast haR.le, ← hb]
    rw [hp]
    field_simp [pow_ne_zero _ hbpos.ne']
  have hlim := (ratio_limit hf).comp htop
  have hlim' : Tendsto (fun _j : ℕ => f n/(n : ℝ)^α) atTop (𝓝 c) := by
    change Tendsto (fun j : ℕ => f (a^j*n)/((a^j*n : ℕ) : ℝ)^α) atTop (𝓝 c) at hlim
    simpa only [hratio] using hlim
  have he : f n/(n : ℝ)^α = c := tendsto_nhds_unique tendsto_const_nhds hlim'
  exact (div_eq_iff (Real.rpow_pos_of_pos hnR α).ne').mp he

/-- Exact dilation would force exponent one, not merely a rational exponent.
This is consequently too restrictive to supply a universal graph recurrence. -/
theorem exponent_eq_one {f : ℕ → ℤ} {α c b : ℝ} {a : ℕ}
    (ha : 2 ≤ a) (hα : α ∈ Ico 1 2) (hc : 0 < c)
    (hf : (fun n => (f n : ℝ)) ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (hrec : ∀ᶠ n : ℕ in atTop, (f (a*n) : ℝ) = b*(f n : ℝ)) :
    α = 1 := by
  by_contra he
  have hα1 : 1 < α := lt_of_le_of_ne hα.1 (Ne.symm he)
  exact Erdos713ExactIntegerPower.no_exact_integer_power_tail hα1 hα.2 hc
    (eventually_exact_power ha hc.ne' hf hrec)

/-- The corresponding natural-valued version allows a real multiplier b. -/
theorem nat_exponent_eq_one {f : ℕ → ℕ} {α c b : ℝ} {a : ℕ}
    (ha : 2 ≤ a) (hα : α ∈ Ico 1 2) (hc : 0 < c)
    (hf : (fun n => (f n : ℝ)) ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (hrec : ∀ᶠ n : ℕ in atTop, (f (a*n) : ℝ) = b*(f n : ℝ)) :
    α = 1 := by
  apply exponent_eq_one (f := fun n => (f n : ℤ)) ha hα hc
  · simpa only [Int.cast_natCast] using hf
  · simpa only [Int.cast_natCast] using hrec

/-- Under a superlinear pure-power asymptotic, every fixed dilation has
infinitely many failures of every exact constant-multiplier identity. -/
theorem extremal_dilation_failures {W : Type*} (H : SimpleGraph W)
    {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hc : 0 < c)
    (hf : (fun n : ℕ => (SimpleGraph.extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) (a : ℕ) (ha : 2 ≤ a) (b : ℝ) :
    ∃ᶠ n : ℕ in atTop,
      (SimpleGraph.extremalNumber (a*n) H : ℝ) ≠ b*(SimpleGraph.extremalNumber n H : ℝ) := by
  by_contra h
  have hrec : ∀ᶠ n : ℕ in atTop,
      (SimpleGraph.extremalNumber (a*n) H : ℝ) = b*(SimpleGraph.extremalNumber n H : ℝ) := by
    simpa only [Filter.Frequently, not_not] using h
  have he := nat_exponent_eq_one ha ⟨hα1.le,hα2⟩ hc hf hrec
  linarith

#print axioms multiplier_eq_power
#print axioms eventually_exact_power
#print axioms exponent_eq_one
#print axioms nat_exponent_eq_one
#print axioms extremal_dilation_failures
end Erdos713ExactDilationExponent
