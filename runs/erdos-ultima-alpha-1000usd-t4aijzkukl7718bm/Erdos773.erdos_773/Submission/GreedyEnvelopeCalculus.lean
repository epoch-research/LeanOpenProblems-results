import Submission.GreedyTrajectoryCalculus

/-!
Growing envelopes with the q powers matched to the residual degree. The
availability envelope includes the factor 1/(1+t^2), so its derivative
absorbs accumulated two-degree errors without an extra power of time.
-/
namespace Erdos773.GreedyEnvelopeCalculus
open Set GreedyTrajectoryCalculus
set_option maxHeartbeats 2500000
noncomputable section

def growth (K r t : ℝ) : ℝ := Real.exp ((K-r)*t^3+K*t)
def dgrowth (K r t : ℝ) : ℝ := (3*(K-r)*t^2+K)*growth K r t

def budgetWeight (K t : ℝ) : ℝ := growth K 0 t/(1+t^2)
def dbudgetWeight (K t : ℝ) : ℝ :=
  growth K 0 t*((3*K*t^2+K)*(1+t^2)-2*t)/(1+t^2)^2

lemma growth_pos (K r t : ℝ) : 0 < growth K r t := Real.exp_pos _
@[simp] lemma growth_zero (K r : ℝ) : growth K r 0 = 1 := by simp [growth]
@[simp] lemma budgetWeight_zero (K : ℝ) : budgetWeight K 0 = 1 := by simp [budgetWeight]

lemma hasDerivAt_growth (K r t : ℝ) : HasDerivAt (growth K r) (dgrowth K r t) t := by
  convert ((((hasDerivAt_id t).pow 3).const_mul (K-r)).add
    ((hasDerivAt_id t).const_mul K)).exp using 1
  simp [dgrowth,growth]
  ring

lemma growth_shift (K r t : ℝ) : growth K (r+1) t = q t*growth K r t := by
  rw [growth,q,growth,← Real.exp_add]
  congr 1
  ring

lemma growth_one (K t : ℝ) : growth K 1 t = q t*growth K 0 t := by
  simpa using growth_shift K 0 t

lemma growth_two (K t : ℝ) : growth K 2 t = (q t)^2*growth K 0 t := by
  have hh := growth_shift K 1 t
  norm_num at hh
  rw [hh,growth_one]
  ring

lemma growth_monotone {K r s t : ℝ} (hK : 0 ≤ K) (hKr : r ≤ K)
    (hs : 0 ≤ s) (hst : s ≤ t) : growth K r s ≤ growth K r t := by
  apply Real.exp_le_exp.mpr
  exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst 3) (sub_nonneg.mpr hKr))
    (mul_le_mul_of_nonneg_left hst hK)

/-- The normalized degree envelopes grow at least as K*(1+t^2) times
    themselves, for all three required q powers r=0,1,2. -/
lemma dgrowth_lower {K r t : ℝ} (hK : 3 ≤ K) (hr : r ≤ 2) :
    K*(1+t^2)*growth K r t ≤ dgrowth K r t := by
  apply mul_le_mul_of_nonneg_right _ (growth_pos _ _ _).le
  have hh : 0 ≤ 2*K-3*r := by linarith
  nlinarith only [mul_nonneg hh (sq_nonneg t)]

lemma growth_increment_lower {K r t h : ℝ} (hK : 3 ≤ K) (hr : r ≤ 2)
    (ht : 0 ≤ t) (hh : 0 ≤ h) :
    K*(1+t^2)*growth K r t*h ≤ growth K r (t+h)-growth K r t := by
  have hK0 : 0 ≤ K := by linarith
  have hKr : r ≤ K := by linarith
  have hdf (x : ℝ) (hx : x ∈ Icc t (t+h)) : K*(1+t^2)*growth K r t ≤ dgrowth K r x := by
    apply le_trans _ (dgrowth_lower hK hr)
    apply mul_le_mul _ (growth_monotone hK0 hKr ht hx.1) (growth_pos _ _ _).le
      (by positivity : (0:ℝ) ≤ K*(1+x^2))
    apply mul_le_mul_of_nonneg_left _ hK0
    have hh := pow_le_pow_left₀ ht hx.1 2
    linarith
  simpa only [add_sub_cancel_left] using increment_lower (growth K r) (dgrowth K r)
    t (t+h) (K*(1+t^2)*growth K r t) (by linarith)
    (fun x _ => hasDerivAt_growth K r x) hdf

lemma hasDerivAt_budgetWeight (K t : ℝ) :
    HasDerivAt (budgetWeight K) (dbudgetWeight K t) t := by
  have hn : (1:ℝ)+t^2 ≠ 0 := by positivity
  convert (hasDerivAt_growth K 0 t).div
    ((hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2)) hn using 1
  simp [dbudgetWeight,dgrowth]
  ring

/-- Dividing by 1+t^2 makes the derivative dominate a constant multiple
    of the undivided two-degree envelope. -/
lemma dbudgetWeight_lower {K t : ℝ} (hK : 0 ≤ K) :
    (K-1)*growth K 0 t ≤ dbudgetWeight K t := by
  have hp : (0:ℝ) < (1+t^2)^2 := by positivity
  have hn : 0 ≤ (2*K+1)*t^4+(2*K+1)*t^2+(t-1)^2 := by positivity
  have hpoly : (K-1)*(1+t^2)^2 ≤ (3*K*t^2+K)*(1+t^2)-2*t := by nlinarith only [hn]
  apply (le_div_iff₀ hp).mpr
  have hh := mul_le_mul_of_nonneg_left hpoly (growth_pos K 0 t).le
  nlinarith only [hh]

lemma budgetWeight_increment_lower {K t h : ℝ} (hK : 1 ≤ K)
    (ht : 0 ≤ t) (hh : 0 ≤ h) :
    (K-1)*growth K 0 t*h ≤ budgetWeight K (t+h)-budgetWeight K t := by
  have hK0 : 0 ≤ K := by linarith
  have hdf (x : ℝ) (hx : x ∈ Icc t (t+h)) : (K-1)*growth K 0 t ≤ dbudgetWeight K x :=
    (mul_le_mul_of_nonneg_left (growth_monotone hK0 hK0 ht hx.1) (by linarith)).trans
      (dbudgetWeight_lower hK0)
  simpa only [add_sub_cancel_left] using increment_lower (budgetWeight K) (dbudgetWeight K)
    t (t+h) ((K-1)*growth K 0 t) (by linarith)
    (fun x _ => hasDerivAt_budgetWeight K x) hdf

/-- Physical error scales, with relative smallness parameter rho. -/
def E2 (d ρ K t : ℝ) : ℝ := d*ρ*growth K 0 t
def E3 (d ρ K t : ℝ) : ℝ := d^2*ρ*growth K 1 t
def E4 (d ρ K t : ℝ) : ℝ := d^3*ρ*growth K 2 t
def EQ (V ρ K t : ℝ) : ℝ := V*ρ*budgetWeight K t

/-- The q powers in consecutive degree errors agree exactly. -/
theorem error_scale_relations (d ρ K t : ℝ) :
    E3 d ρ K t = d*q t*E2 d ρ K t ∧
    E4 d ρ K t = d*q t*E3 d ρ K t := by
  dsimp [E2,E3,E4]
  rw [growth_one,growth_two]
  constructor <;> ring

/-- One physical step h=d/V has enough EQ growth to absorb many copies
    of the local two-degree error. -/
theorem availability_envelope_step {V d ρ K t : ℝ} (hV : 0 < V) (hd : 0 ≤ d)
    (hρ : 0 ≤ ρ) (hK : 1 ≤ K) (ht : 0 ≤ t) :
    (K-1)*E2 d ρ K t ≤ EQ V ρ K (t+d/V)-EQ V ρ K t := by
  have hh := budgetWeight_increment_lower hK ht (div_nonneg hd hV.le)
  have hh := mul_le_mul_of_nonneg_left hh (mul_nonneg hV.le hρ)
  convert hh using 1
  · dsimp [E2]
    field_simp
  · dsimp [EQ]
    ring

/-- Simultaneous physical-step lower bounds for the three degree envelopes. -/
theorem degree_envelope_steps {V d ρ K t : ℝ} (hV : 0 < V) (hd : 0 ≤ d)
    (hρ : 0 ≤ ρ) (hK : 3 ≤ K) (ht : 0 ≤ t) :
    (d/V)*K*(1+t^2)*E2 d ρ K t ≤ E2 d ρ K (t+d/V)-E2 d ρ K t ∧
    (d/V)*K*(1+t^2)*E3 d ρ K t ≤ E3 d ρ K (t+d/V)-E3 d ρ K t ∧
    (d/V)*K*(1+t^2)*E4 d ρ K t ≤ E4 d ρ K (t+d/V)-E4 d ρ K t := by
  have h0 := growth_increment_lower (r := 0) hK (by norm_num) ht (div_nonneg hd hV.le)
  have h1 := growth_increment_lower (r := 1) hK (by norm_num) ht (div_nonneg hd hV.le)
  have h2 := growth_increment_lower (r := 2) hK (by norm_num) ht (div_nonneg hd hV.le)
  refine ⟨?_,?_,?_⟩
  · convert mul_le_mul_of_nonneg_left h0 (mul_nonneg hd hρ) using 1 <;> dsimp [E2] <;> ring
  · convert mul_le_mul_of_nonneg_left h1 (mul_nonneg (sq_nonneg d) hρ) using 1 <;> dsimp [E3] <;> ring
  · convert mul_le_mul_of_nonneg_left h2 (mul_nonneg (pow_nonneg hd 3) hρ) using 1 <;> dsimp [E4] <;> ring

#print axioms growth_increment_lower
#print axioms dbudgetWeight_lower
#print axioms budgetWeight_increment_lower
#print axioms error_scale_relations
#print axioms availability_envelope_step
#print axioms degree_envelope_steps
end
end Erdos773.GreedyEnvelopeCalculus
