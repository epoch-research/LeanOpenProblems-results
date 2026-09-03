import Submission.VariableThresholdSelectionExplore

/-! Variance-sensitive finite color selection. The range term and the finite
list logarithm are both retained; no list-size restriction is imposed. -/
namespace Erdos66BernsteinColorEnergy
open Erdos66UniformColorMoments Erdos66CenteredColorSelection
  Erdos66FixedPatternColorEnergy Erdos66OrderedColorEnergy Erdos66LogarithmicColorBudget
  Erdos66VarianceMatchingExponential Erdos66VariableThresholdSelection
open scoped Classical
set_option maxHeartbeats 3000000

noncomputable def bernsteinEnergy (h m : ℕ) (V M : ℝ) : ℝ :=
  128*(h:ℝ)^2*V*listLog h m+128*h*M^2*(listLog h m)^2+2*h*M^2

lemma bernsteinEnergy_nonneg (h m : ℕ) (V M : ℝ) (hV : 0≤V) :
    0≤bernsteinEnergy h m V M := by
  unfold bernsteinEnergy
  have he := (listLog_pos h m).le
  positivity

variable {α κ : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

lemma ordered_energy_of_fiber_bound (h : ℕ) (f : Fin h → ℝ) (hf : ∀ i, (f i)^2=1)
    (K : α → α → ℝ) (hsym : ∀ a b, K a b=K b a) (M R : ℝ)
    (hK : ∀ a b, |K a b|≤M) (ω : Fin h → α)
    (hfib : ∀ q<2*h, |colorFiber h f K ω q|≤R) :
    orderedEnergy h (fun i j ↦ (f i*f j)*K (ω i) (ω j))≤(h:ℝ)*(16*R^2+2*M^2) := by
  have he := orderedColorEnergy_le h f hf K hsym ω
  have hmass : colorEnergy h f K ω≤2*(h:ℝ)*R^2 := by
    unfold colorEnergy
    calc
      _ ≤ ∑ _q∈Finset.range (2*h), R^2 := by
        apply Finset.sum_le_sum
        intro q hq
        have hb := hfib q (Finset.mem_range.mp hq)
        nlinarith only [hb,abs_nonneg (colorFiber h f K ω q),sq_abs (colorFiber h f K ω q)]
      _ = _ := by simp [Nat.cast_mul]
  have hdiag : (∑ i : Fin h, (K (ω i) (ω i))^2)≤(h:ℝ)*M^2 := by
    calc
      _ ≤ ∑ _i : Fin h, M^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hb := hK (ω i) (ω i)
        nlinarith only [hb,abs_nonneg (K (ω i) (ω i)),sq_abs (K (ω i) (ω i))]
      _ = _ := by simp
  nlinarith only [he,hmass,hdiag]

/-- One coloring, with a variance and range bound for each centered kernel.
The formula remains valid for arbitrarily large finite request lists. -/
theorem exists_bernstein_ordered_energy (h : ℕ) (S : Finset κ)
    (f : κ → Fin h → ℝ) (hf : ∀ k∈S, ∀ i, (f k i)^2=1)
    (K : κ → α → α → ℝ) (hmean : ∀ k∈S, kernelMean (K k)=0)
    (hsym : ∀ k∈S, ∀ a b, K k a b=K k b a)
    (M V : κ → ℝ) (hM : ∀ k∈S, 0<M k) (hV0 : ∀ k∈S, 0≤V k)
    (hK : ∀ k∈S, ∀ a b, |K k a b|≤M k)
    (hV : ∀ k∈S, kernelMean (fun a b ↦ (K k a b)^2)≤V k) :
    ∃ ω : Fin h → α, ∀ k∈S,
      orderedEnergy h (fun i j ↦ (f k i*f k j)*K k (ω i) (ω j))≤
        bernsteinEnergy h S.card (V k) (M k) := by
  let ell := listLog h S.card
  let t (k : κ) := bernsteinTilt ((h:ℝ)*V k) (M k) ell
  let R (k : κ) := bernsteinRadius ((h:ℝ)*V k) (M k) ell
  have hp (k : κ) (hk : k∈S) := bernstein_parameters ((h:ℝ)*V k) (M k) ell
    (mul_nonneg (Nat.cast_nonneg _) (hV0 k hk)) (hM k hk) (listLog_pos h S.card)
  have hplus (k : κ) (hk : k∈S) (q : ℕ) (_hq : q∈Finset.range (2*h)) :
      Erdos66UniformSelection.mean (fun ω : Fin h → α ↦
        Real.exp (t k*colorFiber h (f k) (K k) ω q-t k*R k))≤Real.exp (-ell) := by
    have hm := colorFiber_variance_shifted h (f k) (hf k hk) (K k) (hmean k hk)
      (M k) (V k) (hK k hk) (hV0 k hk) (hV k hk) q (t k) (R k)
      (by rw [abs_of_pos (hp k hk).1]; exact (hp k hk).2.1)
    exact hm.trans (Real.exp_le_exp.mpr (by
      have he := (hp k hk).2.2.1
      change ((h:ℝ)*V k)*(t k)^2-t k*R k≤-ell at he
      nlinarith only [he]))
  have hminus (k : κ) (hk : k∈S) (q : ℕ) (_hq : q∈Finset.range (2*h)) :
      Erdos66UniformSelection.mean (fun ω : Fin h → α ↦
        Real.exp (-t k*colorFiber h (f k) (K k) ω q-t k*R k))≤Real.exp (-ell) := by
    have hm := colorFiber_variance_shifted h (f k) (hf k hk) (K k) (hmean k hk)
      (M k) (V k) (hK k hk) (hV0 k hk) (hV k hk) q (-t k) (-R k)
      (by rw [abs_neg,abs_of_pos (hp k hk).1]; exact (hp k hk).2.1)
    simp only [neg_sq,neg_mul_neg] at hm
    exact hm.trans (Real.exp_le_exp.mpr (by
      have he := (hp k hk).2.2.1
      change ((h:ℝ)*V k)*(t k)^2-t k*R k≤-ell at he
      nlinarith only [he]))
  have hb : 2*(S.card:ℝ)*((Finset.range (2*h)).card:ℝ)*Real.exp (-ell)<1 := by
    convert exponential_list_budget h S.card using 1
    simp only [Finset.card_range,Nat.cast_mul,Nat.cast_ofNat]
    ring
  obtain ⟨ω,hω⟩ := exists_variable_thresholds S (Finset.range (2*h))
    (fun k q ω ↦ colorFiber h (f k) (K k) ω q) t R ell (fun k hk ↦ (hp k hk).1)
    hplus hminus hb
  refine ⟨ω,fun k hk ↦ ?_⟩
  have he := ordered_energy_of_fiber_bound h (f k) (hf k hk) (K k) (hsym k hk)
    (M k) (R k) (hK k hk) ω (fun q hq ↦ (hω k hk q (Finset.mem_range.mpr hq)).le)
  have hr := mul_le_mul_of_nonneg_left (hp k hk).2.2.2 (show (0:ℝ)≤16*h by positivity)
  change 16*(h:ℝ)*(R k)^2≤16*h*(8*(((h:ℝ)*V k)*ell+(M k)^2*ell^2)) at hr
  unfold bernsteinEnergy
  change _≤128*(h:ℝ)^2*V k*ell+128*h*(M k)^2*ell^2+2*h*(M k)^2
  nlinarith only [he,hr]

/-- Specialization to the ACTUAL centered variance of each requested kernel. -/
theorem exists_bernstein_centered_energy (h : ℕ) (S : Finset κ)
    (f : κ → Fin h → ℝ) (hf : ∀ k∈S, ∀ i, (f k i)^2=1)
    (K : κ → α → α → ℝ) (hsym : ∀ k∈S, ∀ a b, K k a b=K k b a)
    (M : κ → ℝ) (hM : ∀ k∈S, 0<M k)
    (hK : ∀ k∈S, ∀ a b, |centeredKernel (K k) a b|≤M k) :
    ∃ ω : Fin h → α, ∀ k∈S,
      centeredSignedEnergy h (f k) (K k) ω≤
        bernsteinEnergy h S.card (colorVariance (K k)) (M k) := by
  exact exists_bernstein_ordered_energy h S f hf (fun k ↦ centeredKernel (K k))
    (fun k _ ↦ kernelMean_centered (K k))
    (fun k hk a b ↦ by simp only [centeredKernel,hsym k hk a b])
    M (fun k ↦ colorVariance (K k)) hM (fun k _ ↦ kernelVariance_nonneg (K k)) hK
    (fun _ _ ↦ le_rfl)

end Erdos66BernsteinColorEnergy
