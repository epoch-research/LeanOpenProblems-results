import Submission.ExponentialColorSelectionExplore

/-! Explicit logarithmic dependence on the number of finite coarse kernels.
The maximum centered entry, not merely the variance, is the input bound. -/
namespace Erdos66LogarithmicColorBudget
open Erdos66UniformColorMoments Erdos66ExponentialColorSelection
  Erdos66OrderedColorEnergy Erdos66FixedPatternColorEnergy
open scoped Classical
set_option maxHeartbeats 2600000

noncomputable def listLog (h m : ℕ) : ℝ := Real.log (4*(m:ℝ)*h+2)

lemma listLog_pos (h m : ℕ) : 0<listLog h m := by
  unfold listLog
  apply Real.log_pos
  nlinarith only [Nat.cast_nonneg (α := ℝ) h,Nat.cast_nonneg (α := ℝ) m,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) h) (Nat.cast_nonneg (α := ℝ) m)]

lemma exponential_list_budget (h m : ℕ) :
    4*(m:ℝ)*h*Real.exp (-listLog h m)<1 := by
  have hd : (0:ℝ)<4*(m:ℝ)*h+2 := by positivity
  rw [listLog,Real.exp_neg,Real.exp_log hd,←div_eq_mul_inv]
  exact (div_lt_one hd).mpr (by linarith)

variable {α κ : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

/-- Under log(4mh+2)<=h, the old linear m-factor is replaced by a logarithm.
The fixed sign pattern may differ across the requested kernels. -/
theorem exists_logarithmic_ordered_energy (h : ℕ) (S : Finset κ)
    (f : κ → Fin h → ℝ) (hf : ∀ k∈S, ∀ i, (f k i)^2=1)
    (K : κ → α → α → ℝ) (hmean : ∀ k∈S, kernelMean (K k)=0)
    (hK : ∀ k∈S, ∀ a b, |K k a b|≤1)
    (hsym : ∀ k∈S, ∀ a b, K k a b=K k b a)
    (hsize : listLog h S.card≤h) :
    ∃ ω : Fin h → α, ∀ k∈S,
      orderedEnergy h (fun i j ↦ (f k i*f k j)*K k (ω i) (ω j))≤
        64*(h:ℝ)^2*listLog h S.card+2*h := by
  let ell := listLog h S.card
  have hel : 0<ell := listLog_pos h S.card
  have hh : (0:ℝ)<h := hel.trans_le hsize
  let t := Real.sqrt (ell/(h:ℝ))
  have ht : 0<t := Real.sqrt_pos.mpr (div_pos hel hh)
  have ht2 : t^2=ell/(h:ℝ) := Real.sq_sqrt (div_nonneg hel.le hh.le)
  have hmul : (h:ℝ)*t^2=ell := by rw [ht2]; field_simp
  have hsq : t^2≤1 := by rw [ht2]; exact (div_le_one hh).mpr hsize
  have ht1 : t≤1 := by nlinarith only [hsq,ht]
  have he : (h:ℝ)*t^2-t*(2*(h:ℝ)*t) = -ell := by nlinarith only [hmul]
  have hb : 4*(S.card:ℝ)*h*Real.exp ((h:ℝ)*t^2-t*(2*(h:ℝ)*t))<1 := by
    rw [he]
    exact exponential_list_budget h S.card
  obtain ⟨ω,hω⟩ := exists_simultaneous_ordered_energy h S f hf K hmean hK hsym
    t (2*(h:ℝ)*t) ht ht1 (by positivity) hb
  refine ⟨ω,fun k hk ↦ (hω k hk).trans_eq ?_⟩
  calc
    (h:ℝ)*(16*(2*(h:ℝ)*t)^2+2)=64*(h:ℝ)^2*((h:ℝ)*t^2)+2*h := by ring
    _ = _ := by rw [hmul]

lemma orderedEnergy_scale (h : ℕ) (V : Fin h → Fin h → ℝ) (M : ℝ) :
    orderedEnergy h (fun i j ↦ M*V i j)=M^2*orderedEnergy h V := by
  have he (q : ℕ) : orderedFiber h (fun i j ↦ M*V i j) q=M*orderedFiber h V q := by
    simp only [orderedFiber,Finset.mul_sum,mul_ite,mul_zero]
  simp only [orderedEnergy,he,mul_pow,Finset.mul_sum]

/-- Each centered kernel can have its own positive range bound. No common
maximum over the target list is taken. -/
theorem exists_logarithmic_centered_energy (h : ℕ) (S : Finset κ)
    (f : κ → Fin h → ℝ) (hf : ∀ k∈S, ∀ i, (f k i)^2=1)
    (K : κ → α → α → ℝ) (hsym : ∀ k∈S, ∀ a b, K k a b=K k b a)
    (M : κ → ℝ) (hM : ∀ k∈S, 0<M k)
    (hK : ∀ k∈S, ∀ a b, |centeredKernel (K k) a b|≤M k)
    (hsize : listLog h S.card≤h) :
    ∃ ω : Fin h → α, ∀ k∈S,
      orderedEnergy h (fun i j ↦ (f k i*f k j)*centeredKernel (K k) (ω i) (ω j))≤
        (M k)^2*(64*(h:ℝ)^2*listLog h S.card+2*h) := by
  let V (k : κ) (a b : α) := centeredKernel (K k) a b/M k
  have hm (k : κ) (hk : k∈S) : kernelMean (V k)=0 := by
    unfold kernelMean V
    simp only [div_eq_mul_inv,mul_comm _ (M k)⁻¹,Erdos66UniformSelection.mean_const_mul]
    have hz := kernelMean_centered (K k)
    unfold kernelMean at hz
    rw [hz,mul_zero]
  have hV (k : κ) (hk : k∈S) (a b : α) : |V k a b|≤1 := by
    dsimp only [V]
    rw [abs_div,abs_of_pos (hM k hk)]
    exact (div_le_one (hM k hk)).mpr (hK k hk a b)
  have hs (k : κ) (hk : k∈S) (a b : α) : V k a b=V k b a := by
    simp only [V,centeredKernel,hsym k hk a b]
  obtain ⟨ω,hω⟩ := exists_logarithmic_ordered_energy h S f hf V hm hV hs hsize
  refine ⟨ω,fun k hk ↦ ?_⟩
  have he : (fun i j ↦ (f k i*f k j)*centeredKernel (K k) (ω i) (ω j))=
      (fun i j ↦ M k*((f k i*f k j)*V k (ω i) (ω j))) := by
    funext i j
    unfold V
    field_simp [(hM k hk).ne']
  rw [he,orderedEnergy_scale]
  exact mul_le_mul_of_nonneg_left (hω k hk) (sq_nonneg _)

end Erdos66LogarithmicColorBudget
