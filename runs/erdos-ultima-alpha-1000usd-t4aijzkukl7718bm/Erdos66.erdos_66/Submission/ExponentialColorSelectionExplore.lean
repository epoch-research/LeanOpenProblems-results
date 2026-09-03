import Submission.MatchingColorExponentialExplore

/-! Finite target lists can be paid for logarithmically using matching-fiber
exponential bounds. No infinite target list or compatible scale chain is asserted. -/
namespace Erdos66ExponentialColorSelection
open Erdos66UniformSelection Erdos66UniformColorMoments Erdos66MatchingColorExponential
  Erdos66FixedPatternColorEnergy Erdos66OrderedColorEnergy
open scoped Classical
set_option maxHeartbeats 3000000

lemma sumEdges_card_le (h q : ℕ) : (sumEdges h q).card≤h := by
  have hinj : Set.InjOn Prod.fst (sumEdges h q : Set (Fin h×Fin h)) := by
    intro e he d hd hed
    apply Prod.ext hed
    apply Fin.ext
    have he' := (mem_sumEdges h q e).mp he
    have hd' := (mem_sumEdges h q d).mp hd
    have hf := congrArg Fin.val hed
    omega
  calc
    _ = ((sumEdges h q).image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (Fin h) := Finset.card_le_univ _
    _ = h := Fintype.card_fin h

variable {α κ : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

lemma colorFiber_mgf (h : ℕ) (f : Fin h → ℝ) (hf : ∀ i, |f i|≤1)
    (K : α → α → ℝ) (hmean : kernelMean K=0) (hK : ∀ a b, |K a b|≤1)
    (q : ℕ) (t : ℝ) (ht : |t|≤1) :
    mean (fun ω : Fin h → α ↦ Real.exp (t*colorFiber h f K ω q))≤
      Real.exp ((h:ℝ)*t^2) := by
  have he := matching_centered_mgf (sumEdges h q) (sumEdges_ne h q) (sumEdges_matching h q)
    (fun e ↦ f e.1*f e.2) (fun e _ ↦ by
      rw [abs_mul]
      exact (mul_le_mul (hf _) (hf _) (abs_nonneg _) (by norm_num)).trans_eq (by ring))
    K hmean hK t ht
  have hc : ((sumEdges h q).card:ℝ)≤h := by exact_mod_cast sumEdges_card_le h q
  exact he.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc (sq_nonneg _)))

lemma shifted_mgf (h : ℕ) (f : Fin h → ℝ) (hf : ∀ i, |f i|≤1)
    (K : α → α → ℝ) (hmean : kernelMean K=0) (hK : ∀ a b, |K a b|≤1)
    (q : ℕ) (t R : ℝ) (ht : |t|≤1) :
    mean (fun ω : Fin h → α ↦ Real.exp (t*colorFiber h f K ω q-t*R))≤
      Real.exp ((h:ℝ)*t^2-t*R) := by
  simp only [sub_eq_add_neg,Real.exp_add]
  have he : mean (fun ω : Fin h → α ↦ Real.exp (t*colorFiber h f K ω q)*Real.exp (-(t*R)))=
      Real.exp (-(t*R))*mean (fun ω : Fin h → α ↦ Real.exp (t*colorFiber h f K ω q)) := by
    conv_lhs => arg 1; ext ω; rw [mul_comm]
    rw [mean_const_mul]
  rw [he]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (colorFiber_mgf h f hf K hmean hK q t ht) (Real.exp_pos (-(t*R))).le

/-- A single coloring works for every listed kernel and every integer label
fiber. The list is finite; the fine field targets do not occur in the budget. -/
theorem exists_simultaneous_fibers (h : ℕ) (S : Finset κ)
    (f : κ → Fin h → ℝ) (hf : ∀ k∈S, ∀ i, |f k i|≤1)
    (K : κ → α → α → ℝ) (hmean : ∀ k∈S, kernelMean (K k)=0)
    (hK : ∀ k∈S, ∀ a b, |K k a b|≤1)
    (t R : ℝ) (ht : 0<t) (ht1 : t≤1)
    (hbudget : 4*(S.card:ℝ)*h*Real.exp ((h:ℝ)*t^2-t*R)<1) :
    ∃ ω : Fin h → α, ∀ k∈S, ∀ q<2*h, |colorFiber h (f k) (K k) ω q|<R := by
  let P (k : κ) (q : ℕ) (ω : Fin h → α) :=
    Real.exp (t*colorFiber h (f k) (K k) ω q-t*R)+
      Real.exp (-t*colorFiber h (f k) (K k) ω q-t*R)
  let total (ω : Fin h → α) := ∑ k∈S, ∑ q∈Finset.range (2*h), P k q ω
  have hp0 (k q ω) : 0≤P k q ω := by dsimp [P]; positivity
  have hm (k : κ) (hk : k∈S) (q : ℕ) :
      mean (P k q)≤2*Real.exp ((h:ℝ)*t^2-t*R) := by
    have hp := shifted_mgf h (f k) (hf k hk) (K k) (hmean k hk) (hK k hk) q t R
      (by rwa [abs_of_pos ht])
    have hn := shifted_mgf h (f k) (hf k hk) (K k) (hmean k hk) (hK k hk) q (-t) (-R)
      (by rw [abs_neg,abs_of_pos ht]; exact ht1)
    simp only [neg_sq,neg_mul_neg] at hn
    change mean (fun ω ↦ Real.exp (t*colorFiber h (f k) (K k) ω q-t*R)+
      Real.exp (-t*colorFiber h (f k) (K k) ω q-t*R))≤_
    rw [mean_add]
    linarith
  have htot : mean total<1 := by
    unfold total
    rw [mean_sum]
    simp_rw [mean_sum]
    calc
      _ ≤ ∑ k∈S, ∑ _q∈Finset.range (2*h), 2*Real.exp ((h:ℝ)*t^2-t*R) :=
        Finset.sum_le_sum (fun k hk ↦ Finset.sum_le_sum (fun q _ ↦ hm k hk q))
      _ = 4*(S.card:ℝ)*h*Real.exp ((h:ℝ)*t^2-t*R) := by
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
        ring
      _ < 1 := hbudget
  obtain ⟨ω,hω⟩ := exists_lt_of_mean_lt total 1 htot
  refine ⟨ω,fun k hk q hq ↦ ?_⟩
  have hrow : P k q ω≤total ω := by
    apply le_trans (Finset.single_le_sum (fun j _ ↦ hp0 k j ω) (Finset.mem_range.mpr hq))
    exact Finset.single_le_sum (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ hp0 i j ω)) hk
  have hp : Real.exp (t*colorFiber h (f k) (K k) ω q-t*R)<1 :=
    (le_add_of_nonneg_right (Real.exp_pos _).le).trans_lt (hrow.trans_lt hω)
  have hn : Real.exp (-t*colorFiber h (f k) (K k) ω q-t*R)<1 :=
    (le_add_of_nonneg_left (Real.exp_pos _).le).trans_lt (hrow.trans_lt hω)
  have hp' := Real.exp_lt_one_iff.mp hp
  have hn' := Real.exp_lt_one_iff.mp hn
  rw [abs_lt]
  constructor <;> nlinarith

/-- Ordered energy includes both orientations and its diagonal. -/
theorem exists_simultaneous_ordered_energy (h : ℕ) (S : Finset κ)
    (f : κ → Fin h → ℝ) (hf : ∀ k∈S, ∀ i, (f k i)^2=1)
    (K : κ → α → α → ℝ) (hmean : ∀ k∈S, kernelMean (K k)=0)
    (hK : ∀ k∈S, ∀ a b, |K k a b|≤1)
    (hsym : ∀ k∈S, ∀ a b, K k a b=K k b a)
    (t R : ℝ) (ht : 0<t) (ht1 : t≤1) (_hR : 0≤R)
    (hbudget : 4*(S.card:ℝ)*h*Real.exp ((h:ℝ)*t^2-t*R)<1) :
    ∃ ω : Fin h → α, ∀ k∈S,
      orderedEnergy h (fun i j ↦ (f k i*f k j)*K k (ω i) (ω j))≤(h:ℝ)*(16*R^2+2) := by
  have hfabs (k : κ) (hk : k∈S) (i : Fin h) : |f k i|≤1 := by
    nlinarith only [hf k hk i,sq_abs (f k i),abs_nonneg (f k i)]
  obtain ⟨ω,hω⟩ := exists_simultaneous_fibers h S f hfabs K hmean hK t R ht ht1 hbudget
  refine ⟨ω,fun k hk ↦ ?_⟩
  have he := orderedColorEnergy_le h (f k) (hf k hk) (K k) (hsym k hk) ω
  have hmass : colorEnergy h (f k) (K k) ω≤2*(h:ℝ)*R^2 := by
    unfold colorEnergy
    calc
      _ ≤ ∑ _q∈Finset.range (2*h), R^2 := by
        apply Finset.sum_le_sum
        intro q hq
        have hbound := (hω k hk q (Finset.mem_range.mp hq)).le
        nlinarith only [hbound,abs_nonneg (colorFiber h (f k) (K k) ω q),
          sq_abs (colorFiber h (f k) (K k) ω q)]
      _ = _ := by simp [Nat.cast_mul]
  have hdiag : (∑ i : Fin h, (K k (ω i) (ω i))^2)≤(h:ℝ) := by
    calc
      _ ≤ ∑ _i : Fin h, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hb := hK k hk (ω i) (ω i)
        nlinarith only [hb,abs_nonneg (K k (ω i) (ω i)),sq_abs (K k (ω i) (ω i))]
      _ = _ := by simp
  nlinarith only [he,hmass,hdiag]

end Erdos66ExponentialColorSelection
