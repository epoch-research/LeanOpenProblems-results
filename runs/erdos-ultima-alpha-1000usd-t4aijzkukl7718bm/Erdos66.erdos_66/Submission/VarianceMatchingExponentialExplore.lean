import Submission.LogarithmicColorBudgetExplore

/-! Finite matching MGFs retaining centered second moments, together with
explicit Bernstein parameters. This contains no infinite selection claim. -/
namespace Erdos66VarianceMatchingExponential
open Erdos66UniformSelection Erdos66UniformColorMoments Erdos66MatchingColorExponential
  Erdos66FixedPatternColorEnergy Erdos66ExponentialColorSelection
open scoped Classical
set_option maxHeartbeats 3000000

variable {γ : Type*} [Fintype γ] [Nonempty γ]

lemma mean_exp_variance (X : γ → ℝ) (hmean : mean X=0)
    (M V : ℝ) (hX : ∀ x, |X x|≤M) (hV : mean (fun x ↦ (X x)^2)≤V)
    (t : ℝ) (ht : |t| *M≤1) :
    mean (fun x ↦ Real.exp (t*X x))≤Real.exp (t^2*V) := by
  have hpt (x : γ) : Real.exp (t*X x)≤1+t*X x+t^2*(X x)^2 := by
    have hx : |t*X x|≤1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hX x) (abs_nonneg t)).trans ht
    have he := (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le hx)
    nlinarith only [he]
  have hm := mean_mono _ _ hpt
  simp only [mean_add,mean_const,mean_const_mul,hmean,mul_zero,add_zero] at hm
  have hv := mul_le_mul_of_nonneg_left hV (sq_nonneg t)
  exact hm.trans ((by linarith : 1+t^2*mean (fun x ↦ (X x)^2)≤1+t^2*V).trans
    (by linarith [Real.add_one_le_exp (t^2*V)]))

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype α] [Nonempty α] [DecidableEq α]

/-- For fixed unit-modulus signs, the MGF retains the actual pair-kernel
second moment. It needs no symmetry and has no color-cardinality factor. -/
theorem matching_variance_mgf (S : Finset (ι×ι))
    (hne : ∀ e∈S, e.1≠e.2)
    (hdis : (S:Set (ι×ι)).Pairwise
      (fun e d ↦ Disjoint ({e.1,e.2}:Set ι) ({d.1,d.2}:Set ι)))
    (v : ι×ι → ℝ) (hv : ∀ e∈S, (v e)^2=1)
    (K : α → α → ℝ) (hmean : kernelMean K=0)
    (M V : ℝ) (hK : ∀ a b, |K a b|≤M)
    (hV : kernelMean (fun a b ↦ (K a b)^2)≤V)
    (t : ℝ) (ht : |t| *M≤1) :
    mean (fun ω : ι → α ↦ Real.exp (t*∑ e∈S, v e*K (ω e.1) (ω e.2)))≤
      Real.exp ((S.card:ℝ)*t^2*V) := by
  rw [matching_exp_factorization S hdis]
  have hpt (e : ι×ι) (he : e∈S) :
      mean (fun ω : ι → α ↦ Real.exp (t*(v e*K (ω e.1) (ω e.2))))≤Real.exp (t^2*V) := by
    apply mean_exp_variance _ _ M V _ _ t ht
    · rw [mean_const_mul,mean_pair_kernel e.1 e.2 (hne e he),hmean,mul_zero]
    · intro ω
      have habs : |v e|=1 := by nlinarith only [hv e he,sq_abs (v e),abs_nonneg (v e)]
      rw [abs_mul,habs,one_mul]
      exact hK _ _
    · simp only [mul_pow,hv e he,one_mul]
      rwa [mean_pair_sq e.1 e.2 (hne e he)]
  calc
    _ ≤ ∏ _e∈S, Real.exp (t^2*V) := by
      apply Finset.prod_le_prod
      · intro e he
        exact div_nonneg (Finset.sum_nonneg (fun ω _ ↦ (Real.exp_pos _).le)) (Nat.cast_nonneg _)
      · exact hpt
    _ = _ := by rw [←Real.exp_sum]; simp [mul_assoc]

lemma colorFiber_variance_mgf (h : ℕ) (f : Fin h → ℝ) (hf : ∀ i, (f i)^2=1)
    (K : α → α → ℝ) (hmean : kernelMean K=0)
    (M V : ℝ) (hK : ∀ a b, |K a b|≤M) (hV0 : 0≤V)
    (hV : kernelMean (fun a b ↦ (K a b)^2)≤V)
    (q : ℕ) (t : ℝ) (ht : |t| *M≤1) :
    mean (fun ω : Fin h → α ↦ Real.exp (t*colorFiber h f K ω q))≤
      Real.exp ((h:ℝ)*t^2*V) := by
  have he := matching_variance_mgf (sumEdges h q) (sumEdges_ne h q) (sumEdges_matching h q)
    (fun e ↦ f e.1*f e.2) (fun e _ ↦ by simp only [mul_pow,hf,one_mul])
    K hmean M V hK hV t ht
  have hc : ((sumEdges h q).card:ℝ)≤h := by exact_mod_cast sumEdges_card_le h q
  exact he.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (sq_nonneg t)) hV0))

lemma colorFiber_variance_shifted (h : ℕ) (f : Fin h → ℝ) (hf : ∀ i, (f i)^2=1)
    (K : α → α → ℝ) (hmean : kernelMean K=0)
    (M V : ℝ) (hK : ∀ a b, |K a b|≤M) (hV0 : 0≤V)
    (hV : kernelMean (fun a b ↦ (K a b)^2)≤V)
    (q : ℕ) (t R : ℝ) (ht : |t| *M≤1) :
    mean (fun ω : Fin h → α ↦ Real.exp (t*colorFiber h f K ω q-t*R))≤
      Real.exp ((h:ℝ)*t^2*V-t*R) := by
  have he (ω : Fin h → α) : Real.exp (t*colorFiber h f K ω q-t*R)=
      Real.exp (-(t*R))*Real.exp (t*colorFiber h f K ω q) := by
    rw [←Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [mean_const_mul]
  have hm := mul_le_mul_of_nonneg_left
    (colorFiber_variance_mgf h f hf K hmean M V hK hV0 hV q t ht)
    (Real.exp_pos (-(t*R))).le
  exact hm.trans_eq (by rw [←Real.exp_add]; congr 1; ring)

noncomputable def bernsteinRadius (V M ell : ℝ) : ℝ := 2*(Real.sqrt (V*ell)+M*ell)
noncomputable def bernsteinTilt (V M ell : ℝ) : ℝ := ell/(Real.sqrt (V*ell)+M*ell)

/-- These parameters also work when the variance is zero. No inequality
ell<=h, or comparable size restriction, is required. -/
lemma bernstein_parameters (V M ell : ℝ) (hV : 0≤V) (hM : 0<M) (hell : 0<ell) :
    0<bernsteinTilt V M ell ∧
    bernsteinTilt V M ell*M≤1 ∧
    V*(bernsteinTilt V M ell)^2-bernsteinTilt V M ell*bernsteinRadius V M ell≤-ell ∧
    (bernsteinRadius V M ell)^2≤8*(V*ell+M^2*ell^2) := by
  let X := Real.sqrt (V*ell)
  let D := X+M*ell
  have hX : 0≤X := Real.sqrt_nonneg _
  have hX2 : X^2=V*ell := Real.sq_sqrt (mul_nonneg hV hell.le)
  have hD : 0<D := add_pos_of_nonneg_of_pos hX (mul_pos hM hell)
  have htilt : bernsteinTilt V M ell=ell/D := rfl
  have hrad : bernsteinRadius V M ell=2*D := rfl
  have hratio0 : 0≤X/D := div_nonneg hX hD.le
  have hratio : X/D≤1 := (div_le_one hD).mpr (by dsimp [D]; nlinarith only [mul_pos hM hell])
  have hsq : (X/D)^2≤1 := by nlinarith only [hratio0,hratio]
  have hvar : V*(ell/D)^2≤ell := by
    have he : V*(ell/D)^2=ell*(X/D)^2 := by
      field_simp
      nlinarith only [hX2]
    rw [he]
    exact (mul_le_mul_of_nonneg_left hsq hell.le).trans_eq (mul_one _)
  have hprod : (ell/D)*(2*D)=2*ell := by field_simp
  refine ⟨by rw [htilt]; exact div_pos hell hD,?_,?_,?_⟩
  · rw [htilt,div_mul_eq_mul_div]
    exact (div_le_one hD).mpr (by dsimp [D]; nlinarith only [hX])
  · rw [htilt,hrad,hprod]
    linarith
  · rw [hrad]
    dsimp [D]
    nlinarith only [hX2,sq_nonneg (X-M*ell)]

end Erdos66VarianceMatchingExponential
