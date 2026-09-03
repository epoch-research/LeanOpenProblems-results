import Submission.BernsteinBudgetParametersExplore
import Submission.UniversalCompleteAccuracyExplore

/-! Bernstein selection for complete field-label fibers. All diagonal
terms are retained; the exponential budget is over a finite kernel list. -/
namespace Erdos66CompleteBernsteinEnergy
open Erdos66UniformSelection Erdos66UniformColorMoments Erdos66CenteredColorSelection
  Erdos66VarianceMatchingExponential Erdos66VariableThresholdSelection
  Erdos66LogarithmicColorBudget Erdos66FiberColorEnergy
  Erdos66CompletePartitionColorTransfer Erdos66ParallelParabolaPartition
open scoped Classical
set_option maxHeartbeats 3000000
variable {α κ : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma edges_card_le {n : ℕ} (ρ : Fin n ≃ F) (q : F) :
    (edges n (fun i j ↦ ρ i+ρ j) q).card≤n := by
  have hinj : Set.InjOn Prod.fst (edges n (fun i j ↦ ρ i+ρ j) q : Set (Fin n×Fin n)) := by
    intro e he d hd h
    apply Prod.ext h
    apply ρ.injective
    have h1 := ((mem_edges _ q e).mp he).2
    have h2 := ((mem_edges _ q d).mp hd).2
    exact add_left_cancel (show ρ d.1+ρ e.2=ρ d.1+ρ d.2 by simpa [h] using h1.trans h2.symm)
  calc
    _ = ((edges n (fun i j ↦ ρ i+ρ j) q).image Prod.fst).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
    _ = n := Fintype.card_fin n

noncomputable def edgeSum {n : ℕ} (ρ : Fin n ≃ F) (K : α → α → ℝ)
    (ω : Fin n → α) (q : F) : ℝ :=
  ∑ e∈edges n (fun i j ↦ ρ i+ρ j) q, K (ω e.1) (ω e.2)

lemma edgeSum_mgf {n : ℕ} (ρ : Fin n ≃ F) (K : α → α → ℝ)
    (hmean : kernelMean K=0) (M V : ℝ) (hK : ∀ a b, |K a b|≤M) (hV0 : 0≤V)
    (hV : kernelMean (fun a b ↦ (K a b)^2)≤V)
    (q : F) (t : ℝ) (ht : |t| * M≤1) :
    mean (fun ω : Fin n → α ↦ Real.exp (t*edgeSum ρ K ω q))≤
      Real.exp ((n:ℝ)*t^2*V) := by
  have he := matching_variance_mgf (edges n (fun i j ↦ ρ i+ρ j) q)
    (fun e he ↦ ne_of_lt ((mem_edges _ q e).mp he).1)
    (edges_matching _ (labelSum_symm ρ) (labelSum_cancel ρ) q)
    (fun _ ↦ (1:ℝ)) (fun _ _ ↦ by norm_num) K hmean M V hK hV t ht
  simp only [one_mul] at he
  have hc : ((edges n (fun i j ↦ ρ i+ρ j) q).card:ℝ)≤n := by exact_mod_cast edges_card_le ρ q
  exact he.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (sq_nonneg t)) hV0))

lemma edgeSum_shifted {n : ℕ} (ρ : Fin n ≃ F) (K : α → α → ℝ)
    (hmean : kernelMean K=0) (M V : ℝ) (hK : ∀ a b, |K a b|≤M) (hV0 : 0≤V)
    (hV : kernelMean (fun a b ↦ (K a b)^2)≤V)
    (q : F) (t R : ℝ) (ht : |t| * M≤1) :
    mean (fun ω : Fin n → α ↦ Real.exp (t*edgeSum ρ K ω q-t*R))≤
      Real.exp ((n:ℝ)*t^2*V-t*R) := by
  have hid (ω : Fin n → α) : Real.exp (t*edgeSum ρ K ω q-t*R)=
      Real.exp (-t*R)*Real.exp (t*edgeSum ρ K ω q) := by
    rw [←Real.exp_add]; congr 1; ring
  simp_rw [hid]
  rw [mean_const_mul]
  exact (mul_le_mul_of_nonneg_left (edgeSum_mgf ρ K hmean M V hK hV0 hV q t ht)
    (Real.exp_pos _).le).trans_eq (by rw [←Real.exp_add]; congr 1; ring)

noncomputable def completeEnergyBound (n m : ℕ) (V M : ℝ) : ℝ :=
  64*(n:ℝ)^2*V*listLog n m+64*n*M^2*(listLog n m)^2+2*n*M^2

/-- A complete label partition costs n rather than 2n matching fibers. -/
theorem exists_complete_bernstein_energy {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2)
    (S : Finset κ) (K : κ → α → α → ℝ) (hsym : ∀ k∈S, ∀ a b, K k a b=K k b a)
    (M V : κ → ℝ) (hM : ∀ k∈S, 0<M k) (hV0 : ∀ k∈S, 0≤V k)
    (hK : ∀ k∈S, ∀ a b, |centeredKernel (K k) a b|≤M k)
    (hV : ∀ k∈S, colorVariance (K k)≤V k) :
    ∃ ω : Fin n → α, ∀ k∈S,
      colorEnergy ρ (K k) ω≤completeEnergyBound n S.card (V k) (M k) := by
  let ell := listLog n S.card
  let R (k : κ) := bernsteinRadius ((n:ℝ)*V k) (M k) ell
  let t (k : κ) := bernsteinTilt ((n:ℝ)*V k) (M k) ell
  have hp (k : κ) (hk : k∈S) := bernstein_parameters ((n:ℝ)*V k) (M k) ell
    (mul_nonneg (Nat.cast_nonneg _) (hV0 k hk)) (hM k hk) (listLog_pos n S.card)
  have hplus (k : κ) (hk : k∈S) (q : F) (hq : q∈(Finset.univ:Finset F)) :
      mean (fun ω : Fin n → α ↦ Real.exp (t k*edgeSum ρ (centeredKernel (K k)) ω q-t k*R k))≤
        Real.exp (-ell) := by
    have he := edgeSum_shifted ρ (centeredKernel (K k)) (kernelMean_centered (K k))
      (M k) (V k) (hK k hk) (hV0 k hk) (hV k hk) q (t k) (R k)
      (by rw [abs_of_pos (hp k hk).1]; exact (hp k hk).2.1)
    exact he.trans (Real.exp_le_exp.mpr (by
      have hh := (hp k hk).2.2.1
      change ((n:ℝ)*V k)*(t k)^2-t k*R k≤-ell at hh
      nlinarith only [hh]))
  have hminus (k : κ) (hk : k∈S) (q : F) (hq : q∈(Finset.univ:Finset F)) :
      mean (fun ω : Fin n → α ↦ Real.exp (-t k*edgeSum ρ (centeredKernel (K k)) ω q-t k*R k))≤
        Real.exp (-ell) := by
    have he := edgeSum_shifted ρ (centeredKernel (K k)) (kernelMean_centered (K k))
      (M k) (V k) (hK k hk) (hV0 k hk) (hV k hk) q (-t k) (-R k)
      (by rw [abs_neg,abs_of_pos (hp k hk).1]; exact (hp k hk).2.1)
    simp only [neg_sq,neg_mul_neg] at he
    exact he.trans (Real.exp_le_exp.mpr (by
      have hh := (hp k hk).2.2.1
      change ((n:ℝ)*V k)*(t k)^2-t k*R k≤-ell at hh
      nlinarith only [hh]))
  have hcard : Fintype.card F=n := by simpa using (Fintype.card_congr ρ).symm
  have hb : 2*(S.card:ℝ)*((Finset.univ:Finset F).card:ℝ)*Real.exp (-ell)<1 := by
    rw [Finset.card_univ,hcard]
    have he := exponential_list_budget n S.card
    have h0 : 0≤(S.card:ℝ)*n*Real.exp (-ell) := by positivity
    change 4*(S.card:ℝ)*n*Real.exp (-ell)<1 at he
    nlinarith only [h0,he]
  obtain ⟨ω,hω⟩ := exists_variable_thresholds S Finset.univ
    (fun k q ω ↦ edgeSum ρ (centeredKernel (K k)) ω q) t R ell
    (fun k hk ↦ (hp k hk).1) hplus hminus hb
  refine ⟨ω,fun k hk ↦ ?_⟩
  have he := energy_le_edge_diag (fun i j ↦ ρ i+ρ j) (labelSum_symm ρ)
    (labelSum_diag_injective ρ hF) (fun i j ↦ centeredKernel (K k) (ω i) (ω j))
    (fun i j ↦ by simp only [centeredKernel,hsym k hk])
  have hsum : (∑ q : F, (edgeSum ρ (centeredKernel (K k)) ω q)^2)≤(n:ℝ)*(R k)^2 := by
    calc
      _ ≤ ∑ _q : F, (R k)^2 := Finset.sum_le_sum (fun q _ ↦ by
        have hh := hω k hk q (Finset.mem_univ _)
        nlinarith only [sq_abs (edgeSum ρ (centeredKernel (K k)) ω q),abs_nonneg
          (edgeSum ρ (centeredKernel (K k)) ω q),hh])
      _ = _ := by simp [hcard]
  have hdiag : (∑ i : Fin n, (centeredKernel (K k) (ω i) (ω i))^2)≤(n:ℝ)*(M k)^2 := by
    calc
      _ ≤ ∑ _i : Fin n, (M k)^2 := Finset.sum_le_sum (fun i _ ↦ by
        have hh := hK k hk (ω i) (ω i)
        nlinarith only [sq_abs (centeredKernel (K k) (ω i) (ω i)),
          abs_nonneg (centeredKernel (K k) (ω i) (ω i)),hh])
      _ = _ := by simp
  have hr := mul_le_mul_of_nonneg_left (hp k hk).2.2.2 (show (0:ℝ)≤8*n by positivity)
  change 8*(n:ℝ)*(R k)^2≤8*n*(8*(((n:ℝ)*V k)*ell+(M k)^2*ell^2)) at hr
  change colorEnergy ρ (K k) ω≤8*(∑ q : F, (edgeSum ρ (centeredKernel (K k)) ω q)^2)+
    2*(∑ i : Fin n, (centeredKernel (K k) (ω i) (ω i))^2) at he
  unfold completeEnergyBound
  change _≤64*(n:ℝ)^2*V k*ell+64*n*(M k)^2*ell^2+2*n*(M k)^2
  nlinarith only [he,hsum,hdiag,hr]

end Erdos66CompleteBernsteinEnergy
