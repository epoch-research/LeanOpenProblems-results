import Submission.PairedSelectionBridge

/-!
A two-branch retention pool and its ordered-cost endpoint comparison.
These are conditional finite-kernel tools, not an odd covering obstruction.
-/
namespace Erdos7BalancedBranchPool
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

lemma ordered_endpoint (f g : ℝ → ℝ)
    (hg : ConvexOn ℝ Set.univ g) (hfg : Monotone (fun t => f t-g t))
    (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    f x+g y ≤ f (x+y-1)+g 1 := by
  have he := Erdos7PairedSelectionBridge.endpoint_pair g hg 1 x y hx hy
  have hm := hfg (show x ≤ x+y-1 by linarith)
  linarith

lemma weighted_convex {I : Type*} [Fintype I]
    (w t : I → ℝ) (hw : ∀ i,0 ≤ w i) (φ : ℝ → ℝ)
    (hφ : ConvexOn ℝ Set.univ φ) :
    ConvexOn ℝ Set.univ (fun x => ∑ i,w i*φ (t i*x)) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  calc
    (∑ i,w i*φ (t i*(a*x+b*y))) ≤
        ∑ i,w i*(a*φ (t i*x)+b*φ (t i*y)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      have h := hφ.2 (Set.mem_univ (t i*x)) (Set.mem_univ (t i*y)) ha hb hab
      simp only [smul_eq_mul] at h
      have he : t i*(a*x+b*y)=a*(t i*x)+b*(t i*y) := by ring
      rw [he]
      exact h
    _ = a*(∑ i,w i*φ (t i*x))+b*(∑ i,w i*φ (t i*y)) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma weighted_gap_mono {I : Type*} [Fintype I]
    (w v t : I → ℝ) (hvw : ∀ i,v i ≤ w i) (ht : ∀ i,0 ≤ t i)
    (φ : ℝ → ℝ) (hmφ : Monotone φ) :
    Monotone (fun x => (∑ i,w i*φ (t i*x))-(∑ i,v i*φ (t i*x))) := by
  intro x y hxy
  simp only [← Finset.sum_sub_distrib,← sub_mul]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (hmφ (mul_le_mul_of_nonneg_left hxy (ht i)))
    (sub_nonneg.mpr (hvw i))

/-- With ordered atom weights, put the larger old load in the larger kernel.
This replacement is made before applying the coordinate scales. -/
theorem weighted_endpoint {I : Type*} [Fintype I]
    (w v t : I → ℝ) (hv : ∀ i,0 ≤ v i) (hvw : ∀ i,v i ≤ w i)
    (ht : ∀ i,0 ≤ t i) (φ : ℝ → ℝ)
    (hcφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ)
    (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    (∑ i,w i*φ (t i*x))+(∑ i,v i*φ (t i*y)) ≤
      (∑ i,w i*φ (t i*(x+y-1)))+(∑ i,v i*φ (t i)) := by
  simpa only [mul_one] using ordered_endpoint
    (fun x => ∑ i,w i*φ (t i*x)) (fun x => ∑ i,v i*φ (t i*x))
    (weighted_convex v t hv φ hcφ) (weighted_gap_mono w v t hvw ht φ hmφ)
    x y hx hy


lemma min_window_identity (a b h : ℝ) (hab : a ≤ b) :
    min h b-min h a=min (max 0 (h-a)) (b-a) := by
  by_cases hha : h ≤ a
  · rw [min_eq_left hha,min_eq_left (hha.trans hab)]
    rw [max_eq_left (by linarith : h-a ≤ 0),min_eq_left (by linarith : 0 ≤ b-a)]
    ring
  · have hah : a ≤ h := le_of_not_ge hha
    rw [min_eq_right hah,max_eq_right (by linarith : 0 ≤ h-a)]
    by_cases hhb : h ≤ b
    · rw [min_eq_left hhb,min_eq_left (by linarith : h-a ≤ b-a)]
    · rw [min_eq_right (le_of_not_ge hhb),min_eq_right (by linarith : b-a ≤ h-a)]

lemma min_window_mono (a b : ℝ) (hab : a ≤ b) :
    Monotone (fun h => min h b-min h a) := by
  intro h k hhk
  dsimp only
  rw [min_window_identity a b h hab,min_window_identity a b k hab]
  exact min_le_min (max_le_max le_rfl (sub_le_sub_right hhk a)) le_rfl

noncomputable def cappedAtom (q : ℕ → ℝ) (h : ℝ) : ℕ → ℝ
  | 0 => h-min h (q 0)
  | j+1 => min h (q j)-min h (q (j+1))

lemma cappedAtom_nonneg (q : ℕ → ℝ) (hq : Antitone q) (h : ℝ) (j : ℕ) :
    0 ≤ cappedAtom q h j := by
  cases j with
  | zero => exact sub_nonneg.mpr (min_le_left _ _)
  | succ j =>
    exact sub_nonneg.mpr (min_le_min le_rfl (hq (Nat.le_succ j)))

lemma cappedAtom_mono (q : ℕ → ℝ) (hq : Antitone q) (j : ℕ) :
    Monotone (fun h => cappedAtom q h j) := by
  cases j with
  | zero =>
    intro h k hhk
    dsimp only [cappedAtom]
    by_cases hh : h ≤ q 0
    · rw [min_eq_left hh,sub_self]
      exact sub_nonneg.mpr (min_le_left _ _)
    · rw [min_eq_right (le_of_not_ge hh),min_eq_right ((le_of_not_ge hh).trans hhk)]
      linarith
  | succ j => exact min_window_mono (q (j+1)) (q j) (hq (Nat.le_succ j))

/-- The finite capped geometric-law atoms are ordered as retained mass grows,
so their old-load endpoint replacement is valid for every convex monotone test. -/
theorem capped_endpoint (q : ℕ → ℝ) (hq : Antitone q) (D : ℕ)
    (u v : ℝ) (hvu : v ≤ u) (φ : ℝ → ℝ)
    (hcφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ)
    (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    (∑ j : Fin (D+1),cappedAtom q u j*φ ((j.val+1)*x))+
        (∑ j : Fin (D+1),cappedAtom q v j*φ ((j.val+1)*y)) ≤
      (∑ j : Fin (D+1),cappedAtom q u j*φ ((j.val+1)*(x+y-1)))+
        (∑ j : Fin (D+1),cappedAtom q v j*φ (j.val+1)) := by
  exact weighted_endpoint (fun j : Fin (D+1) => cappedAtom q u j)
    (fun j => cappedAtom q v j) (fun j => (j.val:ℝ)+1)
    (fun j => cappedAtom_nonneg q hq v j)
    (fun j => cappedAtom_mono q hq j hvu) (fun j => by positivity)
    φ hcφ hmφ x y hx hy

lemma balanced_ordered (a b h : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hh : 0 ≤ h) (hhcap : h ≤ a+b) :
    let u := min a (h/2)
    let v := h-u
    0 ≤ u ∧ 0 ≤ v ∧ u ≤ a ∧ v ≤ b ∧ u+v=h ∧ u ≤ v ∧
      min u v=min (h/2) (min a b) := by
  dsimp only
  have hu0 : 0 ≤ min a (h/2) := le_min ha (by linarith)
  have huh : min a (h/2) ≤ h/2 := min_le_right _ _
  have hua : min a (h/2) ≤ a := min_le_left _ _
  have huv : min a (h/2) ≤ h-min a (h/2) := by linarith
  refine ⟨hu0,by linarith,hua,?_,by ring,huv,?_⟩
  · by_cases hh' : a ≤ h/2
    · rw [min_eq_left hh']; linarith
    · rw [min_eq_right (le_of_not_ge hh')]; linarith
  · rw [min_eq_left huv,min_eq_left hab,min_comm]

/-- Two capacities can be pooled. Their retained masses can be made as equal
as the smaller capacity permits. This is not an independence assertion. -/
theorem exists_balanced_masses (a b h : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hh : 0 ≤ h) (hhcap : h ≤ a+b) :
    ∃ u v : ℝ,0 ≤ u ∧ 0 ≤ v ∧ u ≤ a ∧ v ≤ b ∧ u+v=h ∧
      min u v=min (h/2) (min a b) := by
  by_cases hab : a ≤ b
  · obtain ⟨hu,hv,hua,hvb,he,_,hm⟩ := balanced_ordered a b h ha hab hh hhcap
    exact ⟨min a (h/2),h-min a (h/2),hu,hv,hua,hvb,he,hm⟩
  · have hba : b ≤ a := le_of_not_ge hab
    obtain ⟨hu,hv,hub,hva,he,_,hm⟩ := balanced_ordered b a h hb hba hh (by linarith)
    refine ⟨h-min b (h/2),min b (h/2),hv,hu,hva,hub,by linarith,?_⟩
    simpa only [min_comm] using hm

/-- Separate conditional kernels may supply one shared retained mass. The
cap is relative to each branch's own law; no joint product law is used. -/
theorem exists_pool {Ω A B : Type*} [Fintype A] [Fintype B]
    (μ : Ω → ℝ) (hμ : ∀ x,0 ≤ μ x)
    (ρ : A → ℝ) (hρ : ∀ a,0 ≤ ρ a) (hmρ : (∑ a,ρ a)=1)
    (σ : B → ℝ) (hσ : ∀ b,0 ≤ σ b) (hmσ : (∑ b,σ b)=1)
    (P : Ω → A → Prop) (Q : Ω → B → Prop)
    (u v : Ω → ℝ) (hu : ∀ x,0 ≤ u x) (hv : ∀ x,0 ≤ v x)
    (c : ℝ) (hc : 0 ≤ c)
    (huc : ∀ x,u x ≤ c*(1-∑ a,if P x a then ρ a else 0))
    (hvc : ∀ x,v x ≤ c*(1-∑ b,if Q x b then σ b else 0)) :
    ∃ L : Ω → A → ℝ,∃ R : Ω → B → ℝ,
      (∀ x a,0 ≤ L x a ∧ L x a ≤ c*μ x*ρ a) ∧
      (∀ x b,0 ≤ R x b ∧ R x b ≤ c*μ x*σ b) ∧
      (∀ x a,P x a → L x a=0) ∧ (∀ x b,Q x b → R x b=0) ∧
      ∀ x,(∑ a,L x a)+(∑ b,R x b)=μ x*(u x+v x) := by
  classical
  obtain ⟨L,hL,hLc,hLP,hLm⟩ := Erdos7FiniteRetentionKernel.exists_retention_kernel
    μ hμ ρ hρ hmρ P u c hc hu huc
  obtain ⟨R,hR,hRc,hRQ,hRm⟩ := Erdos7FiniteRetentionKernel.exists_retention_kernel
    μ hμ σ hσ hmσ Q v c hc hv hvc
  refine ⟨L,R,fun x a => ⟨hL x a,hLc x a⟩,
    fun x b => ⟨hR x b,hRc x b⟩,hLP,hRQ,?_⟩
  intro x
  rw [hLm,hRm,mul_add]

#print axioms weighted_endpoint
#print axioms capped_endpoint
#print axioms exists_balanced_masses
#print axioms exists_pool
end Erdos7BalancedBranchPool
