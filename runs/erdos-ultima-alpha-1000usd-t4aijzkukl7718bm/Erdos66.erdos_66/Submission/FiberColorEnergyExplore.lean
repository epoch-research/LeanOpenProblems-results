import Submission.CenteredColorSelectionExplore

/-! Centered color-kernel energy on symmetric cancellative label fibers.
This includes cyclic field-label sums, not only integer sums. -/
namespace Erdos66FiberColorEnergy
open Erdos66UniformSelection Erdos66UniformColorMoments Erdos66MatchingColorMoments
  Erdos66FixedPatternColorEnergy Erdos66CenteredColorSelection
open scoped Classical
set_option maxHeartbeats 2600000

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

noncomputable def edges (h : ℕ) (σ : Fin h → Fin h → κ) (q : κ) : Finset (Fin h×Fin h) :=
  Finset.univ.filter (fun e ↦ e.1<e.2 ∧ σ e.1 e.2=q)

lemma mem_edges {h : ℕ} (σ : Fin h → Fin h → κ) (q : κ) (e : Fin h×Fin h) :
    e∈edges h σ q ↔ e.1<e.2 ∧ σ e.1 e.2=q := by simp [edges]

lemma edges_matching {h : ℕ} (σ : Fin h → Fin h → κ)
    (hs : ∀ i j, σ i j=σ j i) (hc : ∀ i j k, σ i j=σ i k → j=k) (q : κ) :
    (edges h σ q:Set (Fin h×Fin h)).Pairwise
      (fun e d ↦ Disjoint ({e.1,e.2}:Set (Fin h)) ({d.1,d.2}:Set (Fin h))) := by
  intro e he d hd hed
  obtain ⟨helt,heq⟩ := (mem_edges σ q e).mp he
  obtain ⟨hdlt,hdq⟩ := (mem_edges σ q d).mp hd
  have hsum : σ e.1 e.2=σ d.1 d.2 := heq.trans hdq.symm
  have hcase (h₁ : e.1=d.1) : e=d := by
    have h₂ : e.2=d.2 := hc d.1 e.2 d.2 (by rwa [h₁] at hsum)
    exact Prod.ext h₁ h₂
  have hswap (h₁ : e.1=d.2) : False := by
    have h₂ : e.2=d.1 := hc d.2 e.2 d.1 (by rwa [h₁,hs d.1 d.2] at hsum)
    rw [h₁,h₂] at helt
    exact (not_lt_of_ge (le_of_lt hdlt)) helt
  apply Set.disjoint_left.mpr
  intro x hx hy
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hed (hcase (hx.symm.trans hy))
  · exact hswap (hx.symm.trans hy)
  · have h₂ : e.2=d.1 := hx.symm.trans hy
    have h₁ : e.1=d.2 := hc d.1 e.1 d.2 (by
      calc
        σ d.1 e.1=σ e.2 e.1 := by rw [h₂]
        _=σ e.1 e.2 := hs _ _
        _=σ d.1 d.2 := hsum)
    exact hswap h₁
  · have h₂ : e.2=d.2 := hx.symm.trans hy
    have h₁ : e.1=d.1 := hc d.2 e.1 d.1 (by
      calc
        σ d.2 e.1=σ e.2 e.1 := by rw [h₂]
        _=σ e.1 e.2 := hs _ _
        _=σ d.1 d.2 := hsum
        _=σ d.2 d.1 := hs _ _)
    exact hed (hcase h₁)

noncomputable def fiber (h : ℕ) (σ : Fin h → Fin h → κ) (V : Fin h → Fin h → ℝ) (q : κ) : ℝ :=
  ∑ e : Fin h×Fin h, if σ e.1 e.2=q then V e.1 e.2 else 0

noncomputable def diagFiber (h : ℕ) (σ : Fin h → Fin h → κ) (V : Fin h → Fin h → ℝ) (q : κ) : ℝ :=
  ∑ i : Fin h, if σ i i=q then V i i else 0

noncomputable def energy (h : ℕ) (σ : Fin h → Fin h → κ) (V : Fin h → Fin h → ℝ) : ℝ :=
  ∑ q : κ, (fiber h σ V q)^2

lemma fiber_split {h : ℕ} (σ : Fin h → Fin h → κ) (hs : ∀ i j, σ i j=σ j i)
    (V : Fin h → Fin h → ℝ) (hV : ∀ i j, V i j=V j i) (q : κ) :
    fiber h σ V q=2*(∑ e∈edges h σ q, V e.1 e.2)+diagFiber h σ V q := by
  have he (e : Fin h×Fin h) : (if σ e.1 e.2=q then V e.1 e.2 else 0)=
      (if e.1<e.2 ∧ σ e.1 e.2=q then V e.1 e.2 else 0)+
      (if e.2<e.1 ∧ σ e.2 e.1=q then V e.2 e.1 else 0)+
      (if e.2=e.1 then (if σ e.1 e.1=q then V e.1 e.1 else 0) else 0) := by
    rcases lt_trichotomy e.1 e.2 with hl | hl | hl
    · simp [hl,not_lt_of_ge (le_of_lt hl),(ne_of_lt hl).symm]
    · simp [hl]
    · simp [hl,not_lt_of_ge (le_of_lt hl),ne_of_lt hl,hs,hV]
  have hswap := Equiv.sum_comp (Equiv.prodComm (Fin h) (Fin h))
    (fun e : Fin h×Fin h ↦ if e.1<e.2 ∧ σ e.1 e.2=q then V e.1 e.2 else 0)
  simp only [Equiv.prodComm_apply,Prod.fst_swap,Prod.snd_swap] at hswap
  unfold fiber
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,hswap]
  simp only [edges,Finset.sum_filter,diagFiber,Fintype.sum_prod_type,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]
  ring

lemma diagFiber_sq {h : ℕ} (σ : Fin h → Fin h → κ)
    (hd : Function.Injective (fun i ↦ σ i i)) (V : Fin h → Fin h → ℝ) (q : κ) :
    (diagFiber h σ V q)^2=diagFiber h σ (fun i j ↦ (V i j)^2) q := by
  by_cases he : ∃ i, σ i i=q
  · obtain ⟨i,hi⟩ := he
    have hu (j : Fin h) : σ j j=q ↔ j=i := by
      constructor
      · intro hj; exact hd (hj.trans hi.symm)
      · rintro rfl; exact hi
    simp [diagFiber,hu]
  · have hu (i : Fin h) : ¬σ i i=q := by intro hi; exact he ⟨i,hi⟩
    simp [diagFiber,hu]

lemma diag_energy {h : ℕ} (σ : Fin h → Fin h → κ)
    (hd : Function.Injective (fun i ↦ σ i i)) (V : Fin h → Fin h → ℝ) :
    (∑ q : κ, (diagFiber h σ V q)^2)=∑ i : Fin h, (V i i)^2 := by
  simp_rw [diagFiber_sq σ hd]
  unfold diagFiber
  rw [Finset.sum_comm]
  simp

lemma edge_mass_le {h : ℕ} (σ : Fin h → Fin h → κ) :
    (∑ q : κ, ((edges h σ q).card:ℝ))≤(h:ℝ)^2 := by
  simp only [edges,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _e : Fin h×Fin h, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      by_cases he' : e.1<e.2 <;> simp [he']
    _ = _ := by simp [pow_two]

lemma sum_fiber_mul {h : ℕ} (σ : Fin h → Fin h → κ)
    (V : Fin h → Fin h → ℝ) (ψ : κ → ℝ) :
    (∑ q : κ, fiber h σ V q*ψ q)=∑ i : Fin h, ∑ j : Fin h, V i j*ψ (σ i j) := by
  unfold fiber
  simp only [Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true,Fintype.sum_prod_type]

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

lemma mean_centered_edge_sq {h : ℕ} (σ : Fin h → Fin h → κ)
    (hs : ∀ i j, σ i j=σ j i) (hc : ∀ i j k, σ i j=σ i k → j=k)
    (K : α → α → ℝ) (q : κ) :
    mean (fun ω : Fin h → α ↦ (∑ e∈edges h σ q, centeredKernel K (ω e.1) (ω e.2))^2)=
      colorVariance K*((edges h σ q).card:ℝ) := by
  have he := matching_kernel_second_moment (edges h σ q)
    (fun e he ↦ ne_of_lt ((mem_edges σ q e).mp he).1) (edges_matching σ hs hc q)
    (fun _ ↦ (1:ℝ)) (centeredKernel K)
  rw [kernelMean_centered] at he
  simpa only [colorVariance,one_mul,zero_pow (by decide : 2≠0),zero_mul,zero_add,sub_zero,
    one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using he

lemma energy_le_edge_diag {h : ℕ} (σ : Fin h → Fin h → κ)
    (hs : ∀ i j, σ i j=σ j i) (hd : Function.Injective (fun i ↦ σ i i))
    (V : Fin h → Fin h → ℝ) (hV : ∀ i j, V i j=V j i) :
    energy h σ V ≤ 8*(∑ q : κ, (∑ e∈edges h σ q, V e.1 e.2)^2)+
      2*(∑ i : Fin h, (V i i)^2) := by
  rw [←diag_energy σ hd V]
  unfold energy
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q hq
  rw [fiber_split σ hs V hV q]
  nlinarith [sq_nonneg (2*(∑ e∈edges h σ q, V e.1 e.2)-diagFiber h σ V q)]

/-- The centered budget has no residual old-pattern energy. All labels
participate, and all diagonal contributions are retained. -/
theorem mean_centered_energy_le {h : ℕ} (σ : Fin h → Fin h → κ)
    (hs : ∀ i j, σ i j=σ j i) (hc : ∀ i j k, σ i j=σ i k → j=k)
    (hd : Function.Injective (fun i ↦ σ i i))
    (K : α → α → ℝ) (hK : ∀ x y, K x y=K y x) :
    mean (fun ω : Fin h → α ↦ energy h σ (fun i j ↦ centeredKernel K (ω i) (ω j))) ≤
      8*(h:ℝ)^2*colorVariance K+2*(h:ℝ)*diagonalCenteredSecond K := by
  have hm := mean_mono _ _ (fun ω : Fin h → α ↦ energy_le_edge_diag σ hs hd
    (fun i j ↦ centeredKernel K (ω i) (ω j))
    (fun i j ↦ by dsimp [centeredKernel]; rw [hK]))
  rw [mean_add,mean_const_mul,mean_const_mul,mean_sum,mean_sum] at hm
  simp_rw [mean_centered_edge_sq σ hs hc K] at hm
  have hdiag (i : Fin h) : mean (fun ω : Fin h → α ↦ (centeredKernel K (ω i) (ω i))^2)=
      diagonalCenteredSecond K := mean_eval i (fun x ↦ (centeredKernel K x x)^2)
  simp_rw [hdiag] at hm
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hm
  rw [←Finset.mul_sum] at hm
  have hvar : 0≤colorVariance K := kernelVariance_nonneg K
  have hmass := mul_le_mul_of_nonneg_left (edge_mass_le σ) hvar
  nlinarith only [hm,hmass]

end Erdos66FiberColorEnergy
