import Submission.FixedPatternColorEnergyExplore

/-! Ordered label fibers, with the diagonal contribution retained. -/
namespace Erdos66OrderedColorEnergy
open Erdos66UniformSelection Erdos66UniformColorMoments Erdos66FixedPatternColorEnergy
open scoped Classical
set_option maxHeartbeats 2200000

noncomputable def orderedFiber (h : ℕ) (V : Fin h → Fin h → ℝ) (q : ℕ) : ℝ :=
  ∑ e : Fin h × Fin h, if e.1.val+e.2.val=q then V e.1 e.2 else 0

noncomputable def diagonalFiber (h : ℕ) (V : Fin h → Fin h → ℝ) (q : ℕ) : ℝ :=
  ∑ i : Fin h, if 2*i.val=q then V i i else 0

noncomputable def orderedEnergy (h : ℕ) (V : Fin h → Fin h → ℝ) : ℝ :=
  ∑ q∈Finset.range (2*h), (orderedFiber h V q)^2

lemma orderedFiber_split (h : ℕ) (V : Fin h → Fin h → ℝ)
    (hV : ∀ i j, V i j=V j i) (q : ℕ) :
    orderedFiber h V q=2*(∑ e∈sumEdges h q, V e.1 e.2)+diagonalFiber h V q := by
  have he (e : Fin h × Fin h) :
      (if e.1.val+e.2.val=q then V e.1 e.2 else 0)=
        (if e.1<e.2 ∧ e.1.val+e.2.val=q then V e.1 e.2 else 0)+
        (if e.2<e.1 ∧ e.2.val+e.1.val=q then V e.2 e.1 else 0)+
        (if e.2=e.1 then (if 2*e.1.val=q then V e.1 e.1 else 0) else 0) := by
    rcases lt_trichotomy e.1 e.2 with hl | hl | hl
    · have hn : ¬e.2<e.1 := not_lt_of_ge (le_of_lt hl)
      have hne : e.2≠e.1 := (ne_of_lt hl).symm
      simp [hl,hn,hne]
    · simp [hl,two_mul]
    · have hn : ¬e.1<e.2 := not_lt_of_ge (le_of_lt hl)
      have hne : e.2≠e.1 := ne_of_lt hl
      simp [hl,hn,hne,Nat.add_comm,hV]
  have hswap := Equiv.sum_comp (Equiv.prodComm (Fin h) (Fin h))
    (fun e : Fin h × Fin h ↦ if e.1<e.2 ∧ e.1.val+e.2.val=q then V e.1 e.2 else 0)
  simp only [Equiv.prodComm_apply,Prod.fst_swap,Prod.snd_swap] at hswap
  unfold orderedFiber
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,hswap]
  simp only [sumEdges,Finset.sum_filter,diagonalFiber,Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  ring

lemma diagonalFiber_sq (h : ℕ) (V : Fin h → Fin h → ℝ) (q : ℕ) :
    (diagonalFiber h V q)^2=diagonalFiber h (fun i j ↦ (V i j)^2) q := by
  by_cases he : ∃ i : Fin h, 2*i.val=q
  · obtain ⟨i,hi⟩ := he
    have hu (j : Fin h) : 2*j.val=q ↔ j=i := by
      constructor
      · intro hj; apply Fin.ext; omega
      · rintro rfl; exact hi
    simp [diagonalFiber,hu]
  · have hu (i : Fin h) : ¬2*i.val=q := by intro hi; exact he ⟨i,hi⟩
    simp [diagonalFiber,hu]

lemma sum_diagonalFiber (h : ℕ) (V : Fin h → Fin h → ℝ) :
    (∑ q∈Finset.range (2*h), diagonalFiber h V q)=∑ i : Fin h, V i i := by
  unfold diagonalFiber
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hm : 2*i.val∈Finset.range (2*h) := by simp only [Finset.mem_range]; omega
  simp [hm]

lemma diagonalEnergy (h : ℕ) (V : Fin h → Fin h → ℝ) :
    (∑ q∈Finset.range (2*h), (diagonalFiber h V q)^2)=∑ i : Fin h, (V i i)^2 := by
  simp_rw [diagonalFiber_sq]
  exact sum_diagonalFiber h _

lemma edgeEnergy_le_ordered (h : ℕ) (f : Fin h → ℝ) (hf : ∀ i, (f i)^2=1) :
    edgeEnergy h f ≤ (orderedEnergy h (fun i j ↦ f i*f j)+(h:ℝ))/2 := by
  have hdiag : (∑ q∈Finset.range (2*h),
      (diagonalFiber h (fun i j ↦ f i*f j) q)^2)=(h:ℝ) := by
    rw [diagonalEnergy]
    simp only [mul_pow,hf,one_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have hs : 2*edgeEnergy h f ≤ orderedEnergy h (fun i j ↦ f i*f j)+h := by
    rw [←hdiag]
    unfold edgeEnergy orderedEnergy
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro q hq
    have he := orderedFiber_split h (fun i j ↦ f i*f j) (fun i j ↦ mul_comm _ _) q
    change orderedFiber h (fun i j ↦ f i*f j) q=2*edgeFiber h f q+_ at he
    rw [he]
    nlinarith [sq_nonneg (edgeFiber h f q+
      diagonalFiber h (fun i j ↦ f i*f j) q)]
  linarith

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

lemma orderedColorEnergy_le (h : ℕ) (f : Fin h → ℝ) (hf : ∀ i, (f i)^2=1)
    (K : α → α → ℝ) (hK : ∀ x y, K x y=K y x) (ω : Fin h → α) :
    orderedEnergy h (fun i j ↦ (f i*f j)*K (ω i) (ω j)) ≤
      8*colorEnergy h f K ω+2*∑ i : Fin h, (K (ω i) (ω i))^2 := by
  have hdiag : (∑ q∈Finset.range (2*h),
      (diagonalFiber h (fun i j ↦ (f i*f j)*K (ω i) (ω j)) q)^2)=
        ∑ i : Fin h, (K (ω i) (ω i))^2 := by
    rw [diagonalEnergy]
    simp only [mul_pow,hf,one_mul]
  rw [←hdiag]
  unfold orderedEnergy colorEnergy
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q hq
  have he := orderedFiber_split h (fun i j ↦ (f i*f j)*K (ω i) (ω j))
    (fun i j ↦ by dsimp only; rw [mul_comm (f i),hK]) q
  change orderedFiber h (fun i j ↦ (f i*f j)*K (ω i) (ω j)) q=
    2*colorFiber h f K ω q+_ at he
  rw [he]
  nlinarith [sq_nonneg (2*colorFiber h f K ω q-
    diagonalFiber h (fun i j ↦ (f i*f j)*K (ω i) (ω j)) q)]

/-- Average ordered energy after a sign pattern is fixed. The diagonal
kernel second moment is separate from the independent-pair second moment. -/
theorem mean_orderedColorEnergy_le (h : ℕ) (f : Fin h → ℝ) (hf : ∀ i, (f i)^2=1)
    (K : α → α → ℝ) (hK : ∀ x y, K x y=K y x) :
    mean (fun ω : Fin h → α ↦ orderedEnergy h (fun i j ↦ (f i*f j)*K (ω i) (ω j))) ≤
      8*((kernelMean K)^2*edgeEnergy h f+
        kernelMean (fun x y ↦ (K x y)^2)*(h:ℝ)^2)+
      2*(h:ℝ)*mean (fun x : α ↦ (K x x)^2) := by
  have hm := mean_mono _ _ (orderedColorEnergy_le h f hf K hK)
  rw [mean_add,mean_const_mul,mean_const_mul,mean_sum] at hm
  have hd (i : Fin h) : mean (fun ω : Fin h → α ↦ (K (ω i) (ω i))^2)=
      mean (fun x : α ↦ (K x x)^2) := mean_eval i (fun x ↦ (K x x)^2)
  simp_rw [hd] at hm
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hm
  have he := mean_colorEnergy_le h f hf K
  nlinarith only [hm,he]

end Erdos66OrderedColorEnergy
