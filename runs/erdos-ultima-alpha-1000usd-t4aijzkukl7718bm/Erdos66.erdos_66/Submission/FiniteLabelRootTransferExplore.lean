import Submission.CenteredColorSelectionExplore
import Submission.PairWeightedRootTransferExplore

/-! The pair-weight root transfer in finite-label notation. -/
namespace Erdos66FiniteLabelRootTransfer
open Erdos66OrderedColorEnergy Erdos66PairWeightedRootTransfer
  Erdos66PairWeightedCharacterEnergy Erdos66IndexedCharacterEnergy
open scoped Classical
set_option maxHeartbeats 2200000

noncomputable def extendMatrix (h : ℕ) (V : Fin h → Fin h → ℝ) (i j : ℕ) : ℝ :=
  if hi : i<h then if hj : j<h then V ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0

lemma extendMatrix_fin (h : ℕ) (V : Fin h → Fin h → ℝ) (i j : Fin h) :
    extendMatrix h V i.val j.val=V i j := by simp [extendMatrix,i.isLt,j.isLt]

lemma sum_fin_pair (h : ℕ) (G : ℕ → ℕ → ℝ) :
    (∑ i : Fin h, ∑ j : Fin h, G i.val j.val)=
      ∑ i∈Finset.range h, ∑ j∈Finset.range h, G i j := by
  calc
    _ = ∑ i : Fin h, ∑ j∈Finset.range h, G i.val j := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Fin.sum_univ_eq_sum_range (G i.val) h
    _ = _ := Fin.sum_univ_eq_sum_range (fun i ↦ ∑ j∈Finset.range h, G i j) h

lemma matrixSum_extend (h : ℕ) (V : Fin h → Fin h → ℝ) :
    matrixSum h (extendMatrix h V)=∑ i : Fin h, ∑ j : Fin h, V i j := by
  unfold matrixSum
  rw [←sum_fin_pair]
  simp_rw [extendMatrix_fin]

variable {p : ℕ} [Fact p.Prime]

noncomputable def signPattern (h : ℕ) (a : ZMod p) (i : Fin h) : ℝ :=
  (quadraticChar (ZMod p) (a+(i.val:ZMod p)):ℝ)

noncomputable def labelRootCount (h : ℕ) (a : ZMod p) (V : Fin h → Fin h → ℝ)
    (t s : ZMod p) : ℝ :=
  ∑ i : Fin h, ∑ j : Fin h,
    V i j*(Fintype.card {x : ZMod p // x^2/(a+i.val)+(t-x)^2/(a+j.val)=s}:ℝ)

lemma matrixRootCount_extend (h : ℕ) (a : ZMod p) (V : Fin h → Fin h → ℝ)
    (t s : ZMod p) :
    matrixRootCount h a (extendMatrix h V) t s=labelRootCount h a V t s := by
  unfold matrixRootCount
  rw [←sum_fin_pair]
  simp_rw [extendMatrix_fin]
  rfl

lemma matrixFiber_extend (h : ℕ) (a : ZMod p) (V : Fin h → Fin h → ℝ) (q : ℕ) :
    matrixFiber h (extendMatrix h V) a q=
      orderedFiber h (fun i j ↦ (signPattern h a i*signPattern h a j)*V i j) q := by
  unfold matrixFiber pairFiber
  rw [Finset.sum_filter,Finset.sum_product]
  change (∑ i∈Finset.range h, ∑ j∈Finset.range h,
    if i+j=q then extendMatrix h V i j*(quadraticChar (ZMod p) (a+i):ℝ)*
      (quadraticChar (ZMod p) (a+j):ℝ) else 0)=_
  rw [←sum_fin_pair]
  simp_rw [extendMatrix_fin]
  unfold orderedFiber
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only [signPattern]
  split_ifs <;> ring

lemma matrixEnergy_extend (h : ℕ) (a : ZMod p) (V : Fin h → Fin h → ℝ) :
    matrixEnergy h (extendMatrix h V) a=
      orderedEnergy h (fun i j ↦ (signPattern h a i*signPattern h a j)*V i j) := by
  unfold matrixEnergy orderedEnergy
  simp_rw [matrixFiber_extend]

lemma matrixFiber_restrict (h : ℕ) (a : ZMod p) (W : ℕ → ℕ → ℝ) (q : ℕ) :
    matrixFiber h W a q=matrixFiber h (extendMatrix h (fun i j ↦ W i.val j.val)) a q := by
  unfold matrixFiber
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨hi,hj,hs⟩ := mem_pairFiber.mp he
  simp only [extendMatrix,hi,hj,dif_pos]

lemma matrixEnergy_restrict (h : ℕ) (a : ZMod p) (W : ℕ → ℕ → ℝ) :
    matrixEnergy h W a=orderedEnergy h
      (fun i j ↦ (signPattern h a i*signPattern h a j)*W i.val j.val) := by
  rw [←matrixEnergy_extend]
  unfold matrixEnergy
  apply Finset.sum_congr rfl
  intro q hq
  rw [matrixFiber_restrict h a W q]

lemma signPattern_sq (h : ℕ) (a : ZMod p) (ha : ∀ i<h, a+(i:ZMod p)≠0)
    (i : Fin h) : (signPattern h a i)^2=1 := by
  unfold signPattern
  exact_mod_cast quadraticChar_sq_one (ha i.val i.isLt)

/-- Uniform over every fine target, for a fixed admissible translation. -/
theorem labelRootCount_error_sq (hp : p≠2) (h : ℕ) (a : ZMod p)
    (ha : ∀ i<h, a+(i:ZMod p)≠0) (hop : ∀ q<2*h, 2*a+(q:ZMod p)≠0)
    (V : Fin h → Fin h → ℝ) (t s : ZMod p) :
    (labelRootCount h a V t s-(∑ i : Fin h, ∑ j : Fin h, V i j))^2 ≤
      2*(h:ℝ)*orderedEnergy h (fun i j ↦ (signPattern h a i*signPattern h a j)*V i j) := by
  have he := matrixRootCount_error_sq hp h a (extendMatrix h V) ha hop t s
  rwa [matrixRootCount_extend,matrixSum_extend,matrixEnergy_extend] at he

/-- One low-energy sign pattern is selected with no later color data. -/
theorem exists_low_energy_pattern (hp : p≠2) (h : ℕ) (hh : 4*h<p) :
    ∃ a : ZMod p,
      (∀ i<h, a+(i:ZMod p)≠0) ∧ (∀ q<2*h, 2*a+(q:ZMod p)≠0) ∧
      orderedEnergy h (fun i j ↦ signPattern h a i*signPattern h a j) ≤ 8*(h:ℝ)^2 := by
  obtain ⟨a,ha,hop,hbudget,he⟩ := exists_admissible_matrix_budget hp h hh
    ({()}:Finset Unit) (fun _ _ _ ↦ (1:ℝ)) (fun _ ↦ (1:ℝ)) (by intros; norm_num)
  refine ⟨a,ha,hop,?_⟩
  simp only [Finset.sum_singleton,one_mul] at hbudget
  rw [matrixEnergy_restrict] at hbudget
  simpa only [mul_one,matrixMass,one_pow,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
    pow_two] using hbudget

end Erdos66FiniteLabelRootTransfer
