import Submission.MixedExponentialSelectionExplore

/-! Local positive difference counts split into two disjoint-coordinate
matchings. This exposes upper potentials compatible with ordered selection. -/
namespace Erdos66DifferenceMatching
open Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli Erdos66BernoulliConcentration
open scoped Classical
set_option maxHeartbeats 2200000

noncomputable def edges (L N d : ℕ) : Finset (Fin (L+1) × Fin (L+1)) :=
  Finset.univ.filter (fun a ↦ N ≤ a.1.val ∧ a.2.val < 2*N ∧ a.1.val+d=a.2.val)
noncomputable def edgeClass (L N d b : ℕ) : Finset (Fin (L+1) × Fin (L+1)) :=
  (edges L N d).filter (fun a ↦ (a.1.val/d)%2=b)

lemma mem_edges {L N d : ℕ} {a : Fin (L+1) × Fin (L+1)} :
    a∈edges L N d ↔ N ≤ a.1.val ∧ a.2.val < 2*N ∧ a.1.val+d=a.2.val := by simp [edges]
lemma mem_edgeClass {L N d b : ℕ} {a : Fin (L+1) × Fin (L+1)} :
    a∈edgeClass L N d b ↔
      (N ≤ a.1.val ∧ a.2.val < 2*N ∧ a.1.val+d=a.2.val) ∧ (a.1.val/d)%2=b := by
  simp only [edgeClass,Finset.mem_filter,mem_edges]

lemma edgeClass_disjoint (L N d b : ℕ) (hd : 0 < d) :
    (edgeClass L N d b : Set (Fin (L+1) × Fin (L+1))).Pairwise
      (fun a c ↦ Disjoint (pairCoords a) (pairCoords c)) := by
  intro a ha c hc hac
  obtain ⟨⟨haN,ha2,haeq⟩,haq⟩ := mem_edgeClass.mp ha
  obtain ⟨⟨hcN,hc2,hceq⟩,hcq⟩ := mem_edgeClass.mp hc
  have had : a.2.val/d=a.1.val/d+1 := by rw [←haeq,Nat.add_div_right _ hd]
  have hcd : c.2.val/d=c.1.val/d+1 := by rw [←hceq,Nat.add_div_right _ hd]
  have hneq : a.1.val≠c.1.val ∨ a.2.val≠c.2.val := by
    by_contra hn
    push_neg at hn
    exact hac (Prod.ext (Fin.ext hn.1) (Fin.ext hn.2))
  apply Finset.disjoint_left.mpr
  intro i hia hic
  simp only [pairCoords,Finset.mem_insert,Finset.mem_singleton] at hia hic
  rcases hia with hia | hia  <;>  rcases hic with hic | hic  <;> 
    have he := congrArg Fin.val (hia.symm.trans hic)  <;> 
    have hed := congrArg (fun j : ℕ ↦ j/d) he <;> dsimp only at hed <;> omega

noncomputable def matchingCount (L N d b : ℕ) (ω : Fin (L+1) → Bool) : ℝ :=
  ∑ a∈edgeClass L N d b, monomial (pairCoords a) ω
noncomputable def matchingMean (L N d b : ℕ) (p : Fin (L+1) → ℝ) : ℝ :=
  ∑ a∈edgeClass L N d b, ∏ i∈pairCoords a, p i

lemma matchingMean_nonneg (L N d b : ℕ) (p : Fin (L+1) → ℝ) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ matchingMean L N d b p := by
  apply Finset.sum_nonneg
  intro a ha
  exact Finset.prod_nonneg (fun i _ ↦ hp i)

lemma matching_mgf (L N d b : ℕ) (hd : 0 < d) (p : Fin (L+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (t : ℝ) (ht : |t| ≤ 1/2) :
    expect p (fun ω ↦ Real.exp (t*(matchingCount L N d b ω-matchingMean L N d b p))) ≤ 
      Real.exp (2*t^2*matchingMean L N d b p) := by
  simpa only [matchingCount,matchingMean,one_mul] using
    centered_mgf_bound p hp (edgeClass L N d b) pairCoords (edgeClass_disjoint L N d b hd)
      (fun _ ↦ 1) (fun _ _ ↦ by norm_num) t ht

lemma matching_upper_mean (L N d b : ℕ) (hd : 0 < d) (p : Fin (L+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    expect p (fun ω ↦ Real.exp ((1/2:ℝ)*matchingCount L N d b ω)) ≤ Real.exp (matchingMean L N d b p) := by
  have hm := matching_mgf L N d b hd p hp (1/2) (by norm_num)
  have he (ω : Fin (L+1) → Bool) :
      Real.exp ((1/2:ℝ)*matchingCount L N d b ω)=
      Real.exp ((1/2:ℝ)*matchingMean L N d b p)*
        Real.exp ((1/2:ℝ)*(matchingCount L N d b ω-matchingMean L N d b p)) := by
    rw [←Real.exp_add]; congr 1; ring
  simp_rw [he]
  rw [expect_const_mul]
  have hh := mul_le_mul_of_nonneg_left hm (Real.exp_pos ((1/2:ℝ)*matchingMean L N d b p)).le
  apply hh.trans_eq
  rw [←Real.exp_add]
  congr 1
  ring

lemma edgeClass_card_le (L N d b : ℕ) : (edgeClass L N d b).card ≤ N := by
  have hh : (edgeClass L N d b).card ≤ (Finset.Ico N (2*N)).card := by
    apply Finset.card_le_card_of_injOn (fun a : Fin (L+1) × Fin (L+1) ↦ a.1.val)
    · intro a ha
      obtain ⟨⟨hN,h2,he⟩,hq⟩ := mem_edgeClass.mp ha
      exact Finset.mem_Ico.mpr ⟨hN,by omega⟩
    · intro a ha c hc he
      change a.1.val=c.1.val at he
      have ha' := (mem_edgeClass.mp ha).1.2.2
      have hc' := (mem_edgeClass.mp hc).1.2.2
      exact Prod.ext (Fin.ext he) (Fin.ext (by omega))
  simpa only [Nat.card_Ico,show 2*N-N=N by omega] using hh

lemma matchingMean_le (L N d b : ℕ) (hd : 0 < d) (p : Fin (L+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (v : ℝ)
    (hv : ∀ i : Fin (L+1), N ≤ i.val → i.val < 2*N → p i ≤ v) :
    matchingMean L N d b p ≤ (N:ℝ)*v^2 := by
  have hterm (a : Fin (L+1) × Fin (L+1)) (ha : a∈edgeClass L N d b) :
      (∏ i∈pairCoords a, p i) ≤ v^2 := by
    obtain ⟨⟨haN,ha2,haeq⟩,haq⟩ := mem_edgeClass.mp ha
    have hne : a.1≠a.2 := by intro he; have he' := congrArg Fin.val he; omega
    have hi := hv a.1 haN (by omega)
    have hj := hv a.2 (by omega) ha2
    simp only [pairCoords,Finset.prod_pair hne]
    rw [pow_two]
    exact mul_le_mul hi hj (hp a.2) ((hp a.1).trans hi)
  calc
    _  ≤  ∑ a∈edgeClass L N d b, v^2 := Finset.sum_le_sum hterm
    _ = ((edgeClass L N d b).card : ℝ)*v^2 := by simp
    _  ≤  (N:ℝ)*v^2 := mul_le_mul_of_nonneg_right (by exact_mod_cast edgeClass_card_le L N d b) (sq_nonneg v)

end Erdos66DifferenceMatching
