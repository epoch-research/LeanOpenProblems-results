import Submission.Forest93Certificate
import Submission.ForestEvents
import Submission.RootOverlapCompensation

/-! The finite forest certificate applied to actual events, with the two
ternary-branch pivot laws kept as explicit geometric hypotheses. -/
namespace Erdos7Forest93Events
open scoped BigOperators
open Erdos7Forest93Certificate Erdos7ForestUnion Erdos7ForestCapacity Erdos7ForestEvents
set_option maxHeartbeats 2500000
set_option maxRecDepth 100000
set_option autoImplicit false

lemma pivot_weights : weight 192 = 3/20 ∧ weight 160 = 1/10 := by decide +kernel
lemma parent_lt (i j : Index) (h : parent i = some j) : rank j < rank i := by
  have hh := parent_decreases i
  simpa only [h,Option.elim_some] using hh
lemma edge_parent_iff (i j : Index) : (i,j) ∈ edges ↔ parent i = some j := by
  constructor
  · exact edges_parent (i,j)
  · intro h
    have hh := parent_edges i
    simpa only [h,Option.elim_some] using hh

noncomputable def selection (S : Finset Index) (i : Index) : ℚ := bit (i ∈ S)
lemma selection_bounds (S : Finset Index) (i : Index) : 0 ≤ selection S i ∧ selection S i ≤ 1 := bit_bounds _
lemma selection_mem (S : Finset Index) (i : Index) (hi : i ∈ S) : selection S i = 1 := by simp [selection,bit,hi]
lemma selection_not_mem (S : Finset Index) (i : Index) (hi : i ∉ S) : selection S i = 0 := by simp [selection,bit,hi]
lemma selection_sum (S : Finset Index) : (∑ i,selection S i) = (S.card:ℚ) := by
  classical
  letI : DecidablePred (fun i : Index => i ∈ S) := fun _ => Classical.propDecidable _
  unfold selection bit
  rw [Finset.sum_boole]
  congr 1
  apply congrArg Finset.card
  ext i
  simp

lemma polynomial_selection (S : Finset Index) :
    polynomial ordinary (fun i => weight i*selection S i)-(1/40)*selection S 192*selection S 160 =
      (∑ i,weight i*selection S i)-(∑ e ∈ edges,coefficient e*selection S e.1*selection S e.2) := by
  have he := Finset.sum_erase_add edges
    (fun e => coefficient e*selection S e.1*selection S e.2) forced_mem
  have ho : (∑ e ∈ ordinary,coefficient e*selection S e.1*selection S e.2) =
      edgeProduct ordinary (fun i => weight i*selection S i) := by
    apply Finset.sum_congr rfl
    intro e he
    have hn : e ≠ forced := (Finset.mem_erase.mp he).1
    simp only [coefficient,if_neg hn]
    ring
  have hf : coefficient forced*selection S forced.1*selection S forced.2 =
      (1/40)*selection S 192*selection S 160 := by
    simp only [coefficient,if_true,forced]
    ring
  change (∑ e ∈ ordinary,coefficient e*selection S e.1*selection S e.2)+_ = _ at he
  dsimp only at he
  rw [ho,hf] at he
  unfold polynomial
  linarith

section Events
variable {Ω : Type*} [Fintype Ω]

theorem union_mass_lt_one (μ : Ω → ℚ) (hμ : ∀ z,0 ≤ μ z)
    (A : Index → Ω → Prop) (S : Finset Index) (hcard : S.card ≤ 84)
    (hw : ∀ i,mass μ (A i) ≤ weight i*selection S i)
    (hprod : ∀ e ∈ ordinary,mass μ (A e.1)*mass μ (A e.2) ≤
      mass μ (fun z => A e.1 z ∧ A e.2 z))
    (hroot : 192 ∈ S → 160 ∈ S → ∃ u v : ℚ,
      (u = 2/5 ∨ u = 3/5) ∧ (v = 2/5 ∨ v = 3/5) ∧
      mass μ (A 192) = u/4 ∧ mass μ (A 160) = v/6 ∧
      (if u = v then u/24 else 0) ≤ mass μ (fun z => A 160 z ∧ A 192 z)) :
    mass μ (fun z => ∃ i,A i z) < 1 := by
  classical
  let W (i : Index) := weight i*selection S i
  let overlap := mass μ (fun z => A 160 z ∧ A 192 z)
  let slack (i : Index) := (W i-mass μ (A i))*(1-neighbor ordinary W i)
  have hW (i : Index) : W i ≤ weight i := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (selection_bounds S i).2 (weight_nonneg i)
  have hd (i : Index) : neighbor ordinary W i ≤ 1 :=
    (neighbor_mono ordinary W weight hW i).trans (degree_bound i)
  have hn (i : Index) : 0 ≤ slack i :=
    mul_nonneg (sub_nonneg.mpr (hw i)) (sub_nonneg.mpr (hd i))
  have hsum : 0 ≤ ∑ i,slack i := Finset.sum_nonneg (fun i _ => hn i)
  have hoverlap : 0 ≤ overlap := mass_nonneg μ hμ _
  have hcomp : (1/40)*selection S 192*selection S 160 ≤ overlap+∑ i,slack i := by
    by_cases h₁ : 192 ∈ S
    · by_cases h₂ : 160 ∈ S
      · obtain ⟨u,v,hu,hv,ha,hb,hi⟩ := hroot h₁ h₂
        have hd₁ := (neighbor_mono ordinary W weight hW (192:Index)).trans pivot_degree.1
        have hd₂ := (neighbor_mono ordinary W weight hW (160:Index)).trans pivot_degree.2
        have hc := Erdos7RootOverlapCompensation.branch_overlap_charge u v
          (neighbor ordinary W 192) (neighbor ordinary W 160) hu hv hd₁ hd₂
        have hs := Finset.sum_le_sum_of_subset_of_nonneg
          (show ({192,160}:Finset Index) ⊆ Finset.univ from Finset.subset_univ _)
          (fun i _ _ => hn i)
        rw [Finset.sum_pair (by decide : (192:Index) ≠ 160)] at hs
        have hw₁ : W 192 = 3/20 := by simp only [W,selection_mem S 192 h₁,pivot_weights.1,mul_one]
        have hw₂ : W 160 = 1/10 := by simp only [W,selection_mem S 160 h₂,pivot_weights.2,mul_one]
        dsimp only [slack] at hs
        rw [hw₁,hw₂,ha,hb] at hs
        rw [selection_mem S 192 h₁,selection_mem S 160 h₂]
        dsimp only [overlap] at *
        linarith
      · rw [selection_not_mem S 160 h₂,mul_zero]
        linarith
    · rw [selection_not_mem S 192 h₁,mul_zero,zero_mul]
      linarith
  have hb := compensated_forest_bound μ hμ A parent rank parent_lt edges edge_parent_iff
    forced forced_mem W hw overlap ((1/40)*selection S 192*selection S 160) hprod le_rfl hcomp
  have hsel := selection_certificate (selection S) (selection_bounds S)
    (by rw [selection_sum]; exact_mod_cast hcard)
  rw [← polynomial_selection S] at hsel
  exact hb.trans_lt hsel
end Events

#print axioms union_mass_lt_one
end Erdos7Forest93Events
