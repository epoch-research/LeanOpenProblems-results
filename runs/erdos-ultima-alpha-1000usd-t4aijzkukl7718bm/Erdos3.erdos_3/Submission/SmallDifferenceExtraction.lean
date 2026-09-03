import Submission.FiniteGraphPaths

/-! A dense restricted sumset has a large subset with a small difference set.
This is the graph-theoretic stage of quantitative Balog–Szemerédi–Gowers. -/
namespace Erdos3SmallDifferenceExtraction
open Finset Erdos3FiniteGraphPaths
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 3000000

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def labelTuples (D : Finset G) : Finset (G × G × G × G) := D ×ˢ D ×ˢ D ×ˢ D

def labelValue (p : G × G × G × G) : G := p.1-p.2.1-p.2.2.1+p.2.2.2

lemma path_labels_card_le {I : Type*} [Fintype I] [Nonempty I]
    (f : I → G) (hf : Function.Injective f) (D : Finset G) (i k : I) :
    (paths (fun a b ↦ f a+f b ∈ D) i k).card ≤
      ((labelTuples D).filter (fun p ↦ labelValue p = f i-f k)).card := by
  let label : (I × I × I) → (G × G × G × G) :=
    fun p ↦ (f i+f p.2.1,f p.1+f p.2.1,f k+f p.2.2,f p.1+f p.2.2)
  apply card_le_card_of_injOn label
  · intro p hp
    have hh : f i+f p.2.1 ∈ D ∧ f p.1+f p.2.1 ∈ D ∧
        f k+f p.2.2 ∈ D ∧ f p.1+f p.2.2 ∈ D := by
      simpa only [mem_coe,paths,mem_filter,mem_univ,true_and] using hp
    apply mem_filter.mpr
    refine ⟨?_,?_⟩
    · exact mem_product.mpr ⟨hh.1,mem_product.mpr ⟨hh.2.1,mem_product.mpr ⟨hh.2.2.1,hh.2.2.2⟩⟩⟩
    · dsimp [labelValue,label]
      abel
  · intro p _ q _ hpq
    have hb : p.2.1 = q.2.1 := hf (add_left_cancel (congrArg Prod.fst hpq))
    have hc : p.2.2 = q.2.2 := hf (add_left_cancel (congrArg (fun t ↦ t.2.2.1) hpq))
    have hz : p.1 = q.1 := by
      have hh := congrArg (fun t ↦ t.2.1) hpq
      dsimp [label] at hh
      rw [hb] at hh
      exact hf (add_right_cancel hh)
    exact Prod.ext hz (Prod.ext hb hc)

/-- Explicit dense restricted-sumset extraction, in a form without divisions.
Only finiteness of A and D is required; the ambient group can be infinite. -/
theorem restricted_sumset_small_difference (A D : Finset G) (hA : A.Nonempty)
    {ε : ℝ} (hε : 0 < ε)
    (havg : ε ≤ 𝔼 a : A, 𝔼 b : A, edge (fun x y : A ↦ (x : G)+(y : G) ∈ D) a b) :
    ∃ B ⊆ A, ε/4*(A.card : ℝ) ≤ B.card ∧
      (ε^5/4096)*(A.card : ℝ)^3*((B-B).card : ℝ) ≤ (D.card : ℝ)^4 := by
  letI : Nonempty A := hA.to_subtype
  let f : A → G := Subtype.val
  have hf : Function.Injective f := Subtype.val_injective
  let R : A → A → Prop := fun a b ↦ f a+f b ∈ D
  obtain ⟨S,hsize,hpaths⟩ := dense_graph_many_paths R hε havg
  let B := S.image f
  have hcard : B.card = S.card := card_image_of_injective S hf
  have hsub : B ⊆ A := by
    intro x hx
    obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    exact a.property
  have hN : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hsize' : ε/4*(A.card : ℝ) ≤ B.card := by
    rw [hcard]
    simpa only [Fintype.card_coe] using (le_div_iff₀ (by simpa only [Fintype.card_coe] using hN)).mp hsize
  have hlabel (d : G) (hd : d ∈ B-B) :
      (ε^5/4096)*(A.card : ℝ)^3 ≤
        (((labelTuples D).filter (fun p ↦ labelValue p = d)).card : ℝ) := by
    obtain ⟨a,ha,b,hb,hab⟩ := mem_sub.mp hd
    obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hb
    have hh := hpaths i hi k hk
    rw [path_density_eq] at hh
    simp only [Fintype.card_coe] at hh
    have hm := (le_div_iff₀ (by positivity : (0 : ℝ) < (A.card : ℝ)*(A.card : ℝ)^2)).mp hh
    rw [show (A.card : ℝ)*(A.card : ℝ)^2 = (A.card : ℝ)^3 by ring] at hm
    have hc := path_labels_card_le f hf D i k
    rw [hab] at hc
    exact hm.trans (by exact_mod_cast hc)
  refine ⟨B,hsub,hsize',?_⟩
  calc
    _ = ∑ _d ∈ B-B, (ε^5/4096)*(A.card : ℝ)^3 := by simp [mul_comm]
    _ ≤ ∑ d ∈ B-B, (((labelTuples D).filter (fun p ↦ labelValue p = d)).card : ℝ) :=
      sum_le_sum hlabel
    _ = ((((labelTuples D).filter (fun p ↦ labelValue p ∈ B-B)).card : ℕ) : ℝ) := by
      have he := sum_card_fiberwise_eq_card_filter (labelTuples D) (B-B) labelValue
      exact_mod_cast he
    _ ≤ ((labelTuples D).card : ℝ) := by
      exact_mod_cast card_le_card (filter_subset (fun p ↦ labelValue p ∈ B-B) (labelTuples D))
    _ = (D.card : ℝ)^4 := by simp only [labelTuples,card_product,Nat.cast_mul]; ring

#print axioms restricted_sumset_small_difference
end Erdos3SmallDifferenceExtraction
