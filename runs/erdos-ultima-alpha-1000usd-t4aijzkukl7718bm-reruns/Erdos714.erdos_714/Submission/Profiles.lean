import Submission.Packing

/-!
Counting repeated neighborhood profiles on slices. These are obstructions to
restricted graph models, not a solution of Erdős Problem 714.
-/

open SimpleGraph Finset Classical
open Erdos714Packing

namespace Erdos714Profiles

variable {R C X : Type*} [Fintype R] [Fintype C] [Fintype X]

omit [Fintype C] in
/-- A profile with at least r neighbors can occur for fewer than r distinct columns. -/
theorem large_profile_fiber (P : C → Finset X) (label : R → C) {r : ℕ}
    (hr : 0 < r)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free (incidence (P ∘ label)))
    (c : C) (hc : r ≤ (P c).card) :
    (univ.filter (fun v : R => label v = c)).card ≤ r - 1 := by
  by_contra! h
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin r) (s := univ.filter (fun v : R => label v = c)) (by simp only [Fintype.card_fin]; omega)
  have hlabel (i : Fin r) : label (f i) = c := (mem_filter.mp (hf ⟨i,rfl⟩)).2
  have hcommon := (free_iff_common_card (P ∘ label) hr).mp hfree f
  have hsub : P c ⊆ common (P ∘ label) f := by
    intro x hx
    simp only [mem_common, Function.comp_apply, hlabel]
    exact fun _ => hx
  have hcard := card_le_card hsub
  omega

/-- Count small profiles by columns and large profiles by their bounded multiplicity. -/
theorem edge_bound (P : C → Finset X) (label : R → C) {r : ℕ}
    (hr : 0 < r)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free (incidence (P ∘ label))) :
    (incidence (P ∘ label)).edgeFinset.card ≤
      (r - 1) * (Fintype.card R + ∑ c, (P c).card) := by
  let fiber (c : C) := (univ : Finset R).filter (fun v => label v = c)
  have hsum : ∑ c, (fiber c).card = Fintype.card R := by
    simpa [fiber] using sum_card_fiberwise_eq_card_filter
      (univ : Finset R) (univ : Finset C) label
  have hedge : (incidence (P ∘ label)).edgeFinset.card =
      ∑ c, (fiber c).card * (P c).card := by
    rw [incidence_edges]
    simpa [fiber, Function.comp_def] using
      (sum_fiberwise_of_maps_to' (s := (univ : Finset R)) (t := (univ : Finset C))
        (g := label) (fun _ _ => mem_univ _) (fun c => (P c).card)).symm
  rw [hedge]
  calc
    ∑ c, (fiber c).card * (P c).card ≤
        ∑ c, ((r-1)*(fiber c).card + (r-1)*(P c).card) := by
      apply sum_le_sum
      intro c _
      by_cases hc : r ≤ (P c).card
      · have hf := large_profile_fiber P label hr hfree c hc
        exact (Nat.mul_le_mul_right (P c).card hf).trans (Nat.le_add_left _ _)
      · have hc' : (P c).card ≤ r - 1 := by omega
        have h := Nat.mul_le_mul_left (fiber c).card hc'
        rw [Nat.mul_comm (fiber c).card (r-1)] at h
        exact h.trans (Nat.le_add_right _ _)
    _ = (r-1)*(Fintype.card R + ∑ c, (P c).card) := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, hsum, mul_add]

variable {T : Type*} [Fintype T]

/-- The set of neighbors assembled from a family of disjoint coordinate slices. -/
noncomputable def slices (P : T → C → Finset X) (label : T → R → C) (v : R) : Finset (T × X) :=
  univ.filter (fun p => p.2 ∈ P p.1 (label p.1 v))

/-- Restricting to one slice gives a copy of its profile incidence graph. -/
def sliceCopy (P : T → C → Finset X) (label : T → R → C) (t : T) :
    Copy (incidence (P t ∘ label t)) (incidence (slices P label)) := by
  let e : X ↪ T × X := ⟨fun x => (t,x), fun _ _ h => congrArg Prod.snd h⟩
  let f := (Function.Embedding.refl R).sumMap e
  refine ⟨⟨f, ?_⟩, f.injective⟩
  intro a b hab
  cases a <;> cases b <;> simp_all [f, e, incidence, slices]

omit [Fintype C] in
/-- Edges are partitioned by their right-endpoint slice. -/
theorem slices_edges (P : T → C → Finset X) (label : T → R → C) :
    (incidence (slices P label)).edgeFinset.card =
      ∑ t, (incidence (P t ∘ label t)).edgeFinset.card := by
  simp only [incidence_edges, slices, card_filter, Fintype.sum_prod_type]
  rw [sum_comm]
  congr 1
  funext t
  simp

/-- Uniform profile complexity on slices bounds the whole graph. -/
theorem sliced_edge_bound (P : T → C → Finset X) (label : T → R → C)
    {r b : ℕ} (hr : 0 < r) (hb : ∀ t, ∑ c, (P t c).card ≤ b)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free
      (incidence (slices P label))) :
    (incidence (slices P label)).edgeFinset.card ≤
      Fintype.card T * ((r-1)*(Fintype.card R + b)) := by
  rw [slices_edges]
  calc
    ∑ t, (incidence (P t ∘ label t)).edgeFinset.card ≤
        ∑ _t : T, (r-1)*(Fintype.card R+b) := by
      apply sum_le_sum
      intro t _
      have ht : (completeBipartiteGraph (Fin r) (Fin r)).Free
          (incidence (P t ∘ label t)) := by
        rintro ⟨c⟩
        exact hfree ⟨(sliceCopy P label t).comp c⟩
      exact (edge_bound (P t) (label t) hr ht).trans
        (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hb t) _))
    _ = _ := by simp

end Erdos714Profiles

#print axioms Erdos714Profiles.large_profile_fiber
#print axioms Erdos714Profiles.edge_bound
#print axioms Erdos714Profiles.sliced_edge_bound
