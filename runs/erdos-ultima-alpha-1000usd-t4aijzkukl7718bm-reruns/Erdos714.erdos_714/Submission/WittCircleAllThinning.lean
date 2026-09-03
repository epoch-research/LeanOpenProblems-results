import Submission.TwoInputFiberThinning
import Submission.WittNormCircleFinite

/-!
All-characteristic-two arbitrary-thinning obstruction for the full Witt
norm-circle host. This strengthens the odd-degree projective-block argument.
It does not concern arbitrary graphs and does not settle Erdős714.
-/
noncomputable section
open Classical SimpleGraph Finset
open scoped CharTwo
set_option maxHeartbeats 2000000
namespace Erdos714WittCircleAllThinning
open Erdos714WittNormCircle
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E] [CharP F 2]

lemma norm_square_fiber (hE : Fintype.card E=Fintype.card F^2) (x : E) (r : F) :
    (univ.filter (fun u : E => (Algebra.norm F (x+u))^2=r)).card ≤ Fintype.card F+1 := by
  let S := univ.filter (fun u : E => (Algebra.norm F (x+u))^2=r)
  by_cases hne : S.Nonempty
  · obtain ⟨u₀,hu₀⟩ := hne
    have hr : (Algebra.norm F (x+u₀))^2=r := (mem_filter.mp hu₀).2
    have hsub : S ⊆ univ.filter (fun u : E => Algebra.norm F (x+u)=Algebra.norm F (x+u₀)) := by
      intro u hu
      refine mem_filter.mpr ⟨mem_univ _,?_⟩
      have he : (Algebra.norm F (x+u))^2=(Algebra.norm F (x+u₀))^2 := (mem_filter.mp hu).2.trans hr.symm
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
      · exact h
      · simpa only [CharTwo.neg_eq] using h
    have hcard : (univ.filter (fun u : E => Algebra.norm F (x+u)=Algebra.norm F (x+u₀))).card =
        (univ.filter (fun z : E => Algebra.norm F z=Algebra.norm F (x+u₀))).card := by
      apply Finset.card_equiv (Equiv.addLeft x)
      intro u
      simp
    exact (card_le_card hsub).trans (hcard ▸ Erdos714TranslatedNorm.norm_fiber_bound hE _)
  · have he : S=∅ := not_nonempty_iff_eq_empty.mp hne
    change S.card ≤ _
    simp [he]

/-- Fixing x, w=v+x*u, and the norm level gives q^5 blocks, each with
at most q+1 vertices on either side. This holds in BOTH degree parities. -/
theorem arbitrary_thinning (hE : Fintype.card E=Fintype.card F^2)
    (H : SimpleGraph ((E × E) ⊕ (E × E))) (hH : H ≤ fieldGraph (F := F) (E := E))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 1327104*Fintype.card F^27 := by
  let f (x u : E) := -(x*u)
  let g (x u : E) := (Algebra.norm F (x+u))^2
  have hh : H ≤ Erdos714TwoInputFibers.graph (Algebra.norm F) f g := by
    intro v w hvw
    have h := hH hvw
    cases v with
    | inl x =>
      cases w with
      | inl y => exact False.elim h
      | inr y =>
        change Algebra.norm F (x.2+y.2-f x.1 y.1)=g x.1 y.1
        simpa only [f,g,sub_neg_eq_add,wittAdd] using h.2
    | inr y =>
      cases w with
      | inr x => exact False.elim h
      | inl x =>
        change Algebra.norm F (x.2+y.2-f x.1 y.1)=g x.1 y.1
        simpa only [f,g,sub_neg_eq_add,wittAdd] using h.2
  have h := Erdos714TwoInputFibers.fourth_power (Algebra.norm F) f g (Fintype.card F+1)
    (Erdos714TranslatedNorm.norm_fiber_bound hE) (norm_square_fiber hE) H hh hfree
  rw [hE] at h
  have hq : 0 < Fintype.card F := Fintype.card_pos
  calc
    _ ≤ 10368*(Fintype.card F^2*Fintype.card F^2*Fintype.card F)^4*(Fintype.card F+1)^7 := h
    _ ≤ 10368*(Fintype.card F^2*Fintype.card F^2*Fintype.card F)^4*(2*Fintype.card F)^7 := by
      gcongr
      omega
    _ = _ := by ring

/-- No fixed positive critical-scale edge budget can hold along unbounded
binary fields, even after completely arbitrary edge deletions. -/
theorem critical_budget (hE : Fintype.card E=Fintype.card F^2)
    (H : SimpleGraph ((E × E) ⊕ (E × E))) (hH : H ≤ fieldGraph (F := F) (E := E))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (C : ℕ) (he : Fintype.card F^7 ≤ C*H.edgeFinset.card) :
    Fintype.card F ≤ 1327104*C^4 := by
  have hm := arbitrary_thinning hE H hH hfree
  have h : Fintype.card F^27*Fintype.card F ≤ Fintype.card F^27*(1327104*C^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (C*H.edgeFinset.card)^4 := Nat.pow_le_pow_left he 4
      _ = C^4*H.edgeFinset.card^4 := by ring
      _ ≤ C^4*(1327104*Fintype.card F^27) := Nat.mul_le_mul_left _ hm
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (pow_pos Fintype.card_pos 27)

#print axioms norm_square_fiber
#print axioms arbitrary_thinning
#print axioms critical_budget
end Erdos714WittCircleAllThinning
