import FormalConjecturesUtil
import Submission.VertexMerging

/-! A forbidden copy created by a merger lifts to a nontrivial split copy
in the original graph. Both split roots are required to receive edges. -/
open SimpleGraph
namespace Erdos713VertexSplitWitnesses
open Erdos713VertexMerging
variable {V W : Type*}
set_option maxHeartbeats 2000000

def split (H : SimpleGraph W) (w : W) (S : Set W) : SimpleGraph (Option W) where
  Adj
    | none, none => False
    | none, some y => H.Adj w y ∧ y ∉ S
    | some x, none => H.Adj w x ∧ x ∉ S
    | some x, some y => H.Adj x y ∧ (x = w → y ∈ S) ∧ (y = w → x ∈ S)
  symm := by
    rintro (_|x) (_|y) h
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := by
    rintro (_|x) h
    · exact h
    · exact h.1.ne rfl

def project (w : W) : Option W → W := Option.elim' w id

def projectHom (H : SimpleGraph W) (w : W) (S : Set W) : split H w S →g H where
  toFun := project w
  map_rel' := by
    rintro (_|x) (_|y) h
    · exact h.elim
    · exact h.1
    · exact h.1.symm
    · exact h.1

lemma split_bipartite {H : SimpleGraph W} (hH : H.IsBipartite) (w : W) (S : Set W) :
    (split H w S).IsBipartite := hH.of_hom (projectHom H w S)

def leftCopy (H : SimpleGraph W) (w : W) (S : Set W)
    (hall : ∀ x, H.Adj w x → x ∈ S) : H.Copy (split H w S) := by
  refine ⟨⟨some,?_⟩,Option.some_injective W⟩
  intro x y hxy
  exact ⟨hxy,fun he => hall y (he ▸ hxy),fun he => hall x (he ▸ hxy.symm)⟩

open scoped Classical in
noncomputable def rightCopy (H : SimpleGraph W) (w : W) (S : Set W)
    (hall : ∀ x, H.Adj w x → x ∉ S) : H.Copy (split H w S) := by
  let f : W → Option W := fun x => if x = w then none else some x
  refine ⟨⟨f,?_⟩,?_⟩
  · intro x y hxy
    by_cases hx : x = w <;> by_cases hy : y = w
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · subst x
      simp only [f,if_pos rfl,if_neg hy]
      exact ⟨hxy,hall y hxy⟩
    · subst y
      simp only [f,if_neg hx,if_pos rfl]
      exact ⟨hxy.symm,hall x hxy.symm⟩
    · simp only [f,if_neg hx,if_neg hy]
      exact ⟨hxy,fun h => (hx h).elim,fun h => (hy h).elim⟩
  · intro x y hxy
    change f x = f y at hxy
    by_cases hx : x = w <;> by_cases hy : y = w <;> simp_all [f]

/-- The witness keeps the two host roots distinguished. This theorem
asserts actual copies, not a transfer of any extremal rate. -/
theorem split_copy_of_merge {H : SimpleGraph W} {G : SimpleGraph V}
    (hf : H.Free G) {u v : V} (hn : ¬ G.Adj u v)
    (hc : H ⊑ merge G u v hn) :
    ∃ (w : W) (S : Set W) (f : (split H w S).Copy G),
      f (some w) = u ∧ f none = v ∧
      (∃ x, H.Adj w x ∧ x ∈ S) ∧ (∃ y, H.Adj w y ∧ y ∉ S) := by
  classical
  obtain ⟨g⟩ := hc
  let f : W → V := fun x => (g x).val
  have hfi : Function.Injective f := Subtype.val_injective.comp g.injective
  have hfv (x : W) : f x ≠ v := (g x).property
  have hroot : ∃ w, f w = u := by
    by_contra hh
    push_neg at hh
    apply hf
    refine ⟨⟨⟨f,?_⟩,hfi⟩⟩
    intro x y hxy
    have ha := (merge_adj G u v hn (g x) (g y)).mp (g.toHom.map_adj hxy)
    rcases ha with ha | ⟨hx,_⟩ | ⟨hy,_⟩
    · exact ha
    · exact (hh x hx).elim
    · exact (hh y hy).elim
  obtain ⟨w,hw⟩ := hroot
  let S : Set W := {x | G.Adj u (f x)}
  let F : Option W → V := Option.elim' v f
  have hFsome (x : W) : F (some x) = f x := rfl
  have hFnone : F none = v := rfl
  have hFroot : F (some w) = u := hw
  have hFi : Function.Injective F := by
    rintro (_|x) (_|y) hxy
    · rfl
    · exact (hfv y hxy.symm).elim
    · exact (hfv x hxy).elim
    · exact congrArg some (hfi hxy)
  have hcoverage {x : W} (hx : H.Adj w x) : G.Adj u (f x) ∨ G.Adj v (f x) := by
    have ha := (merge_adj G u v hn (g w) (g x)).mp (g.toHom.map_adj hx)
    have hxw : f x ≠ u := by
      intro hh
      exact hx.ne (hfi (hw.trans hh.symm))
    change G.Adj (f w) (f x) ∨ (f w = u ∧ G.Adj v (f x)) ∨
      (f x = u ∧ G.Adj v (f w)) at ha
    rw [hw] at ha
    rcases ha with ha | ⟨_,ha⟩ | ⟨hxu,_⟩
    · exact Or.inl ha
    · exact Or.inr ha
    · exact (hxw hxu).elim
  have hHom : ∀ {x y}, (split H w S).Adj x y → G.Adj (F x) (F y) := by
    rintro (_|x) (_|y) hxy
    · exact hxy.elim
    · have hc := hcoverage hxy.1
      exact hc.resolve_left hxy.2
    · have hc := hcoverage hxy.1
      exact (hc.resolve_left hxy.2).symm
    · by_cases hx : x = w
      · subst x
        have hh : G.Adj u (f y) := hxy.2.1 rfl
        simpa only [hFsome,hw] using hh
      · by_cases hy : y = w
        · subst y
          have hh : G.Adj u (f x) := hxy.2.2 rfl
          simpa only [hFsome,hw] using hh.symm
        · have ha := (merge_adj G u v hn (g x) (g y)).mp (g.toHom.map_adj hxy.1)
          rcases ha with ha | ⟨hxu,_⟩ | ⟨hyu,_⟩
          · exact ha
          · exact (hx (hfi (hxu.trans hw.symm))).elim
          · exact (hy (hfi (hyu.trans hw.symm))).elim
  let c : (split H w S).Copy G := ⟨⟨F,hHom⟩,hFi⟩
  refine ⟨w,S,c,hFroot,hFnone,?_,?_⟩
  · by_contra hh
    push_neg at hh
    exact hf ⟨c.comp (rightCopy H w S hh)⟩
  · by_contra hh
    push_neg at hh
    exact hf ⟨c.comp (leftCopy H w S hh)⟩

#print axioms split_copy_of_merge
#print axioms split_bipartite
end Erdos713VertexSplitWitnesses
