import Submission.FinitePaletteCompactness

/-! The finite triangle-free edge-cover vertex-subset ideal and an ultrafilter separation lemma. -/

open SimpleGraph Set Filter
open Erdos595FinitePalette
namespace Erdos595FiniteEdgeCoverIdeal

private def sumColor {A B C D : Type*} (c : Sym2 A → C) (d : Sym2 B → D) :
    Sym2 (A ⊕ B) → C ⊕ (D ⊕ Unit) :=
  Sym2.lift ⟨fun a b => match a,b with
    | .inl x,.inl y => Sum.inl (c s(x,y))
    | .inr x,.inr y => Sum.inr (Sum.inl (d s(x,y)))
    | _,_ => Sum.inr (Sum.inr ()),by
      intro a b
      cases a <;> cases b <;> simp [Sym2.eq_swap]⟩

lemma sum_coloring {A B C D : Type*} (G : SimpleGraph (A ⊕ B))
    (hc : HasColoring (G.comap Sum.inl) C) (hd : HasColoring (G.comap Sum.inr) D) :
    HasColoring G (C ⊕ (D ⊕ Unit)) := by
  obtain ⟨c,hc⟩ := hc
  obtain ⟨d,hd⟩ := hd
  refine ⟨sumColor c d,?_⟩
  intro a b t hab hat hbt hm
  cases a <;> cases b <;> cases t <;>
    simp only [sumColor,Sym2.lift_mk,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq,false_and,and_false] at hm
  · exact hc _ _ _ hab hat hbt hm
  · exact hd _ _ _ hab hat hbt hm

def FiniteOn {A : Type} (G : SimpleGraph A) (S : Set A) : Prop :=
  ∃ (C : Type) (_ : Finite C), HasColoring (G.induce S) C

lemma finiteOn_empty {A : Type} (G : SimpleGraph A) : FiniteOn G ∅ := by
  refine ⟨Unit,inferInstance,fun _ => (),?_⟩
  intro a
  exact a.property.elim

lemma FiniteOn.mono {A : Type} {G : SimpleGraph A} {S T : Set A}
    (hT : FiniteOn G T) (hST : S ⊆ T) : FiniteOn G S := by
  obtain ⟨C,hC,hc⟩ := hT
  let f : G.induce S →g G.induce T :=
    ⟨fun x => ⟨x.val,hST x.property⟩,fun h => h⟩
  exact ⟨C,hC,hc.comap f⟩

lemma FiniteOn.union {A : Type} {G : SimpleGraph A} {S T : Set A}
    (hS : FiniteOn G S) (hT : FiniteOn G T) : FiniteOn G (S ∪ T) := by
  classical
  obtain ⟨C,hC,hc⟩ := hS
  obtain ⟨D,hD,hd⟩ := hT
  letI := hC
  letI := hD
  let v : S ⊕ T → A := Sum.elim Subtype.val Subtype.val
  let K := G.comap v
  have hk : HasColoring K (C ⊕ (D ⊕ Unit)) := sum_coloring K hc hd
  let f : (S ∪ T : Set A) → S ⊕ T := fun x =>
    if h : x.val ∈ S then .inl ⟨x.val,h⟩ else .inr ⟨x.val,x.property.resolve_left h⟩
  have hf : ∀ x, v (f x) = x.val := by
    intro x
    dsimp only [f]
    split_ifs <;> rfl
  let e : G.induce (S ∪ T) →g K :=
    { toFun := f
      map_rel' := by
        intro a b hab
        change G.Adj (v (f a)) (v (f b))
        rw [hf a,hf b]
        exact hab }
  exact ⟨C ⊕ (D ⊕ Unit),inferInstance,hk.comap e⟩

/-- A finite-union ideal with no common ultrafilter support can be avoided
by one ultrafilter on the index family. -/
theorem avoiding_ultrafilter {A I : Type*} (P : Set A → Prop)
    (h0 : P ∅) (hU : ∀ S T, P S → P T → P (S ∪ T))
    (p : I → Ultrafilter A) (hbad : ∀ S, P S → ∃ i, S ∉ p i) :
    ∃ U : Ultrafilter I, ∀ S, P S → {i | S ∉ p i} ∈ U := by
  let F : Filter I :=
    { sets := {X | ∃ S, P S ∧ {i | S ∉ p i} ⊆ X}
      univ_sets := ⟨∅,h0,Set.subset_univ _⟩
      sets_of_superset := by
        rintro X Y ⟨S,hS,hX⟩ hXY
        exact ⟨S,hS,hX.trans hXY⟩
      inter_sets := by
        rintro X Y ⟨S,hS,hX⟩ ⟨T,hT,hY⟩
        refine ⟨S ∪ T,hU S T hS hT,?_⟩
        intro i hi
        exact ⟨hX (fun hs => hi (Filter.mem_of_superset hs Set.subset_union_left)),
          hY (fun ht => hi (Filter.mem_of_superset ht Set.subset_union_right))⟩ }
  haveI : F.NeBot := Filter.forall_mem_nonempty_iff_neBot.mp (by
    rintro X ⟨S,hS,hX⟩
    obtain ⟨i,hi⟩ := hbad S hS
    exact ⟨i,hX hi⟩)
  refine ⟨Ultrafilter.of F,?_⟩
  intro S hS
  exact Ultrafilter.of_le F (show {i | S ∉ p i} ∈ F from ⟨S,hS,Set.Subset.rfl⟩)

#print axioms FiniteOn.union
#print axioms avoiding_ultrafilter
end Erdos595FiniteEdgeCoverIdeal
