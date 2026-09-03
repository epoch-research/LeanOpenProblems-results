import Submission.FiniteRootCayley

/-!
Two triangle-free edge pieces do not bound the finite proper chromatic
numbers of earlier neighborhoods, even if the linear order can be chosen
freely. This is NOT an obstruction to countable local colorings and does
not settle Erdos 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595FiniteEarlierNeighborhood
open Erdos595Work Erdos595FiniteRootCayley

variable {V : Type*}

lemma graph_sup (G H : SimpleGraph V) : graph (G ⊔ H) = graph G ⊔ graph H := by
  ext x y
  simp only [graph, SimpleGraph.sup_adj]
  aesop

/-- A translated copy of B lies in every neighborhood of its cone's root graph. -/
noncomputable def neighborhoodHom (B : SimpleGraph V) (t : Option V → ZMod 5) :
    B →g (graph (coneGraph B)).induce ((graph (coneGraph B)).neighborSet t) where
  toFun a := ⟨t + root (some a) none, by
    refine ⟨some a,none,?_,?_⟩
    · trivial
    · abel⟩
  map_rel' := by
    intro a b hab
    refine ⟨some b,some a,hab.symm,?_⟩
    change (t + root (some b) none) - (t + root (some a) none) =
      root (some b) (some a)
    unfold root
    abel

lemma finite_shift_not_colorable (n : ℕ) :
    ¬(orderedShiftGraph (Fin (2 ^ n + 1))).Colorable n := by
  classical
  rintro ⟨c⟩
  obtain ⟨e⟩ := orderedShiftGraph_coloring_injection c
  have h := Fintype.card_le_of_injective e e.injective
  simp only [Fintype.card_fin, Fintype.card_set] at h
  omega

/-- Every finite bound fails, already for finite K4-free Cayley graphs
with TWO triangle-free edge pieces. -/
theorem no_uniform_finite_bound (n : ℕ) :
    ∃ (W : Type) (_ : Finite W) (G : SimpleGraph W),
      G.CliqueFree 4 ∧
      (∃ H K : SimpleGraph W, H.CliqueFree 3 ∧ K.CliqueFree 3 ∧ G = H ⊔ K) ∧
      ∀ o : LinearOrder W, ∃ w : W,
        ¬(G.induce {v | @LT.lt W o.toLT v w ∧ G.Adj w v}).Colorable n := by
  classical
  let A := Fin (2 ^ n + 1)
  let U := {p : A × A // p.1 < p.2}
  let B : SimpleGraph U := orderedShiftGraph A
  have hB : B.CliqueFree 3 := orderedShiftGraph_cliqueFree A
  let W := Option U → ZMod 5
  let G : SimpleGraph W := graph (coneGraph B)
  obtain ⟨H,K,hH,hK,hcov⟩ := coneGraph_two_pieces B hB
  refine ⟨W,inferInstance,G,cliqueFree_four _ (coneGraph_cliqueFree B hB),?_,?_⟩
  · refine ⟨graph H,graph K,cliqueFree_three H hH,cliqueFree_three K hK,?_⟩
    change graph (coneGraph B) = _
    rw [hcov,graph_sup]
  · intro o
    letI : LinearOrder W := o
    obtain ⟨w,_,hw⟩ := Finset.exists_max_image (Finset.univ : Finset W) id
      (Finset.univ_nonempty)
    refine ⟨w,?_⟩
    rintro ⟨c⟩
    let f := neighborhoodHom B w
    let g : B →g G.induce {v | v < w ∧ G.Adj w v} :=
      { toFun := fun a => ⟨(f a).val,
          lt_of_le_of_ne (hw _ (Finset.mem_univ _)) (show G.Adj w (f a).val from (f a).property).ne.symm,
          (f a).property⟩
        map_rel' := fun h => f.map_rel h }
    exact finite_shift_not_colorable n ⟨c.comp g⟩

#print axioms neighborhoodHom
#print axioms finite_shift_not_colorable
#print axioms no_uniform_finite_bound
end Erdos595FiniteEarlierNeighborhood
