import Submission.TranslatedFibers
import Submission.BicliquePartition

/-!
The edges in a translated-fiber graph partition into growing bicliques.
Consequently even arbitrary edge thinnings lose relative density.
Unlike the two-connection obstruction, this works in every characteristic.
This is not a resolution of Erdős 714.
-/

noncomputable section
open SimpleGraph Classical

namespace Erdos714TranslatedFiberThinning

variable {A B G : Type*} [Ring G]
open Erdos714TranslatedFibers

/-- For fixed `(z,b)`, all the rows `(z-β(a,b),a)` have the same neighborhood
`S-z` within column label `b`. -/
def blockCopy (β : A → B → G) (S : Finset G) (p : G × B) :
    (completeBipartiteGraph A S).Copy (graph β (S : Set G)) where
  toHom := {
    toFun := Sum.map (fun a => (p.1 - β a p.2,a)) (fun s => ((s : G)-p.1,p.2))
    map_rel' := by
      have he (a : A) (s : S) :
          p.1 - β a p.2 + ((s : G)-p.1) + β a p.2 ∈ S := by
        convert s.property using 1
        abel
      intro x y h
      cases x <;> cases y <;> simp_all [graph] }
  injective' := Sum.map_injective.mpr ⟨by
      intro a a' h
      exact congrArg Prod.snd h, by
      intro s s' h
      apply Subtype.ext
      exact sub_left_inj.mp (congrArg Prod.fst h)⟩

lemma edge_rep (β : A → B → G) (S : Finset G)
    (e : (graph β (S : Set G)).edgeSet) :
    ∃ x a y b, e.val = s(Sum.inl (x,a),Sum.inr (y,b)) ∧ x+y+β a b ∈ S := by
  rcases e with ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | hf p q =>
    cases p with
    | inl xa =>
      cases q with
      | inl xa' => exact False.elim he
      | inr yb => exact ⟨xa.1,xa.2,yb.1,yb.2,rfl,he⟩
    | inr yb =>
      cases q with
      | inl xa => exact ⟨xa.1,xa.2,yb.1,yb.2,Sym2.eq_swap,he⟩
      | inr yb' => exact False.elim he

/-- An exact partition of actual unordered edges; the blocks need not be
vertex-disjoint. The unique block of an edge is `(x+β(a,b),b)`. -/
lemma block_partition (β : A → B → G) (S : Finset G) :
    Function.Bijective (Erdos714BicliquePartition.edgeMap
      (graph β (S : Set G)) (blockCopy β S)) := by
  constructor
  · rintro ⟨⟨z,b⟩,e⟩ ⟨⟨z',b'⟩,e'⟩ hh
    obtain ⟨a,s,he⟩ := Erdos714BicliquePartition.edge_rep e
    obtain ⟨a',s',he'⟩ := Erdos714BicliquePartition.edge_rep e'
    have hv := congrArg Subtype.val hh
    change Sym2.map (blockCopy β S (z,b)) e.val =
      Sym2.map (blockCopy β S (z',b')) e'.val at hv
    rw [he,he'] at hv
    change s(Sum.inl (z-β a b,a),Sum.inr ((s : G)-z,b)) =
      s(Sum.inl (z'-β a' b',a'),Sum.inr ((s' : G)-z',b')) at hv
    simp only [Sym2.eq_iff,Prod.mk.injEq,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,false_and,or_false] at hv
    have ha := hv.1.2
    have hb := hv.2.2
    subst a'
    subst b'
    have hz : z=z' := sub_left_inj.mp hv.1.1
    subst z'
    have hs : s=s' := Subtype.ext (sub_left_inj.mp hv.2.1)
    have hee : e=e' := Subtype.ext (by rw [he,he',hs])
    subst e'
    rfl
  · intro e
    obtain ⟨x,a,y,b,he,hadj⟩ := edge_rep β S e
    let p : G × B := (x+β a b,b)
    let s : S := ⟨x+y+β a b,hadj⟩
    let e' : (completeBipartiteGraph A S).edgeSet :=
      ⟨s(Sum.inl a,Sum.inr s),by simp⟩
    refine ⟨⟨p,e'⟩,?_⟩
    apply Subtype.ext
    change s(Sum.inl (x+β a b-β a b,a),Sum.inr ((x+y+β a b)-(x+β a b),b)) = e.val
    rw [he]
    have hy : x+y+β a b-(x+β a b)=y := by abel
    simp [hy]

/-- Even the full graph has `K_(|A|,|S|)` blocks in every characteristic. -/
theorem not_free_of_large_fibers [Fintype A] (β : A → B → G) (S : Finset G)
    (b : B) (hA : 4 ≤ Fintype.card A) (hS : 4 ≤ S.card) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph β (S : Set G)) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := A)
    (by simpa using hA)
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := S)
    (by simpa using hS)
  let c : (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (completeBipartiteGraph A S) :=
    ⟨⟨e.sumMap f,by intro p q hpq; cases p <;> cases q <;> simp_all⟩,(e.sumMap f).injective⟩
  intro hfree
  exact hfree ⟨(blockCopy β S (0,b)).comp c⟩

variable [Fintype A] [Fintype B] [Fintype G]

/-- General finite density comparison, valid for any forbidden balanced biclique. -/
theorem density_bound (β : A → B → G) (S : Finset G)
    (H : SimpleGraph ((G × A) ⊕ (G × B))) (r t : ℕ)
    (hA : t ≤ Fintype.card A) (hS : t ≤ S.card)
    (hHG : H ≤ graph β (S : Set G))
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free H) :
    t^2 * H.edgeFinset.card ≤
      extremalNumber (2*t) (completeBipartiteGraph (Fin r) (Fin r)) *
        (graph β (S : Set G)).edgeFinset.card := by
  exact Erdos714BicliquePartition.density_bound H _ (blockCopy β S) (block_partition β S)
    r t (fun _ => hA) (fun _ => by simpa using hS) hHG hfree

/-- The retained edge fraction is `O(t^(-1/4))`, uniformly in the voltage table. -/
theorem fourth_density_bound (β : A → B → G) (S : Finset G)
    (H : SimpleGraph ((G × A) ⊕ (G × B))) (t : ℕ)
    (hA : t ≤ Fintype.card A) (hS : t ≤ S.card)
    (hHG : H ≤ graph β (S : Set G))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    t * H.edgeFinset.card ^ 4 ≤ 10368 * (graph β (S : Set G)).edgeFinset.card ^ 4 := by
  exact Erdos714BicliquePartition.fourth_density_bound H _ (blockCopy β S) (block_partition β S)
    t (fun _ => hA) (fun _ => by simpa using hS) hHG hfree

/-- Keeping a fixed reciprocal fraction forces a bound on the smaller block side. -/
theorem density_budget (β : A → B → G) (S : Finset G)
    (H : SimpleGraph ((G × A) ⊕ (G × B))) (t K : ℕ)
    (hA : t ≤ Fintype.card A) (hS : t ≤ S.card)
    (hHG : H ≤ graph β (S : Set G))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (he : 0 < H.edgeFinset.card)
    (hkeep : (graph β (S : Set G)).edgeFinset.card ≤ K * H.edgeFinset.card) :
    t ≤ 10368 * K^4 := by
  have hh := fourth_density_bound β S H t hA hS hHG hfree
  have hk := Nat.pow_le_pow_left hkeep 4
  rw [mul_pow] at hk
  have hb := hh.trans (Nat.mul_le_mul_left 10368 hk)
  apply Nat.le_of_mul_le_mul_right (c := H.edgeFinset.card^4) ?_ (pow_pos he 4)
  simpa only [mul_assoc] using hb

#print axioms blockCopy
#print axioms block_partition
#print axioms not_free_of_large_fibers
#print axioms density_bound
#print axioms fourth_density_bound
#print axioms density_budget

end Erdos714TranslatedFiberThinning
