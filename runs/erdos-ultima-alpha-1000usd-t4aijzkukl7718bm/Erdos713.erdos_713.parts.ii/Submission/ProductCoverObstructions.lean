import FormalConjecturesUtil

/-! Limitations of two graph-scaling operations. These results do not
prove or disprove the rational-exponent conjecture. -/
open SimpleGraph Finset
namespace Erdos713ProductCover

variable {V U W : Type*}

def tensor (G : SimpleGraph V) (F : SimpleGraph U) : SimpleGraph (V × U) where
  Adj x y := G.Adj x.1 y.1 ∧ F.Adj x.2 y.2
  symm := by intro x y h; exact ⟨h.1.symm,h.2.symm⟩
  loopless := by intro x h; exact G.loopless x.1 h.1

/-- Two stars give an induced complete bipartite subgraph in the tensor
product. No bipartiteness or finiteness assumption on either factor is needed. -/
def starRectangle (G : SimpleGraph V) (F : SimpleGraph U) (v : V) (u : U) :
    completeBipartiteGraph (F.neighborSet u) (G.neighborSet v) ↪g tensor G F where
  toFun := Sum.elim (fun y => (v,y.val)) (fun x => (x.val,u))
  inj' := by
    rintro (a|a) (b|b) h
    · exact congrArg Sum.inl (Subtype.ext (congrArg Prod.snd h))
    · exact (b.property.ne (congrArg Prod.fst h)).elim
    · exact (a.property.ne (congrArg Prod.fst h).symm).elim
    · exact congrArg Sum.inr (Subtype.ext (congrArg Prod.fst h))
  map_rel_iff' := by
    rintro (a|a) (b|b)
    · simp [tensor,completeBipartiteGraph]
    · simp [tensor,completeBipartiteGraph,a.property.symm]
      exact b.property
    · simp [tensor,completeBipartiteGraph,a.property.symm]
      exact b.property
    · simp [tensor,completeBipartiteGraph]

noncomputable def embeddingOfCard [Fintype V] [Fintype U]
    (h : Fintype.card V ≤ Fintype.card U) : V ↪ U :=
  (Fintype.equivFin V).toEmbedding.trans
    ((Fin.castLEEmb h).trans (Fintype.equivFin U).symm.toEmbedding)

lemma bipartite_into_complete (H : SimpleGraph W) (hH : H.IsBipartite)
    (a : W ↪ V) (b : W ↪ U) : H ⊑ completeBipartiteGraph V U := by
  classical
  obtain ⟨χ⟩ := hH
  let f : W → V ⊕ U := fun w => if χ w = 0 then .inl (a w) else .inr (b w)
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · intro x y hxy
    have hχ := χ.valid hxy
    by_cases hx : χ x = 0 <;> by_cases hy : χ y = 0
    · exact (hχ (hx.trans hy.symm)).elim
    · simp [f,hx,hy,completeBipartiteGraph]
    · simp [f,hx,hy,completeBipartiteGraph]
    · have he : χ x = χ y := by omega
      exact (hχ he).elim
  · intro x y hxy
    change f x = f y at hxy
    by_cases hx : χ x = 0 <;> by_cases hy : χ y = 0
    · exact a.injective (by simpa [f,hx,hy] using hxy)
    · simp [f,hx,hy] at hxy
    · simp [f,hx,hy] at hxy
    · exact b.injective (by simpa [f,hx,hy] using hxy)

lemma contains_of_large_degrees [Fintype V] [Fintype U] [Fintype W]
    (H : SimpleGraph W) (hH : H.IsBipartite) (G : SimpleGraph V) (F : SimpleGraph U)
    (v : V) (u : U)
    (hv : Fintype.card W ≤ Nat.card (G.neighborSet v))
    (hu : Fintype.card W ≤ Nat.card (F.neighborSet u)) : H ⊑ tensor G F := by
  classical
  let a : W ↪ F.neighborSet u := embeddingOfCard (by simpa [Nat.card_eq_fintype_card] using hu)
  let b : W ↪ G.neighborSet v := embeddingOfCard (by simpa [Nat.card_eq_fintype_card] using hv)
  exact (bipartite_into_complete H hH a b).trans ⟨(starRectangle G F v u).toCopy⟩

/-- An H-free self-tensor forces the original graph to have bounded degree.
In particular, tensor-stable H-free constructions cannot be superlinear. -/
lemma degree_lt_of_free_self_tensor [Fintype V] [Fintype W]
    (H : SimpleGraph W) (hH : H.IsBipartite) (G : SimpleGraph V)
    (hf : H.Free (tensor G G)) (v : V) :
    Nat.card (G.neighborSet v) < Fintype.card W := by
  by_contra hh
  have hd : Fintype.card W ≤ Nat.card (G.neighborSet v) := by omega
  exact hf (contains_of_large_degrees H hH G G v v hd hd)

lemma linear_edges_of_free_self_tensor [Fintype V] [Fintype W]
    (H : SimpleGraph W) (hH : H.IsBipartite) (G : SimpleGraph V)
    (hf : H.Free (tensor G G)) :
    2 * Nat.card G.edgeSet ≤ (Fintype.card W-1)*Fintype.card V := by
  classical
  have hd : ∀ v : V, G.degree v ≤ Fintype.card W-1 := by
    intro v
    have hh := degree_lt_of_free_self_tensor H hH G hf v
    simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] at hh
    omega
  have hh := Finset.sum_le_sum (s := (univ : Finset V)) (fun v _ => hd v)
  rw [G.sum_degrees_eq_twice_card_edges] at hh
  simpa only [sum_const,card_univ,Nat.nsmul_eq_mul,edgeFinset_card,
    Fintype.card_eq_nat_card,mul_comm] using hh

/-- The vertex map induced by a graph homomorphism on a neighbourhood. -/
def neighborMap {G : SimpleGraph V} {F : SimpleGraph U} (f : G →g F) (v : V) :
    G.neighborSet v → F.neighborSet (f v) := fun w => ⟨f w.val,f.map_adj w.property⟩

def IsCover {G : SimpleGraph V} {F : SimpleGraph U} (f : G →g F) : Prop :=
  Function.Surjective f ∧ ∀ v, Function.Bijective (neighborMap f v)

lemma cover_degree {G : SimpleGraph V} {F : SimpleGraph U} (f : G →g F)
    (hf : IsCover f) (v : V) :
    Nat.card (G.neighborSet v) = Nat.card (F.neighborSet (f v)) :=
  Nat.card_congr (Equiv.ofBijective (neighborMap f v) (hf.2 v))

def toFour (i : Fin 8) : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩

def octagonCover : cycleGraph 8 →g cycleGraph 4 :=
  ⟨toFour,by decide⟩

lemma octagonCover_isCover : IsCover octagonCover := by
  unfold IsCover
  decide

/-- A finite cover of a C8-free graph can contain C8. Thus forbidding a
particular cycle is not inherited by arbitrary graph covers. -/
theorem cover_does_not_preserve_C8 :
    (cycleGraph 8).Free (cycleGraph 4) ∧ IsCover octagonCover ∧
      ¬ (cycleGraph 8).Free (cycleGraph 8) := by
  refine ⟨?_,octagonCover_isCover,fun h => h ⟨Copy.id _⟩⟩
  rintro ⟨f⟩
  have hh := Fintype.card_le_of_injective f f.injective
  norm_num at hh

#print axioms starRectangle
#print axioms contains_of_large_degrees
#print axioms degree_lt_of_free_self_tensor
#print axioms linear_edges_of_free_self_tensor
#print axioms cover_degree
#print axioms cover_does_not_preserve_C8
end Erdos713ProductCover
