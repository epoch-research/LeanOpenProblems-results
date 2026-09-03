import Submission.BicliquePartition

/-!
Exact edge partitions for reciprocal evaluation graphs. This is an obstruction
to a class of constructions, not a resolution of Erdős 714.
-/

noncomputable section
open Classical SimpleGraph Finset

namespace Erdos714EvaluationInterchange

variable {C D I J A : Type*}

/-- The message on either side is evaluated at the other side's coordinate. -/
def graph (f : C → I → A) (g : D → J → A) : SimpleGraph ((C × J) ⊕ (D × I)) where
  Adj p q := match p,q with
    | .inl x,.inr y => f x.1 y.2 = g y.1 x.2
    | .inr y,.inl x => f x.1 y.2 = g y.1 x.2
    | _,_ => False
  symm := by intro p q; cases p <;> cases q <;> simp
  loopless := by intro p; cases p <;> simp

/-- Only nonempty blocks are indexed, so no lower bound is imposed on empty fibers. -/
abbrev Block (f : C → I → A) (g : D → J → A) :=
  {p : J × I × A // (∃ c, f c p.2.1 = p.2.2) ∧ (∃ d, g d p.1 = p.2.2)}

abbrev LeftFiber (f : C → I → A) (g : D → J → A) (p : Block f g) :=
  {c : C // f c p.val.2.1 = p.val.2.2}

abbrev RightFiber (f : C → I → A) (g : D → J → A) (p : Block f g) :=
  {d : D // g d p.val.1 = p.val.2.2}

/-- The complete block of fixed coordinates and a fixed common evaluation. -/
def blockCopy (f : C → I → A) (g : D → J → A) (p : Block f g) :
    (completeBipartiteGraph (LeftFiber f g p) (RightFiber f g p)).Copy (graph f g) where
  toHom := {
    toFun := Sum.map (fun c => (c.val,p.val.1)) (fun d => (d.val,p.val.2.1))
    map_rel' := by
      intro x y h
      cases x with
      | inl c =>
        cases y with
        | inl c' => simp at h
        | inr d => exact c.property.trans d.property.symm
      | inr d =>
        cases y with
        | inl c => exact c.property.trans d.property.symm
        | inr d' => simp at h }
  injective' := Sum.map_injective.mpr ⟨by
      intro c c' h
      exact Subtype.ext (congrArg Prod.fst h), by
      intro d d' h
      exact Subtype.ext (congrArg Prod.fst h)⟩

lemma edge_rep (f : C → I → A) (g : D → J → A) (e : (graph f g).edgeSet) :
    ∃ c j d i, e.val=s(Sum.inl (c,j),Sum.inr (d,i)) ∧ f c i=g d j := by
  rcases e with ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | hf p q =>
    cases p with
    | inl cj =>
      cases q with
      | inl cj' => exact False.elim he
      | inr di => exact ⟨cj.1,cj.2,di.1,di.2,rfl,he⟩
    | inr di =>
      cases q with
      | inl cj => exact ⟨cj.1,cj.2,di.1,di.2,Sym2.eq_swap,he⟩
      | inr di' => exact False.elim he

/-- Each actual unordered edge has exactly one block index. -/
lemma block_partition (f : C → I → A) (g : D → J → A) :
    Function.Bijective (Erdos714BicliquePartition.edgeMap (graph f g) (blockCopy f g)) := by
  constructor
  · rintro ⟨p,e⟩ ⟨q,e'⟩ hee
    obtain ⟨c,d,he⟩ := Erdos714BicliquePartition.edge_rep e
    obtain ⟨c',d',he'⟩ := Erdos714BicliquePartition.edge_rep e'
    have hh := congrArg Subtype.val hee
    change Sym2.map (blockCopy f g p) e.val = Sym2.map (blockCopy f g q) e'.val at hh
    rw [he,he'] at hh
    change s(Sum.inl (c.val,p.val.1),Sum.inr (d.val,p.val.2.1)) =
      s(Sum.inl (c'.val,q.val.1),Sum.inr (d'.val,q.val.2.1)) at hh
    simp only [Sym2.eq_iff,Prod.mk.injEq,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,false_and,or_false] at hh
    have hpq : p=q := by
      apply Subtype.ext
      apply Prod.ext hh.1.2
      apply Prod.ext hh.2.2
      exact c.property.symm.trans ((congrArg₂ f hh.1.1 hh.2.2).trans c'.property)
    subst q
    have hc : c=c' := Subtype.ext hh.1.1
    have hd : d=d' := Subtype.ext hh.2.1
    have heq : e=e' := Subtype.ext (by rw [he,he',hc,hd])
    subst e'
    rfl
  · intro e
    obtain ⟨c,j,d,i,he,hadj⟩ := edge_rep f g e
    let p : Block f g := ⟨(j,i,f c i),⟨c,rfl⟩,⟨d,hadj.symm⟩⟩
    let c' : LeftFiber f g p := ⟨c,rfl⟩
    let d' : RightFiber f g p := ⟨d,hadj.symm⟩
    let e' : (completeBipartiteGraph (LeftFiber f g p) (RightFiber f g p)).edgeSet :=
      ⟨s(Sum.inl c',Sum.inr d'),by simp⟩
    refine ⟨⟨p,e'⟩,?_⟩
    apply Subtype.ext
    exact he.symm

variable [Fintype C] [Fintype D] [Fintype I] [Fintype J] [Fintype A]

/-- Relative density comparison for arbitrary selected edges. -/
theorem density_bound (f : C → I → A) (g : D → J → A)
    (H : SimpleGraph ((C × J) ⊕ (D × I))) (r t : ℕ)
    (hf : ∀ i a, (∃ c, f c i=a) → t ≤ Fintype.card {c : C // f c i=a})
    (hg : ∀ j a, (∃ d, g d j=a) → t ≤ Fintype.card {d : D // g d j=a})
    (hHG : H ≤ graph f g) (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free H) :
    t^2 * H.edgeFinset.card ≤
      extremalNumber (2*t) (completeBipartiteGraph (Fin r) (Fin r)) * (graph f g).edgeFinset.card := by
  exact Erdos714BicliquePartition.density_bound H _ (blockCopy f g) (block_partition f g)
    r t (fun p => hf _ _ p.property.1) (fun p => hg _ _ p.property.2) hHG hfree

/-- Growing nonempty evaluation fibers prevent positive-density repair. -/
theorem fourth_density_bound (f : C → I → A) (g : D → J → A)
    (H : SimpleGraph ((C × J) ⊕ (D × I))) (t : ℕ)
    (hf : ∀ i a, (∃ c, f c i=a) → t ≤ Fintype.card {c : C // f c i=a})
    (hg : ∀ j a, (∃ d, g d j=a) → t ≤ Fintype.card {d : D // g d j=a})
    (hHG : H ≤ graph f g) (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    t * H.edgeFinset.card ^ 4 ≤ 10368 * (graph f g).edgeFinset.card ^ 4 := by
  exact Erdos714BicliquePartition.fourth_density_bound H _ (blockCopy f g) (block_partition f g)
    t (fun p => hf _ _ p.property.1) (fun p => hg _ _ p.property.2) hHG hfree

/-- A symmetric second partition is obtained by interchanging the roles of
messages and coordinates in both evaluation tables. -/
def transposeIso (f : C → I → A) (g : D → J → A) :
    graph f g ≃g graph (fun j d => g d j) (fun i c => f c i) where
  toEquiv := (Equiv.prodComm C J).sumCongr (Equiv.prodComm D I)
  map_rel_iff' := by
    intro p q
    cases p <;> cases q <;> simp [graph, eq_comm]

#print axioms blockCopy
#print axioms block_partition
#print axioms density_bound
#print axioms fourth_density_bound
#print axioms transposeIso

end Erdos714EvaluationInterchange
