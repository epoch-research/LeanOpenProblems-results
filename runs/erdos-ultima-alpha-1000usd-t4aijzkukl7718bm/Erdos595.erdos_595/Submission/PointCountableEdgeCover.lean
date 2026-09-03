import Submission.NegativeInner

/-!
Point-countable unions of countably triangle-free-edge-coverable graphs.
The index family can have arbitrary cardinality. Point-countability concerns
vertices incident to the pieces, not the total number of pieces. This is an
auxiliary closure theorem and does not settle Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595PointCountableEdgeCover
open Erdos595Work

variable {V I : Type*}

/-- A piece is relevant to a vertex when it contains an edge at that vertex. -/
def incident (H : I → SimpleGraph V) (v : V) : Set I :=
  {i | ∃ w, (H i).Adj v w}

/-- Countably many positions at each vertex suffice, even for an arbitrarily
large family of edge pieces. No clique bound on the graphs is assumed. -/
theorem countable_cover (H : I → SimpleGraph V)
    (hpoint : ∀ v, (incident H v).Countable)
    (hH : ∀ i, IsCountableUnionOfTriangleFree (H i)) :
    IsCountableUnionOfTriangleFree (⨆ i, H i) := by
  classical
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  have henc (v : V) : ∃ f : incident H v → ℕ, Function.Injective f := by
    letI : Countable (incident H v) := (hpoint v).to_subtype
    exact exists_injective_nat _
  choose enc hinj using henc
  let pos (v : V) (i : I) : ℕ :=
    if hi : i ∈ incident H v then enc v ⟨i,hi⟩ else 0
  have pos_inj (v : V) (i j : I) (hi : i ∈ incident H v)
      (hj : j ∈ incident H v) (he : pos v i = pos v j) : i = j := by
    simp only [pos,dif_pos hi,dif_pos hj] at he
    exact congrArg Subtype.val (hinj v he)
  choose c hc using fun i => (countable_union_iff_edge_coloring (H i)).mp (hH i)
  let G : SimpleGraph V := ⨆ i, H i
  have hex (a b : V) (hab : G.Adj a b) : ∃ i, (H i).Adj a b :=
    SimpleGraph.iSup_adj.mp hab
  let idx (a b : V) : Option I :=
    if h : G.Adj a b then some (hex a b h).choose else none
  have hidx (a b : V) (h : G.Adj a b) :
      ∃ i, idx a b = some i ∧ (H i).Adj a b := by
    exact ⟨(hex a b h).choose,by simp only [idx,dif_pos h],(hex a b h).choose_spec⟩
  let code (a b : V) : ℕ × ℕ × ℕ := match idx a b with
    | none => (0,0,0)
    | some i => (pos a i,pos b i,c i s(a,b))
  apply Erdos595NegativeInner.cover_of_ordered_patterns G code
  intro a b d _ _ hab had hbd ⟨he₁,he₂⟩
  obtain ⟨i,hi,habi⟩ := hidx a b hab
  obtain ⟨j,hj,hadj⟩ := hidx a d had
  obtain ⟨k,hk,hbdk⟩ := hidx b d hbd
  have hai : i ∈ incident H a := ⟨b,habi⟩
  have haj : j ∈ incident H a := ⟨d,hadj⟩
  have hdj : j ∈ incident H d := ⟨a,hadj.symm⟩
  have hdk : k ∈ incident H d := ⟨b,hbdk.symm⟩
  change code a b = code a d at he₁
  change code a b = code b d at he₂
  simp only [code,hi,hj,hk] at he₁ he₂
  have hij : i = j := pos_inj a i j hai haj (congrArg Prod.fst he₁)
  have hjk : j = k := pos_inj d j k hdj hdk
    ((congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) he₁).symm.trans
      (congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) he₂))
  subst j
  subst k
  exact hc i a b d habi hadj hbdk
    ⟨congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) he₁,
      congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) he₂⟩

/-- The same result applies to a subgraph covered by the pieces. -/
theorem cover_of_le_iSup (G : SimpleGraph V) (H : I → SimpleGraph V)
    (hpoint : ∀ v, (incident H v).Countable)
    (hH : ∀ i, IsCountableUnionOfTriangleFree (H i))
    (hle : G ≤ ⨆ i, H i) : IsCountableUnionOfTriangleFree G := by
  exact countable_union_of_hom (SimpleGraph.Hom.ofLE hle) (countable_cover H hpoint hH)

#print axioms countable_cover

/-- Keep the induced edges on a set, with all other vertices isolated. -/
def spanning (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ S ∧ b ∈ S
  symm := fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := fun _ h => G.loopless _ h.1

lemma spanning_cover (G : SimpleGraph V) (S : Set V)
    (hS : IsCountableUnionOfTriangleFree (G.induce S)) :
    IsCountableUnionOfTriangleFree (spanning G S) := by
  classical
  obtain ⟨c,hc⟩ := (countable_union_iff_edge_coloring _).mp hS
  let col (a b : V) : ℕ := if h : a ∈ S ∧ b ∈ S then
    c s(⟨a,h.1⟩,⟨b,h.2⟩) else 0
  have hsymm (a b : V) : col a b = col b a := by
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
      simp [col,ha,hb,Sym2.eq_swap]
  apply (countable_union_iff_edge_coloring _).mpr
  refine ⟨Sym2.lift ⟨col,hsymm⟩,?_⟩
  intro a b d hab had hbd he
  have ha := hab.2.1
  have hb := hab.2.2
  have hd := had.2.2
  apply hc ⟨a,ha⟩ ⟨b,hb⟩ ⟨d,hd⟩ hab.1 had.1 hbd.1
  simpa only [Sym2.lift_mk,col,dif_pos (And.intro ha hb),
    dif_pos (And.intro ha hd),dif_pos (And.intro hb hd)] using he

/-- A point-countable family of covered induced pieces can be used alongside
one additional covered graph. Every remaining edge must lie in one piece. -/
theorem localization (G K : SimpleGraph V) (S : I → Set V)
    (hpoint : ∀ v, {i | v ∈ S i}.Countable)
    (hK : IsCountableUnionOfTriangleFree K)
    (hS : ∀ i, IsCountableUnionOfTriangleFree (G.induce (S i)))
    (hedge : ∀ a b, G.Adj a b → K.Adj a b ∨ ∃ i, a ∈ S i ∧ b ∈ S i) :
    IsCountableUnionOfTriangleFree G := by
  classical
  let H : Option I → SimpleGraph V := fun i => match i with
    | none => K
    | some i => spanning G (S i)
  apply cover_of_le_iSup G H
  · intro v
    apply ((hpoint v).image Option.some |>.insert none).mono
    intro i hi
    cases i with
    | none => exact Set.mem_insert _ _
    | some i =>
      obtain ⟨w,hw⟩ := hi
      exact Set.mem_insert_of_mem _ (Set.mem_image_of_mem Option.some hw.2.1)
  · intro i
    cases i with
    | none => exact hK
    | some i => exact spanning_cover G (S i) (hS i)
  · intro a b hab
    apply SimpleGraph.iSup_adj.mpr
    rcases hedge a b hab with h | ⟨i,ha,hb⟩
    · exact ⟨none,h⟩
    · exact ⟨some i,hab,ha,hb⟩

/-- In particular, countable coordinate supports can localize a cover.
The coordinate type itself need not be countable. -/
theorem cover_of_countable_supports (G : SimpleGraph V) (s : V → Set I)
    (hs : ∀ v, (s v).Countable)
    (hstar : ∀ i, IsCountableUnionOfTriangleFree (G.induce {v | i ∈ s v}))
    (hedge : ∀ a b, G.Adj a b → (s a ∩ s b).Nonempty) :
    IsCountableUnionOfTriangleFree G := by
  apply localization G ⊥ (fun i => {v | i ∈ s v}) hs
    ⟨fun _ => ⊥,fun _ => SimpleGraph.cliqueFree_bot (by decide),by simp⟩ hstar
  intro a b hab
  exact Or.inr (hedge a b hab)

#print axioms spanning_cover
#print axioms localization
#print axioms cover_of_countable_supports


/-- For finite coordinate supports, each edge may be projected to a different
covered target, indexed by the intersection of its endpoint supports. Each
vertex is incident to only finitely many such pieces. -/
theorem finite_intersection_reduction [DecidableEq I] (G : SimpleGraph V) (s : V → Finset I)
    (W : Finset I → Type*) (K : ∀ F, SimpleGraph (W F)) (f : ∀ F, V → W F)
    (hK : ∀ F, IsCountableUnionOfTriangleFree (K F))
    (hedge : ∀ a b, G.Adj a b →
      (K (s a ∩ s b)).Adj (f (s a ∩ s b) a) (f (s a ∩ s b) b)) :
    IsCountableUnionOfTriangleFree G := by
  classical
  let H : Finset I → SimpleGraph V := fun F =>
    { Adj a b := G.Adj a b ∧ s a ∩ s b = F
      symm := fun _ _ h => ⟨h.1.symm,by simpa only [Finset.inter_comm] using h.2⟩
      loopless := fun _ h => G.loopless _ h.1 }
  apply cover_of_le_iSup G H
  · intro v
    apply (s v).powerset.finite_toSet.countable.mono
    rintro F ⟨w,hw⟩
    apply Finset.mem_powerset.mpr
    change G.Adj v w ∧ s v ∩ s w = F at hw
    rw [← hw.2]
    exact Finset.inter_subset_left
  · intro F
    let j : H F →g K F :=
      { toFun := f F
        map_rel' := by
          intro a b hab
          have hh := hedge a b hab.1
          rw [hab.2] at hh
          exact hh }
    exact countable_union_of_hom j (hK F)
  · intro a b hab
    exact SimpleGraph.iSup_adj.mpr ⟨s a ∩ s b,hab,rfl⟩

#print axioms finite_intersection_reduction

#print axioms cover_of_le_iSup
end Erdos595PointCountableEdgeCover
