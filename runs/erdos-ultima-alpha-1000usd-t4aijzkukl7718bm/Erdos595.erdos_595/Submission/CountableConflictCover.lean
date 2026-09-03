import Submission.NegativeInner

/-!
Countably supported partial binary assignments give countable triangle-free
edge covers. This needs no clique bound and no topology. It provides a
covering criterion for coordinate-conflict constructions, not a settlement
of Erdős 595.
-/

open SimpleGraph Set
namespace Erdos595CountableConflict

universe u

variable {V I : Type*}

/-- Two partial assignments disagree at a coordinate defined in both. -/
def Conflict (p : V → I → Option Bool) (a b : V) : Prop :=
  ∃ (i : I) (s : Bool), p a i = some s ∧ p b i = some (!s)

/-- Locally countable coordinate supports suffice, although the total
coordinate set and the vertex set can have arbitrary cardinality. -/
theorem countable_cover (G : SimpleGraph V) (p : V → I → Option Bool)
    (hs : ∀ v, {i | p v i ≠ none}.Countable)
    (hG : ∀ a b, G.Adj a b → Conflict p a b) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  classical
  obtain ⟨slot,hslot⟩ := Classical.axiomOfChoice
    (fun v => (Set.countable_iff_exists_injOn.mp (hs v)))
  have hex : ∀ a b (h : G.Adj a b),
      ∃ w : I × Bool, p a w.1 = some w.2 ∧ p b w.1 = some (!w.2) := by
    intro a b h
    obtain ⟨i,s,hi,hj⟩ := hG a b h
    exact ⟨(i,s),hi,hj⟩
  choose w hw using hex
  let code : V → V → ℕ × ℕ × Bool := fun a b =>
    if h : G.Adj a b then (slot a (w a b h).1,slot b (w a b h).1,(w a b h).2)
    else (0,0,false)
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  apply Erdos595NegativeInner.cover_of_ordered_patterns G code
  intro a b c _ _ hab hac hbc ⟨he₁,he₂⟩
  simp only [code,dif_pos hab,dif_pos hac,dif_pos hbc] at he₁ he₂
  have habA : p a (w a b hab).1 ≠ none := by rw [(hw a b hab).1]; exact Option.some_ne_none _
  have hacA : p a (w a c hac).1 ≠ none := by rw [(hw a c hac).1]; exact Option.some_ne_none _
  have hacC : p c (w a c hac).1 ≠ none := by rw [(hw a c hac).2]; exact Option.some_ne_none _
  have hbcC : p c (w b c hbc).1 ≠ none := by rw [(hw b c hbc).2]; exact Option.some_ne_none _
  have hi₁ : (w a b hab).1 = (w a c hac).1 :=
    hslot a habA hacA (congrArg Prod.fst he₁)
  have hi₂ : (w a c hac).1 = (w b c hbc).1 :=
    hslot c hacC hbcC ((congrArg (fun t => t.2.1) he₁).symm.trans
      (congrArg (fun t => t.2.1) he₂))
  have hb : (w a b hab).2 = (w b c hbc).2 := congrArg (fun t => t.2.2) he₂
  have hv := (hw a b hab).2
  rw [hi₁,hi₂,(hw b c hbc).1] at hv
  exact Bool.not_ne_self _ ((Option.some.inj hv).symm.trans hb.symm)

/-- A biclique cover is locally countable if each vertex belongs to only
countably many of its two-sided pieces. The family of pieces may be huge. -/
def LocallyCountableBicliqueCover {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ (I : Type u) (L R : I → Set V),
    (∀ i, Disjoint (L i) (R i)) ∧
    (∀ v, {i | v ∈ L i ∨ v ∈ R i}.Countable) ∧
    (∀ a b, G.Adj a b → ∃ i, (a ∈ L i ∧ b ∈ R i) ∨ (b ∈ L i ∧ a ∈ R i))

/-- In fact the complete rectangles need not be subgraphs of G: it is
enough that they cover its edges and have disjoint sides. -/
theorem cover_of_local_bicliques (G : SimpleGraph V)
    (L R : I → Set V) (hdis : ∀ i, Disjoint (L i) (R i))
    (hlocal : ∀ v, {i | v ∈ L i ∨ v ∈ R i}.Countable)
    (hcover : ∀ a b, G.Adj a b →
      ∃ i, (a ∈ L i ∧ b ∈ R i) ∨ (b ∈ L i ∧ a ∈ R i)) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  classical
  let p : V → I → Option Bool := fun v i =>
    if v ∈ L i then some false else if v ∈ R i then some true else none
  apply countable_cover G p
  · intro v
    apply (hlocal v).mono
    intro i hi
    by_contra hn
    simp only [mem_setOf_eq,not_or] at hn
    simp [p,hn.1,hn.2] at hi
  · intro a b hab
    obtain ⟨i,hi⟩ := hcover a b hab
    rcases hi with ⟨ha,hb⟩ | ⟨hb,ha⟩
    · have hb' : b ∉ L i := fun h => Set.disjoint_left.mp (hdis i) h hb
      exact ⟨i,false,by simp [p,ha],by simp [p,hb',hb]⟩
    · have ha' : a ∉ L i := fun h => Set.disjoint_left.mp (hdis i) h ha
      exact ⟨i,true,by simp [p,ha',ha],by simp [p,hb]⟩

/-- The criterion applies to arbitrary countably supported real coordinate
families whenever each edge has a pair of coefficients of opposite signs.
No summability or norm bound is required. -/
theorem real_sign_cover (G : SimpleGraph V) (f : V → I → ℝ)
    (hs : ∀ v, (Function.support (f v)).Countable)
    (hG : ∀ a b, G.Adj a b → ∃ i, f a i * f b i < 0) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  classical
  let p : V → I → Option Bool := fun v i =>
    if f v i = 0 then none else some (decide (0 < f v i))
  apply countable_cover G p
  · intro v
    apply (hs v).mono
    intro i hi
    change f v i ≠ 0
    intro he
    simp [p,he] at hi
  · intro a b hab
    obtain ⟨i,hi⟩ := hG a b hab
    rcases mul_neg_iff.mp hi with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · refine ⟨i,true,?_,?_⟩
      · simp [p,ne_of_gt ha,ha]
      · simp [p,ne_of_lt hb,not_lt_of_ge (le_of_lt hb)]
    · refine ⟨i,false,?_,?_⟩
      · simp [p,ne_of_lt ha,not_lt_of_ge (le_of_lt ha)]
      · simp [p,ne_of_gt hb,hb]

#print axioms countable_cover
#print axioms cover_of_local_bicliques
#print axioms real_sign_cover
end Erdos595CountableConflict
