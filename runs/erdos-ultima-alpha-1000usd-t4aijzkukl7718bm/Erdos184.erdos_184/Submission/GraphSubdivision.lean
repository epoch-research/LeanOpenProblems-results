import Submission.GraphSerialTheory
import Submission.PointCode

/-! A single-edge series subdivision, including its parity characterization.
This is an auxiliary structural reduction, not a proof of Erdős 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.GraphSubdivision
open Erdos184Serial
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two new half-edges are independently controlled by the old port
and the extra coordinate. Evenness will force their controls to match. -/
def split (G : SimpleGraph V) (t : Finset Unit) (a b : V) : SimpleGraph (V ⊕ Unit) where
  Adj
    | .inl x, .inl y => G.Adj x y ∧ s(x,y) ≠ s(a,b)
    | .inl x, .inr _ => (x = a ∧ G.Adj a b) ∨ (x = b ∧ () ∈ t)
    | .inr _, .inl x => (x = a ∧ G.Adj a b) ∨ (x = b ∧ () ∈ t)
    | .inr _, .inr _ => False
  symm := by
    intro x y h
    cases x <;> cases y
    · exact ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2⟩
    · exact h
    · exact h
    · exact h
  loopless := by
    intro x
    cases x
    · exact fun h => h.1.ne rfl
    · exact id

noncomputable instance (G : SimpleGraph V) (t : Finset Unit) (a b : V) :
    DecidableRel (split G t a b).Adj := Classical.decRel _

private def replacement (b : V) : V ↪ V ⊕ Unit where
  toFun x := if x = b then .inr () else .inl x
  inj' := by
    intro x y he
    by_cases hx : x = b <;> by_cases hy : y = b <;> simp [hx,hy] at he ⊢
    exact he

lemma neighbors_first (G : SimpleGraph V) (t : Finset Unit) {a b : V} (hab : a ≠ b) :
    (split G t a b).neighborFinset (.inl a) = (G.neighborFinset a).map (replacement b) := by
  ext x
  cases x with
  | inl x =>
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_map]
    change (G.Adj a x ∧ s(a,x) ≠ s(a,b)) ↔ _
    constructor
    · rintro ⟨hax,hne⟩
      have hxb : x ≠ b := fun h => hne (h ▸ rfl)
      exact ⟨x,hax,by simp [replacement,hxb]⟩
    · rintro ⟨y,hay,he⟩
      by_cases hy : y = b
      · simp [replacement,hy] at he
      · have hyx : y = x := by simpa [replacement,hy] using he
        subst y
        refine ⟨hay,?_⟩
        intro heq
        have hx : x = b := (Sym2.eq_iff.mp heq).elim (fun h => h.2) (fun h => (hab h.1).elim)
        exact hy hx
  | inr x =>
    cases x
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_map]
    change ((a = a ∧ G.Adj a b) ∨ (a = b ∧ () ∈ t)) ↔ _
    constructor
    · rintro (⟨_,he⟩ | ⟨he,_⟩)
      · exact ⟨b,he,by simp [replacement]⟩
      · exact (hab he).elim
    · rintro ⟨y,hay,he⟩
      by_cases hy : y = b
      · subst y
        exact Or.inl ⟨rfl,hay⟩
      · simp [replacement,hy] at he

lemma neighbors_other (G : SimpleGraph V) (t : Finset Unit) {a b x : V}
    (hxa : x ≠ a) (hxb : x ≠ b) :
    (split G t a b).neighborFinset (.inl x) = (G.neighborFinset x).map Function.Embedding.inl := by
  ext y
  cases y with
  | inl y =>
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_map,Function.Embedding.inl_apply,Sum.inl.injEq,
      exists_eq_right]
    change (G.Adj x y ∧ s(x,y) ≠ s(a,b)) ↔ G.Adj x y
    have hn : s(x,y) ≠ s(a,b) := by
      intro he
      rcases Sym2.eq_iff.mp he with ⟨he,_⟩ | ⟨he,_⟩
      · exact hxa he
      · exact hxb he
    exact and_iff_left hn
  | inr y => simp [SimpleGraph.mem_neighborFinset,split,hxa,hxb]

lemma neighbors_second (G : SimpleGraph V) (t : Finset Unit) {a b : V} (hab : a ≠ b) :
    (split G t a b).neighborFinset (.inl b) =
      ((G.neighborFinset b).erase a).map Function.Embedding.inl ∪
        (if () ∈ t then {Sum.inr ()} else ∅) := by
  ext x
  cases x with
  | inl x =>
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_union,Finset.mem_map,
      Function.Embedding.inl_apply,Sum.inl.injEq,exists_eq_right,Finset.mem_erase]
    have hfalse : Sum.inl x ∉ (if () ∈ t then ({Sum.inr ()} : Finset (V ⊕ Unit)) else ∅) := by
      split_ifs <;> simp
    rw [iff_false_intro hfalse,or_false]
    change (G.Adj b x ∧ s(b,x) ≠ s(a,b)) ↔ x ≠ a ∧ G.Adj b x
    have he : s(b,x) = s(a,b) ↔ x = a := by
      rw [Sym2.eq_iff]
      simp [hab.symm]
    simp only [ne_eq,he]
    exact and_comm
  | inr x =>
    cases x
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_union,Finset.mem_map,
      Function.Embedding.inl_apply,Sum.inl_ne_inr,exists_false,false_or]
    change ((b = a ∧ G.Adj a b) ∨ (b = b ∧ () ∈ t)) ↔ _
    by_cases ht : () ∈ t <;> simp [hab.symm,ht]

lemma degree_first (G : SimpleGraph V) (t : Finset Unit) {a b : V} (hab : a ≠ b) :
    (split G t a b).degree (.inl a) = G.degree a := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,neighbors_first G t hab,Finset.card_map,
    SimpleGraph.card_neighborFinset_eq_degree]

lemma degree_other (G : SimpleGraph V) (t : Finset Unit) {a b x : V}
    (hxa : x ≠ a) (hxb : x ≠ b) : (split G t a b).degree (.inl x) = G.degree x := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,neighbors_other G t hxa hxb,Finset.card_map,
    SimpleGraph.card_neighborFinset_eq_degree]

lemma degree_second (G : SimpleGraph V) (t : Finset Unit) {a b : V} (hab : a ≠ b) :
    (split G t a b).degree (.inl b) + (if G.Adj a b then 1 else 0) =
      G.degree b + (if () ∈ t then 1 else 0) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,neighbors_second G t hab]
  have hdis : Disjoint (((G.neighborFinset b).erase a).map Function.Embedding.inl)
      (if () ∈ t then ({Sum.inr ()} : Finset (V ⊕ Unit)) else ∅) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨y,hy',rfl⟩ := Finset.mem_map.mp hx
    split_ifs at hy <;> simp at hy
  rw [Finset.card_union_of_disjoint hdis,Finset.card_map]
  have hc : ((G.neighborFinset b).erase a).card + (if G.Adj a b then 1 else 0) = G.degree b := by
    by_cases he : G.Adj a b
    · have ha : a ∈ G.neighborFinset b := (G.mem_neighborFinset b a).mpr he.symm
      rw [if_pos he,Finset.card_erase_add_one ha,SimpleGraph.card_neighborFinset_eq_degree]
    · have ha : a ∉ G.neighborFinset b := fun h => he ((G.mem_neighborFinset b a).mp h).symm
      rw [if_neg he,Finset.erase_eq_of_notMem ha,add_zero,SimpleGraph.card_neighborFinset_eq_degree]
  by_cases ht : () ∈ t <;> simp only [ht,if_true,if_false,Finset.card_singleton,Finset.card_empty] <;> omega

lemma degree_of_ne_second (G : SimpleGraph V) (t : Finset Unit) {a b x : V}
    (hab : a ≠ b) (hxb : x ≠ b) : (split G t a b).degree (.inl x) = G.degree x := by
  by_cases hxa : x = a
  · subst x
    exact degree_first G t hab
  · exact degree_other G t hxa hxb

lemma degree_old_of_match (G : SimpleGraph V) (t : Finset Unit) {a b : V}
    (hab : a ≠ b) (hm : G.Adj a b ↔ () ∈ t) (x : V) :
    (split G t a b).degree (.inl x) = G.degree x := by
  by_cases hx : x = b
  · subst x
    have h := degree_second G t hab
    have he : (if G.Adj a b then 1 else 0 : ℕ) = (if () ∈ t then 1 else 0) := if_congr hm rfl rfl
    rw [he] at h
    omega
  · exact degree_of_ne_second G t hab hx

lemma even_split_iff (G : SimpleGraph V) (t : Finset Unit) {a b : V} (hab : a ≠ b) :
    (∀ x, Even ((split G t a b).degree x)) ↔
      (∀ x, Even (G.degree x)) ∧ (G.Adj a b ↔ () ∈ t) := by
  constructor
  · intro he
    have hElse : ∀ x, x ≠ b → Even (G.degree x) := by
      intro x hxb
      have h := he (.inl x)
      rwa [degree_of_ne_second G t hab hxb] at h
    have hb := GraphSerial.even_degree_of_even_elsewhere G b hElse
    refine ⟨fun x => by
      by_cases hx : x = b
      · exact hx ▸ hb
      · exact hElse x hx,?_⟩
    have hdeg := degree_second G t hab
    have h1 := Nat.even_iff.mp (he (.inl b))
    have h2 := Nat.even_iff.mp hb
    by_cases hp : G.Adj a b <;> by_cases ht : () ∈ t
    · exact iff_of_true hp ht
    · simp only [if_pos hp,if_neg ht] at hdeg
      omega
    · simp only [if_neg hp,if_pos ht] at hdeg
      omega
    · exact iff_of_false hp ht
  · rintro ⟨hG,hm⟩
    have hElse : ∀ x, x ≠ Sum.inr () → Even ((split G t a b).degree x) := by
      intro x hx
      cases x with
      | inl x => rw [degree_old_of_match G t hab hm]; exact hG x
      | inr u => cases u; exact (hx rfl).elim
    have hNew := GraphSerial.even_degree_of_even_elsewhere (split G t a b) (Sum.inr ()) hElse
    intro x
    by_cases hx : x = Sum.inr ()
    · exact hx ▸ hNew
    · exact hElse x hx

#print axioms even_split_iff
end Erdos184Work.GraphSubdivision
