import Submission.GraphCircuitCode

/-! Parity and the two-edge serial switch. This auxiliary development does not
prove the missing structural bound on graphical minimal cores. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.GraphSerial
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Remove the two port edges, and replace them by cross-edges, with one
cross-edge controlled by each original port. Ports need not be present. -/
def switch (G : SimpleGraph V) (H : SimpleGraph W) (a b : V) (c d : W) : SimpleGraph (V ⊕ W) where
  Adj
    | .inl x, .inl y => G.Adj x y ∧ s(x,y) ≠ s(a,b)
    | .inr x, .inr y => H.Adj x y ∧ s(x,y) ≠ s(c,d)
    | .inl x, .inr y => (x = a ∧ y = c ∧ G.Adj a b) ∨ (x = b ∧ y = d ∧ H.Adj c d)
    | .inr y, .inl x => (x = a ∧ y = c ∧ G.Adj a b) ∨ (x = b ∧ y = d ∧ H.Adj c d)
  symm := by
    intro x y h
    cases x <;> cases y
    · exact ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2⟩
    · exact h
    · exact h
    · exact ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2⟩
  loopless := by
    intro x
    cases x <;> exact fun h => (h.1).ne rfl

noncomputable instance (G : SimpleGraph V) (H : SimpleGraph W) (a b : V) (c d : W) :
    DecidableRel (switch G H a b c d).Adj := Classical.decRel _

lemma even_degree_of_even_elsewhere (G : SimpleGraph V) (v : V)
    (h : ∀ w, w ≠ v → Even (G.degree w)) : Even (G.degree v) := by
  have hs : Even (∑ w, G.degree w) := by
    rw [G.sum_degrees_eq_twice_card_edges]
    exact even_two.mul_right _
  have hr : Even (∑ w ∈ Finset.univ.erase v, G.degree w) := by
    apply Finset.even_sum
    intro w hw
    exact h w (Finset.mem_erase.mp hw).1
  have he := Finset.sum_erase_add (s := (Finset.univ : Finset V)) (f := fun w => G.degree w) (Finset.mem_univ v)
  rw [← he] at hs
  exact (Nat.even_add.mp hs).mp hr

private def leftReplacement (b : V) (c : W) : V ↪ V ⊕ W where
  toFun x := if x = b then .inr c else .inl x
  inj' := by
    intro x y he
    by_cases hx : x = b <;> by_cases hy : y = b <;> simp [hx,hy] at he ⊢
    exact he

lemma neighbors_left_first (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hab : a ≠ b) :
    (switch G H a b c d).neighborFinset (.inl a) = (G.neighborFinset a).map (leftReplacement b c) := by
  ext x
  cases x with
  | inl x =>
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_map]
    change (G.Adj a x ∧ s(a,x) ≠ s(a,b)) ↔ _
    constructor
    · rintro ⟨hax,hne⟩
      have hxb : x ≠ b := fun h => hne (h ▸ rfl)
      exact ⟨x,hax,by simp [leftReplacement,hxb]⟩
    · rintro ⟨y,hay,he⟩
      by_cases hy : y = b
      · simp [leftReplacement,hy] at he
      · have hyx : y = x := by simpa [leftReplacement,hy] using he
        subst y
        refine ⟨hay,?_⟩
        intro heq
        have hx : x = b := (Sym2.eq_iff.mp heq).elim (fun h => h.2) (fun h => (hab h.1).elim)
        exact hy hx
  | inr x =>
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_map]
    change ((a = a ∧ x = c ∧ G.Adj a b) ∨ (a = b ∧ x = d ∧ H.Adj c d)) ↔ _
    constructor
    · rintro (⟨_,rfl,he⟩ | ⟨he,_,_⟩)
      · exact ⟨b,he,by simp [leftReplacement]⟩
      · exact (hab he).elim
    · rintro ⟨y,hay,he⟩
      by_cases hy : y = b
      · subst y
        have hcx : c = x := by simpa [leftReplacement] using he
        exact Or.inl ⟨rfl,hcx.symm,hay⟩
      · simp [leftReplacement,hy] at he

lemma neighbors_left_other (G : SimpleGraph V) (H : SimpleGraph W) {a b x : V} {c d : W}
    (hxa : x ≠ a) (hxb : x ≠ b) :
    (switch G H a b c d).neighborFinset (.inl x) = (G.neighborFinset x).map Function.Embedding.inl := by
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
  | inr y => simp [SimpleGraph.mem_neighborFinset,switch,hxa,hxb]

lemma neighbors_left_second (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hab : a ≠ b) :
    (switch G H a b c d).neighborFinset (.inl b) =
      ((G.neighborFinset b).erase a).map Function.Embedding.inl ∪
        (if H.Adj c d then {Sum.inr d} else ∅) := by
  ext x
  cases x with
  | inl x =>
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_union,Finset.mem_map,
      Function.Embedding.inl_apply,Sum.inl.injEq,exists_eq_right,Finset.mem_erase]
    have hfalse : Sum.inl x ∉ (if H.Adj c d then ({Sum.inr d} : Finset (V ⊕ W)) else ∅) := by
      split_ifs <;> simp
    rw [iff_false_intro hfalse,or_false]
    change (G.Adj b x ∧ s(b,x) ≠ s(a,b)) ↔ x ≠ a ∧ G.Adj b x
    have he : s(b,x) = s(a,b) ↔ x = a := by
      rw [Sym2.eq_iff]
      simp [hab.symm]
    simp only [ne_eq,he]
    exact and_comm
  | inr x =>
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_union,Finset.mem_map,
      Function.Embedding.inl_apply,Sum.inl_ne_inr,exists_false, false_or]
    change ((b = a ∧ x = c ∧ G.Adj a b) ∨ (b = b ∧ x = d ∧ H.Adj c d)) ↔ _
    by_cases hH : H.Adj c d <;> simp [hab.symm,hH]

lemma degree_left_first (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hab : a ≠ b) : (switch G H a b c d).degree (.inl a) = G.degree a := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,neighbors_left_first G H hab,Finset.card_map,
    SimpleGraph.card_neighborFinset_eq_degree]

lemma degree_left_other (G : SimpleGraph V) (H : SimpleGraph W) {a b x : V} {c d : W}
    (hxa : x ≠ a) (hxb : x ≠ b) : (switch G H a b c d).degree (.inl x) = G.degree x := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,neighbors_left_other G H hxa hxb,Finset.card_map,
    SimpleGraph.card_neighborFinset_eq_degree]

lemma degree_left_second (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hab : a ≠ b) :
    (switch G H a b c d).degree (.inl b) + (if G.Adj a b then 1 else 0) =
      G.degree b + (if H.Adj c d then 1 else 0) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,neighbors_left_second G H hab]
  have hdis : Disjoint (((G.neighborFinset b).erase a).map Function.Embedding.inl)
      (if H.Adj c d then ({Sum.inr d} : Finset (V ⊕ W)) else ∅) := by
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
  by_cases hH : H.Adj c d <;> simp only [hH,if_true,if_false,Finset.card_singleton,Finset.card_empty] <;> omega

#print axioms degree_left_second

lemma degree_left_of_ne_second (G : SimpleGraph V) (H : SimpleGraph W) {a b x : V} {c d : W}
    (hab : a ≠ b) (hxb : x ≠ b) :
    (switch G H a b c d).degree (.inl x) = G.degree x := by
  by_cases hxa : x = a
  · subst x
    exact degree_left_first G H hab
  · exact degree_left_other G H hxa hxb

noncomputable def swapIso (G : SimpleGraph V) (H : SimpleGraph W) (a b : V) (c d : W) :
    switch G H a b c d ≃g switch H G d c b a where
  toEquiv := Equiv.sumComm V W
  map_rel_iff' := by
    intro x y
    cases x <;> cases y <;>
      simp [switch,Sym2.eq_swap,SimpleGraph.adj_comm,and_comm,and_left_comm,or_comm]

lemma degree_swap (G : SimpleGraph V) (H : SimpleGraph W) (a b : V) (c d y : W) :
    (switch G H a b c d).degree (.inr y) = (switch H G d c b a).degree (.inl y) := by
  have h := (swapIso G H a b c d).degree_eq (.inr y)
  simpa only [swapIso,Equiv.sumComm_apply,Sum.swap_inr,
    ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using h.symm

lemma degree_right_of_ne_first (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d y : W}
    (hcd : c ≠ d) (hyc : y ≠ c) :
    (switch G H a b c d).degree (.inr y) = H.degree y := by
  rw [degree_swap]
  exact degree_left_of_ne_second H G hcd.symm hyc

lemma degree_right_first (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hcd : c ≠ d) :
    (switch G H a b c d).degree (.inr c) + (if H.Adj c d then 1 else 0) =
      H.degree c + (if G.Adj a b then 1 else 0) := by
  rw [degree_swap]
  simpa only [SimpleGraph.adj_comm] using degree_left_second H G (a := d) (b := c) (c := b) (d := a) hcd.symm

lemma degree_left_of_match (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hab : a ≠ b) (hm : G.Adj a b ↔ H.Adj c d) (x : V) :
    (switch G H a b c d).degree (.inl x) = G.degree x := by
  by_cases he : x = b
  · subst x
    have h := degree_left_second G H (c := c) (d := d) hab
    simp only [hm] at h
    omega
  · exact degree_left_of_ne_second G H hab he

lemma degree_right_of_match (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hcd : c ≠ d) (hm : G.Adj a b ↔ H.Adj c d) (y : W) :
    (switch G H a b c d).degree (.inr y) = H.degree y := by
  rw [degree_swap]
  exact degree_left_of_match H G hcd.symm (by simpa only [SimpleGraph.adj_comm] using hm.symm) y

/-- An even switched graph uses both cross-edges or neither, and its two
unswitched factors are themselves even. -/
lemma even_switch_iff (G : SimpleGraph V) (H : SimpleGraph W) {a b : V} {c d : W}
    (hab : a ≠ b) (hcd : c ≠ d) :
    (∀ x, Even ((switch G H a b c d).degree x)) ↔
      (∀ x, Even (G.degree x)) ∧ (∀ y, Even (H.degree y)) ∧ (G.Adj a b ↔ H.Adj c d) := by
  constructor
  · intro he
    have hLelse : ∀ x, x ≠ b → Even (G.degree x) := by
      intro x hxb
      have h := he (.inl x)
      rwa [degree_left_of_ne_second G H hab hxb] at h
    have hLb := even_degree_of_even_elsewhere G b hLelse
    have hL : ∀ x, Even (G.degree x) := by
      intro x
      by_cases hx : x = b
      · exact hx ▸ hLb
      · exact hLelse x hx
    have hRelse : ∀ y, y ≠ c → Even (H.degree y) := by
      intro y hyc
      have h := he (.inr y)
      rwa [degree_right_of_ne_first G H hcd hyc] at h
    have hRc := even_degree_of_even_elsewhere H c hRelse
    have hR : ∀ y, Even (H.degree y) := by
      intro y
      by_cases hy : y = c
      · exact hy ▸ hRc
      · exact hRelse y hy
    refine ⟨hL,hR,?_⟩
    have hdeg := degree_left_second G H (c := c) (d := d) hab
    have h1 := Nat.even_iff.mp (he (.inl b))
    have h2 := Nat.even_iff.mp hLb
    by_cases hp : G.Adj a b <;> by_cases hq : H.Adj c d
    · exact iff_of_true hp hq
    · simp only [if_pos hp,if_neg hq] at hdeg
      omega
    · simp only [if_neg hp,if_pos hq] at hdeg
      omega
    · exact iff_of_false hp hq
  · rintro ⟨hG,hH,hm⟩ x
    cases x with
    | inl x => rw [degree_left_of_match G H hab hm]; exact hG x
    | inr y => rw [degree_right_of_match G H hcd hm]; exact hH y

#print axioms even_switch_iff
end Erdos184Work.GraphSerial
