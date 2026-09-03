import Submission.Work

/-!
The middle-corner sufficient coloring rule is strictly stronger than a
countable triangle-free edge cover. Increasing triples with one- and two-step
shift edges provide counterexamples to that rule. This is NOT a disproof of
Erdős Problem 595: the graphs constructed here have two-piece covers.
-/

set_option autoImplicit false

open SimpleGraph Set

namespace Erdos595MiddleCorner

universe u

structure Triple (A : Type*) [LT A] where
  a : A
  b : A
  c : A
  ab : a < b
  bc : b < c

variable {A : Type*} [LinearOrder A]

def One (x y : Triple A) : Prop := x.b = y.a ∧ x.c = y.b

def Two (x y : Triple A) : Prop := x.c = y.a

def Forward (x y : Triple A) : Prop := One x y ∨ Two x y

lemma forward_lt {x y : Triple A} (h : Forward x y) : x.a < y.a := by
  rcases h with ⟨h, _⟩ | h
  · exact h ▸ x.ab
  · exact h ▸ x.ab.trans x.bc

def graph (A : Type*) [LinearOrder A] : SimpleGraph (Triple A) where
  Adj x y := Forward x y ∨ Forward y x
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h.elim (fun h => (lt_irrefl _ (forward_lt h)))
    (fun h => (lt_irrefl _ (forward_lt h)))

lemma first_ne {x y : Triple A} (h : (graph A).Adj x y) : x.a ≠ y.a := by
  rcases h with h | h
  · exact (forward_lt h).ne
  · exact (forward_lt h).ne.symm

lemma forward_of_le {x y : Triple A} (h : (graph A).Adj x y)
    (hle : x.a ≤ y.a) : Forward x y := by
  exact h.resolve_right (fun h => (not_lt_of_ge hle) (forward_lt h))

lemma first_of_forward {x y : Triple A} (h : Forward x y) :
    y.a = x.b ∨ y.a = x.c := by
  rcases h with h | h
  · exact Or.inl h.1.symm
  · exact Or.inr h.symm

/-- Each forward neighborhood has only two possible first coordinates;
vertices with equal first coordinates cannot be adjacent. -/
theorem graph_cliqueFree (A : Type*) [LinearOrder A] : (graph A).CliqueFree 4 := by
  classical
  by_contra h
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree h
  have adj : ∀ i j : Fin 4, i ≠ j → (graph A).Adj (e i) (e j) :=
    fun i j hij => e.map_rel_iff.mpr hij
  have hinj : Function.Injective (fun i : Fin 4 => (e i).a) := by
    intro i j he
    by_contra hij
    exact first_ne (adj i j hij) he
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin 4 => (e i).a) Finset.univ_nonempty
  have hs : Finset.univ.image (fun j : Fin 4 => (e j).a) ⊆
      {(e i).a, (e i).b, (e i).c} := by
    intro v hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    by_cases hij : i = j
    · subst j
      simp
    · have hfirst := first_of_forward
        (forward_of_le (adj i j hij) (hi j (Finset.mem_univ j)))
      rcases hfirst with hfirst | hfirst <;> simp [hfirst]
  have hc := (Finset.card_le_card hs).trans Finset.card_le_three
  have he : (Finset.univ.image (fun j : Fin 4 => (e j).a)).card = 4 := by
    rw [Finset.card_image_of_injective _ hinj]
    decide
  omega

def oneGraph (A : Type*) [LinearOrder A] : SimpleGraph (Triple A) where
  Adj x y := One x y ∨ One y x
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h.elim
    (fun h => lt_irrefl _ (forward_lt (Or.inl h)))
    (fun h => lt_irrefl _ (forward_lt (Or.inl h)))

def twoGraph (A : Type*) [LinearOrder A] : SimpleGraph (Triple A) where
  Adj x y := Two x y ∨ Two y x
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h.elim
    (fun h => lt_irrefl _ (forward_lt (Or.inr h)))
    (fun h => lt_irrefl _ (forward_lt (Or.inr h)))

theorem oneGraph_cliqueFree (A : Type*) [LinearOrder A] :
    (oneGraph A).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ := SimpleGraph.is3Clique_iff.mp ht
  apply Erdos595Work.orderedShiftGraph_cliqueFree A _
  exact SimpleGraph.is3Clique_triple_iff.mpr
    (show (Erdos595Work.orderedShiftGraph A).Adj ⟨(x.a, x.b), x.ab⟩
        ⟨(y.a, y.b), y.ab⟩ ∧
      (Erdos595Work.orderedShiftGraph A).Adj ⟨(x.a, x.b), x.ab⟩
        ⟨(z.a, z.b), z.ab⟩ ∧
      (Erdos595Work.orderedShiftGraph A).Adj ⟨(y.a, y.b), y.ab⟩
        ⟨(z.a, z.b), z.ab⟩ from
      ⟨hxy.imp And.left And.left, hxz.imp And.left And.left,
        hyz.imp And.left And.left⟩)

theorem twoGraph_cliqueFree (A : Type*) [LinearOrder A] :
    (twoGraph A).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ := SimpleGraph.is3Clique_iff.mp ht
  apply Erdos595Work.orderedShiftGraph_cliqueFree A _
  exact SimpleGraph.is3Clique_triple_iff.mpr
    (show (Erdos595Work.orderedShiftGraph A).Adj ⟨(x.a, x.c), x.ab.trans x.bc⟩
        ⟨(y.a, y.c), y.ab.trans y.bc⟩ ∧
      (Erdos595Work.orderedShiftGraph A).Adj ⟨(x.a, x.c), x.ab.trans x.bc⟩
        ⟨(z.a, z.c), z.ab.trans z.bc⟩ ∧
      (Erdos595Work.orderedShiftGraph A).Adj ⟨(y.a, y.c), y.ab.trans y.bc⟩
        ⟨(z.a, z.c), z.ab.trans z.bc⟩ from ⟨hxy, hxz, hyz⟩)

theorem two_pieces (A : Type*) [LinearOrder A] :
    graph A = oneGraph A ⊔ twoGraph A := by
  ext x y
  simp only [graph, oneGraph, twoGraph, Forward, SimpleGraph.sup_adj]
  tauto

theorem graph_cover (A : Type*) [LinearOrder A] :
    Erdos595Work.IsCountableUnionOfTriangleFree (graph A) := by
  let H : ℕ → SimpleGraph (Triple A) := fun n => if n = 0 then oneGraph A else twoGraph A
  refine ⟨H, ?_, ?_⟩
  · intro n
    dsimp only [H]
    split_ifs
    · exact oneGraph_cliqueFree A
    · exact twoGraph_cliqueFree A
  · rw [two_pieces]
    ext x y
    simp only [SimpleGraph.sup_adj, SimpleGraph.iSup_adj]
    constructor
    · rintro (h | h)
      · exact ⟨0, by simpa [H] using h⟩
      · exact ⟨1, by simpa [H] using h⟩
    · rintro ⟨n, h⟩
      dsimp only [H] at h
      split_ifs at h
      · exact Or.inl h
      · exact Or.inr h

/-- This is stronger than merely forbidding monochromatic triangles. -/
def MiddleDifferent {C : Type*} (col : Sym2 (Triple A) → C) : Prop :=
  ∀ x y z, x.a < y.a → y.a < z.a →
    (graph A).Adj x y → (graph A).Adj x z → (graph A).Adj y z →
    col s(x,y) ≠ col s(y,z)

lemma consecutive_of_middle {C : Type*} {col : Sym2 (Triple A) → C}
    (h : MiddleDifferent col) (a b c d e : A)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e) :
    col s(⟨a,b,c,hab,hbc⟩, ⟨b,c,d,hbc,hcd⟩) ≠
      col s(⟨b,c,d,hbc,hcd⟩, ⟨c,d,e,hcd,hde⟩) := by
  apply h _ _ _ hab hbc
  · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inl (Or.inr rfl)
  · exact Or.inl (Or.inl ⟨rfl, rfl⟩)

/-- The outgoing colors of a triple separate consecutive triples. -/
theorem middle_gives_triple_coloring {C : Type*}
    (col : Sym2 (Triple A) → C) (hcol : MiddleDifferent col) :
    ∃ f : Triple A → Set C, ∀ (a b c d : A)
      (hab : a < b) (hbc : b < c) (hcd : c < d),
      f ⟨a,b,c,hab,hbc⟩ ≠ f ⟨b,c,d,hbc,hcd⟩ := by
  let f : Triple A → Set C := fun x => {k | ∃ d, ∃ h : x.c < d,
    col s(x, ⟨x.b,x.c,d,x.bc,h⟩) = k}
  refine ⟨f, ?_⟩
  intro a b c d hab hbc hcd he
  have hm : col s(⟨a,b,c,hab,hbc⟩, ⟨b,c,d,hbc,hcd⟩) ∈
      f ⟨a,b,c,hab,hbc⟩ := ⟨d, hcd, rfl⟩
  rw [he] at hm
  obtain ⟨e, hde, heq⟩ := hm
  exact consecutive_of_middle hcol a b c d e hab hbc hcd hde heq.symm

/-- A proper coloring of consecutive triples gives a shift-pair coloring
by subsets of the original palette. -/
theorem triple_gives_shift_coloring {C : Type*} (f : Triple A → C)
    (hf : ∀ (a b c d : A) (hab : a < b) (hbc : b < c) (hcd : c < d),
      f ⟨a,b,c,hab,hbc⟩ ≠ f ⟨b,c,d,hbc,hcd⟩) :
    Nonempty ((Erdos595Work.orderedShiftGraph A).Coloring (Set C)) := by
  let S : {p : A × A // p.1 < p.2} → Set C := fun p =>
    {k | ∃ c, ∃ h : p.val.2 < c, f ⟨p.val.1,p.val.2,c,p.property,h⟩ = k}
  have valid : ∀ (a b c : A) (hab : a < b) (hbc : b < c),
      S ⟨(a,b),hab⟩ ≠ S ⟨(b,c),hbc⟩ := by
    intro a b c hab hbc he
    have hm : f ⟨a,b,c,hab,hbc⟩ ∈ S ⟨(a,b),hab⟩ := ⟨c,hbc,rfl⟩
    rw [he] at hm
    obtain ⟨d,hcd,heq⟩ := hm
    exact hf a b c d hab hbc hcd heq.symm
  refine ⟨SimpleGraph.Coloring.mk S ?_⟩
  intro x y hxy he
  rcases x with ⟨⟨a,b⟩,hab⟩
  rcases y with ⟨⟨c,d⟩,hcd⟩
  change b = c ∨ d = a at hxy
  rcases hxy with rfl | rfl
  · exact valid a b d hab hcd he
  · exact valid c d b hcd hab he.symm

/-- No cardinal bound on the strength of the middle-corner rule exists,
even among graphs that have two-piece triangle-free edge covers. -/
theorem no_middle_coloring_on_four_powersets (C : Type u) :
    ∃ (A : Type u) (_ : LinearOrder A),
      (graph A).CliqueFree 4 ∧
      Erdos595Work.IsCountableUnionOfTriangleFree (graph A) ∧
      ¬ ∃ col : Sym2 (Triple A) → C, MiddleDifferent col := by
  classical
  let A := Set (Set (Set (Set C)))
  letI : LinearOrder A := IsWellOrder.linearOrder WellOrderingRel
  refine ⟨A, inferInstance, graph_cliqueFree A, graph_cover A, ?_⟩
  rintro ⟨col,hcol⟩
  obtain ⟨f,hf⟩ := middle_gives_triple_coloring col hcol
  obtain ⟨g⟩ := triple_gives_shift_coloring f hf
  obtain ⟨e⟩ := Erdos595Work.orderedShiftGraph_coloring_injection g
  exact Function.cantor_injective e e.injective

#print axioms graph_cliqueFree
#print axioms graph_cover
#print axioms no_middle_coloring_on_four_powersets


/-- The consecutive-window condition can also be imposed on directed pairs. -/
def ConsecutiveDifferent {C : Type*} (col : Triple A → Triple A → C) : Prop :=
  ∀ (a b c d e : A) (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e),
    col ⟨a,b,c,hab,hbc⟩ ⟨b,c,d,hbc,hcd⟩ ≠
      col ⟨b,c,d,hbc,hcd⟩ ⟨c,d,e,hcd,hde⟩

theorem consecutive_gives_triple_coloring {C : Type*}
    (col : Triple A → Triple A → C) (hcol : ConsecutiveDifferent col) :
    ∃ f : Triple A → Set C, ∀ (a b c d : A)
      (hab : a < b) (hbc : b < c) (hcd : c < d),
      f ⟨a,b,c,hab,hbc⟩ ≠ f ⟨b,c,d,hbc,hcd⟩ := by
  let f : Triple A → Set C := fun x => {k | ∃ d, ∃ h : x.c < d,
    col x ⟨x.b,x.c,d,x.bc,h⟩ = k}
  refine ⟨f, ?_⟩
  intro a b c d hab hbc hcd he
  have hm : col ⟨a,b,c,hab,hbc⟩ ⟨b,c,d,hbc,hcd⟩ ∈
      f ⟨a,b,c,hab,hbc⟩ := ⟨d, hcd, rfl⟩
  rw [he] at hm
  obtain ⟨e, hde, heq⟩ := hm
  exact hcol a b c d e hab hbc hcd hde heq.symm

def OrderedMiddleDifferent {C : Type*} (lt : Triple A → Triple A → Prop)
    (col : Sym2 (Triple A) → C) : Prop :=
  ∀ x y z, lt x y → lt y z →
    (graph A).Adj x y → (graph A).Adj x z → (graph A).Adj y z →
    col s(x,y) ≠ col s(y,z)

/-- Appending the orientation bit converts a middle-corner coloring for
an arbitrary vertex order into a consecutive-window coloring. -/
theorem ordered_middle_gives_consecutive {C : Type*}
    (o : LinearOrder (Triple A)) (col : Sym2 (Triple A) → C)
    (hcol : OrderedMiddleDifferent o.lt col) :
    ∃ f : Triple A → Triple A → C × Bool, ConsecutiveDifferent f := by
  letI : LinearOrder (Triple A) := o
  classical
  refine ⟨fun x y => (col s(x,y), decide (x < y)), ?_⟩
  intro a b c d e hab hbc hcd hde he
  let p : Triple A := ⟨a,b,c,hab,hbc⟩
  let q : Triple A := ⟨b,c,d,hbc,hcd⟩
  let r : Triple A := ⟨c,d,e,hcd,hde⟩
  have hpq : p ≠ q := fun h => hab.ne (congrArg Triple.a h)
  have hqr : q ≠ r := fun h => hbc.ne (congrArg Triple.a h)
  have apq : (graph A).Adj p q := Or.inl (Or.inl ⟨rfl,rfl⟩)
  have apr : (graph A).Adj p r := Or.inl (Or.inr rfl)
  have aqr : (graph A).Adj q r := Or.inl (Or.inl ⟨rfl,rfl⟩)
  have hcols : col s(p,q) = col s(q,r) := congrArg Prod.fst he
  have hbits : (p < q ↔ q < r) := by
    have hh := congrArg Prod.snd he
    simpa only [decide_eq_decide] using hh
  rcases lt_or_gt_of_ne hpq with hpq | hqp
  · exact hcol p q r hpq (hbits.mp hpq) apq apr aqr hcols
  · have hn : ¬q < r := fun h => (not_lt_of_ge hqp.le) (hbits.mpr h)
    have hrq : r < q := lt_of_le_of_ne (le_of_not_gt hn) hqr.symm
    apply hcol r q p hrq hqp aqr.symm apr.symm apq.symm
    simpa only [Sym2.eq_swap] using hcols.symm

/-- Even allowing the vertex order to be chosen freely does not repair
this stronger rule. The displayed graphs remain two-piece coverable. -/
theorem no_ordered_middle_coloring (C : Type u) :
    ∃ (A : Type u) (_ : LinearOrder A),
      (graph A).CliqueFree 4 ∧
      Erdos595Work.IsCountableUnionOfTriangleFree (graph A) ∧
      ∀ o : LinearOrder (Triple A),
        ¬ ∃ col : Sym2 (Triple A) → C, OrderedMiddleDifferent o.lt col := by
  classical
  let A := Set (Set (Set (Set (C × Bool))))
  letI : LinearOrder A := IsWellOrder.linearOrder WellOrderingRel
  refine ⟨A, inferInstance, graph_cliqueFree A, graph_cover A, ?_⟩
  intro o
  rintro ⟨col,hcol⟩
  obtain ⟨c,hc⟩ := ordered_middle_gives_consecutive o col hcol
  obtain ⟨f,hf⟩ := consecutive_gives_triple_coloring c hc
  obtain ⟨g⟩ := triple_gives_shift_coloring f hf
  obtain ⟨e⟩ := Erdos595Work.orderedShiftGraph_coloring_injection g
  exact Function.cantor_injective e e.injective

#print axioms no_ordered_middle_coloring

end Erdos595MiddleCorner
