import Submission.Work

/-!
Countable partial valid edge colorings need not satisfy any fixed chain
condition, even over a K4-free graph with a two-piece triangle-free edge
cover. The partial domains form a delta system with an independent common
root. This is an obstruction to a forcing shortcut, not a settlement of
Erdos 595.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open SimpleGraph Set
namespace Erdos595CountablePartialAntichain

variable {V I : Type*}

/-- Validity is required only for triangles inside the domain. -/
def ValidOn (G : SimpleGraph V) (S : Set V) (c : Sym2 V → ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ d ∈ S,
    G.Adj a b → G.Adj a d → G.Adj b d →
      ¬(c s(a,b) = c s(a,d) ∧ c s(a,b) = c s(b,d))

structure PartialColoring (G : SimpleGraph V) where
  domain : Set V
  countable : domain.Countable
  color : Sym2 V → ℕ
  valid : ValidOn G domain color

/-- Only colors of actual edges must be preserved. -/
def Extends {G : SimpleGraph V} (q p : PartialColoring G) : Prop :=
  p.domain ⊆ q.domain ∧
    ∀ a ∈ p.domain, ∀ b ∈ p.domain, G.Adj a b →
      q.color s(a,b) = p.color s(a,b)

lemma extends_refl {G : SimpleGraph V} (p : PartialColoring G) : Extends p p :=
  ⟨Subset.rfl,fun _ _ _ _ _ => rfl⟩

lemma extends_trans {G : SimpleGraph V} {p q r : PartialColoring G}
    (hpq : Extends p q) (hqr : Extends q r) : Extends p r :=
  ⟨hqr.1.trans hpq.1,fun a ha b hb hab =>
    (hpq.2 a (hqr.1 ha) b (hqr.1 hb) hab).trans (hqr.2 a ha b hb hab)⟩

abbrev Vertex (I : Type*) := ℕ ⊕ (I × Bool)

def graph (I : Type*) : SimpleGraph (Vertex I) where
  Adj
    | .inl _, .inl _ => False
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr a, .inr b => a.1 ≠ b.1 ∧ a.2 ≠ b.2
  symm := by
    intro a b h
    cases a <;> cases b
    · exact h
    · trivial
    · trivial
    · exact ⟨h.1.symm,h.2.symm⟩
  loopless := by
    intro a h
    cases a
    · exact h
    · exact h.1 rfl

def vertexColor : Vertex I → Fin 3
  | .inl _ => 0
  | .inr (_,false) => 1
  | .inr (_,true) => 2

def properColoring (I : Type*) : (graph I).Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk vertexColor (by
    intro a b hab he
    cases a with
    | inl a =>
      cases b with
      | inl b => exact hab
      | inr b => cases b with | mk i t => cases t <;> simp [vertexColor] at he
    | inr a =>
      cases b with
      | inl b => cases a with | mk i t => cases t <;> simp [vertexColor] at he
      | inr b =>
        rcases a with ⟨i,s⟩
        rcases b with ⟨j,t⟩
        have hst : s ≠ t := hab.2
        cases s <;> cases t <;> simp_all [vertexColor])

theorem cliqueFree (I : Type*) : (graph I).CliqueFree 4 :=
  (show (graph I).Colorable 3 from ⟨properColoring I⟩).cliqueFree (by decide)

def rootPiece (I : Type*) : SimpleGraph (Vertex I) where
  Adj a b := (graph I).Adj a b ∧ a.isLeft ≠ b.isLeft
  symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
  loopless := fun _ h => h.2 rfl

def privatePiece (I : Type*) : SimpleGraph (Vertex I) where
  Adj a b := (graph I).Adj a b ∧ ¬a.isLeft ∧ ¬b.isLeft
  symm := fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := fun _ h => (graph I).loopless _ h.1

theorem rootPiece_triangleFree (I : Type*) : (rootPiece I).CliqueFree 3 := by
  have hc : (rootPiece I).Colorable 2 :=
    (SimpleGraph.Coloring.mk (G := rootPiece I) Sum.isLeft (fun h => h.2)).colorable
  exact hc.cliqueFree (by decide)

theorem privatePiece_triangleFree (I : Type*) : (privatePiece I).CliqueFree 3 := by
  let c : Vertex I → Bool := fun a => match a with
    | .inl _ => false
    | .inr x => x.2
  have hc : (privatePiece I).Colorable 2 :=
    (SimpleGraph.Coloring.mk (G := privatePiece I) c (by
      intro a b hab he
      cases a <;> cases b
      · exact hab.2.1 rfl
      · exact hab.2.1 rfl
      · exact hab.2.2 rfl
      · exact hab.1.2 he)).colorable
  exact hc.cliqueFree (by decide)

theorem two_cover (I : Type*) :
    graph I = rootPiece I ⊔ privatePiece I := by
  ext a b
  cases a <;> cases b <;>
    simp [graph,rootPiece,privatePiece,SimpleGraph.sup_adj]

def roots (I : Type*) : Set (Vertex I) := Set.range Sum.inl

def domain (i : I) : Set (Vertex I) :=
  roots I ∪ {Sum.inr (i,false),Sum.inr (i,true)}

@[simp] lemma root_mem (i : I) (n : ℕ) : Sum.inl n ∈ domain i := by
  simp [domain,roots]

@[simp] lemma private_mem (i j : I) (t : Bool) : Sum.inr (j,t) ∈ domain i ↔ j = i := by
  cases t <;> simp [domain,roots]

lemma domain_countable (i : I) : (domain i).Countable :=
  (Set.countable_range Sum.inl).union (Set.toFinite _).countable

lemma domain_triangleFree (i : I) : ((graph I).induce (domain i)).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  have hi {x y : domain i} : (graph I).Adj x.val y.val → x.val.isLeft ≠ y.val.isLeft := by
    intro h he
    rcases x with ⟨x,hx⟩
    rcases y with ⟨y,hy⟩
    cases x <;> cases y
    · exact h
    · simp at he
    · simp at he
    · exact h.1 ((private_mem i _ _).mp hx |>.trans ((private_mem i _ _).mp hy).symm)
  have hab' := hi hab
  have hac' := hi hac
  have hbc' := hi hbc
  cases ha : a.val.isLeft <;> cases hb : b.val.isLeft <;> cases hc : c.val.isLeft <;>
    simp_all

lemma domain_inter {i j : I} (hij : i ≠ j) : domain i ∩ domain j = roots I := by
  ext a
  cases a with
  | inl n => simp [roots]
  | inr p =>
    rcases p with ⟨k,t⟩
    simp only [Set.mem_inter_iff,private_mem]
    simp [roots]
    exact fun hki hkj => hij (hki.symm.trans hkj)

def pairColor : Vertex I → Vertex I → ℕ
  | .inl _, .inl _ => 0
  | .inl n, .inr _ => n
  | .inr _, .inl n => n
  | .inr _, .inr _ => 0

def color : Sym2 (Vertex I) → ℕ := Sym2.lift ⟨pairColor,by
  intro a b
  cases a <;> cases b <;> rfl⟩

def condition (i : I) : PartialColoring (graph I) where
  domain := domain i
  countable := domain_countable i
  color := color
  valid := by
    classical
    intro a ha b hb c hc hab hac hbc _
    exact domain_triangleFree i _ (SimpleGraph.is3Clique_triple_iff.mpr
      (show ((graph I).induce (domain i)).Adj ⟨a,ha⟩ ⟨b,hb⟩ ∧
        ((graph I).induce (domain i)).Adj ⟨a,ha⟩ ⟨c,hc⟩ ∧
        ((graph I).induce (domain i)).Adj ⟨b,hb⟩ ⟨c,hc⟩ from ⟨hab,hac,hbc⟩))

/-- Distinct conditions have no common extension, despite equal root data.
The color of the missing private cross edge selects the obstructing root. -/
theorem incompatible {i j : I} (hij : i ≠ j) :
    ¬∃ q : PartialColoring (graph I), Extends q (condition i) ∧ Extends q (condition j) := by
  rintro ⟨q,hqi,hqj⟩
  let a : Vertex I := .inr (i,false)
  let b : Vertex I := .inr (j,true)
  let n := q.color s(a,b)
  let r : Vertex I := .inl n
  have ha : a ∈ (condition i).domain := (private_mem i i false).mpr rfl
  have hb : b ∈ (condition j).domain := (private_mem j j true).mpr rfl
  have hri : r ∈ (condition i).domain := root_mem i n
  have hrj : r ∈ (condition j).domain := root_mem j n
  have hra : (graph I).Adj r a := True.intro
  have hrb : (graph I).Adj r b := True.intro
  have hab : (graph I).Adj a b := ⟨hij,Bool.false_ne_true⟩
  have he₁ : q.color s(r,a) = n := hqi.2 r hri a ha hra
  have he₂ : q.color s(r,b) = n := hqj.2 r hrj b hb hrb
  exact q.valid r (hqi.1 hri) a (hqi.1 ha) b (hqj.1 hb) hra hrb hab
    ⟨he₁.trans he₂.symm,he₁⟩

theorem condition_injective (I : Type*) : Function.Injective (condition (I := I)) := by
  intro i j he
  by_contra hij
  apply incompatible hij
  exact ⟨condition i,extends_refl _,he ▸ extends_refl _⟩

/-- The ambient graph is already countably covered; incompatibility of
prescribed partial colors is not a covering obstruction. -/
theorem ambient_covered (I : Type*) : Erdos595Work.IsCountableUnionOfTriangleFree (graph I) := by
  let H : ℕ → SimpleGraph (Vertex I) := fun n => if n = 0 then rootPiece I else privatePiece I
  refine ⟨H,?_,?_⟩
  · intro n
    dsimp [H]
    split_ifs
    · exact rootPiece_triangleFree I
    · exact privatePiece_triangleFree I
  · rw [two_cover I]
    ext a b
    simp only [SimpleGraph.sup_adj,SimpleGraph.iSup_adj]
    constructor
    · rintro (h | h)
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
    · rintro ⟨n,hn⟩
      by_cases h : n = 0
      · exact Or.inl (by simpa [H,h] using hn)
      · exact Or.inr (by simpa [H,h] using hn)


/-- Preserve all spokes of the selected pair; shift every other spoke up
by one and give every private edge color zero. -/
noncomputable def globalColor (i : I) : Sym2 (Vertex I) → ℕ := by
  classical
  exact Sym2.lift ⟨(fun a b => match a,b with
    | .inl _,.inl _ => 0
    | .inl n,.inr (j,_) => if j = i then n else n + 1
    | .inr (j,_),.inl n => if j = i then n else n + 1
    | .inr _,.inr _ => 0),by intro a b; cases a <;> cases b <;> rfl⟩

lemma global_no_mono_root (i : I) (n : ℕ) (j k : I) (s t : Bool) (hjk : j ≠ k) :
    ¬(globalColor i s(Sum.inl n,Sum.inr (j,s)) =
        globalColor i s(Sum.inl n,Sum.inr (k,t)) ∧
      globalColor i s(Sum.inl n,Sum.inr (j,s)) =
        globalColor i s(Sum.inr (j,s),Sum.inr (k,t))) := by
  classical
  simp only [globalColor,Sym2.lift_mk]
  by_cases hji : j = i <;> by_cases hki : k = i
  · exact (hjk (hji.trans hki.symm)).elim
  · simp [hji,hki]
  · simp [hji,hki]
  · simp [hji,hki]

theorem globalColor_valid (i : I) : ValidOn (graph I) univ (globalColor i) := by
  intro a _ b _ c _ hab hac hbc he
  cases a with
  | inl n =>
    cases b with
    | inl m => exact hab
    | inr b =>
      cases c with
      | inl m => exact hac
      | inr c => exact global_no_mono_root i n b.1 c.1 b.2 c.2 hbc.1 he
  | inr a =>
    cases b with
    | inl n =>
      cases c with
      | inl m => exact hbc
      | inr c =>
        apply global_no_mono_root i n a.1 c.1 a.2 c.2 hac.1
        constructor
        · simpa only [Sym2.eq_swap] using he.2
        · simpa only [Sym2.eq_swap] using he.1
    | inr b =>
      cases c with
      | inl n =>
        apply global_no_mono_root i n a.1 b.1 a.2 b.2 hab.1
        constructor
        · simpa only [Sym2.eq_swap] using he.1.symm.trans he.2
        · simpa only [Sym2.eq_swap] using he.1.symm
      | inr c =>
        have h₁ := hab.2
        have h₂ := hac.2
        have h₃ := hbc.2
        cases ha : a.2 <;> cases hb : b.2 <;> cases hc : c.2 <;> simp_all

lemma globalColor_agrees (i : I) (a : Vertex I) (ha : a ∈ domain i)
    (b : Vertex I) (hb : b ∈ domain i) (hab : (graph I).Adj a b) :
    globalColor i s(a,b) = color s(a,b) := by
  classical
  cases a with
  | inl n =>
    cases b with
    | inl m => exact hab.elim
    | inr b =>
      have he := (private_mem i b.1 b.2).mp hb
      simp [globalColor,color,pairColor,he]
  | inr a =>
    cases b with
    | inl n =>
      have he := (private_mem i a.1 a.2).mp ha
      simp [globalColor,color,pairColor,he]
    | inr b => rfl

/-- Every member of the antichain is individually globally extendable. -/
theorem condition_globally_extendable (i : I) :
    ∃ c : Sym2 (Vertex I) → ℕ, ValidOn (graph I) univ c ∧
      ∀ a ∈ (condition i).domain, ∀ b ∈ (condition i).domain,
        (graph I).Adj a b → c s(a,b) = (condition i).color s(a,b) :=
  ⟨globalColor i,globalColor_valid i,globalColor_agrees i⟩

#print axioms condition_globally_extendable

#print axioms incompatible
#print axioms domain_inter
#print axioms condition_injective
#print axioms cliqueFree
#print axioms ambient_covered
end Erdos595CountablePartialAntichain
