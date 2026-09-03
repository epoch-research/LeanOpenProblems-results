import FormalConjecturesUtil

/-! A box family with exponentially many different minimal Boolean covering
cores. This tests a proposed union-bound approach, not the odd-cover conjecture. -/
namespace Erdos7ManyBooleanCores
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def baseSupport : Fin 6 → Finset (Fin 4) :=
  ![{0,1},{2,3},{0,2},{0,3},{1,2},{1,3}]
def baseBit : Fin 6 → Fin 2 := ![0,0,1,1,1,1]
def basePrivate : Fin 6 → Fin 4 → Fin 2 :=
  ![![0,0,1,1], ![1,1,0,0], ![1,0,1,0], ![1,0,0,1], ![0,1,1,0], ![0,1,0,1]]

lemma base_properties : Function.Injective baseSupport ∧
    (∀ j, (baseSupport j).card = 2) ∧
    (∀ x : Fin 4 → Fin 2, ∃ j, ∀ i ∈ baseSupport j, x i = baseBit j) ∧
    (∀ j k, (∀ i ∈ baseSupport k, basePrivate j i = baseBit k) ↔ k = j) := by
  decide +kernel

abbrev Old := Fin 3 → Fin 6
abbrev Coord := (Fin 3 × Fin 4) ⊕ (Fin 2 × Fin 4)
abbrev Class := Old × Fin 2 × Fin 6

def used (k : Class) (q : Coord) : Prop :=
  match q with
  | .inl (i,c) => c ∈ baseSupport (k.1 i)
  | .inr (b,c) => b = k.2.1 ∧ c ∈ baseSupport k.2.2

instance (k : Class) (q : Coord) : Decidable (used k q) := by
  rcases q with ⟨i,c⟩ | ⟨b,c⟩ <;> unfold used <;> infer_instance

def support (k : Class) : Finset Coord := Finset.univ.filter (used k)

def bit (k : Class) (q : Coord) : Fin 2 :=
  match q with
  | .inl (i,_) => baseBit (k.1 i)
  | .inr _ => baseBit k.2.2

def Matches (k : Class) (x : Coord → Fin 2) : Prop :=
  ∀ q ∈ support k, x q = bit k q

@[simp] lemma mem_support_left (k : Class) (i : Fin 3) (c : Fin 4) :
    Sum.inl (i,c) ∈ support k ↔ c ∈ baseSupport (k.1 i) := by simp [support, used]
@[simp] lemma mem_support_right (k : Class) (b : Fin 2) (c : Fin 4) :
    Sum.inr (b,c) ∈ support k ↔ b = k.2.1 ∧ c ∈ baseSupport k.2.2 := by simp [support, used]

lemma support_card (k : Class) : (support k).card = 8 := by
  have h : ∀ k : Class, (support k).card = 8 := by decide +kernel
  exact h k

lemma support_injective : Function.Injective support := by
  intro k l h
  have hold : k.1 = l.1 := by
    funext i
    apply base_properties.1
    ext c
    have hh := congrArg (fun s => Sum.inl (i,c) ∈ s) h
    simpa only [mem_support_left] using Iff.of_eq hh
  have hne : (baseSupport k.2.2).Nonempty := by
    apply Finset.card_pos.mp
    rw [base_properties.2.1]
    decide
  obtain ⟨c,hc⟩ := hne
  have hh : Sum.inr (k.2.1,c) ∈ support l := h ▸ (mem_support_right k _ _).mpr ⟨rfl,hc⟩
  have hb : k.2.1 = l.2.1 := ((mem_support_right l _ _).mp hh).1
  have ht : k.2.2 = l.2.2 := by
    apply base_properties.1
    ext c
    have hh := congrArg (fun s => Sum.inr (k.2.1,c) ∈ s) h
    simpa only [mem_support_right, hb, true_and] using Iff.of_eq hh
  exact Prod.ext hold (Prod.ext hb ht)

/-- For each of the 216 old clauses choose which of two disjoint four-variable
gadgets is used to split it into six clauses. -/
def core (f : Old → Fin 2) : Finset Class :=
  Finset.univ.filter (fun k => k.2.1 = f k.1)

@[simp] lemma mem_core (f : Old → Fin 2) (k : Class) : k ∈ core f ↔ k.2.1 = f k.1 := by
  simp [core]

lemma core_injective : Function.Injective core := by
  intro f g h
  funext j
  have hh : (j,f j,0) ∈ core g := h ▸ (mem_core f _).mpr rfl
  exact (mem_core g _).mp hh

/-- Every one of the 2^216 choices is a genuine Boolean cover. -/
theorem core_covers (f : Old → Fin 2) (x : Coord → Fin 2) :
    ∃ k ∈ core f, Matches k x := by
  have hh (i : Fin 3) := base_properties.2.2.1 (fun c => x (.inl (i,c)))
  choose j hj using hh
  obtain ⟨t,ht⟩ := base_properties.2.2.1 (fun c => x (.inr (f j,c)))
  refine ⟨(j,f j,t), (mem_core f _).mpr rfl, ?_⟩
  rintro (⟨i,c⟩|⟨b,c⟩) hq
  · exact hj i c ((mem_support_left _ _ _).mp hq)
  · obtain ⟨hb,hc⟩ := (mem_support_right _ _ _).mp hq
    subst b
    exact ht c hc

def privatePoint (k : Class) (q : Coord) : Fin 2 :=
  match q with
  | .inl (i,c) => basePrivate (k.1 i) c
  | .inr (_,c) => basePrivate k.2.2 c

lemma private_matches (k : Class) : Matches k (privatePoint k) := by
  rintro (⟨i,c⟩|⟨b,c⟩) hq
  · exact (base_properties.2.2.2 (k.1 i) (k.1 i)).mpr rfl c
      ((mem_support_left _ _ _).mp hq)
  · exact (base_properties.2.2.2 k.2.2 k.2.2).mpr rfl c
      ((mem_support_right _ _ _).mp hq).2

/-- These are MINIMAL covering cores, not arbitrary redundant supersets. -/
theorem core_private (f : Old → Fin 2) (k l : Class)
    (hk : k ∈ core f) (hl : l ∈ core f) :
    Matches l (privatePoint k) ↔ l = k := by
  constructor
  · intro h
    have hold : l.1 = k.1 := by
      funext i
      apply (base_properties.2.2.2 (k.1 i) (l.1 i)).mp
      intro c hc
      exact h (.inl (i,c)) ((mem_support_left _ _ _).mpr hc)
    have hb : l.2.1 = k.2.1 := by
      rw [(mem_core f _).mp hl, hold, ← (mem_core f _).mp hk]
    have ht : l.2.2 = k.2.2 := by
      apply (base_properties.2.2.2 k.2.2 l.2.2).mp
      intro c hc
      exact h (.inr (l.2.1,c)) ((mem_support_right _ _ _).mpr ⟨rfl,hc⟩)
    exact Prod.ext hold (Prod.ext hb ht)
  · intro h
    subst l
    exact private_matches k

noncomputable def allCores : Finset (Finset Class) := Finset.univ.image core

lemma allCores_card : allCores.card = 2^216 := by
  rw [allCores, Finset.card_image_of_injective _ core_injective, Finset.card_univ]
  simp only [Fintype.card_fun, Fintype.card_fin, Old]
  norm_num

/-- An explicit family with 2592 different width-eight supports on twenty
Boolean coordinates, and at least 2^216 distinct irredundant covering cores. -/
theorem many_minimal_cores :
    Function.Injective support ∧ (∀ k, (support k).card = 8) ∧
    allCores.card = 2^216 ∧
    ∀ s ∈ allCores,
      (∀ x : Coord → Fin 2, ∃ k ∈ s, Matches k x) ∧
      ∀ k ∈ s, ∃ x : Coord → Fin 2, ∀ l ∈ s, Matches l x ↔ l = k := by
  refine ⟨support_injective, support_card, allCores_card, ?_⟩
  intro s hs
  obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hs
  exact ⟨core_covers f, fun k hk => ⟨privatePoint k, fun l hl => core_private f k l hk hl⟩⟩

#print axioms support_card
#print axioms many_minimal_cores
end Erdos7ManyBooleanCores
