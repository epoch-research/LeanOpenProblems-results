import Submission.Work

/-!
Free amalgamation along induced subgraphs, for a finite Folkman construction.
No finite-to-countable Ramsey inference is made in this development.
-/

open SimpleGraph Set
open Erdos595Work
namespace Erdos595FiniteFolkmanAmalgamation

variable {A B I : Type*} (H : SimpleGraph A) (K : SimpleGraph B) (D : Set A)
    (e : I → H.induce D ↪g K)

abbrev Outside := {a : A // a ∉ D}
abbrev Vertex := B ⊕ (I × Outside D)

noncomputable def copy (i : I) (a : A) : Vertex D (B := B) (I := I) := by
  classical
  exact if h : a ∈ D then Sum.inl (e i ⟨a,h⟩) else Sum.inr (i,⟨a,h⟩)

@[simp] lemma copy_of_mem (i : I) (a : A) (ha : a ∈ D) :
    copy H K D e i a = Sum.inl (e i ⟨a,ha⟩) := by simp [copy,ha]

@[simp] lemma copy_of_not_mem (i : I) (a : A) (ha : a ∉ D) :
    copy H K D e i a = Sum.inr (i,⟨a,ha⟩) := by simp [copy,ha]

lemma copy_injective (i : I) : Function.Injective (copy H K D e i) := by
  classical
  intro a b he
  by_cases ha : a ∈ D <;> by_cases hb : b ∈ D
  · rw [copy_of_mem _ _ _ _ _ _ ha,copy_of_mem _ _ _ _ _ _ hb] at he
    exact congrArg Subtype.val ((e i).injective (Sum.inl.inj he))
  · simp [copy,ha,hb] at he
  · simp [copy,ha,hb] at he
  · simpa [copy,ha,hb,Subtype.ext_iff] using he

def graph : SimpleGraph (Vertex D (B := B) (I := I)) where
  Adj
    | .inl b, .inl c => K.Adj b c
    | .inl b, .inr (i,a) => ∃ d : D, e i d = b ∧ H.Adj d.val a.val
    | .inr (i,a), .inl b => ∃ d : D, e i d = b ∧ H.Adj a.val d.val
    | .inr (i,a), .inr (j,c) => i = j ∧ H.Adj a.val c.val
  symm := by
    intro x y h
    cases x with
    | inl b =>
      cases y with
      | inl c => exact h.symm
      | inr t =>
        obtain ⟨d,hd,ha⟩ := h
        exact ⟨d,hd,ha.symm⟩
    | inr t =>
      cases y with
      | inl b =>
        obtain ⟨d,hd,ha⟩ := h
        exact ⟨d,hd,ha.symm⟩
      | inr u => exact ⟨h.1.symm,h.2.symm⟩
  loopless := by
    intro x h
    cases x with
    | inl b => exact K.loopless b h
    | inr t => exact H.loopless t.2.val h.2

lemma copy_rel (i : I) (a b : A) :
    (graph H K D e).Adj (copy H K D e i a) (copy H K D e i b) ↔ H.Adj a b := by
  classical
  by_cases ha : a ∈ D <;> by_cases hb : b ∈ D
  · rw [copy_of_mem _ _ _ _ _ _ ha,copy_of_mem _ _ _ _ _ _ hb]
    exact (e i).map_rel_iff
  · rw [copy_of_mem _ _ _ _ _ _ ha,copy_of_not_mem _ _ _ _ _ _ hb]
    change (∃ d : D, e i d = e i ⟨a,ha⟩ ∧ H.Adj d.val b) ↔ H.Adj a b
    constructor
    · rintro ⟨d,hd,hab⟩
      have he := (e i).injective hd
      simpa only [he] using hab
    · intro hab
      exact ⟨⟨a,ha⟩,rfl,hab⟩
  · rw [copy_of_not_mem _ _ _ _ _ _ ha,copy_of_mem _ _ _ _ _ _ hb]
    change (∃ d : D, e i d = e i ⟨b,hb⟩ ∧ H.Adj a d.val) ↔ H.Adj a b
    constructor
    · rintro ⟨d,hd,hab⟩
      have he := (e i).injective hd
      simpa only [he] using hab
    · intro hab
      exact ⟨⟨b,hb⟩,rfl,hab⟩
  · rw [copy_of_not_mem _ _ _ _ _ _ ha,copy_of_not_mem _ _ _ _ _ _ hb]
    exact ⟨And.right,fun h => ⟨rfl,h⟩⟩

noncomputable def copyEmbedding (i : I) : H ↪g graph H K D e where
  toFun := copy H K D e i
  inj' := copy_injective H K D e i
  map_rel_iff' := copy_rel H K D e i _ _

def baseEmbedding : K ↪g graph H K D e where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Iff.rfl

lemma neighbor_private {i : I} {a : Outside D} {z : Vertex D (B := B) (I := I)}
    (hz : (graph H K D e).Adj (.inr (i,a)) z) :
    ∃ b : A, copy H K D e i b = z := by
  cases z with
  | inl z =>
    obtain ⟨d,hd,_⟩ := hz
    exact ⟨d.val,by rw [copy_of_mem _ _ _ _ _ _ d.property,hd]⟩
  | inr t =>
    obtain ⟨j,b⟩ := t
    have he : i = j := hz.1
    subst j
    exact ⟨b.val,copy_of_not_mem _ _ _ _ _ _ b.property⟩

/-- No new finite clique crosses between different private copies. -/
theorem cliqueFree (hH : H.CliqueFree 4) (hK : K.CliqueFree 4) :
    (graph H K D e).CliqueFree 4 := by
  classical
  by_contra hn
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have hadj : ∀ i j : Fin 4, i ≠ j → (graph H K D e).Adj (f i) (f j) :=
    fun i j hij => f.map_rel_iff.mpr hij
  by_cases hp : ∃ (i : Fin 4) (j : I) (a : Outside D), f i = .inr (j,a)
  · obtain ⟨i,j,a,hi⟩ := hp
    have hx : ∀ k : Fin 4, ∃ b : A, copy H K D e j b = f k := by
      intro k
      by_cases hk : k = i
      · subst k
        exact ⟨a.val,(copy_of_not_mem _ _ _ _ _ _ a.property).trans hi.symm⟩
      · exact neighbor_private H K D e (hi ▸ hadj i k (Ne.symm hk))
    choose x hx using hx
    have he : ∀ k l : Fin 4, k ≠ l → H.Adj (x k) (x l) := by
      intro k l hkl
      apply (copy_rel H K D e j _ _).mp
      rw [hx k,hx l]
      exact hadj k l hkl
    exact no_adj_common_neighbors hH (he 0 1 (by decide)) (he 0 2 (by decide))
      (he 1 2 (by decide)) (he 0 3 (by decide)) (he 1 3 (by decide)) (he 2 3 (by decide))
  · have hx : ∀ k : Fin 4, ∃ b : B, f k = .inl b := by
      intro k
      cases he : f k with
      | inl b => exact ⟨b,rfl⟩
      | inr t => exact (hp ⟨k,t.1,t.2,he⟩).elim
    choose x hx using hx
    have he : ∀ k l : Fin 4, k ≠ l → K.Adj (x k) (x l) := by
      intro k l hkl
      have hh := hadj k l hkl
      rw [hx k,hx l] at hh
      exact hh
    exact no_adj_common_neighbors hK (he 0 1 (by decide)) (he 0 2 (by decide))
      (he 1 2 (by decide)) (he 0 3 (by decide)) (he 1 3 (by decide)) (he 2 3 (by decide))

#print axioms copyEmbedding
#print axioms cliqueFree
end Erdos595FiniteFolkmanAmalgamation
