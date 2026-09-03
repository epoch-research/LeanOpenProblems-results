import FormalConjecturesUtil

/-!
# Covering a set by full graphs

A set with nonempty finite vertical fibres of cardinality at most `C` is the
union of `C` full graphs, each contained in the set. The graphs may overlap:
unused indices simply repeat an element of the corresponding fibre.

These are elementary set-theoretic reduction lemmas only; no geometric
coordinatization or projective-plane inverse theorem is assumed or proved.
-/

namespace Erdos1159.GraphCover

variable {X Y : Type*}

/-- The full graph of a function, with the dependent coordinate second. -/
def graph (g : X → Y) : Set (X × Y) := {p | p.2 = g p.1}

/-- A nonempty finite type of size at most `C` can be enumerated with repetitions.
The inverse of an embedding into `Fin C` repeats a chosen element off its range. -/
private lemma exists_surjective_fin {A : Type*} [Finite A] [Nonempty A]
    {C : ℕ} (hcard : Nat.card A ≤ C) :
    ∃ g : Fin C → A, Function.Surjective g := by
  letI := Fintype.ofFinite A
  apply Function.exists_surjective_iff.mpr
  refine ⟨inferInstance, Function.Embedding.nonempty_of_card_le ?_⟩
  simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using hcard

/-- Nonempty finite fibres of size at most `C` have a cover by `C` full graphs
contained in `S`. No separate positivity assumption on `C` is needed: if `X`
is nonempty, positivity already follows from the fibre hypotheses. -/
theorem exists_graph_cover_of_finite_fibres (S : Set (X × Y)) (C : ℕ)
    (hfinite : ∀ x : X, {y : Y | (x, y) ∈ S}.Finite)
    (hnonempty : ∀ x : X, {y : Y | (x, y) ∈ S}.Nonempty)
    (hcard : ∀ x : X, {y : Y | (x, y) ∈ S}.ncard ≤ C) :
    ∃ f : Fin C → X → Y,
      (∀ i, graph (f i) ⊆ S) ∧
      (∀ x y, (x, y) ∈ S ↔ ∃ i, y = f i x) := by
  classical
  have hex : ∀ x : X, ∃ g : Fin C → {y : Y // (x, y) ∈ S},
      Function.Surjective g := by
    intro x
    letI : Finite {y : Y // (x, y) ∈ S} := (hfinite x).to_subtype
    letI : Nonempty {y : Y // (x, y) ∈ S} := (hnonempty x).to_subtype
    exact exists_surjective_fin (hcard x)
  choose g hg using hex
  refine ⟨fun i x => (g x i).val, ?_, ?_⟩
  · rintro i ⟨x, y⟩ hxy
    change y = (g x i).val at hxy
    simpa only [hxy] using (g x i).property
  · intro x y
    constructor
    · intro hxy
      obtain ⟨i, hi⟩ := hg x ⟨y, hxy⟩
      exact ⟨i, (congrArg Subtype.val hi).symm⟩
    · rintro ⟨i, rfl⟩
      exact (g x i).property

/-- A convenient version when the whole target type is finite. -/
theorem exists_graph_cover [Finite Y] (S : Set (X × Y)) (C : ℕ)
    (hnonempty : ∀ x : X, {y : Y | (x, y) ∈ S}.Nonempty)
    (hcard : ∀ x : X, {y : Y | (x, y) ∈ S}.ncard ≤ C) :
    ∃ f : Fin C → X → Y,
      (∀ i, graph (f i) ⊆ S) ∧
      (∀ x y, (x, y) ∈ S ↔ ∃ i, y = f i x) := by
  exact exists_graph_cover_of_finite_fibres S C (fun _ => Set.toFinite _) hnonempty hcard

/-- The membership characterization of a graph cover also gives literal union equality. -/
theorem eq_iUnion_graph {I : Type*} {S : Set (X × Y)} {f : I → X → Y}
    (hf : ∀ x y, (x, y) ∈ S ↔ ∃ i, y = f i x) :
    S = ⋃ i, graph (f i) := by
  ext ⟨x, y⟩
  simpa only [Set.mem_iUnion, graph, Set.mem_setOf_eq] using hf x y

/-- Every graph contained in `S` inherits any upper bound on `S ∩ T`.
Only `S ∩ T` needs to be finite; in a finite ambient product this is automatic.
In particular, apply this to any of the graphs supplied by `exists_graph_cover`. -/
theorem graph_inter_ncard_le {g : X → Y} {S T : Set (X × Y)} {B : ℕ}
    (hg : graph g ⊆ S) (hbound : (S ∩ T).ncard ≤ B)
    (hfinite : (S ∩ T).Finite := by toFinite_tac) :
    (graph g ∩ T).ncard ≤ B := by
  exact (Set.ncard_le_ncard (Set.inter_subset_inter hg (Set.Subset.refl T)) hfinite).trans
    hbound

end Erdos1159.GraphCover
