import FormalConjecturesUtil

/-!
# An incidence-graph bridge for function families

For a family `f : X → T → C`, join `x : X` to `(t, c) : T × C` when
`f x t = c`.  This file gives the exact edge count and a complete-bipartite
copy criterion, including copies which interchange the two sides.

All statements are conditional adapters for a supplied function family.
They do not construct such a family or settle Erdős problem 714.
This file does not import `Submission.Spec`.
-/

namespace IncidenceBridge

open SimpleGraph

variable {X T C : Type*}

/-- The bipartite incidence graph of a family of functions. -/
def incidenceGraph (f : X → T → C) : SimpleGraph (X ⊕ (T × C)) where
  Adj
    | .inl x, .inr p => f x p.1 = p.2
    | .inr p, .inl x => f x p.1 = p.2
    | _, _ => False
  symm := by
    intro a b h
    cases a <;> cases b <;> exact h
  loopless := by
    intro a
    cases a <;> exact id

@[simp] theorem incidenceGraph_adj_inl_inr (f : X → T → C) (x : X) (p : T × C) :
    (incidenceGraph f).Adj (.inl x) (.inr p) ↔ f x p.1 = p.2 := Iff.rfl

@[simp] theorem incidenceGraph_adj_inr_inl (f : X → T → C) (p : T × C) (x : X) :
    (incidenceGraph f).Adj (.inr p) (.inl x) ↔ f x p.1 = p.2 := Iff.rfl

@[simp] theorem incidenceGraph_not_adj_inl (f : X → T → C) (x y : X) :
    ¬ (incidenceGraph f).Adj (.inl x) (.inl y) := id

@[simp] theorem incidenceGraph_not_adj_inr (f : X → T → C) (p q : T × C) :
    ¬ (incidenceGraph f).Adj (.inr p) (.inr q) := id

instance incidenceGraph_decidableAdj (f : X → T → C) [DecidableEq C] :
    DecidableRel (incidenceGraph f).Adj := by
  intro a b
  cases a <;> cases b <;> dsimp [incidenceGraph] <;> infer_instance

/-- The displayed sum is a bipartition, including any isolated vertices. -/
theorem incidenceGraph_isBipartiteWith (f : X → T → C) :
    (incidenceGraph f).IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) where
  disjoint := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨p, h⟩
    cases h
  mem_of_adj := by
    intro a b h
    cases a <;> cases b <;> simp_all

/-- In particular, the incidence graph is bipartite. -/
theorem incidenceGraph_isBipartite (f : X → T → C) :
    (incidenceGraph f).IsBipartite :=
  (incidenceGraph_isBipartiteWith f).isBipartite

/-- Each pair `(x,t)` specifies its unique incidence edge. -/
def incidenceEdge (f : X → T → C) (p : X × T) : Sym2 (X ⊕ (T × C)) :=
  s(Sum.inl p.1, Sum.inr (p.2, f p.1 p.2))

/-- Different `(x,t)` pairs give different undirected edges. -/
theorem incidenceEdge_injective (f : X → T → C) :
    Function.Injective (incidenceEdge f) := by
  rintro ⟨x, t⟩ ⟨y, u⟩ h
  simp only [incidenceEdge, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
    Prod.mk.injEq, Sum.inl_ne_inr, false_and, or_false] at h
  exact Prod.ext h.1 h.2.1

/-- An `r`-by-`r` agreement rectangle: `r` distinct members of the family
agree at each of `r` distinct coordinates. -/
def HasAgreementRectangle (f : X → T → C) (r : ℕ) : Prop :=
  ∃ (x : Fin r → X) (t : Fin r → T),
    Function.Injective x ∧ Function.Injective t ∧
      ∀ i i' j, f (x i) (t j) = f (x i') (t j)

/-- If one vertex of the first part is on the incidence graph's left, then
all of that part is on the left and the other part is on the right. -/
private theorem biclique_of_left (f : X → T → C) {r : ℕ} (i₀ : Fin r)
    (a b : Fin r → X ⊕ (T × C))
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, (incidenceGraph f).Adj (a i) (b j))
    (h₀ : ∃ x, a i₀ = Sum.inl x) :
    ∃ (x : Fin r → X) (p : Fin r → T × C),
      Function.Injective x ∧ Function.Injective p ∧
        ∀ i j, f (x i) (p j).1 = (p j).2 := by
  classical
  obtain ⟨x₀, h₀⟩ := h₀
  have hright : ∀ j, ∃ p, b j = Sum.inr p := by
    intro j
    have h := hab i₀ j
    rw [h₀] at h
    cases he : b j with
    | inl y => simp [he] at h
    | inr p => exact ⟨p, rfl⟩
  choose p hp using hright
  have hleft : ∀ i, ∃ x, a i = Sum.inl x := by
    intro i
    have h := hab i i₀
    rw [hp i₀] at h
    cases he : a i with
    | inl x => exact ⟨x, rfl⟩
    | inr q => simp [he] at h
  choose x hx using hleft
  refine ⟨x, p, ?_, ?_, ?_⟩
  · intro i j h
    apply ha
    rw [hx i, hx j, h]
  · intro i j h
    apply hb
    rw [hp i, hp j, h]
  · intro i j
    have h := hab i j
    rw [hx i, hp j] at h
    exact h

/-- A copy of `K_{r,r}` supplies `r` actual left vertices and `r` actual right
vertices with all cross incidences.  The proof treats both orientations of
the copy: if its first part lies on the right, the two parts are exchanged. -/
theorem incidence_rectangle_of_copy (f : X → T → C) {r : ℕ} (hr : 0 < r)
    (φ : (completeBipartiteGraph (Fin r) (Fin r)).Copy (incidenceGraph f)) :
    ∃ (x : Fin r → X) (p : Fin r → T × C),
      Function.Injective x ∧ Function.Injective p ∧
        ∀ i j, f (x i) (p j).1 = (p j).2 := by
  let i₀ : Fin r := ⟨0, hr⟩
  let a : Fin r → X ⊕ (T × C) := fun i => φ (Sum.inl i)
  let b : Fin r → X ⊕ (T × C) := fun i => φ (Sum.inr i)
  have ha : Function.Injective a := φ.injective.comp Sum.inl_injective
  have hb : Function.Injective b := φ.injective.comp Sum.inr_injective
  have hab : ∀ i j, (incidenceGraph f).Adj (a i) (b j) := by
    intro i j
    exact φ.toHom.map_adj (by simp)
  cases h₀ : a i₀ with
  | inl x => exact biclique_of_left f i₀ a b ha hb hab ⟨x, h₀⟩
  | inr p =>
    have hb₀ : ∃ x, b i₀ = Sum.inl x := by
      have h := hab i₀ i₀
      rw [h₀] at h
      cases he : b i₀ with
      | inl x => exact ⟨x, rfl⟩
      | inr q => simp [he] at h
    exact biclique_of_left f i₀ b a hb ha (fun i j => (hab j i).symm) hb₀

/-- In a complete incidence rectangle, the right vertices have distinct
coordinate projections: their colors are forced by any one left vertex. -/
theorem hasAgreementRectangle_of_copy (f : X → T → C) {r : ℕ} (hr : 0 < r)
    (φ : (completeBipartiteGraph (Fin r) (Fin r)).Copy (incidenceGraph f)) :
    HasAgreementRectangle f r := by
  obtain ⟨x, p, hx, hp, h⟩ := incidence_rectangle_of_copy f hr φ
  refine ⟨x, fun j => (p j).1, hx, ?_, ?_⟩
  · intro j k hcoord
    apply hp
    apply Prod.ext hcoord
    exact (h ⟨0, hr⟩ j).symm.trans
      ((congrArg (f (x ⟨0, hr⟩)) hcoord).trans (h ⟨0, hr⟩ k))
  · intro i i' j
    exact (h i j).trans (h i' j).symm

/-- An agreement rectangle constructs an injective (not necessarily induced)
copy of `K_{r,r}`. -/
theorem contains_of_hasAgreementRectangle (f : X → T → C) {r : ℕ} (hr : 0 < r)
    (h : HasAgreementRectangle f r) :
    (completeBipartiteGraph (Fin r) (Fin r)).IsContained (incidenceGraph f) := by
  obtain ⟨x, t, hx, ht, h⟩ := h
  let i₀ : Fin r := ⟨0, hr⟩
  let g : Fin r ⊕ Fin r → X ⊕ (T × C) :=
    Sum.elim (fun i => Sum.inl (x i)) (fun j => Sum.inr (t j, f (x i₀) (t j)))
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl i' => simp at hab
      | inr j => exact h i i₀ j
    | inr j =>
      cases b with
      | inl i => exact h i i₀ j
      | inr j' => simp at hab
  · intro a b heq
    cases a <;> cases b
    · exact congrArg Sum.inl (hx (Sum.inl.inj heq))
    · cases heq
    · cases heq
    · exact congrArg Sum.inr (ht (congrArg Prod.fst (Sum.inr.inj heq)))

/-- Exact copy criterion, valid already for `r ≥ 1`, hence for every `r ≥ 2`.
Neither finiteness nor any decidability assumptions are needed here. -/
theorem contains_iff_hasAgreementRectangle (f : X → T → C) {r : ℕ} (hr : 0 < r) :
    (completeBipartiteGraph (Fin r) (Fin r)).IsContained (incidenceGraph f) ↔
      HasAgreementRectangle f r :=
  ⟨fun ⟨φ⟩ => hasAgreementRectangle_of_copy f hr φ,
    contains_of_hasAgreementRectangle f hr⟩

/-- An orientation-independent complete-bipartite freeness criterion. -/
theorem free_iff_noAgreementRectangle (f : X → T → C) {r : ℕ} (hr : 0 < r) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free (incidenceGraph f) ↔
      ¬ HasAgreementRectangle f r :=
  not_congr (contains_iff_hasAgreementRectangle f hr)

/-- A version of the freeness criterion expressed entirely using injective
functions `Fin r → X` and `Fin r → T`. -/
theorem free_iff_forall_injective (f : X → T → C) {r : ℕ} (hr : 0 < r) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free (incidenceGraph f) ↔
      ∀ (x : Fin r → X), Function.Injective x →
        ∀ (t : Fin r → T), Function.Injective t →
          ¬ (∀ i i' j, f (x i) (t j) = f (x i') (t j)) := by
  rw [free_iff_noAgreementRectangle f hr]
  constructor
  · intro h x hx t ht hagree
    exact h ⟨x, t, hx, ht, hagree⟩
  · intro h ⟨x, t, hx, ht, hagree⟩
    exact h x hx t ht hagree

section AgreementCount

variable [Fintype T]

open Classical in
/-- Coordinates where all members of `S` agree with the selected anchor.
When the anchor belongs to the nonempty set `S`, these are exactly the
coordinates of the common right neighbors of `S`. -/
noncomputable def agreementFinset (f : X → T → C) (S : Finset X) (anchor : X) : Finset T :=
  Finset.univ.filter fun t => ∀ x ∈ S, f x t = f anchor t

@[simp] theorem mem_agreementFinset (f : X → T → C) (S : Finset X) (anchor : X) (t : T) :
    t ∈ agreementFinset f S anchor ↔ ∀ x ∈ S, f x t = f anchor t := by
  classical
  simp [agreementFinset]

/-- Exact finite-coordinate version of the freeness criterion.  It is enough
to bound agreement for `r`-element sets of actual left vertices; the reverse
orientation of a forbidden copy imposes no additional hypothesis. -/
theorem free_iff_agreementFinset_card_lt (f : X → T → C) {r : ℕ} (hr : 0 < r) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free (incidenceGraph f) ↔
      ∀ (S : Finset X), S.card = r → ∀ anchor ∈ S,
        (agreementFinset f S anchor).card < r := by
  classical
  rw [free_iff_forall_injective f hr]
  constructor
  · intro h S hS anchor _hanchor
    by_contra hnot
    have hle : r ≤ (agreementFinset f S anchor).card := Nat.le_of_not_gt hnot
    let eX : Fin r ≃ S := (Finset.equivFinOfCardEq hS).symm
    obtain ⟨eT⟩ : Nonempty (Fin r ↪ agreementFinset f S anchor) :=
      Function.Embedding.nonempty_of_card_le (by
        simpa only [Fintype.card_fin, Fintype.card_coe] using hle)
    let x : Fin r → X := fun i => (eX i).val
    let t : Fin r → T := fun j => (eT j).val
    apply h x (Subtype.val_injective.comp eX.injective) t
      (Subtype.val_injective.comp eT.injective)
    intro i i' j
    have hj := (mem_agreementFinset f S anchor (t j)).mp (eT j).property
    exact (hj _ (eX i).property).trans (hj _ (eX i').property).symm
  · intro h x hx t ht hagree
    let S : Finset X := Finset.univ.image x
    have hS : S.card = r := by
      rw [Finset.card_image_of_injective _ hx]
      simp
    let i₀ : Fin r := ⟨0, hr⟩
    have hi₀ : x i₀ ∈ S := Finset.mem_image.mpr ⟨i₀, Finset.mem_univ _, rfl⟩
    have htmem : ∀ j, t j ∈ agreementFinset f S (x i₀) := by
      intro j
      rw [mem_agreementFinset]
      intro y hy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      exact hagree i i₀ j
    let e : Fin r ↪ agreementFinset f S (x i₀) :=
      ⟨fun j => ⟨t j, htmem j⟩, fun j k heq => ht (congrArg Subtype.val heq)⟩
    have hle : r ≤ (agreementFinset f S (x i₀)).card := by
      simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_embedding e
    exact (h S hS (x i₀) hi₀).not_ge hle

/-- The requested `r ≥ 2` freeness adapter for an arbitrary supplied family. -/
theorem free_of_agreementFinset_card_lt (f : X → T → C) {r : ℕ} (hr : 2 ≤ r)
    (h : ∀ (S : Finset X), S.card = r → ∀ anchor ∈ S,
      (agreementFinset f S anchor).card < r) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free (incidenceGraph f) :=
  (free_iff_agreementFinset_card_lt f (by omega)).2 h

end AgreementCount

section EdgeCount

variable [Fintype X] [Fintype T]

/-- The edge finset is exactly the embedding image of `X × T`.
The statement accepts any `Fintype` instance on the edge set. -/
theorem incidenceGraph_edgeFinset (f : X → T → C) [Fintype (incidenceGraph f).edgeSet] :
    (incidenceGraph f).edgeFinset =
      Finset.univ.map ⟨incidenceEdge f, incidenceEdge_injective f⟩ := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
    cases a <;> cases b <;>
      simp [incidenceEdge, incidenceGraph, Prod.exists, Prod.ext_iff]

/-- The incidence graph has exactly `|X| * |T|` edges, with no loss to collisions. -/
theorem incidenceGraph_card_edgeFinset (f : X → T → C)
    [Fintype (incidenceGraph f).edgeSet] :
    (incidenceGraph f).edgeFinset.card = Fintype.card X * Fintype.card T := by
  rw [incidenceGraph_edgeFinset, Finset.card_map]
  simp

/-- The same exact count for the edge-set subtype. -/
theorem incidenceGraph_card_edgeSet (f : X → T → C) [Fintype (incidenceGraph f).edgeSet] :
    Fintype.card (incidenceGraph f).edgeSet = Fintype.card X * Fintype.card T := by
  rw [← SimpleGraph.edgeFinset_card, incidenceGraph_card_edgeFinset]

/-- The total number of vertices, including unused colors. -/
theorem incidenceGraph_card_vertices [Fintype C] :
    Fintype.card (X ⊕ (T × C)) =
      Fintype.card X + Fintype.card T * Fintype.card C := by
  simp

end EdgeCount

section ExtremalNumber

variable [Fintype X] [Fintype T] [Fintype C]

/-- Any supplied family with no agreement rectangle gives this extremal-number
lower bound at its exact number of vertices. -/
theorem le_extremalNumber_of_noAgreementRectangle (f : X → T → C) {r : ℕ} (hr : 0 < r)
    (h : ¬ HasAgreementRectangle f r) :
    Fintype.card X * Fintype.card T ≤
      extremalNumber (Fintype.card X + Fintype.card T * Fintype.card C)
        (completeBipartiteGraph (Fin r) (Fin r)) := by
  classical
  have hfree := (free_iff_noAgreementRectangle f hr).2 h
  simpa only [incidenceGraph_card_edgeFinset, Fintype.card_sum, Fintype.card_prod] using
    SimpleGraph.card_edgeFinset_le_extremalNumber hfree

/-- The extremal-number adapter with a purely injective-function hypothesis. -/
theorem le_extremalNumber_of_forall_injective (f : X → T → C) {r : ℕ} (hr : 0 < r)
    (h : ∀ (x : Fin r → X), Function.Injective x →
      ∀ (t : Fin r → T), Function.Injective t →
        ¬ (∀ i i' j, f (x i) (t j) = f (x i') (t j))) :
    Fintype.card X * Fintype.card T ≤
      extremalNumber (Fintype.card X + Fintype.card T * Fintype.card C)
        (completeBipartiteGraph (Fin r) (Fin r)) := by
  apply le_extremalNumber_of_noAgreementRectangle f hr
  rintro ⟨x, t, hx, ht, hagree⟩
  exact h x hx t ht hagree

/-- Main finite-family adapter: if each `r`-element set of functions agrees
on fewer than `r` coordinates, its incidence graph witnesses
`|X| * |T| ≤ ex(|X| + |T| * |C|, K_{r,r})`.
This is a conditional lower bound, not an existence assertion for families. -/
theorem le_extremalNumber_of_agreementFinset_card_lt (f : X → T → C)
    {r : ℕ} (hr : 2 ≤ r)
    (h : ∀ (S : Finset X), S.card = r → ∀ anchor ∈ S,
      (agreementFinset f S anchor).card < r) :
    Fintype.card X * Fintype.card T ≤
      extremalNumber (Fintype.card X + Fintype.card T * Fintype.card C)
        (completeBipartiteGraph (Fin r) (Fin r)) := by
  classical
  simpa only [incidenceGraph_card_edgeFinset, Fintype.card_sum, Fintype.card_prod] using
    SimpleGraph.card_edgeFinset_le_extremalNumber (free_of_agreementFinset_card_lt f hr h)

end ExtremalNumber

end IncidenceBridge
