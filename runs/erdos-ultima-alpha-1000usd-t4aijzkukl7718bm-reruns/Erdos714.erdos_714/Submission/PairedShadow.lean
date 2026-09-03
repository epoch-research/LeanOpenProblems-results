import Submission.Packing

/-!
A C4 in the graph of complete two-by-two blocks lifts to a K44.
Fixed-point-free involutions supply such blocks without duplicate representatives.
These are necessary compatibility conditions, not a construction for Erdős 714.
-/

noncomputable section
open SimpleGraph Finset Classical

namespace Erdos714PairedShadow

variable {X Y U V : Type*} [Fintype Y]

/-- The bipartite graph of an arbitrary finite incidence relation. -/
def relationGraph (R : X → Y → Prop) : SimpleGraph (X ⊕ Y) :=
  Erdos714Packing.incidence (fun x => univ.filter (R x))

/-- Each shadow edge represents all four original edges. -/
def shadow (R : (X × Fin 2) → (Y × Fin 2) → Prop) : SimpleGraph (X ⊕ Y) :=
  relationGraph (fun x y => ∀ i j : Fin 2, R (x,i) (y,j))

/-- Keep precisely the complete two-by-two blocks of a relation. -/
def allBlocks (R : (X × Fin 2) → (Y × Fin 2) → Prop) :
    (X × Fin 2) → (Y × Fin 2) → Prop :=
  fun x y => ∀ i j : Fin 2, R (x.1,i) (y.1,j)

/-- Both four-vertex injections are built from two distinct blocks and their
actual two distinct elements. -/
def rectangleCopy (R : (X × Fin 2) → (Y × Fin 2) → Prop)
    (e : Fin 2 ↪ X) (f : Fin 2 ↪ Y)
    (he : ∀ i j u v : Fin 2, R (e i,u) (f j,v)) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (relationGraph R) := by
  let d : Fin 4 ≃ Fin 2 × Fin 2 := (finProdFinEquiv (m := 2) (n := 2)).symm
  let L : Fin 4 ↪ X × Fin 2 := d.toEmbedding.trans (e.prodMap (Function.Embedding.refl _))
  let T : Fin 4 ↪ Y × Fin 2 := d.toEmbedding.trans (f.prodMap (Function.Embedding.refl _))
  have hE (i j : Fin 4) : R (L i) (T j) := he (d i).1 (d j).1 (d i).2 (d j).2
  refine ⟨⟨L.sumMap T,?_⟩,(L.sumMap T).injective⟩
  intro p q hpq
  cases p <;> cases q <;> simp_all [relationGraph, Erdos714Packing.incidence]

/-- Every shadow of a K44-free graph is C4-free. This is only a necessary condition. -/
theorem shadow_free (R : (X × Fin 2) → (Y × Fin 2) → Prop)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (relationGraph R)) :
    (completeBipartiteGraph (Fin 2) (Fin 2)).Free (shadow R) := by
  apply (Erdos714Packing.free_iff_no_rectangle _ (by decide : 0 < 2)).mpr
  intro e f he
  have he' : ∀ i j u v : Fin 2, R (e i,u) (f j,v) := by
    intro i j
    simpa only [mem_filter, mem_univ, true_and] using he i j
  exact hfree ⟨rectangleCopy R e f he'⟩

/-- Relabeling two-element blocks is an actual graph isomorphism. -/
def relationIso [Fintype V] (R : U → V → Prop) (e : X ≃ U) (f : Y ≃ V) :
    relationGraph (fun x y => R (e x) (f y)) ≃g relationGraph R where
  toEquiv := e.sumCongr f
  map_rel_iff' := by
    intro p q
    cases p <;> cases q <;> simp [relationGraph, Erdos714Packing.incidence]

/-- The abstract shadow criterion applies to any chosen two-element partition. -/
theorem paired_shadow_free [Fintype V] (R : U → V → Prop)
    (e : X × Fin 2 ≃ U) (f : Y × Fin 2 ≃ V)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (relationGraph R)) :
    (completeBipartiteGraph (Fin 2) (Fin 2)).Free
      (shadow (fun x y => R (e x) (f y))) := by
  apply shadow_free
  rintro ⟨c⟩
  exact hfree ⟨(relationIso R e f).toCopy.comp c⟩

variable [Fintype X]

/-- The factor four counts undirected edges once, not once from each endpoint. -/
theorem allBlocks_edges (R : (X × Fin 2) → (Y × Fin 2) → Prop) :
    (relationGraph (allBlocks R)).edgeFinset.card = 4 * (shadow R).edgeFinset.card := by
  simp only [shadow, relationGraph, allBlocks]
  rw [Erdos714Packing.incidence_edges, Erdos714Packing.incidence_edges]
  simp only [card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, sum_add_distrib, allBlocks]
  omega

section Pairing

variable {W : Type*} [LinearOrder W]

/-- Exactly one representative from each free involution orbit. -/
abbrev Rep (φ : W → W) := {x : W // x < φ x}

/-- A free involution partitions a linearly ordered type into actual pairs. -/
def involutionPairing (φ : W → W) (hinv : Function.Involutive φ)
    (hfree : ∀ x, φ x ≠ x) : Rep φ × Fin 2 ≃ W where
  toFun p := if p.2 = 0 then p.1.val else φ p.1.val
  invFun x := if hx : x < φ x then (⟨x,hx⟩,0) else
    (⟨φ x, by
      rw [hinv]
      exact lt_of_le_of_ne (le_of_not_gt hx) (hfree x)⟩,1)
  left_inv := by
    rintro ⟨⟨x,hx⟩,i⟩
    fin_cases i
    · simp [hx]
    · have hnot : ¬ φ x < x := not_lt_of_gt hx
      simp [hnot, hinv x]
  right_inv := by
    intro x
    by_cases hx : x < φ x <;> simp [hx, hinv x]

@[simp] lemma involutionPairing_zero (φ : W → W) (hinv : Function.Involutive φ)
    (hfree : ∀ x, φ x ≠ x) (x : Rep φ) : involutionPairing φ hinv hfree (x,0) = x.val := by
  rfl

@[simp] lemma involutionPairing_one (φ : W → W) (hinv : Function.Involutive φ)
    (hfree : ∀ x, φ x ≠ x) (x : Rep φ) : involutionPairing φ hinv hfree (x,1) = φ x.val := by
  rfl

theorem rep_card [Fintype W] (φ : W → W) (hinv : Function.Involutive φ)
    (hfree : ∀ x, φ x ≠ x) : 2 * Fintype.card (Rep φ) = Fintype.card W := by
  simpa only [Fintype.card_prod, Fintype.card_fin, mul_comm] using
    Fintype.card_congr (involutionPairing φ hinv hfree)

end Pairing

section Binary

open scoped CharTwo
variable {G A B : Type*} [Ring G] [CharP G 2]

/-- The four cross edges between additive pairs reduce to two memberships. -/
theorem four_edges_iff (S : Set G) (x y h : G) :
    (∀ i j : Fin 2,
      (x + if i = 0 then 0 else h) + (y + if j = 0 then 0 else h) ∈ S) ↔
      x+y ∈ S ∧ x+y+h ∈ S := by
  simp [Fin.forall_fin_succ, add_left_comm, add_comm, and_comm]

lemma shift_involutive (h : G) : Function.Involutive (fun x => x+h) := by
  intro x
  simp

omit [CharP G 2] in
lemma shift_free {h : G} (hh : h ≠ 0) (x : G) : x+h ≠ x := by
  intro he
  apply hh
  exact add_left_cancel (show x+h=x+0 by simpa using he)

variable [LinearOrder G]

/-- The additive h-orbits, with exactly one representative each. -/
def shiftPairing (h : G) (hh : h ≠ 0) : Rep (fun x : G => x+h) × Fin 2 ≃ G :=
  involutionPairing (fun x => x+h) (shift_involutive h) (shift_free hh)

@[simp] lemma shiftPairing_zero (h : G) (hh : h ≠ 0) (x : Rep (fun x : G => x+h)) :
    shiftPairing h hh (x,0) = x.val := rfl

@[simp] lemma shiftPairing_one (h : G) (hh : h ≠ 0) (x : Rep (fun x : G => x+h)) :
    shiftPairing h hh (x,1) = x.val+h := rfl

/-- The orbit pairing transports labels without identifying them. -/
def labeledPairing (h : G) (hh : h ≠ 0) :
    (Rep (fun x : G => x+h) × A) × Fin 2 ≃ G × A where
  toFun p := (shiftPairing h hh (p.1.1,p.2),p.1.2)
  invFun p := (((shiftPairing h hh).symm p.1 |>.1,p.2),(shiftPairing h hh).symm p.1 |>.2)
  left_inv := by
    rintro ⟨⟨x,a⟩,i⟩
    simp
  right_inv := by
    rintro ⟨x,a⟩
    simp

variable [Fintype G] [Fintype A] [Fintype B]

/-- The actual shadow of a partial-translation graph, not an enlarged relation. -/
def additiveShadow (S : A → B → Set G) (h : G) (hh : h ≠ 0) :
    SimpleGraph ((Rep (fun x : G => x+h) × A) ⊕ (Rep (fun x : G => x+h) × B)) :=
  shadow (fun x y =>
    (labeledPairing h hh x).1 + (labeledPairing h hh y).1 ∈ S x.1.2 y.1.2)

omit [Fintype A] in
theorem additiveShadow_free (S : A → B → Set G) (h : G) (hh : h ≠ 0)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (relationGraph (fun x : G × A => fun y : G × B => x.1+y.1 ∈ S x.2 y.2))) :
    (completeBipartiteGraph (Fin 2) (Fin 2)).Free (additiveShadow S h hh) := by
  exact paired_shadow_free _ (labeledPairing h hh) (labeledPairing h hh) hfree

omit [Fintype A] in
/-- Adjacency can be checked with two field equations rather than four. -/
theorem additiveShadow_adj (S : A → B → Set G) (h : G) (hh : h ≠ 0)
    (x : Rep (fun x : G => x+h) × A) (y : Rep (fun x : G => x+h) × B) :
    (additiveShadow S h hh).Adj (.inl x) (.inr y) ↔
      (x.1.val+y.1.val ∈ S x.2 y.2 ∧ x.1.val+y.1.val+h ∈ S x.2 y.2) := by
  simp only [additiveShadow, shadow, relationGraph, Erdos714Packing.incidence_inl_inr,
    mem_filter, mem_univ, true_and]
  change (∀ i j : Fin 2, shiftPairing h hh (x.1,i)+shiftPairing h hh (y.1,j) ∈ S x.2 y.2) ↔ _
  simp [Fin.forall_fin_succ, add_left_comm, add_comm, and_comm]

/-- The connection differences that support a paired block. -/
def differenceFiber (S : Finset G) (h : G) : Finset G := S.filter (fun z => z+h ∈ S)

omit [Fintype G] [Fintype A] [Fintype B] in
lemma allBlocks_additive_iff (S : A → B → Finset G) (h : G) (hh : h ≠ 0)
    (x : (Rep (fun x : G => x+h) × A) × Fin 2)
    (y : (Rep (fun x : G => x+h) × B) × Fin 2) :
    allBlocks (fun x y => (labeledPairing h hh x).1 + (labeledPairing h hh y).1 ∈ S x.1.2 y.1.2) x y ↔
      (labeledPairing h hh x).1 + (labeledPairing h hh y).1 ∈
        differenceFiber (S x.1.2 y.1.2) h := by
  rcases x with ⟨⟨x,a⟩,i⟩
  rcases y with ⟨⟨y,b⟩,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [allBlocks, labeledPairing, differenceFiber, Fin.forall_fin_succ,
      add_assoc, add_left_comm, add_comm, and_comm]

/-- The graph consisting of complete paired blocks is exactly the graph with
connection sets `S ∩ (S+h)`, after relabeling the actual point coordinates. -/
def blocksIso (S : A → B → Finset G) (h : G) (hh : h ≠ 0) :
    relationGraph (allBlocks (fun x y =>
      (labeledPairing h hh x).1 + (labeledPairing h hh y).1 ∈ S x.1.2 y.1.2)) ≃g
    relationGraph (fun x : G × A => fun y : G × B =>
      x.1+y.1 ∈ differenceFiber (S x.2 y.2) h) where
  toEquiv := (labeledPairing h hh).sumCongr (labeledPairing h hh)
  map_rel_iff' := by
    intro p q
    cases p with
    | inl x =>
      cases q with
      | inl x' => simp [relationGraph, Erdos714Packing.incidence]
      | inr y =>
        simp only [relationGraph, Erdos714Packing.incidence, Equiv.sumCongr_apply,
          Sum.map_inl, Sum.map_inr, mem_filter, mem_univ, true_and]
        exact (allBlocks_additive_iff S h hh x y).symm
    | inr y =>
      cases q with
      | inr y' => simp [relationGraph, Erdos714Packing.incidence]
      | inl x =>
        simp only [relationGraph, Erdos714Packing.incidence, Equiv.sumCongr_apply,
          Sum.map_inl, Sum.map_inr, mem_filter, mem_univ, true_and]
        exact (allBlocks_additive_iff S h hh x y).symm

omit [Fintype A] [Fintype B] in
lemma translate_card (S : Finset G) (x : G) :
    (univ.filter (fun y => x+y ∈ S)).card = S.card := by
  apply card_bij (fun y _ => x+y)
  · intro y hy
    simpa using hy
  · intro y hy z hz he
    exact add_left_cancel he
  · intro z hz
    refine ⟨x+z, ?_, ?_⟩
    · simpa using hz
    · simp

omit [Fintype A] in
lemma translation_neighbor_card (S : A → B → Finset G) (x : G) (a : A) :
    (univ.filter (fun y : G × B => x+y.1 ∈ S a y.2)).card = ∑ b, (S a b).card := by
  calc
    _ = ∑ b, (univ.filter (fun y => x+y ∈ S a b)).card := by
      simp only [card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
      rw [sum_comm]
    _ = _ := sum_congr rfl (fun b _ => translate_card (S a b) x)

/-- Exact edge count in a partial-translation graph, allowing arbitrary fibers. -/
theorem translation_edges (S : A → B → Finset G) :
    (relationGraph (fun x : G × A => fun y : G × B => x.1+y.1 ∈ S x.2 y.2)).edgeFinset.card =
      Fintype.card G * ∑ a, ∑ b, (S a b).card := by
  rw [relationGraph, Erdos714Packing.incidence_edges]
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ _x : G, ∑ a : A, ∑ b : B, (S a b).card := by
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro a _
      convert translation_neighbor_card S x a using 2
      ext y
      simp
    _ = _ := by simp only [sum_const, card_univ, smul_eq_mul]

/-- The exact single-shift shadow count, including its factor four. -/
theorem additiveShadow_edges (S : A → B → Finset G) (h : G) (hh : h ≠ 0) :
    4 * (additiveShadow (fun a b => (S a b : Set G)) h hh).edgeFinset.card =
      Fintype.card G * ∑ a, ∑ b, (differenceFiber (S a b) h).card := by
  have he := allBlocks_edges (fun x y =>
    (labeledPairing h hh x).1 + (labeledPairing h hh y).1 ∈ S x.1.2 y.1.2)
  rw [(blocksIso S h hh).card_edgeFinset_eq] at he
  rw [translation_edges (fun a b => differenceFiber (S a b) h)] at he
  exact he.symm

omit [Fintype A] [Fintype B] in
lemma differences_at_point (S : Finset G) (z : G) :
    ((univ.erase 0).filter (fun h => z+h ∈ S)).card = (S.erase z).card := by
  apply card_bij (fun h _ => z+h)
  · intro h hh
    simp only [mem_filter, mem_erase, mem_univ, and_true] at hh ⊢
    exact ⟨by simpa using hh.1, hh.2⟩
  · intro h hh k hk he
    exact add_left_cancel he
  · intro t ht
    simp only [mem_erase] at ht
    refine ⟨z+t, ?_, ?_⟩
    · simp only [mem_filter, mem_erase, mem_univ, and_true]
      exact ⟨by simpa [CharTwo.add_eq_zero] using ht.1.symm, by simpa using ht.2⟩
    · simp

omit [Fintype A] [Fintype B] in
/-- Summing over nonzero differences counts ordered distinct pairs in `S`. -/
theorem sum_differenceFiber_card (S : Finset G) :
    ∑ h ∈ univ.erase (0 : G), (differenceFiber S h).card = S.card * (S.card-1) := by
  conv_lhs => simp only [differenceFiber, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  have he (z : G) : (∑ h ∈ univ.erase (0 : G), if z+h ∈ S then 1 else 0) =
      (S.erase z).card := by
    simpa only [card_eq_sum_ones, sum_filter] using differences_at_point S z
  simp_rw [he]
  calc
    _ = ∑ _z ∈ S, (S.card-1) := sum_congr rfl (fun z hz => card_erase_of_mem hz)
    _ = S.card*(S.card-1) := by simp

omit [Fintype A] [Fintype B] in
lemma sum_differenceFiber_nonzero (S : Finset G) :
    ∑ h : {h : G // h ≠ 0}, (differenceFiber S h.val).card = S.card * (S.card-1) := by
  rw [← Finset.sum_subtype (univ.erase (0 : G)) (fun h => by simp)
    (fun h => (differenceFiber S h).card)]
  exact sum_differenceFiber_card S

/-- Summing every nonzero-shift shadow counts all ordered distinct connection pairs. -/
theorem sum_additiveShadow_edges (S : A → B → Finset G) :
    4 * (∑ h : {h : G // h ≠ 0},
      (additiveShadow (fun a b => (S a b : Set G)) h.val h.property).edgeFinset.card) =
      Fintype.card G * ∑ a, ∑ b, (S a b).card * ((S a b).card-1) := by
  rw [mul_sum]
  simp_rw [additiveShadow_edges]
  rw [←mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]
  exact sum_congr rfl (fun b _ => sum_differenceFiber_nonzero (S a b))

omit [Fintype G] [Fintype A] [Fintype B] in
lemma orbit_rep_unique (h : G) {x y : Rep (fun x : G => x+h)}
    (hxy : x.val=y.val ∨ x.val=y.val+h) : x=y := by
  rcases hxy with hxy | hxy
  · exact Subtype.ext hxy
  · have hx := x.property
    rw [hxy] at hx
    simp only [CharTwo.add_cancel_right] at hx
    exact False.elim (lt_asymm hx y.property)

omit [Fintype A] in
/-- The usual uniqueness of unordered pairs in each local connection set
makes every fixed-label shadow block at most a matching. It does not prevent
C4s using different labels. -/
theorem fixed_label_matching (S : A → B → Set G) (h : G) (hh : h ≠ 0)
    (a : A) (b : B)
    (hSidon : ∀ z w : G, z ∈ S a b → z+h ∈ S a b →
      w ∈ S a b → w+h ∈ S a b → z=w ∨ z=w+h)
    (x y z : Rep (fun x : G => x+h))
    (hy : (additiveShadow S h hh).Adj (.inl (x,a)) (.inr (y,b)))
    (hz : (additiveShadow S h hh).Adj (.inl (x,a)) (.inr (z,b))) : y=z := by
  obtain ⟨hy₀,hy₁⟩ := (additiveShadow_adj S h hh (x,a) (y,b)).mp hy
  obtain ⟨hz₀,hz₁⟩ := (additiveShadow_adj S h hh (x,a) (z,b)).mp hz
  apply orbit_rep_unique h
  rcases hSidon (x.val+y.val) (x.val+z.val) hy₀ hy₁ hz₀ hz₁ with he | he
  · exact Or.inl (add_left_cancel he)
  · exact Or.inr (add_left_cancel (by simpa only [add_assoc] using he))

end Binary

#print axioms rectangleCopy
#print axioms shadow_free
#print axioms allBlocks_edges
#print axioms involutionPairing
#print axioms rep_card
#print axioms additiveShadow_free
#print axioms additiveShadow_adj
#print axioms blocksIso
#print axioms translation_edges
#print axioms additiveShadow_edges
#print axioms sum_differenceFiber_card
#print axioms sum_additiveShadow_edges
#print axioms fixed_label_matching

end Erdos714PairedShadow
