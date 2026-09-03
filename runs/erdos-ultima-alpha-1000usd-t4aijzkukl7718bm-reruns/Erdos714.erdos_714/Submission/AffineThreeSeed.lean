import FormalConjecturesUtil

/-!
A finite affine-incidence example and its exact balanced-biclique threshold.
Over a field with q elements it has 2*q^4 vertices and q^7 edges and is
K_(q+1,q+1)-free, but contains K_(q,q). In particular q=3 supplies a finite
K44-free graph, not an unbounded family for the fourth case of Erdős 714.
-/

noncomputable section
open Classical SimpleGraph Matrix
set_option maxHeartbeats 2000000

namespace Erdos714AffineThree

variable {F : Type*} [Field F] [Fintype F]

/-- More than q distinct rows span a space of dimension at least two. -/
lemma two_le_rank_of_injective {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J F) (hA : Function.Injective A)
    (hcard : Fintype.card F < Fintype.card I) : 2 ≤ A.rank := by
  let S := Submodule.span F (Set.range A.row)
  letI : Fintype S := Fintype.ofFinite S
  let f : I → S := fun i => ⟨A i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hf : Function.Injective f := fun i j h => hA (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hf
  have hs : Fintype.card S = Fintype.card F ^ A.rank := by
    rw [A.rank_eq_finrank_span_row]
    exact Module.card_eq_pow_finrank
  rw [hs] at hc
  by_contra! h
  have hp : Fintype.card F ^ A.rank ≤ Fintype.card F := by
    calc
      _ ≤ Fintype.card F ^ 1 :=
        Nat.pow_le_pow_right (by have := Fintype.card_pos (α := F); omega) (by omega)
      _ = _ := pow_one _
  omega

abbrev Point (F : Type*) := (Fin 3 → F) × F

/-- A rectangle of affine incidence in dimension three has a side of size at most q. -/
theorem no_rectangle {r : ℕ} (hr : Fintype.card F < r)
    (a b : Fin r → Point F) (ha : Function.Injective a) (hb : Function.Injective b)
    (h : ∀ i j, (a i).2 + (b j).2 = (a i).1 ⬝ᵥ (b j).1) : False := by
  have hr0 : 0 < r := (Fintype.card_pos (α := F)).trans hr
  let z : Fin r := ⟨0, hr0⟩
  have ha' : Function.Injective (fun i => (a i).1) := by
    intro i j hij
    change (a i).1 = (a j).1 at hij
    apply ha
    apply Prod.ext hij
    have hi := h i z
    have hj := h j z
    rw [hij] at hi
    exact add_right_cancel (hi.trans hj.symm)
  have hb' : Function.Injective (fun i => (b i).1) := by
    intro i j hij
    change (b i).1 = (b j).1 at hij
    apply hb
    apply Prod.ext hij
    have hi := h z i
    have hj := h z j
    rw [hij] at hi
    exact add_left_cancel (hi.trans hj.symm)
  let A : Matrix (Fin r) (Fin 3) F := fun i => (a i).1 - (a z).1
  let B : Matrix (Fin r) (Fin 3) F := fun i => (b i).1 - (b z).1
  have hA : 2 ≤ A.rank := two_le_rank_of_injective A
    (fun _ _ he => ha' (sub_left_injective he)) (by simpa using hr)
  have hB : 2 ≤ B.rank := two_le_rank_of_injective B
    (fun _ _ he => hb' (sub_left_injective he)) (by simpa using hr)
  have hAB : A * B.transpose = 0 := by
    ext i j
    change ((a i).1 - (a z).1) ⬝ᵥ ((b j).1 - (b z).1) = 0
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub,
      ← h i j, ← h i z, ← h z j, ← h z z]
    ring
  have hh := Matrix.rank_add_rank_le_card_of_mul_eq_zero hAB
  rw [Matrix.rank_transpose, Fintype.card_fin] at hh
  omega

/-- Two copies of the coefficient/constant space, with the symmetric incidence convention. -/
def graph (F : Type*) [Field F] : SimpleGraph (Bool × Point F) where
  Adj u v := u.1 ≠ v.1 ∧ u.2.2 + v.2.2 = u.2.1 ⬝ᵥ v.2.1
  symm := by
    intro u v h
    exact ⟨h.1.symm, by simpa only [add_comm, dotProduct_comm] using h.2⟩
  loopless := by intro v h; exact h.1 rfl

private lemma bool_eq_of_ne {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- The affine-incidence graph has no balanced biclique larger than its base field. -/
theorem graph_free {r : ℕ} (hr : Fintype.card F < r) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free (graph F) := by
  rintro ⟨f⟩
  have hr0 : 0 < r := (Fintype.card_pos (α := F)).trans hr
  let z : Fin r := ⟨0, hr0⟩
  let a (i : Fin r) := f (Sum.inl i)
  let b (j : Fin r) := f (Sum.inr j)
  have hadj (i j : Fin r) : (graph F).Adj (a i) (b j) :=
    f.toHom.map_adj (by simp)
  have ha : Function.Injective (fun i => (a i).2) := by
    intro i j hij
    have he : a i = a j := Prod.ext (bool_eq_of_ne (hadj i z).1 (hadj j z).1) hij
    exact Sum.inl.inj (f.injective he)
  have hb : Function.Injective (fun j => (b j).2) := by
    intro i j hij
    have he : b i = b j := Prod.ext
      (bool_eq_of_ne (hadj z i).1.symm (hadj z j).1.symm) hij
    exact Sum.inr.inj (f.injective he)
  exact no_rectangle hr (fun i => (a i).2) (fun j => (b j).2) ha hb
    (fun i j => (hadj i j).2)

/-- Orthogonal affine lines supply every balanced biclique of size at most q. -/
def lineCopy {r : ℕ} (e : Fin r ↪ F) :
    (completeBipartiteGraph (Fin r) (Fin r)).Copy (graph F) where
  toHom := {
    toFun := Sum.elim
      (fun i => (false, (![e i, 0, 0], 0)))
      (fun j => (true, (![0, e j, 0], 0)))
    map_rel' := by
      intro x y h
      cases x with
      | inl i =>
        cases y with
        | inl j => simp at h
        | inr j => simp [graph, dotProduct, Fin.sum_univ_succ]
      | inr i =>
        cases y with
        | inl j => simp [graph, dotProduct, Fin.sum_univ_succ]
        | inr j => simp at h }
  injective' := by
    intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        apply congrArg Sum.inl
        apply e.injective
        exact congrArg (fun p : Bool × Point F => p.2.1 0) h
      | inr j => exact Bool.noConfusion (congrArg Prod.fst h)
    | inr i =>
      cases y with
      | inl j => exact Bool.noConfusion (congrArg Prod.fst h)
      | inr j =>
        apply congrArg Sum.inr
        apply e.injective
        exact congrArg (fun p : Bool × Point F => p.2.1 1) h

/-- An exact threshold, not an asymptotic assertion. -/
theorem graph_free_iff (r : ℕ) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free (graph F) ↔ Fintype.card F < r := by
  constructor
  · intro h
    by_contra! hr
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin r) (β := F)
      (by simpa using hr)
    exact h ⟨lineCopy e⟩
  · exact graph_free

/-- The three vector coordinates parameterize each neighborhood. -/
def neighborEquiv (v : Bool × Point F) : (graph F).neighborSet v ≃ (Fin 3 → F) where
  toFun w := w.val.2.1
  invFun x := ⟨(!v.1, (x, v.2.1 ⬝ᵥ x - v.2.2)), by
    constructor
    · cases hv : v.1 <;> simp
    · dsimp
      ring⟩
  left_inv := by
    rintro ⟨⟨s, x, y⟩, hw⟩
    apply Subtype.ext
    change (!v.1, (x, v.2.1 ⬝ᵥ x - v.2.2)) = (s, (x, y))
    apply Prod.ext
    · have hs := hw.1
      cases hv : v.1 <;> cases s <;> simp_all
    · apply Prod.ext
      · rfl
      have hh := hw.2
      change v.2.2 + y = v.2.1 ⬝ᵥ x at hh
      dsimp
      linear_combination -hh
  right_inv x := rfl

/-- The degree is exactly q cubed. -/
theorem graph_degree (v : Bool × Point F) :
    (graph F).degree v = Fintype.card F ^ 3 := by
  rw [← card_neighborSet_eq_degree]
  simpa using Fintype.card_congr (neighborEquiv v)

omit [Field F] in
/-- Both parts have q to the fourth vertices. -/
theorem vertex_count : Fintype.card (Bool × Point F) = 2 * Fintype.card F ^ 4 := by
  simp [Point, pow_succ, mul_assoc]

/-- The graph has exactly q to the seventh edges. -/
theorem edge_count : (graph F).edgeFinset.card = Fintype.card F ^ 7 := by
  have h := (graph F).sum_degrees_eq_twice_card_edges
  simp only [graph_degree, Finset.sum_const, Finset.card_univ, vertex_count, smul_eq_mul] at h
  have he : (2 * Fintype.card F ^ 4) * Fintype.card F ^ 3 = 2 * Fintype.card F ^ 7 := by ring
  rw [he] at h
  omega

/-- A genuine finite lower bound, with the forbidden part size growing with q. -/
theorem finite_lower_bound : Fintype.card F ^ 7 ≤
    extremalNumber (2 * Fintype.card F ^ 4)
      (completeBipartiteGraph (Fin (Fintype.card F + 1)) (Fin (Fintype.card F + 1))) := by
  have h := card_edgeFinset_le_extremalNumber (graph_free (F := F) (Nat.lt_succ_self _))
  simpa only [vertex_count, edge_count] using h

/-- The characteristic-three seed has 162 vertices and 2187 edges. -/
theorem ternary_lower_bound :
    2187 ≤ extremalNumber 162 (completeBipartiteGraph (Fin 4) (Fin 4)) := by
  simpa using finite_lower_bound (F := ZMod 3)

/-- Increasing the field size beyond three loses K44-freeness. -/
theorem not_four_free (hq : 4 ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph F) := by
  rw [graph_free_iff]
  omega

end Erdos714AffineThree

#print axioms Erdos714AffineThree.no_rectangle
#print axioms Erdos714AffineThree.graph_free_iff
#print axioms Erdos714AffineThree.edge_count
#print axioms Erdos714AffineThree.ternary_lower_bound
#print axioms Erdos714AffineThree.not_four_free
