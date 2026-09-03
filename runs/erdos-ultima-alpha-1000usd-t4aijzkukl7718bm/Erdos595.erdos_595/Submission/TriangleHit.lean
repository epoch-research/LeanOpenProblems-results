import Submission.NegativeInner

/-!
A sufficient condition for a countable triangle-free edge cover: a real
Hilbert-space assignment that makes at least one edge of every triangle
strictly negative. The existence of such assignments for arbitrary K4-free
graphs is not established here.
-/

open SimpleGraph Set

namespace Erdos595TriangleHit

variable {V : Type*}

/-- Countable covers are closed under adjoining a single triangle-free graph. -/
theorem cover_sup_triangleFree (G R : SimpleGraph V)
    (hG : Erdos595Work.IsCountableUnionOfTriangleFree G) (hR : R.CliqueFree 3) :
    Erdos595Work.IsCountableUnionOfTriangleFree (G ⊔ R) := by
  obtain ⟨H, hH, he⟩ := hG
  let K : ℕ → SimpleGraph V
    | 0 => R
    | n + 1 => H n
  refine ⟨K, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact hR
    | succ n => exact hH n
  · ext a b
    simp only [SimpleGraph.sup_adj, he, SimpleGraph.iSup_adj]
    constructor
    · rintro (⟨n, hn⟩ | hr)
      · exact ⟨n + 1, hn⟩
      · exact ⟨0, hr⟩
    · rintro ⟨n, hn⟩
      cases n with
      | zero => exact Or.inr hn
      | succ n => exact Or.inl ⟨n, hn⟩

/-- A real Hilbert representation need not make every edge negative: it
suffices for the negative edges to meet every triangle. -/
theorem countable_cover_of_triangle_hit {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (G : SimpleGraph V) (v : V → E)
    (hv : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c →
      inner ℝ (v a) (v b) < 0 ∨ inner ℝ (v a) (v c) < 0 ∨ inner ℝ (v b) (v c) < 0) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  classical
  let N : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ inner ℝ (v a) (v b) < 0
      symm := fun a b h => ⟨h.1.symm, by simpa only [real_inner_comm] using h.2⟩
      loopless := fun a h => G.loopless a h.1 }
  let R : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ 0 ≤ inner ℝ (v a) (v b)
      symm := fun a b h => ⟨h.1.symm, by simpa only [real_inner_comm] using h.2⟩
      loopless := fun a h => G.loopless a h.1 }
  have hN : Erdos595Work.IsCountableUnionOfTriangleFree N :=
    Erdos595NegativeInner.countable_cover_of_negative_inner N v (fun _ _ h => h.2)
  have hR : R.CliqueFree 3 := by
    intro t ht
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp ht
    rcases hv a b c hab.1 hac.1 hbc.1 with h | h | h
    · exact (not_lt_of_ge hab.2) h
    · exact (not_lt_of_ge hac.2) h
    · exact (not_lt_of_ge hbc.2) h
  have he : G = N ⊔ R := by
    ext a b
    change G.Adj a b ↔ (G.Adj a b ∧ inner ℝ (v a) (v b) < 0) ∨
      (G.Adj a b ∧ 0 ≤ inner ℝ (v a) (v b))
    constructor
    · intro hab
      rcases lt_or_ge (inner ℝ (v a) (v b)) 0 with h | h
      · exact Or.inl ⟨hab, h⟩
      · exact Or.inr ⟨hab, h⟩
    · rintro (h | h) <;> exact h.1
  rw [he]
  exact cover_sup_triangleFree N R hN hR

/-- Every proposed counterexample must defeat every real Hilbert-space
assignment: some triangle has three nonnegative inner products. -/
theorem nonnegative_triangle_of_no_cover {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (G : SimpleGraph V) (hG : ¬Erdos595Work.IsCountableUnionOfTriangleFree G)
    (v : V → E) : ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      0 ≤ inner ℝ (v a) (v b) ∧ 0 ≤ inner ℝ (v a) (v c) ∧
      0 ≤ inner ℝ (v b) (v c) := by
  by_contra! hn
  apply hG (countable_cover_of_triangle_hit G v ?_)
  intro a b c hab hac hbc
  by_cases h₁ : inner ℝ (v a) (v b) < 0
  · exact Or.inl h₁
  by_cases h₂ : inner ℝ (v a) (v c) < 0
  · exact Or.inr (Or.inl h₂)
  exact Or.inr (Or.inr (hn a b c hab hac hbc (le_of_not_gt h₁) (le_of_not_gt h₂)))

#print axioms countable_cover_of_triangle_hit
#print axioms nonnegative_triangle_of_no_cover

end Erdos595TriangleHit
