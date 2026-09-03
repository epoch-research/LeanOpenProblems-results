import Submission.TriangleHit

/-!
A boundary case of the Hilbert-space approach. Unit vectors whose edge inner
products are at most -1/2 give a two-piece triangle-free edge cover, without
any cardinality restriction. This is an auxiliary result, not a settlement
of Erdős 595.
-/

open SimpleGraph Set

namespace Erdos595VectorThree

private theorem sign_not_mono {A : Type*} [AddCommGroup A] [LinearOrder A]
    [IsOrderedAddMonoid A] (x y z : A) (hz : z ≠ 0) (h : x + y + z = 0) :
    ¬(decide (0 < x + y) = decide (0 < x + z) ∧
      decide (0 < x + y) = decide (0 < y + z)) := by
  intro ⟨h₁, h₂⟩
  have hsum : (x + y) + (x + z) + (y + z) = 0 := by
    calc
      _ = (x + y + z) + (x + y + z) := by abel
      _ = 0 := by rw [h]; simp
  have hn : x + y ≠ 0 := by
    intro he
    rw [he, zero_add] at h
    exact hz h
  by_cases hp : 0 < x + y
  · have hq : 0 < x + z := by simpa only [decide_eq_true hp, true_eq_decide_iff] using h₁
    have hr : 0 < y + z := by simpa only [decide_eq_true hp, true_eq_decide_iff] using h₂
    have ht := add_pos (add_pos hp hq) hr
    rw [hsum] at ht
    exact (lt_irrefl _) ht
  · have hq : x + z ≤ 0 := by
      have he : ¬0 < x + z := by
        simpa only [decide_eq_false hp, false_eq_decide_iff] using h₁
      exact le_of_not_gt he
    have hr : y + z ≤ 0 := by
      have he : ¬0 < y + z := by
        simpa only [decide_eq_false hp, false_eq_decide_iff] using h₂
      exact le_of_not_gt he
    have ht := add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le
      (lt_of_le_of_ne (le_of_not_gt hp) hn) hq) hr
    simp only [add_zero] at ht
    rw [hsum] at ht
    exact (lt_irrefl _) ht

/-- Nonzero vector labels summing to zero on every triangle yield a
triangle-free edge cover with just two pieces. -/
theorem two_cover_of_zero_sum_triangles {V E : Type*} [AddCommGroup E] [Module ℝ E]
    (G : SimpleGraph V) (v : V → E) (hne : ∀ a, v a ≠ 0)
    (hsum : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c → v a + v b + v c = 0) :
    ∃ H : Bool → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i := by
  classical
  let I := Module.Free.ChooseBasisIndex ℝ E
  let b := Module.Free.chooseBasis ℝ E
  letI : LinearOrder I := IsWellOrder.linearOrder (@WellOrderingRel I)
  let w : V → Lex (I →₀ ℝ) := fun a => toLex (b.repr (v a))
  have hwne : ∀ a, w a ≠ 0 := by
    intro a he
    apply hne a
    apply b.repr.injective
    simpa only [map_zero] using congrArg ofLex he
  have hw : ∀ a d c, G.Adj a d → G.Adj a c → G.Adj d c → w a + w d + w c = 0 := by
    intro a d c had hac hdc
    have he := congrArg (fun x => toLex (b.repr x)) (hsum a d c had hac hdc)
    simpa only [map_add, map_zero, toLex_add, toLex_zero] using he
  let code : V → V → Bool := fun a d => decide (0 < w a + w d)
  let H : Bool → SimpleGraph V := fun i =>
    { Adj := fun a d => G.Adj a d ∧ code a d = i
      symm := fun a d h => ⟨h.1.symm, by simpa only [code, add_comm] using h.2⟩
      loopless := fun a h => G.loopless a h.1 }
  refine ⟨H, ?_, ?_⟩
  · intro i t ht
    obtain ⟨a, d, c, had, hac, hdc, _⟩ := SimpleGraph.is3Clique_iff.mp ht
    exact sign_not_mono (w a) (w d) (w c) (hwne c) (hw a d c had.1 hac.1 hdc.1)
      ⟨had.2.trans hac.2.symm, had.2.trans hdc.2.symm⟩
  · ext a d
    simp only [SimpleGraph.iSup_adj]
    constructor
    · intro had
      exact ⟨code a d, had, rfl⟩
    · rintro ⟨i, hi⟩
      exact hi.1

private theorem triangle_sum_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y z : E)
    (hx : inner ℝ x x = 1) (hy : inner ℝ y y = 1) (hz : inner ℝ z z = 1)
    (hxy : inner ℝ x y ≤ -(1 / 2 : ℝ)) (hxz : inner ℝ x z ≤ -(1 / 2 : ℝ))
    (hyz : inner ℝ y z ≤ -(1 / 2 : ℝ)) : x + y + z = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  have hpos : 0 ≤ inner ℝ (x + y + z) (x + y + z) := by
    simpa only [RCLike.re_to_real] using
      (inner_self_nonneg (𝕜 := ℝ) (x := x + y + z))
  have hex : inner ℝ (x + y + z) (x + y + z) =
      3 + 2 * (inner ℝ x y + inner ℝ x z + inner ℝ y z) := by
    simp only [inner_add_left, inner_add_right, hx, hy, hz]
    rw [real_inner_comm y x, real_inner_comm z x, real_inner_comm z y]
    ring
  rw [hex] at hpos ⊢
  linarith

/-- Strict vector 3-colorability implies two-piece triangle-free edge
coverability, even for graphs of arbitrarily large cardinality. -/
theorem two_cover_of_unit_inner_le_neg_half {V E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (G : SimpleGraph V) (v : V → E)
    (hunit : ∀ a, inner ℝ (v a) (v a) = 1)
    (hv : ∀ a b, G.Adj a b → inner ℝ (v a) (v b) ≤ -(1 / 2 : ℝ)) :
    ∃ H : Bool → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i := by
  apply two_cover_of_zero_sum_triangles G v
  · intro a ha
    have h := hunit a
    simp only [ha, inner_zero_left] at h
    norm_num at h
  · intro a b c hab hac hbc
    exact triangle_sum_zero (v a) (v b) (v c) (hunit a) (hunit b) (hunit c)
      (hv a b hab) (hv a c hac) (hv b c hbc)

#print axioms two_cover_of_unit_inner_le_neg_half

/-- If each triangle has an edge at the -1/2 threshold, three triangle-free
pieces suffice: two for the threshold edges, and one for all other edges. -/
theorem three_cover_of_triangle_hit_neg_half {V E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (G : SimpleGraph V) (v : V → E)
    (hunit : ∀ a, inner ℝ (v a) (v a) = 1)
    (hv : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c →
      inner ℝ (v a) (v b) ≤ -(1 / 2 : ℝ) ∨
      inner ℝ (v a) (v c) ≤ -(1 / 2 : ℝ) ∨
      inner ℝ (v b) (v c) ≤ -(1 / 2 : ℝ)) :
    ∃ H : Option Bool → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i := by
  classical
  let N : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ inner ℝ (v a) (v b) ≤ -(1 / 2 : ℝ)
      symm := fun a b h => ⟨h.1.symm, by simpa only [real_inner_comm] using h.2⟩
      loopless := fun a h => G.loopless a h.1 }
  let R : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ -(1 / 2 : ℝ) < inner ℝ (v a) (v b)
      symm := fun a b h => ⟨h.1.symm, by simpa only [real_inner_comm] using h.2⟩
      loopless := fun a h => G.loopless a h.1 }
  obtain ⟨H, hH, hcov⟩ := two_cover_of_unit_inner_le_neg_half N v hunit (fun _ _ h => h.2)
  have hle : ∀ i, H i ≤ G := by
    intro i a b hab
    have hn : N.Adj a b := by
      rw [hcov, SimpleGraph.iSup_adj]
      exact ⟨i, hab⟩
    exact hn.1
  let K : Option Bool → SimpleGraph V
    | none => R
    | some i => H i
  refine ⟨K, ?_, ?_⟩
  · intro i
    cases i with
    | none =>
      intro t ht
      obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp ht
      rcases hv a b c hab.1 hac.1 hbc.1 with h | h | h
      · exact (not_le_of_gt hab.2) h
      · exact (not_le_of_gt hac.2) h
      · exact (not_le_of_gt hbc.2) h
    | some i => exact hH i
  · ext a b
    simp only [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      by_cases h : inner ℝ (v a) (v b) ≤ -(1 / 2 : ℝ)
      · have hn : N.Adj a b := ⟨hab, h⟩
        rw [hcov, SimpleGraph.iSup_adj] at hn
        obtain ⟨i, hi⟩ := hn
        exact ⟨some i, hi⟩
      · exact ⟨none, hab, lt_of_not_ge h⟩
    · rintro ⟨i, hi⟩
      cases i with
      | none => exact hi.1
      | some i => exact hle i hi

#print axioms three_cover_of_triangle_hit_neg_half

end Erdos595VectorThree
