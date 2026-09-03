import FormalConjecturesUtil

/-! An obstruction to a digit-count quadratic certificate template.
This does not settle the conjecture about powers of two. -/

namespace Erdos406QuadraticCount

/-- The coefficient inequalities obtained when a quadratic count potential is
certified by a linear carry-state correction over the entire nonnegative
count cone. These inequalities force a symmetric quadratic part to be a
multiple of the square of word length. -/
theorem quadratic_count_rigidity
    (Q : Fin 3 → Fin 3 → ℝ) (A B : Fin 4 → Fin 3 → ℝ)
    (hsym : ∀ a b, Q a b = Q b a)
    (hstep : ∀ (s t : Fin 4) (d e : Fin 3),
      4 * d.val + t.val = 3 * s.val + e.val →
      ∀ a b, 0 ≤ -2 * Q d a - A t a + A s a +
        2 * Q e b - B t b + B s b) :
    ∀ a b, Q a b = Q 0 0 := by
  have hrow0 : ∀ a b, Q 0 a = Q 0 b := by
    intro a b
    have h := hstep 0 0 0 0 (by decide) a b
    have h' := hstep 0 0 0 0 (by decide) b a
    linarith
  have hrow2 : ∀ a b, Q 2 a = Q 2 b := by
    intro a b
    have h := hstep 3 3 2 2 (by decide) a b
    have h' := hstep 3 3 2 2 (by decide) b a
    linarith
  have h02 : Q 0 2 = Q 0 0 := hrow0 2 0
  have h01 : Q 0 1 = Q 0 0 := hrow0 1 0
  have h20 : Q 2 0 = Q 0 0 := (hsym 2 0).trans h02
  have h21 : Q 2 1 = Q 0 0 := (hrow2 1 0).trans h20
  have h22 : Q 2 2 = Q 0 0 := (hrow2 2 0).trans h20
  have h10 : Q 1 0 = Q 0 0 := (hsym 1 0).trans h01
  have h12 : Q 1 2 = Q 0 0 := (hsym 1 2).trans h21
  have hup := hstep 2 2 1 0 (by decide) 1 0
  have h₁ := hstep 0 1 0 1 (by decide) 0 1
  have h₂ := hstep 1 3 0 0 (by decide) 0 1
  have h₃ := hstep 3 2 2 1 (by decide) 0 1
  have h₄ := hstep 2 0 2 2 (by decide) 0 1
  rw [h01] at h₂
  rw [h20] at h₃
  rw [h20, h21] at h₄
  have h11 : Q 1 1 = Q 0 0 := by linarith
  intro a b
  fin_cases a <;> fin_cases b <;>
    first | rfl | assumption

/-- A version for a family of prefix-dependent matrices. Strong connectivity
is expressed using nonempty directed paths, including a cycle at each vertex.
It is an explicit hypothesis, not an assertion about all prefix graphs. -/
theorem quadratic_family_rigidity {σ : Type*} (R : σ → σ → Prop)
    (hconn : ∀ i j, Relation.TransGen R i j) (base : σ)
    (Q : σ → Fin 3 → Fin 3 → ℝ)
    (A B : σ → σ → Fin 4 → Fin 3 → ℝ)
    (hsym : ∀ i a b, Q i a b = Q i b a)
    (hstep : ∀ i j, R i j → ∀ (s t : Fin 4) (d e : Fin 3),
      4 * d.val + t.val = 3 * s.val + e.val →
      ∀ a b, 0 ≤ -2 * Q i d a - A i j t a + A i j s a +
        2 * Q j e b - B i j t b + B i j s b) :
    ∀ i a b, Q i a b = Q base 0 0 := by
  have hedge0 : ∀ i j, R i j → ∀ a b, Q i 0 a ≤ Q j 0 b := by
    intro i j hij a b
    have h := hstep i j hij 0 0 0 0 (by decide) a b
    linarith
  have hedge2 : ∀ i j, R i j → ∀ a b, Q i 2 a ≤ Q j 2 b := by
    intro i j hij a b
    have h := hstep i j hij 3 3 2 2 (by decide) a b
    linarith
  have hpath0 : ∀ i j, Relation.TransGen R i j → ∀ a b, Q i 0 a ≤ Q j 0 b := by
    intro i j hp
    induction hp with
    | single hij => exact hedge0 _ _ hij
    | @tail j k hp hjk ih =>
      intro a b
      exact (ih a 0).trans (hedge0 j k hjk 0 b)
  have hpath2 : ∀ i j, Relation.TransGen R i j → ∀ a b, Q i 2 a ≤ Q j 2 b := by
    intro i j hp
    induction hp with
    | single hij => exact hedge2 _ _ hij
    | @tail j k hp hjk ih =>
      intro a b
      exact (ih a 0).trans (hedge2 j k hjk 0 b)
  have hzero : ∀ i a, Q i 0 a = Q base 0 0 := by
    intro i a
    exact le_antisymm (hpath0 i base (hconn i base) a 0)
      (hpath0 base i (hconn base i) 0 a)
  have htwo' : ∀ i a, Q i 2 a = Q base 2 0 := by
    intro i a
    exact le_antisymm (hpath2 i base (hconn i base) a 0)
      (hpath2 base i (hconn base i) 0 a)
  have hlink : Q base 2 0 = Q base 0 0 := (hsym base 2 0).trans (hzero base 2)
  have htwo : ∀ i a, Q i 2 a = Q base 0 0 := fun i a => (htwo' i a).trans hlink
  have hcolzero : ∀ i a, Q i a 0 = Q base 0 0 :=
    fun i a => (hsym i a 0).trans (hzero i a)
  have hcoltwo : ∀ i a, Q i a 2 = Q base 0 0 :=
    fun i a => (hsym i a 2).trans (htwo i a)
  have hin : ∀ i, ∃ j, R j i := by
    intro i
    cases hconn i i with
    | single h => exact ⟨i, h⟩
    | tail _ h => exact ⟨_, h⟩
  have hfirst : ∀ i j, Relation.TransGen R i j → ∃ k, R i k := by
    intro i j hp
    induction hp with
    | single h => exact ⟨_, h⟩
    | tail _ _ ih => exact ih
  have hout : ∀ i, ∃ j, R i j := fun i => hfirst i i (hconn i i)
  have hdiag : ∀ i, Q i 1 1 = Q base 0 0 := by
    intro i
    obtain ⟨j, hij⟩ := hout i
    have hu := hstep i j hij 2 2 1 0 (by decide) 1 0
    rw [hzero j 0] at hu
    obtain ⟨k, hki⟩ := hin i
    have h₁ := hstep k i hki 0 1 0 1 (by decide) 0 1
    have h₂ := hstep k i hki 1 3 0 0 (by decide) 0 1
    have h₃ := hstep k i hki 3 2 2 1 (by decide) 0 1
    have h₄ := hstep k i hki 2 0 2 2 (by decide) 0 1
    rw [hzero k 0] at h₁
    rw [hzero k 0, hzero i 1] at h₂
    rw [htwo k 0] at h₃
    rw [htwo k 0, htwo i 1] at h₄
    linarith
  intro i a b
  fin_cases a <;> fin_cases b
  all_goals first | exact hzero _ _ | exact htwo _ _ |
    exact hcolzero _ _ | exact hcoltwo _ _ | exact hdiag _

#print axioms quadratic_count_rigidity
#print axioms quadratic_family_rigidity
end Erdos406QuadraticCount
