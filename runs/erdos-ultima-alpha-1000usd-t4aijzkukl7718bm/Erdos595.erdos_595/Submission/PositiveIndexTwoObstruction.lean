import Submission.PositiveIndexTwoOrder

/-!
The finite triangle-free Mycielski graph of C5 has no positive-index-two
orthogonality representation over ANY ordered field, even with an arbitrary
positive semidefinite bilinear space as the negative part. A finite generic
rotation removes the chart restriction from PositiveIndexTwoOrder.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open SimpleGraph Set
namespace Erdos595PositiveIndexTwoObstruction
open Erdos595PositiveIndexTwoOrder

variable {K E V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup E] [Module K E]
  (Q : LinearMap.BilinForm K E)
  (hs : ∀ x y, Q x y = Q y x) (hp : ∀ x, 0 ≤ Q x x)

abbrev MVertex := Erdos595MycielskiFiveOrder.Vertex
abbrev MGraph := Erdos595MycielskiFiveOrder.graph

include hs hp in
lemma no_representation_in_chart (p₀ p₁ : MVertex → K) (q : MVertex → E)
    (hn : ∀ v, p₀ v ≠ 0)
    (hr : ∀ v, 0 < p₀ v * p₀ v + p₁ v * p₁ v - Q (q v) (q v))
    (he : ∀ a b, MGraph.Adj a b →
      p₀ a * p₀ b + p₁ a * p₁ b - Q (q a) (q b) = 0) : False := by
  let t : MVertex → K := fun v => p₁ v / p₀ v
  let r : MVertex → E := fun v => (p₀ v)⁻¹ • q v
  have hnorm (v : MVertex) : radius Q t r v =
      (p₀ v * p₀ v + p₁ v * p₁ v - Q (q v) (q v)) / (p₀ v * p₀ v) := by
    simp only [Erdos595PositiveIndexTwoOrder.radius,t,r,map_smul,LinearMap.smul_apply,smul_eq_mul]
    field_simp [hn v]
  have hpos (v : MVertex) : 0 < radius Q t r v := by
    rw [hnorm]
    exact div_pos (hr v) (mul_self_pos.mpr (hn v))
  apply no_mycielski_normalized Q hs hp t r hpos
  intro a b hab
  have h := he a b hab
  change 1 + (p₁ a / p₀ a) * (p₁ b / p₀ b) -
    Q ((p₀ a)⁻¹ • q a) ((p₀ b)⁻¹ • q b) = 0
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  field_simp [hn a,hn b]
  nlinarith

lemma exists_rotation [Finite V] (p₀ p₁ : V → K)
    (hn : ∀ v, ¬(p₀ v = 0 ∧ p₁ v = 0)) :
    ∃ α : K, ∀ v, p₀ v + α * p₁ v ≠ 0 := by
  classical
  obtain ⟨α,hα⟩ := (Set.finite_range (fun v => -p₀ v / p₁ v)).exists_notMem
  refine ⟨α, ?_⟩
  intro v h
  by_cases hv : p₁ v = 0
  · have hp₀ : p₀ v = 0 := by simpa only [hv,mul_zero,add_zero] using h
    exact hn v ⟨hp₀,hv⟩
  · apply hα
    refine ⟨v, (div_eq_iff hv).mpr ?_⟩
    linarith

include hs hp in
/-- Clique-freeness alone does not supply even a positive-index-two
representation of a triangle-free graph. The obstruction is finite. -/
theorem no_representation (p₀ p₁ : MVertex → K) (q : MVertex → E)
    (hr : ∀ v, 0 < p₀ v * p₀ v + p₁ v * p₁ v - Q (q v) (q v))
    (he : ∀ a b, MGraph.Adj a b →
      p₀ a * p₀ b + p₁ a * p₁ b - Q (q a) (q b) = 0) : False := by
  have hn (v : MVertex) : ¬(p₀ v = 0 ∧ p₁ v = 0) := by
    rintro ⟨h₀,h₁⟩
    have h := hr v
    have hq := hp (q v)
    rw [h₀,h₁] at h
    nlinarith
  obtain ⟨α,hα⟩ := exists_rotation p₀ p₁ hn
  let Q' : LinearMap.BilinForm K E := (1 + α*α) • Q
  have hQ' (x y : E) : Q' x y = (1+α*α) * Q x y := rfl
  have hαpos : 0 < 1+α*α := by nlinarith [mul_self_nonneg α]
  have hs' (x y : E) : Q' x y = Q' y x := by rw [hQ',hQ',hs]
  have hp' (x : E) : 0 ≤ Q' x x := mul_nonneg (le_of_lt hαpos) (hp x)
  let a (v : MVertex) := p₀ v + α*p₁ v
  let b (v : MVertex) := p₁ v - α*p₀ v
  have ident (v w : MVertex) :
      a v * a w + b v * b w - Q' (q v) (q w) =
      (1+α*α) * (p₀ v * p₀ w + p₁ v * p₁ w - Q (q v) (q w)) := by
    rw [hQ']
    dsimp only [a,b]
    ring
  apply no_representation_in_chart Q' hs' hp' a b q hα
  · intro v
    rw [ident]
    exact mul_pos hαpos (hr v)
  · intro v w hvw
    rw [ident,he v w hvw,mul_zero]

#print axioms no_representation_in_chart
#print axioms exists_rotation
#print axioms no_representation
end Erdos595PositiveIndexTwoObstruction
