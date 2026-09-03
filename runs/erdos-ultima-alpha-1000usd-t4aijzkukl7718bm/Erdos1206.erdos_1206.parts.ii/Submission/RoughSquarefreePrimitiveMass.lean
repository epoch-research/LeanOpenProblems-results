import Submission.RoughSquarefreePrimitiveFamily
import Submission.QuadraticParameterMass

/-!
Squarefree primitive collisions, coprime to any fixed modulus and outside
any compact adjacent-gap cutoff, have divergent reciprocal maximum-root
mass. This counts collisions; it does not rule out a reusable cover or
settle the Sidon-density conjecture.
-/
namespace Erdos1206.RoughSquarefreePrimitiveMass
open Finset Filter RoughSquarefreeConicSetup RoughSquarefreePrimitiveFamily
open PrimitiveCollisionMass (Collision)
open scoped Classical Topology

lemma index_mass_not_summable {D : Data} (P : Progression D) :
    ¬ Summable (fun x : P.Index => (1:ℝ)/(P.collision x).val.2.2.2) := by
  let S : ℕ := D.A 3+D.B 3+D.C 3
  let K : ℕ := S*(P.M+P.v+P.w+1)
  have hS : 0 < S := by have := D.A_pos 3; dsimp [S]; omega
  have hK : 0 < K := by dsimp [K]; positivity
  have hbound : ∀ N, 0 < N → ∀ x ∈ (range N) ×ˢ (range N),
      P.root 3 x ≤ (K*N)^2 := by
    intro N hN x hx
    exact (AffineQuadraticSquarefreeSieve.quad_size_bound
      (D.A 3) (D.B 3) (D.C 3) P.M P.v P.w N S (D.A_pos 3) P.w_pos le_rfl hN hx).2
  have hmany : ∀ᶠ N : ℕ in atTop, (N:ℝ)^2/2 ≤
      (((range N) ×ˢ (range N)).filter P.Good).card := by
    filter_upwards [P.many] with N hN
    have he : ((range N) ×ˢ (range N)).filter P.Good =
        ((range N) ×ˢ (range N)).filter (fun x =>
          ∀ i, Squarefree (D.F i (P.M*x.1+P.v) (P.M*x.2+P.w))) := by
      ext x
      simp [RoughSquarefreePrimitiveFamily.Progression.Good,
        RoughSquarefreePrimitiveFamily.Progression.root,
        RoughSquarefreePrimitiveFamily.Progression.T,RoughSquarefreePrimitiveFamily.Progression.U]
    rw [he]
    exact hN
  have hraw := QuadraticParameterMass.reciprocal_not_summable P.Good (P.root 3) K hK
    (P.root_pos 3) hbound hmany
  intro hs
  apply hraw
  apply hs.of_nonneg_of_le (fun _ => by positivity)
  intro x
  have he := (P.collision x).property
  have hp : 0 < (P.collision x).val.2.2.2 :=
    ((he.1.trans he.2.1).trans he.2.2.1).trans he.2.2.2.1
  obtain ⟨hg,h0,h1,h2,h3⟩ := P.scale_spec x
  have hle : (P.collision x).val.2.2.2 ≤ P.root 3 x.val := by
    rw [h3]
    exact Nat.le_mul_of_pos_left _ hg
  exact one_div_le_one_div_of_le (by exact_mod_cast hp) (by exact_mod_cast hle)

abbrev Residual (Q H : ℕ) := {e : Collision //
  H*(e.val.2.1-e.val.1) < (H+1)*(e.val.2.2.2-e.val.2.2.1) ∧
  (Squarefree e.val.1 ∧ Nat.Coprime e.val.1 Q) ∧
  (Squarefree e.val.2.1 ∧ Nat.Coprime e.val.2.1 Q) ∧
  (Squarefree e.val.2.2.1 ∧ Nat.Coprime e.val.2.2.1 Q) ∧
  (Squarefree e.val.2.2.2 ∧ Nat.Coprime e.val.2.2.2 Q)}

/-- Divergence remains after requiring all roots to be squarefree, coprime
to Q, and below an arbitrary compact gap-ratio cutoff. -/
theorem residual_reciprocal_heights_not_summable (Q H : ℕ) (hQ : 0 < Q) :
    ¬ Summable (fun e : Residual Q H => (1:ℝ)/e.val.val.2.2.2) := by
  intro hs
  obtain ⟨D,hDq,hDH⟩ := exists_data Q H hQ
  obtain ⟨P⟩ := exists_progression D
  have hQq : Q ∣ D.q := by rw [hDq]; exact dvd_mul_left _ _
  have hprop (x : P.Index) :
      H*((P.collision x).val.2.1-(P.collision x).val.1) <
        (H+1)*((P.collision x).val.2.2.2-(P.collision x).val.2.2.1) ∧
      (Squarefree (P.collision x).val.1 ∧ Nat.Coprime (P.collision x).val.1 Q) ∧
      (Squarefree (P.collision x).val.2.1 ∧ Nat.Coprime (P.collision x).val.2.1 Q) ∧
      (Squarefree (P.collision x).val.2.2.1 ∧ Nat.Coprime (P.collision x).val.2.2.1 Q) ∧
      (Squarefree (P.collision x).val.2.2.2 ∧ Nat.Coprime (P.collision x).val.2.2.2 Q) := by
    obtain ⟨hg,h0,h1,h2,h3⟩ := P.collision_properties x
    rw [hDH] at hg
    exact ⟨hg,⟨h0.1,Nat.Coprime.of_dvd_right hQq h0.2⟩,
      ⟨h1.1,Nat.Coprime.of_dvd_right hQq h1.2⟩,
      ⟨h2.1,Nat.Coprime.of_dvd_right hQq h2.2⟩,
      ⟨h3.1,Nat.Coprime.of_dvd_right hQq h3.2⟩⟩
  let f : P.Index → Residual Q H := fun x => ⟨P.collision x,hprop x⟩
  have hf : Function.Injective f := by
    intro x y he
    have hh := congrArg (fun e : Residual Q H => e.val) he
    exact P.collision_injective hh
  have hcomp := hs.comp_injective hf
  exact index_mass_not_summable P hcomp

#print axioms index_mass_not_summable
#print axioms residual_reciprocal_heights_not_summable
end Erdos1206.RoughSquarefreePrimitiveMass
