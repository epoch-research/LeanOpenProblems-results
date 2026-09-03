import Submission.RoughConicCancellation
import Submission.AffineQuadraticSelectionMass
import Submission.FiniteDilationMass
import Submission.RoughSquarefreePrimitiveMass

/-! Distinct whole-root cover obstructions on squarefree primitive collisions
coprime to any fixed modulus and below every compact gap cutoff. Proper-divisor
covers and the density conjecture remain outside the scope of this result. -/
namespace Erdos1206.RoughSquarefreeWholeRootMass
open Finset Filter RoughSquarefreeConicSetup RoughSquarefreePrimitiveFamily
open PrimitiveCollisionMass (Collision)
open scoped Classical Topology

def coordinate (e : Collision) : Fin 4 → ℕ :=
  ![e.val.1,e.val.2.1,e.val.2.2.1,e.val.2.2.2]

namespace Progression
variable {D : Data} (P : RoughSquarefreePrimitiveFamily.Progression D)

lemma root_eval (i : Fin 4) :
    AffineQuadraticImageMass.eval (D.C i) (D.B i) (D.A i) P.M P.v P.w=P.root i := by
  funext x
  dsimp [AffineQuadraticImageMass.eval,RoughSquarefreePrimitiveFamily.Progression.root,
    RoughSquarefreePrimitiveFamily.Progression.T,RoughSquarefreePrimitiveFamily.Progression.U,
    Data.F,QuadraticSquarefreeSieve.quad]
  ring

lemma C_pos (i : Fin 4) : 0 < D.C i := by
  apply Nat.mul_pos (D.dn_pos i)
  have hh := D.gamma_pos i
  rw [←D.cast_cn] at hh
  exact_mod_cast hh

lemma raw_selected_not_summable (sel : ℕ × ℕ → Fin 4) :
    ¬ Summable (fun n : ℕ =>
      if n∈(fun x => P.root (sel x) x) '' {x | P.Good x} then (1:ℝ)/n else 0) := by
  have hd (i : Fin 4) : 4*(D.C i:ℤ)*D.A i-(D.B i:ℤ)^2 ≠ 0 := by
    have hh := D.full_discriminant_ne i
    dsimp [QuadraticSquarefreeSieve.discriminant] at hh
    intro he
    apply hh
    nlinarith only [he]
  have hm : ∀ᶠ N : ℕ in atTop, (N:ℝ)^2/2 ≤
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
  have hh := AffineQuadraticSelectionMass.selected_values_not_summable
    D.C D.B D.A P.M P.v P.w (C_pos (D := D)) D.A_pos P.M_pos hd P.Good sel
    (fun x _ => by rw [root_eval]; exact P.root_pos (sel x) x) hm
  simpa only [root_eval] using hh

lemma scale_coordinate (x : P.Index) (i : Fin 4) :
    P.root i x.val=P.scale x*coordinate (P.collision x) i := by
  obtain ⟨hg,h0,h1,h2,h3⟩ := P.scale_spec x
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- Distinct normalized selected values have divergent reciprocal mass.
The selector may vary arbitrarily and different parameters may reuse a root. -/
theorem normalized_selected_not_summable (sel : P.Index → Fin 4) :
    ¬ Summable (fun n : ℕ =>
      if n∈Set.range (fun x => coordinate (P.collision x) (sel x)) then (1:ℝ)/n else 0) := by
  let sel' (x : ℕ × ℕ) : Fin 4 := if hx : P.Good x then sel ⟨x,hx⟩ else 0
  have he : Set.range (fun x : P.Index => P.root (sel x) x.val)=
      (fun x => P.root (sel' x) x) '' {x | P.Good x} := by
    ext n
    constructor
    · rintro ⟨x,rfl⟩
      refine ⟨x.val,x.property,?_⟩
      simp [sel',x.property]
    · rintro ⟨x,hx,rfl⟩
      change P.Good x at hx
      refine ⟨⟨x,hx⟩,?_⟩
      simp [sel',hx]
  apply FiniteDilationMass.image_not_summable_of_bounded_normalization
    (fun x : P.Index => P.root (sel x) x.val)
    (fun x => coordinate (P.collision x) (sel x)) (RoughConicCancellation.Progression.bound P)
  · intro x
    exact ⟨P.scale x,mem_Icc.mpr ⟨(P.scale_spec x).1,
      RoughConicCancellation.Progression.scale_le P x⟩,scale_coordinate P x (sel x)⟩
  · rw [he]
    exact raw_selected_not_summable P sel'

theorem no_summable_root_cover (B : Set ℕ)
    (hB : ∀ x : P.Index, ∃ i : Fin 4, coordinate (P.collision x) i∈B) :
    ¬ Summable (fun n : ℕ => if n∈B then (1:ℝ)/n else 0) := by
  choose sel hs using hB
  intro hsum
  apply normalized_selected_not_summable P sel
  apply FiniteDilationMass.subset_summable ?_ hsum
  rintro n ⟨x,rfl⟩
  exact hs x

end Progression

open RoughSquarefreePrimitiveMass

/-- The arbitrary-modulus rough residual source admits no summable cover by
whole roots. A single covered root may be reused for arbitrarily many edges. -/
theorem no_summable_residual_root_cover (Q H : ℕ) (hQ : 0 < Q) (B : Set ℕ)
    (hB : ∀ e : Residual Q H, ∃ i : Fin 4, coordinate e.val i∈B) :
    ¬ Summable (fun n : ℕ => if n∈B then (1:ℝ)/n else 0) := by
  obtain ⟨D,hDq,hDH⟩ := exists_data Q H hQ
  obtain ⟨P⟩ := exists_progression D
  apply Progression.no_summable_root_cover P B
  intro x
  have hQq : Q∣D.q := by rw [hDq]; exact dvd_mul_left _ _
  obtain ⟨hg,h0,h1,h2,h3⟩ := P.collision_properties x
  rw [hDH] at hg
  let e : Residual Q H := ⟨P.collision x,hg,
    ⟨h0.1,Nat.Coprime.of_dvd_right hQq h0.2⟩,
    ⟨h1.1,Nat.Coprime.of_dvd_right hQq h1.2⟩,
    ⟨h2.1,Nat.Coprime.of_dvd_right hQq h2.2⟩,
    ⟨h3.1,Nat.Coprime.of_dvd_right hQq h3.2⟩⟩
  exact hB e

/-- In particular, the sum is over distinct maximum roots, not collisions. -/
theorem residual_maxima_not_summable (Q H : ℕ) (hQ : 0 < Q) :
    ¬ Summable (fun n : ℕ =>
      if n∈Set.range (fun e : Residual Q H => e.val.val.2.2.2) then (1:ℝ)/n else 0) := by
  apply no_summable_residual_root_cover Q H hQ
  intro e
  exact ⟨3,e,rfl⟩

#print axioms Progression.normalized_selected_not_summable
#print axioms no_summable_residual_root_cover
#print axioms residual_maxima_not_summable
end Erdos1206.RoughSquarefreeWholeRootMass
