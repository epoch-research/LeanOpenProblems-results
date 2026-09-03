import FormalConjecturesUtil

/-! A branch-square-class obstruction on the six projective roots used by
  the standard heptad. This is NOT an upper bound for rational-distance sets.
  The obstruction is independent of polynomial degree: two simple-supported
  square forms cannot agree nontrivially at three other supported roots. -/
namespace Erdos213.HeptadResidualSquareClasses

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Indices 0 through 4 denote -2,-1,-1/2,0,1; index 5 denotes infinity. -/
def rootValue : Fin 6 → ℚ := ![-2,-1,-1/2,0,1,0]

/-- Evaluation of a homogeneous root factor, with a harmless choice of sign
at infinity. Factors for infinity are the constant affine polynomial 1. -/
def rootEval (r m : Fin 6) : ℚ :=
  if m=5 then (if r=5 then 0 else 1)
  else if r=5 then 1 else rootValue m-rootValue r

def crossClass (r s a b : Fin 6) : ℚ :=
  rootEval s a / rootEval r a * rootEval r b / rootEval s b

lemma rootEval_ne_zero : ∀ r m : Fin 6, r≠m → rootEval r m≠0 := by
  decide +kernel

/-- The finite certificate is checked by kernel reduction, including exact
rational-square decisions. No external computation is used by this proof. -/
lemma branch_square_obstruction : ∀ r s a b c : Fin 6,
    Function.Injective (![r,s,a,b,c] : Fin 5 → Fin 6) →
    ¬ (IsSquare (crossClass r s a b) ∧ IsSquare (crossClass r s a c)) := by
  decide +kernel

lemma compatible_values_force_square
    {A₀ A₁ B₀ B₁ u₀ u₁ v₀ v₁ α β : ℚ}
    (hA₀ : A₀≠0) (hB₁ : B₁≠0) (hu₁ : u₁≠0) (hv₀ : v₀≠0) (hβ : β≠0)
    (h₀ : α*A₀*u₀^2=β*B₀*v₀^2) (h₁ : α*A₁*u₁^2=β*B₁*v₁^2) :
    IsSquare (B₀/A₀*A₁/B₁) := by
  have h : B₀*A₁*(u₁*v₀)^2=A₀*B₁*(v₁*u₀)^2 := by
    apply mul_left_cancel₀ hβ
    linear_combination (A₀*u₀^2)*h₁-(A₁*u₁^2)*h₀
  refine ⟨v₁*u₀/(u₁*v₀), ?_⟩
  rw [← pow_two]
  field_simp
  nlinarith only [h]

/-- This algebraic obstruction allows arbitrary rational values at the three
roots. In particular it does not depend on a coefficient-height search or a
bound on the degrees of prospective squared polynomial factors. -/
theorem no_three_compatible_values
    {r s a b c : Fin 6}
    (hi : Function.Injective (![r,s,a,b,c] : Fin 5 → Fin 6))
    {α β : ℚ} (hβ : β≠0) (U V : Fin 3 → ℚ)
    (hU : ∀ i, U i≠0) (hV : ∀ i, V i≠0)
    (h₀ : α*rootEval r a*(U 0)^2=β*rootEval s a*(V 0)^2)
    (h₁ : α*rootEval r b*(U 1)^2=β*rootEval s b*(V 1)^2)
    (h₂ : α*rootEval r c*(U 2)^2=β*rootEval s c*(V 2)^2) : False := by
  have hra : r≠a := hi.ne (by decide : (0 : Fin 5)≠2)
  have hsb : s≠b := hi.ne (by decide : (1 : Fin 5)≠3)
  have hsc : s≠c := hi.ne (by decide : (1 : Fin 5)≠4)
  apply branch_square_obstruction r s a b c hi
  constructor
  · exact compatible_values_force_square (rootEval_ne_zero r a hra)
      (rootEval_ne_zero s b hsb) (hU 1) (hV 0) hβ h₀ h₁
  · exact compatible_values_force_square (rootEval_ne_zero r a hra)
      (rootEval_ne_zero s c hsc) (hU 2) (hV 0) hβ h₀ h₂

#print axioms rootEval_ne_zero
#print axioms branch_square_obstruction
#print axioms compatible_values_force_square
#print axioms no_three_compatible_values

end Erdos213.HeptadResidualSquareClasses
