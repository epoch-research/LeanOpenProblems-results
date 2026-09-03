import Submission.LocalCharacterApproximation
import Submission.LocalQuadraticProgressions

/-! Local polarization and approximate ambient-character representations of
derivatives of arbitrary unit locally quadratic phases. The representations
are approximate, not exact extensions of local characters. -/
namespace Erdos3LocalQuadraticPolarization
open Finset Erdos3LocalCharacterApproximation Erdos3LocalQuadraticProgressions
  Erdos3LocalQuadraticInverse Erdos3FiniteUniformity Erdos3FiniteFourier
  Erdos3CorrelationSifting Erdos3FiniteBohr Erdos3FourierSmoothing
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G]

noncomputable def localPolar (q : G → ℂ) (h x : G) : ℂ :=
  derivative q h x*conj (derivative q h 0)

lemma localPolar_norm (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (h x : G) :
    ‖localPolar q h x‖ = 1 := by
  simp only [localPolar,norm_mul,Complex.norm_conj,derivative_norm_one q hq,one_mul]

lemma localPolar_zero (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (h : G) :
    localPolar q h 0 = 1 := mul_conj_eq_one (derivative_norm_one q hq h 0)

lemma localPolar_symmetric (q : G → ℂ) (h x : G) :
    localPolar q h x = localPolar q x h := by
  simp only [localPolar,derivative,zero_add,map_mul,starRingEnd_self_apply]
  rw [add_comm h x]
  ring

lemma derivative_eq_localPolar (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (h x : G) :
    derivative q h x = derivative q h 0*localPolar q h x := by
  dsimp [localPolar]
  have he := mul_conj_eq_one (derivative_norm_one q hq h 0)
  calc
    _ = derivative q h x*(derivative q h 0*conj (derivative q h 0)) := by rw [he,mul_one]
    _ = _ := by ring

/-- The cube identity gives local multiplicativity of each normalized
derivative, with all eight vertices explicitly required to lie in R. -/
theorem localPolar_add {R : Set G} {q : G → ℂ}
    (hq : ∀ x, ‖q x‖ = 1) (hquad : IsLocallyQuadratic R q)
    (h x y : G) (h0 : 0 ∈ R) (hh : h ∈ R)
    (hx : x ∈ R) (hxh : x+h ∈ R) (hy : y ∈ R) (hyh : y+h ∈ R)
    (hxy : x+y ∈ R) (hxyh : (x+y)+h ∈ R) :
    localPolar q h (x+y) = localPolar q h x*localPolar q h y := by
  have he := hquad 0 h x y h0 (by simpa using hh) (by simpa using hx)
    (by simpa using hxh) (by simpa using hy) (by simpa using hyh)
    (by simpa only [zero_add,add_comm y x] using hxy)
    (by simpa only [zero_add,add_comm y x] using hxyh)
  change derivative (derivative q h) x (0+y)*
    conj (derivative (derivative q h) x 0) = 1 at he
  have he' := unit_conj_cancel
    (derivative_norm_one (derivative q h) (derivative_norm_one q hq h) x 0) he
  simp only [one_mul,zero_add] at he'
  change derivative q h (y+x)*conj (derivative q h y) =
    derivative q h (0+x)*conj (derivative q h 0) at he'
  rw [zero_add] at he'
  have he'' := unit_conj_cancel (derivative_norm_one q hq h y) he'
  change derivative q h (y+x) =
    (derivative q h x*conj (derivative q h 0))*derivative q h y at he''
  dsimp only [localPolar]
  rw [add_comm x y,he'']
  ring

variable [Fintype G]

/-- Character approximation for a fixed derivative on arbitrary inner sets.
The domain hypotheses ensure genuine local multiplicativity, rather than
assuming it from notation. -/
theorem exists_local_derivative_character (R : Set G) (W P : Finset G)
    (hW : W.Nonempty) (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1)
    (hquad : IsLocallyQuadratic R q) (h : G) (h0 : 0 ∈ R) (hh : h ∈ R)
    (hWR : ∀ x ∈ W, x ∈ R ∧ x+h ∈ R)
    (hPR : ∀ y ∈ P, y ∈ R ∧ y+h ∈ R)
    (hstable : ∀ y ∈ P, boundary W y ≤ density W/2)
    {ρ : ℝ} (hρ : 0 < ρ) (hsize : 4*ρ^2*density W ≤ density P) :
    ∃ ψ : AddChar G ℂ,
      ρ ≤ ‖𝔼 x : W, localPolar q h x*conj (ψ x)‖ ∧
      ∀ y : G, y ∈ R → y+h ∈ R →
        ∀ δ : ℝ, (𝔼 x : G, |normalized W (x+y)-normalized W x|) ≤ δ →
          ‖localPolar q h y-ψ y‖ ≤ δ/ρ := by
  have hlin (y : G) (hy : y ∈ R) (hyh : y+h ∈ R)
      (x : G) (hx : x ∈ W) (hxy : x+y ∈ W) :
      localPolar q h (x+y) = localPolar q h y*localPolar q h x := by
    rw [localPolar_add hq hquad h x y h0 hh (hWR x hx).1 (hWR x hx).2
      hy hyh (hWR (x+y) hxy).1 (hWR (x+y) hxy).2,mul_comm]
  obtain ⟨ψ,hψ,herr⟩ := exists_normalized_local_character W P hW
    (localPolar q h) (localPolar q h) (localPolar_norm q hq h)
    (fun y _ ↦ localPolar_norm q hq h y)
    (fun y hy ↦ hlin y (hPR y hy).1 (hPR y hy).2)
    hstable hρ hsize
  refine ⟨ψ,hψ,?_⟩
  intro y hy hyh δ hδ
  rw [norm_sub_rev]
  exact herr y (localPolar q h y) (localPolar_norm q hq h y) (hlin y hy hyh) δ hδ

#print axioms localPolar_add
#print axioms exists_local_derivative_character
end Erdos3LocalQuadraticPolarization
