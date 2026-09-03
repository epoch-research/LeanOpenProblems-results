import Submission.RootFreeQuadraticDilation

/-! The root-free phase transform preserves local quadraticity and commutes
with integer phase combinations. The new coordinates therefore remain valid
quadratic coordinates after one coordinate is eliminated. -/
namespace Erdos3RootFreePhaseStructure
open Finset Erdos3RootFreeQuadraticDilation Erdos3BoundedFrequencyPhaseApproximation
  Erdos3LocalQuadraticInverse Erdos3LocalQuadraticProgressions Erdos3FiniteUniformity
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

lemma derivative_mul_fun (f g : G → ℂ) (h : G) :
    derivative (fun x ↦ f x*g x) h = fun x ↦ derivative f h x*derivative g h x := by
  funext x
  simp only [derivative,map_mul]
  ring

lemma derivative_pow_fun (f : G → ℂ) (n : ℕ) (h : G) :
    derivative (fun x ↦ (f x)^n) h = fun x ↦ (derivative f h x)^n := by
  funext x
  simp only [derivative,map_pow,mul_pow]

lemma derivative_conj_fun (f : G → ℂ) (h : G) :
    derivative (fun x ↦ conj (f x)) h = fun x ↦ conj (derivative f h x) := by
  funext x
  simp only [derivative,map_mul,starRingEnd_self_apply]

lemma IsLocallyQuadratic.mul {R : Set G} {f g : G → ℂ}
    (hf : IsLocallyQuadratic R f) (hg : IsLocallyQuadratic R g) :
    IsLocallyQuadratic R (fun x ↦ f x*g x) := by
  intro x h k l hx hxh hxk hxkh hxl hxlh hxlk hxlkh
  rw [derivative_mul_fun,derivative_mul_fun,derivative_mul_fun]
  dsimp only
  rw [hf x h k l hx hxh hxk hxkh hxl hxlh hxlk hxlkh,
    hg x h k l hx hxh hxk hxkh hxl hxlh hxlk hxlkh,one_mul]

lemma IsLocallyQuadratic.pow {R : Set G} {f : G → ℂ}
    (hf : IsLocallyQuadratic R f) (n : ℕ) : IsLocallyQuadratic R (fun x ↦ (f x)^n) := by
  intro x h k l hx hxh hxk hxkh hxl hxlh hxlk hxlkh
  rw [derivative_pow_fun,derivative_pow_fun,derivative_pow_fun]
  dsimp only
  rw [hf x h k l hx hxh hxk hxkh hxl hxlh hxlk hxlkh,one_pow]

lemma IsLocallyQuadratic.conj {R : Set G} {f : G → ℂ}
    (hf : IsLocallyQuadratic R f) : IsLocallyQuadratic R (fun x ↦ conj (f x)) := by
  intro x h k l hx hxh hxk hxkh hxl hxlh hxlk hxlkh
  rw [derivative_conj_fun,derivative_conj_fun,derivative_conj_fun]
  dsimp only
  rw [hf x h k l hx hxh hxk hxkh hxl hxlh hxlk hxlkh,map_one]

lemma unit_const_quadratic (R : Set G) (c : ℂ) (hc : ‖c‖ = 1) :
    IsLocallyQuadratic R (fun _ ↦ c) := by
  intro x h k l hx hxh hxk hxkh hxl hxlh hxlk hxlkh
  simp only [derivative,mul_conj_eq_one hc,map_one,mul_one]

lemma IsLocallyQuadratic.comp_affine {R : Set G} {S : Set H} {q : G → ℂ}
    (hq : IsLocallyQuadratic R q) (e : H →+ G) (b : G)
    (hdom : ∀ x ∈ S, b+e x ∈ R) : IsLocallyQuadratic S (fun x ↦ q (b+e x)) := by
  intro x h k l hx hxh hxk hxkh hxl hxlh hxlk hxlkh
  have ht := hq (b+e x) (e h) (e k) (e l) (hdom x hx)
    (by simpa only [map_add,add_assoc] using hdom (x+h) hxh)
    (by simpa only [map_add,add_assoc] using hdom (x+k) hxk)
    (by simpa only [map_add,add_assoc] using hdom ((x+k)+h) hxkh)
    (by simpa only [map_add,add_assoc] using hdom (x+l) hxl)
    (by simpa only [map_add,add_assoc] using hdom ((x+l)+h) hxlh)
    (by simpa only [map_add,add_assoc] using hdom ((x+l)+k) hxlk)
    (by simpa only [map_add,add_assoc] using hdom (((x+l)+k)+h) hxlkh)
  simpa only [derivative,map_add,add_assoc] using ht

/-- Only the first two sampled points are needed to retain local quadraticity
of the transformed coordinate. The 2n-dilate identity has its own domain checks. -/
theorem rootFreeTransform_locally_quadratic {R S : Set G} {q : G → ℂ}
    (hq : ∀ x, ‖q x‖ = 1) (hquad : IsLocallyQuadratic R q) (n : ℕ) (b : G)
    (h1 : ∀ x ∈ S, b+x ∈ R) (h2 : ∀ x ∈ S, b+(2 : ℕ) • x ∈ R) :
    IsLocallyQuadratic S (rootFreeTransform n q b) := by
  have hA : IsLocallyQuadratic S (fun x ↦ q (b+x)) :=
    IsLocallyQuadratic.comp_affine hquad (AddMonoidHom.id G) b h1
  have hB : IsLocallyQuadratic S (fun x ↦ q (b+(2 : ℕ) • x)) :=
    IsLocallyQuadratic.comp_affine hquad (nsmulAddMonoidHom 2) b h2
  have hU : IsLocallyQuadratic S (fun x ↦ derivative q x b) := by
    exact IsLocallyQuadratic.mul hA (unit_const_quadratic S (conj (q b)) (by rw [Complex.norm_conj,hq]))
  have hV : IsLocallyQuadratic S (fun x ↦ derivative (derivative q x) x b) := by
    have ht := IsLocallyQuadratic.mul (IsLocallyQuadratic.mul hB
      (IsLocallyQuadratic.pow (IsLocallyQuadratic.conj hA) 2)) (unit_const_quadratic S (q b) (hq b))
    convert ht using 1
    funext x
    simp only [derivative,two_nsmul,map_mul,starRingEnd_self_apply,add_assoc]
    ring
  exact IsLocallyQuadratic.mul (IsLocallyQuadratic.pow hU 2) (IsLocallyQuadratic.pow hV (2*n-1))

lemma zpow_pow_comm (a : ℂ) (k : ℤ) (n : ℕ) : (a^k)^n = (a^n)^k := by
  rw [← zpow_natCast,← zpow_mul,mul_comm k,zpow_mul,zpow_natCast]

variable {I : Type*} [Fintype I] [DecidableEq I] [Fintype G]

/-- Integer phase combinations commute exactly with the root-free transform. -/
theorem rootFreeTransform_integerPhase (n : ℕ) (k : I → ℤ) (Q : I → G → ℂ) (b x : G) :
    rootFreeTransform n (fun y ↦ integerPhase k (fun i ↦ Q i y)) b x =
      integerPhase k (fun i ↦ rootFreeTransform n (Q i) b x) := by
  simp only [rootFreeTransform,derivative_integerPhase]
  simp only [integerPhase,← prod_pow,zpow_pow_comm,mul_zpow,prod_mul_distrib]

#print axioms rootFreeTransform_locally_quadratic
#print axioms rootFreeTransform_integerPhase
end Erdos3RootFreePhaseStructure
