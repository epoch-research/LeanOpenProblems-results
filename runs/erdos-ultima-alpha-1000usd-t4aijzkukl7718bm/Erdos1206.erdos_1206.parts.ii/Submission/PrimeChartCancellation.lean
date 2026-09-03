import Submission.AllChartCancellation

/-! Exact cancellation in a four-prime example. This auxiliary result does
not settle the positive-density cube-Sidon conjecture. -/

namespace Erdos1206.PrimeChartCancellation
open CubicBaseLocus ChartCancellation

/-- Primitive certificates in a fixed nondegenerate signed chart have the
same absolute cancellation factor. -/
lemma certificate_natAbs_scale_eq {a b t g x y z w α β τ G : ℤ}
    (hg : g ≠ 0) (hG : G ≠ 0) (hx : x ≠ 0)
    (hInv : inverseT x y z w ≠ 0)
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (hprim' : Nat.gcd (Int.gcd α β) τ.natAbs = 1)
    (hA : A a b t = g*x) (hB : B a b t = g*y)
    (hC : C a b t = g*z) (hD : D a b t = g*w)
    (hα : A α β τ = G*x) (hβ : B α β τ = G*y)
    (hτ : C α β τ = G*z) (hδ : D α β τ = G*w) :
    G.natAbs = g.natAbs := by
  obtain ⟨hcA,hcB⟩ := certificate_cross_general hg hA hB hC hD
  obtain ⟨hcα,hcβ⟩ := certificate_cross_general hG hα hβ hτ hδ
  have ht : t ≠ 0 := by
    intro ht
    have ha : a = 0 := (mul_eq_zero.mp (by simpa [ht] using hcA.symm)).resolve_right hInv
    have hb : b = 0 := (mul_eq_zero.mp (by simpa [ht] using hcB.symm)).resolve_right hInv
    simp [ha,hb,ht] at hprim
  have hcrossA : t*α=a*τ := by
    apply mul_right_cancel₀ hInv
    linear_combination τ*hcA-t*hcα
  have hcrossB : t*β=b*τ := by
    apply mul_right_cancel₀ hInv
    linear_combination τ*hcB-t*hcβ
  obtain ⟨m,hmα,hmβ,hmτ⟩ := primitive_collinear_integer_signed hprim ht hcrossA hcrossB
  have hmabs : m.natAbs = 1 := by
    rw [hmα,hmβ,hmτ,Int.gcd_mul_left,Int.natAbs_mul,Nat.gcd_mul_left,
      hprim,mul_one] at hprim'
    exact hprim'
  have hGg : G = m^3*g := by
    apply mul_right_cancel₀ hx
    calc
      G*x = A α β τ := hα.symm
      _ = m^3*A a b t := by rw [hmα,hmβ,hmτ,(homogeneous a b t m).1]
      _ = (m^3*g)*x := by rw [hA]; ring
  rw [hGg,Int.natAbs_mul,Int.natAbs_pow,hmabs]
  simp

structure Certificate where
  a : ℤ
  b : ℤ
  t : ℤ
  g : ℤ

def signedRoots : Fin 4 → ℤ := ![17713, -42643, -57119, 63689]

def exampleCertificate (i : Fin 24) : Certificate :=
  match i.val with
  | 0 => ⟨-17312, 9270, 67179, 8932993167⟩
  | 1 => ⟨-35604, -9930, 10727, -2133097393⟩
  | 2 => ⟨-4168, 21454, 91917, 19197876537⟩
  | 3 => ⟨-89126, -43894, 13905, -26798979501⟩
  | 4 => ⟨-27028, -44786, -21947, 2977664389⟩
  | 5 => ⟨-41366, -61278, -14895, 6399292179⟩
  | 6 => ⟨-25674, 9930, 10727, 2133097393⟩
  | 7 => ⟨-26582, -9270, 67179, -8932993167⟩
  | 8 => ⟨17758, 44786, 21947, 2977664389⟩
  | 9 => ⟨-41366, -61278, 14895, -6399292179⟩
  | 10 => ⟨-25622, -21454, -91917, 19197876537⟩
  | 11 => ⟨-89126, -43894, -13905, 26798979501⟩
  | 12 => ⟨-45232, 43894, 13905, 26798979501⟩
  | 13 => ⟨-25622, -21454, 91917, -19197876537⟩
  | 14 => ⟨19912, 61278, 14895, 6399292179⟩
  | 15 => ⟨-27028, -44786, 21947, -2977664389⟩
  | 16 => ⟨-26582, -9270, -67179, 8932993167⟩
  | 17 => ⟨-35604, -9930, -10727, 2133097393⟩
  | 18 => ⟨19912, 61278, -14895, -6399292179⟩
  | 19 => ⟨17758, 44786, -21947, -2977664389⟩
  | 20 => ⟨-45232, 43894, -13905, -26798979501⟩
  | 21 => ⟨-4168, 21454, -91917, -19197876537⟩
  | 22 => ⟨-25674, 9930, -10727, -2133097393⟩
  | _ => ⟨-17312, 9270, -67179, -8932993167⟩

set_option maxHeartbeats 2000000 in
lemma example_audit (i : Fin 24) :
    let e := exampleCertificate i
    let x := signedRoots (chartIndices i 0)
    let y := -signedRoots (chartIndices i 1)
    let z := -signedRoots (chartIndices i 2)
    let w := signedRoots (chartIndices i 3)
    e.g ≠ 0 ∧ x ≠ 0 ∧ inverseT x y z w ≠ 0 ∧
    Nat.gcd (Int.gcd e.a e.b) e.t.natAbs = 1 ∧
    A e.a e.b e.t = e.g*x ∧ B e.a e.b e.t = e.g*y ∧
    C e.a e.b e.t = e.g*z ∧ D e.a e.b e.t = e.g*w ∧
    2133097393 ≤ e.g.natAbs := by
  fin_cases i <;>
    norm_num [exampleCertificate,signedRoots,chartIndices,A,B,C,D,Q,inverseT,
      Matrix.cons_val_two, Matrix.cons_val_three]

lemma example_prime_identity :
    Nat.Prime 17713 ∧ Nat.Prime 42643 ∧ Nat.Prime 57119 ∧ Nat.Prime 63689 ∧
    (17713 : ℕ)^3+63689^3=42643^3+57119^3 := by
  norm_num

/-- Even when all four roots are prime, every primitive certificate in any
of the 24 signed permutation charts can require substantial cancellation.
This is a single exact example, not an asymptotic unboundedness assertion. -/
theorem prime_example_cancellation_lower
    (p : Equiv.Perm (Fin 4)) {a b t g : ℤ} (hg : g ≠ 0)
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (hA : A a b t = g*signedRoots (p 0))
    (hB : B a b t = -g*signedRoots (p 1))
    (hC : C a b t = -g*signedRoots (p 2))
    (hD : D a b t = g*signedRoots (p 3)) :
    2133097393 ≤ g.natAbs := by
  obtain ⟨i,hi⟩ := chartIndices_exhaustive p p.injective
  obtain ⟨hG,hx,hInv,hprim',hα,hβ,hτ,hδ,hbound⟩ := example_audit i
  simp only [hi] at hx hInv hα hβ hτ hδ
  have heq := certificate_natAbs_scale_eq hg hG hx hInv hprim hprim'
    hA (by simpa only [mul_neg,neg_mul] using hB)
    (by simpa only [mul_neg,neg_mul] using hC) hD hα hβ hτ hδ
  rwa [heq] at hbound

#print axioms certificate_natAbs_scale_eq
#print axioms example_prime_identity
#print axioms prime_example_cancellation_lower

end Erdos1206.PrimeChartCancellation
