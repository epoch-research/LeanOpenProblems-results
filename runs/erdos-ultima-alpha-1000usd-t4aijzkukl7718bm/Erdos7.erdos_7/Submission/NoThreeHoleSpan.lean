import Submission.ExceptionalArithmetic
import Submission.MinimumTernaryClass

/-!
# Affine span of the holes of a distinct odd no-3 family

The absolute one-exception sieve implies that these holes are not contained
in any proper arithmetic progression. These are consequences of the sieve,
not a resolution of the odd covering conjecture.
-/
namespace Erdos7NoThreeHoleSpan
open Erdos7Reduction Erdos7MinimumTernaryClass
open Erdos7ExceptionalArithmetic
open scoped BigOperators
set_option maxHeartbeats 4000000

def Hole {I : Type*} (m : I → ℕ) (a : I → ℤ) (x : ℤ) : Prop :=
  ∀ i, ¬ (m i : ℤ) ∣ x-a i

/-- Permit a factor3 in the exceptional odd modulus as well. -/
theorem not_cover_with_odd_exception {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : ℕ) (hd : 1 < d ∧ Odd d) (b : ℤ) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ (d : ℤ) ∣ x-b) := by
  classical
  by_cases hd3 : 3 ∣ d
  · intro hcover
    choose a' ha' using fun i => affine_residue (m i) (h3 i) (a i) (b+1)
    have hc : IsOddArithmeticCover m a' := by
      refine ⟨hinj,hm,fun x => ?_⟩
      rcases hcover (3*x+(b+1)) with ⟨i,hi⟩ | hi
      · exact ⟨i,ha' i x hi⟩
      · have hh := (Int.natCast_dvd_natCast.mpr hd3).trans hi
        omega
    obtain ⟨i,hi⟩ := Erdos7No23Sieve.arithmetic_exists_three m a' hc
    exact h3 i hi
  · exact not_no_three_cover_with_exception m a hinj hm h3 d hd hd3 b

/-- There is a hole outside every proposed nontrivial odd exceptional class. -/
theorem hole_escape {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : ℕ) (hd : 1 < d ∧ Odd d) (b : ℤ) :
    ∃ x : ℤ, Hole m a x ∧ ¬ (d : ℤ) ∣ x-b := by
  classical
  by_contra! hn
  apply not_cover_with_odd_exception m a hinj hm h3 d hd b
  intro x
  by_cases hx : ∃ i, (m i : ℤ) ∣ x-a i
  · exact Or.inl hx
  · exact Or.inr (hn x (fun i hi => hx ⟨i,hi⟩))

lemma hole_add_period {I : Type*} (m : I → ℕ) (a : I → ℤ)
    (P : ℕ) (hP : ∀ i, m i ∣ P) (x : ℤ) (hx : Hole m a x) :
    Hole m a (x+P) := by
  intro i hi
  apply hx i
  have hp : (m i : ℤ) ∣ (P : ℤ) := Int.natCast_dvd_natCast.mpr (hP i)
  convert dvd_sub hi hp using 1 <;> ring

/-- Every common natural divisor of all hole differences is1. -/
theorem hole_difference_divisor {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : ℕ) (hspan : ∀ x y : ℤ, Hole m a x → Hole m a y → (d : ℤ) ∣ x-y) :
    d=1 := by
  classical
  obtain ⟨x₀,hx₀,_⟩ := hole_escape m a hinj hm h3 5 ⟨by decide,by decide⟩ 0
  let P := ∏ i, m i
  have hP : ∀ i, m i ∣ P := fun i => Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have hPodd : Odd P := Finset.prod_induction m Odd
    (fun _ _ hu hv => hu.mul hv) (by norm_num) (fun i _ => (hm i).2)
  have hdP : d ∣ P := by
    apply Int.natCast_dvd_natCast.mp
    simpa only [add_sub_cancel_left] using
      hspan (x₀+P) x₀ (hole_add_period m a P hP x₀ hx₀) hx₀
  have hdo := hPodd.of_dvd_nat hdP
  by_contra hne
  have hd0 := hdo.pos
  have hdgt : 1 < d := by omega
  obtain ⟨x,hx,hn⟩ := hole_escape m a hinj hm h3 d ⟨hdgt,hdo⟩ x₀
  exact hn (hspan x x₀ hx hx₀)

/-- The holes lie in one residue modulo d exactly when d=1. -/
theorem holes_in_residue_iff {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : ℕ) (b : ℤ) :
    (∀ x : ℤ, Hole m a x → (d : ℤ) ∣ x-b) ↔ d=1 := by
  constructor
  · intro h
    apply hole_difference_divisor m a hinj hm h3 d
    intro x y hx hy
    convert dvd_sub (h x hx) (h y hy) using 1 <;> ring
  · intro h
    subst d
    simp

/-- Coarse isolation of a 3-divisible class forces its modulus to be3 in ANY
odd cover. No irredundance or minimum-cardinality hypothesis is needed. -/
theorem isolated_ternary_modulus {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (j : I) (hj3 : 3 ∣ m j)
    (hiso : ∀ k, k ≠ j → 3 ∣ m k → ¬ (3 : ℤ) ∣ a k-a j) :
    m j=3 := by
  classical
  by_contra hjne
  obtain ⟨d,hjd⟩ := hj3
  have hd : 1 < d ∧ Odd d := by
    have hm := hc.2.1 j
    exact ⟨by omega,hm.2.of_dvd_nat (hjd ▸ dvd_mul_left d 3)⟩
  obtain ⟨b,hb⟩ := isolated_restriction m a hc j d hjd hiso
  apply not_cover_with_odd_exception (fun i : {i // ¬ 3 ∣ m i} => m i) b
    (hc.1.comp Subtype.val_injective) (fun i => hc.2.1 i) (fun i => i.property) d hd 0
  simpa only [sub_zero] using hb

#print axioms not_cover_with_odd_exception
#print axioms hole_difference_divisor
#print axioms holes_in_residue_iff
#print axioms isolated_ternary_modulus
end Erdos7NoThreeHoleSpan
