import FormalConjecturesUtil
import Submission.C8CommutingDifferences
import Submission.C8SmallDifferenceCayley

/-! Twisted two-step groups do not repair the cubic-coordinate Cayley ansatz.
This is an auxiliary construction obstruction, not a solution of Erdős 713. -/
open SimpleGraph
namespace Erdos713C8TwistedCayley
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K]

/-- A central extension associated to the bilinear map x*sigma(y).
The parameter sigma is only additive, not necessarily K-linear. -/
@[ext]
structure Twist (σ : K →+ K) where
  first : K
  central : K
  deriving Fintype

instance (σ : K →+ K) : Group (Twist σ) where
  mul x y := ⟨x.first+y.first,x.central+y.central+x.first*σ y.first⟩
  one := ⟨0,0⟩
  inv x := ⟨-x.first,-x.central+x.first*σ x.first⟩
  mul_assoc x y z := by
    ext
    · exact add_assoc _ _ _
    · change (x.central+y.central+x.first*σ y.first)+z.central+
        (x.first+y.first)*σ z.first =
        x.central+(y.central+z.central+y.first*σ z.first)+x.first*σ (y.first+z.first)
      rw [map_add]
      ring
  one_mul x := by
    ext
    · change 0+x.first = x.first
      ring
    · change 0+x.central+0*σ x.first = x.central
      ring
  mul_one x := by
    ext
    · change x.first+0 = x.first
      ring
    · change x.central+0+x.first*σ 0 = x.central
      rw [map_zero]
      ring
  inv_mul_cancel x := by
    ext
    · exact neg_add_cancel _
    · change -x.central+x.first*σ x.first+x.central+(-x.first)*σ x.first = 0
      ring

variable (σ : K →+ K)

lemma commute_of_first_eq (x y : Twist σ) (he : x.first = y.first) : Commute x y := by
  change x*y = y*x
  ext
  · exact add_comm _ _
  · change x.central+y.central+x.first*σ y.first =
      y.central+x.central+y.first*σ x.first
    rw [he]
    ring

variable {W : Type*} [AddCommGroup W]

abbrev Ambient := Twist σ × Multiplicative K × Multiplicative W

def first (x : Ambient σ (W := W)) : K := x.1.first

def cubic (x : Ambient σ (W := W)) : K := Multiplicative.toAdd x.2.1

def generator (f : K → K) (g : K → W) (a : K) : Ambient σ (W := W) :=
  (⟨a,f a⟩,Multiplicative.ofAdd (a^3),Multiplicative.ofAdd (g a))

lemma first_mul (x y : Ambient σ (W := W)) : first σ (x*y) = first σ x+first σ y := rfl
lemma cubic_mul (x y : Ambient σ (W := W)) : cubic σ (x*y) = cubic σ x+cubic σ y := rfl

lemma ambient_commute (x y : Ambient σ (W := W)) (he : first σ x = first σ y) :
    Commute x y := by
  change x*y = y*x
  exact Prod.ext (commute_of_first_eq σ x.1 y.1 he).eq (mul_comm x.2 y.2)

/-- This includes arbitrary additive twists, arbitrary central generator
values, and arbitrary extra additive coordinates. Finiteness is only used
to select a field element other than zero and one. -/
theorem contains_twisted_cubic [Fintype K] [CharP K 2] (f : K → K) (g : K → W)
    (hq : 2 < Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (generator σ f g) := by
  apply Erdos713C8CommutingDifferences.contains_commuting_fibers_finite
    (first σ) (cubic σ) rfl rfl (first_mul σ) (cubic_mul σ)
    (generator σ f g) (fun _ => rfl) (fun _ => rfl) (ambient_commute σ) hq

def arbitraryGenerator (f h : K → K) (g : K → W) (a : K) : Ambient σ (W := W) :=
  (⟨a,f a⟩,Multiplicative.ofAdd (h a),Multiplicative.ofAdd (g a))

/-- At a larger absolute field threshold, the cubic coordinate assumption
can be removed entirely. All generator functions may depend on the field. -/
theorem contains_twisted_arbitrary [Fintype K] [CharP K 2] (f h : K → K) (g : K → W)
    (hq : 253125 < Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (arbitraryGenerator σ f h g) := by
  apply Erdos713C8SmallDifferenceCayley.contains_commuting_section (first σ) rfl
    (first_mul σ) (arbitraryGenerator σ f h g) (fun _ => rfl) (ambient_commute σ) hq

#print axioms commute_of_first_eq
#print axioms contains_twisted_cubic
#print axioms contains_twisted_arbitrary
end Erdos713C8TwistedCayley
