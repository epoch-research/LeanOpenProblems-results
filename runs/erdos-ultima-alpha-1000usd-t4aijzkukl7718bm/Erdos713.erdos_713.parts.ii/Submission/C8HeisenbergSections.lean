import FormalConjecturesUtil
import Submission.C8ParallelDirections
import Submission.C8SmallDifferenceCayley

/-! Full section Cayley graphs in Heisenberg-type central extensions have C8,
even with arbitrary extra additive coordinates. This is auxiliary progress
and does not settle the rational extremal-exponent conjecture. -/
open SimpleGraph
namespace Erdos713C8HeisenbergSections
open Erdos713C8CommutingDifferences
variable {G K : Type*} [Group G] [Field K]
set_option maxHeartbeats 2000000

/-- Parallel noncentral coordinate vectors commute. No restriction is placed
on the second generator coordinate or on additional group coordinates. -/
theorem contains_parallel_section [Fintype K]
    (φ ψ : G → K) (hφ1 : φ 1 = 0) (hψ1 : ψ 1 = 0)
    (hφmul : ∀ x y, φ (x*y) = φ x+φ y)
    (hψmul : ∀ x y, ψ (x*y) = ψ x+ψ y)
    (g : K → G) (hφg : ∀ a, φ (g a) = a)
    (hcomm : ∀ x y, φ x*ψ y = φ y*ψ x → Commute x y)
    (hq : 1428050000 < Fintype.card K) : cycleGraph 8 ⊑ graph g := by
  classical
  by_contra hf
  have hg : Function.Injective g := by
    intro a b h
    simpa only [hφg] using congrArg φ h
  let τ : K → K → K := fun m a => ψ (g a)-m*a
  have hc : Erdos713C8ParallelDirections.ParallelCommute τ g := by
    intro m a b c d hab hcd
    apply hcomm
    simp only [hφmul,hψmul,coord_inv φ hφ1 hφmul,coord_inv ψ hψ1 hψmul,hφg]
    dsimp [τ] at hab hcd
    linear_combination (a-b)*hcd-(c-d)*hab
  have hcover : ∀ a b, ∃ m, τ m a = τ m b := by
    intro a b
    by_cases hab : a = b
    · exact ⟨0,hab ▸ rfl⟩
    let m := (ψ (g a)-ψ (g b))/(a-b)
    have hm : m*(a-b) = ψ (g a)-ψ (g b) := div_mul_cancel₀ _ (sub_ne_zero.mpr hab)
    refine ⟨m,?_⟩
    dsimp [τ]
    linear_combination -hm
  have hD := Erdos713C8ParallelDirections.differences_card τ g hg hf hc hcover
  have hb := Erdos713C8SmallDifferenceCayley.card_bound_of_difference_ratio g hg hf 25 hD
  norm_num at hb
  omega

/-- Standard three-coordinate Heisenberg group over a field. -/
@[ext]
structure Heisenberg (K : Type*) where
  first : K
  second : K
  central : K
  deriving Fintype

instance : Group (Heisenberg K) where
  mul x y := ⟨x.first+y.first,x.second+y.second,x.central+y.central+x.first*y.second⟩
  one := ⟨0,0,0⟩
  inv x := ⟨-x.first,-x.second,-x.central+x.first*x.second⟩
  mul_assoc x y z := by
    ext
    · exact add_assoc _ _ _
    · exact add_assoc _ _ _
    · change (x.central+y.central+x.first*y.second)+z.central+
        (x.first+y.first)*z.second =
        x.central+(y.central+z.central+y.first*z.second)+x.first*(y.second+z.second)
      ring
  one_mul x := by
    ext
    · exact zero_add _
    · exact zero_add _
    · change 0+x.central+0*x.second = x.central
      ring
  mul_one x := by
    ext
    · exact add_zero _
    · exact add_zero _
    · change x.central+0+x.first*0 = x.central
      ring
  inv_mul_cancel x := by
    ext
    · exact neg_add_cancel _
    · exact neg_add_cancel _
    · change -x.central+x.first*x.second+x.central+(-x.first)*x.second = 0
      ring

lemma heisenberg_commute (x y : Heisenberg K)
    (he : x.first*y.second = y.first*x.second) : Commute x y := by
  change x*y = y*x
  ext
  · exact add_comm _ _
  · exact add_comm _ _
  · change x.central+y.central+x.first*y.second =
      y.central+x.central+y.first*x.second
    linear_combination he

variable {W : Type*} [AddCommGroup W]

abbrev Ambient (K W : Type*) := Heisenberg K × Multiplicative W

def first (x : Ambient K W) : K := x.1.first

def second (x : Ambient K W) : K := x.1.second

def generator (f c : K → K) (g : K → W) (a : K) : Ambient K W :=
  (⟨a,f a,c a⟩,Multiplicative.ofAdd (g a))

lemma first_mul (x y : Ambient K W) : first (x*y) = first x+first y := rfl
lemma second_mul (x y : Ambient K W) : second (x*y) = second x+second y := rfl

lemma ambient_commute (x y : Ambient K W)
    (he : first x*second y = first y*second x) : Commute x y := by
  change x*y = y*x
  exact Prod.ext (heisenberg_commute x.1 y.1 he).eq (mul_comm x.2 y.2)

/-- All finite-field characteristics and all generator functions are covered.
The extra additive group can have any dimension, or can even be infinite. -/
theorem contains_arbitrary_heisenberg [Fintype K] (f c : K → K) (g : K → W)
    (hq : 1428050000 < Fintype.card K) :
    cycleGraph 8 ⊑ graph (generator f c g) := by
  apply contains_parallel_section first second rfl rfl first_mul second_mul
    (generator f c g) (fun _ => rfl) ambient_commute hq

#print axioms contains_parallel_section
#print axioms heisenberg_commute
#print axioms contains_arbitrary_heisenberg
end Erdos713C8HeisenbergSections
