import Submission.PrimeOrbitArithmetic
import Submission.ForestUnion

/-! A forest-corrected prime-orbit moment bound. The period-one events are
charged by a forest union bound, rather than their uncorrected sum. This is
a necessary condition for coverage, not a universal noncoverage theorem. -/
namespace Erdos7PrimeOrbitForest
open scoped BigOperators
open Erdos7UnitOrbitDescent Erdos7UnitOrbitPhaseDescent Erdos7PrimeOrbitMoment
open Erdos7ForestUnion Erdos7UnitOrbitArithmetic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

variable {G I : Type} [Group G] [Fintype G] [Fintype I]
variable (H : I → Type) [∀ i, Group (H i)]
variable (π : (i : I) → G →* H i) (a : (i : I) → H i)

def UnitEvent (u : G) (i : I) (v : G) : Prop :=
  Active H π a u v i ∧ orderOf (π i u) = 1

lemma bit_sum_card {Ω : Type} [Fintype Ω] (P : Ω → Prop) :
    (∑ x : Ω, bit (P x)) = ((Finset.univ.filter P).card:ℚ) := by
  unfold bit
  exact Finset.sum_boole _ _

/-- The actual union of unit-period events, rather than its union bound,
is enough in the prime-orbit second-moment inequality. -/
lemma pointwise_union_moment {p : ℕ} (hp : p.Prime)
    (hc : ∀ x : G, ∃ i, π i x = a i) (u v : G) (hu : orderOf u = p) :
    (p*(p-1):ℕ) ≤ ((p*(p-1):ℕ):ℚ)*bit (∃ i, UnitEvent H π a u i v) +
      ∑ ij : I × I, bit (Conflict H π a u v ij.1 ij.2) := by
  have hnonneg : (0:ℚ) ≤ ∑ ij : I × I, bit (Conflict H π a u v ij.1 ij.2) :=
    Finset.sum_nonneg (fun ij _ => (bit_bounds _).1)
  by_cases hunit : ∃ i, UnitEvent H π a u i v
  · rw [show bit (∃ i, UnitEvent H π a u i v) = 1 by simp [bit,hunit],mul_one]
    exact le_add_of_nonneg_right hnonneg
  · have hn : ∀ i, Active H π a u v i → orderOf (π i u) ≠ 1 := by
      intro i hi hoi
      exact hunit ⟨i,hi,hoi⟩
    have hh := prime_orbit_conflicts H π a hp hc u v hu hn
    rw [bit_sum_card]
    simp only [bit,if_neg hunit,mul_zero,zero_add]
    exact_mod_cast hh

/-- A nonnegative-weight version, allowing later conditioning or distortion.
The forest is on unit-period events; every parent edge must decrease rank. -/
theorem weighted_forest_moment {p : ℕ} (hp : p.Prime)
    (hc : ∀ x : G, ∃ i, π i x = a i) (u : G) (hu : orderOf u = p)
    (μ : G → ℚ) (hμ : ∀ v, 0 ≤ μ v)
    (parent : I → Option I) (rank : I → ℕ)
    (hparent : ∀ i j, parent i = some j → rank j < rank i) :
    ((p*(p-1):ℕ):ℚ)*(∑ v,μ v) ≤
      ((p*(p-1):ℕ):ℚ)*((∑ i, mass μ (UnitEvent H π a u i)) -
        ∑ i, (parent i).elim 0 (fun j => mass μ (fun v =>
          UnitEvent H π a u i v ∧ UnitEvent H π a u j v))) +
      ∑ ij : I × I, mass μ (fun v => Conflict H π a u v ij.1 ij.2) := by
  have hpoint := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset G)) =>
    mul_le_mul_of_nonneg_left (pointwise_union_moment H π a hp hc u v hu) (hμ v))
  have he1 : (∑ v, μ v * ((p*(p-1):ℕ):ℚ)) = ((p*(p-1):ℕ):ℚ)*(∑ v,μ v) := by
    rw [← Finset.sum_mul,mul_comm]
  have he2 : (∑ v, μ v * (((p*(p-1):ℕ):ℚ)*bit (∃ i, UnitEvent H π a u i v))) =
      ((p*(p-1):ℕ):ℚ)*mass μ (fun v => ∃ i, UnitEvent H π a u i v) := by
    simp only [mass,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _; ring
  have he3 : (∑ v, μ v * ∑ ij : I × I, bit (Conflict H π a u v ij.1 ij.2)) =
      ∑ ij : I × I, mass μ (fun v => Conflict H π a u v ij.1 ij.2) := by
    simp only [Finset.mul_sum,mass]
    exact Finset.sum_comm
  simp only [mul_add,Finset.sum_add_distrib] at hpoint
  rw [he1,he2,he3] at hpoint
  have hforest := weighted_forest_union_bound μ hμ (UnitEvent H π a u) parent rank hparent
  have hmul := mul_le_mul_of_nonneg_left hforest (Nat.cast_nonneg (p*(p-1)) : (0:ℚ) ≤ _)
  linarith

lemma mass_one_card {Ω : Type} [Fintype Ω] (P : Ω → Prop) :
    mass (fun _ : Ω => 1) P = ((Finset.univ.filter P).card:ℚ) := by
  simp only [mass,one_mul]
  exact bit_sum_card P

/-- A finite cardinality form of the forest correction. -/
theorem forest_moment {p : ℕ} (hp : p.Prime)
    (hc : ∀ x : G, ∃ i, π i x = a i) (u : G) (hu : orderOf u = p)
    (parent : I → Option I) (rank : I → ℕ)
    (hparent : ∀ i j, parent i = some j → rank j < rank i) :
    ((p*(p-1):ℕ):ℚ)*Fintype.card G ≤
      ((p*(p-1):ℕ):ℚ)*((∑ i, ((Finset.univ.filter (UnitEvent H π a u i)).card:ℚ)) -
        ∑ i, (parent i).elim 0 (fun j =>
          ((Finset.univ.filter (fun v => UnitEvent H π a u i v ∧ UnitEvent H π a u j v)).card:ℚ))) +
      ∑ ij : I × I, ((Finset.univ.filter (fun v => Conflict H π a u v ij.1 ij.2)).card:ℚ) := by
  have hh := weighted_forest_moment H π a hp hc u hu (fun _ => 1) (fun _ => by norm_num) parent rank hparent
  simp only [mass_one_card,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hh
  convert hh using 1
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases h : parent i with
  | none => simp only [h,Option.elim_none]
  | some j =>
    simp only [h,Option.elim_some]
    apply congrArg (fun s : Finset G => (s.card:ℚ))
    ext v
    simp only [Finset.mem_filter]

end
end Erdos7PrimeOrbitForest

namespace Erdos7PrimeOrbitForest
open scoped BigOperators
open Erdos7UnitOrbitArithmetic Erdos7PrimeOrbitMoment
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable
variable {I : Type} [Fintype I]

def arithmeticBudget (N : ℕ) [NeZero N] (m : I → ℕ) (a : I → ℤ)
    (hd : ∀ i, m i ∣ N) (u : (ZMod N)ˣ) (p : ℕ)
    (parent : UnitIndex m a → Option (UnitIndex m a)) : ℚ :=
  let J := UnitIndex m a
  let H (i : J) := (ZMod (m i.val))ˣ
  let π (i : J) := unitMap N m hd i.val
  ((p*(p-1):ℕ):ℚ)*((∑ i : J,
    ((Finset.univ.filter (UnitEvent H π (unitResidue m a) u i)).card:ℚ)) -
    ∑ i : J, (parent i).elim 0 (fun j => ((Finset.univ.filter (fun v =>
      UnitEvent H π (unitResidue m a) u i v ∧ UnitEvent H π (unitResidue m a) u j v)).card:ℚ))) +
    ∑ ij : J × J, ((Finset.univ.filter (fun v =>
      Conflict H π (unitResidue m a) u v ij.1 ij.2)).card:ℚ)

/-- Arithmetic specialization, requiring neither strictness nor minimality. -/
theorem arithmetic_forest_moment {p : ℕ} (hp : p.Prime)
    (N : ℕ) [NeZero N] (m : I → ℕ) (a : I → ℤ) (hd : ∀ i, m i ∣ N)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i)
    (u : (ZMod N)ˣ) (hu : orderOf u = p)
    (parent : UnitIndex m a → Option (UnitIndex m a)) (rank : UnitIndex m a → ℕ)
    (hparent : ∀ i j, parent i = some j → rank j < rank i) :
    ((p*(p-1):ℕ):ℚ)*N.totient ≤ arithmeticBudget N m a hd u p parent := by
  have hh := forest_moment (fun i : UnitIndex m a => (ZMod (m i.val))ˣ)
    (fun i => unitMap N m hd i.val) (unitResidue m a)
    hp (unit_cover N m a hd hc) u hu parent rank hparent
  simpa only [ZMod.card_units_eq_totient,arithmeticBudget] using hh

/-- Any strict finite upper certificate of the corrected budget produces
an integer missed by the original classes. No universal certificate is supplied. -/
theorem exists_uncovered_of_forest_lt {p : ℕ} (hp : p.Prime)
    (N : ℕ) [NeZero N] (m : I → ℕ) (a : I → ℤ) (hd : ∀ i, m i ∣ N)
    (u : (ZMod N)ˣ) (hu : orderOf u = p)
    (parent : UnitIndex m a → Option (UnitIndex m a)) (rank : UnitIndex m a → ℕ)
    (hparent : ∀ i j, parent i = some j → rank j < rank i)
    (hb : arithmeticBudget N m a hd u p parent < ((p*(p-1):ℕ):ℚ)*N.totient) :
    ∃ x : ℤ, ∀ i, ¬ (m i : ℤ) ∣ x-a i := by
  by_contra! hc
  exact (not_lt_of_ge (arithmetic_forest_moment hp N m a hd hc u hu parent rank hparent)) hb

#print axioms weighted_forest_moment
#print axioms arithmetic_forest_moment
#print axioms exists_uncovered_of_forest_lt
end
end Erdos7PrimeOrbitForest
