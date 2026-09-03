import Submission.CoreUnionOvercount
import Submission.SquarefreeBoxRealization

/-! A genuine odd, squarefree, divisor-closed, irredundant partial congruence
family for which the raw sum of minimal-core probabilities exceeds one.
The integer -3 is uncovered. This refutes one proposed counting bound, NOT
Erdos7.erdos_7. -/
namespace Erdos7CoreOvercountArithmetic
open scoped BigOperators
open Erdos7ManyBooleanCores Erdos7CoreUnionOvercount
open Erdos7SquarefreeBoxRealization
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 2000
attribute [local irreducible] allCores

abbrev FullIndex := Erdos7UniformSupportCompletion.Index (I := Coord) (J := Clause) 8

def fullSupport : FullIndex → Finset Coord :=
  Erdos7UniformSupportCompletion.support 8 Erdos7ManyBooleanCores.support

def moduli (k : FullIndex) : ℕ := modulus prime (fullSupport k)

def localResidue (k : FullIndex) (i : Coord) : ℤ :=
  Erdos7UniformSupportCompletion.residue 8 bit k i

lemma odd_primes : ∀ i : Coord, Odd (prime i) := by decide +kernel

/-- The arithmetic family is finite, has no repeated moduli, contains every
nontrivial divisor of each modulus, and every class has a private integer. -/
theorem exists_structured_family : ∃ a : FullIndex → ℤ,
    Function.Injective moduli ∧
    (∀ k, 1 < moduli k ∧ Odd (moduli k) ∧ Squarefree (moduli k)) ∧
    (∀ k d, 1 < d → d ∣ moduli k → ∃ l, moduli l=d) ∧
    (∀ k i, (prime i : ℤ) ∣ a k-localResidue k i) ∧
    (∀ k, ∃ z : ℤ, ∀ l, ((moduli l : ℤ) ∣ z-a l) ↔ l=k) ∧
    ∀ k, ¬ (moduli k : ℤ) ∣ -3-a k := by
  have hh := exists_completed_arithmetic_family 8 (by decide)
    Erdos7ManyBooleanCores.support support_card support_injective bit prime
    (fun i => (prime_properties.2 i).1) prime_properties.1 odd_primes
    (fun i => (prime_properties.2 i).2)
  obtain ⟨hinj,hmod,hdiv,a,ha,hpriv,hmiss⟩ := hh
  exact ⟨a,hinj,hmod,hdiv,ha,hpriv,hmiss⟩

lemma encode_divisibility (i : Coord) (x : Branch i) (v : Fin 2) :
    (prime i : ℤ) ∣ ((x.val : ℤ)+1)-((v.val : ℤ)-2) ↔ x = encode i v := by
  have hp := (prime_properties.2 i).2
  have hv := v.isLt
  have he : ((encode i v).val : ℤ)+1-((v.val : ℤ)-2) = prime i := by
    simp only [encode]
    omega
  constructor
  · intro h
    have hd : (prime i : ℤ) ∣ (x.val : ℤ)-(encode i v).val := by
      have hh := dvd_sub h (show (prime i : ℤ) ∣ ((encode i v).val : ℤ)+1-((v.val : ℤ)-2) by rw [he])
      convert hh using 1 <;> ring
    have hx := x.isLt
    have hev := (encode i v).isLt
    have hh := eq_of_bounded_congruent (prime i) (prime i-3) (by omega)
      ((x.val : ℤ)-3) (((encode i v).val : ℤ)-3)
      (by constructor <;> omega) (by constructor <;> omega)
      (by convert hd using 1 <;> ring)
    exact Fin.ext (by omega)
  · intro h
    subst x
    rw [he]

/-- Membership of the squarefree class at a chosen prime-coordinate tuple. -/
def ArithmeticMatches (a : FullIndex → ℤ) (k : Clause) (x : (i : Coord) → Branch i) : Prop :=
  ∀ i ∈ Erdos7ManyBooleanCores.support k,
    (prime i : ℤ) ∣ ((x i).val : ℤ)+1-a (.inl k)

lemma arithmetic_match_iff (a : FullIndex → ℤ)
    (ha : ∀ k i, (prime i : ℤ) ∣ a k-localResidue k i)
    (k : Clause) (x : (i : Coord) → Branch i) :
    ArithmeticMatches a k x ↔ ∀ i ∈ Erdos7ManyBooleanCores.support k,
      x i = encode i (bit k i) := by
  unfold ArithmeticMatches
  apply forall_congr'
  intro i
  apply forall_congr'
  intro _hi
  rw [← encode_divisibility]
  have hr := ha (.inl k) i
  change (prime i : ℤ) ∣ a (.inl k)-((bit k i).val-2) at hr
  constructor
  · intro h
    convert dvd_add h hr using 1 <;> ring
  · intro h
    convert dvd_sub h hr using 1 <;> ring

/-- Coverage and private points within the chosen product, expressed using
actual integer residues of the completed family. -/
def ArithmeticMinimalEvent (a : FullIndex → ℤ) (s : Finset Clause) (z : Sample) : Prop :=
  (∀ x : (i : Coord) → Branch i, (∀ i, x i ∈ (z i).val) →
    ∃ k ∈ s, ArithmeticMatches a k x) ∧
  ∀ k ∈ s, ∃ x : (i : Coord) → Branch i,
    (∀ i, x i ∈ (z i).val) ∧ ∀ l ∈ s, ArithmeticMatches a l x ↔ l=k

lemma arithmetic_event_iff (a : FullIndex → ℤ)
    (ha : ∀ k i, (prime i : ℤ) ∣ a k-localResidue k i)
    (s : Finset Clause) (z : Sample) :
    ArithmeticMinimalEvent a s z ↔ MinimalCoreEvent s z := by
  unfold ArithmeticMinimalEvent MinimalCoreEvent CoreEvent
  simp_rw [arithmetic_match_iff a ha]

noncomputable def arithmeticCoreProbability (a : FullIndex → ℤ) (s : Finset Clause) : ℚ := by
  classical
  exact ((Finset.univ.filter (ArithmeticMinimalEvent a s)).card : ℚ)/Fintype.card Sample

lemma arithmetic_probability_eq (a : FullIndex → ℤ)
    (ha : ∀ k i, (prime i : ℤ) ∣ a k-localResidue k i) (s : Finset Clause) :
    arithmeticCoreProbability a s = coreProbability s := by
  classical
  have he : ArithmeticMinimalEvent a s = MinimalCoreEvent s := by
    funext z
    exact propext (arithmetic_event_iff a ha s z)
  unfold arithmeticCoreProbability coreProbability
  rw [he]

/-- The overcount persists in an actual odd congruence family with all the
usual divisor-closure and irredundance properties. Even MINIMAL core events
are too correlated for their raw union bound to be universally below one. -/
theorem exists_arithmetic_overcount : ∃ a : FullIndex → ℤ,
    Function.Injective moduli ∧
    (∀ k, 1 < moduli k ∧ Odd (moduli k) ∧ Squarefree (moduli k)) ∧
    (∀ k d, 1 < d → d ∣ moduli k → ∃ l, moduli l=d) ∧
    (∀ k, ∃ z : ℤ, ∀ l, ((moduli l : ℤ) ∣ z-a l) ↔ l=k) ∧
    (∀ k, ¬ (moduli k : ℤ) ∣ -3-a k) ∧
    1 < ∑ s ∈ allCores, arithmeticCoreProbability a s := by
  obtain ⟨a,hinj,hmod,hdiv,ha,hpriv,hmiss⟩ := exists_structured_family
  refine ⟨a,hinj,hmod,hdiv,hpriv,hmiss,?_⟩
  have he : (∑ s ∈ allCores, arithmeticCoreProbability a s) =
      ∑ s ∈ allCores, coreProbability s := by
    apply Finset.sum_congr rfl
    exact fun s _ => arithmetic_probability_eq a ha s
  rw [he]
  exact sum_core_probabilities_gt_one

#print axioms exists_structured_family
#print axioms arithmetic_event_iff
#print axioms exists_arithmetic_overcount
end Erdos7CoreOvercountArithmetic
