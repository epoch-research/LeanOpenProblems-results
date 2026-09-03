import Submission.SoftEndpointDerivative
import Submission.RoundedSieve

/-! Full inclusion-exclusion gives a cardinality-only discrepancy bound.
This exponential bound does not imply the quadratic Jacobsthal conjecture. -/
namespace Erdos970.GapAverages
open Finset Real BlockSieve BlockSieve.SievePolynomial

noncomputable def fullPolynomial (P : Finset ℕ) : SievePolynomial where
  Term := ↥P.powerset
  fintypeTerm := inferInstance
  primes := Subtype.val
  coefficient := fun Q => (-1 : ℝ)^Q.val.card

lemma fullPolynomial_supported (P : Finset ℕ) : (fullPolynomial P).SupportedOn P := by
  intro Q
  exact mem_powerset.mp Q.property

lemma fullPolynomial_value (P : Finset ℕ) (r : ℕ → ℕ) (i : ℕ) :
    (fullPolynomial P).value r i =
      ∏ p ∈ P, (1-if i ≡ r p [MOD p] then (1 : ℝ) else 0) := by
  classical
  have he := prod_sub (fun _ : ℕ => (1 : ℝ))
    (fun p => if i ≡ r p [MOD p] then (1 : ℝ) else 0) P
  simp only [prod_const_one, mul_one, prod_boole] at he
  rw [he]
  exact sum_coe_sort P.powerset (fun Q : Finset ℕ =>
    (-1 : ℝ)^Q.card * if ∀ p ∈ Q, i ≡ r p [MOD p] then (1 : ℝ) else 0)

lemma fullPolynomial_mean (P : Finset ℕ) : (fullPolynomial P).mean = density P := by
  classical
  have he := prod_sub (fun _ : ℕ => (1 : ℝ)) (fun p => 1/(p : ℝ)) P
  simp only [prod_const_one, mul_one] at he
  unfold density
  rw [he]
  change (∑ Q : ↥P.powerset, (-1 : ℝ)^Q.val.card/(∏ p ∈ Q.val, (p : ℝ))) = _
  rw [sum_coe_sort P.powerset (fun Q : Finset ℕ =>
    (-1 : ℝ)^Q.card/(∏ p ∈ Q, (p : ℝ)))]
  apply sum_congr rfl
  intro Q hQ
  simp only [div_eq_mul_inv, one_mul, prod_inv_distrib]

lemma fullPolynomial_cost (P : Finset ℕ) : (fullPolynomial P).cost = (2 : ℝ)^P.card := by
  change (∑ Q : ↥P.powerset, |(-1 : ℝ)^Q.val.card|) = _
  simp

/-- Extend a normalized phase to a total natural residue function. -/
def fullPhaseResidues (P : Finset ℕ) (r : Phase P) (p : ℕ) : ℕ :=
  if hp : p ∈ P then (r ⟨p, hp⟩).val else 0

lemma fullPolynomial_value_phase (P : Finset ℕ) (r : Phase P) (i : ℕ) :
    (fullPolynomial P).value (fullPhaseResidues P r) i = point P i r := by
  classical
  rw [fullPolynomial_value, point]
  rw [← prod_attach P (fun p =>
    (1-if i ≡ fullPhaseResidues P r p [MOD p] then (1 : ℝ) else 0))]
  apply prod_congr rfl
  intro p hp
  simp [fullPhaseResidues, p.property, Nat.ModEq,
    Nat.mod_eq_of_lt (r p).isLt]

/-- Uniform over every interval length and every actual phase. The cost is
exponential in cardinality, not quadratic. -/
theorem intervalCount_full_discrepancy (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (r : Phase P) :
    |intervalCount P m r - (m : ℝ)*density P| ≤ (2 : ℝ)^P.card := by
  have hh := (fullPolynomial P).interval_error
    (fun Q p hp => hP p ((fullPolynomial_supported P) Q hp))
    (fullPhaseResidues P r) m
  simpa only [fullPolynomial_value_phase, fullPolynomial_mean,
    fullPolynomial_cost, intervalCount] using hh

/-- A consequence for the range of the actual count over phases. -/
theorem intervalCount_phase_difference (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (r s : Phase P) :
    |intervalCount P m r - intervalCount P m s| ≤ (2 : ℝ)^(P.card+1) := by
  obtain ⟨hrl, hru⟩ := abs_le.mp (intervalCount_full_discrepancy P hP m r)
  obtain ⟨hsl, hsu⟩ := abs_le.mp (intervalCount_full_discrepancy P hP m s)
  rw [pow_succ]
  apply abs_le.mpr
  constructor <;> linarith

#print axioms intervalCount_full_discrepancy
#print axioms intervalCount_phase_difference
end Erdos970.GapAverages
