import Submission.RemovePrimeLogWeight

/-! Natural prime-counting asymptotics in every fixed residue class. The
modulus is fixed before the initial-interval endpoint tends to infinity. -/
namespace Erdos371.AbelPrimes
open Finset Filter ArithmeticFunction ArithmeticFunction.vonMangoldt
open scoped Topology
set_option autoImplicit false

noncomputable def primeResidueIndicator {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  if n.Prime ∧ (n : ZMod q) = a then 1 else 0

lemma primeResidueIndicator_bounds {q : ℕ} (a : ZMod q) (n : ℕ) :
    0 ≤ primeResidueIndicator a n ∧ primeResidueIndicator a n ≤ 1 := by
  unfold primeResidueIndicator
  split_ifs <;> norm_num

lemma primeResidueIndicator_log {q : ℕ} (a : ZMod q) (n : ℕ) :
    primeResidueIndicator a n*Real.log n = primeResidueCoeff a n := by
  classical
  by_cases hp : n.Prime
  · by_cases he : (n : ZMod q) = a <;>
      simp [primeResidueIndicator,primeResidueCoeff,hp,he,residueClass,
        vonMangoldt_apply_prime hp]
  · simp [primeResidueIndicator,primeResidueCoeff,hp]

noncomputable def residuePrimeCount {q : ℕ} (a : ZMod q) (N : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun n : ℕ => n.Prime ∧ (n : ZMod q) = a)).card

lemma plainSum_primeResidueIndicator {q : ℕ} (a : ZMod q) (N : ℕ) :
    plainSum (primeResidueIndicator a) N = (residuePrimeCount a N : ℝ) := by
  classical
  simp [plainSum,primeResidueIndicator,residuePrimeCount]

/-- Prime number theorem for one fixed arithmetic progression, including the
zero-density nonunit residue classes. -/
theorem prime_number_theorem_AP (q : ℕ) [NeZero q] (a : ZMod q) :
    Tendsto (fun N : ℕ => (residuePrimeCount a N : ℝ)*Real.log N/(N : ℝ)) atTop
      (𝓝 (if IsUnit a then (q.totient : ℝ)⁻¹ else 0)) := by
  apply (remove_log_weight (primeResidueIndicator a) (primeResidueIndicator_bounds a) _ ?_).congr'
  · exact Eventually.of_forall (fun N => by simp only [plainSum_primeResidueIndicator])
  · simpa only [logWeightedSum,primeResidueIndicator_log] using prime_residue_natural_limit q a

noncomputable def initialPrimes (N : ℕ) : Finset ℕ := (Icc 1 N).filter Nat.Prime

lemma initialPrimes_eq_primesBelow (N : ℕ) : initialPrimes N = (N+1).primesBelow := by
  ext p
  simp only [initialPrimes,mem_filter,mem_Icc,Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨_,hpN⟩,hp⟩
    exact ⟨by omega,hp⟩
  · rintro ⟨hpN,hp⟩
    exact ⟨⟨hp.pos,by omega⟩,hp⟩

lemma residuePrimeCount_mod_one (N : ℕ) : residuePrimeCount (0 : ZMod 1) N = (initialPrimes N).card := by
  unfold residuePrimeCount initialPrimes
  congr 1
  ext n
  simp only [mem_filter]
  have he : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  simp only [he,and_true]

/-- The total prime-counting asymptotic, obtained from the modulus-one case. -/
theorem prime_number_theorem_initial :
    Tendsto (fun N : ℕ => ((initialPrimes N).card : ℝ)*Real.log N/(N : ℝ)) atTop (𝓝 1) := by
  have hu : IsUnit (0 : ZMod 1) := by
    rw [show (0 : ZMod 1) = 1 from Subsingleton.elim _ _]
    exact isUnit_one
  simpa only [residuePrimeCount_mod_one,if_pos hu,Nat.totient_one,Nat.cast_one,inv_one] using
    prime_number_theorem_AP 1 0

#print axioms prime_number_theorem_AP
#print axioms prime_number_theorem_initial
end Erdos371.AbelPrimes
