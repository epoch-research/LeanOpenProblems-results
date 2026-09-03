import FormalConjecturesUtil

/-!
A finite obstruction to inferring comparison balance from invariance under
multiplication by 2 and 3 alone. This is not a counterexample to Erdős 371.
-/

namespace Erdos371.MultiplierInvariantModel

def strip (p n : ℕ) : ℕ := n / p ^ Nat.maxPowDiv p n

def core (n : ℕ) : ℕ := strip 3 (strip 2 n)

lemma strip_eq_ordCompl (p n : ℕ) (hp : p.Prime) : strip p n = ordCompl[p] n := by
  rw [Nat.factorization_def n hp, padicValNat.padicValNat_eq_maxPowDiv]
  rfl

lemma core_eq (n : ℕ) : core n = ordCompl[3] (ordCompl[2] n) := by
  rw [core, strip_eq_ordCompl 3 _ Nat.prime_three, strip_eq_ordCompl 2 _ Nat.prime_two]

/-- A dyadic mantissa of a high power. The exponent is motivated by the
approximation 53 log₂(3) ≈ 84; the verified finite counts use only exact
integer arithmetic, not that approximation. -/
def label (n : ℕ) : ℕ :=
  let a := core n ^ 53
  (2 ^ 20 * a) / 2 ^ (Nat.log 2 a)

lemma core_mul (a b : ℕ) : core (a * b) = core a * core b := by
  simp only [core_eq, Nat.ordCompl_mul]

lemma core_one : core 1 = 1 := by decide +kernel

lemma core_two : core 2 = 1 := by decide +kernel
lemma core_three : core 3 = 1 := by decide +kernel

lemma label_mul_two (n : ℕ) : label (2 * n) = label n := by
  simp only [label, core_mul, core_two, one_mul]

lemma label_mul_three (n : ℕ) : label (3 * n) = label n := by
  simp only [label, core_mul, core_three, one_mul]

lemma label_mul_smooth (i j n : ℕ) : label (2 ^ i * 3 ^ j * n) = label n := by
  have hpow (a k : ℕ) : core (a ^ k) = core a ^ k := by
    induction k with
    | zero => simp [core_one]
    | succ k ih => rw [pow_succ, core_mul, ih, pow_succ]
  simp only [label, core_mul, hpow, core_two, core_three, one_pow, one_mul]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma rise_count :
    ((Finset.range 1000).filter fun n => label (n + 1) < label (n + 2)).card = 769 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tie_count :
    ((Finset.range 1000).filter fun n => label (n + 1) = label (n + 2)).card = 4 := by
  decide +kernel

/-- This model lacks the max-under-multiplication property of maxPrimeFac. -/
lemma not_max_multiplicative : label (5 * 7) ≠ max (label 5) (label 7) := by
  decide +kernel

#print axioms not_max_multiplicative
#print axioms label_mul_smooth
#print axioms rise_count
#print axioms tie_count
end Erdos371.MultiplierInvariantModel
