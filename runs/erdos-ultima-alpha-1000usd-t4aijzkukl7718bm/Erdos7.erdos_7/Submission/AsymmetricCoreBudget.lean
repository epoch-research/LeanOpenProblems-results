import FormalConjecturesUtil

/-! Exact scalar comparisons for two explicit partial-core formulas.
No assertion here supplies a covering system or a universal obstruction.
The formulas' arithmetic-geometric interpretation is separate from these
rational inequalities. -/
namespace Erdos7AsymmetricCoreBudget
set_option autoImplicit false

def greedyMass (t q : ℚ) : ℚ := (t*(q+1)+2*q)/4
def greedyCoeff (t q : ℚ) : ℚ := (t*(3*q+1)+2*q-2)/4

def asymmetricMass (t q : ℚ) : ℚ := (t*(7*q+5)+3*q+1)/8
def asymmetricCoeff (t q : ℚ) : ℚ := t*(11*q+1)/4

lemma greedyCoeff_pos (t q : ℚ) (ht : 0<t) (hq : 1≤q) :
    0<greedyCoeff t q := by
  have hq0 : 0<q := by linarith
  have hp : 0<t*(3*q+1) := mul_pos ht (by positivity)
  unfold greedyCoeff
  linarith

lemma greedyCoeff_lt (t q : ℚ) (ht : 0<t) (hq : 1≤q) :
    greedyCoeff t q < 3*greedyMass t q := by
  unfold greedyCoeff greedyMass
  nlinarith

/-- This scalar test cannot pass for the greedy formulas when beta<=4/3,
regardless of the two positive depth parameters. -/
theorem greedy_obstruction (t q β : ℚ) (ht : 0<t) (hq : 1≤q)
    (hb : β≤4/3) : greedyCoeff t q * β < 7*greedyMass t q-greedyCoeff t q := by
  have hc := greedyCoeff_pos t q ht hq
  have hm := greedyCoeff_lt t q ht hq
  have h := mul_le_mul_of_nonneg_left hb (le_of_lt hc)
  nlinarith

lemma asymmetricCoeff_pos (t q : ℚ) (ht : 0<t) (hq : 1≤q) :
    0<asymmetricCoeff t q := by
  have hq0 : 0<q := by linarith
  unfold asymmetricCoeff
  positivity

lemma asymmetricCoeff_lt (t q : ℚ) (ht : 0<t) (hq : 1≤q) :
    7*asymmetricCoeff t q < 22*asymmetricMass t q := by
  unfold asymmetricCoeff asymmetricMass
  nlinarith

/-- The improved scalar formula still has a strictly positive obstruction
threshold. Passing it is only a necessary screen, never existence. -/
theorem asymmetric_obstruction (t q β : ℚ) (ht : 0<t) (hq : 1≤q)
    (hb : β≤27/22) :
    asymmetricCoeff t q * β < 7*asymmetricMass t q-asymmetricCoeff t q := by
  have hc := asymmetricCoeff_pos t q ht hq
  have hm := asymmetricCoeff_lt t q ht hq
  have h := mul_le_mul_of_nonneg_left hb (le_of_lt hc)
  nlinarith

def beta73 : ℚ :=
  84099471644767165885144561230 / 66525144978773406112681495001

lemma beta73_lt_four_thirds : beta73 < 4/3 := by norm_num [beta73]

/-- A strict scalar comparison, NOT a covering-system certificate. -/
theorem asymmetric_five_three_passes :
    asymmetricMass 81 125 = 8957 ∧ asymmetricCoeff 81 125 = 27864 ∧
      7*asymmetricMass 81 125-asymmetricCoeff 81 125 <
        asymmetricCoeff 81 125*beta73 := by
  norm_num [asymmetricMass, asymmetricCoeff, beta73]

theorem greedy_fails_beta73 (t q : ℚ) (ht : 0<t) (hq : 1≤q) :
    greedyCoeff t q*beta73 < 7*greedyMass t q-greedyCoeff t q :=
  greedy_obstruction t q beta73 ht hq (le_of_lt beta73_lt_four_thirds)

#print axioms greedy_obstruction
#print axioms asymmetric_obstruction
#print axioms asymmetric_five_three_passes
#print axioms greedy_fails_beta73
end Erdos7AsymmetricCoreBudget
