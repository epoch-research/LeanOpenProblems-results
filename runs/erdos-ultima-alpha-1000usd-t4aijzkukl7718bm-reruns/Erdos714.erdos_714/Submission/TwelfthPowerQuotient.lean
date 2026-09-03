import Submission.SkewPowerFinite

/-! The degree-twelve quotient and its two-sheet refinement are uniformly
not K4,4-free in odd characteristic. No result on arbitrary edge thinnings
or the original extremal-number conjecture is claimed. -/
noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714SkewPowerGrid

def weightSize (q : ℕ) : ℕ := (q^3-1)*(q+1)
def torusExponent (q : ℕ) : ℕ := (q^2+1)*(q^2-q+1)*(q^4-q^2+1)

lemma exponent_factorization (q : ℕ) (hq : 1 ≤ q) :
    q^12-1=torusExponent q*weightSize q := by
  have he : q^12=torusExponent q*weightSize q+1 := by
    cases q with
    | zero => omega
    | succ k =>
      have h₂ : (k+1)^2-(k+1)+1=k^2+k+1 := by
        have h : (k+1)^2=k^2+k+(k+1) := by ring
        omega
      have h₄ : (k+1)^4-(k+1)^2+1=k^4+4*k^3+5*k^2+2*k+1 := by
        have h : (k+1)^4=k^4+4*k^3+5*k^2+2*k+(k+1)^2 := by ring
        omega
      have h₃ : (k+1)^3-1=k^3+3*k^2+3*k := by
        have h : (k+1)^3=k^3+3*k^2+3*k+1 := by ring
        omega
      simp only [torusExponent,weightSize,h₂,h₄,h₃]
      ring
  omega

lemma exponent_pos (q : ℕ) : 0<torusExponent q := by
  unfold torusExponent
  positivity

lemma exponent_even (q : ℕ) (hq : Odd q) : Even (torusExponent q) := by
  have he : Even (q^2+1) := (hq.pow (n := 2)).add_odd (by decide : Odd 1)
  exact (he.mul_right _).mul_right _

lemma half_exponent_factorization (q : ℕ) (hq : Odd q) :
    q^12-1=(torusExponent q/2)*modulus q := by
  rw [exponent_factorization q hq.pos]
  have he : torusExponent q/2*2=torusExponent q :=
    Nat.div_mul_cancel (even_iff_two_dvd.mp (exponent_even q hq))
  rw [modulus]
  change torusExponent q*((q^3-1)*(q+1)) = _
  calc
    _ = (torusExponent q/2*2)*((q^3-1)*(q+1)) := by rw [he]
    _ = _ := by ring

lemma two_ne_zero_of_odd_card {E : Type*} [Field E] [Fintype E]
    (hq : Odd (Fintype.card E)) : (2 : E) ≠ 0 := by
  apply Ring.two_ne_zero
  intro h
  have he := FiniteField.even_card_of_char_two h
  have ho := Nat.odd_iff.mp hq
  omega

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]

/-- The original degree-twelve model fails for every odd finite base field. -/
theorem twelfth_not_free (hq : Odd (Fintype.card F)) (hdegree : Module.finrank F E=12) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714WeightedPower.graph
        (Erdos714WeightedPower.powerMap E (torusExponent (Fintype.card F)))) := by
  have hcard : Fintype.card E=Fintype.card F^12 := by
    rw [Module.card_eq_pow_finrank (K := F),hdegree]
  have h₂ : (2 : E) ≠ 0 := two_ne_zero_of_odd_card (by rw [hcard]; exact hq.pow)
  apply finite_not_free hq h₂ hdegree
  refine ⟨2,?_⟩
  rw [hcard,exponent_factorization _ hq.pos,modulus,weightSize]
  ring

/-- The two-sheet refinement retains a whole skew K4,6; it is not a repair. -/
theorem twelfth_double_not_free (hq : Odd (Fintype.card F)) (hdegree : Module.finrank F E=12) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714WeightedPower.graph
        (Erdos714WeightedPower.powerMap E (torusExponent (Fintype.card F)/2))) := by
  have hcard : Fintype.card E=Fintype.card F^12 := by
    rw [Module.card_eq_pow_finrank (K := F),hdegree]
  have h₂ : (2 : E) ≠ 0 := two_ne_zero_of_odd_card (by rw [hcard]; exact hq.pow)
  apply finite_not_free hq h₂ hdegree
  rw [hcard,half_exponent_factorization _ hq]

lemma twelfth_weight_card (hdegree : Module.finrank F E=12) :
    Fintype.card (Erdos714WeightedPower.Weight E (torusExponent (Fintype.card F))) =
      weightSize (Fintype.card F) := by
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have hcard : Fintype.card E=Fintype.card F^12 := by
    rw [Module.card_eq_pow_finrank (K := F),hdegree]
  rw [Erdos714WeightedPower.weight_card,hcard,exponent_factorization _ hq,
    Nat.gcd_mul_right_left]
  exact Nat.mul_div_cancel_left _ (exponent_pos _)

lemma twelfth_double_weight_card (hq : Odd (Fintype.card F)) (hdegree : Module.finrank F E=12) :
    Fintype.card (Erdos714WeightedPower.Weight E (torusExponent (Fintype.card F)/2)) =
      2*weightSize (Fintype.card F) := by
  have hcard : Fintype.card E=Fintype.card F^12 := by
    rw [Module.card_eq_pow_finrank (K := F),hdegree]
  have hd : 0<torusExponent (Fintype.card F)/2 := by
    have he := Nat.div_mul_cancel (even_iff_two_dvd.mp (exponent_even _ hq))
    have hp := exponent_pos (Fintype.card F)
    omega
  rw [Erdos714WeightedPower.weight_card,hcard,half_exponent_factorization _ hq,
    Nat.gcd_mul_right_left,Nat.mul_div_cancel_left _ hd]
  unfold modulus weightSize
  ring

lemma twelfth_edges (hdegree : Module.finrank F E=12) :
    (Erdos714WeightedPower.graph
      (Erdos714WeightedPower.powerMap E (torusExponent (Fintype.card F)))).edgeFinset.card =
      Fintype.card F^12*weightSize (Fintype.card F)*(Fintype.card F^12-1) := by
  rw [Erdos714WeightedPower.edge_count,twelfth_weight_card hdegree,
    Module.card_eq_pow_finrank (K := F),hdegree]

lemma twelfth_double_edges (hq : Odd (Fintype.card F)) (hdegree : Module.finrank F E=12) :
    (Erdos714WeightedPower.graph
      (Erdos714WeightedPower.powerMap E (torusExponent (Fintype.card F)/2))).edgeFinset.card =
      Fintype.card F^12*(2*weightSize (Fintype.card F))*(Fintype.card F^12-1) := by
  rw [Erdos714WeightedPower.edge_count,twelfth_double_weight_card hq hdegree,
    Module.card_eq_pow_finrank (K := F),hdegree]

end Erdos714SkewPowerGrid
#print axioms Erdos714SkewPowerGrid.twelfth_not_free
#print axioms Erdos714SkewPowerGrid.twelfth_double_not_free
#print axioms Erdos714SkewPowerGrid.twelfth_weight_card
#print axioms Erdos714SkewPowerGrid.twelfth_double_weight_card
#print axioms Erdos714SkewPowerGrid.twelfth_edges
#print axioms Erdos714SkewPowerGrid.twelfth_double_edges
