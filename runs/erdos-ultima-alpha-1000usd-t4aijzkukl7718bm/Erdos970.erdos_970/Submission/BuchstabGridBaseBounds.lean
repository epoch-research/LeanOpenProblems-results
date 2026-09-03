import Submission.BuchstabGridBaseCheck

/-! The integer cross-product checks imply the rational initial-node bounds.
The symbolic conversion avoids expanding hundreds of rational divisions in
one kernel computation. -/
namespace Erdos970.BuchstabGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma base_formula_bound_nat (j : ℕ) (hj : j < 601) :
    baseFormula j ≤ ((baseNodes (j)) : ℚ)/scale := by
  have hc := integer_base_bound ⟨j,hj⟩
  change integerBaseBound j at hc
  by_cases h0 : j = 0
  · subst j
    decide +kernel
  have hjQ : (0 : ℚ) < j := by exact_mod_cast (show 0 < j by omega)
  unfold baseFormula
  rw [if_neg h0]
  unfold integerBaseBound at hc
  rw [if_neg h0] at hc
  by_cases h100 : j ≤ 100
  · rw [if_pos h100] at hc ⊢
    rw [show (100*(90009/50000 : ℚ))/(j : ℚ) = (100*90009)/(50000*j) by ring]
    apply (div_le_div_iff₀ (by positivity : (0 : ℚ) < 50000*j)
      (by norm_num [scale] : (0 : ℚ) < scale)).mpr
    have hcQ : (scale : ℚ)*100*90009 ≤ ((baseNodes (j)) : ℚ)*50000*j := by exact_mod_cast hc
    nlinarith only [hcQ]
  rw [if_neg h100] at hc ⊢
  by_cases h270 : j < 270
  · rw [if_pos h270] at hc ⊢
    have ha : j/10-10 < 18 := by omega
    have hb : j/10-10+1 < 18 := by omega
    have hv0 := profile_value_eq ⟨j/10-10,ha⟩
    have hv1 := profile_value_eq ⟨j/10-10+1,hb⟩
    dsimp only at hv0 hv1
    rw [hv0,hv1]
    have hr : j%10 ≤ 10 := by omega
    have hcQ : (scale : ℚ)*90009*((10-(j%10 : ℕ) : ℕ)*profileNumerators[j/10-10]!+
        ((j%10 : ℕ) : ℚ)*(profileNumerators[j/10-10+1]! : ℚ)) ≤ ((baseNodes (j)) : ℚ)*50000*10*scale := by exact_mod_cast hc
    push_cast at hcQ
    rw [Nat.cast_sub hr] at hcQ
    norm_num [scale] at hcQ ⊢
    nlinarith only [hcQ]
  rw [if_neg h270] at hc ⊢
  by_cases h400 : j < 400
  · rw [if_pos h400] at hc ⊢
    have hcQ : (scale : ℚ)*90009*581998 ≤ ((baseNodes (j)) : ℚ)*50000*scale := by exact_mod_cast hc
    norm_num [scale] at hcQ ⊢
    nlinarith only [hcQ]
  rw [if_neg h400] at hc ⊢
  have he : 1+(3/50 : ℚ)*(400/(j : ℚ))^8 = (50*(j : ℚ)^8+3*400^8)/(50*(j : ℚ)^8) := by
    field_simp
  rw [he]
  apply (div_le_div_iff₀ (by positivity : (0 : ℚ) < 50*(j : ℚ)^8)
    (by norm_num [scale] : (0 : ℚ) < scale)).mpr
  have hcQ : (scale : ℚ)*(50*(j : ℚ)^8+3*400^8) ≤ ((baseNodes (j)) : ℚ)*50*(j : ℚ)^8 := by exact_mod_cast hc
  nlinarith only [hcQ]

lemma base_formula_bound : ∀ j : Fin 601, baseFormula j.val ≤ ((baseNodes (j.val)) : ℚ)/scale :=
  fun j => base_formula_bound_nat j.val j.isLt

#print axioms base_formula_bound
end Erdos970.BuchstabGrid
