import FormalConjectures.Util.ProblemImports

open Nat Real

lemma log_le_log_of_le {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : Real.log x ≤ Real.log y := by
  exact (Real.log_le_log hx h)

lemma log_lt_log_of_lt {x y : ℝ} (hx : 0 < x) (h : x < y) : Real.log x < Real.log y := by
  rwa [Real.log_lt_log_iff hx (by linarith)]

lemma logb_two_bounds {C : ℕ} (hC : C > 1) {a b d : ℕ} (hb : b > 0) (hl : 2^a ≤ C^b) (hu : C^b < 2^d) :
  (a : ℝ) / (b : ℝ) ≤ Real.logb 2 C ∧ Real.logb 2 C < (d : ℝ) / (b : ℝ) := by
  have hC_pos : (0 : ℝ) < C := by positivity
  have h_two_pos : (0 : ℝ) < 2 := by norm_num
  have h_log_two : (0 : ℝ) < Real.log 2 := by
    have : (1 : ℝ) < 2 := by norm_num
    exact Real.log_pos this
  have hb_real : (0 : ℝ) < (b : ℝ) := by positivity
  
  -- We prove the lower bound first: (a : ℝ) / (b : ℝ) ≤ Real.logb 2 C
  have hl_real : (2 : ℝ)^a ≤ (C : ℝ)^b := by
    exact_mod_cast hl
  
  have h_log_l : Real.log (2^a) ≤ Real.log (C^b) := by
    apply log_le_log_of_le (by positivity) hl_real
    
  rw [Real.log_pow 2 a, Real.log_pow (C : ℝ) b] at h_log_l
  
  have h_log_l' : (a : ℝ) * Real.log 2 ≤ Real.log (C : ℝ) * (b : ℝ) := by
    rw [mul_comm (Real.log (C : ℝ))]
    exact h_log_l
    
  have h_lower_1 : (a : ℝ) * Real.log 2 / (b : ℝ) ≤ Real.log (C : ℝ) := by
    exact (div_le_iff₀ hb_real).mpr h_log_l'
    
  have h_lower : (a : ℝ) / (b : ℝ) ≤ Real.log (C : ℝ) / Real.log 2 := by
    have h_lower_2 : (a : ℝ) / (b : ℝ) * Real.log 2 ≤ Real.log (C : ℝ) := by
      calc (a : ℝ) / (b : ℝ) * Real.log 2
        _ = (a : ℝ) * Real.log 2 / (b : ℝ) := by ring
        _ ≤ Real.log (C : ℝ) := h_lower_1
    exact (le_div_iff₀ h_log_two).mpr h_lower_2

  -- Now the upper bound: Real.logb 2 C < (d : ℝ) / (b : ℝ)
  have hu_real : (C : ℝ)^b < (2 : ℝ)^d := by
    exact_mod_cast hu
    
  have h_log_u : Real.log (C^b) < Real.log (2^d) := by
    apply log_lt_log_of_lt (by positivity) hu_real
    
  rw [Real.log_pow (C : ℝ) b, Real.log_pow 2 d] at h_log_u
  
  have h_log_u' : Real.log (C : ℝ) * (b : ℝ) < (d : ℝ) * Real.log 2 := by
    rw [mul_comm (Real.log (C : ℝ))]
    exact h_log_u
    
  have h_upper_1 : Real.log (C : ℝ) < (d : ℝ) * Real.log 2 / (b : ℝ) := by
    exact (lt_div_iff₀ hb_real).mpr h_log_u'
    
  have h_upper : Real.log (C : ℝ) / Real.log 2 < (d : ℝ) / (b : ℝ) := by
    have h_upper_2 : Real.log (C : ℝ) < (d : ℝ) / (b : ℝ) * Real.log 2 := by
      calc Real.log (C : ℝ)
        _ < (d : ℝ) * Real.log 2 / (b : ℝ) := h_upper_1
        _ = (d : ℝ) / (b : ℝ) * Real.log 2 := by ring
    exact (div_lt_iff₀ h_log_two).mpr h_upper_2
    
  rw [Real.logb]
  exact ⟨h_lower, h_upper⟩
