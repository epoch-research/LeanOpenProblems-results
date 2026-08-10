import Submission.Closed2
open Finset BigOperators Nat

theorem hfilterprod (p M M' d : ℕ) (hp2 : 2 ≤ p) (hd : 2*d+1 = p) (hM : M = p*M' + d) :
    ∏ i ∈ (Finset.range M).filter (fun i => p ∣ (i+1)), (1 - (2*(M:ℚ)+1)^2/((i:ℚ)+1)^2)
    = ∏ j ∈ Finset.range M', (1 - (2*(M':ℚ)+1)^2/((j:ℚ)+1)^2) := by
  classical
  have hp0 : 0 < p := by omega
  have hnat : 2*M+1 = p*(2*M'+1) := by
    rw [hM, show p*(2*M'+1) = 2*(p*M')+p from by ring]; omega
  have h2M : (2*(M:ℚ)+1) = (p:ℚ)*(2*(M':ℚ)+1) := by exact_mod_cast hnat
  apply Finset.prod_bij' (i := fun a _ => (a+1)/p - 1) (j := fun b _ => p*(b+1)-1)
  · -- hi : i a ha ∈ range M'
    intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha
    rw [Finset.mem_range]
    have hdvd := ha.2
    have hc : p * ((a+1)/p) = a+1 := Nat.mul_div_cancel' hdvd
    have hple : p ≤ a+1 := Nat.le_of_dvd (by omega) hdvd
    have hc1 : 1 ≤ (a+1)/p := (Nat.one_le_div_iff hp0).mpr hple
    have hcM : (a+1)/p ≤ M' := by
      by_contra hcon
      push_neg at hcon
      have hmul : p*(M'+1) ≤ p*((a+1)/p) := mul_le_mul_left' (by omega) p
      have he : p*(M'+1) = p*M'+p := by ring
      omega
    omega
  · -- hj : j b hb ∈ s
    intro b hb
    rw [Finset.mem_range] at hb
    rw [Finset.mem_filter, Finset.mem_range]
    have hmul : p*(b+1) ≤ p*M' := mul_le_mul_left' (by omega) p
    have hge : 1 ≤ p*(b+1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    constructor
    · omega
    · have : p*(b+1)-1+1 = p*(b+1) := by omega
      rw [this]; exact Dvd.intro _ rfl
  · -- left_inv
    intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha
    have hc : p * ((a+1)/p) = a+1 := Nat.mul_div_cancel' ha.2
    have hple : p ≤ a+1 := Nat.le_of_dvd (by omega) ha.2
    have hc1 : 1 ≤ (a+1)/p := (Nat.one_le_div_iff hp0).mpr hple
    have : (a+1)/p - 1 + 1 = (a+1)/p := by omega
    rw [this, hc]; omega
  · -- right_inv
    intro b hb
    rw [Finset.mem_range] at hb
    have hge : 1 ≤ p*(b+1) := by
      have h1 : 1 ≤ b+1 := by omega
      calc 1 ≤ p*1 := by omega
        _ ≤ p*(b+1) := mul_le_mul_left' h1 p
    have h1 : p*(b+1)-1+1 = p*(b+1) := by omega
    rw [h1, Nat.mul_div_cancel_left _ hp0]; omega
  · -- h : f a = g (i a ha)
    intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha
    have hc : p * ((a+1)/p) = a+1 := Nat.mul_div_cancel' ha.2
    have hple : p ≤ a+1 := Nat.le_of_dvd (by omega) ha.2
    have hc1 : 1 ≤ (a+1)/p := (Nat.one_le_div_iff hp0).mpr hple
    have he1 : (a+1)/p - 1 + 1 = (a+1)/p := by omega
    have hcast : ((((a+1)/p - 1 : ℕ):ℚ)+1) = ((a:ℚ)+1)/(p:ℚ) := by
      rw [← Nat.cast_add_one, he1, eq_div_iff (by positivity : (p:ℚ)≠0)]
      have hc' := congrArg (Nat.cast : ℕ → ℚ) hc
      push_cast at hc' ⊢; linarith [hc']
    rw [hcast, h2M]
    have hane : ((a:ℚ)+1) ≠ 0 := by positivity
    have hpne : (p:ℚ) ≠ 0 := by positivity
    field_simp
