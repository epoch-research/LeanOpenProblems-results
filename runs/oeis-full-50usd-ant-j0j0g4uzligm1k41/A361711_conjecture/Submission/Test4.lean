import Mathlib
open Finset BigOperators Nat

noncomputable def CertN (n k : ℚ) : ℚ :=
  84*k^3*n^9+(436*k^3-234*k^4)*n^8+(261*k^5-981*k^4+786*k^3)*n^7
   +((-135)*k^6+840*k^5-1375*k^4+466*k^3)*n^6
   +(27*k^7-306*k^6+833*k^5-452*k^4-318*k^3)*n^5
   +(36*k^7-165*k^6-64*k^5+859*k^4-702*k^3)*n^4
   +((-3)*k^7+172*k^6-808*k^5+1183*k^4-484*k^3)*n^3
   +((-34)*k^7+274*k^6-718*k^5+704*k^4-188*k^3)*n^2
   +((-22)*k^7+136*k^6-292*k^5+248*k^4-64*k^3)*n
   -4*k^7+24*k^6-52*k^5+48*k^4-16*k^3
noncomputable def cc0 (n:ℚ):ℚ := -3*(n-1)*n*(3*n+1)*(3*n+2)*(3*n^2+4*n+2)
noncomputable def cc1 (n:ℚ):ℚ := -6*n*(6*n^3+12*n^2+5*n+1)
noncomputable def cc2 (n:ℚ):ℚ := -n^2*(n+2)^2*(3*n^2-2*n+1)
noncomputable def DD (n:ℚ):ℚ := n*(n-1)*(n+1)^2*(n+2)^2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem perterm (a k : ℕ) :
    DD ((a:ℚ)+(k:ℚ)+2) * (cc0 ((a:ℚ)+(k:ℚ)+2) * ((a+k+2).choose k : ℚ)^2 * ((a+k).choose k : ℚ) + cc1 ((a:ℚ)+(k:ℚ)+2) * ((a+k+3).choose k : ℚ)^2 * ((a+k+1).choose k : ℚ) + cc2 ((a:ℚ)+(k:ℚ)+2) * ((a+k+4).choose k : ℚ)^2 * ((a+k+2).choose k : ℚ))
      = - CertN ((a:ℚ)+(k:ℚ)+2) ((k:ℚ)+1) * ((a+k+2).choose (k+1) : ℚ) * ((a+k+4).choose (k+1) : ℚ)^2 - CertN ((a:ℚ)+(k:ℚ)+2) (k:ℚ) * ((a+k+2).choose k : ℚ) * ((a+k+4).choose k : ℚ)^2 := by
  have hR : (Nat.factorial k : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hQ : (Nat.factorial a : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos a).ne'
  have hP : (Nat.factorial (a+k) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (a+k)).ne'
  have v_Cnk : ((a+k+2).choose k : ℚ) = (Nat.factorial (a+k+2) : ℚ)/((Nat.factorial k : ℚ) * (Nat.factorial (a+2) : ℚ)) := by
    rw [eq_div_iff (mul_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne') (by exact_mod_cast (Nat.factorial_pos _).ne'))]
    have h := Nat.choose_mul_factorial_mul_factorial (n := a+k+2) (k := k) (by omega)
    rw [show (a+k+2) - k = a+2 from by omega] at h
    have hc := congrArg (fun x:ℕ => (x:ℚ)) h
    push_cast at hc ⊢
    linarith [hc]
  have v_Cn2k : ((a+k).choose k : ℚ) = (Nat.factorial (a+k) : ℚ)/((Nat.factorial k : ℚ) * (Nat.factorial (a) : ℚ)) := by
    rw [eq_div_iff (mul_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne') (by exact_mod_cast (Nat.factorial_pos _).ne'))]
    have h := Nat.choose_mul_factorial_mul_factorial (n := a+k) (k := k) (by omega)
    rw [show (a+k) - k = a from by omega] at h
    have hc := congrArg (fun x:ℕ => (x:ℚ)) h
    push_cast at hc ⊢
    linarith [hc]
  have v_Cn1k : ((a+k+3).choose k : ℚ) = (Nat.factorial (a+k+3) : ℚ)/((Nat.factorial k : ℚ) * (Nat.factorial (a+3) : ℚ)) := by
    rw [eq_div_iff (mul_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne') (by exact_mod_cast (Nat.factorial_pos _).ne'))]
    have h := Nat.choose_mul_factorial_mul_factorial (n := a+k+3) (k := k) (by omega)
    rw [show (a+k+3) - k = a+3 from by omega] at h
    have hc := congrArg (fun x:ℕ => (x:ℚ)) h
    push_cast at hc ⊢
    linarith [hc]
  have v_Cnm1k : ((a+k+1).choose k : ℚ) = (Nat.factorial (a+k+1) : ℚ)/((Nat.factorial k : ℚ) * (Nat.factorial (a+1) : ℚ)) := by
    rw [eq_div_iff (mul_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne') (by exact_mod_cast (Nat.factorial_pos _).ne'))]
    have h := Nat.choose_mul_factorial_mul_factorial (n := a+k+1) (k := k) (by omega)
    rw [show (a+k+1) - k = a+1 from by omega] at h
    have hc := congrArg (fun x:ℕ => (x:ℚ)) h
    push_cast at hc ⊢
    linarith [hc]
  have v_Cn2pk : ((a+k+4).choose k : ℚ) = (Nat.factorial (a+k+4) : ℚ)/((Nat.factorial k : ℚ) * (Nat.factorial (a+4) : ℚ)) := by
    rw [eq_div_iff (mul_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne') (by exact_mod_cast (Nat.factorial_pos _).ne'))]
    have h := Nat.choose_mul_factorial_mul_factorial (n := a+k+4) (k := k) (by omega)
    rw [show (a+k+4) - k = a+4 from by omega] at h
    have hc := congrArg (fun x:ℕ => (x:ℚ)) h
    push_cast at hc ⊢
    linarith [hc]
  have v_Cnkp1 : ((a+k+2).choose (k+1) : ℚ) = (Nat.factorial (a+k+2) : ℚ)/((Nat.factorial (k+1) : ℚ) * (Nat.factorial (a+1) : ℚ)) := by
    rw [eq_div_iff (mul_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne') (by exact_mod_cast (Nat.factorial_pos _).ne'))]
    have h := Nat.choose_mul_factorial_mul_factorial (n := a+k+2) (k := (k+1)) (by omega)
    rw [show (a+k+2) - (k+1) = a+1 from by omega] at h
    have hc := congrArg (fun x:ℕ => (x:ℚ)) h
    push_cast at hc ⊢
    linarith [hc]
  have v_Cn2kp1 : ((a+k+4).choose (k+1) : ℚ) = (Nat.factorial (a+k+4) : ℚ)/((Nat.factorial (k+1) : ℚ) * (Nat.factorial (a+3) : ℚ)) := by
    rw [eq_div_iff (mul_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne') (by exact_mod_cast (Nat.factorial_pos _).ne'))]
    have h := Nat.choose_mul_factorial_mul_factorial (n := a+k+4) (k := (k+1)) (by omega)
    rw [show (a+k+4) - (k+1) = a+3 from by omega] at h
    have hc := congrArg (fun x:ℕ => (x:ℚ)) h
    push_cast at hc ⊢
    linarith [hc]
  have fe_apk1 : (Nat.factorial (a+k+1) : ℚ) = (↑(a+k+1):ℚ)*(Nat.factorial (a+k) : ℚ) := by
    rw [show a+k+1 = a+k+0+1 from by omega, Nat.factorial_succ]
    push_cast; ring
  have fe_apk2 : (Nat.factorial (a+k+2) : ℚ) = (↑(a+k+2):ℚ)*(↑(a+k+1):ℚ)*(Nat.factorial (a+k) : ℚ) := by
    rw [show a+k+2 = a+k+1+1 from by omega, Nat.factorial_succ]
    rw [show a+k+1 = a+k+0+1 from by omega, Nat.factorial_succ]
    push_cast; ring
  have fe_apk3 : (Nat.factorial (a+k+3) : ℚ) = (↑(a+k+3):ℚ)*(↑(a+k+2):ℚ)*(↑(a+k+1):ℚ)*(Nat.factorial (a+k) : ℚ) := by
    rw [show a+k+3 = a+k+2+1 from by omega, Nat.factorial_succ]
    rw [show a+k+2 = a+k+1+1 from by omega, Nat.factorial_succ]
    rw [show a+k+1 = a+k+0+1 from by omega, Nat.factorial_succ]
    push_cast; ring
  have fe_apk4 : (Nat.factorial (a+k+4) : ℚ) = (↑(a+k+4):ℚ)*(↑(a+k+3):ℚ)*(↑(a+k+2):ℚ)*(↑(a+k+1):ℚ)*(Nat.factorial (a+k) : ℚ) := by
    rw [show a+k+4 = a+k+3+1 from by omega, Nat.factorial_succ]
    rw [show a+k+3 = a+k+2+1 from by omega, Nat.factorial_succ]
    rw [show a+k+2 = a+k+1+1 from by omega, Nat.factorial_succ]
    rw [show a+k+1 = a+k+0+1 from by omega, Nat.factorial_succ]
    push_cast; ring
  have fe_a1 : (Nat.factorial (a+1) : ℚ) = (↑(a+1):ℚ)*(Nat.factorial (a) : ℚ) := by
    rw [show a+1 = a+0+1 from by omega, Nat.factorial_succ]
    push_cast; ring
  have fe_a2 : (Nat.factorial (a+2) : ℚ) = (↑(a+2):ℚ)*(↑(a+1):ℚ)*(Nat.factorial (a) : ℚ) := by
    rw [show a+2 = a+1+1 from by omega, Nat.factorial_succ]
    rw [show a+1 = a+0+1 from by omega, Nat.factorial_succ]
    push_cast; ring
  have fe_a3 : (Nat.factorial (a+3) : ℚ) = (↑(a+3):ℚ)*(↑(a+2):ℚ)*(↑(a+1):ℚ)*(Nat.factorial (a) : ℚ) := by
    rw [show a+3 = a+2+1 from by omega, Nat.factorial_succ]
    rw [show a+2 = a+1+1 from by omega, Nat.factorial_succ]
    rw [show a+1 = a+0+1 from by omega, Nat.factorial_succ]
    push_cast; ring
  have fe_a4 : (Nat.factorial (a+4) : ℚ) = (↑(a+4):ℚ)*(↑(a+3):ℚ)*(↑(a+2):ℚ)*(↑(a+1):ℚ)*(Nat.factorial (a) : ℚ) := by
    rw [show a+4 = a+3+1 from by omega, Nat.factorial_succ]
    rw [show a+3 = a+2+1 from by omega, Nat.factorial_succ]
    rw [show a+2 = a+1+1 from by omega, Nat.factorial_succ]
    rw [show a+1 = a+0+1 from by omega, Nat.factorial_succ]
    push_cast; ring
  have fe_k1 : (Nat.factorial (k+1) : ℚ) = (↑(k+1):ℚ)*(Nat.factorial (k) : ℚ) := by
    rw [show k+1 = k+0+1 from by omega, Nat.factorial_succ]
    push_cast; ring
  rw [v_Cnk, v_Cn2k, v_Cn1k, v_Cnm1k, v_Cn2pk, v_Cnkp1, v_Cn2kp1]
  rw [fe_apk1, fe_apk2, fe_apk3, fe_apk4, fe_a1, fe_a2, fe_a3, fe_a4, fe_k1]
  simp only [CertN, cc0, cc1, cc2, DD]
  push_cast
  field_simp
  ring