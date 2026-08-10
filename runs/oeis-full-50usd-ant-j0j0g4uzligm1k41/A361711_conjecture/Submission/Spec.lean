import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

/--
A361711: $a(1) = 1$ and $a(n) = \sum_{k = 0}^{n-2} (-1)^k \binom{n}{k}^2 \binom{n-2}{k}$ for $n \ge 2$.
-/
def A361711 (n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | 1 => 1
  | n_ge_2 =>
    let N := n_ge_2
    -- $n-2$ is the upper limit of summation.
    let m : ℕ := N - 2

    -- The sum is over k from 0 to m, which is Finset.range (m + 1).
    (Finset.range (m + 1)).sum fun k : ℕ =>
      let term_nat : ℕ := (N.choose k) * (N.choose k) * (m.choose k)
      let sign_k : ℤ := (-1 : ℤ) ^ k
      sign_k * term_nat.cast

-- ===== from Closed =====

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
set_option maxHeartbeats 1000000 in
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
    rw [show a+k+1 = a+k+0+1 from by omega, Nat.factorial_succ]; push_cast; ring
  have fe_apk2 : (Nat.factorial (a+k+2) : ℚ) = (↑(a+k+2):ℚ)*(↑(a+k+1):ℚ)*(Nat.factorial (a+k) : ℚ) := by
    rw [show a+k+2 = a+k+1+1 from by omega, Nat.factorial_succ, show a+k+1 = a+k+0+1 from by omega, Nat.factorial_succ]; push_cast; ring
  have fe_apk3 : (Nat.factorial (a+k+3) : ℚ) = (↑(a+k+3):ℚ)*(↑(a+k+2):ℚ)*(↑(a+k+1):ℚ)*(Nat.factorial (a+k) : ℚ) := by
    rw [show a+k+3 = a+k+2+1 from by omega, Nat.factorial_succ, show a+k+2 = a+k+1+1 from by omega, Nat.factorial_succ, show a+k+1 = a+k+0+1 from by omega, Nat.factorial_succ]; push_cast; ring
  have fe_apk4 : (Nat.factorial (a+k+4) : ℚ) = (↑(a+k+4):ℚ)*(↑(a+k+3):ℚ)*(↑(a+k+2):ℚ)*(↑(a+k+1):ℚ)*(Nat.factorial (a+k) : ℚ) := by
    rw [show a+k+4 = a+k+3+1 from by omega, Nat.factorial_succ, show a+k+3 = a+k+2+1 from by omega, Nat.factorial_succ, show a+k+2 = a+k+1+1 from by omega, Nat.factorial_succ, show a+k+1 = a+k+0+1 from by omega, Nat.factorial_succ]; push_cast; ring
  have fe_a1 : (Nat.factorial (a+1) : ℚ) = (↑(a+1):ℚ)*(Nat.factorial (a) : ℚ) := by
    rw [show a+1 = a+0+1 from by omega, Nat.factorial_succ]; push_cast; ring
  have fe_a2 : (Nat.factorial (a+2) : ℚ) = (↑(a+2):ℚ)*(↑(a+1):ℚ)*(Nat.factorial (a) : ℚ) := by
    rw [show a+2 = a+1+1 from by omega, Nat.factorial_succ, show a+1 = a+0+1 from by omega, Nat.factorial_succ]; push_cast; ring
  have fe_a3 : (Nat.factorial (a+3) : ℚ) = (↑(a+3):ℚ)*(↑(a+2):ℚ)*(↑(a+1):ℚ)*(Nat.factorial (a) : ℚ) := by
    rw [show a+3 = a+2+1 from by omega, Nat.factorial_succ, show a+2 = a+1+1 from by omega, Nat.factorial_succ, show a+1 = a+0+1 from by omega, Nat.factorial_succ]; push_cast; ring
  have fe_a4 : (Nat.factorial (a+4) : ℚ) = (↑(a+4):ℚ)*(↑(a+3):ℚ)*(↑(a+2):ℚ)*(↑(a+1):ℚ)*(Nat.factorial (a) : ℚ) := by
    rw [show a+4 = a+3+1 from by omega, Nat.factorial_succ, show a+3 = a+2+1 from by omega, Nat.factorial_succ, show a+2 = a+1+1 from by omega, Nat.factorial_succ, show a+1 = a+0+1 from by omega, Nat.factorial_succ]; push_cast; ring
  have fe_k1 : (Nat.factorial (k+1) : ℚ) = (↑(k+1):ℚ)*(Nat.factorial (k) : ℚ) := by
    rw [show k+1 = k+0+1 from by omega, Nat.factorial_succ]; push_cast; ring
  rw [v_Cnk, v_Cn2k, v_Cn1k, v_Cnm1k, v_Cn2pk, v_Cnkp1, v_Cn2kp1]
  rw [fe_apk1, fe_apk2, fe_apk3, fe_apk4, fe_a1, fe_a2, fe_a3, fe_a4, fe_k1]
  clear v_Cnk v_Cn2k v_Cn1k v_Cnm1k v_Cn2pk v_Cnkp1 v_Cn2kp1 fe_apk1 fe_apk2 fe_apk3 fe_apk4 fe_a1 fe_a2 fe_a3 fe_a4 fe_k1
  simp only [CertN, cc0, cc1, cc2, DD]
  push_cast
  field_simp
  ring

noncomputable def Fq (n k : ℕ) : ℚ := (-1:ℚ)^k * ((n.choose k : ℚ))^2 * ((n-2).choose k : ℚ)
noncomputable def Hc (n k : ℕ) : ℚ := (-1:ℚ)^k * CertN (n:ℚ) (k:ℚ) * ((n.choose k : ℚ)) * ((n+2).choose k : ℚ)^2

theorem pt (a k : ℕ) :
    DD ((a+k+2 : ℕ):ℚ) * (cc0 ((a+k+2:ℕ):ℚ) * Fq (a+k+2) k + cc1 ((a+k+2:ℕ):ℚ) * Fq (a+k+3) k + cc2 ((a+k+2:ℕ):ℚ) * Fq (a+k+4) k)
      = Hc (a+k+2) (k+1) - Hc (a+k+2) k := by
  simp only [Fq, Hc]
  rw [show a+k+2-2 = a+k from by omega, show a+k+3-2 = a+k+1 from by omega,
      show a+k+4-2 = a+k+2 from by omega, show a+k+2+2 = a+k+4 from by omega]
  have hp := perterm a k
  push_cast
  push_cast at hp
  linear_combination ((-1:ℚ)^k) * hp

-- ===== from Rec =====

noncomputable def aaq (n : ℕ) : ℚ := ∑ k ∈ range (n+1), Fq n k

lemma Fq_zero (m j : ℕ) (h : m - 2 < j) : Fq m j = 0 := by
  simp only [Fq, Nat.choose_eq_zero_of_lt h, Nat.cast_zero, mul_zero]

lemma CertN_zero (x : ℚ) : CertN x 0 = 0 := by simp only [CertN]; ring

lemma Hc_zero (n : ℕ) : Hc n 0 = 0 := by
  simp only [Hc, Nat.cast_zero, CertN_zero, mul_zero, zero_mul]

-- boundary identity
theorem hbdry (n : ℕ) (hn : 2 ≤ n) :
    Hc n (n-1) + DD (n:ℚ) * (cc1 (n:ℚ) * Fq (n+1) (n-1) + cc2 (n:ℚ) * Fq (n+2) (n-1) + cc2 (n:ℚ) * Fq (n+2) n) = 0 := by
  obtain ⟨a, rfl⟩ : ∃ a, n = a + 2 := ⟨n-2, by omega⟩
  rw [show a+2-1 = a+1 from by omega, show a+2+1 = a+3 from by omega, show a+2+2 = a+4 from by omega]
  have hf1 : (Nat.factorial (a+1):ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have w1 : ((a+2).choose (a+1):ℚ) = (Nat.factorial (a+2))/((Nat.factorial (a+1))*(Nat.factorial 1)) := by
    rw [eq_div_iff (mul_ne_zero hf1 (by norm_num [Nat.factorial]))]
    have h := Nat.choose_mul_factorial_mul_factorial (n := a+2) (k := a+1) (by omega)
    rw [show a+2-(a+1)=1 from by omega] at h
    have hc := congrArg (Nat.cast : ℕ → ℚ) h; push_cast at hc ⊢; linarith [hc]
  have w2 : ((a+3).choose (a+1):ℚ) = (Nat.factorial (a+3))/((Nat.factorial (a+1))*(Nat.factorial 2)) := by
    rw [eq_div_iff (mul_ne_zero hf1 (by norm_num [Nat.factorial]))]
    have h := Nat.choose_mul_factorial_mul_factorial (n := a+3) (k := a+1) (by omega)
    rw [show a+3-(a+1)=2 from by omega] at h
    have hc := congrArg (Nat.cast : ℕ → ℚ) h; push_cast at hc ⊢; linarith [hc]
  have w3 : ((a+4).choose (a+1):ℚ) = (Nat.factorial (a+4))/((Nat.factorial (a+1))*(Nat.factorial 3)) := by
    rw [eq_div_iff (mul_ne_zero hf1 (by norm_num [Nat.factorial]))]
    have h := Nat.choose_mul_factorial_mul_factorial (n := a+4) (k := a+1) (by omega)
    rw [show a+4-(a+1)=3 from by omega] at h
    have hc := congrArg (Nat.cast : ℕ → ℚ) h; push_cast at hc ⊢; linarith [hc]
  have hf2 : (Nat.factorial (a+2):ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have w4 : ((a+4).choose (a+2):ℚ) = (Nat.factorial (a+4))/((Nat.factorial (a+2))*(Nat.factorial 2)) := by
    rw [eq_div_iff (mul_ne_zero hf2 (by norm_num [Nat.factorial]))]
    have h := Nat.choose_mul_factorial_mul_factorial (n := a+4) (k := a+2) (by omega)
    rw [show a+4-(a+2)=2 from by omega] at h
    have hc := congrArg (Nat.cast : ℕ → ℚ) h; push_cast at hc ⊢; linarith [hc]
  have ea2 : (Nat.factorial (a+2):ℚ) = (↑(a+2))*(Nat.factorial (a+1)) := by
    rw [show a+2=(a+1)+1 from by omega, Nat.factorial_succ]; push_cast; ring
  have ea3 : (Nat.factorial (a+3):ℚ) = (↑(a+3))*(↑(a+2))*(Nat.factorial (a+1)) := by
    rw [show a+3=(a+2)+1 from by omega, Nat.factorial_succ, show a+2=(a+1)+1 from by omega, Nat.factorial_succ]; push_cast; ring
  have ea4 : (Nat.factorial (a+4):ℚ) = (↑(a+4))*(↑(a+3))*(↑(a+2))*(Nat.factorial (a+1)) := by
    rw [show a+4=(a+3)+1 from by omega, Nat.factorial_succ, show a+3=(a+2)+1 from by omega, Nat.factorial_succ, show a+2=(a+1)+1 from by omega, Nat.factorial_succ]; push_cast; ring
  have hsign : (-1:ℚ)^(a+2) = (-1)^(a+1) * (-1) := by rw [show a+2 = (a+1)+1 from by omega, pow_succ]
  simp only [Hc, Fq]
  rw [show (a+2)+2 = a+4 from by omega, show a+3-2 = a+1 from by omega, show a+4-2 = a+2 from by omega]
  rw [Nat.choose_self (a+1), Nat.choose_self (a+2)]
  rw [w1, w2, w3, w4, ea2, ea3, ea4, hsign]
  simp only [CertN, cc0, cc1, cc2, DD, Nat.factorial]
  push_cast
  field_simp
  ring

theorem nrec (n : ℕ) (hn : 2 ≤ n) :
    cc0 (n:ℚ) * aaq n + cc1 (n:ℚ) * aaq (n+1) + cc2 (n:ℚ) * aaq (n+2) = 0 := by
  have htel : ∑ k ∈ range (n-1), (Hc n (k+1) - Hc n k) = Hc n (n-1) - Hc n 0 :=
    Finset.sum_range_sub (fun k => Hc n k) (n-1)
  have hcong : ∑ k ∈ range (n-1), (Hc n (k+1) - Hc n k)
      = ∑ k ∈ range (n-1), DD (n:ℚ) * (cc0 (n:ℚ) * Fq n k + cc1 (n:ℚ) * Fq (n+1) k + cc2 (n:ℚ) * Fq (n+2) k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hp := pt (n-2-k) k
    rw [show n-2-k+k+2 = n from by omega, show n-2-k+k+3 = n+1 from by omega, show n-2-k+k+4 = n+2 from by omega] at hp
    exact hp.symm
  have hS0 : ∑ k ∈ range (n-1), Fq n k = aaq n := by
    rw [aaq]; apply Finset.sum_subset
    · intro x hx; rw [Finset.mem_range] at *; omega
    · intro x hx hnx; rw [Finset.mem_range] at hx hnx; apply Fq_zero; omega
  have hS1 : ∑ k ∈ range (n-1), Fq (n+1) k = aaq (n+1) - Fq (n+1) (n-1) := by
    have h1 : ∑ k ∈ range n, Fq (n+1) k = aaq (n+1) := by
      rw [aaq]; apply Finset.sum_subset
      · intro x hx; rw [Finset.mem_range] at *; omega
      · intro x hx hnx; rw [Finset.mem_range] at hx hnx; apply Fq_zero; omega
    have h2 : ∑ k ∈ range n, Fq (n+1) k = ∑ k ∈ range (n-1), Fq (n+1) k + Fq (n+1) (n-1) := by
      have hr : range n = range ((n-1)+1) := by congr 1; omega
      rw [hr, Finset.sum_range_succ]
    rw [h2] at h1; linarith [h1]
  have hS2 : ∑ k ∈ range (n-1), Fq (n+2) k = aaq (n+2) - Fq (n+2) (n-1) - Fq (n+2) n := by
    have h1 : ∑ k ∈ range (n+1), Fq (n+2) k = aaq (n+2) := by
      rw [aaq]; apply Finset.sum_subset
      · intro x hx; rw [Finset.mem_range] at *; omega
      · intro x hx hnx; rw [Finset.mem_range] at hx hnx; apply Fq_zero; omega
    have h2 : ∑ k ∈ range (n+1), Fq (n+2) k = ∑ k ∈ range n, Fq (n+2) k + Fq (n+2) n :=
      Finset.sum_range_succ _ _
    have h3 : ∑ k ∈ range n, Fq (n+2) k = ∑ k ∈ range (n-1), Fq (n+2) k + Fq (n+2) (n-1) := by
      have hr : range n = range ((n-1)+1) := by congr 1; omega
      rw [hr, Finset.sum_range_succ]
    rw [h3] at h2; rw [h2] at h1; linarith [h1]
  have hsplit : ∑ k ∈ range (n-1), (cc0 (n:ℚ) * Fq n k + cc1 (n:ℚ) * Fq (n+1) k + cc2 (n:ℚ) * Fq (n+2) k)
      = cc0 (n:ℚ) * (∑ k ∈ range (n-1), Fq n k) + cc1 (n:ℚ) * (∑ k ∈ range (n-1), Fq (n+1) k) + cc2 (n:ℚ) * (∑ k ∈ range (n-1), Fq (n+2) k) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsum : DD (n:ℚ) * (∑ k ∈ range (n-1), (cc0 (n:ℚ) * Fq n k + cc1 (n:ℚ) * Fq (n+1) k + cc2 (n:ℚ) * Fq (n+2) k)) = Hc n (n-1) - Hc n 0 := by
    rw [Finset.mul_sum, ← hcong, htel]
  rw [hsplit, hS0, hS1, hS2, Hc_zero] at hsum
  have hb := hbdry n hn
  have hDD : DD (n:ℚ) ≠ 0 := by
    have hn2 : (2:ℚ) ≤ (n:ℚ) := by exact_mod_cast hn
    simp only [DD]
    have e1 : (0:ℚ) < (n:ℚ) := by linarith
    have e2 : (0:ℚ) < (n:ℚ)-1 := by linarith
    have e3 : (0:ℚ) < ((n:ℚ)+1)^2 := by positivity
    have e4 : (0:ℚ) < ((n:ℚ)+2)^2 := by positivity
    exact (mul_pos (mul_pos (mul_pos e1 e2) e3) e4).ne'
  have hkey : DD (n:ℚ) * (cc0 (n:ℚ) * aaq n + cc1 (n:ℚ) * aaq (n+1) + cc2 (n:ℚ) * aaq (n+2)) = 0 := by
    linear_combination hsum + hb
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h hDD
  · exact h

-- ===== from Closed2 =====

def Gnat (m : ℕ) : ℕ := (2*m).choose m * (3*m+1).choose m
noncomputable def gq (m : ℕ) : ℚ := (-1:ℚ)^m * (Gnat m : ℚ)

theorem hGrec (m : ℕ) :
    ((m:ℚ)+1)^2*(2*(m:ℚ)+3)*(Gnat (m+1):ℚ) = 3*(2*(m:ℚ)+1)*(3*(m:ℚ)+2)*(3*(m:ℚ)+4)*(Gnat m:ℚ) := by
  have hm : (Nat.factorial m : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h2m1 : (Nat.factorial (2*m+1) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hmp1 : ((m:ℚ)+1) ≠ 0 := by positivity
  have fA : ((2*m+2).factorial:ℚ)=(2*(m:ℚ)+2)*(2*(m:ℚ)+1)*((2*m).factorial) := by
    rw [show 2*m+2=(2*m+1)+1 from by ring, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have fB : ((m+1).factorial:ℚ)=((m:ℚ)+1)*(m.factorial) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have fC : ((3*m+4).factorial:ℚ)=(3*(m:ℚ)+4)*(3*(m:ℚ)+3)*(3*(m:ℚ)+2)*((3*m+1).factorial) := by
    rw [show 3*m+4=(3*m+3)+1 from by ring, Nat.factorial_succ, show 3*m+3=(3*m+2)+1 from by ring, Nat.factorial_succ, show 3*m+2=(3*m+1)+1 from by ring, Nat.factorial_succ]; push_cast; ring
  have fD : ((2*m+3).factorial:ℚ)=(2*(m:ℚ)+3)*(2*(m:ℚ)+2)*((2*m+1).factorial) := by
    rw [show 2*m+3=(2*m+2)+1 from by ring, Nat.factorial_succ, show 2*m+2=(2*m+1)+1 from by ring, Nat.factorial_succ]; push_cast; ring
  simp only [Gnat]
  push_cast
  rw [Nat.cast_choose ℚ (show m ≤ 2*m by omega), Nat.cast_choose ℚ (show m ≤ 3*m+1 by omega),
      Nat.cast_choose ℚ (show m+1 ≤ 2*(m+1) by omega), Nat.cast_choose ℚ (show m+1 ≤ 3*(m+1)+1 by omega)]
  rw [show 2*m-m = m from by omega, show 3*m+1-m = 2*m+1 from by omega,
      show 2*(m+1) = 2*m+2 from by ring, show 2*m+2-(m+1) = m+1 from by omega,
      show 3*(m+1)+1 = 3*m+4 from by ring, show 3*m+4-(m+1) = 2*m+3 from by omega]
  rw [fA, fB, fC, fD]
  field_simp

noncomputable def AA (m:ℕ):ℚ := -(cc0 (↑(2*m+1)) * cc0 (↑(2*m+2)) * cc1 (↑(2*m+3)))
noncomputable def BB (m:ℕ):ℚ := cc1 (↑(2*m+1)) * cc1 (↑(2*m+2)) * cc1 (↑(2*m+3)) - cc2 (↑(2*m+1)) * cc0 (↑(2*m+2)) * cc1 (↑(2*m+3)) - cc1 (↑(2*m+1)) * cc2 (↑(2*m+2)) * cc0 (↑(2*m+3))
noncomputable def CC (m:ℕ):ℚ := -(cc1 (↑(2*m+1)) * cc2 (↑(2*m+2)) * cc2 (↑(2*m+3)))

theorem aaq1 : aaq 1 = 1 := by
  rw [aaq]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Fq]
theorem aaq2 : aaq 2 = 1 := by
  rw [aaq]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Fq]
theorem aaq3 : aaq 3 = -8 := by
  rw [aaq]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Fq]

theorem nrec1 : cc0 ((1:ℕ):ℚ) * aaq 1 + cc1 ((1:ℕ):ℚ) * aaq 2 + cc2 ((1:ℕ):ℚ) * aaq 3 = 0 := by
  rw [aaq1, aaq2, aaq3]; simp only [cc0, cc1, cc2]; norm_num

theorem nrec_ge1 (n:ℕ) (hn:1≤n) :
    cc0 (n:ℚ)*aaq n + cc1 (n:ℚ)*aaq (n+1) + cc2 (n:ℚ)*aaq (n+2) = 0 := by
  rcases lt_or_ge n 2 with h | h
  · interval_cases n
    exact nrec1
  · exact nrec n h

theorem Rrec (m:ℕ) : AA m * aaq (2*m+1) + BB m * aaq (2*m+3) + CC m * aaq (2*m+5) = 0 := by
  have E0 := nrec_ge1 (2*m+1) (by omega)
  have E1 := nrec_ge1 (2*m+2) (by omega)
  have E2 := nrec_ge1 (2*m+3) (by omega)
  rw [show 2*m+1+1=2*m+2 from by ring, show 2*m+1+2=2*m+3 from by ring] at E0
  rw [show 2*m+2+1=2*m+3 from by ring, show 2*m+2+2=2*m+4 from by ring] at E1
  rw [show 2*m+3+1=2*m+4 from by ring, show 2*m+3+2=2*m+5 from by ring] at E2
  simp only [AA, BB, CC]
  linear_combination (cc1 (↑(2*m+1)) * cc1 (↑(2*m+3))) * E1 - (cc0 (↑(2*m+2)) * cc1 (↑(2*m+3))) * E0 - (cc2 (↑(2*m+2)) * cc1 (↑(2*m+1))) * E2

set_option maxHeartbeats 1000000 in
theorem hGid (m:ℕ) : AA m * (Gnat m:ℚ) - BB m * (Gnat (m+1):ℚ) + CC m * (Gnat (m+2):ℚ) = 0 := by
  have hr0 := hGrec m
  have hr1 := hGrec (m+1)
  rw [show m+1+1 = m+2 from rfl] at hr1
  push_cast at hr1
  have hP : (((m:ℚ)+1)^2*(2*(m:ℚ)+3)) * (((m:ℚ)+2)^2*(2*(m:ℚ)+5)) ≠ 0 := by positivity
  have hcl : (((m:ℚ)+1)^2*(2*(m:ℚ)+3)) * (((m:ℚ)+2)^2*(2*(m:ℚ)+5)) * (AA m * (Gnat m:ℚ) - BB m * (Gnat (m+1):ℚ) + CC m * (Gnat (m+2):ℚ)) = 0 := by
    simp only [AA, BB, CC, cc0, cc1, cc2]
    push_cast
    linear_combination ((-1146617856)*(m:ℚ)^19 + (-28474343424)*(m:ℚ)^18 + (-331133681664)*(m:ℚ)^17 + (-2396118122496)*(m:ℚ)^16 + (-12089996181504)*(m:ℚ)^15 + (-45170402181120)*(m:ℚ)^14 + (-129508542554112)*(m:ℚ)^13 + (-291348258582528)*(m:ℚ)^12 + (-521333734053888)*(m:ℚ)^11 + (-747532339236864)*(m:ℚ)^10 + (-860923362030336)*(m:ℚ)^9 + (-794437996953600)*(m:ℚ)^8 + (-582963271929216)*(m:ℚ)^7 + (-335525377024512)*(m:ℚ)^6 + (-148109323373568)*(m:ℚ)^5 + (-48373417460736)*(m:ℚ)^4 + (-11004553040256)*(m:ℚ)^3 + (-1555425400320)*(m:ℚ)^2 + (-102745843200)*(m:ℚ)) * hr0 + ((42467328)*(m:ℚ)^19 + (1054605312)*(m:ℚ)^18 + (12276006912)*(m:ℚ)^17 + (89042780160)*(m:ℚ)^16 + (451239051264)*(m:ℚ)^15 + (1697667465216)*(m:ℚ)^14 + (4917797462016)*(m:ℚ)^13 + (11225614036992)*(m:ℚ)^12 + (20491840026624)*(m:ℚ)^11 + (30180357642240)*(m:ℚ)^10 + (36012629971200)*(m:ℚ)^9 + (34816955661312)*(m:ℚ)^8 + (27161531303040)*(m:ℚ)^7 + (16948802339328)*(m:ℚ)^6 + (8336190147072)*(m:ℚ)^5 + (3158052235776)*(m:ℚ)^4 + (888553079424)*(m:ℚ)^3 + (174744843264)*(m:ℚ)^2 + (21423813120)*(m:ℚ) + (1231718400)) * hr1
  exact (mul_eq_zero.mp hcl).resolve_left hP

theorem Rg (m:ℕ) : AA m * gq m + BB m * gq (m+1) + CC m * gq (m+2) = 0 := by
  have key := hGid m
  have hs1 : (-1:ℚ)^(m+1) = (-1)^m * (-1) := pow_succ (-1) m
  have hs2 : (-1:ℚ)^(m+2) = (-1)^m := by rw [show m+2 = m+1+1 from rfl, pow_succ, pow_succ]; ring
  simp only [gq]
  rw [hs1, hs2]
  linear_combination ((-1:ℚ)^m) * key

theorem CCne (m:ℕ) : CC m ≠ 0 := by
  have h1 : (0:ℚ) < (↑(2*m+1):ℚ) := by positivity
  have h2 : (0:ℚ) < (↑(2*m+2):ℚ) := by positivity
  have h3 : (0:ℚ) < (↑(2*m+3):ℚ) := by positivity
  have hc1 : cc1 (↑(2*m+1):ℚ) ≠ 0 := by
    have hcube : (0:ℚ) < 6*(↑(2*m+1):ℚ)^3+12*(↑(2*m+1))^2+5*(↑(2*m+1))+1 := by positivity
    have hpos := mul_pos (mul_pos (by norm_num : (0:ℚ)<6) h1) hcube
    have : cc1 (↑(2*m+1):ℚ) < 0 := by simp only [cc1]; nlinarith [hpos]
    linarith
  have hc2 : cc2 (↑(2*m+2):ℚ) ≠ 0 := by
    have hq : (0:ℚ) < 3*(↑(2*m+2):ℚ)^2-2*(↑(2*m+2))+1 := by nlinarith [sq_nonneg (3*(↑(2*m+2):ℚ)-1)]
    have hpos : (0:ℚ) < (↑(2*m+2):ℚ)^2*((↑(2*m+2):ℚ)+2)^2*(3*(↑(2*m+2):ℚ)^2-2*(↑(2*m+2))+1) :=
      mul_pos (mul_pos (by positivity) (by positivity)) hq
    have : cc2 (↑(2*m+2):ℚ) < 0 := by simp only [cc2]; nlinarith [hpos]
    linarith
  have hc3 : cc2 (↑(2*m+3):ℚ) ≠ 0 := by
    have hq : (0:ℚ) < 3*(↑(2*m+3):ℚ)^2-2*(↑(2*m+3))+1 := by nlinarith [sq_nonneg (3*(↑(2*m+3):ℚ)-1)]
    have hpos : (0:ℚ) < (↑(2*m+3):ℚ)^2*((↑(2*m+3):ℚ)+2)^2*(3*(↑(2*m+3):ℚ)^2-2*(↑(2*m+3))+1) :=
      mul_pos (mul_pos (by positivity) (by positivity)) hq
    have : cc2 (↑(2*m+3):ℚ) < 0 := by simp only [cc2]; nlinarith [hpos]
    linarith
  simp only [CC, neg_ne_zero]
  exact mul_ne_zero (mul_ne_zero hc1 hc2) hc3

theorem gq0 : gq 0 = 1 := by norm_num [gq, Gnat]
theorem gq1 : gq 1 = -8 := by norm_num [gq, Gnat, Nat.choose]

theorem closed_pair : ∀ m, aaq (2*m+1) = gq m ∧ aaq (2*(m+1)+1) = gq (m+1) := by
  intro m
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · show aaq 1 = gq 0; rw [aaq1, gq0]
    · show aaq 3 = gq 1; rw [aaq3, gq1]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have h2' : aaq (2*k+3) = gq (k+1) := by rw [show 2*k+3 = 2*(k+1)+1 from by ring]; exact h2
    refine ⟨?_, ?_⟩
    · rw [show 2*(k+1)+1 = 2*k+3 from by ring]; exact h2'
    · have hR := Rrec k
      have hG := Rg k
      have hCne := CCne k
      have e : CC k * aaq (2*k+5) = CC k * gq (k+2) := by
        rw [h1, h2'] at hR
        linear_combination hR - hG
      rw [show 2*(k+1+1)+1 = 2*k+5 from by ring]
      exact mul_left_cancel₀ hCne e

theorem closedform (m:ℕ) : aaq (2*m+1) = gq m := (closed_pair m).1

-- ===== from Cong =====

theorem prodrep (m : ℕ) :
    (aaq (2*m+1) : ℚ) = ∏ i ∈ Finset.range m, (1 - (2*(m:ℚ)+1)^2/((i:ℚ)+1)^2) := by
  have hm : (m.factorial:ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h2m1 : ((2*m+1).factorial:ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  -- denominator
  have hden : ∏ i ∈ Finset.range m, ((i:ℚ)+1)^2 = (m.factorial:ℚ)^2 := by
    have h1 : ∏ i ∈ Finset.range m, ((i:ℚ)+1) = (m.factorial:ℚ) := by
      rw [← Finset.prod_range_add_one_eq_factorial m, Nat.cast_prod]
      exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)
    rw [Finset.prod_pow, h1]
  -- ascending factorial product
  have hasc : ∏ i ∈ Finset.range m, ((i:ℚ)+2*(m:ℚ)+2) = ((2*m+2).ascFactorial m : ℚ) := by
    rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)
  -- descending factorial product
  have hdesc2 : ∏ i ∈ Finset.range m, (2*(m:ℚ)-(i:ℚ)) = ((2*m).descFactorial m:ℚ) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi; rw [Finset.mem_range] at hi
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hdesc : ∏ i ∈ Finset.range m, ((i:ℚ)-2*(m:ℚ)) = (-1)^m * ((2*m).descFactorial m:ℚ) := by
    rw [← hdesc2]
    rw [show ((-1:ℚ))^m = ∏ _i ∈ Finset.range m, (-1:ℚ) from by rw [Finset.prod_const, Finset.card_range], ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => by ring)
  -- numerator
  have hnum : ∏ i ∈ Finset.range m, (((i:ℚ)+1)^2-(2*(m:ℚ)+1)^2)
      = (-1)^m * ((2*m).descFactorial m:ℚ) * ((2*m+2).ascFactorial m:ℚ) := by
    have step1 : ∏ i ∈ Finset.range m, (((i:ℚ)+1)^2-(2*(m:ℚ)+1)^2)
        = (∏ i ∈ Finset.range m, ((i:ℚ)-2*(m:ℚ))) * (∏ i ∈ Finset.range m, ((i:ℚ)+2*(m:ℚ)+2)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => by ring)
    rw [step1, hdesc, hasc]
  -- factorial relations
  have hfd : ((2*m).descFactorial m:ℚ) = ((2*m).factorial:ℚ)/(m.factorial:ℚ) := by
    rw [eq_div_iff hm]
    have := Nat.factorial_mul_descFactorial (show m ≤ 2*m by omega)
    rw [show 2*m-m = m from by omega] at this
    have hc := congrArg (Nat.cast : ℕ → ℚ) this; push_cast at hc ⊢; linarith [hc]
  have hfa : ((2*m+2).ascFactorial m:ℚ) = ((3*m+1).factorial:ℚ)/((2*m+1).factorial:ℚ) := by
    rw [eq_div_iff h2m1]
    have := Nat.factorial_mul_ascFactorial (2*m+1) m
    rw [show 2*m+1+1 = 2*m+2 from by omega, show 2*m+1+m = 3*m+1 from by omega] at this
    have hc := congrArg (Nat.cast : ℕ → ℚ) this; push_cast at hc ⊢; linarith [hc]
  -- RHS as ratio
  have hterm : ∀ i ∈ Finset.range m, (1 - (2*(m:ℚ)+1)^2/((i:ℚ)+1)^2)
      = (((i:ℚ)+1)^2-(2*(m:ℚ)+1)^2)/((i:ℚ)+1)^2 := by
    intro i _
    have : ((i:ℚ)+1)^2 ≠ 0 := by positivity
    field_simp
  rw [Finset.prod_congr rfl hterm, Finset.prod_div_distrib, hnum, hden, hfd, hfa, closedform]
  simp only [gq, Gnat, Nat.cast_mul]
  rw [Nat.cast_choose ℚ (show m ≤ 2*m by omega), Nat.cast_choose ℚ (show m ≤ 3*m+1 by omega)]
  rw [show 2*m-m = m from by omega, show 3*m+1-m = 2*m+1 from by omega]
  push_cast
  field_simp

-- ===== from Split =====

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

-- ===== from Test1 =====


/-- For an odd prime power modulus `N = p^k` with `p ≥ 5`, the sum of squares of all
units in `ZMod N` is zero.  Proof: multiplication by the unit `2` permutes the units,
so `4 * S = S`, hence `3 * S = 0`, and `3` is a unit. -/
theorem unitsq_sum_zero (N : ℕ) [NeZero N] (hN2 : IsUnit (2 : ZMod N)) (hN3 : IsUnit (3 : ZMod N)) :
    ∑ u : (ZMod N)ˣ, ((u : ZMod N))^2 = 0 := by
  set S := ∑ u : (ZMod N)ˣ, ((u : ZMod N))^2 with hS
  -- the unit 2
  obtain ⟨c, hc⟩ := hN2
  -- reindex u ↦ c * u
  have hbij : ∑ u : (ZMod N)ˣ, (((c * u : (ZMod N)ˣ) : ZMod N))^2 = S := by
    rw [hS]
    exact Equiv.sum_comp (Equiv.mulLeft c) (fun u => ((u : ZMod N))^2)
  have h4 : (4 : ZMod N) * S = S := by
    have : ∑ u : (ZMod N)ˣ, (((c * u : (ZMod N)ˣ) : ZMod N))^2
         = ∑ u : (ZMod N)ˣ, (2:ZMod N)^2 * ((u : ZMod N))^2 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Units.val_mul, hc, mul_pow]
    rw [this, ← Finset.mul_sum] at hbij
    have : (2:ZMod N)^2 = 4 := by norm_num
    rw [this] at hbij
    rw [← hS] at hbij
    exact hbij
  -- 3 * S = 0
  have h3 : (3 : ZMod N) * S = 0 := by
    have : (4 : ZMod N) * S - S = 0 := by rw [h4]; ring
    have e : (4 : ZMod N) * S - S = 3 * S := by ring
    rw [e] at this; exact this
  -- cancel 3
  obtain ⟨d, hd⟩ := hN3
  have key : ((d⁻¹ : (ZMod N)ˣ) : ZMod N) * ((3 : ZMod N) * S) = ((d⁻¹ : (ZMod N)ˣ) : ZMod N) * 0 := by
    rw [h3]
  rw [mul_zero, ← mul_assoc] at key
  rw [show ((d⁻¹ : (ZMod N)ˣ) : ZMod N) * 3 = 1 by
    rw [← hd, ← Units.val_mul]; simp] at key
  rw [one_mul] at key
  exact key

-- ===== from Cong2 =====


set_option maxHeartbeats 1000000 in
/-- Key divisibility: `p^k` divides the elementary symmetric "T0" sum. -/
theorem pk_dvd_T0 (p k M : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) (hM : 2*M+1 = p^k) :
    ((p^k : ℕ):ℤ) ∣ ∑ i ∈ (Finset.range M).filter (fun i => ¬ p ∣ (i+1)),
        ∏ j ∈ ((Finset.range M).filter (fun i => ¬ p ∣ (i+1))).erase i, ((j:ℤ)+1)^2 := by
  haveI : NeZero (p^k) := ⟨(pow_pos (by omega : 0 < p) k).ne'⟩
  have hpk1 : 1 < p^k := by
    have := Nat.le_self_pow (show k ≠ 0 by omega) p; omega
  set VF := (Finset.range M).filter (fun i => ¬ p ∣ (i+1)) with hVF
  set Vfull := (Finset.range (2*M)).filter (fun i => ¬ p ∣ (i+1)) with hVfull
  -- units 2 and 3
  have h2unit : IsUnit (2:ZMod (p^k)) := by
    rw [show (2:ZMod (p^k)) = ((2:ℕ):ZMod (p^k)) from by push_cast; ring, ZMod.isUnit_iff_coprime]
    exact ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_right k
  -- membership helpers
  have hvf : ∀ a, a ∈ VF → a < M ∧ ¬ p ∣ (a+1) := by
    intro a ha; rw [hVF, Finset.mem_filter, Finset.mem_range] at ha; exact ha
  have hsd : ∀ a, a ∈ Vfull \ VF → M ≤ a ∧ a < 2*M ∧ ¬ p ∣ (a+1) := by
    intro a ha
    rw [Finset.mem_sdiff, hVfull, hVF, Finset.mem_filter, Finset.mem_range,
        Finset.mem_filter, Finset.mem_range] at ha
    refine ⟨?_, ha.1.1, ha.1.2⟩
    by_contra h; push_neg at h
    exact ha.2 ⟨h, ha.1.2⟩
  have hcopV : ∀ a ∈ Vfull, Nat.Coprime (a+1) (p^k) := by
    intro a ha
    rw [hVfull, Finset.mem_filter] at ha
    exact (((hp.coprime_iff_not_dvd.mpr ha.2)).symm).pow_right k
  have hupos : ∀ b : (ZMod (p^k))ˣ, 1 ≤ (b:ZMod (p^k)).val := by
    intro b
    rcases Nat.eq_zero_or_pos (b:ZMod (p^k)).val with h0|h0
    · exfalso
      have hcp := ZMod.val_coe_unit_coprime b
      rw [h0, Nat.coprime_zero_left] at hcp
      omega
    · exact h0
  have hundvd : ∀ b : (ZMod (p^k))ˣ, ¬ p ∣ (b:ZMod (p^k)).val := by
    intro b
    have hcp := ZMod.val_coe_unit_coprime b
    have hpdvd : p ∣ p^k := dvd_pow_self p (by omega : k ≠ 0)
    exact (hp.coprime_iff_not_dvd).mp (Nat.Coprime.coprime_dvd_right hpdvd hcp).symm
  -- negation cast helper
  have hneg : ∀ a, a ≤ 2*M → ((2*M - a : ℕ):ZMod (p^k)) = -((a:ZMod (p^k))+1) := by
    intro a hle
    have hcast : ((2*M-a:ℕ):ZMod (p^k)) = ((2*M:ℕ):ZMod (p^k)) - (a:ZMod (p^k)) := by
      rw [Nat.cast_sub hle]
    rw [hcast]
    have h2 : ((2*M:ℕ):ZMod (p^k)) = -1 := by
      have hz : ((2*M+1:ℕ):ZMod (p^k)) = 0 := by rw [hM, ZMod.natCast_self]
      push_cast at hz ⊢
      linear_combination hz
    rw [h2]; ring
  -- reduce to ZMod
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  -- per-term factoring
  have key : (∑ i ∈ VF, ∏ j ∈ VF.erase i, ((j:ZMod (p^k))+1)^2)
           = (∏ j ∈ VF, ((j:ZMod (p^k))+1)^2) * ∑ i ∈ VF, Ring.inverse (((i:ZMod (p^k))+1)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hunit : IsUnit (((i:ZMod (p^k))+1)^2) := by
      have h1 : IsUnit ((i:ZMod (p^k))+1) := by
        rw [show ((i:ZMod (p^k))+1) = ((i+1:ℕ):ZMod (p^k)) from by push_cast; ring, ZMod.isUnit_iff_coprime]
        exact (((hp.coprime_iff_not_dvd.mpr (hvf i hi).2)).symm).pow_right k
      exact h1.pow 2
    have hW : (∏ j ∈ VF, ((j:ZMod (p^k))+1)^2)
            = (((i:ZMod (p^k))+1)^2) * ∏ j ∈ VF.erase i, ((j:ZMod (p^k))+1)^2 :=
      (Finset.mul_prod_erase VF (fun j => ((j:ZMod (p^k))+1)^2) hi).symm
    rw [hW]
    rw [show (((i:ZMod (p^k))+1)^2 * ∏ j ∈ VF.erase i, ((j:ZMod (p^k))+1)^2) * Ring.inverse (((i:ZMod (p^k))+1)^2)
          = (∏ j ∈ VF.erase i, ((j:ZMod (p^k))+1)^2) * (((i:ZMod (p^k))+1)^2 * Ring.inverse (((i:ZMod (p^k))+1)^2)) from by ring]
    rw [Ring.mul_inverse_cancel _ hunit, mul_one]
  rw [key]
  -- main sum is zero
  have hsum0 : (∑ i ∈ VF, Ring.inverse (((i:ZMod (p^k))+1)^2)) = 0 := by
    -- full sum over Vfull equals the units sum, which is 0
    have hb : (∑ i ∈ Vfull, Ring.inverse (((i:ZMod (p^k))+1)^2))
            = ∑ w : (ZMod (p^k))ˣ, Ring.inverse (((w:ZMod (p^k)))^2) := by
      apply Finset.sum_bij' (fun a ha => ZMod.unitOfCoprime (a+1) (hcopV a ha))
        (fun b _ => (b:ZMod (p^k)).val - 1)
        (fun a ha => Finset.mem_univ _)
        ?_ ?_ ?_ ?_
      · -- hj
        intro b _
        simp only [hVfull, Finset.mem_filter, Finset.mem_range]
        have hbv : (b:ZMod (p^k)).val < p^k := ZMod.val_lt _
        refine ⟨by omega, ?_⟩
        rw [Nat.sub_add_cancel (hupos b)]; exact hundvd b
      · -- left_inv
        intro a ha
        have haM : a < 2*M := by rw [hVfull, Finset.mem_filter, Finset.mem_range] at ha; exact ha.1
        simp only [ZMod.coe_unitOfCoprime]
        rw [ZMod.val_natCast_of_lt (by omega : a+1 < p^k)]
        omega
      · -- right_inv
        intro b _
        apply Units.ext
        simp only [ZMod.coe_unitOfCoprime]
        rw [Nat.sub_add_cancel (hupos b)]
        exact ZMod.natCast_zmod_val _
      · -- summand correspondence
        intro a ha
        dsimp only
        congr 1
        rw [ZMod.coe_unitOfCoprime]
        push_cast; ring
    -- units sum is 0
    have hconv : ∀ w : (ZMod (p^k))ˣ, Ring.inverse (((w:ZMod (p^k)))^2) = ((↑(w⁻¹) : ZMod (p^k)))^2 := by
      intro w
      rw [show ((w:ZMod (p^k)))^2 = ((w^2 : (ZMod (p^k))ˣ):ZMod (p^k)) from (Units.val_pow_eq_pow_val w 2).symm,
          Ring.inverse_unit, show ((w^2:(ZMod (p^k))ˣ))⁻¹ = (w⁻¹)^2 from (inv_pow w 2).symm,
          Units.val_pow_eq_pow_val]
    have hreindex : (∑ w : (ZMod (p^k))ˣ, ((↑(w⁻¹) : ZMod (p^k)))^2)
                  = ∑ w : (ZMod (p^k))ˣ, ((↑w : ZMod (p^k)))^2 :=
      Equiv.sum_comp (Equiv.inv (ZMod (p^k))ˣ) (fun w => ((↑w:ZMod (p^k)))^2)
    have hfull0 : (∑ i ∈ Vfull, Ring.inverse (((i:ZMod (p^k))+1)^2)) = 0 := by
      rw [hb]
      simp_rw [hconv]
      rw [hreindex]
      exact unitsq_sum_zero (p^k) h2unit
        (by rw [show (3:ZMod (p^k)) = ((3:ℕ):ZMod (p^k)) from by push_cast; ring, ZMod.isUnit_iff_coprime]
            exact ((Nat.coprime_primes Nat.prime_three hp).mpr (by omega)).pow_right k)
    -- doubling
    have hVFsub : VF ⊆ Vfull := by
      intro x hx
      rw [hVF, Finset.mem_filter, Finset.mem_range] at hx
      rw [hVfull, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hx.2⟩
    have hbij : (∑ i ∈ Vfull \ VF, Ring.inverse (((i:ZMod (p^k))+1)^2))
              = ∑ i ∈ VF, Ring.inverse (((i:ZMod (p^k))+1)^2) := by
      apply Finset.sum_bij' (fun a _ => 2*M-1-a) (fun a _ => 2*M-1-a) ?_ ?_ ?_ ?_ ?_
      · -- maps Vfull\VF into VF
        intro a ha
        obtain ⟨h1, h2, h3⟩ := hsd a ha
        simp only [hVF, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        intro hd
        have hpk : p ∣ (2*M+1) := by rw [hM]; exact dvd_pow_self p (by omega : k ≠ 0)
        have : p ∣ (a+1) := by
          have := Nat.dvd_sub hpk hd
          rwa [show 2*M+1 - (2*M-1-a+1) = a+1 from by omega] at this
        exact h3 this
      · -- maps VF into Vfull\VF
        intro a ha
        obtain ⟨h1, h2⟩ := hvf a ha
        have hnd : ¬ p ∣ (2*M-1-a+1) := by
          intro hd
          have hpk : p ∣ (2*M+1) := by rw [hM]; exact dvd_pow_self p (by omega : k ≠ 0)
          have : p ∣ (a+1) := by
            have := Nat.dvd_sub hpk hd
            rwa [show 2*M+1 - (2*M-1-a+1) = a+1 from by omega] at this
          exact h2 this
        simp only [Finset.mem_sdiff, hVfull, hVF, Finset.mem_filter, Finset.mem_range]
        refine ⟨⟨by omega, hnd⟩, ?_⟩
        rintro ⟨hlt, _⟩; omega
      · intro a ha; obtain ⟨h1, h2, _⟩ := hsd a ha; dsimp only; omega
      · intro a ha; obtain ⟨h1, _⟩ := hvf a ha; dsimp only; omega
      · -- summand correspondence
        intro a ha
        obtain ⟨h1, h2, _⟩ := hsd a ha
        dsimp only
        congr 1
        rw [show ((2*M-1-a:ℕ):ZMod (p^k)) + 1 = ((2*M-a:ℕ):ZMod (p^k)) from by
              rw [← Nat.cast_add_one]; congr 1; omega,
            hneg a (by omega)]
        ring
    have hsplit : (∑ i ∈ Vfull \ VF, Ring.inverse (((i:ZMod (p^k))+1)^2))
                + (∑ i ∈ VF, Ring.inverse (((i:ZMod (p^k))+1)^2))
                = ∑ i ∈ Vfull, Ring.inverse (((i:ZMod (p^k))+1)^2) := Finset.sum_sdiff hVFsub
    -- hsplit : ∑_{Vfull\VF} + ∑_VF = ∑_Vfull
    have hdbl : (∑ i ∈ Vfull, Ring.inverse (((i:ZMod (p^k))+1)^2))
              = 2 * ∑ i ∈ VF, Ring.inverse (((i:ZMod (p^k))+1)^2) := by
      rw [← hsplit, hbij]; ring
    have hS : (2:ZMod (p^k)) * (∑ i ∈ VF, Ring.inverse (((i:ZMod (p^k))+1)^2)) = 0 := by
      rw [← hdbl]; exact hfull0
    exact (h2unit.mul_right_eq_zero).mp hS
  rw [hsum0, mul_zero]

/-- `u` divides `∏(xᵢ - u) - ∏xᵢ`. -/
theorem divu_lemma (s : Finset ℕ) (x : ℕ → ℤ) (u : ℤ) :
    u ∣ ((∏ i ∈ s, (x i - u)) - ∏ i ∈ s, x i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    rw [show (x a - u) * ∏ i ∈ s, (x i - u) - x a * ∏ i ∈ s, x i
          = x a * ((∏ i ∈ s, (x i - u)) - ∏ i ∈ s, x i) - u * ∏ i ∈ s, (x i - u) from by ring]
    exact dvd_sub (ih.mul_left (x a)) (dvd_mul_right u _)

/-- `u^2` divides `∏(xᵢ - u) - ∏xᵢ + u·∑ᵢ∏_{j≠i}xⱼ`. -/
theorem expand_lemma (s : Finset ℕ) (x : ℕ → ℤ) (u : ℤ) :
    u^2 ∣ ((∏ i ∈ s, (x i - u)) - (∏ i ∈ s, x i) + u * ∑ i ∈ s, ∏ j ∈ s.erase i, x j) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hRa : ∏ j ∈ (insert a s).erase a, x j = ∏ j ∈ s, x j := by rw [Finset.erase_insert ha]
    have hRs : ∑ i ∈ s, ∏ j ∈ (insert a s).erase i, x j
             = x a * ∑ i ∈ s, ∏ j ∈ s.erase i, x j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hai : a ≠ i := by rintro rfl; exact ha hi
      rw [Finset.erase_insert_of_ne hai,
          Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    rw [hRa, hRs]
    rw [show (x a - u) * ∏ i ∈ s, (x i - u) - x a * ∏ i ∈ s, x i
            + u * ((∏ i ∈ s, x i) + x a * ∑ i ∈ s, ∏ j ∈ s.erase i, x j)
          = x a * ((∏ i ∈ s, (x i - u)) - (∏ i ∈ s, x i) + u * ∑ i ∈ s, ∏ j ∈ s.erase i, x j)
            - u * ((∏ i ∈ s, (x i - u)) - ∏ i ∈ s, x i) from by ring]
    refine dvd_sub (ih.mul_left (x a)) ?_
    rw [pow_two]
    exact mul_dvd_mul_left u (divu_lemma s x u)

/-- The closed-form integer value at odd arguments. -/
def Aint (m : ℕ) : ℤ := (-1:ℤ)^m * (Gnat m : ℤ)

theorem Aint_cast (m : ℕ) : ((Aint m : ℤ):ℚ) = gq m := by
  simp only [Aint, gq]; push_cast; ring

/-- Core divisibility: `p^(3k)` divides `Aint M - Aint M'`. -/
theorem core_dvd (p k M M' d : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k)
    (hMk : 2*M+1 = p^k) (hM'k : 2*M'+1 = p^(k-1)) (hd : 2*d+1 = p) (hMM' : M = p*M'+d) :
    ((p:ℤ)^(3*k)) ∣ (Aint M - Aint M') := by
  classical
  set VF := (Finset.range M).filter (fun i => ¬ p ∣ (i+1)) with hVF
  -- ℚ product-split
  have hMc : (2*(M:ℚ)+1) = (p:ℚ)^k := by
    have h := congrArg (Nat.cast : ℕ → ℚ) hMk
    push_cast at h; linarith
  have hps : aaq (2*M+1) = (∏ i ∈ VF, (1 - (2*(M:ℚ)+1)^2/((i:ℚ)+1)^2)) * aaq (2*M'+1) := by
    rw [prodrep M,
        ← Finset.prod_filter_mul_prod_filter_not (Finset.range M) (fun i => p ∣ (i+1))
            (fun i => (1 - (2*(M:ℚ)+1)^2/((i:ℚ)+1)^2)),
        hfilterprod p M M' d (by omega) hd hMM', ← prodrep M']
    ring
  -- rewrite each VF factor; introduce p^(2k)
  have hsq : (2*(M:ℚ)+1)^2 = (p:ℚ)^(2*k) := by rw [hMc, ← pow_mul]; congr 1; ring
  have hterm : ∀ i ∈ VF, (1 - (2*(M:ℚ)+1)^2/((i:ℚ)+1)^2)
      = (((i:ℚ)+1)^2 - (p:ℚ)^(2*k))/((i:ℚ)+1)^2 := by
    intro i _
    have hne : ((i:ℚ)+1)^2 ≠ 0 := by positivity
    rw [hsq]; field_simp
  -- denominators
  have hDcast : ((∏ i ∈ VF, ((i:ℤ)+1)^2 : ℤ):ℚ) = ∏ i ∈ VF, ((i:ℚ)+1)^2 := by
    rw [Int.cast_prod]; exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)
  have hNcast : ((∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k)) : ℤ):ℚ)
              = ∏ i ∈ VF, (((i:ℚ)+1)^2 - (p:ℚ)^(2*k)) := by
    rw [Int.cast_prod]; exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)
  have hDne : (∏ i ∈ VF, ((i:ℚ)+1)^2) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr; intro i _; positivity
  -- the cleared-denominator ℚ identity
  have hQ : (∏ i ∈ VF, ((i:ℚ)+1)^2) * gq M
          = (∏ i ∈ VF, (((i:ℚ)+1)^2 - (p:ℚ)^(2*k))) * gq M' := by
    have hh : gq M = (∏ i ∈ VF, (((i:ℚ)+1)^2 - (p:ℚ)^(2*k)))
                    / (∏ i ∈ VF, ((i:ℚ)+1)^2) * gq M' := by
      rw [← closedform M, ← closedform M', hps]
      rw [Finset.prod_congr rfl hterm, Finset.prod_div_distrib]
    rw [hh]; field_simp
  -- cast to ℤ : KEYI
  have hKEYI : (∏ i ∈ VF, ((i:ℤ)+1)^2) * Aint M
             = (∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k))) * Aint M' := by
    have : ((∏ i ∈ VF, ((i:ℤ)+1)^2 : ℤ):ℚ) * (Aint M : ℚ)
         = ((∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k)) : ℤ):ℚ) * (Aint M' : ℚ) := by
      rw [hDcast, hNcast, Aint_cast, Aint_cast]; exact hQ
    exact_mod_cast this
  -- p^k ∣ T0z
  have hT0 : (p:ℤ)^k ∣ ∑ i ∈ VF, ∏ j ∈ VF.erase i, ((j:ℤ)+1)^2 := by
    have hpk := pk_dvd_T0 p k M hp hp5 hk hMk
    rw [← hVF] at hpk
    have hcast : ((p^k:ℕ):ℤ) = (p:ℤ)^k := by push_cast; ring
    rwa [hcast] at hpk
  -- p^(3k) ∣ Nz - Dz
  have hexp : ((p:ℤ)^(2*k))^2 ∣ ((∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k)))
        - (∏ i ∈ VF, ((i:ℤ)+1)^2) + (p:ℤ)^(2*k) * ∑ i ∈ VF, ∏ j ∈ VF.erase i, ((j:ℤ)+1)^2) :=
    expand_lemma VF (fun i => ((i:ℤ)+1)^2) ((p:ℤ)^(2*k))
  have hNminusD : ((p:ℤ)^(3*k)) ∣ ((∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k))) - (∏ i ∈ VF, ((i:ℤ)+1)^2)) := by
    have h1 : ((p:ℤ)^(3*k)) ∣ ((∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k))) - (∏ i ∈ VF, ((i:ℤ)+1)^2)
                + (p:ℤ)^(2*k) * ∑ i ∈ VF, ∏ j ∈ VF.erase i, ((j:ℤ)+1)^2) := by
      refine dvd_trans (pow_dvd_pow (p:ℤ) (by omega : 3*k ≤ 4*k)) ?_
      have he : ((p:ℤ)^(2*k))^2 = (p:ℤ)^(4*k) := by rw [← pow_mul]; ring_nf
      rw [← he]; exact hexp
    have h2 : ((p:ℤ)^(3*k)) ∣ ((p:ℤ)^(2*k) * ∑ i ∈ VF, ∏ j ∈ VF.erase i, ((j:ℤ)+1)^2) := by
      have hmm : (p:ℤ)^(2*k) * (p:ℤ)^k ∣ (p:ℤ)^(2*k) * ∑ i ∈ VF, ∏ j ∈ VF.erase i, ((j:ℤ)+1)^2 :=
        mul_dvd_mul_left _ hT0
      rwa [← pow_add, show 2*k+k = 3*k from by ring] at hmm
    have h3 := dvd_sub h1 h2
    rwa [show (∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k))) - (∏ i ∈ VF, ((i:ℤ)+1)^2)
              + (p:ℤ)^(2*k) * (∑ i ∈ VF, ∏ j ∈ VF.erase i, ((j:ℤ)+1)^2)
              - (p:ℤ)^(2*k) * (∑ i ∈ VF, ∏ j ∈ VF.erase i, ((j:ℤ)+1)^2)
            = (∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k))) - (∏ i ∈ VF, ((i:ℤ)+1)^2) from by ring] at h3
  -- p^(3k) ∣ Dz * (Aint M - Aint M')
  have hDdiff : ((p:ℤ)^(3*k)) ∣ (∏ i ∈ VF, ((i:ℤ)+1)^2) * (Aint M - Aint M') := by
    have heq : (∏ i ∈ VF, ((i:ℤ)+1)^2) * (Aint M - Aint M')
             = ((∏ i ∈ VF, (((i:ℤ)+1)^2 - (p:ℤ)^(2*k))) - (∏ i ∈ VF, ((i:ℤ)+1)^2)) * Aint M' := by
      linear_combination hKEYI
    rw [heq]; exact hNminusD.mul_right _
  -- coprimality and cancellation
  have hcop : IsCoprime ((p:ℤ)^(3*k)) (∏ i ∈ VF, ((i:ℤ)+1)^2) := by
    apply IsCoprime.pow_left
    apply IsCoprime.prod_right
    intro i hi
    apply IsCoprime.pow_right
    rw [hVF, Finset.mem_filter] at hi
    rw [show ((i:ℤ)+1) = ((i+1:ℕ):ℤ) from by push_cast; ring]
    exact Nat.isCoprime_iff_coprime.mpr (hp.coprime_iff_not_dvd.mpr hi.2)
  exact hcop.dvd_of_dvd_mul_left hDdiff

theorem hAnat (n : ℕ) (hn : 2 ≤ n) : (A361711 n : ℚ) = aaq n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  have hA : A361711 (j+2) = (Finset.range (j+1)).sum
      (fun k : ℕ => (-1:ℤ)^k * (((j+2).choose k)*((j+2).choose k)*(j.choose k) : ℕ)) := rfl
  rw [hA]; push_cast
  rw [aaq]
  rw [← Finset.sum_subset (s₁ := Finset.range (j+1)) (s₂ := Finset.range (j+2+1))
        (by intro x hx; rw [Finset.mem_range] at *; omega)
        (fun x _ hx => Fq_zero (j+2) x (by simp only [Finset.mem_range, not_lt] at hx; omega))]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Fq]
  rw [show (j+2)-2 = j from rfl]
  push_cast; ring

theorem hA_odd (m : ℕ) : A361711 (2*m+1) = Aint m := by
  rcases Nat.eq_zero_or_pos m with h|h
  · subst h; rfl
  · have hge : 2 ≤ 2*m+1 := by omega
    have h1 := hAnat (2*m+1) hge
    have hcast : ((A361711 (2*m+1):ℤ):ℚ) = ((Aint m:ℤ):ℚ) := by
      rw [h1, closedform m, Aint_cast m]
    exact_mod_cast hcast

theorem A361711_conjecture (p : ℕ) (hp : Nat.Prime p) (h_geq_5 : 5 ≤ p) (k : ℕ) (hk : k > 0) :
    A361711 (p ^ k) ≡ A361711 (p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℕ)] := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  set M := (p^k - 1)/2 with hMdef
  have hMk : 2*M+1 = p^k := by
    have : (p^k) % 2 = 1 := Nat.odd_iff.mp (hodd.pow)
    rw [hMdef]; omega
  set M' := (p^(k-1) - 1)/2 with hM'def
  have hM'k : 2*M'+1 = p^(k-1) := by
    have : (p^(k-1)) % 2 = 1 := Nat.odd_iff.mp (hodd.pow)
    rw [hM'def]; omega
  set d := (p-1)/2 with hddef
  have hd : 2*d+1 = p := by
    have : p % 2 = 1 := Nat.odd_iff.mp hodd
    rw [hddef]; omega
  have e1 : p * (2*M'+1) = p^k := by rw [hM'k, ← pow_succ']; congr 1; omega
  have hMM' : M = p*M' + d := by
    have e2 : 2*(p*M'+d)+1 = 2*M+1 := by rw [hMk, ← e1, ← hd]; ring
    omega
  have hcore := core_dvd p k M M' d hp h_geq_5 (by omega) hMk hM'k hd hMM'
  have hAk : A361711 (p^k) = Aint M := by rw [← hMk]; exact hA_odd M
  have hAk1 : A361711 (p^(k-1)) = Aint M' := by rw [← hM'k]; exact hA_odd M'
  rw [hAk, hAk1, Int.modEq_iff_dvd]
  have hcast : ((p^(3*k):ℕ):ℤ) = (p:ℤ)^(3*k) := by push_cast; ring
  rw [hcast, show Aint M' - Aint M = -(Aint M - Aint M') from by ring]
  exact dvd_neg.mpr hcore
