import Submission.Closed
open Finset BigOperators Nat

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
