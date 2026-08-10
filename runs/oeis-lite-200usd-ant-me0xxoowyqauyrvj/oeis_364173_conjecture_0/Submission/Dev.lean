import FormalConjectures.Util.ProblemImports
open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

lemma halfGamma (m : ℕ) :
    Real.Gamma ((m:ℝ) + 3/2)
      = ((2*m+1).factorial : ℝ) * (2:ℝ)^(-(2*(m:ℝ)+1)) * Real.sqrt π / (m.factorial : ℝ) := by
  have hkey := Real.Gamma_mul_Gamma_add_half ((m:ℝ) + 1)
  have e1 : (m:ℝ) + 1 + 1/2 = (m:ℝ) + 3/2 := by ring
  have e3 : 2 * ((m:ℝ) + 1) = (((2*m+1 : ℕ)) : ℝ) + 1 := by push_cast; ring
  rw [e1, e3, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial] at hkey
  have hfac : ((m.factorial : ℝ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have e4 : (1:ℝ) - (((2*m+1 : ℕ):ℝ)+1) = -(2*(m:ℝ)+1) := by push_cast; ring
  rw [e4] at hkey
  rw [eq_div_iff hfac, mul_comm]
  exact hkey

lemma halfGamma' (m : ℕ) :
    Real.Gamma ((m:ℝ) + 3/2)
      = ((2*m+1).factorial : ℝ) * Real.sqrt π / ((2^(2*m+1):ℝ) * (m.factorial : ℝ)) := by
  rw [halfGamma]
  have h2 : (2:ℝ)^(-(2*(m:ℝ)+1)) = ((2^(2*m+1):ℝ))⁻¹ := by
    rw [show -(2*(m:ℝ)+1) = -(((2*m+1:ℕ)):ℝ) by push_cast; ring,
        Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [h2]
  field_simp

lemma sqrtpi_ne : Real.sqrt π ≠ 0 := by
  have : (0:ℝ) < π := Real.pi_pos
  positivity

example (j : ℕ) :
    a (2*j+1) = (2:ℝ)^(12*j+6) * ((4*j+2).factorial : ℝ) * ((9*j+4).factorial : ℝ) /
      (((3*j+1).factorial : ℝ) * ((8*j+4).factorial : ℝ) * ((2*j+1).factorial : ℝ)) := by
  unfold a
  simp only
  set nr : ℝ := ((2*j+1 : ℕ) : ℝ) with hnr
  have g1 : (9:ℝ) * nr + 1 = ((18*j+9 : ℕ):ℝ) + 1 := by rw [hnr]; push_cast; ring
  have g2 : (2:ℝ) * nr + 1 = ((4*j+2 : ℕ):ℝ) + 1 := by rw [hnr]; push_cast; ring
  have g3 : (3/2:ℝ) * nr + 1 = ((3*j+1 : ℕ):ℝ) + 3/2 := by rw [hnr]; push_cast; ring
  have g4 : (9/2:ℝ) * nr + 1 = ((9*j+4 : ℕ):ℝ) + 3/2 := by rw [hnr]; push_cast; ring
  have g5 : (4:ℝ) * nr + 1 = ((8*j+4 : ℕ):ℝ) + 1 := by rw [hnr]; push_cast; ring
  have g6 : (3:ℝ) * nr + 1 = ((6*j+3 : ℕ):ℝ) + 1 := by rw [hnr]; push_cast; ring
  have g7 : nr + 1 = ((2*j+1 : ℕ):ℝ) + 1 := by rw [hnr]
  rw [g1, g2, g3, g4, g5, g6, g7, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
    Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
    halfGamma', halfGamma']
  rw [show 2*(3*j+1)+1 = 6*j+3 from by ring, show 2*(9*j+4)+1 = 18*j+9 from by ring]
  have hpow : (2:ℝ)^(18*j+9) = (2:ℝ)^(12*j+6) * (2:ℝ)^(6*j+3) := by
    rw [← pow_add]; ring_nf
  have hf1 : ((18*j+9).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hf2 : ((6*j+3).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hf3 : ((3*j+1).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hf4 : ((9*j+4).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hf5 : ((8*j+4).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hf6 : ((2*j+1).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hsp := sqrtpi_ne
  rw [hpow]
  field_simp

-- ============ REDUCTION SCAFFOLDING ============
section Reduction
variable (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ))))

noncomputable def z (m : ℕ) : ℤ := Classical.choose (h_int m)

lemma z_spec (m : ℕ) : ((z h_int m : ℝ)) = a m := Classical.choose_spec (h_int m)

-- The step congruence (THE HARD CORE), stated; proof deferred.
lemma step (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (L t : ℕ)
    (hLpos : 0 < L) (hdvd : p ^ t ∣ L) :
    (p : ℤ) ^ (3 + 3 * t) ∣ (z h_int (L * p) - z h_int L) := by
  sorry

theorem main (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (n r : ℕ) (hn : n > 0) (hr : r > 0) :
    (z h_int (n * p ^ r)) ≡ (z h_int (n * p ^ (r - 1))) [ZMOD ((p : ℤ) ^ (3 * r))] := by
  set L := n * p ^ (r - 1) with hL
  have hLpos : 0 < L := by positivity
  have hdvd : p ^ (r - 1) ∣ L := Dvd.intro_left n rfl
  have hstep := step h_int p hp h5 L (r - 1) hLpos hdvd
  have hLp : L * p = n * p ^ r := by
    rw [hL]; rw [mul_assoc, ← pow_succ]
    congr 2
    omega
  rw [hLp] at hstep
  -- now hstep : p^(3 + 3*(r-1)) ∣ z(n*p^r) - z L
  have hexp : 3 * r ≤ 3 + 3 * (r - 1) := by omega
  have : (p : ℤ) ^ (3 * r) ∣ (z h_int (n * p ^ r) - z h_int L) := by
    exact dvd_trans (pow_dvd_pow _ hexp) hstep
  rw [Int.modEq_iff_dvd]
  exact dvd_sub_comm.mp this

end Reduction
