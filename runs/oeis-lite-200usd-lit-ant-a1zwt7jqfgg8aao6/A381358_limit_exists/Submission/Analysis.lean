import FormalConjectures.Util.ProblemImports
open Filter Topology

/-!
PART 2 (analysis): given the structural recurrences for L, r, q, a as hypotheses,
prove a(n)^(1/n) → λ.
-/

namespace A381358dev

-- The potential function.
noncomputable def Phi (lam : ℝ) (L r q : ℕ → ℝ) (n : ℕ) : ℝ :=
  L n + r n / (lam - 1) + q n / (lam - 1)^2
    + (lam - 1) * L (n-1) + lam * (lam - 1) * L (n-2)
    + lam^2 * (lam - 1) * L (n-3) + lam^3 * (lam - 1) * L (n-4)

section
variable {lam : ℝ} {a L r q : ℕ → ℝ} {n0 : ℕ}

theorem Phi_step
    (hlam1 : (1:ℝ) < lam) (hlam_eq : lam^4 * (lam-1)^3 = 1)
    (HR1 : ∀ n, n0 ≤ n → L (n+1) = L n + r n)
    (HR2 : ∀ n, n0 ≤ n → r (n+1) = r n + q n - 1)
    (HR3 : ∀ n, n0 ≤ n → q (n+1) = q n + L (n-4))
    (n : ℕ) (hn : n0 ≤ n) (hn4 : 4 ≤ n) :
    Phi lam L r q (n+1) = lam * Phi lam L r q n - 1 / (lam - 1) := by
  have hne : (lam - 1) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlam1)
  have e1 : (n+1) - 1 = n := by omega
  have e2 : (n+1) - 2 = n - 1 := by omega
  have e3 : (n+1) - 3 = n - 2 := by omega
  have e4 : (n+1) - 4 = n - 3 := by omega
  unfold Phi
  rw [e1, e2, e3, e4, HR1 n hn, HR2 n hn, HR3 n hn]
  have hne2 : (lam - 1)^2 ≠ 0 := pow_ne_zero _ hne
  field_simp
  ring_nf
  linear_combination (-(L (n-4))) * hlam_eq

-- Geometric solution of the potential.
theorem Phi_geom
    (hlam1 : (1:ℝ) < lam) (hlam_eq : lam^4 * (lam-1)^3 = 1)
    (HR1 : ∀ n, n0 ≤ n → L (n+1) = L n + r n)
    (HR2 : ∀ n, n0 ≤ n → r (n+1) = r n + q n - 1)
    (HR3 : ∀ n, n0 ≤ n → q (n+1) = q n + L (n-4))
    (n1 : ℕ) (hn1a : n0 ≤ n1) (hn1b : 4 ≤ n1) :
    ∀ n, n1 ≤ n →
      Phi lam L r q n - 1/(lam-1)^2 = lam^(n-n1) * (Phi lam L r q n1 - 1/(lam-1)^2) := by
  have hne : (lam - 1) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlam1)
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m n1 with hm | hm
    · -- m < n1, so m+1 = n1 (since n1 ≤ m+1)
      have : m + 1 = n1 := by omega
      rw [this]; simp
    · have hstep := Phi_step hlam1 hlam_eq HR1 HR2 HR3 m (le_trans hn1a hm) (le_trans hn1b hm)
      have ihm := ih hm
      have hsm : (m+1) - n1 = (m - n1) + 1 := by omega
      have hLHS : lam * Phi lam L r q m - 1/(lam-1) - 1/(lam-1)^2
            = lam * (Phi lam L r q m - 1/(lam-1)^2) := by field_simp; ring
      rw [hstep, hsm]
      calc lam * Phi lam L r q m - 1 / (lam - 1) - 1 / (lam - 1) ^ 2
          = lam * (Phi lam L r q m - 1/(lam-1)^2) := hLHS
        _ = lam * (lam^(m-n1) * (Phi lam L r q n1 - 1/(lam-1)^2)) := by rw [ihm]
        _ = lam^((m-n1)+1) * (Phi lam L r q n1 - 1/(lam-1)^2) := by ring

end

/-- If `c·λⁿ ≤ a n ≤ C·λⁿ` eventually with `c,C,λ>0`, then `a n ^ (1/n) → λ`. -/
theorem tendsto_rpow_inv_of_geom {a : ℕ → ℝ} {lam c C : ℝ}
    (hlam : 0 < lam) (hc : 0 < c) (hC : 0 < C) (N : ℕ)
    (hlo : ∀ n, N ≤ n → c * lam^n ≤ a n)
    (hhi : ∀ n, N ≤ n → a n ≤ C * lam^n) :
    Tendsto (fun n : ℕ => (a n) ^ ((n:ℝ)⁻¹)) atTop (nhds lam) := by
  have h0 : Tendsto (fun n : ℕ => ((n:ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  -- key: for any d>0, d^(1/n) → 1
  have hpow : ∀ d : ℝ, 0 < d → Tendsto (fun n : ℕ => d ^ ((n:ℝ)⁻¹)) atTop (nhds 1) := by
    intro d hd
    have hcont : ContinuousAt (fun x : ℝ => d ^ x) 0 := by
      apply Real.continuousAt_const_rpow (ne_of_gt hd)
    have := hcont.tendsto.comp h0
    simpa [Real.rpow_zero] using this
  -- helper: (d * lam^n)^(1/n) = d^(1/n) * lam  for n ≥ 1
  have hfact : ∀ d : ℝ, 0 ≤ d → ∀ n : ℕ, 1 ≤ n →
      (d * lam^n) ^ ((n:ℝ)⁻¹) = d ^ ((n:ℝ)⁻¹) * lam := by
    intro d hd n hn
    have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Real.mul_rpow hd (by positivity)]
    congr 1
    rw [← Real.rpow_natCast lam n, ← Real.rpow_mul (le_of_lt hlam),
        mul_inv_cancel₀ hn0, Real.rpow_one]
  -- the lower and upper envelope sequences tend to lam
  have hlow : Tendsto (fun n : ℕ => c ^ ((n:ℝ)⁻¹) * lam) atTop (nhds lam) := by
    have := (hpow c hc).mul_const lam
    simpa using this
  have hup : Tendsto (fun n : ℕ => C ^ ((n:ℝ)⁻¹) * lam) atTop (nhds lam) := by
    have := (hpow C hC).mul_const lam
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
    have hnN : N ≤ n := le_trans (le_max_left N 1) hn
    rw [← hfact c (le_of_lt hc) n hn1]
    apply Real.rpow_le_rpow (by positivity) (hlo n hnN) (by positivity)
  · filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
    have hnN : N ≤ n := le_trans (le_max_left N 1) hn
    rw [← hfact C (le_of_lt hC) n hn1]
    apply Real.rpow_le_rpow (le_trans (by positivity) (hlo n hnN)) (hhi n hnN) (by positivity)

/-- Sum of coefficients of `Phi` (positive). -/
noncomputable def Scoef (lam : ℝ) : ℝ :=
  1 + 1/(lam-1) + 1/(lam-1)^2 + (lam-1) + lam*(lam-1) + lam^2*(lam-1) + lam^3*(lam-1)

section
variable {lam : ℝ} {a L r q : ℕ → ℝ} {n0 : ℕ}

theorem Phi_ge_L (hlam1 : (1:ℝ) < lam)
    (hL : ∀ k, 0 ≤ L k) (hr : ∀ k, 0 ≤ r k) (hq : ∀ k, 0 ≤ q k) (n : ℕ) :
    L n ≤ Phi lam L r q n := by
  have h1 : (0:ℝ) < lam - 1 := by linarith
  have hlam0 : (0:ℝ) ≤ lam := by linarith
  unfold Phi
  have t1 : 0 ≤ r n / (lam-1) := div_nonneg (hr n) (le_of_lt h1)
  have t2 : 0 ≤ q n / (lam-1)^2 := div_nonneg (hq n) (by positivity)
  have t3 : 0 ≤ (lam-1) * L (n-1) := mul_nonneg (le_of_lt h1) (hL _)
  have t4 : 0 ≤ lam * (lam-1) * L (n-2) :=
    mul_nonneg (mul_nonneg hlam0 (le_of_lt h1)) (hL _)
  have t5 : 0 ≤ lam^2 * (lam-1) * L (n-3) :=
    mul_nonneg (mul_nonneg (by positivity) (le_of_lt h1)) (hL _)
  have t6 : 0 ≤ lam^3 * (lam-1) * L (n-4) :=
    mul_nonneg (mul_nonneg (by positivity) (le_of_lt h1)) (hL _)
  linarith

theorem Phi_le_S_L (hlam1 : (1:ℝ) < lam)
    (hmono : ∀ i j, i ≤ j → L i ≤ L j)
    (hqr : ∀ k, q k ≤ r k) (hrl : ∀ k, r k ≤ L k)
    (n : ℕ) (hn : 4 ≤ n) :
    Phi lam L r q n ≤ Scoef lam * L n := by
  have h1 : (0:ℝ) < lam - 1 := by linarith
  have hlam0 : (0:ℝ) ≤ lam := by linarith
  have hqn : q n ≤ L n := le_trans (hqr n) (hrl n)
  have hrn : r n ≤ L n := hrl n
  have hm1 : L (n-1) ≤ L n := hmono _ _ (by omega)
  have hm2 : L (n-2) ≤ L n := hmono _ _ (by omega)
  have hm3 : L (n-3) ≤ L n := hmono _ _ (by omega)
  have hm4 : L (n-4) ≤ L n := hmono _ _ (by omega)
  have hsq : (0:ℝ) < (lam-1)^2 := by positivity
  rw [show Scoef lam * L n = L n + L n/(lam-1) + L n/(lam-1)^2 + (lam-1)*L n
        + lam*(lam-1)*L n + lam^2*(lam-1)*L n + lam^3*(lam-1)*L n from by unfold Scoef; ring]
  unfold Phi
  gcongr

theorem Scoef_pos (hlam1 : (1:ℝ) < lam) : 0 < Scoef lam := by
  have h1 : (0:ℝ) < lam - 1 := by linarith
  unfold Scoef
  have : (0:ℝ) ≤ lam := by linarith
  positivity

set_option maxHeartbeats 1000000 in
theorem main_limit
    (hlam_lo : (3:ℝ)/2 < lam) (hlam_hi : lam < 2) (hlam_eq : lam^4 * (lam-1)^3 = 1)
    (HR0 : ∀ n, n0 ≤ n → a (n+1) = a n + L n)
    (HR1 : ∀ n, n0 ≤ n → L (n+1) = L n + r n)
    (HR2 : ∀ n, n0 ≤ n → r (n+1) = r n + q n - 1)
    (HR3 : ∀ n, n0 ≤ n → q (n+1) = q n + L (n-4))
    (hL : ∀ k, 0 ≤ L k) (hr : ∀ k, 0 ≤ r k) (hq : ∀ k, 0 ≤ q k)
    (hmono : ∀ i j, i ≤ j → L i ≤ L j)
    (hqr : ∀ k, q k ≤ r k) (hrl : ∀ k, r k ≤ L k)
    (n1 : ℕ) (hn1a : n0 ≤ n1) (hn1b : 4 ≤ n1)
    (hbig : (4:ℝ) ≤ L n1) (hapos : 0 < a n1) :
    Tendsto (fun n : ℕ => (a n) ^ ((n:ℝ)⁻¹)) atTop (nhds lam) := by
  have hlam1 : (1:ℝ) < lam := by linarith
  have hlam0 : (0:ℝ) < lam := by linarith
  have h1 : (0:ℝ) < lam - 1 := by linarith
  set C : ℝ := 1/(lam-1)^2 with hC
  -- C < 4
  have hClt4 : C < 4 := by
    rw [hC]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hlam_lo]
  have hCpos : 0 < C := by rw [hC]; positivity
  -- geometric solution
  have hgeom := Phi_geom (lam := lam) (L := L) (r := r) (q := q) (n0 := n0)
    hlam1 hlam_eq HR1 HR2 HR3 n1 hn1a hn1b
  set K : ℝ := Phi lam L r q n1 - C with hKdef
  have hPhin1 : L n1 ≤ Phi lam L r q n1 := Phi_ge_L hlam1 hL hr hq n1
  have hK : 0 < K := by rw [hKdef]; linarith [hPhin1, hbig, hClt4]
  -- rewrite hgeom as Phi n = C + K * lam^(n-n1)
  have hPhi : ∀ n, n1 ≤ n → Phi lam L r q n = C + K * lam^(n-n1) := by
    intro n hn
    have := hgeom n hn
    rw [hKdef]; linarith [this]
  -- pow conversion
  have hpowconv : ∀ n, n1 ≤ n → lam^n = lam^n1 * lam^(n-n1) := by
    intro n hn; rw [← pow_add]; congr 1; omega
  have hSpos := Scoef_pos (lam := lam) hlam1
  set CU : ℝ := C + K with hCU
  set cL : ℝ := K / (Scoef lam * lam^n1) with hcL
  have hCUpos : 0 < CU := by rw [hCU]; linarith
  have hcLpos : 0 < cL := by rw [hcL]; positivity
  -- L upper bound: L n ≤ CU * lam^n
  have hLhi : ∀ n, n1 ≤ n → L n ≤ CU * lam^n := by
    intro n hn
    have h2 : L n ≤ Phi lam L r q n := Phi_ge_L hlam1 hL hr hq n
    rw [hPhi n hn] at h2
    have hge1 : (1:ℝ) ≤ lam^(n-n1) := one_le_pow₀ (le_of_lt hlam1)
    have hple : lam^(n-n1) ≤ lam^n := by
      apply pow_le_pow_right₀ (le_of_lt hlam1); omega
    calc L n ≤ C + K * lam^(n-n1) := h2
      _ ≤ C * lam^(n-n1) + K * lam^(n-n1) := by nlinarith [hge1, hCpos, le_of_lt hK]
      _ = CU * lam^(n-n1) := by rw [hCU]; ring
      _ ≤ CU * lam^n := by nlinarith [hple, le_of_lt hCUpos]
  -- L lower bound: cL * lam^n ≤ L n
  have hLlo : ∀ n, n1 ≤ n → cL * lam^n ≤ L n := by
    intro n hn
    have h2 : Phi lam L r q n ≤ Scoef lam * L n :=
      Phi_le_S_L hlam1 hmono hqr hrl n (le_trans hn1b hn)
    rw [hPhi n hn] at h2
    -- C + K lam^(n-n1) ≤ Scoef * L n, and C ≥ 0 so K lam^(n-n1) ≤ Scoef L n
    have h3 : K * lam^(n-n1) ≤ Scoef lam * L n := by nlinarith [hCpos]
    -- lam^n = lam^n1 * lam^(n-n1)
    have hpc := hpowconv n hn
    rw [hcL, hpc]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    -- K * (lam^n1 * lam^(n-n1)) ≤ L n * (Scoef lam * lam^n1)
    nlinarith [h3, pow_pos hlam0 n1, le_of_lt hK]
  -- a upper bound
  set Ca : ℝ := a n1 / lam^n1 + CU / (lam-1) with hCa
  have hCapos : 0 < Ca := by rw [hCa]; have := pow_pos hlam0 n1; positivity
  have hCUle : CU ≤ Ca * (lam - 1) := by
    rw [hCa]; rw [add_mul, div_mul_cancel₀ _ (ne_of_gt h1)]
    have : 0 ≤ a n1 / lam^n1 * (lam-1) := by
      have := pow_pos hlam0 n1; positivity
    linarith
  have hahi : ∀ n, n1 ≤ n → a n ≤ Ca * lam^n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        rw [hCa]
        have hp := pow_pos hlam0 n1
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hp)]
        have : 0 ≤ CU / (lam-1) * lam^n1 := by positivity
        linarith
    | succ m hm ih =>
        have hrec := HR0 m (le_trans hn1a hm)
        have hLm := hLhi m hm
        have hpm := pow_pos hlam0 m
        have hprod : CU * lam^m ≤ Ca*(lam-1)*lam^m :=
          mul_le_mul_of_nonneg_right hCUle (le_of_lt hpm)
        calc a (m+1) = a m + L m := hrec
          _ ≤ Ca * lam^m + CU * lam^m := by linarith
          _ ≤ Ca * lam^(m+1) := by
              rw [pow_succ]
              have : Ca * (lam^m * lam) = Ca * lam^m + Ca*(lam-1)*lam^m := by ring
              rw [this]; linarith [hprod]
  -- a lower bound
  set ca : ℝ := min (a n1 / lam^n1) (cL / (lam-1)) with hca
  have hcapos : 0 < ca := by
    rw [hca]; apply lt_min
    · have := pow_pos hlam0 n1; positivity
    · positivity
  have hca2 : ca ≤ cL / (lam-1) := by rw [hca]; exact min_le_right _ _
  have hkey : ca * (lam - 1) ≤ cL := by
    rw [le_div_iff₀ h1] at hca2; linarith [hca2]
  have halo : ∀ n, n1 ≤ n → ca * lam^n ≤ a n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        have hp := pow_pos hlam0 n1
        have hle1 : ca ≤ a n1 / lam^n1 := by rw [hca]; exact min_le_left _ _
        calc ca * lam^n1 ≤ (a n1 / lam^n1) * lam^n1 := by nlinarith [hp]
          _ = a n1 := by rw [div_mul_cancel₀ _ (ne_of_gt hp)]
    | succ m hm ih =>
        have hrec := HR0 m (le_trans hn1a hm)
        have hLm := hLlo m hm
        have hpm := pow_pos hlam0 m
        have hprod : ca * (lam-1) * lam^m ≤ cL * lam^m :=
          mul_le_mul_of_nonneg_right hkey (le_of_lt hpm)
        rw [hrec, pow_succ]
        have : ca * (lam^m * lam) = ca * lam^m + ca*(lam-1)*lam^m := by ring
        rw [this]
        linarith [ih, hLm, hprod]
  -- conclude
  exact tendsto_rpow_inv_of_geom hlam0 hcapos hCapos n1 halo hahi

end

end A381358dev
