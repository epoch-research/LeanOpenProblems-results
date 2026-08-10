import Submission.Frame2a
open PowerSeries
namespace Frame2b
open ExpFrame Frame1 Frame2a Finset
variable (p : ℕ) (hp : p ≠ 0)

noncomputable def Mser (p : ℕ) (hp : p ≠ 0) (L : PowerSeries ℚ) : PowerSeries ℚ :=
  L - (p : ℚ)⁻¹ • (PowerSeries.expand p hp L)

-- (M0)
theorem Mser_const (L : PowerSeries ℚ) (hL : PowerSeries.constantCoeff L = 0) :
    PowerSeries.constantCoeff (Mser p hp L) = 0 := by
  rw [Mser, map_sub, PowerSeries.constantCoeff_smul, PowerSeries.constantCoeff_expand, hL,
    smul_zero, sub_zero]

-- (K3)
theorem K3 (L : PowerSeries ℚ) :
    PowerSeries.expand p hp L + (p : ℚ) • (Mser p hp L) = (p : ℚ) • L := by
  have hpc : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  rw [Mser, smul_sub, smul_smul, mul_inv_cancel₀ hpc, one_smul, add_sub_cancel]

-- key smul fact
theorem smul_key (N : ℕ) (x : PowerSeries ℚ) :
    N • ((p : ℚ) • x) = (p * N) • x := by
  rw [← Nat.cast_smul_eq_nsmul ℚ N, smul_smul, ← Nat.cast_mul, mul_comm,
    Nat.cast_smul_eq_nsmul]

-- (FACT)
theorem factor (L : PowerSeries ℚ) (hL : PowerSeries.constantCoeff L = 0) (N : ℕ) :
    (Exp L) ^ (p * N)
      = PowerSeries.expand p hp ((Exp L) ^ N) * (Exp ((p : ℚ) • Mser p hp L)) ^ N := by
  rw [Exp_pow, Exp_pow, expand_Exp, Exp_pow, map_nsmul, Exp_mul, ← smul_add, K3 p hp L,
    smul_key p N L]

-- (RED)
theorem reduction (L : PowerSeries ℚ) (hL : PowerSeries.constantCoeff L = 0) (N : ℕ) :
    PowerSeries.coeff (p * N) ((Exp L) ^ (p * N))
      = PowerSeries.coeff N ((Exp L) ^ N * Up p ((Exp ((p : ℚ) • Mser p hp L)) ^ N)) := by
  rw [factor p hp L hL N, ← Up_coeff p _ N, Up_expand_mul p hp]

-- (EXPAND-SUM)
theorem b_expand (L : PowerSeries ℚ) (hL : PowerSeries.constantCoeff L = 0) (N : ℕ) :
    PowerSeries.coeff (p * N) ((Exp L) ^ (p * N))
      = ∑ j ∈ Finset.range (p * N + 1),
          ((p : ℚ) * N) ^ j / (j.factorial : ℚ)
            * PowerSeries.coeff N ((Exp L) ^ N * Up p ((Mser p hp L) ^ j)) := by
  rw [reduction p hp L hL N]
  set A := (Exp L) ^ N with hA
  set M := Mser p hp L with hMdef
  have hMc : PowerSeries.constantCoeff M = 0 := by rw [hMdef]; exact Mser_const p hp L hL
  -- coefficient formula for E^N
  have hEcoeff : ∀ n, coeff n ((Exp ((p : ℚ) • M)) ^ N)
      = ∑ j ∈ range (n + 1), ((p : ℚ) * N) ^ j * coeff n (M ^ j) / (j.factorial : ℚ) := by
    intro n
    have hEN : (Exp ((p : ℚ) • M)) ^ N = Exp (((p : ℚ) * N) • M) := by
      rw [Exp_pow]; congr 1
      rw [← Nat.cast_smul_eq_nsmul ℚ N, smul_smul, mul_comm (N : ℚ) (p : ℚ)]
    have hc0 : PowerSeries.constantCoeff (((p : ℚ) * N) • M) = 0 := by
      rw [constantCoeff_smul, hMc, smul_zero]
    rw [hEN, Exp_eq_sum _ hc0, coeff_mk]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_pow, coeff_smul, smul_eq_mul]
  -- vanishing of M-powers
  have hvanish : ∀ (i n : ℕ), n < i → coeff n (M ^ i) = 0 := by
    intro i n hni
    rw [hMdef]; exact vanish (Mser p hp L) (Mser_const p hp L hL) i n hni
  -- LHS as double sum
  have hLHS : coeff N (A * Up p ((Exp ((p : ℚ) • M)) ^ N))
      = ∑ j ∈ range (p * N + 1), ∑ ij ∈ antidiagonal N,
          ((p : ℚ) * N) ^ j / (j.factorial : ℚ) * (coeff ij.1 A * coeff (p * ij.2) (M ^ j)) := by
    rw [coeff_mul]
    have step1 : (∑ ij ∈ antidiagonal N, coeff ij.1 A * coeff ij.2 (Up p ((Exp ((p : ℚ) • M)) ^ N)))
        = ∑ ij ∈ antidiagonal N, coeff ij.1 A *
            (∑ j ∈ range (p * N + 1), ((p : ℚ) * N) ^ j * coeff (p * ij.2) (M ^ j) / (j.factorial : ℚ)) := by
      apply Finset.sum_congr rfl
      intro ij hij
      rw [Up_coeff, hEcoeff]
      congr 1
      apply Finset.sum_subset
      · intro x hx
        rw [Finset.mem_range] at hx ⊢
        have hij2 : ij.2 ≤ N := by rw [Finset.mem_antidiagonal] at hij; omega
        have hle : p * ij.2 ≤ p * N := Nat.mul_le_mul (le_refl p) hij2
        omega
      · intro x _ hxnot
        rw [Finset.mem_range] at hxnot
        rw [hvanish x (p * ij.2) (by omega)]; ring
    rw [step1]
    have step2 : (∑ ij ∈ antidiagonal N, coeff ij.1 A *
            (∑ j ∈ range (p * N + 1), ((p : ℚ) * N) ^ j * coeff (p * ij.2) (M ^ j) / (j.factorial : ℚ)))
        = ∑ ij ∈ antidiagonal N, ∑ j ∈ range (p * N + 1),
            coeff ij.1 A * (((p : ℚ) * N) ^ j * coeff (p * ij.2) (M ^ j) / (j.factorial : ℚ)) := by
      apply Finset.sum_congr rfl
      intro ij _
      rw [Finset.mul_sum]
    rw [step2, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro ij _
    ring
  -- RHS as double sum
  have hRHS : (∑ j ∈ range (p * N + 1),
          ((p : ℚ) * N) ^ j / (j.factorial : ℚ) * coeff N (A * Up p (M ^ j)))
      = ∑ j ∈ range (p * N + 1), ∑ ij ∈ antidiagonal N,
          ((p : ℚ) * N) ^ j / (j.factorial : ℚ) * (coeff ij.1 A * coeff (p * ij.2) (M ^ j)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [coeff_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij _
    rw [Up_coeff]
  rw [hLHS]
  exact hRHS.symm

-- (DIFF)
theorem b_diff (L : PowerSeries ℚ) (hL : PowerSeries.constantCoeff L = 0) (N : ℕ) :
    PowerSeries.coeff (p * N) ((Exp L) ^ (p * N)) - PowerSeries.coeff N ((Exp L) ^ N)
      = ∑ j ∈ Finset.Icc 1 (p * N),
          ((p : ℚ) * N) ^ j / (j.factorial : ℚ)
            * PowerSeries.coeff N ((Exp L) ^ N * Up p ((Mser p hp L) ^ j)) := by
  have Up_one : Up p (1 : PowerSeries ℚ) = 1 := by
    ext k
    rw [Up_coeff, coeff_one, coeff_one]
    by_cases hk : k = 0
    · subst hk; simp
    · rw [if_neg (Nat.mul_ne_zero hp hk), if_neg hk]
  rw [b_expand p hp L hL N]
  have hins : Finset.range (p * N + 1) = insert 0 (Finset.Icc 1 (p * N)) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hins, Finset.sum_insert (by simp)]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul, Up_one, mul_one]
  ring

#print axioms Frame2b.factor
#print axioms Frame2b.reduction
#print axioms Frame2b.b_expand
#print axioms Frame2b.b_diff

end Frame2b
