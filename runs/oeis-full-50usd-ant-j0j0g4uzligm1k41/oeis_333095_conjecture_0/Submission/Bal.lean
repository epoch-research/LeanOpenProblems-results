import FormalConjectures.Util.ProblemImports
open Nat Finset PowerSeries

noncomputable section

-- rational ballot number B r k = r/(r+2k) * C(r+2k, k)
def Bq (r k : ℕ) : ℚ := (r : ℚ) / (r + 2*k) * ((r + 2*k).choose k : ℚ)

-- Nat identity: (2k+1)*C(2k,k) = (k+1)*C(2k+1,k)
theorem nat_id1 (k : ℕ) : (2*k+1) * (2*k).choose k = (k+1) * (2*k+1).choose k := by
  have h := Nat.succ_mul_choose_eq (2*k) k
  -- h : (2k+1) * C(2k,k) = C(2k+1, k+1) * (k+1)
  have hs : (2*k+1).choose (k+1) = (2*k+1).choose k := by
    have := Nat.choose_symm (n := 2*k+1) (k := k+1) (by omega)
    rw [show 2*k+1-(k+1) = k by omega] at this
    exact this.symm
  rw [hs] at h
  simp only [Nat.succ_eq_add_one] at h ⊢
  rw [h]; ring

-- base identity r = 1 : Bq 1 k = catalan k
theorem Bq_one (k : ℕ) : Bq 1 k = (catalan k : ℚ) := by
  unfold Bq
  have hcat : ((k:ℚ)+1) * (catalan k : ℚ) = ((2*k).choose k : ℚ) := by
    have h := succ_mul_catalan_eq_centralBinom k
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    have := congrArg (Nat.cast (R := ℚ)) h
    push_cast at this ⊢; linarith [this]
  have hid : ((2:ℚ)*k+1) * ((2*k).choose k : ℚ) = ((k:ℚ)+1) * ((2*k+1).choose k : ℚ) := by
    have := congrArg (Nat.cast (R := ℚ)) (nat_id1 k)
    push_cast at this ⊢; linarith [this]
  have e : (1+2*k) = 2*k+1 := by ring
  rw [e]
  push_cast
  have h1 : (1 + 2*(k:ℚ)) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, div_eq_iff h1]
  nlinarith [hcat, hid]

-- Catalan power series over ℚ
def Cq : PowerSeries ℚ := PowerSeries.map (Nat.castRingHom ℚ) PowerSeries.catalanSeries

theorem Cq_coeff (n : ℕ) : (coeff n) Cq = (catalan n : ℚ) := by
  unfold Cq; rw [coeff_map]; simp [PowerSeries.catalanSeries_coeff]

theorem Cq_rel : Cq^2 * PowerSeries.X + 1 = Cq := by
  unfold Cq
  have h := PowerSeries.catalanSeries_sq_mul_X_add_one
  have := congrArg (PowerSeries.map (Nat.castRingHom ℚ)) h
  simpa using this

theorem Cq_step (r : ℕ) : PowerSeries.X * Cq^(r+2) = Cq^(r+1) - Cq^r := by
  have h : Cq^2 * PowerSeries.X = Cq - 1 := by linear_combination Cq_rel
  calc PowerSeries.X * Cq^(r+2) = (Cq^2 * PowerSeries.X) * Cq^r := by ring
    _ = (Cq - 1) * Cq^r := by rw [h]
    _ = Cq^(r+1) - Cq^r := by ring

theorem Bq_zero (k : ℕ) : Bq 0 (k+1) = 0 := by
  unfold Bq; simp

-- recurrence: Bq (r+2) k = Bq (r+1) (k+1) - Bq r (k+1)
theorem Bq_rec (r k : ℕ) : Bq (r+2) k = Bq (r+1) (k+1) - Bq r (k+1) := by
  have hk1 : ((k:ℚ)+1) ≠ 0 := by positivity
  -- Pascal : C(r+2k+3, k+1) = C(r+2k+2, k) + C(r+2k+2, k+1)
  have Pas : (r+2*k+3).choose (k+1) = (r+2*k+2).choose k + (r+2*k+2).choose (k+1) := by
    have h : r+2*k+3 = (r+2*k+2)+1 := by omega
    rw [h, Nat.choose_succ_succ]
  have Pasq : ((r+2*k+3).choose (k+1) : ℚ)
      = ((r+2*k+2).choose k : ℚ) + ((r+2*k+2).choose (k+1) : ℚ) := by
    have := congrArg (Nat.cast (R := ℚ)) Pas; push_cast at this; linarith [this]
  -- R1 : C(r+2k+2, k+1) = C(r+2k+2, k) * (r+k+2) / (k+1)
  have R1nat : (r+2*k+2).choose (k+1) * (k+1) = (r+2*k+2).choose k * (r+k+2) := by
    have := Nat.choose_succ_right_eq (r+2*k+2) k
    rw [show (r+2*k+2) - k = r+k+2 by omega] at this
    exact this
  have hB : ((r+2*k+2).choose (k+1) : ℚ) = ((r+2*k+2).choose k : ℚ) * (r+k+2) / (k+1) := by
    rw [eq_div_iff hk1]
    have := congrArg (Nat.cast (R := ℚ)) R1nat; push_cast at this ⊢; linarith [this]
  unfold Bq
  have e1 : (r+2)+2*k = r+2*k+2 := by ring
  have e2 : (r+1)+2*(k+1) = r+2*k+3 := by ring
  have e3 : r+2*(k+1) = r+2*k+2 := by ring
  rw [e1, e2, e3, Pasq, hB]
  push_cast
  have d1 : ((r:ℚ)+2) + 2*k ≠ 0 := by positivity
  have d2 : ((r:ℚ)+1) + 2*(k+1) ≠ 0 := by positivity
  have d3 : (r:ℚ) + 2*(k+1) ≠ 0 := by positivity
  field_simp
  ring

-- base: coeff k (Cq^2) = Bq 2 k
theorem Bq_two (k : ℕ) : (coeff k) (Cq^2) = Bq 2 k := by
  have step := Cq_step 0
  simp only [pow_zero, zero_add, pow_one] at step
  have h := congrArg (coeff (k+1)) step
  rw [mul_comm, coeff_succ_mul_X, map_sub, Cq_coeff, coeff_one] at h
  simp only [Nat.add_one_ne_zero, if_false, sub_zero] at h
  rw [h]
  have hrec := Bq_rec 0 k
  rw [Bq_zero, sub_zero, Bq_one] at hrec
  exact hrec.symm

-- main: for r ≥ 1, coeff k (Cq^r) = Bq r k
theorem coeff_pow_Cq : ∀ r, 1 ≤ r → ∀ k, (coeff k) (Cq^r) = Bq r k := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr k
    match r, hr with
    | 1, _ =>
      rw [pow_one, Cq_coeff, Bq_one]
    | 2, _ =>
      exact Bq_two k
    | (s+3), _ =>
      have step := Cq_step (s+1)
      have h := congrArg (coeff (k+1)) step
      rw [mul_comm, coeff_succ_mul_X, map_sub] at h
      rw [ih (s+2) (by omega) (by omega) (k+1), ih (s+1) (by omega) (by omega) (k+1)] at h
      rw [show s+3 = (s+1)+2 by ring, h]
      exact (Bq_rec (s+1) k).symm

end

/-- integer Catalan-power coefficients -/
noncomputable def cn (n k : ℕ) : ℕ := (coeff k) (PowerSeries.catalanSeries ^ (3*n))

theorem Cq_pow_coeff_eq_cn (n k : ℕ) :
    (coeff k) (Cq ^ (3*n)) = (cn n k : ℚ) := by
  unfold Cq cn
  rw [← map_pow, coeff_map]
  simp

theorem Bq_eq_cn (n k : ℕ) (hn : 1 ≤ n) : Bq (3*n) k = (cn n k : ℚ) := by
  rw [← Cq_pow_coeff_eq_cn, coeff_pow_Cq (3*n) (by omega) k]

noncomputable def aa (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    ((Finset.sum (range (n + 1)) fun k =>
      let N := 3 * n
      let term_val : ℚ := (N : ℚ) / (N + 2 * k : ℚ) * ((N + 2 * k).choose k : ℚ)
      term_val).floor).toNat

theorem aa_eq (n : ℕ) (hn : 1 ≤ n) :
    aa n = ∑ k ∈ range (n+1), cn n k := by
  unfold aa
  rw [if_neg (by omega)]
  simp only
  have key : ∀ k ∈ range (n+1),
      (((3*n:ℕ):ℚ) / (((3*n:ℕ):ℚ) + 2 * (k:ℚ)) * (((3*n+2*k).choose k : ℕ):ℚ))
        = ((cn n k : ℕ):ℚ) := by
    intro k _
    have hb := Bq_eq_cn n k hn
    unfold Bq at hb
    push_cast at hb ⊢
    linarith [hb]
  rw [Finset.sum_congr rfl key, ← Nat.cast_sum]
  show ⌊((∑ x ∈ range (n+1), cn n x : ℕ):ℚ)⌋.toNat = ∑ k ∈ range (n+1), cn n k
  rw [Int.floor_natCast, Int.toNat_natCast]


/-- Catalan series over ℤ. -/
def Czi : PowerSeries ℤ := PowerSeries.map (Nat.castRingHom ℤ) PowerSeries.catalanSeries

theorem coeff_Czi_pow (n k : ℕ) : (coeff k) (Czi ^ (3*n)) = (cn n k : ℤ) := by
  unfold Czi cn; rw [← map_pow, coeff_map]; simp

/-- `a(n)` as a coefficient of an integer power series times `1/(1-X)`. -/
theorem az_eq (n : ℕ) (hn : 1 ≤ n) :
    (aa n : ℤ) = (coeff n) (Czi ^ (3*n) * PowerSeries.mk fun _ => (1:ℤ)) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, aa_eq n hn]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rw [coeff_Czi_pow, coeff_mk, mul_one]
