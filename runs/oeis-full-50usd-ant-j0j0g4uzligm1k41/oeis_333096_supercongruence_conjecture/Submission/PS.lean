import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators Int
open PowerSeries

noncomputable section

/-- period-3 weight -/
def hh (t : ℕ) : ℤ := if t = 0 then 1 else if t % 3 = 0 then 2 else -1

abbrev C (r : ℤ) (k : ℕ) : ℤ := Ring.choose r k

/-- generalized binomial power series `(1+X)^r`. -/
abbrev bs (r : ℤ) : PowerSeries ℤ := binomialSeries ℤ r

lemma coeff_bs (r : ℤ) (n : ℕ) : coeff n (bs r) = C r n := by
  simp [bs, binomialSeries_coeff]

/-- `Ff s N = coeff N (bs (s*N) * Gser)`. -/
def Gser : PowerSeries ℤ := PowerSeries.mk hh

def Ff (s : ℤ) (N : ℕ) : ℤ := ∑ j ∈ range (N + 1), hh (N - j) * C (s * (N : ℤ)) j

lemma coeff_Gser (n : ℕ) : coeff n Gser = hh n := by simp [Gser, coeff_mk]

lemma Ff_eq_coeff (s : ℤ) (N : ℕ) : Ff s N = coeff N (bs (s * N) * Gser) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold Ff
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeff_bs, coeff_Gser]
  ring

variable (p : ℕ)

/-- `(1+X)^p - 1`. -/
def Ypp : PowerSeries ℤ := (1 + X) ^ p - 1

lemma constantCoeff_Ypp : constantCoeff (Ypp p) = 0 := by
  simp [Ypp]

lemma hasSubst_Ypp : HasSubst (Ypp p) := HasSubst.of_constantCoeff_zero' (constantCoeff_Ypp p)

lemma bs_one : bs (1 : ℤ) = 1 + X := by
  have : (1 : ℤ) = ((1 : ℕ) : ℤ) := by norm_num
  rw [this, bs, binomialSeries_nat]
  ring

lemma bs_natCast (d : ℕ) : bs (d : ℤ) = (1 + X) ^ d := by
  rw [bs, binomialSeries_nat]

lemma bs_add (r s : ℤ) : bs (r + s) = bs r * bs s := binomialSeries_add r s

lemma bs_zero : bs (0 : ℤ) = 1 := binomialSeries_zero

lemma subst_Ypp_one : subst (Ypp p) (1 : PowerSeries ℤ) = 1 := by
  rw [← coe_substAlgHom (hasSubst_Ypp p), map_one]

lemma subst_bs_one : subst (Ypp p) (bs 1) = bs (p : ℤ) := by
  have h := hasSubst_Ypp p
  rw [bs_one, subst_add h, subst_Ypp_one, subst_X h, Ypp, bs_natCast]
  ring

lemma subst_bs_neg_one : subst (Ypp p) (bs (-1)) = bs (-(p : ℤ)) := by
  have h := hasSubst_Ypp p
  have e1 : subst (Ypp p) (bs (-1)) * bs (p : ℤ) = 1 := by
    rw [← subst_bs_one p, ← subst_mul h, ← bs_add, neg_add_cancel, bs_zero, subst_Ypp_one]
  have e3 : bs (p : ℤ) * bs (-(p : ℤ)) = 1 := by
    rw [← bs_add, add_neg_cancel, bs_zero]
  calc subst (Ypp p) (bs (-1))
      = subst (Ypp p) (bs (-1)) * (bs (p:ℤ) * bs (-(p:ℤ))) := by rw [e3, mul_one]
    _ = (subst (Ypp p) (bs (-1)) * bs (p:ℤ)) * bs (-(p:ℤ)) := by ring
    _ = bs (-(p:ℤ)) := by rw [e1, one_mul]

lemma subst_bs (w : ℤ) : subst (Ypp p) (bs w) = bs (p * w) := by
  have h := hasSubst_Ypp p
  induction w using Int.induction_on with
  | zero => rw [bs_zero, subst_Ypp_one, mul_zero, bs_zero]
  | succ i ih =>
      rw [bs_add, subst_mul h, ih, subst_bs_one p, ← bs_add]
      congr 1 <;> push_cast <;> ring
  | pred i ih =>
      rw [show (-(i:ℤ) - 1) = (-i) + (-1) by ring, bs_add, subst_mul h, ih, subst_bs_neg_one p,
        ← bs_add]
      congr 1 <;> push_cast <;> ring

/-- Cartier operator: `Up f` has `n`-th coeff = `pn`-th coeff of `f`. -/
def Up (f : PowerSeries ℤ) : PowerSeries ℤ := PowerSeries.mk (fun n => coeff (p * n) f)

lemma coeff_Up (f : PowerSeries ℤ) (n : ℕ) : coeff n (Up p f) = coeff (p * n) f := by
  simp [Up, coeff_mk]

/-- `Δ = ((1+X)^p - 1 - X^p)/p`. -/
def Del : PowerSeries ℤ := PowerSeries.mk (fun i => coeff i ((1 + X) ^ p - 1 - X ^ p) / p)

lemma coeff_onePlusX_pow (i : ℕ) : coeff i ((1 + X : PowerSeries ℤ) ^ p) = (p.choose i : ℤ) := by
  rw [← bs_natCast, coeff_bs]
  exact Ring.choose_natCast p i

lemma p_dvd_coeff_Ydiff (hp : p.Prime) (i : ℕ) :
    (p : ℤ) ∣ coeff i ((1 + X : PowerSeries ℤ) ^ p - 1 - X ^ p) := by
  rw [map_sub, map_sub, coeff_onePlusX_pow, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  rcases lt_trichotomy i p with hlt | heq | hgt
  · by_cases hi0 : i = 0
    · subst hi0; rw [Nat.choose_zero_right, if_pos rfl, if_neg (by omega : ¬ (0 = p))]; simp
    · rw [if_neg hi0, if_neg (by omega : ¬ i = p), sub_zero, sub_zero]
      exact_mod_cast Int.natCast_dvd_natCast.mpr (hp.dvd_choose_self hi0 hlt)
  · subst heq
    rw [Nat.choose_self, if_neg hp.pos.ne', if_pos rfl]; simp
  · rw [Nat.choose_eq_zero_of_lt hgt, if_neg (by omega : ¬ i = 0),
      if_neg (by omega : ¬ i = p)]; simp

lemma coeff_Del (hp : p.Prime) (i : ℕ) :
    (p : ℤ) * coeff i (Del p) = coeff i ((1 + X : PowerSeries ℤ) ^ p - 1 - X ^ p) := by
  rw [Del, coeff_mk, Int.mul_ediv_cancel' (p_dvd_coeff_Ydiff p hp i)]

lemma Y_eq (hp : p.Prime) : Ypp p = X ^ p + (p : ℤ) • Del p := by
  have hpD : (p : ℤ) • Del p = (1 + X : PowerSeries ℤ) ^ p - 1 - X ^ p := by
    ext i
    rw [PowerSeries.coeff_smul, smul_eq_mul, coeff_Del p hp]
  rw [hpD, Ypp]; ring

lemma coeff_Ypp_pow_zero_of_lt (d a : ℕ) (h : a < d) : coeff a ((Ypp p) ^ d) = 0 := by
  have hX : (X : PowerSeries ℤ) ∣ Ypp p := X_dvd_iff.mpr (constantCoeff_Ypp p)
  have hd : (X : PowerSeries ℤ) ^ d ∣ (Ypp p) ^ d := pow_dvd_pow_of_dvd hX d
  exact (X_pow_dvd_iff.mp hd) a h

lemma coeff_subst_bs (w : ℤ) (a : ℕ) :
    coeff a (subst (Ypp p) (bs w)) = ∑ d ∈ range (a + 1), C w d * coeff a ((Ypp p) ^ d) := by
  rw [coeff_subst' (hasSubst_Ypp p)]
  rw [finsum_eq_sum_of_support_subset _ (s := range (a + 1)) ?_]
  · apply Finset.sum_congr rfl
    intro d _; rw [coeff_bs, smul_eq_mul]
  · intro d hd
    simp only [Function.mem_support, coeff_bs, ne_eq] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    push_neg at hcon
    exact hd (by rw [coeff_Ypp_pow_zero_of_lt p d a (by omega), smul_zero])

lemma coeff_Ypp_pow (hp : p.Prime) (d a : ℕ) :
    coeff a ((Ypp p) ^ d)
      = ∑ k ∈ range (d + 1), (d.choose k : ℤ) * (p : ℤ) ^ (d - k)
          * coeff a (X ^ (p * k) * (Del p) ^ (d - k)) := by
  rw [Y_eq p hp, add_pow]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [smul_pow, ← pow_mul,
    show ((d.choose k : ℕ) : PowerSeries ℤ) = (d.choose k) • (1 : PowerSeries ℤ) by
      rw [nsmul_eq_mul, mul_one],
    mul_smul_comm, mul_one, mul_smul_comm, PowerSeries.coeff_smul, PowerSeries.coeff_smul,
    nsmul_eq_mul, smul_eq_mul]
  push_cast; ring

/-- `Qser r = U_p (Δ^r G)`. -/
def Qser (r : ℕ) : PowerSeries ℤ := Up p (Del p ^ r * Gser)

lemma coeff_Qser (r n : ℕ) :
    coeff n (Qser p r) = ∑ c ∈ range (p * n + 1), coeff c (Del p ^ r) * hh (p * n - c) := by
  rw [Qser, coeff_Up, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro c hc
  rw [coeff_Gser]

/-- coeff of `X^(pk) * Del^r` is a shift of coeff of `Del^r`. -/
lemma coeff_Xpk_mul (k r c : ℕ) :
    coeff c (X ^ (p * k) * (Del p) ^ r) = if p * k ≤ c then coeff (c - p * k) ((Del p) ^ r) else 0 := by
  rw [PowerSeries.coeff_X_pow_mul']

lemma Up_sum {ι} (s : Finset ι) (f : ι → PowerSeries ℤ) :
    Up p (∑ i ∈ s, f i) = ∑ i ∈ s, Up p (f i) := by
  ext n; rw [coeff_Up, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [coeff_Up])

lemma Up_smul (c : ℤ) (f : PowerSeries ℤ) : Up p (c • f) = c • Up p f := by
  ext n; rw [coeff_Up, PowerSeries.coeff_smul, PowerSeries.coeff_smul, coeff_Up]

lemma Up_Xpk_mul (hp : 0 < p) (k : ℕ) (f : PowerSeries ℤ) :
    Up p (X ^ (p * k) * f) = X ^ k * Up p f := by
  ext n
  rw [coeff_Up, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  by_cases h : k ≤ n
  · rw [if_pos h, if_pos (by gcongr : p * k ≤ p * n), coeff_Up, Nat.mul_sub_left_distrib]
  · rw [if_neg h, if_neg (fun hc => h (Nat.le_of_mul_le_mul_left hc hp))]

lemma Ypp_pow_eq (hp : p.Prime) (d : ℕ) :
    (Ypp p) ^ d = ∑ k ∈ range (d + 1),
      ((d.choose k : ℤ) * (p : ℤ) ^ (d - k)) • (X ^ (p * k) * (Del p) ^ (d - k)) := by
  ext a
  rw [map_sum, coeff_Ypp_pow p hp d a]
  apply Finset.sum_congr rfl
  intro k hk
  rw [PowerSeries.coeff_smul, smul_eq_mul]

lemma Up_Ypp_pow_Gser (hp : p.Prime) (d : ℕ) :
    Up p ((Ypp p) ^ d * Gser)
      = ∑ k ∈ range (d + 1), ((d.choose k : ℤ) * (p : ℤ) ^ (d - k)) • (X ^ k * Qser p (d - k)) := by
  rw [Ypp_pow_eq p hp d, Finset.sum_mul, Up_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [smul_mul_assoc, Up_smul, mul_assoc, Up_Xpk_mul p hp.pos, Qser]

/-- Step A of the master identity. -/
lemma Ff_pM_eq (hp : p.Prime) (s : ℤ) (M : ℕ) :
    Ff s (p * M)
      = ∑ d ∈ range (p * M + 1), C (s * (M : ℤ)) d * coeff M (Up p ((Ypp p) ^ d * Gser)) := by
  have hbs : bs (s * ((p * M : ℕ) : ℤ)) = subst (Ypp p) (bs (s * (M : ℤ))) := by
    rw [subst_bs]; congr 1; push_cast; ring
  rw [Ff_eq_coeff, hbs, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hL : (∑ c ∈ range (p * M + 1), coeff c (subst (Ypp p) (bs (s * (M : ℤ)))) * coeff (p * M - c) Gser)
      = ∑ c ∈ range (p * M + 1), ∑ d ∈ range (p * M + 1),
          C (s * (M : ℤ)) d * coeff c ((Ypp p) ^ d) * hh (p * M - c) := by
    apply Finset.sum_congr rfl
    intro c hc
    simp only [Finset.mem_range] at hc
    rw [coeff_Gser, coeff_subst_bs, Finset.sum_mul]
    rw [Finset.sum_subset (Finset.range_subset.mpr (by omega))]
    intro d _ hd
    simp only [Finset.mem_range] at hd
    rw [coeff_Ypp_pow_zero_of_lt p d c (by omega), mul_zero, zero_mul]
  have hR : (∑ d ∈ range (p * M + 1), C (s * (M : ℤ)) d * coeff M (Up p ((Ypp p) ^ d * Gser)))
      = ∑ d ∈ range (p * M + 1), ∑ c ∈ range (p * M + 1),
          C (s * (M : ℤ)) d * coeff c ((Ypp p) ^ d) * hh (p * M - c) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [coeff_Up, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    rw [coeff_Gser, mul_assoc]
  rw [hL, hR, Finset.sum_comm]

end
