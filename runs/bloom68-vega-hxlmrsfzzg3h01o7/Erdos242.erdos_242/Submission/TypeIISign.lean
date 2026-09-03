import SignedPivotGraph.Core

/-! Auxiliary sign certificate only. This file does not assert Erdős–Straus existence. -/
namespace Erdos242.Development.TypeIISign
open IndependentConstructive
open SignedPivotGraph

lemma jacobi_divisor_square_linear (b : ℤ) {d : ℕ} (hd : d ≠ 0)
    (hdiv : (d : ℤ) ∣ b ^ 2) : jacobiSym (d : ℤ) (4 * b - 1).natAbs = 1 := by
  induction d using induction_on_primes with
  | zero => exact False.elim (hd rfl)
  | one => exact jacobiSym.one_left _
  | prime_mul r d hr ih =>
    have hrz : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
    have hrd : (r : ℤ) ∣ b ^ 2 := dvd_trans (by exact_mod_cast dvd_mul_right r d) hdiv
    have hrb : (r : ℤ) ∣ b := hrz.dvd_of_dvd_pow hrd
    obtain ⟨n, hn⟩ := hrb
    have hrpos : (0 : ℤ) < r := by exact_mod_cast hr.pos
    have hJ := jacobi_positive_linear (m := (r : ℤ)) (n := n) hrpos
    have hden : 4 * (r : ℤ) * n - 1 = 4 * b - 1 := by rw [hn]; ring
    rw [hden] at hJ
    have hd0 : d ≠ 0 := by intro h; exact hd (by simp [h])
    have hdd : (d : ℤ) ∣ b ^ 2 := dvd_trans (by exact_mod_cast dvd_mul_left d r) hdiv
    rw [Nat.cast_mul, jacobiSym.mul_left, hJ, ih hd0 hdd, one_mul]

lemma abs_jacobi_of_square_dvd {b d : ℤ} (hd : d ≠ 0) (hdiv : d ∣ b ^ 2) :
    jacobiSym (d.natAbs : ℤ) (4 * b - 1).natAbs = 1 := by
  apply jacobi_divisor_square_linear b (Int.natAbs_ne_zero.mpr hd)
  exact (Int.natAbs_dvd).mpr hdiv

/-- Exact sign certificate, conditional on an actual Type II integer point and
its three p-unit coordinates/cofactors. No existence assertion is made. -/
lemma character_iff_positive {p : ℕ} {a b c : ℤ} (hp : p.Prime)
    (hp4 : p % 4 = 1) (ha : 0 < a)
    (hau : ¬ (p : ℤ) ∣ a) (hbu : ¬ (p : ℤ) ∣ b) (hcu : ¬ (p : ℤ) ∣ c)
    (heq : 4 * a * b * c = (p : ℤ) * b * c + a * (b + c)) :
    jacobiSym (b * c) p = -1 ↔ 0 < b ∧ 0 < c := by
  let R : ℤ := 4 * b - 1
  let d : ℤ := R * a - (p : ℤ) * b
  have hP : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpo : Odd p := Nat.odd_iff.mpr (by omega)
  have hb0 : b ≠ 0 := by intro h; apply hbu; simp [h]
  have hc0 : c ≠ 0 := by intro h; apply hcu; simp [h]
  have hRc : (p : ℤ) ∣ R * c - b := by
    have h : (p : ℤ) ∣ a * (R * c - b) := by
      refine ⟨b * c, ?_⟩
      dsimp [R]
      nlinarith only [heq]
    exact (hP.dvd_mul.mp h).resolve_left hau
  have hRu : ¬ (p : ℤ) ∣ R := by
    intro h
    have hb := dvd_sub (dvd_mul_of_dvd_left h c) hRc
    apply hbu
    convert hb using 1 <;> ring
  have hdu : ¬ (p : ℤ) ∣ d := by
    intro h
    have hRa : (p : ℤ) ∣ R * a := by
      have h' := dvd_add h (dvd_mul_right (p : ℤ) b)
      convert h' using 1 <;> dsimp [d] <;> ring
    exact (hP.dvd_mul.mp hRa).elim hRu hau
  have hdc : d * c = a * b := by dsimp [d, R]; nlinarith only [heq]
  have hd0 : d ≠ 0 := by
    intro h
    have hab : a * b ≠ 0 := mul_ne_zero (ne_of_gt ha) hb0
    apply hab
    simpa [h] using hdc.symm
  have hddiv : d ∣ b ^ 2 := by
    apply ((hP.coprime_iff_not_dvd.mpr hdu).symm).dvd_of_dvd_mul_left
    refine ⟨R * c - b, ?_⟩
    dsimp [d, R]
    nlinarith only [congrArg (fun x : ℤ => x * (4 * b - 1)) heq]
  have hJabs := abs_jacobi_of_square_dvd hd0 hddiv
  have hR4 : R % 4 = 3 := by dsimp [R]; omega
  have hR0 : R ≠ 0 := by omega
  have hNabs : (R.natAbs : ℤ) = |R| := Int.natCast_natAbs R
  have hNo : Odd R.natAbs := by
    apply Nat.odd_iff.mpr
    have : (R.natAbs : ℤ) % 2 = 1 := by
      by_cases h : 0 ≤ R
      · rw [abs_of_nonneg h] at hNabs; omega
      · rw [abs_of_neg (by omega)] at hNabs; omega
    exact_mod_cast this
  have hrec : jacobiSym R p = jacobiSym (p : ℤ) R.natAbs := by
    have h := jacobiSym.quadratic_reciprocity_one_mod_four hp4 hNo
    have hab : jacobiSym (R.natAbs : ℤ) p = jacobiSym R p := by
      rw [hNabs]
      by_cases hR : 0 ≤ R
      · rw [abs_of_nonneg hR]
      · rw [abs_of_neg (by omega), jacobiSym.neg R hpo,
          ZMod.χ₄_nat_one_mod_four hp4, one_mul]
    exact hab.symm.trans h.symm
  have hbc : jacobiSym (b * c) p = jacobiSym R p := by
    have hsq := jacobiSym.sq_one
      (Int.isCoprime_iff_gcd_eq_one.mp (hP.coprime_iff_not_dvd.mpr hcu).symm)
    have hcong : jacobiSym (b * c) p = jacobiSym (R * c ^ 2) p := by
      apply jacobi_congr_of_dvd_sub
      convert dvd_mul_of_dvd_left hRc (-c) using 1 <;> ring
    rw [hcong, jacobiSym.mul_left, jacobiSym.pow_left, hsq, mul_one]
  have hdcong : jacobiSym d R.natAbs = jacobiSym (-((p : ℤ) * b)) R.natAbs := by
    apply jacobi_congr_of_dvd_sub
    apply Int.natAbs_dvd.mpr
    refine ⟨a, ?_⟩
    dsimp [d]; ring
  rw [hbc, hrec]
  by_cases hb : 0 < b
  · have hRp : 0 < R := by dsimp [R]; omega
    have hN4 : R.natAbs % 4 = 3 := by
      rw [abs_of_pos hRp] at hNabs
      have : (R.natAbs : ℤ) % 4 = 3 := by omega
      exact_mod_cast this
    have hJb : jacobiSym b R.natAbs = 1 := by
      simpa [R] using jacobi_positive_linear (m := b) (n := 1) hb
    rw [jacobiSym.neg _ hNo, ZMod.χ₄_nat_three_mod_four hN4,
      jacobiSym.mul_left, hJb, mul_one] at hdcong
    by_cases hc : 0 < c
    · have hdp : 0 < d := (mul_pos_iff_of_pos_right hc).mp (by rw [hdc]; positivity)
      have hJd : jacobiSym d R.natAbs = 1 := by
        simpa only [Int.natCast_natAbs, abs_of_pos hdp] using hJabs
      constructor
      · intro _; exact ⟨hb, hc⟩
      · intro _; linarith only [hdcong, hJd]
    · have hcn : c < 0 := by omega
      have hdn : d < 0 := by
        by_contra h
        have hnon := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ d by omega) hcn.le
        have hpos : 0 < a * b := mul_pos ha hb
        rw [hdc] at hnon
        omega
      have hJd : jacobiSym d R.natAbs = -1 := by
        have hab : (d.natAbs : ℤ) = -d := by rw [Int.natCast_natAbs, abs_of_neg hdn]
        rw [hab, jacobiSym.neg _ hNo, ZMod.χ₄_nat_three_mod_four hN4] at hJabs
        linarith only [hJabs]
      constructor
      · intro h; linarith only [h, hdcong, hJd]
      · intro h; exact False.elim (hc h.2)
  · have hbn : b < 0 := by omega
    have hRn : R < 0 := by dsimp [R]; omega
    have hN4 : R.natAbs % 4 = 1 := by
      rw [abs_of_neg hRn] at hNabs
      have : (R.natAbs : ℤ) % 4 = 1 := by omega
      exact_mod_cast this
    have hJb : jacobiSym b R.natAbs = 1 := by
      have hJ := jacobi_positive_linear (m := -b) (n := -1) (by omega)
      have he : 4 * (-b) * (-1) - 1 = R := by dsimp [R]; ring
      rw [he, jacobiSym.neg _ hNo, ZMod.χ₄_nat_one_mod_four hN4, one_mul] at hJ
      exact hJ
    have hJd : jacobiSym d R.natAbs = 1 := by
      rcases Int.natAbs_eq d with h | h
      · simpa only [← h] using hJabs
      · calc
          jacobiSym d R.natAbs = jacobiSym (-(d.natAbs : ℤ)) R.natAbs :=
            congrArg (fun z : ℤ => jacobiSym z R.natAbs) h
          _ = 1 := by rw [jacobiSym.neg _ hNo, ZMod.χ₄_nat_one_mod_four hN4, hJabs, one_mul]
    rw [jacobiSym.neg _ hNo, ZMod.χ₄_nat_one_mod_four hN4,
      jacobiSym.mul_left, hJb, mul_one, one_mul] at hdcong
    constructor
    · intro h; linarith only [h, hdcong, hJd]
    · intro h; exact False.elim (hb h.1)

/-- In the exact signed-core interval, a Type II cofactor is a p-unit. -/
lemma cofactor_unit_left {p : ℕ} {a b c : ℤ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (ha : 0 < a) (ha2 : 2 * a < p) (hau : ¬ (p : ℤ) ∣ a)
    (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (heq : 4 * a * b * c = (p : ℤ) * b * c + a * (b + c)) :
    ¬ (p : ℤ) ∣ b := by
  intro hpb
  have hP : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpc : (p : ℤ) ∣ c := by
    have hsum : (p : ℤ) ∣ a * (b + c) := by
      have hleft : (p : ℤ) ∣ 4 * a * b * c :=
        dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpb (4 * a)) c
      have hright : (p : ℤ) ∣ (p : ℤ) * b * c := by exact ⟨b*c, by ring⟩
      have h := dvd_sub hleft hright
      convert h using 1 <;> nlinarith only [heq]
    have hbc := (hP.dvd_mul.mp hsum).resolve_left hau
    have h := dvd_sub hbc hpb
    simpa using h
  have hbp : (p : ℤ) ≤ |b| := Int.le_of_dvd (abs_pos.mpr hb0) ((dvd_abs _ _).mpr hpb)
  have hcp : (p : ℤ) ≤ |c| := Int.le_of_dvd (abs_pos.mpr hc0) ((dvd_abs _ _).mpr hpc)
  have hp4z : (p : ℤ) % 4 = 1 := by exact_mod_cast hp4
  have hq0 : 4 * a - (p : ℤ) ≠ 0 := by omega
  have hq : 1 ≤ |4 * a - (p : ℤ)| := by have := abs_pos.mpr hq0; omega
  have he : (4 * a - (p : ℤ)) * b * c = a * (b + c) := by nlinarith only [heq]
  have heabs := congrArg abs he
  simp only [abs_mul, abs_of_pos ha] at heabs
  have hsum := mul_le_mul_of_nonneg_left (abs_add_le b c) ha.le
  have h1 := mul_lt_mul_of_pos_left (show 2 * a < |b| by omega) (abs_pos.mpr hc0)
  have h2 := mul_lt_mul_of_pos_left (show 2 * a < |c| by omega) (abs_pos.mpr hb0)
  have h3 := mul_le_mul_of_nonneg_right hq (mul_nonneg (abs_nonneg b) (abs_nonneg c))
  nlinarith only [heabs, hsum, h1, h2, h3]

/-- Type II sign law for actual signed triples in the proved prime core. -/
lemma signed_typeII_character {p : ℕ} {k a b c : ℤ} (H : Context p k)
    (s : SignedSolution p a ((p : ℤ) * b) ((p : ℤ) * c))
    (hau : UnitCoord p a) :
    jacobiSym (b * c) p = -1 ↔ 0 < a ∧ 0 < b ∧ 0 < c := by
  have hacore := typeII_core H s
  have ha : 0 < a := by have := hacore.1; omega
  have ha2 : 2 * a < (p : ℤ) := by have := hacore.2; have := H.formula; omega
  have hb0 : b ≠ 0 := by intro h; exact s.y_ne (by simp [h])
  have hc0 : c ≠ 0 := by intro h; exact s.z_ne (by simp [h])
  have hp0 : (p : ℤ) ≠ 0 := ne_of_gt H.p_pos
  have heq : 4 * a * b * c = (p : ℤ) * b * c + a * (b + c) := by
    apply mul_left_cancel₀ (mul_ne_zero hp0 hp0)
    nlinarith only [s.equation]
  have hbu := cofactor_unit_left H.prime H.p4 ha ha2 hau hb0 hc0 heq
  have hcu := cofactor_unit_left H.prime H.p4 ha ha2 hau hc0 hb0
    (show 4 * a * c * b = (p : ℤ) * c * b + a * (c + b) by nlinarith only [heq])
  rw [character_iff_positive H.prime H.p4 ha hau hbu hcu heq]
  exact ⟨fun h => ⟨ha, h⟩, fun h => h.2⟩

#print axioms jacobi_divisor_square_linear
#print axioms abs_jacobi_of_square_dvd
#print axioms character_iff_positive
#print axioms cofactor_unit_left
#print axioms signed_typeII_character
end Erdos242.Development.TypeIISign
