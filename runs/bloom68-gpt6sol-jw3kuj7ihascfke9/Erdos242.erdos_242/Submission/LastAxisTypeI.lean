import Submission.Classification

/-!
# An exact last-denominator factor test for full Type I

This extends the restricted `c ∣ x` auxiliary factor test to the full
`c ∣ x²` condition. It does not prove an Erdős–Straus decomposition for
all primes. It neither imports nor modifies `Submission/Spec.lean`.
-/

namespace Erdos242

/-- A square divisor of the auxiliary number `M=(hp+1)/4` in the
integrality class for a two-unit-fraction split. Unlike the restricted
auxiliary test, `c` need not divide `M`: it need only divide `M²`. -/
def LastAxisTypeI (p : ℕ) : Prop :=
  ∃ h M c : ℕ, 0 < h ∧ 4 * M = h * p + 1 ∧
    0 < c ∧ c < M ∧ c ∣ M ^ 2 ∧ h ∣ M + c

/-- Every full Type-I certificate has an auxiliary square-divisor test.
The numerator need not be prime. -/
theorem lastAxisTypeI_of_typeI (p x : ℕ) (hlo : p < 4 * x)
    (hhi : 2 * x < p) (hI : TypeI p x) : LastAxisTypeI p := by
  obtain ⟨c, hc, hcx, hac⟩ := hI
  let a := 4 * x - p
  have ha : 0 < a := by dsimp [a]; omega
  have haeq : a + p = 4 * x := by dsimp [a]; omega
  have halt : a < 2 * x := by dsimp [a]; omega
  obtain ⟨h, hh⟩ := hac
  have hh' : h * a = 4 * c + 1 := by nlinarith [hh]
  have hhpos : 0 < h := by
    by_contra hn
    have : h = 0 := by omega
    simp [this] at hh'
  have hax : h * a < h * (2 * x) := Nat.mul_lt_mul_of_pos_left halt hhpos
  have hxc : 2 * c < h * x := by nlinarith [hh', hax]
  let M := h * x - c
  have hMc : M + c = h * x := Nat.sub_add_cancel (by omega)
  have hcM : c < M := by dsimp [M]; omega
  have hM : 4 * M = h * p + 1 := by
    have heq := congrArg (fun t : ℕ => h * t) haeq
    nlinarith [hh', hMc, heq]
  have hcHx : c ∣ (h * x) ^ 2 := by
    simpa only [mul_pow] using hcx.mul_left (h ^ 2)
  have hcMc : c ∣ (M + c) ^ 2 := by rw [hMc]; exact hcHx
  have hcCross : c ∣ c * (2 * M + c) := dvd_mul_right c _
  have hsq : (M + c) ^ 2 = M ^ 2 + c * (2 * M + c) := by ring
  rw [hsq] at hcMc
  have hcM2 : c ∣ M ^ 2 :=
    (Nat.dvd_add_iff_left hcCross).mpr hcMc
  refine ⟨h, M, c, hhpos, hM, hc, hcM, hcM2, ?_⟩
  rw [hMc]
  exact dvd_mul_right h x

/-- Conversely, the auxiliary square-divisor condition implies the *full*
Type-I certificate with first denominator `(M+c)/h`. -/
theorem typeI_of_lastAxisTypeI (p h M c : ℕ)
    (hh : 0 < h) (hM : 4 * M = h * p + 1) (hc : 0 < c)
    (hcM : c < M) (hcM2 : c ∣ M ^ 2) (hdiv : h ∣ M + c) :
    ∃ x : ℕ, p < 4 * x ∧ 2 * x < p ∧ TypeI p x ∧ h * x = M + c := by
  have hcopM : h.Coprime M := by
    apply Nat.coprime_of_dvd
    intro q hq hqh hqM
    have hqhp : q ∣ h * p := hqh.mul_right p
    have hq4M : q ∣ 4 * M := hqM.mul_left 4
    have hqhp1 : q ∣ h * p + 1 := by rw [← hM]; exact hq4M
    have hqone : q ∣ 1 := (Nat.dvd_add_iff_right hqhp).mpr hqhp1
    exact (ne_of_gt hq.one_lt) (Nat.dvd_one.mp hqone)
  have hcopC : h.Coprime c := (hcopM.pow_right 2).of_dvd_right hcM2
  obtain ⟨x, hx⟩ := hdiv
  have hx' : h * x = M + c := by simpa only [mul_comm] using hx.symm
  have hrelation : h * (4 * x) = h * p + 4 * c + 1 := by
    nlinarith [hM, hx']
  have hlo : p < 4 * x := by
    by_contra hn
    have hle : 4 * x ≤ p := by omega
    have hprod : h * (4 * x) ≤ h * p := Nat.mul_le_mul_left h hle
    omega
  have hle : 2 * x ≤ p := by
    have hineq : 2 * (h * x) < h * p + 1 := by
      nlinarith [hM, hx', hcM]
    by_contra hn
    have hlt : p < 2 * x := by omega
    have hprod : h * p < h * (2 * x) := Nat.mul_lt_mul_of_pos_left hlt hh
    have hprod' : h * p < 2 * (h * x) := by nlinarith only [hprod]
    omega
  have hne : 2 * x ≠ p := by
    intro heq
    have hparity : 2 * (h * x) = 4 * c + 1 := by
      nlinarith [hrelation, heq]
    omega
  have hhi : 2 * x < p := by omega
  obtain ⟨e, he⟩ := hcM2
  have hsq : (h * x) ^ 2 = c * (e + 2 * M + c) := by
    nlinarith [he, hx']
  have hcHx : c ∣ (h * x) ^ 2 := ⟨e + 2 * M + c, hsq⟩
  have hcHx2 : c ∣ h ^ 2 * x ^ 2 := by simpa only [mul_pow] using hcHx
  have hcopCh : c.Coprime (h ^ 2) := hcopC.symm.pow_right 2
  have hcx : c ∣ x ^ 2 := hcopCh.dvd_of_dvd_mul_left hcHx2
  have ha : 0 < 4 * x - p := by omega
  have haeq : (4 * x - p) + p = 4 * x := by omega
  have hac : (4 * x - p) ∣ 4 * c + 1 := by
    refine ⟨h, ?_⟩
    have heq := congrArg (fun t : ℕ => h * t) haeq
    nlinarith [hrelation, heq]
  exact ⟨x, hlo, hhi, ⟨c, hc, hcx, hac⟩, hx'⟩

/-- The `c ∣ M²` auxiliary criterion is exactly equivalent to the
existence of a full Type-I certificate in the ordered first-denominator
range. No primality hypothesis is needed. -/
theorem lastAxisTypeI_iff_typeI (p : ℕ) :
    LastAxisTypeI p ↔ ∃ x : ℕ, p < 4 * x ∧ 2 * x < p ∧ TypeI p x := by
  constructor
  · rintro ⟨h, M, c, hh, hM, hc, hcM, hcM2, hdiv⟩
    obtain ⟨x, hlo, hhi, hI, _⟩ :=
      typeI_of_lastAxisTypeI p h M c hh hM hc hcM hcM2 hdiv
    exact ⟨x, hlo, hhi, hI⟩
  · rintro ⟨x, hlo, hhi, hI⟩
    exact lastAxisTypeI_of_typeI p x hlo hhi hI

/-- Replace the *full* Type-I alternative in the existing prime
classification by the last-axis square-divisor criterion. The Type-II
alternative must still be retained. -/
theorem good_iff_lastAxisTypeI_or_typeII (p : ℕ) (hp : p.Prime)
    (hgt : 2 < p) :
    Good p ↔ LastAxisTypeI p ∨
      ∃ x : ℕ, p < 4 * x ∧ 2 * x < p ∧ TypeII p x := by
  rw [good_iff_ordered_divisors p hp hgt, lastAxisTypeI_iff_typeI]
  constructor
  · rintro ⟨x, hlo, hhi, hI | hII⟩
    · exact Or.inl ⟨x, hlo, hhi, hI⟩
    · exact Or.inr ⟨x, hlo, hhi, hII⟩
  · rintro (⟨x, hlo, hhi, hI⟩ | ⟨x, hlo, hhi, hII⟩)
    · exact ⟨x, hlo, hhi, Or.inl hI⟩
    · exact ⟨x, hlo, hhi, Or.inr hII⟩

/-- For an ordered prime solution with last denominator `p*w`, the middle
one is non-`p`-divisible exactly when `4*w-1` is divisible by `p`.
This condition distinguishes the two branches without assuming Type I or II
in advance. -/
theorem prime_not_dvd_middle_iff_last_residue (p x y w : ℕ)
    (hp : p.Prime) (hgt : 2 < p) (hx : 0 < x)
    (hxy : x < y) (hyz : y < p * w)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / (p * w)) :
    (¬p ∣ y) ↔ p ∣ 4 * w - 1 := by
  have heq' : (4 / p : ℚ) = 1 / x + 1 / y + 1 / (p * w : ℕ) := by
    simpa only [Nat.cast_mul] using heq
  have hxltp : x < p := by
    have hbound := ordered_solution_bounds p x y (p * w) hp hgt hx hxy hyz heq'
    omega
  have hnotx : ¬p ∣ x := Nat.not_dvd_of_pos_of_lt hx hxltp
  have hwpos : 0 < w := by
    by_contra hn
    have hw : w = 0 := by omega
    simp [hw] at hyz
  have hpoly : 4 * x * y * (p * w) =
      p * (x * y + x * (p * w) + y * (p * w)) := by
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    have hxq : (x : ℚ) ≠ 0 := by exact_mod_cast (by omega : x ≠ 0)
    have hyq : (y : ℚ) ≠ 0 := by exact_mod_cast (by omega : y ≠ 0)
    have hzq : ((p * w : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (by positivity : p * w ≠ 0)
    have hf : (4 / p : ℚ) = 1 / x + 1 / y + 1 / (p * w : ℕ) ↔
        4 * (x : ℚ) * y * (p * w) =
          p * (x * y + x * (p * w) + y * (p * w)) := by
      simp only [Nat.cast_mul]
      field_simp
      constructor <;> intro h <;> nlinarith [h]
    exact_mod_cast hf.mp heq'
  have hcancel : 4 * x * y * w = x * y + p * w * (x + y) := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < p)
    nlinarith only [hpoly]
  let r := 4 * w - 1
  have hr : r + 1 = 4 * w := by dsimp [r]; omega
  have hrel : r * x * y = p * w * (x + y) := by
    have hmul := congrArg (fun t : ℕ => t * x * y) hr
    nlinarith only [hcancel, hmul]
  constructor
  · intro hnoty
    have hprxy : p ∣ r * (x * y) := by
      rw [show r * (x * y) = r * x * y by ring, hrel]
      exact ⟨w * (x + y), by ring⟩
    rcases (hp.dvd_mul).mp hprxy with hpr | hpxy
    · exact hpr
    · rcases (hp.dvd_mul).mp hpxy with hpx | hpy
      · exact False.elim (hnotx hpx)
      · exact False.elim (hnoty hpy)
  · intro hpr
    have hpr' : p ∣ r := hpr
    have hnotw : ¬p ∣ w := by
      intro hpw
      have hpd4w : p ∣ 4 * w := hpw.mul_left 4
      have hpd1 : p ∣ 1 := (Nat.dvd_add_iff_right hpr').mpr (by
        rw [hr]
        exact hpd4w)
      have hp1 : p = 1 := Nat.dvd_one.mp hpd1
      omega
    intro hpy
    have hpwy : p ∣ w * y := hpy.mul_left w
    obtain ⟨t, ht⟩ := hpr'
    obtain ⟨m, hm⟩ := hpy
    have hred : t * x * (p * m) = w * (x + p * m) := by
      apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < p)
      rw [ht, hm] at hrel
      nlinarith only [hrel]
    have hpwxy : p ∣ w * (x + y) := by
      rw [hm, ← hred]
      exact ⟨t * x * m, by ring⟩
    have hpwx : p ∣ w * x := by
      have hadd : p ∣ w * x + w * y := by
        simpa only [mul_add] using hpwxy
      exact (Nat.dvd_add_iff_left hpwy).mpr hadd
    rcases (hp.dvd_mul).mp hpwx with hpw | hpx
    · exact hnotw hpw
    · exact hnotx hpx

/-- Every ordered prime solution has last denominator `p*w` and satisfies
the exact middle-denominator/residue separation above. -/
theorem ordered_last_residue_dichotomy (p x y z : ℕ)
    (hp : p.Prime) (hgt : 2 < p) (hx : 0 < x)
    (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) :
    ∃ w : ℕ, z = p * w ∧ ((¬p ∣ y) ↔ p ∣ 4 * w - 1) := by
  obtain ⟨w, hw⟩ :=
    (ordered_solution_bounds p x y z hp hgt hx hxy hyz heq).2.2
  subst z
  have heq' : (4 / p : ℚ) = 1 / x + 1 / y + 1 / (p * w) := by
    simpa only [Nat.cast_mul] using heq
  exact ⟨w, rfl, prime_not_dvd_middle_iff_last_residue p x y w hp hgt hx hxy hyz heq'⟩


/-- At this particular last denominator, the displayed certificate has
`c=40 ∣ 420²` but `40 ∤ 420`. See `LastAxisTypeI.md` for the finite
check excluding *all* restricted `c ∣ 420` at this fixed `h=23`. -/
theorem lastAxisTypeI_73_h23 : LastAxisTypeI 73 := by
  refine ⟨23, 420, 40, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_, ?_⟩
  · norm_num
  · norm_num

theorem lastAxisTypeI_193_h3 : LastAxisTypeI 193 := by
  refine ⟨3, 145, 5, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_, ?_⟩
  · norm_num
  · norm_num

theorem lastAxisTypeI_2521_h15 : LastAxisTypeI 2521 := by
  refine ⟨15, 9454, 326, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_, ?_⟩
  · norm_num
  · norm_num

/-- Exact-rational ordered examples independently checking the integrality
and order of the denominators supplied by the auxiliary certificates. -/
theorem good_193_lastAxis_explicit : Good 193 := by
  refine ⟨50, 1450, 27985, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

theorem good_2521_lastAxis_explicit : Good 2521 := by
  refine ⟨652, 18908, 23833534, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

end Erdos242
