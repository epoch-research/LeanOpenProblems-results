import FormalConjectures.Util.ProblemImports

open Int Zsqrtd

abbrev ZsqrtNegTwo : Type := ℤ√(-2)

local notation "R" => ZsqrtNegTwo

namespace ZsqrtNegTwo

instance instCommRing : CommRing R := Zsqrtd.commRing
instance instNontrivial : Nontrivial R := ⟨⟨0, 1, by decide⟩⟩

lemma norm_formula (z : R) : z.norm = z.re * z.re + 2 * z.im * z.im := by
  simp [Zsqrtd.norm]

lemma norm_nonneg' (z : R) : 0 ≤ z.norm :=
  Zsqrtd.norm_nonneg (by decide : (-2 : ℤ) ≤ 0) z

lemma norm_eq_zero_iff' (z : R) : z.norm = 0 ↔ z = 0 :=
  Zsqrtd.norm_eq_zero_iff (by decide : (-2 : ℤ) < 0) z

lemma norm_pos_of_ne_zero {z : R} (hz : z ≠ 0) : 0 < z.norm :=
  lt_of_le_of_ne (norm_nonneg' z) (Ne.symm ((norm_eq_zero_iff' z).not.mpr hz))

end ZsqrtNegTwo

namespace ZsqrtNegTwo

/-- Division by rounding both coordinates in the `{1, √-2}` basis. -/
noncomputable instance : Div R :=
  ⟨fun x y =>
    ⟨round (((x * star y).re : ℚ) / y.norm),
     round (((x * star y).im : ℚ) / y.norm)⟩⟩

lemma div_def (x y : R) :
    x / y = ⟨round (((x * star y).re : ℚ) / y.norm),
             round (((x * star y).im : ℚ) / y.norm)⟩ :=
  rfl

noncomputable instance : Mod R :=
  ⟨fun x y => x - y * (x / y)⟩

lemma mod_def (x y : R) : x % y = x - y * (x / y) := rfl

lemma sq_le_half_sq {δ : ℚ} (h : |δ| ≤ 1 / 2) : δ ^ 2 ≤ (1 / 4 : ℚ) := by
  have h1 : |δ| ≤ |(1 / 2 : ℚ)| := by simpa using h
  have h2 : δ ^ 2 ≤ (1 / 2 : ℚ) ^ 2 := (sq_le_sq (a := δ) (b := (1 / 2 : ℚ))).mpr h1
  nlinarith

lemma err_form_le (α β : ℚ) :
    let δα := α - (round α : ℚ)
    let δβ := β - (round β : ℚ)
    δα ^ 2 + 2 * δβ ^ 2 ≤ (3 / 4 : ℚ) := by
  intro δα δβ
  have hα : |δα| ≤ 1 / 2 := abs_sub_round α
  have hβ : |δβ| ≤ 1 / 2 := abs_sub_round β
  have h1 : δα ^ 2 ≤ (1 / 4 : ℚ) := sq_le_half_sq hα
  have h2 : δβ ^ 2 ≤ (1 / 4 : ℚ) := sq_le_half_sq hβ
  nlinarith

end ZsqrtNegTwo

namespace ZsqrtNegTwo

lemma mul_star_self (y : R) : y * star y = ⟨y.norm, 0⟩ := by
  rw [← Zsqrtd.intCast_val, Zsqrtd.norm_eq_mul_conj]

lemma rem_mul_star_re (x y : R) :
    ((x % y) * star y).re = (x * star y).re - (x / y).re * y.norm := by
  have h : (x - y * (x / y)) * star y = x * star y - (x / y) * (y * star y) := by
    ring
  rw [mod_def, h, mul_star_self]
  simp [Zsqrtd.re_mul]

lemma rem_mul_star_im (x y : R) :
    ((x % y) * star y).im = (x * star y).im - (x / y).im * y.norm := by
  have h : (x - y * (x / y)) * star y = x * star y - (x / y) * (y * star y) := by
    ring
  rw [mod_def, h, mul_star_self]
  simp [Zsqrtd.im_mul]

end ZsqrtNegTwo

namespace ZsqrtNegTwo

lemma rem_norm_identity (x y : R) (hy : y ≠ 0) :
    ((x % y).norm : ℚ) =
      (y.norm : ℚ) *
        ((((x * star y).re : ℚ) / y.norm - ((x / y).re : ℚ)) ^ 2 +
         2 * (((x * star y).im : ℚ) / y.norm - ((x / y).im : ℚ)) ^ 2) := by
  have hyN : y.norm ≠ 0 := (norm_eq_zero_iff' y).not.mpr hy
  have hyNq : (y.norm : ℚ) ≠ 0 := by exact_mod_cast hyN
  have nmul : ((x % y) * star y).norm = (x % y).norm * y.norm := by
    rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj]
  have lhs : (((x % y) * star y).norm : ℚ) =
      (((x % y) * star y).re : ℚ) ^ 2 + 2 * (((x % y) * star y).im : ℚ) ^ 2 := by
    simp [norm_formula]; ring
  have re_eq : (((x % y) * star y).re : ℚ) =
      (y.norm : ℚ) * (((x * star y).re : ℚ) / y.norm - ((x / y).re : ℚ)) := by
    rw [rem_mul_star_re]
    push_cast
    field_simp [hyNq]
  have im_eq : (((x % y) * star y).im : ℚ) =
      (y.norm : ℚ) * (((x * star y).im : ℚ) / y.norm - ((x / y).im : ℚ)) := by
    rw [rem_mul_star_im]
    push_cast
    field_simp [hyNq]
  have hprod : (((x % y) * star y).norm : ℚ) =
      (y.norm : ℚ) ^ 2 *
        ((((x * star y).re : ℚ) / y.norm - ((x / y).re : ℚ)) ^ 2 +
         2 * (((x * star y).im : ℚ) / y.norm - ((x / y).im : ℚ)) ^ 2) := by
    rw [lhs, re_eq, im_eq]
    ring
  have nmulQ : (((x % y) * star y).norm : ℚ) = ((x % y).norm : ℚ) * y.norm := by
    exact_mod_cast nmul
  have hmul : ((x % y).norm : ℚ) * y.norm =
      (y.norm : ℚ) ^ 2 *
        ((((x * star y).re : ℚ) / y.norm - ((x / y).re : ℚ)) ^ 2 +
         2 * (((x * star y).im : ℚ) / y.norm - ((x / y).im : ℚ)) ^ 2) := by
    linarith
  apply (mul_right_inj' hyNq).mp
  linarith [hmul]

lemma div_re (x y : R) :
    ((x / y).re : ℚ) = round (((x * star y).re : ℚ) / y.norm) := by
  simp [div_def]

lemma div_im (x y : R) :
    ((x / y).im : ℚ) = round (((x * star y).im : ℚ) / y.norm) := by
  simp [div_def]

lemma norm_mod_lt (x : R) {y : R} (hy : y ≠ 0) : (x % y).norm < y.norm := by
  have hyNpos : 0 < y.norm := norm_pos_of_ne_zero hy
  set α : ℚ := (x * star y).re / y.norm
  set β : ℚ := (x * star y).im / y.norm
  have hid := rem_norm_identity x y hy
  have hqre : ((x / y).re : ℚ) = round α := by simp [div_re, α]
  have hqim : ((x / y).im : ℚ) = round β := by simp [div_im, β]
  have hQle : (α - (round α : ℚ)) ^ 2 + 2 * (β - (round β : ℚ)) ^ 2 ≤ (3 / 4 : ℚ) :=
    err_form_le α β
  have : ((x % y).norm : ℚ) =
      (y.norm : ℚ) * ((α - ((x / y).re : ℚ)) ^ 2 + 2 * (β - ((x / y).im : ℚ)) ^ 2) := by
    simpa [α, β] using hid
  have hle : ((x % y).norm : ℚ) ≤ (y.norm : ℚ) * (3 / 4) := by
    rw [this, hqre, hqim]
    have : 0 ≤ (y.norm : ℚ) := by exact_mod_cast (norm_nonneg' y)
    nlinarith [hQle]
  have hlt : ((x % y).norm : ℚ) < (y.norm : ℚ) := by
    have hypos : (0 : ℚ) < y.norm := by exact_mod_cast hyNpos
    nlinarith
  exact_mod_cast hlt

lemma natAbs_norm_mod_lt (x : R) {y : R} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  have h := norm_mod_lt x hy
  have h1 : 0 ≤ (x % y).norm := norm_nonneg' _
  have h2 : 0 ≤ y.norm := norm_nonneg' _
  exact Int.ofNat_lt.mp (by simpa [Int.natAbs_of_nonneg h1, Int.natAbs_of_nonneg h2] using h)

lemma norm_le_norm_mul_left (x : R) {y : R} (hy : y ≠ 0) :
    x.norm.natAbs ≤ (x * y).norm.natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  refine le_mul_of_one_le_right (Nat.zero_le _) ?_
  have ypos : 0 < y.norm := norm_pos_of_ne_zero hy
  have hnn : 0 ≤ y.norm := norm_nonneg' y
  have h1 : (1 : ℤ) ≤ y.norm := Int.add_one_le_of_lt ypos
  have : 1 ≤ y.norm.natAbs := by
    rw [← Int.natAbs_of_nonneg hnn] at h1
    exact_mod_cast h1
  exact this

noncomputable instance : EuclideanDomain R :=
  { ZsqrtNegTwo.instCommRing,
    ZsqrtNegTwo.instNontrivial with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by
      intro a
      simp [div_def]
      rfl
    quotient_mul_add_remainder_eq := fun _ _ => by simp [mod_def]
    r := fun a b => a.norm.natAbs < b.norm.natAbs
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun a _ hb0 => not_lt_of_ge <| norm_le_norm_mul_left a hb0 }

end ZsqrtNegTwo

namespace ZsqrtNegTwo

open scoped Classical

lemma units_iff (z : R) : IsUnit z ↔ z.norm = 1 := by
  constructor
  · intro h
    have := (Zsqrtd.norm_eq_one_iff' (by decide : (-2 : ℤ) ≤ 0) z).mpr h
    exact this
  · intro h
    exact (Zsqrtd.norm_eq_one_iff' (by decide : (-2 : ℤ) ≤ 0) z).mp h

lemma units_eq : ∀ z : R, IsUnit z → z = 1 ∨ z = -1 := by
  intro z hz
  have hn : z.norm = 1 := (units_iff z).mp hz
  rw [norm_formula] at hn
  have hre : z.re * z.re ≤ 1 := by nlinarith [mul_self_nonneg z.im]
  have : z.re = 1 ∨ z.re = -1 ∨ z.re = 0 := by
    have : z.re ≤ 1 ∧ -1 ≤ z.re := by
      nlinarith [mul_self_nonneg z.re]
    interval_cases z.re <;> simp_all
  rcases this with h | h | h
  · have : z.im = 0 := by nlinarith [mul_self_nonneg z.im, hn, h]
    apply_fun (fun t => (t.re, t.im))
    · simp [h, this]
    · exact fun _ _ h => Zsqrtd.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  · have : z.im = 0 := by nlinarith [mul_self_nonneg z.im, hn, h]
    right
    apply Zsqrtd.ext <;> simp [h, this]
  · have : 2 * z.im * z.im = 1 := by nlinarith [hn, h]
    have : (2 : ℤ) ∣ 1 := ⟨z.im * z.im, by linarith⟩
    exact (by decide : ¬(2 : ℤ) ∣ 1) this

lemma exists_sq_add_two_sq_of_not_irreducible (p : ℕ) [hp : Fact p.Prime]
    (hpi : ¬Irreducible (p : R)) : ∃ a b : ℤ, a ^ 2 + 2 * b ^ 2 = p := by
  have hpu : ¬IsUnit (p : R) := by
    intro hu
    have : (p : R).norm = 1 := (units_iff _).mp hu
    have : (p : ℤ) * p = 1 := by
      simpa [Zsqrtd.norm_natCast] using this
    have : p = 1 := by
      have : p * p = 1 := by exact_mod_cast this
      nlinarith [hp.out.one_lt]
    exact (ne_of_gt hp.out.one_lt) this
  have hab : ∃ a b : R, (p : R) = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
    simpa [irreducible_iff, hpu, not_forall, not_or] using hpi
  obtain ⟨a, b, hpab, hau, hbu⟩ := hab
  have hnap : a.norm.natAbs = p := by
    have := (hp.out.mul_eq_prime_sq_iff
      (mt (units_iff a).mpr hau) (mt (units_iff b).mpr hbu)).1 ?_
    · exact this.1
    · have : (p : R).norm.natAbs = p * p := by
        simp [Zsqrtd.norm_natCast, Int.natAbs_mul, sq]
      rw [← this, hpab, Zsqrtd.norm_mul, Int.natAbs_mul]
      ring
  refine ⟨a.re, a.im, ?_⟩
  have : a.norm = a.re * a.re + 2 * a.im * a.im := norm_formula a
  have hnn : 0 ≤ a.norm := norm_nonneg' a
  have : a.norm = p := by
    rw [← Int.natAbs_of_nonneg hnn, hnap]
    simp
  linarith

lemma odd_prime_splits_of_mod_eight {p : ℕ} [hp : Fact p.Prime] (h2 : p ≠ 2)
    (hm : p % 8 = 1 ∨ p % 8 = 3) : ¬Irreducible (p : R) := by
  have hsq : IsSquare (-2 : ZMod p) := (ZMod.exists_sq_eq_neg_two_iff h2).2 hm
  obtain ⟨x, hx⟩ := hsq
  let a : ℤ := x.val
  have ha : (a : ZMod p) = x := by simp [a]
  have hdiv : (p : ℤ) ∣ a ^ 2 + 2 := by
    have : (a : ZMod p) ^ 2 + 2 = 0 := by
      rw [ha, hx]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by simpa using this)
  have hfac : (⟨a, 1⟩ * ⟨a, -1⟩ : R) = ⟨a ^ 2 + 2, 0⟩ := by
    ext <;> simp [Zsqrtd.mul_re, Zsqrtd.mul_im]; ring
  have hpdiv : (p : R) ∣ ⟨a, 1⟩ * ⟨a, -1⟩ := by
    refine ⟨⟨a ^ 2 + 2, 0⟩ / p, ?_⟩
    -- better: use integer divisibility
    have : (⟨a ^ 2 + 2, 0⟩ : R) = (p : R) * ⟨(a ^ 2 + 2) / p, 0⟩ := by
      obtain ⟨k, hk⟩ := hdiv
      ext <;> simp [Zsqrtd.natCast_re, Zsqrtd.natCast_im, Zsqrtd.intCast_re, Zsqrtd.intCast_im]
      · simp [hk]; ring
      · simp
    rw [hfac, this]
    simp
  intro hirr
  haveI : EuclideanDomain R := inferInstance
  have hprime : Prime (p : R) := hirr.prime
  have : (p : R) ∣ ⟨a, 1⟩ ∨ (p : R) ∣ ⟨a, -1⟩ :=
    hprime.dvd_or_dvd hpdiv
  have hp_not_dvd_one : ∀ (b : ℤ), ¬ (p : R) ∣ ⟨b, 1⟩ ∧ ¬ (p : R) ∣ ⟨b, -1⟩ := by
    intro b
    constructor <;> intro ⟨c, hc⟩
    · have : c.im * p = 1 := by
        have := congrArg Zsqrtd.im hc
        simp [Zsqrtd.natCast_im, Zsqrtd.mul_im] at this
        linarith
      have : (p : ℤ) ∣ 1 := ⟨c.im, by linarith⟩
      have : p ∣ 1 := Int.natCast_dvd_natCast.mp (by simpa using this)
      exact hp.out.not_dvd_one this
    · have : c.im * p = -1 := by
        have := congrArg Zsqrtd.im hc
        simp [Zsqrtd.natCast_im, Zsqrtd.mul_im] at this
        linarith
      have : (p : ℤ) ∣ 1 := ⟨-c.im, by linarith⟩
      have : p ∣ 1 := Int.natCast_dvd_natCast.mp (by simpa using this)
      exact hp.out.not_dvd_one this
  rcases this with h | h
  · exact (hp_not_dvd_one a).1 h
  · exact (hp_not_dvd_one a).2 h


end ZsqrtNegTwo
