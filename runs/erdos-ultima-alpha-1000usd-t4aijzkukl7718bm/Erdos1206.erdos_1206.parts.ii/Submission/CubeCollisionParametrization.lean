import FormalConjecturesUtil

/-!
An exact rational normal form for every ordered positive cubic collision.
This is an algebraic reduction only, not a density theorem.
-/

namespace Erdos1206

lemma cube_normal_form_identity (q u v : ℚ) :
    (q ^ 2 + u) ^ 3 + (q * v + 1) ^ 3 -
      (q ^ 2 + v) ^ 3 - (q * u + 1) ^ 3 =
        (u - v) * (q ^ 3 - 1) * (3 * q - (u ^ 2 + u * v + v ^ 2)) := by
  ring

private lemma ordered_cube_collision_gap_lt {a b c d : ℚ}
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (he : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) : d - c < b - a := by
  have hb : 0 < b := ha.trans_lt hab
  have hc : 0 < c := hb.trans hbc
  have hd : 0 < d := hc.trans hcd
  have hQ₁ : 0 ≤ b ^ 2 + b * a + a ^ 2 := by positivity
  have hQ₂ : b ^ 2 + b * a + a ^ 2 < d ^ 2 + d * c + c ^ 2 := by
    have h₁ : b ^ 2 < d ^ 2 := (sq_lt_sq₀ hb.le hd.le).mpr (hbc.trans hcd)
    have h₂ : a ^ 2 < c ^ 2 := (sq_lt_sq₀ ha hc.le).mpr (hab.trans hbc)
    have h₃ : b * a ≤ d * c := mul_le_mul (hbc.trans hcd).le
      (hab.trans hbc).le ha hd.le
    linarith
  have hprod : (d - c) * (d ^ 2 + d * c + c ^ 2) =
      (b - a) * (b ^ 2 + b * a + a ^ 2) := by
    nlinarith only [he]
  by_contra hn
  have hle : b - a ≤ d - c := le_of_not_gt hn
  have hlt := mul_lt_mul_of_pos_left hQ₂ (sub_pos.mpr hab)
  have hle' := mul_le_mul_of_nonneg_right hle (hQ₁.trans hQ₂.le)
  linarith

/-- The nontrivial ordered positive part of the Fermat cubic surface is
parametrized by a rational quadratic norm relation and a positive scale. -/
theorem ordered_cube_collision_normal_form {a b c d : ℚ}
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (he : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    ∃ q u v t : ℚ,
      0 < q ∧ q < 1 ∧ 0 < t ∧ u < v ∧
      u ^ 2 + u * v + v ^ 2 = 3 * q ∧
      a = t * (q ^ 2 + u) ∧ b = t * (q ^ 2 + v) ∧
      c = t * (q * u + 1) ∧ d = t * (q * v + 1) := by
  let q := (d - c) / (b - a)
  have hba : 0 < b - a := sub_pos.mpr hab
  have hq : 0 < q := div_pos (sub_pos.mpr hcd) hba
  have hq1 : q < 1 := by
    dsimp [q]
    exact (div_lt_one hba).mpr (ordered_cube_collision_gap_lt ha hab hbc hcd he)
  have hq3 : q ^ 3 < 1 := by nlinarith [sq_nonneg (q - 1)]
  have hden : q ^ 3 - 1 ≠ 0 := by linarith
  have hgap : q * (b - a) = d - c := by
    dsimp [q]
    exact div_mul_cancel₀ _ hba.ne'
  have hnum : q * a - c < 0 := by
    have hqa := mul_le_mul_of_nonneg_right hq1.le ha
    linarith
  let t := (q * a - c) / (q ^ 3 - 1)
  have ht : 0 < t := div_pos_of_neg_of_neg hnum (by linarith)
  have htn : t ≠ 0 := ht.ne'
  have hscale : t * (q ^ 3 - 1) = q * a - c := by
    dsimp [t]
    exact div_mul_cancel₀ _ hden
  let u := a / t - q ^ 2
  let v := b / t - q ^ 2
  have ha' : a = t * (q ^ 2 + u) := by
    dsimp [u]
    field_simp
    ring
  have hb' : b = t * (q ^ 2 + v) := by
    dsimp [v]
    field_simp
    ring
  have hc' : c = t * (q * u + 1) := by
    nlinarith only [hscale, congrArg (fun x : ℚ => q * x) ha']
  have hd' : d = t * (q * v + 1) := by
    nlinarith only [hgap, hc', congrArg (fun x : ℚ => q * x) ha',
      congrArg (fun x : ℚ => q * x) hb']
  have huv : u < v := by
    have hlt : t * (q ^ 2 + u) < t * (q ^ 2 + v) := by
      rw [← ha', ← hb']; exact hab
    have hh := (mul_lt_mul_iff_right₀ ht).mp hlt
    linarith
  have he' : (q ^ 2 + u) ^ 3 + (q * v + 1) ^ 3 =
      (q ^ 2 + v) ^ 3 + (q * u + 1) ^ 3 := by
    rw [ha', hb', hc', hd'] at he
    simp only [mul_pow] at he
    have hh : t ^ 3 * ((q ^ 2 + u) ^ 3 + (q * v + 1) ^ 3) =
        t ^ 3 * ((q ^ 2 + v) ^ 3 + (q * u + 1) ^ 3) := by
      simpa only [mul_add] using he
    exact mul_left_cancel₀ (pow_ne_zero _ htn) hh
  have hz : (u - v) * (q ^ 3 - 1) * (3 * q - (u ^ 2 + u * v + v ^ 2)) = 0 := by
    rw [← cube_normal_form_identity]
    linarith
  have hnorm : u ^ 2 + u * v + v ^ 2 = 3 * q := by
    have hzero := (mul_eq_zero.mp hz).resolve_left
      (mul_ne_zero (sub_ne_zero.mpr huv.ne) hden)
    linarith
  exact ⟨q, u, v, t, hq, hq1, ht, huv, hnorm, ha', hb', hc', hd'⟩

#print axioms ordered_cube_collision_normal_form

/-- The quadratic Eisenstein norm in two rational parameters. -/
def cubeParamNorm (r s : ℚ) : ℚ := r ^ 2 - r * s + s ^ 2

def cubeParamA (r s : ℚ) : ℚ := (cubeParamNorm r s) ^ 2 + r - 2 * s

def cubeParamB (r s : ℚ) : ℚ := (cubeParamNorm r s) ^ 2 + r + s

def cubeParamC (r s : ℚ) : ℚ := cubeParamNorm r s * (r - 2 * s) + 1

def cubeParamD (r s : ℚ) : ℚ := cubeParamNorm r s * (r + s) + 1

lemma cubeParam_identity (r s : ℚ) :
    cubeParamA r s ^ 3 + cubeParamD r s ^ 3 =
      cubeParamB r s ^ 3 + cubeParamC r s ^ 3 := by
  dsimp [cubeParamA, cubeParamB, cubeParamC, cubeParamD, cubeParamNorm]
  ring

/-- Every nontrivial ordered nonnegative rational collision is a positive
rational dilate of this fixed quartic parametrization. -/
theorem ordered_cube_collision_quartic_parametrization {a b c d : ℚ}
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (he : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    ∃ r s t : ℚ, 0 < s ∧ 0 < t ∧
      0 < cubeParamNorm r s ∧ cubeParamNorm r s < 1 ∧
      a = t * cubeParamA r s ∧ b = t * cubeParamB r s ∧
      c = t * cubeParamC r s ∧ d = t * cubeParamD r s := by
  obtain ⟨q, u, v, t, hq, hq1, ht, huv, hnorm, ha', hb', hc', hd'⟩ :=
    ordered_cube_collision_normal_form ha hab hbc hcd he
  let r := (u + 2 * v) / 3
  let s := (v - u) / 3
  have hs : 0 < s := div_pos (sub_pos.mpr huv) (by norm_num)
  have hN : cubeParamNorm r s = q := by
    dsimp [cubeParamNorm, r, s]
    nlinarith only [hnorm]
  have hu : r - 2 * s = u := by dsimp [r, s]; ring
  have hv : r + s = v := by dsimp [r, s]; ring
  refine ⟨r, s, t, hs, ht, hN ▸ hq, hN ▸ hq1, ?_, ?_, ?_, ?_⟩
  · simpa only [cubeParamA, hN, add_sub_assoc, hu] using ha'
  · simpa only [cubeParamB, hN, add_assoc, hv] using hb'
  · simpa only [cubeParamC, hN, hu] using hc'
  · simpa only [cubeParamD, hN, hv] using hd'

#print axioms ordered_cube_collision_quartic_parametrization

end Erdos1206
