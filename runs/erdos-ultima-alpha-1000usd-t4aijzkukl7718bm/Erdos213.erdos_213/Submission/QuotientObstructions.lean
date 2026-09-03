import FormalConjecturesUtil

/-! Necessary geometric and norm conditions for the two elliptic quotients.
These exclude the identity and rational two-torsion trace patterns; they do
not classify rational points on the elliptic curves or settle Erdős 213. -/

namespace Erdos213.QuotientObstructions
noncomputable section

def RationalNorm (z : ℂ) : Prop := ∃ q : ℚ, (q : ℝ) = ‖z‖

def quotientTwo (z : ℂ) : ℂ := z + 3/z

def quotientThree (z : ℂ) : ℂ := z*(z^2-9)/(z^2-1)

lemma RationalNorm.mul {z w : ℂ} (hz : RationalNorm z) (hw : RationalNorm w) :
    RationalNorm (z*w) := by
  obtain ⟨a,ha⟩ := hz
  obtain ⟨b,hb⟩ := hw
  exact ⟨a*b, by simp [ha,hb]⟩

lemma RationalNorm.div {z w : ℂ} (hz : RationalNorm z) (hw : RationalNorm w) :
    RationalNorm (z/w) := by
  obtain ⟨a,ha⟩ := hz
  obtain ⟨b,hb⟩ := hw
  exact ⟨a/b, by simp [ha,hb]⟩

lemma RationalNorm.normSq_ne {z : ℂ} (hz : RationalNorm z) {a : ℚ}
    (ha : ¬ IsSquare a) : Complex.normSq z ≠ (a : ℝ) := by
  intro he
  obtain ⟨q,hq⟩ := hz
  apply ha
  refine ⟨q, ?_⟩
  have hh : (a : ℝ) = (q : ℝ)*(q : ℝ) := by
    rw [← he, Complex.normSq_eq_norm_sq, ← hq]
    ring
  exact_mod_cast hh

private lemma nonreal_ne_real {z : ℂ} (hz : z.im ≠ 0) (r : ℝ) : z ≠ (r : ℂ) := by
  intro he
  apply hz
  simp [he]

lemma quotientTwo_nonreal {z : ℂ} (hz : z.im ≠ 0) (hn : RationalNorm z) :
    (quotientTwo z).im ≠ 0 := by
  have h0 : z ≠ 0 := by simpa using nonreal_ne_real hz 0
  have hN : Complex.normSq z ≠ 0 := mt Complex.normSq_eq_zero.mp h0
  have h3 : Complex.normSq z ≠ 3 := hn.normSq_ne (by norm_num : ¬ IsSquare (3 : ℚ))
  have he : (quotientTwo z).im * Complex.normSq z = z.im*(Complex.normSq z-3) := by
    simp only [quotientTwo, Complex.add_im, Complex.div_im, Complex.im_ofNat,
      Complex.re_ofNat, zero_mul, zero_div, zero_sub]
    field_simp
    ring
  intro hh
  rw [hh,zero_mul] at he
  exact (mul_ne_zero hz (sub_ne_zero.mpr h3)) he.symm

lemma quotientThree_partial_fractions {z : ℂ} (hz : z.im ≠ 0) :
    quotientThree z = z - 4/(z-1) - 4/(z+1) := by
  have h1 : z-1 ≠ 0 := sub_ne_zero.mpr (by simpa using nonreal_ne_real hz 1)
  have hm1 : z+1 ≠ 0 := by
    have hh := sub_ne_zero.mpr (nonreal_ne_real hz (-1))
    simpa using hh
  have hprod : z^2-1 = (z-1)*(z+1) := by ring
  dsimp [quotientThree]
  rw [hprod]
  field_simp
  ring

lemma quotientThree_nonreal {z : ℂ} (hz : z.im ≠ 0) :
    (quotientThree z).im ≠ 0 := by
  have h1 : z-1 ≠ 0 := sub_ne_zero.mpr (by simpa using nonreal_ne_real hz 1)
  have hm1 : z+1 ≠ 0 := by
    have hh := sub_ne_zero.mpr (nonreal_ne_real hz (-1))
    simpa using hh
  have hp : 0 < 1 + 4/Complex.normSq (z-1) + 4/Complex.normSq (z+1) := by
    have ha := Complex.normSq_pos.mpr h1
    have hb := Complex.normSq_pos.mpr hm1
    positivity
  have he : (quotientThree z).im =
      z.im*(1+4/Complex.normSq (z-1)+4/Complex.normSq (z+1)) := by
    rw [quotientThree_partial_fractions hz]
    simp only [Complex.sub_im, Complex.div_im, Complex.im_ofNat, Complex.re_ofNat,
      Complex.add_im, Complex.one_im, sub_zero, add_zero, zero_mul, zero_div]
    ring
  rw [he]
  exact mul_ne_zero hz (ne_of_gt hp)

lemma quotientTwo_shifted_norms {z : ℂ} (hz : z.im ≠ 0)
    (h0 : RationalNorm z) (h1 : RationalNorm (z-1)) (hm1 : RationalNorm (z+1))
    (h3 : RationalNorm (z-3)) (hm3 : RationalNorm (z+3)) :
    RationalNorm (quotientTwo z-4) ∧ RationalNorm (quotientTwo z+4) := by
  have hz0 : z ≠ 0 := by simpa using nonreal_ne_real hz 0
  have he : quotientTwo z-4 = (z-1)*(z-3)/z := by
    dsimp [quotientTwo]
    field_simp
    ring
  have he' : quotientTwo z+4 = (z+1)*(z+3)/z := by
    dsimp [quotientTwo]
    field_simp
    ring
  rw [he,he']
  exact ⟨(h1.mul h3).div h0, (hm1.mul hm3).div h0⟩

lemma quotientThree_rationalNorm {z : ℂ}
    (h0 : RationalNorm z) (h1 : RationalNorm (z-1)) (hm1 : RationalNorm (z+1))
    (h3 : RationalNorm (z-3)) (hm3 : RationalNorm (z+3)) :
    RationalNorm (quotientThree z) := by
  have he : quotientThree z = z*(z-3)*(z+3)/((z-1)*(z+1)) := by
    dsimp [quotientThree]
    congr 1 <;> ring
  rw [he]
  exact ((h0.mul h3).mul hm3).div (h1.mul hm1)

/-- These are the norm equalities forced by translating a point by the three
nonzero two-torsion points on y²=x(x-4)(x+4). -/
lemma quotientTwo_torsion_norm_exclusions {z : ℂ} (hz : z.im ≠ 0)
    (h0 : RationalNorm z) (h1 : RationalNorm (z-1)) (hm1 : RationalNorm (z+1))
    (h3 : RationalNorm (z-3)) (hm3 : RationalNorm (z+3)) :
    Complex.normSq (quotientTwo z) ≠ -16 ∧
    Complex.normSq (quotientTwo z-4) ≠ 32 ∧
    Complex.normSq (quotientTwo z+4) ≠ 32 := by
  obtain ⟨ha,hb⟩ := quotientTwo_shifted_norms hz h0 h1 hm1 h3 hm3
  refine ⟨?_, ha.normSq_ne (by norm_num : ¬ IsSquare (32 : ℚ)),
    hb.normSq_ne (by norm_num : ¬ IsSquare (32 : ℚ))⟩
  have hh := Complex.normSq_nonneg (quotientTwo z)
  linarith

/-- The analogous norm value for the nonzero rational two-torsion point on
 y²=x(x²+27) is impossible as well. -/
lemma quotientThree_torsion_norm_exclusion {z : ℂ}
    (h0 : RationalNorm z) (h1 : RationalNorm (z-1)) (hm1 : RationalNorm (z+1))
    (h3 : RationalNorm (z-3)) (hm3 : RationalNorm (z+3)) :
    Complex.normSq (quotientThree z) ≠ 27 :=
  (quotientThree_rationalNorm h0 h1 hm1 h3 hm3).normSq_ne
    (by norm_num : ¬ IsSquare (27 : ℚ))

/-- The x-coordinate involution induced by a two-torsion point forces this
norm equation when it exchanges a point with its complex conjugate. -/
lemma normSq_of_conjugate_involution {w : ℂ} {e k : ℝ}
    (hw : w ≠ (e : ℂ)) (h : starRingEnd ℂ w = e + k/(w-e)) :
    Complex.normSq (w-e) = k := by
  have hw0 : w-(e : ℂ) ≠ 0 := sub_ne_zero.mpr hw
  have hh : (w-(e : ℂ))*starRingEnd ℂ (w-e) = (k : ℂ) := by
    rw [map_sub]
    simp only [Complex.conj_ofReal]
    rw [h]
    field_simp
    ring
  rw [Complex.mul_conj] at hh
  exact Complex.ofReal_injective hh

lemma quotientThree_no_trivial_conjugacy {z : ℂ} (hz : z.im ≠ 0)
    (h0 : RationalNorm z) (h1 : RationalNorm (z-1)) (hm1 : RationalNorm (z+1))
    (h3 : RationalNorm (z-3)) (hm3 : RationalNorm (z+3)) :
    starRingEnd ℂ (quotientThree z) ≠ quotientThree z ∧
    starRingEnd ℂ (quotientThree z) ≠ 27/quotientThree z := by
  have hn := quotientThree_nonreal hz
  refine ⟨fun he => hn (Complex.conj_eq_iff_im.mp he), ?_⟩
  intro he
  apply quotientThree_torsion_norm_exclusion h0 h1 hm1 h3 hm3
  have hw : quotientThree z ≠ ((0 : ℝ) : ℂ) := nonreal_ne_real hn 0
  have hh := normSq_of_conjugate_involution (k := 27) hw (by simpa using he)
  simpa using hh

lemma quotientTwo_no_trivial_conjugacy {z : ℂ} (hz : z.im ≠ 0)
    (h0 : RationalNorm z) (h1 : RationalNorm (z-1)) (hm1 : RationalNorm (z+1))
    (h3 : RationalNorm (z-3)) (hm3 : RationalNorm (z+3)) :
    starRingEnd ℂ (quotientTwo z) ≠ quotientTwo z ∧
    starRingEnd ℂ (quotientTwo z) ≠ -16/quotientTwo z ∧
    starRingEnd ℂ (quotientTwo z) ≠ 4+32/(quotientTwo z-4) ∧
    starRingEnd ℂ (quotientTwo z) ≠ -4+32/(quotientTwo z+4) := by
  have hn := quotientTwo_nonreal hz h0
  obtain ⟨ha,hb,hc⟩ := quotientTwo_torsion_norm_exclusions hz h0 h1 hm1 h3 hm3
  refine ⟨fun he => hn (Complex.conj_eq_iff_im.mp he), ?_, ?_, ?_⟩
  · intro he
    have hw : quotientTwo z ≠ ((0 : ℝ) : ℂ) := nonreal_ne_real hn 0
    have hh := normSq_of_conjugate_involution (k := -16) hw (by simpa using he)
    apply ha
    simpa using hh
  · intro he
    have hw : quotientTwo z ≠ ((4 : ℝ) : ℂ) := nonreal_ne_real hn 4
    exact hb (normSq_of_conjugate_involution (k := 32) hw (by simpa using he))
  · intro he
    have hw : quotientTwo z ≠ ((-4 : ℝ) : ℂ) := nonreal_ne_real hn (-4)
    have hh := normSq_of_conjugate_involution (k := 32) hw (by simpa using he)
    apply hc
    simpa using hh

#print axioms quotientTwo_no_trivial_conjugacy
#print axioms quotientThree_no_trivial_conjugacy

#print axioms quotientTwo_nonreal
#print axioms quotientThree_nonreal
#print axioms quotientTwo_torsion_norm_exclusions
#print axioms quotientThree_torsion_norm_exclusion

end
end Erdos213.QuotientObstructions
