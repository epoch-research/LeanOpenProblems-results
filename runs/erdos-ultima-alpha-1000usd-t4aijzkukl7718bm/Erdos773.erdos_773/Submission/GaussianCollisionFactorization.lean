import FormalConjecturesUtil

/-! A small-factor encoding step for equal Gaussian norms. No counting or Sidon bound is asserted. -/
namespace Erdos773.GaussianCollisionFactorization
abbrev G := GaussianInt
open Zsqrtd
set_option maxHeartbeats 1000000
noncomputable section
local instance : GCDMonoid G := EuclideanDomain.gcdMonoid G

lemma norm_eq_of_associated {z w : G} (h : Associated z w) : z.norm=w.norm := by
  obtain ⟨u,hu⟩ := h
  have hn : (u.val : G).norm=1 := (norm_eq_one_iff' (by norm_num : (-1:ℤ) ≤ 0) _).mpr u.isUnit
  have he := congrArg Zsqrtd.norm hu
  rw [Zsqrtd.norm_mul,hn,mul_one] at he
  exact he

/-- Equal norms split into a common Gaussian factor and conjugate factors,
    up to a unit. -/
theorem factorization {z w : G} (hz : z ≠ 0) (he : z.norm=w.norm) :
    ∃ g h : G, z=g*h ∧ Associated w (g*star h) := by
  obtain ⟨h,k,hz',hw',hcop⟩ := extract_gcd z w
  let g := gcd z w
  change z=g*h at hz'
  change w=g*k at hw'
  have hg : g ≠ 0 := by intro h; apply hz; simpa [g,h] using hz'
  have hh : h ≠ 0 := by intro h0; apply hz; simp [h0] at hz'; exact hz'
  have hgN : g.norm ≠ 0 := GaussianInt.norm_eq_zero.not.mpr hg
  have hhN : h.norm ≠ 0 := GaussianInt.norm_eq_zero.not.mpr hh
  have hnorm : h.norm=k.norm := by
    rw [hz',hw',Zsqrtd.norm_mul,Zsqrtd.norm_mul] at he
    exact mul_left_cancel₀ hgN he
  have hprod : h*star h=k*star k := by
    rw [← norm_eq_mul_conj,← norm_eq_mul_conj,hnorm]
  have hdiv : h ∣ star k :=
    ((gcd_isUnit_iff h k).mp hcop).dvd_of_dvd_mul_left ⟨star h,hprod.symm⟩
  obtain ⟨u,hu⟩ := hdiv
  have hunit : IsUnit u := by
    apply (norm_eq_one_iff' (by norm_num : (-1:ℤ) ≤ 0) _).mp
    have hh' := congrArg Zsqrtd.norm hu
    rw [norm_conj,Zsqrtd.norm_mul,← hnorm] at hh'
    apply mul_left_cancel₀ hhN
    simpa only [mul_one] using hh'.symm
  have ha : Associated h (star k) := by
    obtain ⟨v,hv⟩ := hunit
    refine ⟨v,?_⟩
    rw [hv]
    exact hu.symm
  have hk : Associated k (star h) := by
    have ha' := ha.map (starRingEnd G)
    simpa only [starRingEnd_apply,star_star] using ha'.symm
  refine ⟨g,h,hz',?_⟩
  rw [hw']
  exact hk.mul_left g

/-- One of the two factors can always be chosen with squared norm no
    larger than the original norm. Conjugating the output does not alter
    its unordered absolute coordinate pair. -/
theorem small_factor {z w : G} (hz : z ≠ 0) (he : z.norm=w.norm) :
    ∃ g h : G, z=g*h ∧ h ≠ 0 ∧ h.norm^2 ≤ z.norm ∧
      (Associated w (g*star h) ∨ Associated (star w) (g*star h)) := by
  obtain ⟨g,h,hz',hw⟩ := factorization hz he
  have hg0 : g ≠ 0 := by intro hg; apply hz; simpa [hg] using hz'
  have hh0 : h ≠ 0 := by intro hh; apply hz; simpa [hh] using hz'
  have hgN := GaussianInt.norm_nonneg g
  have hhN := GaussianInt.norm_nonneg h
  have hn : z.norm=g.norm*h.norm := by rw [hz',Zsqrtd.norm_mul]
  by_cases hle : h.norm ≤ g.norm
  · refine ⟨g,h,hz',hh0,?_,Or.inl hw⟩
    nlinarith [mul_le_mul_of_nonneg_right hle hhN]
  · refine ⟨h,g,by simpa only [mul_comm] using hz',hg0,?_,Or.inr ?_⟩
    · have hle' : g.norm ≤ h.norm := le_of_lt (lt_of_not_ge hle)
      nlinarith [mul_le_mul_of_nonneg_right hle' hgN]
    · have hw' := hw.map (starRingEnd G)
      simpa only [starRingEnd_apply,star_mul,star_star,mul_comm] using hw'

/-- Removing the rational-integer content cannot increase the norm. -/
lemma primitive_part {h : G} (hh : h ≠ 0) :
    ∃ k : ℤ, ∃ h₀ : G, h=(k:G)*h₀ ∧ IsCoprime h₀.re h₀.im ∧
      h₀ ≠ 0 ∧ h₀.norm ≤ h.norm := by
  obtain ⟨r,s,hr,hs,hcop⟩ := extract_gcd h.re h.im
  let k := gcd h.re h.im
  change h.re=k*r at hr
  change h.im=k*s at hs
  let h₀ : G := ⟨r,s⟩
  have he : h=(k:G)*h₀ := by
    ext <;> simp only [Zsqrtd.re_mul,Zsqrtd.im_mul,Zsqrtd.re_intCast,
      Zsqrtd.im_intCast,zero_mul,mul_zero,add_zero,h₀] <;> assumption
  have hk : k ≠ 0 := by
    intro hk
    apply hh
    rw [he,hk]
    simp
  have hh₀ : h₀ ≠ 0 := by
    intro hz
    apply hh
    rw [he,hz,mul_zero]
  have hn : h.norm=k^2*h₀.norm := by
    rw [he,Zsqrtd.norm_mul]
    simp [Zsqrtd.norm_intCast,pow_two]
  have hk1 : 1 ≤ k^2 := by have := sq_pos_of_ne_zero hk; omega
  have hhN := GaussianInt.norm_nonneg h₀
  refine ⟨k,h₀,he,(gcd_isUnit_iff r s).mp hcop,hh₀,?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hk1 hhN]

/-- The small Gaussian factor may also be taken to have coprime coordinates.
    The odd-norm and quadrant normalizations needed for a counting bound are
    not included in this theorem. -/
theorem small_primitive_factor {z w : G} (hz : z ≠ 0) (he : z.norm=w.norm) :
    ∃ g h : G, z=g*h ∧ h ≠ 0 ∧ IsCoprime h.re h.im ∧ h.norm^2 ≤ z.norm ∧
      (Associated w (g*star h) ∨ Associated (star w) (g*star h)) := by
  obtain ⟨g,h,hz',hh,hsmall,hw⟩ := small_factor hz he
  obtain ⟨k,h₀,hh₀,hcop,hne,hN⟩ := primitive_part hh
  have heq : g*star h=(g*(k:G))*star h₀ := by
    rw [hh₀,star_mul]
    simp only [star_intCast]
    ring
  refine ⟨g*(k:G),h₀,?_,hne,hcop,?_,?_⟩
  · rw [hz',hh₀]
    ring
  · have hp := pow_le_pow_left₀ (GaussianInt.norm_nonneg h₀) hN 2
    exact hp.trans hsmall
  · rwa [← heq]

#print axioms norm_eq_of_associated
#print axioms factorization
#print axioms small_factor
#print axioms primitive_part
#print axioms small_primitive_factor
end
end Erdos773.GaussianCollisionFactorization
