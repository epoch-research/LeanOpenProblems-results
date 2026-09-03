import Submission.GaussianQuadrantFactor

/-! Congruence and uniqueness consequences of the normalized Gaussian factor. -/
namespace Erdos773.GaussianFactorResidues
open GaussianCollisionFactorization GaussianQuadrantFactor
set_option maxHeartbeats 1000000
noncomputable section

lemma real_coprime_norm {h : G} (hc : IsCoprime h.re h.im) : IsCoprime h.re h.norm := by
  apply IsRelPrime.isCoprime
  intro d hdU hdQ
  apply (show IsCoprime h.re (h.im^2) from hc.pow_right).isRelPrime hdU
  have hh := dvd_sub hdQ (dvd_mul_of_dvd_left hdU h.re)
  convert hh using 1
  rw [Zsqrtd.norm_def]
  ring

lemma norm_dvd_cross {z g h : G} (he : z=g*h) : h.norm ∣ z.im*h.re-z.re*h.im := by
  have hh : z*star h=g*(h*star h) := by rw [he]; ring
  rw [← Zsqrtd.norm_eq_mul_conj] at hh
  have hi := congrArg Zsqrtd.im hh
  simp only [Zsqrtd.im_mul,Zsqrtd.re_star,Zsqrtd.im_star,Zsqrtd.re_intCast,
    Zsqrtd.im_intCast,mul_zero] at hi
  refine ⟨g.im,?_⟩
  nlinarith only [hi]

/-- For a fixed primitive factor and fixed real input coordinate, all
    imaginary input coordinates occupy one residue class modulo its norm. -/
theorem partner_congruence {a b c : ℤ} {h g g' : G}
    (hc : IsCoprime h.re h.im) (he : (⟨a,b⟩:G)=g*h) (he' : (⟨a,c⟩:G)=g'*h) :
    h.norm ∣ b-c := by
  have hb := norm_dvd_cross he
  have hc' := norm_dvd_cross he'
  have hd := dvd_sub hb hc'
  have heq : (b*h.re-a*h.im)-(c*h.re-a*h.im)=(b-c)*h.re := by ring
  change h.norm ∣ (b*h.re-a*h.im)-(c*h.re-a*h.im) at hd
  rw [heq] at hd
  exact (real_coprime_norm hc).symm.dvd_of_dvd_mul_right hd

lemma fixed_factor_unique {z g g' h : G} (hh : h ≠ 0)
    (he : z=g*h) (he' : z=g'*h) : g=g' :=
  mul_right_cancel₀ hh (he.symm.trans he')

lemma output_unique {z w w' g g' h : G} (hh : h ≠ 0)
    (he : z=g*h) (he' : z=g'*h)
    (hw : squareCoords w=squareCoords (g*star h))
    (hw' : squareCoords w'=squareCoords (g'*star h)) : squareCoords w=squareCoords w' := by
  have hg := fixed_factor_unique hh he he'
  rw [hw,hw',hg]

/-- Height only: the small factor's norm is at most 2N. -/
lemma norm_height {a b N : ℕ} {h : G} (ha : a ≤ N) (hb : b ≤ N)
    (hh : h.norm^2 ≤ (⟨(a:ℤ),(b:ℤ)⟩:G).norm) : h.norm ≤ 2*N := by
  have ha' : (a:ℤ) ≤ N := by exact_mod_cast ha
  have hb' : (b:ℤ) ≤ N := by exact_mod_cast hb
  have hN : (0:ℤ) ≤ N := by positivity
  have ha0 : (0:ℤ) ≤ a := by positivity
  have hb0 : (0:ℤ) ≤ b := by positivity
  have hasq := pow_le_pow_left₀ ha0 ha' 2
  have hbsq := pow_le_pow_left₀ hb0 hb' 2
  have hn := GaussianInt.norm_nonneg h
  have he : (⟨(a:ℤ),(b:ℤ)⟩:G).norm=(a:ℤ)^2+(b:ℤ)^2 := by
    rw [Zsqrtd.norm_def]
    dsimp only
    ring
  rw [he] at hh
  nlinarith

#print axioms real_coprime_norm
#print axioms partner_congruence
#print axioms output_unique
#print axioms norm_height
end
end Erdos773.GaussianFactorResidues
