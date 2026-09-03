import Submission.GaussianCollisionFactorization

/-! Removing the ramified factor 1+i while preserving the collision encoding. -/
namespace Erdos773.GaussianOddFactor
open GaussianCollisionFactorization
set_option maxHeartbeats 1000000
noncomputable section

def ramified : G := ⟨1,1⟩
def imagUnit : Gˣ := ⟨⟨0,1⟩,⟨0,-1⟩,by ext <;> norm_num,by ext <;> norm_num⟩

lemma ramified_associated : Associated (star ramified) ramified := by
  refine ⟨imagUnit,?_⟩
  ext <;> norm_num [ramified,imagUnit]

/-- Coprime same-parity coordinates must both be odd. -/
lemma same_parity {h : G} (hcop : IsCoprime h.re h.im)
    (he : h.re%2=h.im%2) : h.re%2=1 ∧ h.im%2=1 := by
  have hr0 := Int.emod_nonneg h.re (by norm_num : (2:ℤ) ≠ 0)
  have hr2 := Int.emod_lt_of_pos h.re (by norm_num : (0:ℤ)<2)
  have hn : h.re%2 ≠ 0 := by
    intro hz
    have hd₁ : (2:ℤ) ∣ h.re := Int.dvd_of_emod_eq_zero hz
    have hd₂ : (2:ℤ) ∣ h.im := Int.dvd_of_emod_eq_zero (he.symm.trans hz)
    have hh := hcop.isRelPrime hd₁ hd₂
    norm_num [Int.isUnit_iff_natAbs_eq] at hh
  omega

/-- The normalized factor has opposite-parity coprime coordinates. No
    orientation or uniqueness statement is included here. -/
theorem remove_ramified (g h : G) (hcop : IsCoprime h.re h.im) :
    ∃ g' h' : G, g*h=g'*h' ∧ Associated (g*star h) (g'*star h') ∧
      IsCoprime h'.re h'.im ∧ h'.re%2 ≠ h'.im%2 ∧ h'.norm ≤ h.norm := by
  by_cases ho : h.re%2 ≠ h.im%2
  · exact ⟨g,h,rfl,Associated.refl _,hcop,ho,le_refl _⟩
  have hodd := same_parity hcop (not_ne_iff.mp ho)
  let x := (h.re+h.im)/2
  let y := (h.im-h.re)/2
  let h' : G := ⟨x,y⟩
  have hx : h.re=x-y := by dsimp [x,y]; omega
  have hy : h.im=x+y := by dsimp [x,y]; omega
  have he : h=ramified*h' := by
    ext <;> simp [ramified,h',hx,hy] <;> ring
  have hcop' : IsCoprime x y := by
    apply IsRelPrime.isCoprime
    intro d hdx hdy
    apply hcop.isRelPrime
    · rw [hx]; exact dvd_sub hdx hdy
    · rw [hy]; exact dvd_add hdx hdy
  have ho' : x%2 ≠ y%2 := by omega
  have hnorm : h.norm=2*h'.norm := by
    rw [he,Zsqrtd.norm_mul]
    norm_num [ramified,Zsqrtd.norm_def]
  refine ⟨g*ramified,h',?_,?_,hcop',ho',?_⟩
  · rw [he,mul_assoc]
  · rw [he,star_mul]
    have hh := ramified_associated.mul_left (g*star h')
    convert hh using 1 <;> ring
  · have hh := GaussianInt.norm_nonneg h'
    linarith

lemma norm_odd {h : G} (hp : h.re%2 ≠ h.im%2) : Odd h.norm := by
  have hn : h.norm=h.re^2+h.im^2 := by rw [Zsqrtd.norm_def]; ring
  rw [hn,Int.odd_add,Int.odd_pow' (by decide : (2:ℕ) ≠ 0),
    Int.even_pow' (by decide : (2:ℕ) ≠ 0)]
  simp only [Int.odd_iff,Int.even_iff] at *
  omega

/-- Equal nonzero Gaussian norms admit a small primitive odd-norm factor. -/
theorem small_odd_factor {z w : G} (hz : z ≠ 0) (he : z.norm=w.norm) :
    ∃ g h : G, z=g*h ∧ h ≠ 0 ∧ IsCoprime h.re h.im ∧
      h.re%2 ≠ h.im%2 ∧ h.norm^2 ≤ z.norm ∧
      (Associated w (g*star h) ∨ Associated (star w) (g*star h)) := by
  obtain ⟨g,h,hz',hh,hcop,hsmall,hw⟩ := small_primitive_factor hz he
  obtain ⟨g',h',he',hw',hcop',ho',hN⟩ := remove_ramified g h hcop
  have hz'' : z=g'*h' := hz'.trans he'
  have hh' : h' ≠ 0 := by intro h0; apply hz; simpa [h0] using hz''
  refine ⟨g',h',hz'',hh',hcop',ho',?_,?_⟩
  · exact (pow_le_pow_left₀ (GaussianInt.norm_nonneg h') hN 2).trans hsmall
  · exact hw.imp (fun h => h.trans hw') (fun h => h.trans hw')

#print axioms remove_ramified
#print axioms norm_odd
#print axioms small_odd_factor
end
end Erdos773.GaussianOddFactor
