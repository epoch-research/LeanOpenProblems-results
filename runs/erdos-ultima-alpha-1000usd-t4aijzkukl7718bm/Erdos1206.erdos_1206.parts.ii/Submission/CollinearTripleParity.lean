import FormalConjecturesUtil

/-! Three distinct collinear representations of a nonzero sum of two cubes
cannot have all six integer coordinates odd. This controls chord-generated
triples only, not arbitrary cubic collision cycles. -/

namespace Erdos1206.CollinearTripleParity
set_option maxHeartbeats 2000000

private lemma cubic_three_roots (a c e L M N P : ℤ)
    (hac : a ≠ c) (hae : a ≠ e) (hce : c ≠ e)
    (ha : L*a^3+M*a^2+N*a+P=0)
    (hc : L*c^3+M*c^2+N*c+P=0)
    (he : L*e^3+M*e^2+N*e+P=0) :
    L*(a+c+e) = -M ∧ L*(a*c+a*e+c*e)=N := by
  have h₁ : L*(a^2+a*c+c^2)+M*(a+c)+N=0 := by
    have hh : (a-c)*(L*(a^2+a*c+c^2)+M*(a+c)+N)=0 := by
      linear_combination ha-hc
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hac)
  have h₂ : L*(a^2+a*e+e^2)+M*(a+e)+N=0 := by
    have hh : (a-e)*(L*(a^2+a*e+e^2)+M*(a+e)+N)=0 := by
      linear_combination ha-he
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hae)
  have hM : L*(a+c+e)+M=0 := by
    have hh : (c-e)*(L*(a+c+e)+M)=0 := by linear_combination h₁-h₂
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hce)
  refine ⟨by linarith, ?_⟩
  linear_combination (a+c)*hM-h₁

private lemma line_cubic_root (a b H K T S : ℤ)
    (hc : a^3+b^3=S) (hl : K*a-H*b=T) :
    (H^3+K^3)*a^3+(-3*K^2*T)*a^2+(3*K*T^2)*a+(-T^3-S*H^3)=0 := by
  have hl' : K*a-T=H*b := by linarith
  have hp := congrArg (fun z : ℤ => z^3) hl'
  linear_combination hp+H^3*hc

/-- Arithmetic form of the parity obstruction, using a line with primitive
parity in its two direction coefficients. -/
theorem primitive_line_odd_triple_false
    (a b c d e f H K T S : ℤ)
    (hH : H ≠ 0) (hK : K ≠ 0) (hHK : Odd H ∨ Odd K) (hS : S ≠ 0)
    (ha : Odd a) (hb : Odd b) (hc : Odd c) (hd : Odd d) (he : Odd e) (hf : Odd f)
    (hac : a ≠ c) (hae : a ≠ e) (hce : c ≠ e)
    (hbd : b ≠ d) (hbf : b ≠ f) (hdf : d ≠ f)
    (h₁ : a^3+b^3=S) (h₂ : c^3+d^3=S) (h₃ : e^3+f^3=S)
    (hl₁ : K*a-H*b=T) (hl₂ : K*c-H*d=T) (hl₃ : K*e-H*f=T) : False := by
  let L := H^3+K^3
  obtain ⟨hs₁,hs₂⟩ := cubic_three_roots a c e L (-3*K^2*T) (3*K*T^2) (-T^3-S*H^3)
    hac hae hce (line_cubic_root a b H K T S h₁ hl₁)
    (line_cubic_root c d H K T S h₂ hl₂)
    (line_cubic_root e f H K T S h₃ hl₃)
  have hs₁' : L*(a+c+e)=3*K^2*T := by simpa using hs₁
  have hy₁ := line_cubic_root b a K H (-T) S (by linarith only [h₁]) (by linarith only [hl₁])
  have hy₂ := line_cubic_root d c K H (-T) S (by linarith only [h₂]) (by linarith only [hl₂])
  have hy₃ := line_cubic_root f e K H (-T) S (by linarith only [h₃]) (by linarith only [hl₃])
  obtain ⟨ht₁,_⟩ := cubic_three_roots b d f (K^3+H^3) (-3*H^2*(-T))
    (3*H*(-T)^2) (-(-T)^3-S*K^3) hbd hbf hdf hy₁ hy₂ hy₃
  have ht₁' : L*(b+d+f) = -3*H^2*T := by
    dsimp [L]
    nlinarith only [ht₁]
  have hL : L ≠ 0 := by
    intro hL
    have hT : T=0 := by
      have hh : (3*K^2)*T=0 := by rw [hL] at hs₁'; nlinarith only [hs₁']
      exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero (by norm_num) (pow_ne_zero _ hK))
    have hline : K*a=H*b := by rw [hT] at hl₁; linarith
    have hp : K^3*a^3=H^3*b^3 := by
      convert congrArg (fun z : ℤ => z^(3 : ℕ)) hline using 1 <;> ring
    have hz : H^3*S=0 := by
      calc
        H^3*S = H^3*(a^3+b^3) := by rw [h₁]
        _ = L*a^3 := by dsimp [L]; rw [mul_add, ← hp]; ring
        _ = 0 := by rw [hL,zero_mul]
    exact (mul_ne_zero (pow_ne_zero _ hH) hS) hz
  have hrel : H^2*(a+c+e)+K^2*(b+d+f)=0 := by
    apply mul_left_cancel₀ hL
    linear_combination H^2*hs₁'+K^2*ht₁'
  have hsOdd : Odd (a+c+e) := (ha.add_odd hc).add_odd he
  have htOdd : Odd (b+d+f) := (hb.add_odd hd).add_odd hf
  have hpairOdd : Odd (a*c+a*e+c*e) := ((ha.mul hc).add_odd (ha.mul he)).add_odd (hc.mul he)
  have hpar : Odd H ↔ Odd K := by
    have hzeroEven : Even (H^2*(a+c+e)+K^2*(b+d+f)) := by rw [hrel]; exact ⟨0, by ring⟩
    have hh := Int.even_add'.mp hzeroEven
    simpa [Int.odd_mul,Int.odd_pow,hsOdd,htOdd] using hh
  have hHo : Odd H := hHK.elim id hpar.mpr
  have hKo : Odd K := hpar.mp hHo
  have hcross : (a+c+e)*T=K*(a*c+a*e+c*e) := by
    apply mul_left_cancel₀ hL
    linear_combination T*hs₁'-K*hs₂
  have hTOdd : Odd T := by
    have hh : Odd ((a+c+e)*T) := by rw [hcross]; exact hKo.mul hpairOdd
    exact (Int.odd_mul.mp hh).2
  have hLEven : Even L := by
    dsimp [L]
    exact hHo.pow.add_odd hKo.pow
  have hEven : Even (3*K^2*T) := hs₁' ▸ hLEven.mul_right (a+c+e)
  have hOdd : Odd (3*K^2*T) := ((by decide : Odd (3 : ℤ)).mul hKo.pow).mul hTOdd
  exact (Int.not_even_iff_odd.mpr hOdd) hEven

/-- Coordinate formulation: three distinct points on a nonzero cubic
x^3+y^3=S, collinear over the rationals, cannot all have odd coordinates. -/
theorem odd_collinear_triple_false (a b c d e f S : ℤ) (hS : S ≠ 0)
    (ha : Odd a) (hb : Odd b) (hc : Odd c) (hd : Odd d) (he : Odd e) (hf : Odd f)
    (hac : a ≠ c) (hae : a ≠ e) (hce : c ≠ e)
    (hbd : b ≠ d) (hbf : b ≠ f) (hdf : d ≠ f)
    (h₁ : a^3+b^3=S) (h₂ : c^3+d^3=S) (h₃ : e^3+f^3=S)
    (hcol : (c-a)*(f-b)=(e-a)*(d-b)) : False := by
  have hgpos : 0 < Int.gcd (c-a) (d-b) :=
    Int.gcd_pos_of_ne_zero_left _ (sub_ne_zero.mpr hac.symm)
  obtain ⟨g,H,K,hg,hcop,hgH,hgK⟩ := Int.exists_gcd_one' hgpos
  have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hg)
  have hH : H ≠ 0 := by
    intro hh
    rw [hh,zero_mul] at hgH
    exact (sub_ne_zero.mpr hac.symm) hgH
  have hK : K ≠ 0 := by
    intro hh
    rw [hh,zero_mul] at hgK
    exact (sub_ne_zero.mpr hbd.symm) hgK
  have hHK : Odd H ∨ Odd K := by
    by_contra! hn
    have heH := Int.not_odd_iff_even.mp hn.1
    have heK := Int.not_odd_iff_even.mp hn.2
    have hh : (2 : ℤ) ∣ (Int.gcd H K : ℤ) :=
      Int.dvd_coe_gcd (even_iff_two_dvd.mp heH) (even_iff_two_dvd.mp heK)
    rw [hcop] at hh
    norm_num at hh
  have hline₂ : K*c-H*d=K*a-H*b := by
    have hh : K*(c-a)=H*(d-b) := by rw [hgH,hgK]; ring
    nlinarith only [hh]
  have hline₃ : K*e-H*f=K*a-H*b := by
    rw [hgH,hgK] at hcol
    have hh : H*(f-b)=K*(e-a) := by
      apply mul_right_cancel₀ hgz
      nlinarith only [hcol]
    nlinarith only [hh]
  exact primitive_line_odd_triple_false a b c d e f H K (K*a-H*b) S hH hK hHK hS
    ha hb hc hd he hf hac hae hce hbd hbf hdf h₁ h₂ h₃ rfl hline₂ hline₃

#print axioms primitive_line_odd_triple_false
#print axioms odd_collinear_triple_false
end Erdos1206.CollinearTripleParity
