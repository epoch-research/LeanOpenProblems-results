import Submission.RoughSquarefreePrimitiveFamily

/-! A fixed common-factor bound for the primitive squarefree rough family.
This bound depends on the family, not on its two varying parameters. -/
namespace Erdos1206.RoughConicCancellation
open RoughNearUnitConicFamily

def certificate (m L : ℤ) : ℤ :=
  216*m^3*norm m L*(norm m L^3-27*m^6)

lemma certificate_ne {m L : ℤ} (hL : 0 < L) (hm : 12*L ≤ m) :
    certificate m L ≠ 0 := by
  have hm0 : 0 < m := by omega
  have hn : 0 < norm m L := by
    have h := mul_nonneg (by omega : 0 ≤ m-3*L) hm0.le
    dsimp [RoughNearUnitConicFamily.norm]
    nlinarith [sq_pos_of_pos hL]
  have hnlt : norm m L < 3*m^2 := by
    have h := mul_pos (by omega : 0 < 9*m-7*L) hL
    dsimp [RoughNearUnitConicFamily.norm]
    nlinarith only [h]
  have he : norm m L^3-27*m^6 ≠ 0 := by
    have hh := (by decide : Odd (3:ℕ)).strictMono_pow hnlt
    dsimp only at hh
    have hc : (3*m^2)^3=27*m^6 := by ring
    rw [hc] at hh
    omega
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero _ hm0.ne')) hn.ne') he

lemma common_divisor {m L s t g : ℤ} (hc : IsCoprime s t)
    (hA : g ∣ A m L s t) (hB : g ∣ B m L s t) (hC : g ∣ C m L s t) :
    g ∣ certificate m L := by
  let n := norm m L
  let E := n^3-27*m^6
  let W := 36*m^3*n*E
  have hD : g ∣ E*den s t := by
    have he : E*den s t=n*A m L s t-3*m^2*C m L s t := by
      dsimp [E,n,A,C]; ring
    rw [he]
    exact dvd_sub (dvd_mul_of_dvd_right hA _) (dvd_mul_of_dvd_right hC _)
  have hU : g ∣ 9*m^3*E*U m L s t := by
    have he : 9*m^3*E*U m L s t=E*A m L s t-n^2*(E*den s t) := by
      dsimp [n,A]; ring
    rw [he]
    exact dvd_sub (dvd_mul_of_dvd_right hA _) (dvd_mul_of_dvd_right hD _)
  have hV : g ∣ 9*m^3*E*V m L s t := by
    have he : 9*m^3*E*V m L s t=E*B m L s t-n^2*(E*den s t) := by
      dsimp [n,B]; ring
    rw [he]
    exact dvd_sub (dvd_mul_of_dvd_right hB _) (dvd_mul_of_dvd_right hD _)
  have hX : g ∣ W*(s^2-3*t^2) := by
    have he : W*(s^2-3*t^2)=
        (6*m-10*L)*(9*m^3*E*U m L s t)+(6*m-8*L)*(9*m^3*E*V m L s t) := by
      dsimp [W,n,RoughNearUnitConicFamily.norm,U,V]; ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_right hU _) (dvd_mul_of_dvd_right hV _)
  have hY : g ∣ W*(s^2+3*t^2) := by
    have he : W*(s^2+3*t^2)=(36*m^3*n)*(E*den s t) := by dsimp [W,den]; ring
    rw [he]
    exact dvd_mul_of_dvd_right hD _
  have hs : g ∣ certificate m L*s^2 := by
    have he : certificate m L*s^2=3*(W*(s^2+3*t^2)+W*(s^2-3*t^2)) := by
      dsimp [certificate,W,E,n]; ring
    rw [he]
    exact dvd_mul_of_dvd_right (dvd_add hY hX) _
  have ht : g ∣ certificate m L*t^2 := by
    have he : certificate m L*t^2=W*(s^2+3*t^2)-W*(s^2-3*t^2) := by
      dsimp [certificate,W,E,n]; ring
    rw [he]
    exact dvd_sub hY hX
  obtain ⟨u,v,huv⟩ := (hc.pow : IsCoprime (s^2) (t^2))
  have he : certificate m L=u*(certificate m L*s^2)+v*(certificate m L*t^2) := by
    linear_combination -certificate m L*huv
  rw [he]
  exact dvd_add (dvd_mul_of_dvd_right hs _) (dvd_mul_of_dvd_right ht _)

open RoughSquarefreeConicSetup RoughSquarefreePrimitiveFamily
namespace Progression
variable {D : Data} (P : RoughSquarefreePrimitiveFamily.Progression D)

def bound (P : RoughSquarefreePrimitiveFamily.Progression D) : ℕ := (certificate D.m D.L).natAbs

lemma bound_pos : 0 < bound P := by
  apply Int.natAbs_pos.mpr
  exact certificate_ne (by exact_mod_cast D.L_pos) (by exact_mod_cast D.large')

lemma scale_dvd (x : P.Index) : P.scale x ∣ bound P := by
  obtain ⟨hg,h0,h1,h2,h3⟩ := P.scale_spec x
  have hc : IsCoprime ((P.U x.val:ℤ)+D.shift*P.T x.val) (P.T x.val:ℤ) := by
    have hh := (D.coprime_parameters (x.property 0)).symm.isCoprime
    simpa only [mul_comm] using hh.add_mul_left_left (D.shift:ℤ)
  have hh (i : Fin 4) (v : ℕ) (he : P.root i x.val=P.scale x*v) :
      (P.scale x:ℤ) ∣ RoughConicCoefficientArithmetic.raw
        (D.m:ℤ) D.L ((P.U x.val:ℤ)+D.shift*P.T x.val) (P.T x.val) i := by
    rw [D.raw_eq_eighteen]
    change (P.scale x:ℤ) ∣ 18*(P.root i x.val:ℤ)
    rw [he,Nat.cast_mul]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  apply Int.natCast_dvd.mp
  exact common_divisor hc (hh 0 _ h0) (hh 1 _ h1) (hh 2 _ h2)

lemma scale_le (x : P.Index) : P.scale x ≤ bound P :=
  Nat.le_of_dvd (bound_pos P) (scale_dvd P x)
end Progression

#print axioms common_divisor
#print axioms Progression.scale_le
end Erdos1206.RoughConicCancellation
