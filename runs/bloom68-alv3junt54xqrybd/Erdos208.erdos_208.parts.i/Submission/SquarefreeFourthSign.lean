import Submission.SquarefreeFourthSignReduction
import Submission.SquarefreeFourthSignExceptional

/-!
# Strict negativity of the four-point large-square-witness determinant

Universal `D₃<0` proof for four integer large-square witnesses.
No higher determinant sign is assumed.
All products, bases, gaps, and quotient drops used in the arithmetic cases
are integers. The final public statements have natural inputs and an integer
determinant.
-/
namespace SquarefreeFourthSign

set_option autoImplicit false

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Gap-coordinate version of the four-point sign theorem. Positive integer
previous minors and quotient drops are hypotheses only in this intermediate
lemma; the public witness theorem below proves them from the interval data. -/
theorem gap_determinant_negative (N H x a b c Q u v h : ℤ)
    (hx : 2 ≤ x) (hHx : H < x)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (_hu : 1 ≤ u) (hv : 1 ≤ v) (_hh : 1 ≤ h)
    (hA : 1 ≤ b*u-a*v) (hB : 1 ≤ c*v-b*h)
    (hn₀ : N < Q*x^2) (hn₀' : Q*x^2 ≤ N+H)
    (hn₁ : N < (Q-u)*(x+a)^2) (hn₁' : (Q-u)*(x+a)^2 ≤ N+H)
    (hn₂ : N < (Q-u-v)*(x+a+b)^2) (hn₂' : (Q-u-v)*(x+a+b)^2 ≤ N+H)
    (hn₃ : N < (Q-u-v-h)*(x+a+b+c)^2) (hn₃' : (Q-u-v-h)*(x+a+b+c)^2 ≤ N+H) :
    a*(a+b)*(c*v-b*h)-c*(b+c)*(b*u-a*v) < 0 := by
  let y := x+a
  let z := x+a+b
  let w := x+a+b+c
  let q₁ := Q-u
  let q₂ := Q-u-v
  let q₃ := Q-u-v-h
  let A := b*u-a*v
  let B := c*v-b*h
  let D := a*(a+b)*B-c*(b+c)*A
  let E := e3 (x : ℝ) y z w
  let C := v3 (x : ℝ) z w*e2 (x : ℝ) z w + v3 (x : ℝ) y z*e2 (x : ℝ) y z
  let C₀ := ((a : ℝ)+b)*((a : ℝ)+c)*((b : ℝ)+c)
  let Ux := (a : ℝ)*((a : ℝ)+b)*((a : ℝ)+b+c)
  let Uw := (c : ℝ)*((b : ℝ)+c)*((a : ℝ)+b+c)
  let L := mixedDet4 (x : ℝ) y z w ((Q : ℝ)*(x : ℝ)^2)
    ((q₁ : ℝ)*(y : ℝ)^2) ((q₂ : ℝ)*(z : ℝ)^2) ((q₃ : ℝ)*(w : ℝ)^2)
  by_contra hnD
  have hD : 0 ≤ D := by change 0 ≤ a*(a+b)*(c*v-b*h)-c*(b+c)*(b*u-a*v); omega
  have hxR : (0 : ℝ) < x := by exact_mod_cast (show (0 : ℤ) < x by omega)
  have haR : (0 : ℝ) < a := by exact_mod_cast (show (0 : ℤ) < a by omega)
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show (0 : ℤ) < b by omega)
  have hcR : (0 : ℝ) < c := by exact_mod_cast (show (0 : ℤ) < c by omega)
  have hxy : (x : ℝ) < y := by dsimp [y]; push_cast; linarith
  have hyz : (y : ℝ) < z := by dsimp [y,z]; push_cast; linarith
  have hzw : (z : ℝ) < w := by dsimp [z,w]; push_cast; linarith
  have hyR : (0 : ℝ) < y := hxR.trans hxy
  have hzR : (0 : ℝ) < z := hyR.trans hyz
  have hwR : (0 : ℝ) < w := hzR.trans hzw
  have hER : 0 < E := e3_pos (x : ℝ) y z w hxR hyR hzR hwR
  have hS₀ : 0 < e2 (x : ℝ) y z := e2_pos (x : ℝ) y z hxR hyR hzR
  have hS₂ : 0 < e2 (y : ℝ) z w := e2_pos (y : ℝ) z w hyR hzR hwR
  have hCR : 0 < C := by
    dsimp [C]
    exact add_pos (mul_pos (v3_pos (x : ℝ) z w (hxy.trans hyz) hzw)
      (e2_pos (x : ℝ) z w hxR hzR hwR))
      (mul_pos (v3_pos (x : ℝ) y z hxy hyz) hS₀)
  have hn₀R : (N : ℝ) < (Q : ℝ)*(x : ℝ)^2 := by exact_mod_cast hn₀
  have hn₀R' : (Q : ℝ)*(x : ℝ)^2 ≤ (N : ℝ)+H := by exact_mod_cast hn₀'
  have hn₁R : (N : ℝ) < (q₁ : ℝ)*(y : ℝ)^2 := by exact_mod_cast hn₁
  have hn₁R' : (q₁ : ℝ)*(y : ℝ)^2 ≤ (N : ℝ)+H := by exact_mod_cast hn₁'
  have hn₂R : (N : ℝ) < (q₂ : ℝ)*(z : ℝ)^2 := by exact_mod_cast hn₂
  have hn₂R' : (q₂ : ℝ)*(z : ℝ)^2 ≤ (N : ℝ)+H := by exact_mod_cast hn₂'
  have hn₃R : (N : ℝ) < (q₃ : ℝ)*(w : ℝ)^2 := by exact_mod_cast hn₃
  have hn₃R' : (q₃ : ℝ)*(w : ℝ)^2 ≤ (N : ℝ)+H := by exact_mod_cast hn₃'
  have hHxR : (H : ℝ) < x := by exact_mod_cast hHx
  have hupper := mixed_upper (N : ℝ) H x y z w
    ((Q : ℝ)*(x : ℝ)^2) ((q₁ : ℝ)*(y : ℝ)^2)
    ((q₂ : ℝ)*(z : ℝ)^2) ((q₃ : ℝ)*(w : ℝ)^2)
    hxR hxy hyz hzw hn₀R hn₁R' hn₂R.le hn₃R'
  change L < (H : ℝ)*C at hupper
  have hhigh : L < (x : ℝ)*C :=
    hupper.trans (mul_lt_mul_of_pos_right hHxR hCR)
  have hAr : ((z : ℝ)-y)*(Q : ℝ)-((z : ℝ)-x)*(q₁ : ℝ)+((y : ℝ)-x)*(q₂ : ℝ) = (A : ℝ) := by
    dsimp [A,y,z,q₁,q₂]
    push_cast
    ring
  have hBr : ((w : ℝ)-z)*(q₁ : ℝ)-((w : ℝ)-y)*(q₂ : ℝ)+((z : ℝ)-y)*(q₃ : ℝ) = (B : ℝ) := by
    dsimp [B,y,z,w,q₁,q₂,q₃]
    push_cast
    ring
  have hdet : det4 (x : ℝ) y z w Q q₁ q₂ q₃ = (D : ℝ) := by
    dsimp [det4,v3,D,A,B,y,z,w,q₁,q₂,q₃]
    push_cast
    ring
  have hidR : L = (B : ℝ)*Ux*E+(D : ℝ)*(x : ℝ)^2*e2 (y : ℝ) z w := by
    dsimp [L]
    rw [mul_comm (Q : ℝ) ((x : ℝ)^2), mul_comm (q₁ : ℝ) ((y : ℝ)^2),
      mul_comm (q₂ : ℝ) ((z : ℝ)^2), mul_comm (q₃ : ℝ) ((w : ℝ)^2)]
    rw [mixed_identity_right,hBr,hdet]
    dsimp [Ux,E,y,z,w]
    push_cast
    ring
  have hidL : L = (A : ℝ)*Uw*E+(D : ℝ)*(w : ℝ)^2*e2 (x : ℝ) y z := by
    dsimp [L]
    rw [mul_comm (Q : ℝ) ((x : ℝ)^2), mul_comm (q₁ : ℝ) ((y : ℝ)^2),
      mul_comm (q₂ : ℝ) ((z : ℝ)^2), mul_comm (q₃ : ℝ) ((w : ℝ)^2)]
    rw [mixed_identity_left,hAr,hdet]
    dsimp [Uw,E,y,z,w]
    push_cast
    ring
  have hDR : (0 : ℝ) ≤ D := by exact_mod_cast hD
  have hlowA : (A : ℝ)*Uw*E ≤ L := by
    have he := mul_nonneg (mul_nonneg hDR (sq_nonneg (w : ℝ))) hS₀.le
    nlinarith only [hidL,he]
  have hlowB : (B : ℝ)*Ux*E ≤ L := by
    have he := mul_nonneg (mul_nonneg hDR (sq_nonneg (x : ℝ))) hS₂.le
    nlinarith only [hidR,he]
  have hcoeffeq : v3 (x : ℝ) z w+v3 (x : ℝ) y z = C₀ := by
    dsimp [v3,C₀,y,z,w]
    push_cast
    ring
  have hcoef := cofactor_weight_lower (x : ℝ) y z w hxR hxy hyz hzw
  rw [hcoeffeq] at hcoef
  change 4*(x : ℝ)*C < 3*E*C₀ at hcoef
  have hsmallA : 4*((A : ℝ)*Uw) < 3*C₀ :=
    small_weight_of_cofactor_bounds (x : ℝ) C L E ((A : ℝ)*Uw) C₀ hER hlowA hhigh hcoef
  have hsmallB : 4*((B : ℝ)*Ux) < 3*C₀ :=
    small_weight_of_cofactor_bounds (x : ℝ) C L E ((B : ℝ)*Ux) C₀ hER hlowB hhigh hcoef
  have hcomb : c*A+a*B = b*(c*u-a*h) := by dsimp [A,B]; ring
  have hcombpos : 0 < c*A+a*B := by
    have hm₁ := mul_le_mul_of_nonneg_left hA (show 0 ≤ c by omega)
    have hm₂ := mul_le_mul_of_nonneg_left hB (show 0 ≤ a by omega)
    change 1 ≤ A at hA
    change 1 ≤ B at hB
    nlinarith only [hm₁,hm₂,ha,hc]
  have hk : 1 ≤ c*u-a*h := by
    by_contra hk
    have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ b by omega) (show c*u-a*h ≤ 0 by omega)
    nlinarith only [hcomb,hcombpos,hm]
  have hgap : b ≤ c*A+a*B := by
    have hm := mul_le_mul_of_nonneg_left hk (show 0 ≤ b by omega)
    nlinarith only [hm,hcomb]
  by_cases hlarge : 2 ≤ A ∨ 2 ≤ B
  · have hg := large_minors_give_large_weight (a : ℝ) b c A B haR hbR hcR
      (by exact_mod_cast hA) (by exact_mod_cast hB) (by exact_mod_cast hlarge) (by exact_mod_cast hgap)
    have h₁ : (A : ℝ)*(c : ℝ)*((b : ℝ)+c)*((a : ℝ)+b+c) = (A : ℝ)*Uw := by dsimp [Uw]; ring
    have h₂ : (B : ℝ)*(a : ℝ)*((a : ℝ)+b)*((a : ℝ)+b+c) = (B : ℝ)*Ux := by dsimp [Ux]; ring
    rw [h₁,h₂] at hg
    have heqC : 3*((a : ℝ)+b)*((a : ℝ)+c)*((b : ℝ)+c) = 3*C₀ := by dsimp [C₀]; ring
    rw [heqC] at hg
    rcases le_total ((A : ℝ)*Uw) ((B : ℝ)*Ux) with h | h
    · rw [max_eq_right h] at hg
      linarith
    · rw [max_eq_left h] at hg
      linarith
  · have hAeq : A = 1 := by change 1 ≤ A at hA; omega
    have hBeq : B = 1 := by change 1 ≤ B at hB; omega
    have hAunit : b*u-a*v = 1 := hAeq
    have hBunit : c*v-b*h = 1 := hBeq
    have hDunit : 0 ≤ a*(a+b)-c*(b+c) := by
      dsimp [D] at hD
      rw [hAeq,hBeq] at hD
      nlinarith only [hD]
    have hsmallunitR : (4 : ℝ)*(a : ℝ)*((a : ℝ)+b)*((a : ℝ)+b+c) <
        3*((a : ℝ)+b)*((a : ℝ)+c)*((b : ℝ)+c) := by
      rw [hBeq] at hsmallB
      norm_num only [Int.cast_one,one_mul] at hsmallB
      dsimp [Ux,C₀] at hsmallB
      nlinarith only [hsmallB]
    have hsmallunit : 4*a*(a+b)*(a+b+c) < 3*(a+b)*(a+c)*(b+c) := by exact_mod_cast hsmallunitR
    obtain ⟨hbsum,hca⟩ := unit_gap_reduction a b c u v h ha hb hc hAunit hBunit hDunit hsmallunit
    by_cases heq : a = c
    · have hmul : a*(2*u-v) = 1 := by
        have hi := hAunit
        rw [hbsum,← heq] at hi
        nlinarith only [hi]
      have haone : a = 1 := by
        rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hmul with hgood | hbad
        · exact hgood.1
        · omega
      have hcone : c = 1 := by omega
      have hbtwo : b = 2 := by omega
      have hvrel : v = 2*u-1 := by rw [haone,hbtwo] at hAunit; omega
      have hhrel : h = u-1 := by rw [hcone,hbtwo,hvrel] at hBunit; omega
      apply exceptional_no_short_interval N H x Q (u-1) hx hHx hn₀ hn₀'
      · convert hn₁ using 1
        rw [haone]
        ring
      · convert hn₁' using 1
        rw [haone]
        ring
      · convert hn₂ using 1
        rw [haone,hbtwo,hvrel]
        ring
      · convert hn₂' using 1
        rw [haone,hbtwo,hvrel]
        ring
      · convert hn₃ using 1
        rw [haone,hbtwo,hcone,hvrel,hhrel]
        ring
      · convert hn₃' using 1
        rw [haone,hbtwo,hcone,hvrel,hhrel]
        ring
    · have hcal : c < a := by omega
      obtain ⟨hb3,hres⟩ := asymmetric_residue a b c u v ha hc hcal hv hbsum hAunit
      have hbsumR : (b : ℝ) = (a : ℝ)+c := by exact_mod_cast hbsum
      have hDformula : D = 2*b*(a-c) := by
        dsimp [D]
        rw [hAeq,hBeq,hbsum]
        ring
      have hmixed :
          (2*(b : ℝ)*(a : ℝ)*((a : ℝ)+b))*e3 (x : ℝ) ((x : ℝ)+a) ((x : ℝ)+a+b) ((x : ℝ)+2*b) +
            (2*(b : ℝ)*((a : ℝ)-c))*(x : ℝ)^2*e2 ((x : ℝ)+a) ((x : ℝ)+a+b) ((x : ℝ)+2*b) <
          (x : ℝ)*(2*(b : ℝ)*(c : ℝ)*((a : ℝ)+b)*e2 (x : ℝ) ((x : ℝ)+a+b) ((x : ℝ)+2*b) +
            (a : ℝ)*(b : ℝ)*((a : ℝ)+b)*e2 (x : ℝ) ((x : ℝ)+a) ((x : ℝ)+a+b)) := by
        have hi := hhigh
        rw [hidR,hBeq,hDformula] at hi
        norm_num only [Int.cast_one,one_mul] at hi
        convert hi using 1 <;> dsimp [Ux,E,C,y,z,w,v3,e2,e3] <;>
          push_cast <;> rw [hbsumR] <;> ring
      let T := (b : ℝ)*((y : ℝ)+z)*((q₁ : ℝ)*(y : ℝ)^2-(Q : ℝ)*(x : ℝ)^2) -
        (a : ℝ)*((x : ℝ)+y)*((q₂ : ℝ)*(z : ℝ)^2-(q₁ : ℝ)*(y : ℝ)^2)
      have hTidentity : T = (a : ℝ)*(v : ℝ)*((a : ℝ)+b)*e2 (x : ℝ) y z -
          (A : ℝ)*((y : ℝ)+z)*(x : ℝ)^2 := by
        have hi := triple_identity (x : ℝ) y z Q q₁ q₂
        rw [hAr] at hi
        dsimp [T]
        convert hi using 1 <;> dsimp [y,z,q₁,q₂] <;> push_cast <;> ring
      have hTcoef : (b : ℝ)*((y : ℝ)+z)+(a : ℝ)*((x : ℝ)+y) =
          ((a : ℝ)+b)*((x : ℝ)+z) := by dsimp [y,z]; push_cast; ring
      have hT₁ := mul_lt_mul_of_pos_left
        (show (q₁ : ℝ)*(y : ℝ)^2-(Q : ℝ)*(x : ℝ)^2 < (H : ℝ) by linarith)
        (show 0 < (b : ℝ)*((y : ℝ)+z) by positivity)
      have hT₂ := mul_lt_mul_of_pos_left
        (show (q₁ : ℝ)*(y : ℝ)^2-(q₂ : ℝ)*(z : ℝ)^2 < (H : ℝ) by linarith)
        (show 0 < (a : ℝ)*((x : ℝ)+y) by positivity)
      have hTupper : T < (H : ℝ)*((a : ℝ)+b)*((x : ℝ)+z) := by
        have hid : T = (b : ℝ)*((y : ℝ)+z)*((q₁ : ℝ)*(y : ℝ)^2-(Q : ℝ)*(x : ℝ)^2) +
            (a : ℝ)*((x : ℝ)+y)*((q₁ : ℝ)*(y : ℝ)^2-(q₂ : ℝ)*(z : ℝ)^2) := by dsimp [T]; ring
        have hsum : T < (H : ℝ)*((b : ℝ)*((y : ℝ)+z)+(a : ℝ)*((x : ℝ)+y)) := by
          nlinarith only [hT₁,hT₂,hid]
        rw [hTcoef] at hsum
        nlinarith only [hsum]
      have hTupperx : T < (x : ℝ)*((a : ℝ)+b)*((x : ℝ)+z) := by
        have hi := mul_lt_mul_of_pos_right hHxR (show 0 < ((a : ℝ)+b)*((x : ℝ)+z) by positivity)
        nlinarith only [hTupper,hi]
      have htriple : (a : ℝ)*(v : ℝ)*((a : ℝ)+b)*e2 (x : ℝ) ((x : ℝ)+a) ((x : ℝ)+a+b) -
          (((x : ℝ)+a)+((x : ℝ)+a+b))*(x : ℝ)^2 <
          (x : ℝ)*((a : ℝ)+b)*((x : ℝ)+((x : ℝ)+a+b)) := by
        rw [hTidentity,hAeq] at hTupperx
        norm_num only [Int.cast_one,one_mul] at hTupperx
        convert hTupperx using 1 <;> dsimp [y,z] <;> push_cast <;> ring
      exact asymmetric_unit_impossible (x : ℝ) a b c v hxR haR hcR
        (by exact_mod_cast (show (0 : ℤ) < v by omega))
        (by exact_mod_cast hb3) hbsumR (by exact_mod_cast hcal) (by exact_mod_cast hres) hmixed htriple

/-- Adjacent integer witnesses have quotient drops at least one. -/
lemma witness_drop_ge_one (N H x y q₀ q₁ : ℕ)
    (hx : H < x) (hxy : x < y) (hq₀ : 0 < q₀)
    (hn₀ : N < q₀*x^2) (hn₁ : q₁*y^2 ≤ N+H) :
    (1 : ℤ) ≤ (q₀ : ℤ)-q₁ := by
  have hr := SquarefreeRothAlgebra.witness_q_decreases_real N H x y q₀ q₁
    (by positivity) (by exact_mod_cast hx)
    (by exact_mod_cast (show x+1 ≤ y by omega))
    (by exact_mod_cast hq₀) (by exact_mod_cast hn₀) (by exact_mod_cast hn₁)
  have hi : (q₁ : ℤ) < q₀ := by exact_mod_cast hr
  omega

/-- Universal strict four-point sign, with natural witness inputs. There are
no minor-sign or higher-order assumptions in this statement. `det4` is exactly
the determinant with rows `1,d,d²,q` (see `det_witnessMatrix`). -/
theorem witness_det4_negative (N H x y z w q₀ q₁ q₂ q₃ : ℕ)
    (hH : 0 < H) (hx : H < x) (hxy : x < y) (hyz : y < z) (hzw : z < w)
    (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hq₃ : 0 < q₃)
    (hn₀ : N < q₀*x^2) (hn₀' : q₀*x^2 ≤ N+H)
    (hn₁ : N < q₁*y^2) (hn₁' : q₁*y^2 ≤ N+H)
    (hn₂ : N < q₂*z^2) (hn₂' : q₂*z^2 ≤ N+H)
    (hn₃ : N < q₃*w^2) (hn₃' : q₃*w^2 ≤ N+H) :
    det4 (x : ℤ) y z w q₀ q₁ q₂ q₃ < 0 := by
  let a := (y : ℤ)-x
  let b := (z : ℤ)-y
  let c := (w : ℤ)-z
  let u := (q₀ : ℤ)-q₁
  let v := (q₁ : ℤ)-q₂
  let h := (q₂ : ℤ)-q₃
  have hxyI : (x : ℤ) < y := by exact_mod_cast hxy
  have hyzI : (y : ℤ) < z := by exact_mod_cast hyz
  have hzwI : (z : ℤ) < w := by exact_mod_cast hzw
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hc : 1 ≤ c := by dsimp [c]; omega
  have hu : 1 ≤ u := witness_drop_ge_one N H x y q₀ q₁ hx hxy hq₀ hn₀ hn₁'
  have hv : 1 ≤ v := witness_drop_ge_one N H y z q₁ q₂ (by omega) hyz hq₁ hn₁ hn₂'
  have hh : 1 ≤ h := witness_drop_ge_one N H z w q₂ q₃ (by omega) hzw hq₂ hn₂ hn₃'
  have hApos := SquarefreeRothAlgebra.witness_determinant_positive N H x y z q₀ q₁ q₂
    hH hx hxy hyz hq₀ hq₁ hq₂ hn₀ hn₀' hn₁ hn₁' hn₂ hn₂'
  have hBpos := SquarefreeRothAlgebra.witness_determinant_positive N H y z w q₁ q₂ q₃
    hH (by omega) hyz hzw hq₁ hq₂ hq₃ hn₁ hn₁' hn₂ hn₂' hn₃ hn₃'
  have hAeq : b*u-a*v = ((z : ℤ)-y)*q₀-((z : ℤ)-x)*q₁+((y : ℤ)-x)*q₂ := by
    dsimp [a,b,u,v]
    ring
  have hBeq : c*v-b*h = ((w : ℤ)-z)*q₁-((w : ℤ)-y)*q₂+((z : ℤ)-y)*q₃ := by
    dsimp [b,c,v,h]
    ring
  have hA : 1 ≤ b*u-a*v := by rw [hAeq]; omega
  have hB : 1 ≤ c*v-b*h := by rw [hBeq]; omega
  have hcore : a*(a+b)*(c*v-b*h)-c*(b+c)*(b*u-a*v) < 0 := by
    apply gap_determinant_negative (N : ℤ) H x a b c q₀ u v h
      (by exact_mod_cast (show 2 ≤ x by omega)) (by exact_mod_cast hx) ha hb hc hu hv hh hA hB
    · exact_mod_cast hn₀
    · exact_mod_cast hn₀'
    · have hi : (N : ℤ) < (q₁ : ℤ)*(y : ℤ)^2 := by exact_mod_cast hn₁
      convert hi using 1
      dsimp [a,u]
      ring
    · have hi : (q₁ : ℤ)*(y : ℤ)^2 ≤ (N : ℤ)+H := by exact_mod_cast hn₁'
      convert hi using 1
      dsimp [a,u]
      ring
    · have hi : (N : ℤ) < (q₂ : ℤ)*(z : ℤ)^2 := by exact_mod_cast hn₂
      convert hi using 1
      dsimp [a,b,u,v]
      ring
    · have hi : (q₂ : ℤ)*(z : ℤ)^2 ≤ (N : ℤ)+H := by exact_mod_cast hn₂'
      convert hi using 1
      dsimp [a,b,u,v]
      ring
    · have hi : (N : ℤ) < (q₃ : ℤ)*(w : ℤ)^2 := by exact_mod_cast hn₃
      convert hi using 1
      dsimp [a,b,c,u,v,h]
      ring
    · have hi : (q₃ : ℤ)*(w : ℤ)^2 ≤ (N : ℤ)+H := by exact_mod_cast hn₃'
      convert hi using 1
      dsimp [a,b,c,u,v,h]
      ring
  have hid : det4 (x : ℤ) y z w q₀ q₁ q₂ q₃ = a*(a+b)*(c*v-b*h)-c*(b+c)*(b*u-a*v) := by
    dsimp [det4,v3,a,b,c,u,v,h]
    ring
  rw [hid]
  exact hcore

/-- The requested universal determinant theorem, in literal matrix form. -/
theorem witness_determinant_negative (N H x y z w q₀ q₁ q₂ q₃ : ℕ)
    (hH : 0 < H) (hx : H < x) (hxy : x < y) (hyz : y < z) (hzw : z < w)
    (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hq₃ : 0 < q₃)
    (hn₀ : N < q₀*x^2) (hn₀' : q₀*x^2 ≤ N+H)
    (hn₁ : N < q₁*y^2) (hn₁' : q₁*y^2 ≤ N+H)
    (hn₂ : N < q₂*z^2) (hn₂' : q₂*z^2 ≤ N+H)
    (hn₃ : N < q₃*w^2) (hn₃' : q₃*w^2 ≤ N+H) :
    Matrix.det (witnessMatrix (x : ℤ) y z w q₀ q₁ q₂ q₃) < 0 := by
  rw [det_witnessMatrix]
  exact witness_det4_negative N H x y z w q₀ q₁ q₂ q₃ hH hx hxy hyz hzw
    hq₀ hq₁ hq₂ hq₃ hn₀ hn₀' hn₁ hn₁' hn₂ hn₂' hn₃ hn₃'

end SquarefreeFourthSign
