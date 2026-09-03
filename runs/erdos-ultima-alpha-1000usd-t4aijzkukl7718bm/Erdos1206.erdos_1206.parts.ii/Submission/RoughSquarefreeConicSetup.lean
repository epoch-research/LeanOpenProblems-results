import Submission.RoughConicIntegralCoefficients
import Submission.PositiveQuadraticShift
import Submission.PrescribedQuadraticSieve

/-! Prime-centered rough conics with positive primitive integral coefficient
forms. Auxiliary setup for simultaneous squarefree values. -/
namespace Erdos1206.RoughSquarefreeConicSetup
open Finset RoughConicIntegralCoefficients PositiveQuadraticShift

structure Data where
  q : ℕ
  q_pos : 0 < q
  multiple210 : 210 ∣ q
  H : ℕ
  m : ℕ
  prime : m.Prime
  modular : Nat.ModEq (18*q) m 1
  large : 12*(18*q)*(H+1) < m

namespace Data
variable (D : Data)
def L : ℕ := 18*D.q

def aa (i : Fin 4) : ℤ := a D.m D.L i
def bb (i : Fin 4) : ℤ := b D.m D.L i
def cc (i : Fin 4) : ℤ := c D.m D.L i

def shift : ℕ := 12*D.m+(∑ i : Fin 4, ((D.bb i).natAbs+(D.cc i).natAbs))+1

def an (i : Fin 4) : ℕ := (D.aa i).toNat
def bn (i : Fin 4) : ℕ := (beta (D.aa i) (D.bb i) D.shift).toNat
def cn (i : Fin 4) : ℕ := (gamma (D.aa i) (D.bb i) (D.cc i) D.shift).toNat
def dn : Fin 4 → ℕ := ![1,1,D.m,D.m]
def A (i : Fin 4) : ℕ := D.dn i*D.an i
def B (i : Fin 4) : ℕ := D.dn i*D.bn i
def C (i : Fin 4) : ℕ := D.dn i*D.cn i
def F (i : Fin 4) (t u : ℕ) : ℕ := QuadraticSquarefreeSieve.quad (D.A i) (D.B i) (D.C i) t u

lemma L_pos : 0 < D.L := by dsimp [L]; exact Nat.mul_pos (by decide) D.q_pos
lemma large' : 12*D.L ≤ D.m := by have := D.large; dsimp [L]; nlinarith
lemma modulus_m : (18*(D.q:ℤ)) ∣ (D.m:ℤ)-1 := by
  have hh := D.modular.symm.dvd
  simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hh
lemma modulus_L : (18*(D.q:ℤ)) ∣ (D.L:ℤ) := by dsimp [L]; norm_cast
lemma eighteen_m : (18:ℤ) ∣ (D.m:ℤ)-1 := (dvd_mul_right _ _).trans D.modulus_m
lemma eighteen_L : (18:ℤ) ∣ (D.L:ℤ) := (dvd_mul_right _ _).trans D.modulus_L
lemma coprime_m_L : IsCoprime (D.m:ℤ) (D.L:ℤ) := by
  obtain ⟨z,hz⟩ := D.modulus_m
  refine ⟨1,-z,?_⟩
  dsimp [L]
  linear_combination hz

lemma aa_pos (i : Fin 4) : 0 < D.aa i :=
  a_pos (by have := D.L_pos; exact_mod_cast this)
    (by exact_mod_cast D.large') D.eighteen_m D.eighteen_L i
lemma shift_large : 12*D.m ≤ D.shift := by dsimp [shift]; omega
lemma shift_bound (i : Fin 4) : |D.bb i|+|D.cc i|+1 ≤ (D.shift:ℤ) := by
  have hh := single_le_sum (f := fun j : Fin 4 => (D.bb j).natAbs+(D.cc j).natAbs)
    (fun _ _ => Nat.zero_le _) (mem_univ i)
  dsimp only at hh
  have hh' : (D.bb i).natAbs+(D.cc i).natAbs+1 ≤ D.shift := by dsimp [shift]; omega
  have hz : ((D.bb i).natAbs:ℤ)+(D.cc i).natAbs+1 ≤ D.shift := by exact_mod_cast hh'
  simpa only [Nat.cast_natAbs,Int.cast_id] using hz
lemma beta_pos (i : Fin 4) : 0 < beta (D.aa i) (D.bb i) (D.shift:ℤ) :=
  (coefficients_pos (D.aa_pos i) (D.shift_bound i)).2.1
lemma gamma_pos (i : Fin 4) : 0 < gamma (D.aa i) (D.bb i) (D.cc i) (D.shift:ℤ) :=
  (coefficients_pos (D.aa_pos i) (D.shift_bound i)).2.2

lemma cast_an (i : Fin 4) : (D.an i:ℤ)=D.aa i := Int.toNat_of_nonneg (D.aa_pos i).le
lemma cast_bn (i : Fin 4) : (D.bn i:ℤ)=beta (D.aa i) (D.bb i) D.shift :=
  Int.toNat_of_nonneg (D.beta_pos i).le
lemma cast_cn (i : Fin 4) : (D.cn i:ℤ)=gamma (D.aa i) (D.bb i) (D.cc i) D.shift :=
  Int.toNat_of_nonneg (D.gamma_pos i).le
lemma cast_dn (i : Fin 4) : (D.dn i:ℤ)=RoughConicCoefficientArithmetic.content (D.m:ℤ) i := by
  fin_cases i <;> simp [dn,RoughConicCoefficientArithmetic.content]
lemma an_pos (i : Fin 4) : 0 < D.an i := by
  have hh := D.aa_pos i
  rw [←D.cast_an] at hh
  exact_mod_cast hh
lemma dn_pos (i : Fin 4) : 0 < D.dn i := by
  have := D.prime.pos
  fin_cases i <;> simp [dn] <;> omega
lemma dn_squarefree (i : Fin 4) : Squarefree (D.dn i) := by
  fin_cases i <;> simp [dn,D.prime.squarefree]
lemma A_pos (i : Fin 4) : 0 < D.A i := Nat.mul_pos (D.dn_pos i) (D.an_pos i)

lemma primitive (i : Fin 4) : Nat.gcd (D.an i) (Nat.gcd (D.bn i) (D.cn i))=1 := by
  apply nat_primitive (D.aa_pos i).le (D.beta_pos i).le (D.gamma_pos i).le
  exact RoughConicIntegralCoefficients.primitive D.q D.multiple210 D.modulus_m D.modulus_L D.coprime_m_L i
lemma discriminant_pos (i : Fin 4) :
    0 < QuadraticSquarefreeSieve.discriminant (D.an i) (D.bn i) (D.cn i) := by
  rw [show D.an i=(D.aa i).toNat from rfl,
    show D.bn i=(beta (D.aa i) (D.bb i) (D.shift:ℤ)).toNat from rfl,
    show D.cn i=(gamma (D.aa i) (D.bb i) (D.cc i) (D.shift:ℤ)).toNat from rfl,
    nat_discriminant (D.aa_pos i).le (D.beta_pos i).le (D.gamma_pos i).le]
  exact RoughConicIntegralCoefficients.discriminant_pos
    (by have := D.L_pos; exact_mod_cast this) (by exact_mod_cast D.large') D.eighteen_m D.eighteen_L i
lemma full_discriminant_ne (i : Fin 4) :
    QuadraticSquarefreeSieve.discriminant (D.A i) (D.B i) (D.C i) ≠ 0 := by
  rw [A,B,C,QuadraticLocalAdmissibility.discriminant_scale]
  exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (D.dn_pos i).ne' : (D.dn i:ℤ) ≠ 0))
    (D.discriminant_pos i).ne'

lemma F_cast (i : Fin 4) (t u : ℕ) : (D.F i t u:ℤ)=
    (D.dn i:ℤ)*qval D.m D.L ((u:ℤ)+D.shift*t) t i := by
  rw [F,A,B,C,QuadraticLocalAdmissibility.quad_scale]
  simp only [QuadraticSquarefreeSieve.quad,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,
    D.cast_an,D.cast_bn,D.cast_cn]
  dsimp [qval,aa,bb,cc,beta,gamma]
  ring

lemma raw_eq_eighteen (i : Fin 4) (t u : ℕ) :
    RoughConicCoefficientArithmetic.raw (D.m:ℤ) D.L ((u:ℤ)+D.shift*t) t i=18*(D.F i t u:ℤ) := by
  rw [raw_reconstruction D.eighteen_m D.eighteen_L,D.F_cast,D.cast_dn]
  ring


lemma identity (t u : ℕ) : D.F 0 t u^3+D.F 3 t u^3=D.F 1 t u^3+D.F 2 t u^3 := by
  have hh := RoughNearUnitConicFamily.identity (D.m:ℤ) (D.L:ℤ) ((u:ℤ)+D.shift*t) (t:ℤ)
  change RoughConicCoefficientArithmetic.raw _ _ _ _ 0^3+
    RoughConicCoefficientArithmetic.raw _ _ _ _ 3^3=
    RoughConicCoefficientArithmetic.raw _ _ _ _ 1^3+
    RoughConicCoefficientArithmetic.raw _ _ _ _ 2^3 at hh
  rw [D.raw_eq_eighteen,D.raw_eq_eighteen,D.raw_eq_eighteen,D.raw_eq_eighteen] at hh
  have he : (D.F 0 t u:ℤ)^3+(D.F 3 t u:ℤ)^3=(D.F 1 t u:ℤ)^3+(D.F 2 t u:ℤ)^3 := by
    nlinarith only [hh]
  exact_mod_cast he

lemma ordered {t : ℕ} (ht : 0 < t) (u : ℕ) :
    0 < D.F 0 t u ∧ D.F 0 t u < D.F 1 t u ∧
      D.F 1 t u < D.F 2 t u ∧ D.F 2 t u < D.F 3 t u := by
  have hk : 12*(D.m:ℤ) ≤ D.shift := by exact_mod_cast D.shift_large
  have hL : (1:ℤ) ≤ D.L := by have := D.L_pos; exact_mod_cast this
  have hm : 12*(D.L:ℤ) ≤ D.m := by exact_mod_cast D.large'
  have hu : 0 ≤ (u:ℤ)+(D.shift-12*(D.m:ℤ))*t := by
    have hh := mul_nonneg (sub_nonneg.mpr hk) (Nat.cast_nonneg t : (0:ℤ) ≤ t)
    linarith [Nat.cast_nonneg u (α := ℤ)]
  have hh := RoughNearUnitConicFamily.ordered_int (t := (t:ℤ)) hL hm hu (by exact_mod_cast ht)
  have harg : (u:ℤ)+(D.shift-12*(D.m:ℤ))*t+12*D.m*t=(u:ℤ)+D.shift*t := by ring
  rw [harg] at hh
  change 0 < RoughConicCoefficientArithmetic.raw _ _ _ _ 0 ∧
    RoughConicCoefficientArithmetic.raw _ _ _ _ 0 < RoughConicCoefficientArithmetic.raw _ _ _ _ 1 ∧
    RoughConicCoefficientArithmetic.raw _ _ _ _ 1 < RoughConicCoefficientArithmetic.raw _ _ _ _ 2 ∧
    RoughConicCoefficientArithmetic.raw _ _ _ _ 2 < RoughConicCoefficientArithmetic.raw _ _ _ _ 3 at hh
  simp only [D.raw_eq_eighteen] at hh
  have he : (0:ℤ) < D.F 0 t u ∧ (D.F 0 t u:ℤ) < D.F 1 t u ∧
      (D.F 1 t u:ℤ) < D.F 2 t u ∧ (D.F 2 t u:ℤ) < D.F 3 t u := by omega
  exact_mod_cast he

lemma near_unit_gap {t : ℕ} (ht : 0 < t) (u : ℕ) :
    D.H*(D.F 1 t u-D.F 0 t u) < (D.H+1)*(D.F 3 t u-D.F 2 t u) := by
  let m : ℤ := D.m
  let L : ℤ := D.L
  let s : ℤ := (u:ℤ)+D.shift*t
  let n : ℤ := RoughNearUnitConicFamily.norm m L
  have hm0 : 0 < m := by dsimp [m]; exact_mod_cast D.prime.pos
  have hL0 : 0 < L := by dsimp [L]; exact_mod_cast D.L_pos
  have hH0 : (0:ℤ) ≤ D.H := Nat.cast_nonneg _
  have hlarge : 12*L*(D.H+1) < m := by
    dsimp [m,L,Data.L]
    exact_mod_cast D.large
  have hcoef : (D.H:ℤ)*3*m^2 < (D.H+1)*n := by
    have hh : 0 < 3*m-9*L*(D.H+1) := by nlinarith
    have hmul := mul_pos hm0 hh
    have hnonneg : 0 ≤ 7*(D.H+1)*L^2 := by positivity
    dsimp [n,RoughNearUnitConicFamily.norm]
    nlinarith only [hmul,hnonneg]
  obtain ⟨ha,hab,hbc,hcd⟩ := D.ordered ht u
  have hgaps := RoughNearUnitConicFamily.gaps m L s (t:ℤ)
  have hBA : RoughNearUnitConicFamily.B m L s (t:ℤ)-RoughNearUnitConicFamily.A m L s (t:ℤ)=
      18*((D.F 1 t u:ℤ)-D.F 0 t u) := by
    have h0 := D.raw_eq_eighteen 0 t u
    have h1 := D.raw_eq_eighteen 1 t u
    change RoughNearUnitConicFamily.A m L s (t:ℤ)=_ at h0
    change RoughNearUnitConicFamily.B m L s (t:ℤ)=_ at h1
    rw [h0,h1]; ring
  have hDC : RoughNearUnitConicFamily.D m L s (t:ℤ)-RoughNearUnitConicFamily.C m L s (t:ℤ)=
      18*((D.F 3 t u:ℤ)-D.F 2 t u) := by
    have h2 := D.raw_eq_eighteen 2 t u
    have h3 := D.raw_eq_eighteen 3 t u
    change RoughNearUnitConicFamily.C m L s (t:ℤ)=_ at h2
    change RoughNearUnitConicFamily.D m L s (t:ℤ)=_ at h3
    rw [h2,h3]; ring
  have hgap : 0 < RoughNearUnitConicFamily.V m L s (t:ℤ)-RoughNearUnitConicFamily.U m L s (t:ℤ) := by
    have hpos : 0 < 18*((D.F 1 t u:ℤ)-D.F 0 t u) := by
      have hh : (D.F 0 t u:ℤ) < D.F 1 t u := by exact_mod_cast hab
      linarith
    rw [←hBA,hgaps.1] at hpos
    exact pos_of_mul_pos_right hpos (by positivity)
  have hmul := mul_lt_mul_of_pos_right hcoef (mul_pos (show (0:ℤ) < 3*m by positivity) hgap)
  have he : (D.H:ℤ)*((D.F 1 t u:ℤ)-D.F 0 t u) <
      (D.H+1)*((D.F 3 t u:ℤ)-D.F 2 t u) := by
    rw [hBA] at hgaps
    rw [hDC] at hgaps
    dsimp [n] at hmul
    nlinarith only [hmul,hgaps.1,hgaps.2]
  have hcast1 : ((D.F 1 t u-D.F 0 t u:ℕ):ℤ)=(D.F 1 t u:ℤ)-D.F 0 t u := Nat.cast_sub hab.le
  have hcast2 : ((D.F 3 t u-D.F 2 t u:ℕ):ℤ)=(D.F 3 t u:ℤ)-D.F 2 t u := Nat.cast_sub hcd.le
  rw [←hcast1,←hcast2] at he
  exact_mod_cast he


set_option maxHeartbeats 2000000 in
lemma raw_eq_eighteen_rat (i : Fin 4) (t u : ℕ) :
    RoughConicCoefficientArithmetic.raw (D.m:ℚ) D.L ((u:ℚ)+D.shift*t) t i=18*(D.F i t u:ℚ) := by
  have hh := congrArg (fun z : ℤ => (z:ℚ)) (D.raw_eq_eighteen i t u)
  fin_cases i <;> simpa [RoughConicCoefficientArithmetic.raw,
    RoughNearUnitConicFamily.A,RoughNearUnitConicFamily.B,RoughNearUnitConicFamily.C,
    RoughNearUnitConicFamily.D,RoughNearUnitConicFamily.U,RoughNearUnitConicFamily.V,
    RoughNearUnitConicFamily.norm,RoughNearUnitConicFamily.den] using hh

lemma scaled_parameter {t u t' u' g h : ℕ} (ht : 0 < t) (hg : 0 < g)
    (h0 : g*D.F 0 t u=h*D.F 0 t' u')
    (h1 : g*D.F 1 t u=h*D.F 1 t' u')
    (h2 : g*D.F 2 t u=h*D.F 2 t' u') : u*t'=u'*t := by
  have hraw (i : Fin 4) (he : g*D.F i t u=h*D.F i t' u') :
      (g:ℚ)*RoughConicCoefficientArithmetic.raw (D.m:ℚ) D.L ((u:ℚ)+D.shift*t) t i=
      (h:ℚ)*RoughConicCoefficientArithmetic.raw (D.m:ℚ) D.L ((u':ℚ)+D.shift*t') t' i := by
    rw [D.raw_eq_eighteen_rat,D.raw_eq_eighteen_rat]
    have hh : (g:ℚ)*D.F i t u=(h:ℚ)*D.F i t' u' := by exact_mod_cast he
    nlinarith only [hh]
  have hh := RoughNearUnitConicFamily.projective_parameter (r' := (h:ℚ))
    (show (0:ℚ) < D.L by exact_mod_cast D.L_pos)
    (show 12*(D.L:ℚ) ≤ D.m by exact_mod_cast D.large')
    (show (g:ℚ) ≠ 0 by exact_mod_cast hg.ne')
    (show (t:ℚ) ≠ 0 by exact_mod_cast ht.ne')
    (hraw 0 h0) (hraw 1 h1) (hraw 2 h2)
  have hcross : (u:ℚ)*t'=(u':ℚ)*t := by nlinarith only [hh]
  exact_mod_cast hcross

lemma coprime_parameters {t u : ℕ} (h : Squarefree (D.F 0 t u)) : Nat.Coprime t u := by
  apply Nat.coprime_of_dvd
  intro p hp hpt hpu
  have hh : p^2 ∣ D.F 0 t u := by
    dsimp [F,QuadraticSquarefreeSieve.quad]
    apply dvd_add
    · apply dvd_add
      · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpu 2) _
      · have hmul := mul_dvd_mul hpt hpu
        simpa only [pow_two,mul_assoc] using dvd_mul_of_dvd_right hmul (D.B 0)
    · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpt 2) _
  exact (Nat.squarefree_iff_prime_squarefree.mp h p hp) (by simpa [pow_two] using hh)

lemma coprime_pair_eq {t u t' u' : ℕ} (ht : 0 < t) (ht' : 0 < t')
    (hc : Nat.Coprime t u) (hc' : Nat.Coprime t' u') (he : u*t'=u'*t) : t=t' ∧ u=u' := by
  have hdt : t ∣ t' := by
    have hh : t ∣ u*t' := by rw [he]; exact dvd_mul_left _ _
    exact hc.dvd_mul_left.mp hh
  have hdt' : t' ∣ t := by
    have hh : t' ∣ u'*t := by rw [←he]; exact dvd_mul_left _ _
    exact hc'.dvd_mul_left.mp hh
  have htt := Nat.dvd_antisymm hdt hdt'
  refine ⟨htt,?_⟩
  rw [←htt] at he
  exact Nat.eq_of_mul_eq_mul_right ht he

end Data

/-- Prime centers can be chosen beyond any requested gap-ratio cutoff. -/
theorem exists_data (Q H : ℕ) (hQ : 0 < Q) : ∃ D : Data, D.q=210*Q ∧ D.H=H := by
  obtain ⟨m,hm,hlarge,hmod⟩ := Nat.exists_prime_gt_modEq_one
    (12*(18*(210*Q))*(H+1)) (by positivity : 18*(210*Q) ≠ 0)
  exact ⟨⟨210*Q,by positivity,dvd_mul_right _ _,H,m,hm,hmod,hlarge⟩,rfl,rfl⟩

#print axioms Data.primitive
#print axioms Data.full_discriminant_ne
#print axioms Data.raw_eq_eighteen
#print axioms exists_data
#print axioms Data.ordered
#print axioms Data.near_unit_gap
#print axioms Data.scaled_parameter
#print axioms Data.coprime_parameters
end Erdos1206.RoughSquarefreeConicSetup
