import Submission.RoughConicCoefficientArithmetic

/-! Integral normalization of the rough conic coefficients. This is an
auxiliary arithmetic step, not a positive-density Sidon construction. -/
namespace Erdos1206.RoughConicIntegralCoefficients
open RoughConicCoefficientArithmetic

def a (m L : ℤ) (i : Fin 4) : ℤ := leading m L i/18
def b (m L : ℤ) (i : Fin 4) : ℤ := middle m L i/18
def c (m L : ℤ) (i : Fin 4) : ℤ := trailing m L i/18
def qval (m L s t : ℤ) (i : Fin 4) : ℤ :=
  a m L i*s^2+b m L i*s*t+c m L i*t^2

lemma intCast_leading {R : Type*} [CommRing R] (m L : ℤ) (i : Fin 4) :
    ((leading m L i : ℤ) : R)=leading (m:R) (L:R) i := by
  fin_cases i <;> simp [leading,RoughNearUnitConicFamily.norm]
lemma intCast_middle {R : Type*} [CommRing R] (m L : ℤ) (i : Fin 4) :
    ((middle m L i : ℤ) : R)=middle (m:R) (L:R) i := by
  fin_cases i <;> simp [middle,RoughNearUnitConicFamily.norm]
lemma intCast_trailing {R : Type*} [CommRing R] (m L : ℤ) (i : Fin 4) :
    ((trailing m L i : ℤ) : R)=trailing (m:R) (L:R) i := by
  fin_cases i <;> simp [trailing,RoughNearUnitConicFamily.norm]

lemma reconstruction {m L : ℤ} (hm : 18 ∣ m-1) (hL : 18 ∣ L) (i : Fin 4) :
    18*a m L i=leading m L i ∧ 18*b m L i=middle m L i ∧
      18*c m L i=trailing m L i := by
  obtain ⟨ha,hb,hc⟩ := eighteen_dvd hm hL i
  exact ⟨Int.mul_ediv_cancel' ha,Int.mul_ediv_cancel' hb,Int.mul_ediv_cancel' hc⟩

lemma raw_reconstruction {m L : ℤ} (hm : 18 ∣ m-1) (hL : 18 ∣ L)
    (s t : ℤ) (i : Fin 4) : raw m L s t i=18*content m i*qval m L s t i := by
  obtain ⟨ha,hb,hc⟩ := reconstruction hm hL i
  rw [raw_eq_content_mul]
  dsimp [value,qval]
  rw [←ha,←hb,←hc]
  ring

lemma leading_congruence {m L : ℤ} (Q : ℕ)
    (hm : (18*(Q:ℤ)) ∣ m-1) (hL : (18*(Q:ℤ)) ∣ L) (i : Fin 4) :
    (18*(Q:ℤ)) ∣ leading m L i-18 := by
  have hm' : ((18*Q:ℕ):ℤ) ∣ m-1 := by exact_mod_cast hm
  have hL' : ((18*Q:ℕ):ℤ) ∣ L := by exact_mod_cast hL
  have hm0 : (m : ZMod (18*Q))=1 := by
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (m-1) (18*Q)).mpr hm'
    simpa only [Int.cast_sub,Int.cast_one,sub_eq_zero] using hh
  have hL0 : (L : ZMod (18*Q))=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd L (18*Q)).mpr hL'
  have he : ((leading m L i : ℤ) : ZMod (18*Q))=18 := by
    rw [intCast_leading,hm0,hL0]
    fin_cases i <;> norm_num [leading,RoughNearUnitConicFamily.norm]
  have hz : ((leading m L i-18 : ℤ) : ZMod (18*Q))=0 := by
    simpa only [Int.cast_sub,Int.cast_ofNat,sub_eq_zero] using he
  have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (18*Q)).mp hz
  exact_mod_cast hh

lemma a_eq_one_add {m L : ℤ} (Q : ℕ)
    (hm : (18*(Q:ℤ)) ∣ m-1) (hL : (18*(Q:ℤ)) ∣ L) (i : Fin 4) :
    ∃ z : ℤ, a m L i=1+(Q:ℤ)*z := by
  obtain ⟨z,hz⟩ := leading_congruence Q hm hL i
  have he : leading m L i=18*(1+(Q:ℤ)*z) := by linear_combination hz
  refine ⟨z,?_⟩
  dsimp [a]
  rw [he,Int.mul_ediv_cancel_left _ (by norm_num)]

lemma a_coprime {m L : ℤ} (Q : ℕ)
    (hm : (18*(Q:ℤ)) ∣ m-1) (hL : (18*(Q:ℤ)) ∣ L) (i : Fin 4) :
    IsCoprime (a m L i) (Q:ℤ) := by
  obtain ⟨z,hz⟩ := a_eq_one_add Q hm hL i
  refine ⟨1,-z,?_⟩
  rw [hz]
  ring

lemma a_pos {m L : ℤ} (hL0 : 1 ≤ L) (hmL : 12*L ≤ m)
    (hm : 18 ∣ m-1) (hL : 18 ∣ L) (i : Fin 4) : 0 < a m L i := by
  have hh := leading_pos (m := (m:ℝ)) (L := (L:ℝ))
    (by exact_mod_cast hL0) (by exact_mod_cast hmL) i
  rw [←intCast_leading m L i] at hh
  have hpos : 0 < leading m L i := by exact_mod_cast hh
  have ha := (reconstruction hm hL i).1
  omega

lemma discriminant_pos {m L : ℤ} (hL0 : 1 ≤ L) (hmL : 12*L ≤ m)
    (hm : 18 ∣ m-1) (hL : 18 ∣ L) (i : Fin 4) :
    0 < b m L i^2-4*a m L i*c m L i := by
  have hh := RoughConicCoefficientArithmetic.discriminant_pos
    (m := (m:ℝ)) (L := (L:ℝ)) (by exact_mod_cast hL0) (by exact_mod_cast hmL) i
  rw [←intCast_leading m L i,←intCast_middle m L i,←intCast_trailing m L i] at hh
  have hpos : 0 < middle m L i^2-4*leading m L i*trailing m L i := by exact_mod_cast hh
  obtain ⟨ha,hb,hc⟩ := reconstruction hm hL i
  rw [←ha,←hb,←hc] at hpos
  nlinarith only [hpos]


lemma coefficients_mod_prime {m L : ℤ} (Q : ℕ) (h210 : 210 ∣ Q)
    (hm : (18*(Q:ℤ)) ∣ m-1) (hL : (18*(Q:ℤ)) ∣ L)
    (hcop : IsCoprime m L) {p : ℕ} (hp : p.Prime) (i : Fin 4) :
    ((a m L i : ℤ) : ZMod p) ≠ 0 ∨ ((b m L i : ℤ) : ZMod p) ≠ 0 ∨
      ((c m L i : ℤ) : ZMod p) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra! hz
  by_cases hp7 : 7 < p
  · have hbase : ¬ ((m : ZMod p)=0 ∧ (L : ZMod p)=0) := by
      rintro ⟨hm0,hL0⟩
      obtain ⟨u,v,huv⟩ := hcop
      have hh : (u : ZMod p)*m+v*L=1 := by
        simpa only [Int.cast_add,Int.cast_mul,Int.cast_one] using
          congrArg (fun z : ℤ => (z : ZMod p)) huv
      simp [hm0,hL0] at hh
    have hc := large_prime_coefficients hp hp7 (m : ZMod p) (L : ZMod p) hbase i
    have hm18 : 18 ∣ m-1 := (dvd_mul_right 18 (Q:ℤ)).trans hm
    have hL18 : 18 ∣ L := (dvd_mul_right 18 (Q:ℤ)).trans hL
    obtain ⟨ha,hb,hc'⟩ := reconstruction hm18 hL18 i
    have ha0 : leading (m : ZMod p) (L : ZMod p) i=0 := by
      rw [←intCast_leading m L i,←ha]
      simp [hz.1]
    have hb0 : middle (m : ZMod p) (L : ZMod p) i=0 := by
      rw [←intCast_middle m L i,←hb]
      simp [hz.2.1]
    have hc0 : trailing (m : ZMod p) (L : ZMod p) i=0 := by
      rw [←intCast_trailing m L i,←hc']
      simp [hz.2.2]
    exact hc.elim (fun h => h ha0) (fun h => h.elim (fun h => h hb0) (fun h => h hc0))
  · have hp210 : p ∣ 210 := by
      have hple : p ≤ 7 := by omega
      interval_cases p <;> norm_num at hp <;> norm_num
    have hpQ := hp210.trans h210
    have hQ0 : (Q : ZMod p)=0 := (CharP.cast_eq_zero_iff (ZMod p) p Q).mpr hpQ
    obtain ⟨u,v,huv⟩ := a_coprime Q hm hL i
    have hh : (u : ZMod p)*(a m L i : ℤ)+(v : ZMod p)*Q=1 := by
      simpa only [Int.cast_add,Int.cast_mul,Int.cast_one,Int.cast_natCast] using
        congrArg (fun z : ℤ => (z : ZMod p)) huv
    simp [hz.1,hQ0] at hh

lemma primitive {m L : ℤ} (Q : ℕ) (h210 : 210 ∣ Q)
    (hm : (18*(Q:ℤ)) ∣ m-1) (hL : (18*(Q:ℤ)) ∣ L)
    (hcop : IsCoprime m L) (i : Fin 4) :
    Nat.gcd (a m L i).natAbs (Nat.gcd (b m L i).natAbs (c m L i).natAbs)=1 := by
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hpg
  obtain ⟨ha,hbc⟩ := Nat.dvd_gcd_iff.mp hpg
  obtain ⟨hb,hc⟩ := Nat.dvd_gcd_iff.mp hbc
  have ha0 : ((a m L i : ℤ) : ZMod p)=0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (Int.natCast_dvd.mpr ha)
  have hb0 : ((b m L i : ℤ) : ZMod p)=0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (Int.natCast_dvd.mpr hb)
  have hc0 : ((c m L i : ℤ) : ZMod p)=0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (Int.natCast_dvd.mpr hc)
  have hh := coefficients_mod_prime Q h210 hm hL hcop hp i
  exact hh.elim (fun h => h ha0) (fun h => h.elim (fun h => h hb0) (fun h => h hc0))

#print axioms reconstruction
#print axioms a_coprime
#print axioms discriminant_pos
#print axioms primitive
end Erdos1206.RoughConicIntegralCoefficients
