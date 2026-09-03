import Submission.RoughNearUnitConicFamily
import Submission.QuadraticLocalAdmissibility

/-!
Coefficient arithmetic for the rough near-unit conics. The third and fourth
raw coordinates have an explicit factor m; the displayed forms remove that
factor, but not the common coefficient factor 18. No density conclusion is
asserted here.
-/
namespace Erdos1206.RoughConicCoefficientArithmetic
open RoughNearUnitConicFamily

section Formulas
variable {R : Type*} [CommRing R]

def leading (m L : R) : Fin 4 → R :=
  ![RoughNearUnitConicFamily.norm m L^2+9*m^3*(m-2*L), RoughNearUnitConicFamily.norm m L^2+9*m^3*(m-L),
    9*m^3+3*RoughNearUnitConicFamily.norm m L*(m-2*L), 9*m^3+3*RoughNearUnitConicFamily.norm m L*(m-L)]
def middle (m L : R) : Fin 4 → R :=
  ![-9*m^3*(6*m-8*L), 9*m^3*(6*m-10*L),
    -3*RoughNearUnitConicFamily.norm m L*(6*m-8*L), 3*RoughNearUnitConicFamily.norm m L*(6*m-10*L)]
def trailing (m L : R) : Fin 4 → R :=
  ![3*RoughNearUnitConicFamily.norm m L^2-27*m^3*(m-2*L), 3*RoughNearUnitConicFamily.norm m L^2-27*m^3*(m-L),
    27*m^3-9*RoughNearUnitConicFamily.norm m L*(m-2*L), 27*m^3-9*RoughNearUnitConicFamily.norm m L*(m-L)]
def content (m : R) : Fin 4 → R := ![1,1,m,m]
def value (m L s t : R) (i : Fin 4) : R :=
  leading m L i*s^2+middle m L i*s*t+trailing m L i*t^2

def raw (m L s t : R) : Fin 4 → R := ![A m L s t,B m L s t,C m L s t,D m L s t]

lemma raw_eq_content_mul (m L s t : R) (i : Fin 4) :
    raw m L s t i=content m i*value m L s t i := by
  fin_cases i <;> dsimp [raw,content,value,leading,middle,trailing,A,B,C,D,U,V,den] <;> ring

lemma discriminants (m L : R) :
    middle m L 0^2-4*leading m L 0*trailing m L 0=12*RoughNearUnitConicFamily.norm m L*(108*m^6-RoughNearUnitConicFamily.norm m L^3) ∧
    middle m L 1^2-4*leading m L 1*trailing m L 1=12*RoughNearUnitConicFamily.norm m L*(108*m^6-RoughNearUnitConicFamily.norm m L^3) ∧
    middle m L 2^2-4*leading m L 2*trailing m L 2=36*(4*RoughNearUnitConicFamily.norm m L^3-27*m^6) ∧
    middle m L 3^2-4*leading m L 3*trailing m L 3=36*(4*RoughNearUnitConicFamily.norm m L^3-27*m^6) := by
  dsimp [leading,middle,trailing,RoughNearUnitConicFamily.norm]
  constructor; ring
  constructor; ring
  constructor <;> ring

lemma first_third_combination (m L : R) (i : Fin 4) :
    3*leading m L i+trailing m L i=if i.val < 2 then 6*RoughNearUnitConicFamily.norm m L^2 else 54*m^3 := by
  fin_cases i <;> norm_num [leading,trailing] <;> ring

end Formulas

lemma norm_bounds {m L : ℝ} (hL : 1 ≤ L) (hm : 12*L ≤ m) :
    0 < m ∧ 0 < RoughNearUnitConicFamily.norm m L ∧ 2*m^2 ≤ RoughNearUnitConicFamily.norm m L ∧ RoughNearUnitConicFamily.norm m L ≤ 3*m^2 := by
  have hm0 : 0 < m := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hml : 0 ≤ m-9*L := by linarith
  have hlm : 0 ≤ 9*m-7*L := by linarith
  have hlow : 2*m^2 ≤ RoughNearUnitConicFamily.norm m L := by
    dsimp [RoughNearUnitConicFamily.norm]
    nlinarith [mul_nonneg hm0.le hml,sq_nonneg L]
  have hupp : RoughNearUnitConicFamily.norm m L ≤ 3*m^2 := by
    dsimp [RoughNearUnitConicFamily.norm]
    nlinarith [mul_nonneg hL0 hlm]
  exact ⟨hm0,lt_of_lt_of_le (by positivity) hlow,hlow,hupp⟩

lemma leading_pos {m L : ℝ} (hL : 1 ≤ L) (hm : 12*L ≤ m) (i : Fin 4) :
    0 < leading m L i := by
  obtain ⟨hm0,hn0,_,_⟩ := norm_bounds hL hm
  have hmL : 0 < m-L := by linarith
  have hm2L : 0 < m-2*L := by linarith
  fin_cases i <;> dsimp [leading] <;> positivity

lemma discriminant_pos {m L : ℝ} (hL : 1 ≤ L) (hm : 12*L ≤ m) (i : Fin 4) :
    0 < middle m L i^2-4*leading m L i*trailing m L i := by
  obtain ⟨hm0,hn0,hlo,hhi⟩ := norm_bounds hL hm
  have hp : 0 < m^6 := pow_pos hm0 _
  have h₁ := pow_le_pow_left₀ (by positivity : 0 ≤ 2*m^2) hlo 3
  have h₂ := pow_le_pow_left₀ hn0.le hhi 3
  have hid₁ : (2*m^2)^3=8*m^6 := by ring
  have hid₂ : (3*m^2)^3=27*m^6 := by ring
  rw [hid₁] at h₁
  rw [hid₂] at h₂
  have hfirst : 0 < 12*RoughNearUnitConicFamily.norm m L*(108*m^6-RoughNearUnitConicFamily.norm m L^3) := by
    have h : 0 < 108*m^6-RoughNearUnitConicFamily.norm m L^3 := by linarith
    positivity
  have hlast : 0 < 36*(4*RoughNearUnitConicFamily.norm m L^3-27*m^6) := by nlinarith
  obtain ⟨h0,h1,h2,h3⟩ := discriminants m L
  fin_cases i <;> simp [leading,middle,trailing] at h0 h1 h2 h3 ⊢ <;> linarith

lemma eighteen_dvd {m L : ℤ} (hm : 18 ∣ m-1) (hL : 18 ∣ L) (i : Fin 4) :
    18 ∣ leading m L i ∧ 18 ∣ middle m L i ∧ 18 ∣ trailing m L i := by
  have hm0 : (m : ZMod 18)=1 := by
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (m-1) 18).mpr hm
    simpa only [Int.cast_sub,Int.cast_one,sub_eq_zero] using hh
  have hL0 : (L : ZMod 18)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd L 18).mpr hL
  have hl : ((leading m L i : ℤ) : ZMod 18)=0 := by
    fin_cases i <;> norm_num [leading,RoughNearUnitConicFamily.norm,hm0,hL0] <;> decide +kernel
  have hb : ((middle m L i : ℤ) : ZMod 18)=0 := by
    fin_cases i <;> norm_num [middle,RoughNearUnitConicFamily.norm,hm0,hL0] <;> decide +kernel
  have hc : ((trailing m L i : ℤ) : ZMod 18)=0 := by
    fin_cases i <;> norm_num [trailing,RoughNearUnitConicFamily.norm,hm0,hL0]
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ 18).mp hl,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 18).mp hb,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 18).mp hc⟩


private lemma zero_of_norm_zero {R : Type*} [Field R] {m L : R}
    (h7 : (7:R) ≠ 0) (hm : m=0) (hn : RoughNearUnitConicFamily.norm m L=0) : L=0 := by
  have hh : (7:R)*L^2=0 := by simpa [RoughNearUnitConicFamily.norm,hm] using hn
  exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp ((mul_eq_zero.mp hh).resolve_left h7)

private lemma norm_at_boundary {R : Type*} [Field R] {m L k : R}
    (hk : k=1 ∨ k=2) (hm : m=k*L) : RoughNearUnitConicFamily.norm m L=L^2 := by
  rcases hk with rfl | rfl <;> rw [hm] <;> dsimp [RoughNearUnitConicFamily.norm] <;> ring

private lemma first_pair_zero {R : Type*} [Field R] {m L k : R}
    (h9 : (9:R) ≠ 0) (h7 : (7:R) ≠ 0) (hk : k=1 ∨ k=2)
    (hn : RoughNearUnitConicFamily.norm m L=0)
    (ha : RoughNearUnitConicFamily.norm m L^2+9*m^3*(m-k*L)=0) : m=0 ∧ L=0 := by
  have hh : m^3*(m-k*L)=0 := by
    apply (mul_eq_zero.mp (show (9:R)*(m^3*(m-k*L))=0 by
      simpa [hn,mul_assoc] using ha)).resolve_left h9
  rcases mul_eq_zero.mp hh with hm | hmk
  · have hm0 : m=0 := (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hm
    exact ⟨hm0,zero_of_norm_zero h7 hm0 hn⟩
  · have hm : m=k*L := sub_eq_zero.mp hmk
    have hL2 : L^2=0 := (norm_at_boundary hk hm).symm.trans hn
    have hL : L=0 := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hL2
    exact ⟨by simp [hm,hL],hL⟩

private lemma last_pair_zero {R : Type*} [Field R] {m L k : R}
    (h2 : (2:R) ≠ 0) (h3 : (3:R) ≠ 0) (h7 : (7:R) ≠ 0) (hk : k=1 ∨ k=2)
    (hm : m=0) (ha : 9*m^3+3*RoughNearUnitConicFamily.norm m L*(m-k*L)=0) :
    m=0 ∧ L=0 := by
  have hh : RoughNearUnitConicFamily.norm m L*(m-k*L)=0 := by
    apply (mul_eq_zero.mp (show (3:R)*(RoughNearUnitConicFamily.norm m L*(m-k*L))=0 by
      simpa [hm,mul_assoc] using ha)).resolve_left h3
  rcases mul_eq_zero.mp hh with hn | hmk
  · exact ⟨hm,zero_of_norm_zero h7 hm hn⟩
  · have hk0 : k ≠ 0 := hk.elim (fun h => h ▸ one_ne_zero) (fun h => h ▸ h2)
    have hh : k*L=0 := by simpa [hm] using (sub_eq_zero.mp hmk).symm
    exact ⟨hm,(mul_eq_zero.mp hh).resolve_left hk0⟩

lemma no_common_coefficient_zero {R : Type*} [Field R]
    (h2 : (2:R) ≠ 0) (h3 : (3:R) ≠ 0) (h7 : (7:R) ≠ 0)
    (m L : R) (hbase : ¬ (m=0 ∧ L=0)) (i : Fin 4) :
    leading m L i ≠ 0 ∨ trailing m L i ≠ 0 := by
  have h6 : (6:R) ≠ 0 := by convert mul_ne_zero h2 h3 using 1 <;> norm_num
  have h9 : (9:R) ≠ 0 := by convert pow_ne_zero 2 h3 using 1 <;> norm_num
  have h54 : (54:R) ≠ 0 := by convert mul_ne_zero h2 (pow_ne_zero 3 h3) using 1 <;> norm_num
  by_contra! hh
  obtain ⟨ha,hc⟩ := hh
  have hfirst (hn : (6:R)*RoughNearUnitConicFamily.norm m L^2=0) :
      RoughNearUnitConicFamily.norm m L=0 :=
    (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp ((mul_eq_zero.mp hn).resolve_left h6)
  have hlast (hm : (54:R)*m^3=0) : m=0 :=
    (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp ((mul_eq_zero.mp hm).resolve_left h54)
  apply hbase
  fin_cases i <;> simp [leading,trailing] at ha hc
  · exact first_pair_zero h9 h7 (Or.inr rfl)
      (hfirst (by linear_combination 3*ha+hc)) ha
  · exact first_pair_zero h9 h7 (Or.inl rfl)
      (hfirst (by linear_combination 3*ha+hc)) (by simpa using ha)
  · exact last_pair_zero h2 h3 h7 (Or.inr rfl)
      (hlast (by linear_combination 3*ha+hc)) ha
  · exact last_pair_zero h2 h3 h7 (Or.inl rfl)
      (hlast (by linear_combination 3*ha+hc)) (by simpa using ha)

/-- Away from 2,3,7, the content-removed forms have no prime dividing every
coefficient unless that prime divides both geometric parameters m,L. -/
lemma large_prime_coefficients {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (m L : ZMod p) (hbase : ¬ (m=0 ∧ L=0)) (i : Fin 4) :
    leading m L i ≠ 0 ∨ middle m L i ≠ 0 ∨ trailing m L i ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn (n : ℕ) (hn0 : 0 < n) (hn7 : n ≤ 7) : (n : ZMod p) ≠ 0 := by
    intro hh
    have hd := (CharP.cast_eq_zero_iff (ZMod p) p n).mp hh
    have := Nat.le_of_dvd hn0 hd
    omega
  exact (no_common_coefficient_zero (hn 2 (by decide) (by decide))
    (hn 3 (by decide) (by decide)) (hn 7 (by decide) (by decide)) m L hbase i).elim
      Or.inl (fun h => Or.inr (Or.inr h))

#print axioms raw_eq_content_mul
#print axioms discriminant_pos
#print axioms eighteen_dvd
#print axioms large_prime_coefficients
end Erdos1206.RoughConicCoefficientArithmetic
