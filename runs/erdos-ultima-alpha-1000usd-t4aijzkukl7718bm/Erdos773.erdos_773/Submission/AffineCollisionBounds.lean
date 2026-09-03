import Submission.OrderedCollisionDefect
import Submission.DivisorBound

/-!
Four-distinct-root collision savings for one unit affine progression. The
coefficient savings must be balanced against root height; no improvement to
the exponent in Erdős 773 is asserted.
-/
namespace Erdos773.AffineCollisionBounds
open Finset
set_option maxHeartbeats 2000000

/-- The positive index half-defect is a multiple of q in a unit residue class. -/
theorem normalized_parameters {q r a b c d : ℕ} (hq : 0 < q)
    (hcop : q.Coprime (2*r)) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (he : (q*a+r)^2+(q*d+r)^2 = (q*b+r)^2+(q*c+r)^2) :
    ∃ z y u : ℕ, 0 < z ∧ 0 < y ∧ 0 < u ∧
      b = a+z+2*q*u ∧ c = a+z+2*q*u+y ∧ d = a+2*z+2*q*u+y ∧
      2*u*(q*(a+q*u)+r) = z*(z+y) := by
  have hm : StrictMono (fun n : ℕ => q*n+r) := by
    intro x y hxy
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hxy hq) _
  obtain ⟨Z,Y,T,hZ,hY,hT,hb,hc,hd,hprod⟩ :=
    OrderedCollisionDefect.normalized_parameters (hm hab) (hm hbc) (hm hcd) he
  let z := d-c
  let y := c-b
  have hz : 0 < z := Nat.sub_pos_of_lt hcd
  have hy : 0 < y := Nat.sub_pos_of_lt hbc
  have hzE : Z = q*z := by
    have hh := Nat.sub_add_cancel hcd.le
    dsimp [z]
    nlinarith only [hc,hd,congrArg (q*·) hh]
  have hyE : Y = q*y := by
    have hh := Nat.sub_add_cancel hbc.le
    dsimp [y]
    nlinarith only [hb,hc,congrArg (q*·) hh]
  have hdiv : q ∣ 2*T := by
    have hh : q ∣ q*(a+z)+2*T := by
      convert dvd_mul_right q b using 1
      nlinarith only [hb,hzE]
    exact (Nat.dvd_add_iff_right (dvd_mul_right q (a+z))).mpr hh
  have hq2 : q.Coprime 2 := hcop.of_dvd_right (dvd_mul_right 2 r)
  obtain ⟨t,ht⟩ := hq2.dvd_of_dvd_mul_left hdiv
  have hprod' : 2*t*(q*(a+t)+r) = q*z*(z+y) := by
    apply Nat.eq_of_mul_eq_mul_left hq
    nlinarith only [hprod, congrArg (fun v => 2*v*(q*a+r+v)) ht,
      congrArg (fun v => v*(v+Y)) hzE, congrArg (fun v => q*z*(q*z+v)) hyE]
  have htdiv : q ∣ 2*r*t := by
    have hh : q ∣ q*(2*t*(a+t))+2*r*t := by
      convert dvd_mul_right q (z*(z+y)) using 1
      nlinarith only [hprod']
    exact (Nat.dvd_add_iff_right (dvd_mul_right q (2*t*(a+t)))).mpr hh
  obtain ⟨u,hu⟩ := hcop.dvd_of_dvd_mul_left htdiv
  have hu0 : 0 < u := by
    by_contra! hh
    have : u = 0 := by omega
    simp only [this,mul_zero] at hu
    simp only [hu,mul_zero] at ht
    omega
  have hb' : b = a+z+2*q*u := by
    apply Nat.eq_of_mul_eq_mul_left hq
    nlinarith only [hb,hzE,ht,congrArg (q*·) hu]
  have hc' : c = a+z+2*q*u+y := by
    apply Nat.eq_of_mul_eq_mul_left hq
    nlinarith only [hc,hzE,hyE,ht,congrArg (q*·) hu]
  have hd' : d = a+2*z+2*q*u+y := by
    apply Nat.eq_of_mul_eq_mul_left hq
    nlinarith only [hd,hzE,hyE,ht,congrArg (q*·) hu]
  refine ⟨z,y,u,hz,hy,hu0,hb',hc',hd',?_⟩
  apply Nat.eq_of_mul_eq_mul_left hq
  nlinarith only [hprod',congrArg (fun v => 2*v*(q*(a+v)+r)) hu]

/-- Strictly ordered index quadruples colliding after one affine map. -/
def collisions (N q r : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (((Icc 1 N) ×ˢ (Icc 1 N)) ×ˢ ((Icc 1 N) ×ˢ (Icc 1 N))).filter (fun v =>
    v.1.1 < v.1.2 ∧ v.1.2 < v.2.1 ∧ v.2.1 < v.2.2 ∧
    (q*v.1.1+r)^2+(q*v.2.2+r)^2 = (q*v.1.2+r)^2+(q*v.2.1+r)^2)

/-- The available positive defect parameters, including the offset saving. -/
def defectRange (N q r : ℕ) : ℕ := min (N/(2*q)) (N^2/(8*r+4*q))

private def encode (q : ℕ) (v : (ℕ × ℕ) × (ℕ × ℕ)) : (ℕ × ℕ) × ℕ :=
  ((v.1.1, (v.1.2+v.2.1-v.1.1-v.2.2)/(2*q)), v.2.2-v.2.1)

private lemma encode_spec {N q r : ℕ} (hq : 0 < q) (hcop : q.Coprime (2*r))
    {v : (ℕ × ℕ) × (ℕ × ℕ)} (hv : v ∈ collisions N q r) :
    let a := (encode q v).1.1
    let u := (encode q v).1.2
    let z := (encode q v).2
    ∃ y : ℕ, 0 < z ∧ 0 < y ∧ 0 < u ∧
      v.1.1 = a ∧ v.1.2 = a+z+2*q*u ∧
      v.2.1 = a+z+2*q*u+y ∧ v.2.2 = a+2*z+2*q*u+y ∧
      2*u*(q*(a+q*u)+r) = z*(z+y) := by
  obtain ⟨_,hab,hbc,hcd,he⟩ := mem_filter.mp hv
  obtain ⟨z,y,u,hz,hy,hu,hb,hc,hd,hp⟩ := normalized_parameters hq hcop hab hbc hcd he
  have henc : encode q v = ((v.1.1,u),z) := by
    have hh : v.1.2+v.2.1-v.1.1-v.2.2 = 2*q*u := by omega
    simp only [encode,hh,Nat.mul_div_cancel_left u (show 0 < 2*q by positivity)]
    congr 1
    omega
  rw [henc]
  exact ⟨y,hz,hy,hu,rfl,hb,hc,hd,hp⟩

private lemma span_identity (q r a z y u : ℕ)
    (he : 2*u*(q*(a+q*u)+r) = z*(z+y)) :
    4*u*(2*q*a+2*r+2*q*z+3*q^2*u+q*y)+y^2 = (2*z+2*q*u+y)^2 := by
  nlinarith only [he]

/-- The remaining divisor argument is at most N², not the square of the
larger affine root height. -/
theorem parameter_bounds {N q r : ℕ} (hq : 0 < q) (hcop : q.Coprime (2*r))
    {v : (ℕ × ℕ) × (ℕ × ℕ)} (hv : v ∈ collisions N q r) :
    (encode q v).1.1 ∈ Icc 1 N ∧
      (encode q v).1.2 ∈ Icc 1 (defectRange N q r) ∧
      (encode q v).2 ∈ (2*(encode q v).1.2*
        (q*((encode q v).1.1+q*(encode q v).1.2)+r)).divisors ∧
      2*(encode q v).1.2*(q*((encode q v).1.1+q*(encode q v).1.2)+r) ≤ N^2 := by
  obtain ⟨y,hz,hy,hu,ha,hb,hc,hd,hp⟩ := encode_spec hq hcop hv
  let a := (encode q v).1.1
  let u := (encode q v).1.2
  let z := (encode q v).2
  change 0 < z at hz
  change 0 < u at hu
  change v.1.1 = a at ha
  change v.1.2 = a+z+2*q*u at hb
  change v.2.1 = a+z+2*q*u+y at hc
  change v.2.2 = a+2*z+2*q*u+y at hd
  change 2*u*(q*(a+q*u)+r) = z*(z+y) at hp
  have hm := (mem_filter.mp hv).1
  simp only [mem_product,mem_Icc] at hm
  have hspan : 2*z+2*q*u+y ≤ N := by omega
  have hqbound : u ≤ N/(2*q) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2*q)).mpr
    nlinarith only [hspan]
  have hrbound : u ≤ N^2/(8*r+4*q) := by
    have hh := span_identity q r a z y u hp
    have hsq := Nat.pow_le_pow_left hspan 2
    have hfactor : 2*r+q ≤ 2*q*a+2*r+2*q*z+3*q^2*u+q*y := by
      have hqy := Nat.mul_le_mul_left q hy
      nlinarith only [hqy,Nat.zero_le (q*a),Nat.zero_le (q*z),Nat.zero_le (q^2*u)]
    have hmul := Nat.mul_le_mul_left (4*u) hfactor
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 8*r+4*q)).mpr
    nlinarith only [hh,hsq,hmul]
  have hprod : 2*u*(q*(a+q*u)+r) ≤ N^2 := by
    rw [hp,pow_two]
    exact Nat.mul_le_mul (by omega : z ≤ N) (by omega : z+y ≤ N)
  refine ⟨mem_Icc.mpr ⟨by omega,by omega⟩,
    mem_Icc.mpr ⟨hu,le_min hqbound hrbound⟩,?_,hprod⟩
  exact Nat.mem_divisors.mpr ⟨⟨z+y,hp⟩,by positivity⟩

private lemma encode_injective (N q r : ℕ) (hq : 0 < q) (hcop : q.Coprime (2*r)) :
    Set.InjOn (encode q) (collisions N q r : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
  intro v hv w hw he
  obtain ⟨y,hz,hy,hu,ha,hb,hc,hd,hp⟩ := encode_spec hq hcop hv
  obtain ⟨Y,hZ,hY,hU,hA,hB,hC,hD,hP⟩ := encode_spec hq hcop hw
  rw [← he] at hA hB hC hD hP
  have hyY : y = Y := by
    have hh := Nat.eq_of_mul_eq_mul_left hz (hp.symm.trans hP)
    omega
  apply Prod.ext <;> apply Prod.ext <;> omega

private def parameterSet (N q r : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((Icc 1 N) ×ˢ (Icc 1 (defectRange N q r))).biUnion (fun v =>
    if 2*v.2*(q*(v.1+q*v.2)+r) ≤ N^2 then
      (2*v.2*(q*(v.1+q*v.2)+r)).divisors.image (fun z => (v,z)) else ∅)

/-- A finite divisor sum with one coefficient-dependent defect range. -/
theorem divisor_sum_bound (N q r : ℕ) (hq : 0 < q) (hcop : q.Coprime (2*r)) :
    (collisions N q r).card ≤ ∑ a ∈ Icc 1 N, ∑ u ∈ Icc 1 (defectRange N q r),
      if 2*u*(q*(a+q*u)+r) ≤ N^2 then
        (2*u*(q*(a+q*u)+r)).divisors.card else 0 := by
  have hcount : (collisions N q r).card ≤ (parameterSet N q r).card := by
    apply card_le_card_of_injOn (encode q) _ (encode_injective N q r hq hcop)
    intro v hv
    obtain ⟨ha,hu,hz,hprod⟩ := parameter_bounds hq hcop hv
    exact mem_biUnion.mpr ⟨(encode q v).1,mem_product.mpr ⟨ha,hu⟩,
      by rw [if_pos hprod]; exact mem_image.mpr ⟨(encode q v).2,hz,Prod.eta _⟩⟩
  calc
    _ ≤ (parameterSet N q r).card := hcount
    _ ≤ ∑ v ∈ (Icc 1 N) ×ˢ (Icc 1 (defectRange N q r)),
        if 2*v.2*(q*(v.1+q*v.2)+r) ≤ N^2 then
          (2*v.2*(q*(v.1+q*v.2)+r)).divisors.card else 0 := by
      apply card_biUnion_le.trans
      apply sum_le_sum
      intro v hv
      split_ifs
      · exact card_image_le
      · simp
    _ = _ := by rw [sum_product]

/-- A coefficient-uniform collision bound. Only the index-scale divisor
function is needed. -/
theorem uniform_divisor_bound (N q r : ℕ) (hq : 0 < q) (hcop : q.Coprime (2*r))
    (K : ℝ) (hK : 0 ≤ K)
    (hdiv : ∀ D : ℕ, 0 < D → D ≤ N^2 → (D.divisors.card : ℝ) ≤ K) :
    ((collisions N q r).card : ℝ) ≤ (N : ℝ)*defectRange N q r*K := by
  have hc : ((collisions N q r).card : ℝ) ≤
      ∑ a ∈ Icc 1 N, ∑ u ∈ Icc 1 (defectRange N q r),
        if 2*u*(q*(a+q*u)+r) ≤ N^2 then
          ((2*u*(q*(a+q*u)+r)).divisors.card : ℝ) else 0 := by
    exact_mod_cast divisor_sum_bound N q r hq hcop
  calc
    _ ≤ ∑ _a ∈ Icc 1 N, ∑ _u ∈ Icc 1 (defectRange N q r), K := by
      apply hc.trans
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro u hu
      split_ifs with hD
      · exact hdiv _ (by have := (mem_Icc.mp ha).1; have := (mem_Icc.mp hu).1; positivity) hD
      · exact hK
    _ = _ := by simp [mul_assoc]

/-- Uniform subpower divisor control retains the denominator and offset
savings. It is a bound for one affine progression at a time. -/
theorem collision_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ N q r : ℕ, 0 < q → q.Coprime (2*r) →
      ((collisions N q r).card : ℝ) ≤
        C*(N : ℝ)*defectRange N q r*(N : ℝ)^(2*δ) := by
  obtain ⟨C,hC,hdiv⟩ := divisor_card_subpower δ hδ
  refine ⟨C,hC,?_⟩
  intro N q r hq hcop
  have hh := uniform_divisor_bound N q r hq hcop (C*(N : ℝ)^(2*δ)) (by positivity)
    (fun D hD hDN => (hdiv D).trans (by
      calc
        C*(D : ℝ)^δ ≤ C*((N : ℝ)^2)^δ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hDN) hδ.le) hC.le
        _ = C*(N : ℝ)^(2*δ) := by
          rw [← Real.rpow_natCast_mul (Nat.cast_nonneg N)]; norm_num))
  nlinarith only [hh]

#print axioms normalized_parameters
#print axioms parameter_bounds
#print axioms divisor_sum_bound
#print axioms uniform_divisor_bound
#print axioms collision_subpower
end Erdos773.AffineCollisionBounds
