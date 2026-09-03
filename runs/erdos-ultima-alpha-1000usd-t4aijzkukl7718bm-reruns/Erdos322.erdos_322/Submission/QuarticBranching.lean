import FormalConjecturesUtil

/-! Exact ternary branching on a quartic elliptic curve. This research module
proves no positive-power bound for the original representation count. -/
namespace Erdos322Research.QuarticBranching

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private def F {R : Type*} [CommRing R] (s t : R) : R :=
  3468*s^8 - 612*s^4*t^4 - 140*s^2*t^6 - 9*t^8
private def G {R : Type*} [CommRing R] (s t : R) : R :=
  10404*s^8 + 4760*s^6*t^2 + 612*s^4*t^4 - 3*t^8
private def H {R : Type*} [CommRing R] (s t : R) : R :=
  3468*s^8 + 2312*s^6*t^2 + 612*s^4*t^4 + 72*s^2*t^6 + 3*t^8
private def J {R : Type*} [CommRing R] (s t : R) : R :=
  3468*s^8 + 2448*s^6*t^2 + 612*s^4*t^4 + 68*s^2*t^6 + 3*t^8
private def K {R : Type*} [CommRing R] (s t : R) : R :=
  F s t ^ 4 + 4*t^4*(102*s^4+35*s^2*t^2+3*t^4)*
    (F s t - G s t)*(F s t ^ 2 + G s t ^ 2)

private theorem first_quadric {R : Type*} [CommRing R] (s t : R) :
    (6*s^2+t^2)*H s t ^ 2 = 6*(s*F s t)^2+(t*G s t)^2 := by
  simp only [F, G, H]
  ring

private theorem second_quadric {R : Type*} [CommRing R] (s t : R) :
    (1207*s^2+213*t^2)*J s t ^ 2 = 1207*(s*F s t)^2+213*(t*G s t)^2 := by
  simp only [F, G, J]
  ring

private theorem defect_step {R : Type*} [CommRing R] (s t : R) :
    34*(s*F s t)^4-(t*G s t)^4 = (34*s^4-t^4)*K s t := by
  simp only [F, G, K]
  ring

private theorem mod_three : ∀ s t : ZMod 3, s ≠ 0 → t ≠ 0 →
    F s t = 1 ∧ G s t = 2 ∧ H s t = 2 ∧ J s t = 2 := by
  decide

private theorem mod_nine : ∀ s t : ZMod 9,
    s^2 ≠ 0 → t^2 ≠ 0 → K s t = 6 := by
  decide


@[ext] structure Point (R : Type*) where
  s : R
  t : R
  z : R
  w : R
  deriving DecidableEq

def Point.map {R S : Type*} (f : R → S) (P : Point R) : Point S :=
  ⟨f P.s, f P.t, f P.z, f P.w⟩

def trip {R : Type*} [CommRing R] (P : Point R) : Point R :=
  ⟨-P.s*F P.s P.t, P.t*G P.s P.t, P.z*H P.s P.t, P.w*J P.s P.t⟩

def plus {R : Type*} [CommRing R] (P : Point R) : Point R :=
  ⟨826387624149740010783281*P.s*P.z - 25349208904102897330440*P.t*P.w,
   839031934614575458232081*P.t*P.z + 149803159971211324910640*P.s*P.w,
   221654090335856671785600*P.s^2 - 1234987807373286188790481*P.z^2,
   -1222752558296646539325240*P.s*P.t - 1216376395086711517021681*P.z*P.w⟩

def minus {R : Type*} [CommRing R] (P : Point R) : Point R :=
  ⟨826387624149740010783281*P.s*P.z + 25349208904102897330440*P.t*P.w,
   839031934614575458232081*P.t*P.z - 149803159971211324910640*P.s*P.w,
   221654090335856671785600*P.s^2 - 1234987807373286188790481*P.z^2,
   1222752558296646539325240*P.s*P.t - 1216376395086711517021681*P.z*P.w⟩

def Disk (P : Point (ZMod 3)) : Prop :=
  P.t ≠ 0 ∧ P.s = -P.t ∧ P.z = -P.t ∧ P.w = -P.t

instance (P : Point (ZMod 3)) : Decidable (Disk P) := inferInstanceAs
  (Decidable (P.t ≠ 0 ∧ P.s = -P.t ∧ P.z = -P.t ∧ P.w = -P.t))

structure Good (P : Point ℤ) : Prop where
  quad1 : P.z^2 = 6*P.s^2+P.t^2
  quad2 : P.w^2 = 1207*P.s^2+213*P.t^2
  disk : Disk (P.map (Int.castRingHom (ZMod 3)))

private theorem disk_trip (s t z w : ZMod 3) (h : Disk ⟨s,t,z,w⟩) :
    Disk (trip ⟨s,t,z,w⟩) := by
  revert s t z w
  decide

private theorem disk_plus (s t z w : ZMod 3) (h : Disk ⟨s,t,z,w⟩) :
    Disk (plus ⟨s,t,z,w⟩) := by
  revert s t z w
  decide

private theorem disk_minus (s t z w : ZMod 3) (h : Disk ⟨s,t,z,w⟩) :
    Disk (minus ⟨s,t,z,w⟩) := by
  revert s t z w
  decide

@[simp] theorem map_trip {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : Point R) : (trip P).map f = trip (P.map f) := by
  ext <;> simp [trip, Point.map, F, G, H, J, map_ofNat]

@[simp] theorem map_plus {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : Point R) : (plus P).map f = plus (P.map f) := by
  ext <;> simp [plus, Point.map, map_ofNat]

@[simp] theorem map_minus {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : Point R) : (minus P).map f = minus (P.map f) := by
  ext <;> simp [minus, Point.map, map_ofNat]

theorem Good.trip {P : Point ℤ} (h : Good P) : Good (trip P) := by
  constructor
  · change (P.z*H P.s P.t)^2 = _
    rw [mul_pow, h.quad1, first_quadric]
    simp [Erdos322Research.QuarticBranching.trip]
  · change (P.w*J P.s P.t)^2 = _
    rw [mul_pow, h.quad2, second_quadric]
    simp [Erdos322Research.QuarticBranching.trip]
  · rw [map_trip]
    exact disk_trip _ _ _ _ h.disk

theorem Good.plus {P : Point ℤ} (h : Good P) : Good (plus P) := by
  rcases P with ⟨s,t,z,w⟩
  have h₁ := h.quad1
  have h₂ := h.quad2
  dsimp only at h₁ h₂
  constructor
  · dsimp only [Erdos322Research.QuarticBranching.plus]
    linear_combination (4506190076038550567755073141509564886786296771200*s^2 + 821220297057599805498329525661576285187658620800*t^2 + 1525194884360677032494830804072056622977716211361*z^2)*h₁ + (-22440986737360330999629967058200737003985209600*s^2 - 3855494352383097678395913266016790071303561600*t^2)*h₂
  · dsimp only [Erdos322Research.QuarticBranching.plus]
    linear_combination (961562620215784142837644643493314279515260253545600*s^2 + 165202149758087160872747289578920429370250659217600*t^2)*h₁ + (-4779930175057750502921182983396756981848849644800*s^2 - 775596947221066482970644552013710936010566475200*t^2 + 1479571534524143709967145830424191273800624065761*z^2)*h₂
  · rw [map_plus]
    exact disk_plus _ _ _ _ h.disk

theorem Good.minus {P : Point ℤ} (h : Good P) : Good (minus P) := by
  rcases P with ⟨s,t,z,w⟩
  have h₁ := h.quad1
  have h₂ := h.quad2
  dsimp only at h₁ h₂
  constructor
  · dsimp only [Erdos322Research.QuarticBranching.minus]
    linear_combination (4506190076038550567755073141509564886786296771200*s^2 + 821220297057599805498329525661576285187658620800*t^2 + 1525194884360677032494830804072056622977716211361*z^2)*h₁ + (-22440986737360330999629967058200737003985209600*s^2 - 3855494352383097678395913266016790071303561600*t^2)*h₂
  · dsimp only [Erdos322Research.QuarticBranching.minus]
    linear_combination (961562620215784142837644643493314279515260253545600*s^2 + 165202149758087160872747289578920429370250659217600*t^2)*h₁ + (-4779930175057750502921182983396756981848849644800*s^2 - 775596947221066482970644552013710936010566475200*t^2 + 1479571534524143709967145830424191273800624065761*z^2)*h₂
  · rw [map_minus]
    exact disk_minus _ _ _ _ h.disk

theorem plus_inverse (P : Point ℤ) (h : Good P) :
    (minus (plus P)).s * P.t = P.s * (minus (plus P)).t := by
  rcases P with ⟨s,t,z,w⟩
  have h₁ := h.quad1
  dsimp only at h₁
  dsimp only [plus, minus]
  linear_combination (26006474461370616477147624225027563879731221393964772853661287595953600*s*t*z + 4643270289602927521002458022987628867110643028731498916510756371584000*s^2*w)*h₁

theorem minus_inverse (P : Point ℤ) (h : Good P) :
    (plus (minus P)).s * P.t = P.s * (plus (minus P)).t := by
  rcases P with ⟨s,t,z,w⟩
  have h₁ := h.quad1
  dsimp only at h₁
  dsimp only [minus, plus]
  linear_combination (26006474461370616477147624225027563879731221393964772853661287595953600*s*t*z - 4643270289602927521002458022987628867110643028731498916510756371584000*s^2*w)*h₁

private def diff (s t a b : ℤ) : ℤ :=
  -36081072*s^8*a^8 - 16507680*s^6*t^2*a^8 - 2122416*s^4*t^4*a^8 + 10404*t^8*a^8 - 16507680*s^7*t*a^7*b - 8489664*s^5*t^3*a^7*b - 1456560*s^3*t^5*a^7*b - 83232*s*t^7*a^7*b - 16507680*s^8*a^6*b^2 - 8489664*s^6*t^2*a^6*b^2 - 1456560*s^4*t^4*a^6*b^2 - 83232*s^2*t^6*a^6*b^2 - 8489664*s^7*t*a^5*b^3 - 4369680*s^5*t^3*a^5*b^3 - 749632*s^3*t^5*a^5*b^3 - 42840*s*t^7*a^5*b^3 - 2122416*s^8*a^4*b^4 - 1456560*s^6*t^2*a^4*b^4 - 375088*s^4*t^4*a^4*b^4 - 42840*s^2*t^6*a^4*b^4 - 1836*t^8*a^4*b^4 - 1456560*s^7*t*a^3*b^5 - 749632*s^5*t^3*a^3*b^5 - 128520*s^3*t^5*a^3*b^5 - 7344*s*t^7*a^3*b^5 - 83232*s^6*t^2*a^2*b^6 - 42840*s^4*t^4*a^2*b^6 - 7344*s^2*t^6*a^2*b^6 - 420*t^8*a^2*b^6 - 83232*s^7*t*a*b^7 - 42840*s^5*t^3*a*b^7 - 7344*s^3*t^5*a*b^7 - 420*s*t^7*a*b^7 + 10404*s^8*b^8 - 1836*s^4*t^4*b^8 - 420*s^2*t^6*b^8 - 27*t^8*b^8

private theorem diff_identity (s t a b : ℤ) :
    (-s*F s t)*(b*G a b) - (-a*F a b)*(t*G s t) =
      (s*b-a*t)*diff s t a b := by
  simp only [F,G,diff]
  ring

private theorem diff_mod_nine (s t a b : ℤ) :
    ((diff (-t+3*s) t (-b+3*a) b : ℤ) : ZMod 9) = 6*(t : ZMod 9)^8*(b : ZMod 9)^8 := by
  simp only [diff]
  push_cast
  ring_nf
  simp only [
    show (128027199 : ZMod 9) = 3 by decide,
    show (2622811788 : ZMod 9) = 0 by decide,
    show (23891660028 : ZMod 9) = 0 by decide,
    show (54115840620 : ZMod 9) = 0 by decide,
    show (126296291880 : ZMod 9) = 0 by decide,
    show (358891712604 : ZMod 9) = 0 by decide,
    show (423481616100 : ZMod 9) = 0 by decide,
    show (496335607128 : ZMod 9) = 0 by decide,
    show (921795537096 : ZMod 9) = 0 by decide,
    show (1015081283376 : ZMod 9) = 0 by decide,
    show (1271316571920 : ZMod 9) = 0 by decide,
    show (2641517155224 : ZMod 9) = 0 by decide,
    show (4582023802776 : ZMod 9) = 0 by decide,
    show (7798095970560 : ZMod 9) = 0 by decide,
    show (8917821201240 : ZMod 9) = 0 by decide,
    show (19548424634616 : ZMod 9) = 0 by decide,
    show (21860789790672 : ZMod 9) = 0 by decide,
    show (24541749866088 : ZMod 9) = 0 by decide,
    show (27161092275984 : ZMod 9) = 0 by decide,
    show (75028823373888 : ZMod 9) = 0 by decide,
    show (83383965757944 : ZMod 9) = 0 by decide,
    show (132263873418312 : ZMod 9) = 0 by decide,
    show (183978548661168 : ZMod 9) = 0 by decide,
    show (208657225281168 : ZMod 9) = 0 by decide,
    show (257369841123408 : ZMod 9) = 0 by decide,
    show (417922243336512 : ZMod 9) = 0 by decide,
    show (452151872527536 : ZMod 9) = 0 by decide,
    show (1003850772751728 : ZMod 9) = 0 by decide,
    show (1153675055542032 : ZMod 9) = 0 by decide,
    show (1413358204383504 : ZMod 9) = 0 by decide,
    show (1474968077317296 : ZMod 9) = 0 by decide,
    show (1553171839764912 : ZMod 9) = 0 by decide,
    show (1555070490393408 : ZMod 9) = 0 by decide,
    show (3379304888842176 : ZMod 9) = 0 by decide,
    show (3473511949711728 : ZMod 9) = 0 by decide,
    show (4043117808336096 : ZMod 9) = 0 by decide,
    show (4141791572706432 : ZMod 9) = 0 by decide,
    show (4911045889859424 : ZMod 9) = 0 by decide,
    show (4920990919605072 : ZMod 9) = 0 by decide,
    show (7805678635938096 : ZMod 9) = 0 by decide,
    show (9200221476409440 : ZMod 9) = 0 by decide,
    show (11123733248919072 : ZMod 9) = 0 by decide,
    show (11126573983879776 : ZMod 9) = 0 by decide,
    show (13280352390262944 : ZMod 9) = 0 by decide,
    show (15958831254093792 : ZMod 9) = 0 by decide,
    mul_zero, add_zero, sub_zero, zero_add, neg_zero]
  rw [show (3 : ZMod 9) = -6 by decide]
  ring


theorem Good.t_unit {P : Point ℤ} (h : Good P) : (P.t : ZMod 3) ≠ 0 := h.disk.1

theorem Good.s_mod {P : Point ℤ} (h : Good P) : (P.s : ZMod 3) = -(P.t : ZMod 3) :=
  h.disk.2.1

theorem Good.z_mod {P : Point ℤ} (h : Good P) : (P.z : ZMod 3) = -(P.t : ZMod 3) :=
  h.disk.2.2.1

theorem Good.w_mod {P : Point ℤ} (h : Good P) : (P.w : ZMod 3) = -(P.t : ZMod 3) :=
  h.disk.2.2.2

theorem Good.t_ne {P : Point ℤ} (h : Good P) : P.t ≠ 0 := by
  intro he
  exact h.t_unit (by simp [he])

private theorem nine_unit (a : ℤ) (h : (a : ZMod 3) ≠ 0) : (a : ZMod 9)^2 ≠ 0 := by
  intro he
  have hd : (9 : ℤ) ∣ a^2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using he)
  have hd3 : (3 : ℤ) ∣ a^2 := dvd_trans (by norm_num) hd
  exact h ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (Int.prime_three.dvd_of_dvd_pow hd3))

private theorem diff_ne {P Q : Point ℤ} (hP : Good P) (hQ : Good Q) :
    diff P.s P.t Q.s Q.t ≠ 0 := by
  have hPs : (3 : ℤ) ∣ P.s+P.t := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_add, hP.s_mod, neg_add_cancel]
  have hQs : (3 : ℤ) ∣ Q.s+Q.t := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_add, hQ.s_mod, neg_add_cancel]
  obtain ⟨a,ha⟩ := hPs
  obtain ⟨b,hb⟩ := hQs
  have hs : P.s = -P.t+3*a := by omega
  have ht : Q.s = -Q.t+3*b := by omega
  have hh := diff_mod_nine a P.t b Q.t
  rw [← hs, ← ht] at hh
  have hn : ∀ x y : ZMod 9, x^2 ≠ 0 → y^2 ≠ 0 → 6*x^8*y^8 ≠ 0 := by decide
  intro he
  rw [he, Int.cast_zero] at hh
  exact hn _ _ (nine_unit _ hP.t_unit) (nine_unit _ hQ.t_unit) hh.symm

def ratio (P : Point ℤ) : ℚ := (P.s : ℚ)/P.t

private theorem ratio_eq_iff {P Q : Point ℤ} (hP : Good P) (hQ : Good Q) :
    ratio P = ratio Q ↔ P.s*Q.t = Q.s*P.t := by
  have ht : (P.t : ℚ) ≠ 0 := by exact_mod_cast hP.t_ne
  have hu : (Q.t : ℚ) ≠ 0 := by exact_mod_cast hQ.t_ne
  rw [ratio, ratio, div_eq_div_iff ht hu]
  exact_mod_cast (Iff.rfl : P.s*Q.t = Q.s*P.t ↔ P.s*Q.t = Q.s*P.t)

theorem trip_ratio_injective {P Q : Point ℤ} (hP : Good P) (hQ : Good Q)
    (he : ratio (trip P) = ratio (trip Q)) : ratio P = ratio Q := by
  apply (ratio_eq_iff hP hQ).mpr
  have hc := (ratio_eq_iff hP.trip hQ.trip).mp he
  have hd := diff_identity P.s P.t Q.s Q.t
  change (-P.s*F P.s P.t)*(Q.t*G Q.s Q.t) =
    (-Q.s*F Q.s Q.t)*(P.t*G P.s P.t) at hc
  rw [hc, sub_self] at hd
  exact sub_eq_zero.mp ((mul_eq_zero.mp hd.symm).resolve_right (diff_ne hP hQ))

private theorem cross_square {P Q : Point ℤ} (hP : Good P) (hQ : Good Q)
    (he : P.s*Q.t = Q.s*P.t) :
    P.z*Q.t = Q.z*P.t ∧ P.w*Q.t = Q.w*P.t := by
  have hs : (P.s*Q.t)^2 = (Q.s*P.t)^2 := congrArg (fun x : ℤ ↦ x^2) he
  have hz : (P.z*Q.t)^2 = (Q.z*P.t)^2 := by
    linear_combination Q.t^2*hP.quad1 - P.t^2*hQ.quad1 + 6*hs
  have hw : (P.w*Q.t)^2 = (Q.w*P.t)^2 := by
    linear_combination Q.t^2*hP.quad2 - P.t^2*hQ.quad2 + 1207*hs
  have hnonzero : -(P.t : ZMod 3)*(Q.t : ZMod 3) ≠ (Q.t : ZMod 3)*(P.t : ZMod 3) := by
    have hh : ∀ t u : ZMod 3, t ≠ 0 → u ≠ 0 → -t*u ≠ u*t := by decide
    exact hh _ _ hP.t_unit hQ.t_unit
  constructor
  · rcases eq_or_eq_neg_of_sq_eq_sq _ _ hz with h | h
    · exact h
    · exfalso
      have hc : (P.z : ZMod 3)*(Q.t : ZMod 3) = -((Q.z : ZMod 3)*(P.t : ZMod 3)) := by
        simpa only [Int.cast_mul, Int.cast_neg] using congrArg (fun x : ℤ ↦ (x : ZMod 3)) h
      simp only [hP.z_mod, hQ.z_mod, neg_mul, neg_neg] at hc
      exact hnonzero (by simpa only [neg_mul] using hc)
  · rcases eq_or_eq_neg_of_sq_eq_sq _ _ hw with h | h
    · exact h
    · exfalso
      have hc : (P.w : ZMod 3)*(Q.t : ZMod 3) = -((Q.w : ZMod 3)*(P.t : ZMod 3)) := by
        simpa only [Int.cast_mul, Int.cast_neg] using congrArg (fun x : ℤ ↦ (x : ZMod 3)) h
      simp only [hP.w_mod, hQ.w_mod, neg_mul, neg_neg] at hc
      exact hnonzero (by simpa only [neg_mul] using hc)

private theorem quadratic_cross {P Q : Point ℤ} (he : P.s*Q.t = Q.s*P.t)
    (hz : P.z*Q.t = Q.z*P.t) (hw : P.w*Q.t = Q.w*P.t) :
    P.s*P.z*Q.t^2 = Q.s*Q.z*P.t^2 ∧
    P.t*P.w*Q.t^2 = Q.t*Q.w*P.t^2 ∧
    P.t*P.z*Q.t^2 = Q.t*Q.z*P.t^2 ∧
    P.s*P.w*Q.t^2 = Q.s*Q.w*P.t^2 := by
  constructor
  · linear_combination P.s*Q.t*hz + Q.z*P.t*he
  constructor
  · linear_combination P.t*Q.t*hw
  constructor
  · linear_combination P.t*Q.t*hz
  · linear_combination P.s*Q.t*hw + Q.w*P.t*he

theorem plus_ratio_congr {P Q : Point ℤ} (hP : Good P) (hQ : Good Q)
    (he : ratio P = ratio Q) : ratio (plus P) = ratio (plus Q) := by
  apply (ratio_eq_iff hP.plus hQ.plus).mpr
  have hc := (ratio_eq_iff hP hQ).mp he
  obtain ⟨hz,hw⟩ := cross_square hP hQ hc
  obtain ⟨h₁,h₂,h₃,h₄⟩ := quadratic_cross hc hz hw
  have hs : (plus P).s*Q.t^2 = (plus Q).s*P.t^2 := by
    dsimp only [plus]
    linear_combination 826387624149740010783281*h₁ - 25349208904102897330440*h₂
  have ht : (plus P).t*Q.t^2 = (plus Q).t*P.t^2 := by
    dsimp only [plus]
    linear_combination 839031934614575458232081*h₃ + 149803159971211324910640*h₄
  have hh : ((plus P).s*(plus Q).t-(plus Q).s*(plus P).t)*Q.t^2 = 0 := by
    linear_combination (plus Q).t*hs - (plus Q).s*ht
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right (pow_ne_zero _ hQ.t_ne))

theorem minus_ratio_congr {P Q : Point ℤ} (hP : Good P) (hQ : Good Q)
    (he : ratio P = ratio Q) : ratio (minus P) = ratio (minus Q) := by
  apply (ratio_eq_iff hP.minus hQ.minus).mpr
  have hc := (ratio_eq_iff hP hQ).mp he
  obtain ⟨hz,hw⟩ := cross_square hP hQ hc
  obtain ⟨h₁,h₂,h₃,h₄⟩ := quadratic_cross hc hz hw
  have hs : (minus P).s*Q.t^2 = (minus Q).s*P.t^2 := by
    dsimp only [minus]
    linear_combination 826387624149740010783281*h₁ + 25349208904102897330440*h₂
  have ht : (minus P).t*Q.t^2 = (minus Q).t*P.t^2 := by
    dsimp only [minus]
    linear_combination 839031934614575458232081*h₃ - 149803159971211324910640*h₄
  have hh : ((minus P).s*(minus Q).t-(minus Q).s*(minus P).t)*Q.t^2 = 0 := by
    linear_combination (minus Q).t*hs - (minus Q).s*ht
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right (pow_ne_zero _ hQ.t_ne))

theorem plus_ratio_inverse {P : Point ℤ} (hP : Good P) :
    ratio (minus (plus P)) = ratio P :=
  (ratio_eq_iff hP.plus.minus hP).mpr (plus_inverse P hP)

theorem minus_ratio_inverse {P : Point ℤ} (hP : Good P) :
    ratio (plus (minus P)) = ratio P :=
  (ratio_eq_iff hP.minus.plus hP).mpr (minus_inverse P hP)

theorem plus_ratio_injective {P Q : Point ℤ} (hP : Good P) (hQ : Good Q)
    (he : ratio (plus P) = ratio (plus Q)) : ratio P = ratio Q := by
  have hh := minus_ratio_congr hP.plus hQ.plus he
  rwa [plus_ratio_inverse hP, plus_ratio_inverse hQ] at hh

theorem minus_ratio_injective {P Q : Point ℤ} (hP : Good P) (hQ : Good Q)
    (he : ratio (minus P) = ratio (minus Q)) : ratio P = ratio Q := by
  have hh := plus_ratio_congr hP.minus hQ.minus he
  rwa [minus_ratio_inverse hP, minus_ratio_inverse hQ] at hh


def defect {R : Type*} [CommRing R] (P : Point R) : R := 34*P.s^4-P.t^4

@[simp] theorem map_defect {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : Point R) : f (defect P) = defect (P.map f) := by
  simp [defect, Point.map, map_ofNat]

private theorem cube_mod_nine_zero (a : ℤ) (h : (a : ZMod 3) = 0) :
    (a : ZMod 9)^3 = 0 := by
  obtain ⟨b,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  rw [hb, Int.cast_mul, mul_pow]
  norm_num only [Int.cast_ofNat]
  rw [show (27 : ZMod 9) = 0 by decide, zero_mul]

def Disk9 (P : Point (ZMod 9)) : Prop :=
  P.t^2 ≠ 0 ∧ (P.s+P.t)^3 = 0 ∧ (P.z+P.t)^3 = 0 ∧ (P.w+P.t)^3 = 0

instance (P : Point (ZMod 9)) : Decidable (Disk9 P) := inferInstanceAs
  (Decidable (P.t^2 ≠ 0 ∧ (P.s+P.t)^3 = 0 ∧ (P.z+P.t)^3 = 0 ∧ (P.w+P.t)^3 = 0))

theorem Good.disk9 {P : Point ℤ} (hP : Good P) : Disk9 (P.map (Int.castRingHom (ZMod 9))) := by
  refine ⟨nine_unit _ hP.t_unit, ?_, ?_, ?_⟩
  · have hh := cube_mod_nine_zero (P.s+P.t) (by simp only [Int.cast_add, hP.s_mod, neg_add_cancel])
    simpa only [Point.map, Int.cast_add] using hh
  · have hh := cube_mod_nine_zero (P.z+P.t) (by simp only [Int.cast_add, hP.z_mod, neg_add_cancel])
    simpa only [Point.map, Int.cast_add] using hh
  · have hh := cube_mod_nine_zero (P.w+P.t) (by simp only [Int.cast_add, hP.w_mod, neg_add_cancel])
    simpa only [Point.map, Int.cast_add] using hh

private theorem trip_mod9 : ∀ s t : ZMod 9, t^2 ≠ 0 → (s+t)^3 = 0 →
    34*(-s*F s t)^4-(t*G s t)^4 = 0 := by decide

private theorem translation_mod9 : ∀ s t z w : ZMod 9,
    Disk9 ⟨s,t,z,w⟩ → z^2 = 6*s^2+t^2 → w^2 = 1207*s^2+213*t^2 →
    defect ⟨s,t,z,w⟩ = 0 → defect (plus ⟨s,t,z,w⟩) = 3 ∧ defect (minus ⟨s,t,z,w⟩) = 6 := by
  decide

theorem trip_defect {P : Point ℤ} (hP : Good P) : ((defect (trip P) : ℤ) : ZMod 9) = 0 := by
  have hh := trip_mod9 (P.s : ZMod 9) (P.t : ZMod 9) hP.disk9.1 hP.disk9.2.1
  simpa [defect, trip, F, G] using hh

theorem translate_defect {P : Point ℤ} (hP : Good P) (hd : ((defect P : ℤ) : ZMod 9) = 0) :
    ((defect (plus P) : ℤ) : ZMod 9) = 3 ∧ ((defect (minus P) : ℤ) : ZMod 9) = 6 := by
  have h₁ : (P.z : ZMod 9)^2 = 6*(P.s : ZMod 9)^2+(P.t : ZMod 9)^2 := by
    simpa only [Int.cast_pow, Int.cast_add, Int.cast_mul, Int.cast_ofNat] using
      congrArg (fun x : ℤ ↦ (x : ZMod 9)) hP.quad1
  have h₂ : (P.w : ZMod 9)^2 = 1207*(P.s : ZMod 9)^2+213*(P.t : ZMod 9)^2 := by
    simpa only [Int.cast_pow, Int.cast_add, Int.cast_mul, Int.cast_ofNat] using
      congrArg (fun x : ℤ ↦ (x : ZMod 9)) hP.quad2
  have hh := translation_mod9 (P.s : ZMod 9) (P.t : ZMod 9) (P.z : ZMod 9)
    (P.w : ZMod 9) hP.disk9 h₁ h₂ (by simpa [defect] using hd)
  simpa [defect, plus, minus] using hh

def branch (j : Fin 3) (P : Point ℤ) : Point ℤ :=
  ![trip P, plus (trip P), minus (trip P)] j

theorem Good.branch {P : Point ℤ} (hP : Good P) (j : Fin 3) : Good (branch j P) := by
  fin_cases j
  · exact hP.trip
  · exact hP.trip.plus
  · exact hP.trip.minus

theorem branch_defect {P : Point ℤ} (hP : Good P) (j : Fin 3) :
    ((defect (branch j P) : ℤ) : ZMod 9) = 3*(j.val : ZMod 9) := by
  have hh := translate_defect hP.trip (trip_defect hP)
  fin_cases j
  · simpa only [branch, Matrix.cons_val_zero, Fin.val_zero, Nat.cast_zero, mul_zero] using trip_defect hP
  · simpa only [branch, Matrix.cons_val_one, Fin.val_one, Nat.cast_one, mul_one] using hh.1
  · simpa only [branch, Matrix.cons_val_two, show (2 : Fin 3).val = 2 by rfl,
      Nat.cast_ofNat, show (3 : ZMod 9)*2 = 6 by decide] using hh.2

private theorem branch_residue_unique : ∀ i j : Fin 3, ∀ t u : ZMod 9,
    t^2 ≠ 0 → u^2 ≠ 0 → (3*(i.val : ZMod 9))*u^4 = (3*(j.val : ZMod 9))*t^4 → i = j := by
  decide

theorem branch_index_injective {P Q : Point ℤ} (hP : Good P) (hQ : Good Q)
    {i j : Fin 3} (he : ratio (branch i P) = ratio (branch j Q)) : i = j := by
  have hc := (ratio_eq_iff (hP.branch i) (hQ.branch j)).mp he
  have hpow := congrArg (fun x : ℤ ↦ x^4) hc
  have hd : defect (branch i P)*(branch j Q).t^4 = defect (branch j Q)*(branch i P).t^4 := by
    dsimp only [defect]
    linear_combination 34*hpow
  have hm := congrArg (fun x : ℤ ↦ (x : ZMod 9)) hd
  simp only [Int.cast_mul, Int.cast_pow, branch_defect hP, branch_defect hQ] at hm
  exact branch_residue_unique i j _ _ (hP.branch i).disk9.1 (hQ.branch j).disk9.1 hm

theorem branch_ratio_injective {P Q : Point ℤ} (hP : Good P) (hQ : Good Q)
    (j : Fin 3) (he : ratio (branch j P) = ratio (branch j Q)) : ratio P = ratio Q := by
  apply trip_ratio_injective hP hQ
  fin_cases j
  · exact he
  · exact plus_ratio_injective hP.trip hQ.trip he
  · exact minus_ratio_injective hP.trip hQ.trip he


def point : (d : ℕ) → (Fin d → Fin 3) → Point ℤ
  | 0, _ => ⟨2,1,5,71⟩
  | d+1, f => branch (f 0) (point d (Fin.tail f))

theorem point_good (d : ℕ) (f : Fin d → Fin 3) : Good (point d f) := by
  induction d with
  | zero => constructor <;> dsimp only [point] <;> decide
  | succ d ih => exact (ih (Fin.tail f)).branch (f 0)

theorem point_ratio_injective (d : ℕ) : Function.Injective (fun f : Fin d → Fin 3 ↦ ratio (point d f)) := by
  induction d with
  | zero => intro f g _; exact Subsingleton.elim _ _
  | succ d ih =>
    intro f g he
    have hi : f 0 = g 0 := branch_index_injective (point_good d (Fin.tail f))
      (point_good d (Fin.tail g)) he
    have ht : Fin.tail f = Fin.tail g := by
      apply ih
      have hh : ratio (branch (g 0) (point d (Fin.tail f))) =
          ratio (branch (g 0) (point d (Fin.tail g))) := by
        simpa only [point, hi] using he
      exact branch_ratio_injective (point_good d (Fin.tail f))
        (point_good d (Fin.tail g)) (g 0) hh
    funext i
    refine Fin.cases hi (fun j ↦ ?_) i
    exact congrFun ht j

private theorem ratio_square_injective {P Q : Point ℤ} (hP : Good P) (hQ : Good Q)
    (he : ratio P ^ 2 = ratio Q ^ 2) : ratio P = ratio Q := by
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ he with he | he
  · exact he
  · exfalso
    have ht : (P.t : ℚ) ≠ 0 := by exact_mod_cast hP.t_ne
    have hu : (Q.t : ℚ) ≠ 0 := by exact_mod_cast hQ.t_ne
    have hc : (P.s : ℚ)*(Q.t : ℚ) = (-Q.s : ℚ)*(P.t : ℚ) := by
      apply (div_eq_div_iff ht hu).mp
      simpa only [ratio, neg_div] using he
    have hc' : P.s*Q.t = -Q.s*P.t := by exact_mod_cast hc
    have hm := congrArg (fun x : ℤ ↦ (x : ZMod 3)) hc'
    simp only [Int.cast_mul, Int.cast_neg, hP.s_mod, hQ.s_mod, neg_neg] at hm
    have hn : ∀ t u : ZMod 3, t ≠ 0 → u ≠ 0 → -t*u ≠ u*t := by decide
    exact hn _ _ hP.t_unit hQ.t_unit hm

theorem point_squared_ratio_injective (d : ℕ) :
    Function.Injective (fun f : Fin d → Fin 3 ↦ ratio (point d f)^2) := by
  intro f g he
  exact point_ratio_injective d (ratio_square_injective (point_good d f) (point_good d g) he)

theorem Good.w_ne {P : Point ℤ} (hP : Good P) : P.w ≠ 0 := by
  intro he
  have hh := hP.w_mod
  rw [he, Int.cast_zero] at hh
  exact hP.t_unit (neg_eq_zero.mp hh.symm)

def rationalTriple (P : Point ℤ) : Fin 3 → ℚ :=
  ![71*(P.s+P.t)/P.w, 71*(P.s-P.t)/P.w, 142*P.z/P.w]

theorem rationalTriple_sum {P : Point ℤ} (hP : Good P) :
    ∑ i, rationalTriple P i ^ 4 = 10082 := by
  have hw : (P.w : ℚ) ≠ 0 := by exact_mod_cast hP.w_ne
  have h₁ : (P.z : ℚ)^2 = 6*(P.s : ℚ)^2+(P.t : ℚ)^2 := by exact_mod_cast hP.quad1
  have h₂ : (P.w : ℚ)^2 = 1207*(P.s : ℚ)^2+213*(P.t : ℚ)^2 := by exact_mod_cast hP.quad2
  simp only [rationalTriple, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  field_simp
  linear_combination (142 : ℚ)^4 * congrArg (fun x : ℚ ↦ x^2) h₁ -
    10082 * congrArg (fun x : ℚ ↦ x^2) h₂

private theorem ratio_recovery {P : Point ℤ} (hP : Good P) : ratio P ^ 2 =
    (rationalTriple P 2 ^ 2 - 2*(rationalTriple P 0 ^ 2 + rationalTriple P 1 ^ 2)) /
    (12*(rationalTriple P 0 ^ 2 + rationalTriple P 1 ^ 2)-rationalTriple P 2 ^ 2) := by
  have ht : (P.t : ℚ) ≠ 0 := by exact_mod_cast hP.t_ne
  have hw : (P.w : ℚ) ≠ 0 := by exact_mod_cast hP.w_ne
  have h₁ : (P.z : ℚ)^2 = 6*(P.s : ℚ)^2+(P.t : ℚ)^2 := by exact_mod_cast hP.quad1
  have hd : 12*(rationalTriple P 0 ^ 2 + rationalTriple P 1 ^ 2)-rationalTriple P 2 ^ 2 =
      100820 * (P.t : ℚ)^2 / (P.w : ℚ)^2 := by
    simp only [rationalTriple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp
    linear_combination -20164 * h₁
  rw [hd]
  simp only [ratio, rationalTriple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  field_simp
  linear_combination -20164 * h₁

theorem point_squared_triple_injective (d : ℕ) :
    Function.Injective (fun f : Fin d → Fin 3 ↦ fun i : Fin 3 ↦ rationalTriple (point d f) i ^ 2) := by
  intro f g he
  apply point_squared_ratio_injective d
  have hi : ∀ i, rationalTriple (point d f) i ^ 2 = rationalTriple (point d g) i ^ 2 := congrFun he
  change ratio (point d f)^2 = ratio (point d g)^2
  rw [ratio_recovery (point_good d f), ratio_recovery (point_good d g), hi 0, hi 1, hi 2]


private theorem coordinates_bound {P : Point ℤ} (hP : Good P) {B : ℝ}
    (hb : |(P.w : ℝ)| ≤ B) : |(P.s : ℝ)| ≤ B ∧ |(P.t : ℝ)| ≤ B ∧ |(P.z : ℝ)| ≤ B := by
  have h₁ : (P.z : ℝ)^2 = 6*(P.s : ℝ)^2+(P.t : ℝ)^2 := by exact_mod_cast hP.quad1
  have h₂ : (P.w : ℝ)^2 = 1207*(P.s : ℝ)^2+213*(P.t : ℝ)^2 := by exact_mod_cast hP.quad2
  have hs := sq_nonneg (P.s : ℝ)
  have ht := sq_nonneg (P.t : ℝ)
  exact ⟨(sq_le_sq.mp (by nlinarith : (P.s : ℝ)^2 ≤ (P.w : ℝ)^2)).trans hb,
    (sq_le_sq.mp (by nlinarith : (P.t : ℝ)^2 ≤ (P.w : ℝ)^2)).trans hb,
    (sq_le_sq.mp (by nlinarith : (P.z : ℝ)^2 ≤ (P.w : ℝ)^2)).trans hb⟩

private theorem trip_w_bound {P : Point ℤ} (hP : Good P) {B : ℝ} (hB : 0 ≤ B)
    (hb : |(P.w : ℝ)| ≤ B) : |((trip P).w : ℝ)| ≤ 6599*B^9 := by
  obtain ⟨hs,ht,hz⟩ := coordinates_bound hP hb
  have hJ : |J (P.s : ℝ) (P.t : ℝ)| ≤ 6599*B^8 := by
    unfold J
    have he : (3468 : ℝ)*(P.s : ℝ)^8 + 2448*(P.s : ℝ)^6*(P.t : ℝ)^2 +
        612*(P.s : ℝ)^4*(P.t : ℝ)^4 + 68*(P.s : ℝ)^2*(P.t : ℝ)^6 + 3*(P.t : ℝ)^8 =
        3468*|(P.s : ℝ)|^8 + 2448*|(P.s : ℝ)|^6*|(P.t : ℝ)|^2 +
        612*|(P.s : ℝ)|^4*|(P.t : ℝ)|^4 + 68*|(P.s : ℝ)|^2*|(P.t : ℝ)|^6 + 3*|(P.t : ℝ)|^8 := by
      simp only [Even.pow_abs (by decide : Even 8), Even.pow_abs (by decide : Even 6),
        Even.pow_abs (by decide : Even 4), sq_abs]
    rw [he, abs_of_nonneg (by positivity)]
    calc
      _ ≤ 3468*B^8 + 2448*B^6*B^2 + 612*B^4*B^4 + 68*B^2*B^6 + 3*B^8 := by gcongr
      _ = 6599*B^8 := by ring
  have he : ((trip P).w : ℝ) = (P.w : ℝ)*J (P.s : ℝ) (P.t : ℝ) := by
    simp [trip, J]
  rw [he, abs_mul]
  calc
    _ ≤ B*(6599*B^8) := mul_le_mul hb hJ (abs_nonneg _) hB
    _ = _ := by ring

private theorem translate_w_bound {P : Point ℤ} (hP : Good P) {B : ℝ} (hB : 0 ≤ B)
    (hb : |(P.w : ℝ)| ≤ B) :
    |((plus P).w : ℝ)| ≤ 3000000000000000000000000*B^2 ∧
    |((minus P).w : ℝ)| ≤ 3000000000000000000000000*B^2 := by
  obtain ⟨hs,ht,hz⟩ := coordinates_bound hP hb
  have h₁ : |(1222752558296646539325240 : ℝ)*(P.s : ℝ)*(P.t : ℝ)| ≤
      1222752558296646539325240*B^2 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num)]
    calc
      _ ≤ 1222752558296646539325240*B*B := by gcongr
      _ = _ := by ring
  have h₂ : |(1216376395086711517021681 : ℝ)*(P.z : ℝ)*(P.w : ℝ)| ≤
      1216376395086711517021681*B^2 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num)]
    calc
      _ ≤ 1216376395086711517021681*B*B := by gcongr
      _ = _ := by ring
  constructor
  · have he : ((plus P).w : ℝ) = -(1222752558296646539325240*(P.s : ℝ)*(P.t : ℝ)) -
        1216376395086711517021681*(P.z : ℝ)*(P.w : ℝ) := by simp [plus]
    rw [he]
    calc
      _ ≤ |(1222752558296646539325240 : ℝ)*(P.s : ℝ)*(P.t : ℝ)| +
          |(1216376395086711517021681 : ℝ)*(P.z : ℝ)*(P.w : ℝ)| := by
        simpa only [abs_neg, sub_zero, zero_sub] using abs_sub_le (-(1222752558296646539325240*(P.s : ℝ)*(P.t : ℝ)))
          0 (1216376395086711517021681*(P.z : ℝ)*(P.w : ℝ))
      _ ≤ 3000000000000000000000000*B^2 := by nlinarith [sq_nonneg B]
  · have he : ((minus P).w : ℝ) = 1222752558296646539325240*(P.s : ℝ)*(P.t : ℝ) -
        1216376395086711517021681*(P.z : ℝ)*(P.w : ℝ) := by simp [minus]
    rw [he]
    calc
      _ ≤ |(1222752558296646539325240 : ℝ)*(P.s : ℝ)*(P.t : ℝ)| +
          |(1216376395086711517021681 : ℝ)*(P.z : ℝ)*(P.w : ℝ)| := by
            simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le
              (1222752558296646539325240*(P.s : ℝ)*(P.t : ℝ)) 0
              (1216376395086711517021681*(P.z : ℝ)*(P.w : ℝ))
      _ ≤ 3000000000000000000000000*B^2 := by nlinarith [sq_nonneg B]

private theorem branch_w_bound {P : Point ℤ} (hP : Good P) {B : ℝ} (hB : 10^40 ≤ B)
    (hb : |(P.w : ℝ)| ≤ B) (j : Fin 3) : |((branch j P).w : ℝ)| ≤ B^20 := by
  have hB0 : 0 ≤ B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have ht := trip_w_bound hP hB0 hb
  have hp := translate_w_bound hP.trip (by positivity : (0 : ℝ) ≤ 6599*B^9) ht
  have hs : (10^40 : ℝ)*B^18 ≤ B^20 := by
    calc
      (10^40 : ℝ)*B^18 ≤ B^2*B^18 := by
        gcongr
        calc
          (10^40 : ℝ) ≤ B := hB
          _ ≤ B^2 := by nlinarith
      _ = B^20 := by ring
  have ht' : (6599 : ℝ)*B^9 ≤ B^20 := by
    calc
      _ ≤ (10^40 : ℝ)*B^18 := by
        gcongr
        · norm_num
        · exact hB1
        · norm_num
      _ ≤ _ := hs
  have hp' : (3000000000000000000000000 : ℝ)*(6599*B^9)^2 ≤ B^20 := by
    calc
      _ = (3000000000000000000000000 : ℝ)*6599^2*B^18 := by ring
      _ ≤ (10^40 : ℝ)*B^18 := by gcongr; norm_num
      _ ≤ _ := hs
  fin_cases j
  · exact ht.trans ht'
  · exact hp.1.trans hp'
  · exact hp.2.trans hp'

theorem point_w_bound (d : ℕ) (f : Fin d → Fin 3) :
    |((point d f).w : ℝ)| ≤ (10^40 : ℝ)^(20^d) := by
  induction d with
  | zero => norm_num [point]
  | succ d ih =>
    have hB : (10^40 : ℝ) ≤ (10^40 : ℝ)^(20^d) := by
      apply le_self_pow₀ (by norm_num)
      positivity
    have hh := branch_w_bound (point_good d (Fin.tail f)) hB (ih (Fin.tail f)) (f 0)
    change |((branch (f 0) (point d (Fin.tail f))).w : ℝ)| ≤ (10^40 : ℝ)^(20^(d+1))
    rw [pow_succ (20 : ℕ) d, pow_mul]
    exact hh

def integerTriple (d : ℕ) (f : Fin d → Fin 3) : Fin 3 → ℤ :=
  ![71*((point d f).s+(point d f).t), 71*((point d f).s-(point d f).t), 142*(point d f).z]

private theorem rationalTriple_eq (d : ℕ) (f : Fin d → Fin 3) (i : Fin 3) :
    rationalTriple (point d f) i = (integerTriple d f i : ℚ) / (point d f).w := by
  fin_cases i <;> simp [rationalTriple, integerTriple]

theorem integerTriple_sum (d : ℕ) (f : Fin d → Fin 3) :
    ∑ i, integerTriple d f i ^ 4 = 10082 * (point d f).w^4 := by
  have h := rationalTriple_sum (point_good d f)
  simp only [rationalTriple_eq, div_pow, ← Finset.sum_div] at h
  have hw : ((point d f).w : ℚ) ≠ 0 := by exact_mod_cast (point_good d f).w_ne
  have he := (div_eq_iff (pow_ne_zero 4 hw)).mp h
  exact_mod_cast he

private theorem norm_three_obstruction (a b w : ℤ) (hw : (w : ZMod 3) ≠ 0) :
    a^2+a*b+b^2 ≠ 71*w^2 := by
  intro he
  have hc : (a : ZMod 3)^2+(a : ZMod 3)*b+b^2 = 71*(w : ZMod 3)^2 := by
    simpa using congrArg (Int.castRingHom (ZMod 3)) he
  have hw2 : (w : ZMod 3)^2 = 1 := by
    have h : ∀ x : ZMod 3, x ≠ 0 → x^2 = 1 := by decide
    exact h _ hw
  rw [hw2] at hc
  norm_num at hc
  have h : ∀ x y : ZMod 3, x^2+x*y+y^2 ≠ 71 := by decide
  exact h _ _ hc

private theorem not_additive_of_sum (a b c w : ℤ)
    (hs : a^4+b^4+c^4 = 10082*w^4) (hw : (w : ZMod 3) ≠ 0) : c ≠ a+b := by
  intro he
  rw [he] at hs
  have hi : a^4+b^4+(a+b)^4 = 2*(a^2+a*b+b^2)^2 := by ring
  rw [hi] at hs
  have hsq : (a^2+a*b+b^2)^2 = (71*w^2)^2 := by nlinarith [hs]
  have hp : 0 ≤ a^2+a*b+b^2 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a+b)]
  exact norm_three_obstruction a b w hw ((sq_eq_sq₀ hp (by positivity)).mp hsq)

theorem integerTriple_abs_nonadditive (d : ℕ) (f : Fin d → Fin 3) (σ : Equiv.Perm (Fin 3)) :
    |integerTriple d f (σ 2)| ≠ |integerTriple d f (σ 0)| + |integerTriple d f (σ 1)| := by
  have hs : ∑ i, |integerTriple d f (σ i)| ^ 4 = 10082 * (point d f).w^4 := by
    simpa only [Even.pow_abs (by decide : Even 4)] using
      (Equiv.sum_comp σ (fun i ↦ integerTriple d f i ^ 4)).trans (integerTriple_sum d f)
  simp only [Fin.sum_univ_three] at hs
  exact not_additive_of_sum _ _ _ _ hs (by
    intro he
    have hh := (point_good d f).w_mod
    rw [he] at hh
    exact (point_good d f).t_unit (neg_eq_zero.mp hh.symm))

private def natTriple (d : ℕ) (f : Fin d → Fin 3) (i : Fin 3) : ℕ := (integerTriple d f i).natAbs

private theorem natTriple_sum (d : ℕ) (f : Fin d → Fin 3) :
    ∑ i, natTriple d f i ^ 4 = 10082 * (point d f).w.natAbs^4 := by
  have hi := integerTriple_sum d f
  have h : ∑ i, (natTriple d f i : ℤ)^4 = 10082 * ((point d f).w.natAbs : ℤ)^4 := by
    simpa only [natTriple, Int.natCast_natAbs, Even.pow_abs (by decide : Even 4)] using hi
  exact_mod_cast h

private theorem natTriple_nonadditive (d : ℕ) (f : Fin d → Fin 3) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    natTriple d f k ≠ natTriple d f i + natTriple d f j := by
  have h₀ := integerTriple_abs_nonadditive d f (Equiv.refl _)
  have h₁ := integerTriple_abs_nonadditive d f (Equiv.swap 1 2)
  have h₂ := integerTriple_abs_nonadditive d f (Equiv.swap 0 2)
  simp only [Equiv.refl_apply] at h₀
  simp [Equiv.swap_apply_def, Fin.ext_iff] at h₁ h₂
  have hh₀ : natTriple d f 2 ≠ natTriple d f 0 + natTriple d f 1 := by
    have h : (natTriple d f 2 : ℤ) ≠ (natTriple d f 0 : ℤ) + natTriple d f 1 := by
      simpa only [natTriple, Int.natCast_natAbs] using h₀
    exact_mod_cast h
  have hh₁ : natTriple d f 1 ≠ natTriple d f 0 + natTriple d f 2 := by
    have h : (natTriple d f 1 : ℤ) ≠ (natTriple d f 0 : ℤ) + natTriple d f 2 := by
      simpa only [natTriple, Int.natCast_natAbs] using h₁
    exact_mod_cast h
  have hh₂ : natTriple d f 0 ≠ natTriple d f 2 + natTriple d f 1 := by
    have h : (natTriple d f 0 : ℤ) ≠ (natTriple d f 2 : ℤ) + natTriple d f 1 := by
      simpa only [natTriple, Int.natCast_natAbs] using h₂
    exact_mod_cast h
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> omega

def commonDenominator (d : ℕ) : ℕ := ∏ i : (Fin d → Fin 3), (point d i).w.natAbs

private theorem commonDenominator_pos (d : ℕ) : 0 < commonDenominator d := by
  apply Finset.prod_pos
  intro i _
  exact Int.natAbs_pos.mpr ((point_good d i).w_ne)

private theorem point_denominator_dvd (d : ℕ) (i : (Fin d → Fin 3)) :
    (point d i).w.natAbs ∣ commonDenominator d :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

private def scale (d : ℕ) (i : (Fin d → Fin 3)) : ℕ := commonDenominator d / (point d i).w.natAbs

private theorem scale_mul (d : ℕ) (i : (Fin d → Fin 3)) :
    (point d i).w.natAbs * scale d i = commonDenominator d :=
  Nat.mul_div_cancel' (point_denominator_dvd d i)

private theorem scale_pos (d : ℕ) (i : (Fin d → Fin 3)) : 0 < scale d i :=
  Nat.div_pos (Nat.le_of_dvd (commonDenominator_pos d) (point_denominator_dvd d i))
    (Int.natAbs_pos.mpr ((point_good d i).w_ne))

private def tuple (d : ℕ) (i : (Fin d → Fin 3)) : Fin 4 → ℕ :=
  Fin.snoc (fun j : Fin 3 ↦ 2 * natTriple d i j * scale d i) 1

def representedNumber (d : ℕ) : ℕ := 10082 * (2*commonDenominator d)^4+1

private theorem tuple_sum (d : ℕ) (i : (Fin d → Fin 3)) :
    ∑ j, tuple d i j ^ 4 = representedNumber d := by
  rw [Fin.sum_univ_castSucc]
  simp only [tuple, Fin.snoc_castSucc, Fin.snoc_last, one_pow]
  simp_rw [mul_pow]
  rw [← Finset.sum_mul, ← Finset.mul_sum, natTriple_sum]
  dsimp [representedNumber]
  have h := scale_mul d i
  calc
    2^4 * (10082 * (point d i).w.natAbs^4) * scale d i ^ 4 + 1 =
        10082 * (2*((point d i).w.natAbs * scale d i))^4+1 := by ring
    _ = _ := by rw [h]

private theorem tuple_gcd (d : ℕ) (i : (Fin d → Fin 3)) :
    Finset.univ.gcd (tuple d i) = 1 := by
  apply Nat.dvd_one.mp
  have h := Finset.gcd_dvd (f := tuple d i) (Finset.mem_univ (Fin.last 3))
  simpa only [tuple, Fin.snoc_last] using h

private theorem tuple_abs_ratio (d : ℕ) (i : (Fin d → Fin 3)) (j : Fin 3) :
    ((tuple d i j.castSucc : ℕ) : ℚ) / (2*commonDenominator d) = |rationalTriple (point d i) j| := by
  have hd : ((point d i).w.natAbs : ℚ) ≠ 0 := by
    exact_mod_cast (Int.natAbs_pos.mpr ((point_good d i).w_ne)).ne'
  have hl : (commonDenominator d : ℚ) ≠ 0 := by
    exact_mod_cast (commonDenominator_pos d).ne'
  have hs : ((point d i).w.natAbs : ℚ) * (scale d i : ℚ) = commonDenominator d := by
    exact_mod_cast scale_mul d i
  rw [rationalTriple_eq, abs_div]
  simp only [tuple, Fin.snoc_castSucc, natTriple, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_natAbs, Int.cast_abs]
  rw [show |((point d i).w : ℚ)| = ((point d i).w.natAbs : ℚ) by
    simp only [Nat.cast_natAbs, Int.cast_abs]]
  field_simp
  linear_combination |(integerTriple d i j : ℚ)| * hs

private theorem tuple_injective (d : ℕ) : Function.Injective (tuple d) := by
  intro i j he
  apply point_squared_triple_injective d
  funext k
  have h := congrArg (fun f : Fin 4 → ℕ ↦ ((f k.castSucc : ℕ) : ℚ) /
    (2*commonDenominator d)) he
  change ((tuple d i k.castSucc : ℕ) : ℚ) / (2*commonDenominator d) =
    ((tuple d j k.castSucc : ℕ) : ℚ) / (2*commonDenominator d) at h
  rw [tuple_abs_ratio, tuple_abs_ratio] at h
  have h2 := congrArg (fun x : ℚ ↦ x^2) h
  dsimp only at h2
  simpa only [sq_abs] using h2

private theorem tuple_nonadditive_indices (d : ℕ) (n : (Fin d → Fin 3)) (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    tuple d n k ≠ tuple d n i + tuple d n j := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
  all_goals simp only [tuple, Fin.snoc_castSucc, Fin.snoc_last] at *
  · intro he
    apply natTriple_nonadditive d n i j k
      (fun h ↦ hij (congrArg Fin.castSucc h)) (fun h ↦ hik (congrArg Fin.castSucc h))
      (fun h ↦ hjk (congrArg Fin.castSucc h))
    apply Nat.mul_left_cancel (n := 2*scale d n) (by have := scale_pos d n; positivity)
    nlinarith [he]
  all_goals try simp only [mul_assoc] at *
  all_goals omega

private def boundedTuple (d : ℕ) (n : (Fin d → Fin 3)) : Fin 4 → Fin (representedNumber d+1) :=
  fun i ↦ ⟨tuple d n i, by
    have hs := tuple_sum d n
    have hi : tuple d n i ^ 4 ≤ ∑ j, tuple d n j ^ 4 :=
      Finset.single_le_sum (f := fun j ↦ tuple d n j ^ 4)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hp := Nat.le_pow (a := tuple d n i) (by decide : 0 < 4)
    omega⟩

private theorem boundedTuple_injective (d : ℕ) : Function.Injective (boundedTuple d) := by
  intro i j he
  apply tuple_injective d
  funext k
  exact congrArg (fun f ↦ ((f k : Fin (representedNumber d+1)) : ℕ)) he


/-- Primitive representations outside every additive-triple locus. -/
def primitiveNonadditiveCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun a : Fin 4 → Fin (n+1) ↦
    (∑ i, (a i : ℕ)^4 = n) ∧ Finset.univ.gcd (fun i ↦ (a i : ℕ)) = 1 ∧
      ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → (a k : ℕ) ≠ (a i : ℕ) + (a j : ℕ))).card

theorem primitive_nonadditive_count_lower (d : ℕ) :
    3^d ≤ primitiveNonadditiveCount (representedNumber d) := by
  classical
  unfold primitiveNonadditiveCount
  have hc := Finset.card_le_card_of_injOn (boundedTuple d) (s := Finset.univ)
    (t := Finset.univ.filter (fun a : Fin 4 → Fin (representedNumber d+1) ↦
      (∑ i, (a i : ℕ)^4 = representedNumber d) ∧
        Finset.univ.gcd (fun i ↦ (a i : ℕ)) = 1 ∧
        ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → (a k : ℕ) ≠ (a i : ℕ) + (a j : ℕ)))
    (by
      intro f _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨tuple_sum d f, tuple_gcd d f, tuple_nonadditive_indices d f⟩)
    (boundedTuple_injective d).injOn
  simpa using hc


theorem commonDenominator_bound (d : ℕ) : commonDenominator d ≤ (10^40)^(60^d) := by
  have hi : ∀ f : Fin d → Fin 3, (point d f).w.natAbs ≤ (10^40)^(20^d) := by
    intro f
    have hh := point_w_bound d f
    rw [← Int.cast_abs, ← Nat.cast_natAbs] at hh
    exact_mod_cast hh
  calc
    commonDenominator d ≤ ∏ _f : Fin d → Fin 3, (10^40)^(20^d) :=
      Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) (fun f _ ↦ hi f)
    _ = ((10^40)^(20^d))^(3^d) := by simp
    _ = (10^40)^(60^d) := by rw [← pow_mul, ← mul_pow]; norm_num

theorem representedNumber_bound (d : ℕ) : representedNumber d ≤ (10^40)^(60^(d+1)) := by
  have hL := commonDenominator_pos d
  have hp : 1 ≤ commonDenominator d ^ 4 := Nat.one_le_pow 4 _ hL
  have he : 1+4*60^d ≤ 60^(d+1) := by
    rw [pow_succ]
    have hh : 1 ≤ 60^d := Nat.one_le_pow d 60 (by norm_num)
    omega
  calc
    representedNumber d ≤ (10082*16+1)*commonDenominator d ^ 4 := by
      unfold representedNumber
      nlinarith
    _ ≤ (10^40)*commonDenominator d ^ 4 := by gcongr; norm_num
    _ ≤ (10^40)*((10^40)^(60^d))^4 := by gcongr; exact commonDenominator_bound d
    _ = (10^40)^(1+4*60^d) := by rw [← pow_mul, ← pow_succ']; congr 1; omega
    _ ≤ (10^40)^(60^(d+1)) := Nat.pow_le_pow_right (by norm_num) he

private theorem representedNumber_log_bound (d : ℕ) :
    Real.log (representedNumber d) < (100*(primitiveNonadditiveCount (representedNumber d) : ℝ))^4 := by
  have hn : 0 < representedNumber d := by unfold representedNumber; positivity
  have hnR : (0 : ℝ) < representedNumber d := by exact_mod_cast hn
  have hupper : (representedNumber d : ℝ) ≤ (10^40 : ℝ)^(60^(d+1)) := by
    exact_mod_cast representedNumber_bound d
  have hlog : Real.log (representedNumber d) ≤ (60 : ℝ)^(d+1)*(40*Real.log 10) := by
    have hh := Real.log_le_log hnR hupper
    simpa only [Real.log_pow, Nat.cast_pow, Nat.cast_ofNat] using hh
  have hlog10 : Real.log 10 < 10 := (Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)).trans (by norm_num)
  have hcount : (3 : ℝ)^d ≤ primitiveNonadditiveCount (representedNumber d) := by
    exact_mod_cast primitive_nonadditive_count_lower d
  have hpow : (60 : ℝ)^d ≤ 81^d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
  calc
    Real.log (representedNumber d) ≤ (60 : ℝ)^(d+1)*(40*Real.log 10) := hlog
    _ < (60 : ℝ)^(d+1)*400 := by gcongr; linarith
    _ ≤ (81 : ℝ)^d*24000 := by rw [pow_succ]; nlinarith
    _ < (81 : ℝ)^d*100000000 := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 81) d]
    _ = (100*(3 : ℝ)^d)^4 := by rw [mul_pow, ← pow_mul, mul_comm d 4, pow_mul]; norm_num; ring
    _ ≤ (100*(primitiveNonadditiveCount (representedNumber d) : ℝ))^4 := by gcongr

/-- This improves the primitive nonadditive lower bound from iterated logarithmic
growth to a fixed power of the logarithm. It is not an `n^c` lower bound. -/
theorem primitive_nonadditive_log_growth :
    {n : ℕ | (Real.log (n : ℝ))^(1/4 : ℝ) < 100*(primitiveNonadditiveCount n : ℝ)}.Infinite := by
  have hg : ∀ d : ℕ, (Real.log (representedNumber d : ℝ))^(1/4 : ℝ) <
      100*(primitiveNonadditiveCount (representedNumber d) : ℝ) := by
    intro d
    have hn : (1 : ℝ) ≤ representedNumber d := by
      exact_mod_cast (show 1 ≤ representedNumber d by unfold representedNumber; omega)
    have hh := Real.rpow_lt_rpow (Real.log_nonneg hn) (representedNumber_log_bound d)
      (by norm_num : (0 : ℝ) < 1/4)
    have he : ((100*(primitiveNonadditiveCount (representedNumber d) : ℝ))^4)^(1/4 : ℝ) =
        100*(primitiveNonadditiveCount (representedNumber d) : ℝ) := by
      convert Real.pow_rpow_inv_natCast (by positivity :
        (0 : ℝ) ≤ 100*(primitiveNonadditiveCount (representedNumber d) : ℝ)) (by decide : 4 ≠ 0) using 1
      norm_num
    rwa [he] at hh
  intro hf
  let C := hf.toFinset.sup primitiveNonadditiveCount
  have hm := hg C
  have hn : representedNumber C ∈ hf.toFinset := hf.mem_toFinset.mpr hm
  have hu : primitiveNonadditiveCount (representedNumber C) ≤ C := Finset.le_sup hn
  have hl := primitive_nonadditive_count_lower C
  have hp : C < 3^C := Nat.lt_pow_self (by norm_num : 1 < 3)
  omega

/-- Some permutation of the four coordinates forms a rank-one matrix. -/
def HasProductRelation {n : ℕ} (a : Fin 4 → Fin (n+1)) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4),
    (a (σ 0) : ℕ)*(a (σ 3) : ℕ)=(a (σ 1) : ℕ)*(a (σ 2) : ℕ)

instance {n : ℕ} (a : Fin 4 → Fin (n+1)) : Decidable (HasProductRelation a) :=
  inferInstanceAs (Decidable (∃ σ : Equiv.Perm (Fin 4),
    (a (σ 0) : ℕ)*(a (σ 3) : ℕ)=(a (σ 1) : ℕ)*(a (σ 2) : ℕ)))

private theorem product_inequalities (a b c : ℕ)
    (ha : a=0 ∨ 71 ≤ a) (hb : b=0 ∨ 71 ≤ b)
    (hp : 0 < a+b) (hl : 2*(a^2+b^2) ≤ c^2)
    (hu : c^2 ≤ 12*(a^2+b^2)) :
    c ≠ a*b ∧ b ≠ a*c ∧ a ≠ b*c := by
  have hac : a < c := by
    by_contra hn
    have hca : c^2 ≤ a^2 := Nat.pow_le_pow_left (by omega) 2
    have hsq : 0 < a^2+b^2 := by
      rcases ha with rfl | ha
      · nlinarith [Nat.mul_self_le_mul_self (show 1 ≤ b by omega)]
      · nlinarith [Nat.mul_self_le_mul_self ha]
    nlinarith
  have hbc : b < c := by
    by_contra hn
    have hcb : c^2 ≤ b^2 := Nat.pow_le_pow_left (by omega) 2
    have hsq : 0 < a^2+b^2 := by
      rcases ha with rfl | ha
      · nlinarith [Nat.mul_self_le_mul_self (show 1 ≤ b by omega)]
      · nlinarith [Nat.mul_self_le_mul_self ha]
    nlinarith
  have hc : 0 < c := by omega
  refine ⟨?_,?_,?_⟩
  · intro he
    rcases ha with rfl | ha
    · simp at he; omega
    rcases hb with rfl | hb
    · simp at he; omega
    rcases le_total a b with hab | hba
    · have hs : a^2 ≤ b^2 := Nat.pow_le_pow_left hab 2
      have hlo : 71*b ≤ c := by nlinarith
      have hsq : (71*b)^2 ≤ c^2 := Nat.pow_le_pow_left hlo 2
      nlinarith
    · have hs : b^2 ≤ a^2 := Nat.pow_le_pow_left hba 2
      have hlo : 71*a ≤ c := by nlinarith
      have hsq : (71*a)^2 ≤ c^2 := Nat.pow_le_pow_left hlo 2
      nlinarith
  · intro he
    rcases ha with rfl | ha
    · simp at he; omega
    · nlinarith
  · intro he
    rcases hb with rfl | hb
    · simp at he; omega
    · nlinarith

private theorem no_product_relation (n : ℕ) (v : Fin 4 → Fin (n+1))
    (h3 : (v 3 : ℕ)=1)
    (h0 : (v 0 : ℕ) ≠ (v 1 : ℕ)*(v 2 : ℕ))
    (h1 : (v 1 : ℕ) ≠ (v 0 : ℕ)*(v 2 : ℕ))
    (h2 : (v 2 : ℕ) ≠ (v 0 : ℕ)*(v 1 : ℕ)) :
    ¬HasProductRelation v := by
  change (v ⟨3, by decide⟩ : ℕ)=1 at h3
  rintro ⟨σ,he⟩
  have h01 := σ.injective.ne (by decide : (0 : Fin 4) ≠ 1)
  have h02 := σ.injective.ne (by decide : (0 : Fin 4) ≠ 2)
  have h03 := σ.injective.ne (by decide : (0 : Fin 4) ≠ 3)
  have h12 := σ.injective.ne (by decide : (1 : Fin 4) ≠ 2)
  have h13 := σ.injective.ne (by decide : (1 : Fin 4) ≠ 3)
  have h23 := σ.injective.ne (by decide : (2 : Fin 4) ≠ 3)
  generalize hi : σ 0 = i at *
  generalize hj : σ 1 = j at *
  generalize hk : σ 2 = k at *
  generalize hl : σ 3 = l at *
  clear hi hj hk hl σ
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals fin_cases k <;> try contradiction
  all_goals fin_cases l <;> try contradiction
  all_goals simp only [h3, mul_one, one_mul] at he
  all_goals try first
    | exact h0 he
    | exact h0 he.symm
    | exact h1 he
    | exact h1 he.symm
    | exact h2 he
    | exact h2 he.symm
  all_goals rw [mul_comm] at he
  all_goals first
    | exact h0 he
    | exact h0 he.symm
    | exact h1 he
    | exact h1 he.symm
    | exact h2 he
    | exact h2 he.symm

private theorem tuple_sq (d : ℕ) (i : (Fin d → Fin 3)) (j : Fin 3) :
    (tuple d i j.castSucc : ℤ)^2 = (2*scale d i)^2 * (integerTriple d i j)^2 := by
  simp only [tuple, Fin.snoc_castSucc, natTriple, Nat.cast_mul, Nat.cast_ofNat,
    Int.natCast_natAbs, mul_pow, sq_abs]
  ring

private theorem tuple_pinching (d : ℕ) (i : (Fin d → Fin 3)) :
    0 < tuple d i 0+tuple d i 1 ∧
    2*((tuple d i 0)^2+(tuple d i 1)^2) ≤ (tuple d i 2)^2 ∧
    (tuple d i 2)^2 ≤ 12*((tuple d i 0)^2+(tuple d i 1)^2) := by
  let a := tuple d i 0
  let b := tuple d i 1
  let c := tuple d i 2
  have hq := (point_good d i).quad1
  have ha : (a : ℤ)^2 = (142 * scale d i)^2*((point d i).s+(point d i).t)^2 := by
    rw [show a = tuple d i (0 : Fin 3).castSucc from rfl, tuple_sq]
    simp [integerTriple]
    ring
  have hb : (b : ℤ)^2 = (142 * scale d i)^2*((point d i).s-(point d i).t)^2 := by
    rw [show b = tuple d i (1 : Fin 3).castSucc from rfl, tuple_sq]
    simp [integerTriple]
    ring
  have hc : (c : ℤ)^2 = (284 * scale d i)^2*(point d i).z^2 := by
    rw [show c = tuple d i (2 : Fin 3).castSucc from rfl, tuple_sq]
    simp [integerTriple]
    ring
  have hs : 0 < (scale d i : ℤ) := by exact_mod_cast scale_pos d i
  have hl : 2*((a : ℤ)^2+(b : ℤ)^2) ≤ (c : ℤ)^2 := by
    rw [ha,hb,hc,hq]
    nlinarith [sq_nonneg ((scale d i : ℤ)*(point d i).s)]
  have hu : (c : ℤ)^2 ≤ 12*((a : ℤ)^2+(b : ℤ)^2) := by
    rw [ha,hb,hc,hq]
    nlinarith [sq_nonneg ((scale d i : ℤ)*(point d i).t)]
  have hp : 0 < a+b := by
    by_contra hn
    have ha0 : a=0 := by omega
    have hb0 : b=0 := by omega
    have hs0 : (142*(scale d i : ℤ))^2 ≠ 0 := by positivity
    have hst : (point d i).s+(point d i).t = 0 := by
      have hh : (142*(scale d i : ℤ))^2*((point d i).s+(point d i).t)^2=0 := by
        rw [←ha,ha0]; norm_num
      exact eq_zero_of_pow_eq_zero (mul_eq_zero.mp hh |>.resolve_left hs0)
    have hst' : (point d i).s-(point d i).t = 0 := by
      have hh : (142*(scale d i : ℤ))^2*((point d i).s-(point d i).t)^2=0 := by
        rw [←hb,hb0]; norm_num
      exact eq_zero_of_pow_eq_zero (mul_eq_zero.mp hh |>.resolve_left hs0)
    exact (point_good d i).t_ne (by omega)
  exact ⟨hp,by exact_mod_cast hl,by exact_mod_cast hu⟩

private theorem tuple_multiple (d : ℕ) (i : (Fin d → Fin 3)) (j : Fin 3) :
    71 ∣ tuple d i j.castSucc := by
  simp only [tuple, Fin.snoc_castSucc, natTriple]
  have hd : 71 ∣ (integerTriple d i j).natAbs := by
    fin_cases j
    · simp [integerTriple, Int.natAbs_mul]
    · simp [integerTriple, Int.natAbs_mul]
    · change 71 ∣ (142*(point d i).z).natAbs
      rw [Int.natAbs_mul]
      exact dvd_mul_of_dvd_left (by norm_num : 71 ∣ (142 : ℤ).natAbs) _
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd 2) _

private theorem boundedTuple_nonmultiplicative (d : ℕ) (i : (Fin d → Fin 3)) :
    ¬HasProductRelation (boundedTuple d i) := by
  have ha : tuple d i 0=0 ∨ 71 ≤ tuple d i 0 := by
    by_cases h : tuple d i 0=0
    · exact Or.inl h
    · exact Or.inr (Nat.le_of_dvd (Nat.pos_of_ne_zero h) (tuple_multiple d i 0))
  have hb : tuple d i 1=0 ∨ 71 ≤ tuple d i 1 := by
    by_cases h : tuple d i 1=0
    · exact Or.inl h
    · exact Or.inr (Nat.le_of_dvd (Nat.pos_of_ne_zero h) (tuple_multiple d i 1))
  obtain ⟨hp,hl,hu⟩ := tuple_pinching d i
  obtain ⟨h2,h1,h0⟩ := product_inequalities _ _ _ ha hb hp hl hu
  exact no_product_relation _ _ (by change tuple d i (Fin.last 3) = 1; simp only [tuple, Fin.snoc_last]) h0 h1 h2


def HasPythagoreanRelation {n : ℕ} (a : Fin 4 → Fin (n+1)) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4), ((a (σ 0) : ℕ)+(a (σ 1) : ℕ))^2 =
    (a (σ 2) : ℕ)^2+(a (σ 3) : ℕ)^2

instance {n : ℕ} (a : Fin 4 → Fin (n+1)) : Decidable (HasPythagoreanRelation a) :=
  inferInstanceAs (Decidable (∃ σ : Equiv.Perm (Fin 4), ((a (σ 0) : ℕ)+(a (σ 1) : ℕ))^2 =
    (a (σ 2) : ℕ)^2+(a (σ 3) : ℕ)^2))

private theorem pyth_parity : ∀ a b c d : ZMod 2, (a+b)^2=c^2+d^2 →
    a^4+b^4+c^4+d^4 = 0 := by decide

private theorem boundedTuple_nonpythagorean (d : ℕ) (f : Fin d → Fin 3) :
    ¬HasPythagoreanRelation (boundedTuple d f) := by
  rintro ⟨σ,he⟩
  have hh := congrArg (fun x : ℕ ↦ (x : ZMod 2)) he
  simp only [Nat.cast_add, Nat.cast_pow] at hh
  have hz := pyth_parity _ _ _ _ hh
  have hs : ∑ i, tuple d f (σ i)^4 = representedNumber d :=
    (Equiv.sum_comp σ (fun i ↦ tuple d f i ^ 4)).trans (tuple_sum d f)
  have hm := congrArg (fun x : ℕ ↦ (x : ZMod 2)) hs
  simp only [Fin.sum_univ_four, Nat.cast_add, Nat.cast_pow] at hm
  change ((tuple d f (σ 0) : ZMod 2)^4+(tuple d f (σ 1) : ZMod 2)^4+
    (tuple d f (σ 2) : ZMod 2)^4+(tuple d f (σ 3) : ZMod 2)^4) = 0 at hz
  rw [hz] at hm
  have hn : (representedNumber d : ZMod 2) = 1 := by
    simp only [representedNumber, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat]
    rw [show (2 : ZMod 2) = 0 by decide]
    simp
  rw [hn] at hm
  exact (by decide : (0 : ZMod 2) ≠ 1) hm

/-- Primitive representations avoiding additive, multiplicative, and Pythagorean
relations in every coordinate ordering. -/
def coreCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun a : Fin 4 → Fin (n+1) ↦
    (∑ i, (a i : ℕ)^4 = n) ∧ Finset.univ.gcd (fun i ↦ (a i : ℕ)) = 1 ∧
      (∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → (a k : ℕ) ≠ (a i : ℕ) + (a j : ℕ)) ∧
      ¬HasProductRelation a ∧ ¬HasPythagoreanRelation a)).card

theorem core_count_lower (d : ℕ) : 3^d ≤ coreCount (representedNumber d) := by
  classical
  unfold coreCount
  have hc := Finset.card_le_card_of_injOn (boundedTuple d) (s := Finset.univ)
    (t := Finset.univ.filter (fun a : Fin 4 → Fin (representedNumber d+1) ↦
      (∑ i, (a i : ℕ)^4 = representedNumber d) ∧
        Finset.univ.gcd (fun i ↦ (a i : ℕ)) = 1 ∧
        (∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → (a k : ℕ) ≠ (a i : ℕ) + (a j : ℕ)) ∧
        ¬HasProductRelation a ∧ ¬HasPythagoreanRelation a))
    (by
      intro f _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨tuple_sum d f, tuple_gcd d f, tuple_nonadditive_indices d f,
        boundedTuple_nonmultiplicative d f, boundedTuple_nonpythagorean d f⟩)
    (boundedTuple_injective d).injOn
  simpa using hc

private theorem representedNumber_core_log_bound (d : ℕ) :
    Real.log (representedNumber d) < (100*(coreCount (representedNumber d) : ℝ))^4 := by
  have hn : 0 < representedNumber d := by unfold representedNumber; positivity
  have hnR : (0 : ℝ) < representedNumber d := by exact_mod_cast hn
  have hupper : (representedNumber d : ℝ) ≤ (10^40 : ℝ)^(60^(d+1)) := by
    exact_mod_cast representedNumber_bound d
  have hlog : Real.log (representedNumber d) ≤ (60 : ℝ)^(d+1)*(40*Real.log 10) := by
    have hh := Real.log_le_log hnR hupper
    simpa only [Real.log_pow, Nat.cast_pow, Nat.cast_ofNat] using hh
  have hlog10 : Real.log 10 < 10 := (Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)).trans (by norm_num)
  have hcount : (3 : ℝ)^d ≤ coreCount (representedNumber d) := by
    exact_mod_cast core_count_lower d
  have hpow : (60 : ℝ)^d ≤ 81^d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
  calc
    Real.log (representedNumber d) ≤ (60 : ℝ)^(d+1)*(40*Real.log 10) := hlog
    _ < (60 : ℝ)^(d+1)*400 := by gcongr; linarith
    _ ≤ (81 : ℝ)^d*24000 := by rw [pow_succ]; nlinarith
    _ < (81 : ℝ)^d*100000000 := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 81) d]
    _ = (100*(3 : ℝ)^d)^4 := by rw [mul_pow, ← pow_mul, mul_comm d 4, pow_mul]; norm_num; ring
    _ ≤ (100*(coreCount (representedNumber d) : ℝ))^4 := by gcongr

/-- This improves the primitive core lower bound from iterated logarithmic
growth to a fixed power of the logarithm. It is not an `n^c` lower bound. -/
theorem core_log_growth :
    {n : ℕ | (Real.log (n : ℝ))^(1/4 : ℝ) < 100*(coreCount n : ℝ)}.Infinite := by
  have hg : ∀ d : ℕ, (Real.log (representedNumber d : ℝ))^(1/4 : ℝ) <
      100*(coreCount (representedNumber d) : ℝ) := by
    intro d
    have hn : (1 : ℝ) ≤ representedNumber d := by
      exact_mod_cast (show 1 ≤ representedNumber d by unfold representedNumber; omega)
    have hh := Real.rpow_lt_rpow (Real.log_nonneg hn) (representedNumber_core_log_bound d)
      (by norm_num : (0 : ℝ) < 1/4)
    have he : ((100*(coreCount (representedNumber d) : ℝ))^4)^(1/4 : ℝ) =
        100*(coreCount (representedNumber d) : ℝ) := by
      convert Real.pow_rpow_inv_natCast (by positivity :
        (0 : ℝ) ≤ 100*(coreCount (representedNumber d) : ℝ)) (by decide : 4 ≠ 0) using 1
      norm_num
    rwa [he] at hh
  intro hf
  let C := hf.toFinset.sup coreCount
  have hm := hg C
  have hn : representedNumber C ∈ hf.toFinset := hf.mem_toFinset.mpr hm
  have hu : coreCount (representedNumber C) ≤ C := Finset.le_sup hn
  have hl := core_count_lower C
  have hp : C < 3^C := Nat.lt_pow_self (by norm_num : 1 < 3)
  omega


private theorem point_w_min (d : ℕ) (f : Fin d → Fin 3) : 2 ≤ (point d f).w.natAbs := by
  have hq := (point_good d f).quad2
  have ht : 0 < (point d f).t^2 := sq_pos_of_ne_zero (point_good d f).t_ne
  have hs := sq_nonneg (point d f).s
  have hw : (((point d f).w.natAbs : ℤ))^2 = (point d f).w^2 := by
    rw [Int.natCast_natAbs, sq_abs]
  have h : (2 : ℤ) ≤ (point d f).w.natAbs := by
    have hn : (0 : ℤ) ≤ (point d f).w.natAbs := by positivity
    nlinarith
  exact_mod_cast h

/-- Even the crude product-denominator lower bound is exponential in the
number of points certified at depth `d`. -/
theorem commonDenominator_lower (d : ℕ) : 2^(3^d) ≤ commonDenominator d := by
  calc
    2^(3^d) = ∏ _f : Fin d → Fin 3, (2 : ℕ) := by simp
    _ ≤ commonDenominator d := Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
      (fun f _ ↦ point_w_min d f)

theorem representedNumber_lower (d : ℕ) : 2^(3^d) ≤ representedNumber d := by
  apply (commonDenominator_lower d).trans
  have hp : commonDenominator d ≤ commonDenominator d ^ 4 := Nat.le_pow (by decide)
  unfold representedNumber
  nlinarith

/-- This bounds ONLY the `3^d` representations certified by the construction.
It is not an upper bound on `coreCount` or on the full quartic count. -/
theorem certified_contribution_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ d : ℕ, (3 : ℝ)^d ≤ C*(representedNumber d : ℝ)^ε := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(ε*Real.log 2)⁻¹, inv_pos.mpr (mul_pos hε hlog2), fun d ↦ ?_⟩
  have hn : (0 : ℝ) < representedNumber d := by
    exact_mod_cast (show 0 < representedNumber d by unfold representedNumber; positivity)
  have hl : (2 : ℝ)^(3^d) ≤ representedNumber d := by
    exact_mod_cast representedNumber_lower d
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) (3^d)) hl
  rw [Real.log_pow] at hlog
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hlog
  have hexp := Real.add_one_le_exp (Real.log (representedNumber d : ℝ)*ε)
  rw [← Real.rpow_def_of_pos hn] at hexp
  have hmul : (3 : ℝ)^d*(ε*Real.log 2) ≤ (representedNumber d : ℝ)^ε := by
    have hh := mul_le_mul_of_nonneg_right hlog hε.le
    nlinarith
  apply (le_div_iff₀ (mul_pos hε hlog2)).mpr hmul |>.trans_eq
  simp only [div_eq_mul_inv, mul_comm]

end Erdos322Research.QuarticBranching
