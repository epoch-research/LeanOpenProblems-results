import Submission.FullRosati

/-!
# Exact positive norm and inverse-lift sheets

The two full Rosati forms correspond to explicit positive factor sheets with
an exact gcd-square divisibility test. The inverse-sheet lift bounds retain
all permitted positive lifts. No uniform occurrence theorem is asserted.
-/

set_option maxHeartbeats 4000000

namespace Erdos242Aux

/-- Exact norm algebra for full I, including every composite and nonsquarefree d. -/
theorem rosatiI_norm (p a b c d : ℤ)
    (h : 4*a*b*c*d=p*(a+b)+c) :
    (4*a*c*d-p)*(4*b*c*d-p)=p^2+4*c^2*d := by
  linear_combination 4*c*d*h

/-- Exact norm algebra for full II. -/
theorem rosatiII_norm (p a b c d : ℤ)
    (h : 4*a*b*c*d=p*c+a+b) :
    (4*a*c*d-1)*(4*b*c*d-1)=1+p*(4*c^2*d) := by
  linear_combination 4*c*d*h

/-- Divisibility formulation of the common full-pattern square test. -/
theorem square_test_extract {H M : ℕ} (hH : 0 < H) (hM : 0 < M)
    (hHM : H ∣ M) (h4 : 4*M ∣ H^2) :
    ∃ c d : ℕ, 0 < c ∧ 0 < d ∧ H=4*c*d ∧ M=4*c^2*d := by
  obtain ⟨c,hmc⟩ := hHM
  have hc : 0 < c := by
    by_contra h
    have hz : c=0 := by omega
    rw [hz,mul_zero] at hmc
    omega
  obtain ⟨d,hq⟩ := h4
  have hd : 0 < d := by
    by_contra h
    have hz : d=0 := by omega
    rw [hz,mul_zero] at hq
    have hsq : 0 < H^2 := pow_pos hH 2
    omega
  have hform : H=4*c*d := by
    apply Nat.eq_of_mul_eq_mul_left hH
    simpa [hmc,pow_two,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hq
  refine ⟨c,d,hc,hd,hform,?_⟩
  rw [hmc,hform]; ring

/-- Prime saturation and its exact gcd form hold for EVERY one-sided lift. -/
theorem extended_shifted_gcd (p r S M : ℕ) (hp : p.Prime)
    (hr : r+1<p) (hprod : r*S=1+p*M) :
    Nat.gcd (r+1) (S+1) ∣ M ∧
      Nat.gcd (r+1) (S+1)=Nat.gcd (r+1) M := by
  let H := Nat.gcd (r+1) (S+1)
  have hH : 0 < H := Nat.gcd_pos_of_pos_left _ (by omega)
  have hHr : H ∣ r+1 := Nat.gcd_dvd_left _ _
  have hHS : H ∣ S+1 := Nat.gcd_dvd_right _ _
  have hHp : H.Coprime p :=
    (Nat.coprime_of_lt_prime (by omega) (lt_of_le_of_lt (Nat.le_of_dvd (by omega) hHr) hr) hp).symm
  have hid : (r+1)*(S+1)=p*M+((r+1)+(S+1)) := by nlinarith only [hprod]
  have hd : H ∣ p*M+((r+1)+(S+1)) := by
    rw [←hid]; exact dvd_mul_of_dvd_left hHr _
  have hHM : H ∣ M := hHp.dvd_of_dvd_mul_left
    ((Nat.dvd_add_iff_left (dvd_add hHr hHS)).mpr hd)
  refine ⟨hHM,Nat.dvd_antisymm (Nat.dvd_gcd hHr hHM) ?_⟩
  have hNr : Nat.gcd (r+1) M ∣ r+1 := Nat.gcd_dvd_left _ _
  have hNM : Nat.gcd (r+1) M ∣ M := Nat.gcd_dvd_right _ _
  have hprod' : (r+1)*S=p*M+(S+1) := by nlinarith only [hprod]
  have hNS : Nat.gcd (r+1) M ∣ S+1 := by
    have hdiv : Nat.gcd (r+1) M ∣ p*M+(S+1) := by
      rw [←hprod']; exact dvd_mul_of_dvd_left hNr _
    exact (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right hNM p)).mpr hdiv
  exact Nat.dvd_gcd hNr hNS

/-- Exact actual-winding gcd formula, valid without a bound on k. -/
theorem inverse_lift_gcd (p r s m k : ℕ) (hp : p.Prime)
    (hr : r+1<p) (hprod : r*s=1+p*m) :
    r*(s+k*p)=1+p*(m+k*r) ∧
      Nat.gcd (r+1) (s+k*p+1)=Nat.gcd (r+1) (m+k*r) := by
  have hp' : r*(s+k*p)=1+p*(m+k*r) := by nlinarith only [hprod]
  exact ⟨hp',(extended_shifted_gcd p r (s+k*p) (m+k*r) hp hr hp').2⟩

/-- On the finite relevant prefix the winding formula is gcd(r+1,m-k). -/
theorem inverse_lift_prefix_gcd (p r s m k : ℕ) (hp : p.Prime)
    (hr : r+1<p) (hprod : r*s=1+p*m) (hk : k ≤ m) :
    Nat.gcd (r+1) (s+k*p+1)=Nat.gcd (r+1) (m-k) := by
  rw [(inverse_lift_gcd p r s m k hp hr hprod).2]
  have heq : m+k*r=(m-k)+k*(r+1) := by nlinarith only [Nat.sub_add_cancel hk]
  rw [heq,Nat.gcd_add_mul_right_right]

/-- Full Type I positive norm-factor sheets. -/
def NormI (p : ℕ) : Prop :=
  ∃ r S M : ℕ, 0<r ∧ r<S ∧ r<p ∧ 0<M ∧ r*S=p^2+M ∧
    4*M ∣ (Nat.gcd (r+p) (S+p))^2

/-- Full Type II positive inverse-factor sheets with one anchor interior. -/
def LiftII (p : ℕ) : Prop :=
  ∃ r S M : ℕ, 0<r ∧ r<S ∧ r+1<p ∧ 0<M ∧ r*S=1+p*M ∧
    4*M ∣ (Nat.gcd (r+1) (S+1))^2

/-- The entire Type I norm sheet, not a prime-kernel subfamily, maps to FullI. -/
theorem normI_fullI {p : ℕ} (hp : p.Prime) (h : NormI p) : FullI p := by
  obtain ⟨r,S,M,hr,hrS,hrp,hM,hprod,h4⟩ := h
  let H := Nat.gcd (r+p) (S+p)
  have hH : 0<H := Nat.gcd_pos_of_pos_left _ (by omega)
  have hHr : H ∣ r+p := Nat.gcd_dvd_left _ _
  have hHS : H ∣ S+p := Nat.gcd_dvd_right _ _
  have hid : (r+p)*(S+p)=M+p*((r+p)+(S+p)) := by nlinarith only [hprod]
  have hHM : H ∣ M := by
    have hdiv : H ∣ M+p*((r+p)+(S+p)) := by rw [←hid]; exact dvd_mul_of_dvd_left hHr _
    exact (Nat.dvd_add_iff_left (dvd_mul_of_dvd_right (dvd_add hHr hHS) p)).mpr hdiv
  obtain ⟨c,d,hc,hd,hHform,hMform⟩ := square_test_extract hH hM hHM h4
  let a := (r+p)/H
  let b := (S+p)/H
  have hra : r+p=H*a := (Nat.mul_div_cancel' hHr).symm
  have hSb : S+p=H*b := (Nat.mul_div_cancel' hHS).symm
  have ha : 0<a := positive_quotient_of_dvd (r+p) H (by omega) hH hHr
  have hab : a<b := by
    have : H*a<H*b := by rw [←hra,←hSb]; omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hcop : a.Coprime b := Nat.coprime_div_gcd_div_gcd hH
  have hmc : M=H*c := by rw [hHform,hMform]; ring
  have hrel : H*a*b=p*(a+b)+c := by
    apply Nat.eq_of_mul_eq_mul_left hH
    calc
      H*(H*a*b)=(H*a)*(H*b) := by ring
      _ = (r+p)*(S+p) := by rw [←hra,←hSb]
      _ = M+p*((r+p)+(S+p)) := hid
      _ = H*(p*(a+b)+c) := by rw [hra,hSb,hmc]; ring
  have hHp : p.Coprime H := by
    apply (Nat.coprime_add_self_right.mpr (Nat.coprime_of_lt_prime (by omega) hrp hp)).of_dvd_right hHr
  have hcp : c.Coprime p := by
    apply hHp.symm.of_dvd_left
    refine ⟨4*d,?_⟩; rw [hHform]; ring
  have hcdiv : c ∣ a+b := by
    apply hcp.dvd_of_dvd_mul_left
    have hcl : c ∣ H*a*b := by refine ⟨4*d*a*b,?_⟩; rw [hHform]; ring
    rw [hrel] at hcl
    exact (Nat.dvd_add_iff_left (dvd_refl c)).mpr hcl
  obtain ⟨e,hce⟩ := hcdiv
  have he : 0<e := by
    by_contra h
    have hz : e=0 := by omega
    rw [hz,mul_zero] at hce
    omega
  have hpe : p*e+1=4*a*b*d := by
    apply Nat.eq_of_mul_eq_mul_left hc
    rw [hHform,hce] at hrel
    nlinarith only [hrel]
  exact ⟨a,b,c,d,e,ha,hab,hc,hd,he,hcop,hce.symm,hpe⟩

/-- The one-sided lifted inverse square test maps to the FULL Type II. -/
theorem liftII_fullII {p : ℕ} (hp : p.Prime) (h : LiftII p) : FullII p := by
  obtain ⟨r,S,M,hr,hrS,hrp,hM,hprod,h4⟩ := h
  let H := Nat.gcd (r+1) (S+1)
  have hH : 0<H := Nat.gcd_pos_of_pos_left _ (by omega)
  have hHr : H ∣ r+1 := Nat.gcd_dvd_left _ _
  have hHS : H ∣ S+1 := Nat.gcd_dvd_right _ _
  have hHM : H ∣ M := (extended_shifted_gcd p r S M hp hrp hprod).1
  obtain ⟨c,d,hc,hd,hHform,hMform⟩ := square_test_extract hH hM hHM h4
  let a := (r+1)/H
  let b := (S+1)/H
  have hra : r+1=H*a := (Nat.mul_div_cancel' hHr).symm
  have hSb : S+1=H*b := (Nat.mul_div_cancel' hHS).symm
  have ha : 0<a := positive_quotient_of_dvd (r+1) H (by omega) hH hHr
  have hab : a<b := by
    have : H*a<H*b := by rw [←hra,←hSb]; omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hcop : a.Coprime b := Nat.coprime_div_gcd_div_gcd hH
  have hmc : M=H*c := by rw [hHform,hMform]; ring
  have hid : (r+1)*(S+1)=p*M+((r+1)+(S+1)) := by nlinarith only [hprod]
  have hrel : H*a*b=p*c+a+b := by
    apply Nat.eq_of_mul_eq_mul_left hH
    calc
      H*(H*a*b)=(H*a)*(H*b) := by ring
      _ = (r+1)*(S+1) := by rw [←hra,←hSb]
      _ = p*M+((r+1)+(S+1)) := hid
      _ = H*(p*c+a+b) := by rw [hra,hSb,hmc]; ring
  have hcdiv : c ∣ a+b := by
    have hcl : c ∣ H*a*b := by refine ⟨4*d*a*b,?_⟩; rw [hHform]; ring
    have heq : H*a*b=p*c+(a+b) := by nlinarith only [hrel]
    rw [heq] at hcl
    exact (Nat.dvd_add_iff_right (dvd_mul_left c p)).mpr hcl
  obtain ⟨e,hce⟩ := hcdiv
  have he : 0<e := by
    by_contra h
    have hz : e=0 := by omega
    rw [hz,mul_zero] at hce
    omega
  have hpe : p+e=4*a*b*d := by
    apply Nat.eq_of_mul_eq_mul_left hc
    rw [hHform] at hrel
    nlinarith only [hrel,hce]
  exact ⟨a,b,c,d,e,ha,hab,hc,hd,he,hcop,hce.symm,hpe⟩

/-- The strict first-denominator bounds follow from the full I equations. -/
theorem fullI_parameter_bounds (p a b c d e : ℕ)
    (ha : 0<a) (hab : a<b) (_hc : 0<c) (hd : 0<d) (_he : 0<e)
    (hce : c*e=a+b) (hpe : p*e+1=4*a*b*d) :
    p<4*(a*c*d) ∧ 2*(a*c*d)<p := by
  have hm : 4*(a*c*d)*e=p*e+(4*a^2*d+1) := by
    have h := congrArg (fun n : ℕ => 4*a*d*n) hce
    nlinarith only [h,hpe]
  have hlo : p<4*(a*c*d) := by
    have hmul : p*e<(4*(a*c*d))*e := by nlinarith only [hm]
    exact Nat.lt_of_mul_lt_mul_right hmul
  have had : 1 ≤ a*d := by have hpos : 0<a*d := Nat.mul_pos ha hd; omega
  have hdiff : a*d*a+1 ≤ a*d*b := by
    have h := Nat.mul_le_mul_left (a*d) (by omega : a+1 ≤ b)
    nlinarith only [h,had]
  have h2 : 2*(a*c*d)*e+2*a*d*b=p*e+1+2*a*d*a := by
    have h := congrArg (fun n : ℕ => 2*a*d*n) hce
    nlinarith only [h,hpe]
  have hhi : 2*(a*c*d)<p := by
    have hmul : (2*(a*c*d))*e<p*e := by nlinarith only [h2,hdiff]
    exact Nat.lt_of_mul_lt_mul_right hmul
  exact ⟨hlo,hhi⟩

/-- Full II bounds needed to choose its ALWAYS-interior first factor. -/
theorem fullII_parameter_bounds (p a b c d e : ℕ)
    (ha : 0<a) (hab : a<b) (hc : 0<c) (hd : 0<d) (_he : 0<e)
    (hce : c*e=a+b) (hpe : p+e=4*a*b*d) : 2*(a*b*d)<p := by
  have hsum : a+b ≤ a*b+1 := by nlinarith
  have hge : 2 ≤ a*b := by nlinarith
  have hxge : a*b ≤ a*b*d := Nat.le_mul_of_pos_right _ hd
  have hege : e ≤ c*e := Nat.le_mul_of_pos_left _ hc
  nlinarith only [hsum,hge,hxge,hege,hce,hpe]

/-- All full I patterns occur in the p²+4c²d norm-factor sheet. -/
theorem fullI_normI {p : ℕ} (h : FullI p) : NormI p := by
  obtain ⟨a,b,c,d,e,ha,hab,hc,hd,he,hcop,hce,hpe⟩ := h
  obtain ⟨hlo,hhi⟩ := fullI_parameter_bounds p a b c d e ha hab hc hd he hce hpe
  let r := 4*a*c*d-p
  let S := 4*b*c*d-p
  let M := 4*c^2*d
  have hmul : 4*a*c*d<4*b*c*d := by
    have hpos : 0<4*c*d := by positivity
    have h := Nat.mul_lt_mul_of_pos_left hab hpos
    simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
  have hrp : r+p=4*a*c*d := by
    have hple : p ≤ 4*a*c*d := by nlinarith only [hlo]
    exact Nat.sub_add_cancel hple
  have hSp : S+p=4*b*c*d := by
    have hpS : p ≤ 4*b*c*d := by nlinarith only [hlo,hmul]
    exact Nat.sub_add_cancel hpS
  have hr : 0<r := by nlinarith only [hrp,hlo]
  have hrS : r<S := by nlinarith only [hrp,hSp,hmul]
  have hrlt : r<p := by nlinarith only [hrp,hhi]
  have hM : 0<M := by dsimp [M]; positivity
  have hRosati : 4*a*b*c*d=p*(a+b)+c := by
    have h1 := congrArg (fun n : ℕ => c*n) hpe
    have h2 := congrArg (fun n : ℕ => p*n) hce
    nlinarith only [h1,h2]
  have hprod : r*S=p^2+M := by
    have hz : 4*(a:ℤ)*b*c*d=(p:ℤ)*((a:ℤ)+b)+c := by exact_mod_cast hRosati
    have hnorm := rosatiI_norm (p:ℤ) a b c d hz
    have hrz : (r:ℤ)=4*(a:ℤ)*c*d-p := by
      have hh : (r:ℤ)+p=4*(a:ℤ)*c*d := by exact_mod_cast hrp
      linarith
    have hSz : (S:ℤ)=4*(b:ℤ)*c*d-p := by
      have hh : (S:ℤ)+p=4*(b:ℤ)*c*d := by exact_mod_cast hSp
      linarith
    rw [←hrz,←hSz] at hnorm
    dsimp [M]
    exact_mod_cast hnorm
  have hG : Nat.gcd (r+p) (S+p)=4*c*d := by
    rw [hrp,hSp]
    have haeq : 4*a*c*d=(4*c*d)*a := by ring
    have hbeq : 4*b*c*d=(4*c*d)*b := by ring
    rw [haeq,hbeq,Nat.gcd_mul_left,hcop.gcd_eq_one,mul_one]
  refine ⟨r,S,M,hr,hrS,hrlt,hM,hprod,?_⟩
  rw [hG]
  refine ⟨d,?_⟩
  dsimp [M]; ring

/-- Every full II admits a one-sided lift; no c<a condition is imposed. -/
theorem fullII_liftII {p : ℕ} (hp4 : p%4=1) (h : FullII p) : LiftII p := by
  obtain ⟨a,b,c,d,e,ha,hab,hc,hd,he,hcop,hce,hpe⟩ := h
  have hb : 0<b := lt_trans ha hab
  have hhi := fullII_parameter_bounds p a b c d e ha hab hc hd he hce hpe
  have hage : a ≤ a*b*d := by
    have hbge : 1 ≤ b*d := by have hh : 0<b*d := Nat.mul_pos hb hd; omega
    have hh := Nat.mul_le_mul_left a hbge
    simpa [Nat.mul_assoc] using hh
  have hap : a<p := by nlinarith only [hage,hhi]
  have he3 : 3 ≤ e := by
    have hdiv : 4 ∣ 4*a*b*d := ⟨a*b*d,by ring⟩
    have hm : (p+e)%4=0 := by rw [hpe]; exact Nat.mod_eq_zero_of_dvd hdiv
    omega
  have hcb : c<b := by
    have hh := Nat.mul_le_mul_left c he3
    nlinarith only [hh,hce,hab]
  let r := 4*a*c*d-1
  let S := 4*b*c*d-1
  let M := 4*c^2*d
  have hapos : 0<4*a*c*d := by positivity
  have hbpos : 0<4*b*c*d := by positivity
  have hr1 : r+1=4*a*c*d := Nat.sub_add_cancel hapos
  have hS1 : S+1=4*b*c*d := Nat.sub_add_cancel hbpos
  have hr : 0<r := by
    have hge : 1 ≤ a*c*d := by
      have hh : 0<a*c*d := by positivity
      omega
    nlinarith only [hr1,hge]
  have hrS : r<S := by
    have hpos : 0<4*c*d := by positivity
    have hh := Nat.mul_lt_mul_of_pos_left hab hpos
    nlinarith only [hh,hr1,hS1]
  have hrb : r*b=p*c+a := by
    have hh := congrArg (fun n : ℕ => c*n) hpe
    nlinarith only [hh,hce,congrArg (fun n : ℕ => b*n) hr1]
  have hrlt : r<p := by
    have hh := Nat.mul_le_mul_left p (by omega : c+1 ≤ b)
    have hmul : r*b<p*b := by nlinarith only [hh,hrb,hap]
    exact Nat.lt_of_mul_lt_mul_right hmul
  have hrp : r+1<p := by
    have hm : (r+1)%4=0 := by rw [hr1]; simp [Nat.mul_mod]
    omega
  have hM : 0<M := by dsimp [M]; positivity
  have hRosati : 4*a*b*c*d=p*c+a+b := by
    have hh := congrArg (fun n : ℕ => c*n) hpe
    nlinarith only [hh,hce]
  have hprod : r*S=1+p*M := by
    have hz : 4*(a:ℤ)*b*c*d=(p:ℤ)*c+a+b := by exact_mod_cast hRosati
    have hnorm := rosatiII_norm (p:ℤ) a b c d hz
    have hrz : (r:ℤ)=4*(a:ℤ)*c*d-1 := by
      have hh : (r:ℤ)+1=4*(a:ℤ)*c*d := by exact_mod_cast hr1
      linarith
    have hSz : (S:ℤ)=4*(b:ℤ)*c*d-1 := by
      have hh : (S:ℤ)+1=4*(b:ℤ)*c*d := by exact_mod_cast hS1
      linarith
    rw [←hrz,←hSz] at hnorm
    dsimp [M]
    exact_mod_cast hnorm
  have hG : Nat.gcd (r+1) (S+1)=4*c*d := by
    rw [hr1,hS1]
    have haeq : 4*a*c*d=(4*c*d)*a := by ring
    have hbeq : 4*b*c*d=(4*c*d)*b := by ring
    rw [haeq,hbeq,Nat.gcd_mul_left,hcop.gcd_eq_one,mul_one]
  refine ⟨r,S,M,hr,hrS,hrp,hM,hprod,?_⟩
  rw [hG]
  refine ⟨d,?_⟩
  dsimp [M]; ring

/-- Exact full-pattern bridge to the arithmetic certificate. -/
theorem primeCertificate_iff_full_patterns {p : ℕ} (hp : p.Prime) (hp4 : p%4=1) :
    PrimeCertificate p ↔ NormI p ∨ LiftII p := by
  rw [primeCertificate_iff_full_rosati hp hp4]
  exact ⟨fun h => h.elim (fun hi => Or.inl (fullI_normI hi))
      (fun hii => Or.inr (fullII_liftII hp4 hii)),
    fun h => h.elim (fun hi => Or.inl (normI_fullI hp hi))
      (fun hii => Or.inr (liftII_fullII hp hii))⟩

/-- Every favorable lift lies in a proved FINITE prefix; not an assumed height cutoff. -/
theorem favorable_lift_bounds (r m k : ℕ) (hr : 3 ≤ r) (hm : 0 < m)
    (h4 : 4*(m+k*r) ∣ (Nat.gcd (r+1) (m+k*r))^2) :
    k ≤ m ∧ 4*k ≤ r+1 := by
  let M := m+k*r
  let H := Nat.gcd (r+1) M
  have hM : 0<M := by dsimp [M]; omega
  have hH : 0<H := Nat.gcd_pos_of_pos_left _ (by omega)
  have hHN : H ∣ r+1 := Nat.gcd_dvd_left _ _
  have hHM : H ∣ M := Nat.gcd_dvd_right _ _
  have hHle : H ≤ r+1 := Nat.le_of_dvd (by omega) hHN
  obtain ⟨c,d,hc,hd,hHform,hMform⟩ := square_test_extract hH hM hHM h4
  have hmc : M=H*c := by rw [hHform,hMform]; ring
  have h4c : 4*c ≤ H := by
    have hh := Nat.mul_le_mul_left (4*c) (by omega : 1 ≤ d)
    nlinarith only [hh,hHform]
  have hcr : c<r := by omega
  have hkc : k ≤ c := by
    by_contra hnot
    have hge : c+1 ≤ k := by omega
    have hmul := Nat.mul_le_mul_right r hge
    have hmul2 := Nat.mul_le_mul_right c hHle
    dsimp [M] at hmc
    nlinarith only [hmc,hm,hcr,hmul,hmul2]
  have hkm : k ≤ m := by
    by_contra hnot
    have hmk : m<k := by omega
    have hdiff : H ∣ k-m := by
      have heq : M+(k-m)=k*(r+1) := by dsimp [M]; nlinarith only [Nat.sub_add_cancel hmk.le]
      have hdiv : H ∣ M+(k-m) := by rw [heq]; exact dvd_mul_of_dvd_right hHN k
      exact (Nat.dvd_add_iff_right hHM).mpr hdiv
    have hdiffle : H ≤ k-m := Nat.le_of_dvd (by omega) hdiff
    have hh := Nat.mul_le_mul_right c hdiffle
    have hh2 := Nat.mul_le_mul_right k (by omega : c ≤ r)
    have hh3 := Nat.mul_le_mul_right c (Nat.sub_le k m)
    dsimp [M] at hmc
    nlinarith only [hmc,hm,hh,hh2,hh3,Nat.sub_add_cancel hmk.le]
  exact ⟨hkm,by omega⟩


end Erdos242Aux
