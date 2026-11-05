import Submission.PrimeCriterion

/-!
# Full Rosati normal forms

Every positive divisor of a square is normalized without any squarefree or
prime-kernel restriction. For primes congruent to one modulo four, the exact
certificate is equivalent to the union of the two full Rosati forms.
These equivalences do not assert uniform existence of either form.
-/

set_option maxHeartbeats 4000000

namespace Erdos242Aux

/-- Canonical normalization of ANY positive divisor of a square.
The kernel d is not assumed prime or squarefree. -/
theorem divisor_square_normalization {x t : ℕ} (hx : 0 < x) (ht : 0 < t)
    (hdiv : t ∣ x ^ 2) :
    ∃ a c d : ℕ, 0 < a ∧ 0 < c ∧ 0 < d ∧ Nat.Coprime a c ∧
      x = a * c * d ∧ t = a ^ 2 * d := by
  let g := Nat.gcd t x
  let a := t / g
  let c := x / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ ht
  have hgt : g ∣ t := Nat.gcd_dvd_left _ _
  have hgx : g ∣ x := Nat.gcd_dvd_right _ _
  have hta : t = g * a := (Nat.mul_div_cancel' hgt).symm
  have hxc : x = g * c := (Nat.mul_div_cancel' hgx).symm
  have ha : 0 < a := positive_quotient_of_dvd t g ht hg hgt
  have hc : 0 < c := positive_quotient_of_dvd x g hx hg hgx
  have hac : a.Coprime c := Nat.coprime_div_gcd_div_gcd hg
  have hagc : a ∣ g * c ^ 2 := by
    apply Nat.dvd_of_mul_dvd_mul_left hg
    simpa only [hta, hxc, mul_pow, pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hdiv
  have hag : a ∣ g := (hac.pow_right 2).dvd_of_dvd_mul_right hagc
  obtain ⟨d, hgd⟩ := hag
  have hd : 0 < d := by
    by_contra h
    have hz : d = 0 := by omega
    rw [hz, mul_zero] at hgd
    omega
  refine ⟨a, c, d, ha, hc, hd, hac, ?_, ?_⟩
  · rw [hxc, hgd]; ring
  · rw [hta, hgd]; ring

/-- Ordered, primitive full Type I, with all kernel valuations retained. -/
def FullI (p : ℕ) : Prop :=
  ∃ a b c d e : ℕ, 0 < a ∧ a < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧
    Nat.Coprime a b ∧ c * e = a + b ∧ p * e + 1 = 4 * a * b * d

/-- Ordered, primitive full Type II. -/
def FullII (p : ℕ) : Prop :=
  ∃ a b c d e : ℕ, 0 < a ∧ a < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧
    Nat.Coprime a b ∧ c * e = a + b ∧ p + e = 4 * a * b * d

/-- Every full Type I supplies precisely the primal divisor a²d. -/
theorem fullI_certificate {p : ℕ} (h : FullI p) : PrimeCertificate p := by
  obtain ⟨a,b,c,d,e,ha,hab,hc,hd,he,_,hce,hpe⟩ := h
  let x := a*c*d
  let t := a^2*d
  have hx : 0 < x := by dsimp [x]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hprod : 4*x*e = p*e + (4*t+1) := by
    dsimp [x,t]
    calc
      4*(a*c*d)*e = 4*a*d*(c*e) := by ring
      _ = 4*a*d*(a+b) := by rw [hce]
      _ = p*e + (4*(a^2*d)+1) := by nlinarith only [hpe]
  have hlo : p < 4*x := by
    have : p*e < (4*x)*e := by nlinarith [hprod]
    exact Nat.lt_of_mul_lt_mul_right this
  have hsum : (4*x-p)+p=4*x := Nat.sub_add_cancel hlo.le
  have hgap : (4*x-p)*e = 4*t+1 := by nlinarith only [hprod,hsum]
  have had : 1 ≤ a*d := by have hpos : 0 < a*d := Nat.mul_pos ha hd; omega
  have habmul : a*d*(a+1) ≤ a*d*b := Nat.mul_le_mul_left _ (by omega)
  have h2eq : 2*x*e + 2*a*d*b = p*e+1+2*a*d*a := by
    dsimp [x]
    have hm : 2*a*d*(c*e) = 2*a*d*(a+b) := by rw [hce]
    nlinarith only [hm,hpe]
  have hdiff : a*d*a+1 ≤ a*d*b := by nlinarith only [habmul,had]
  have hhi : 2*x < p := by
    have hmul : (2*x)*e < p*e := by nlinarith only [h2eq,hdiff]
    exact Nat.lt_of_mul_lt_mul_right hmul
  refine ⟨x,t,hx,ht,hlo,hhi,?_,Or.inl ?_⟩
  · refine ⟨c^2*d,?_⟩; dsimp [x,t]; ring
  · exact ⟨e,hgap.symm⟩

/-- Every full Type II supplies its ordered primal divisor a²d. -/
theorem fullII_certificate {p : ℕ} (h : FullII p) : PrimeCertificate p := by
  obtain ⟨a,b,c,d,e,ha,hab,hc,hd,he,_,hce,hpe⟩ := h
  have hb : 0 < b := lt_trans ha hab
  let x := a*b*d
  let t := a^2*d
  have hx : 0 < x := by dsimp [x]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hlo : p < 4*x := by dsimp [x]; nlinarith only [hpe,he]
  have hsum : a+b ≤ a*b+1 := by nlinarith
  have hge : 2 ≤ a*b := by nlinarith
  have hxge : a*b ≤ x := by dsimp [x]; exact Nat.le_mul_of_pos_right _ hd
  have hege : e ≤ c*e := Nat.le_mul_of_pos_left _ hc
  have hhi : 2*x < p := by dsimp [x] at *; nlinarith [hpe,hce]
  have htx : t < x := by
    have := Nat.mul_lt_mul_of_pos_left hab (Nat.mul_pos ha hd)
    dsimp [x,t]; nlinarith only [this]
  have hgap : 4*x-p=e := by
    have hpe' : p+e=4*x := by dsimp [x]; nlinarith only [hpe]
    omega
  refine ⟨x,t,hx,ht,hlo,hhi,?_,Or.inr ⟨htx,?_⟩⟩
  · refine ⟨b^2*d,?_⟩; dsimp [x,t]; ring
  · rw [hgap]
    refine ⟨a*d*c,?_⟩
    dsimp [x,t]
    calc
      a*b*d+a^2*d = a*d*(a+b) := by ring
      _ = e*(a*d*c) := by rw [←hce]; ring

/-- Full necessity: no prime-kernel hypothesis occurs anywhere. -/
theorem certificate_full_rosati {p : ℕ} (hp : p.Prime) (hp4 : p%4=1)
    (h : PrimeCertificate p) : FullI p ∨ FullII p := by
  obtain ⟨x,t,hx,ht,hlo,hhi,hdiv,hbranch⟩ := h
  obtain ⟨a,c,d,ha,hc,hd,hac,hxform,htform⟩ := divisor_square_normalization hx ht hdiv
  let r := 4*x-p
  obtain ⟨hr3,hrp,_,_,hrx,_⟩ := certificate_modulus_facts p x hp hp4 hlo hhi
  change 3 ≤ r at hr3
  change r < p at hrp
  change r.Coprime x at hrx
  have hr : 0 < r := by omega
  have hrsum : r+p=4*x := by dsimp [r]; omega
  rcases hbranch with hI | ⟨htx,hII⟩
  · change r ∣ 4*t+1 at hI
    obtain ⟨e,heq⟩ := hI
    have he : 0 < e := by
      by_contra h
      have hz : e=0 := by omega
      rw [hz,mul_zero] at heq
      omega
    have hrel : c*(4*t+1)=r*a+(p*a+c) := by
      calc
        c*(4*t+1) = a*(4*x)+c := by rw [htform,hxform]; ring
        _ = a*(r+p)+c := by rw [hrsum]
        _ = r*a+(p*a+c) := by ring
    have hrdiv : r ∣ p*a+c := by
      have hmul : r ∣ c*(4*t+1) := dvd_mul_of_dvd_right ⟨e,heq⟩ c
      rw [hrel] at hmul
      exact (Nat.dvd_add_iff_right (dvd_mul_right r a)).mpr hmul
    obtain ⟨b,hbeq⟩ := hrdiv
    have hab : a < b := by
      have hpra : r*a < p*a+c := by nlinarith [hrp,ha]
      rw [hbeq] at hpra
      exact Nat.lt_of_mul_lt_mul_left hpra
    have hcop : a.Coprime b := by
      have hpa : a.Coprime (p*a+c) := by
        have h := (Nat.coprime_add_mul_right_left c a p).mpr hac.symm
        simpa only [Nat.add_comm] using h.symm
      apply hpa.of_dvd_right
      exact ⟨r,by rw [hbeq]; ring⟩
    have hce : c*e=a+b := by
      apply Nat.eq_of_mul_eq_mul_left hr
      calc
        r*(c*e)=c*(r*e) := by ring
        _ = c*(4*t+1) := by rw [←heq]
        _ = r*a+(p*a+c) := hrel
        _ = r*(a+b) := by rw [hbeq]; ring
    have hpe : p*e+1=4*a*b*d := by
      apply Nat.eq_of_mul_eq_mul_left hr
      calc
        r*(p*e+1)=p*(r*e)+r := by ring
        _ = p*(4*t+1)+r := by rw [←heq]
        _ = 4*p*a^2*d+(p+r) := by rw [htform]; ring
        _ = 4*p*a^2*d+4*x := by rw [Nat.add_comm p r,hrsum]
        _ = 4*a*d*(p*a+c) := by rw [hxform]; ring
        _ = r*(4*a*b*d) := by rw [hbeq]; ring
    exact Or.inl ⟨a,b,c,d,e,ha,hab,hc,hd,he,hcop,hce,hpe⟩
  · change r ∣ x+t at hII
    have hrd : r.Coprime (a*d) := by
      apply hrx.of_dvd_right
      refine ⟨c,?_⟩
      rw [hxform]; ring
    have hrac : r ∣ a+c := by
      apply hrd.dvd_of_dvd_mul_left
      convert hII using 1
      rw [hxform,htform]; ring
    obtain ⟨b,hcb⟩ := hrac
    have hb : 0 < b := by
      by_contra h
      have hz : b=0 := by omega
      rw [hz,mul_zero] at hcb
      omega
    have haclt : a < c := by
      have hmul : (a*d)*a < (a*d)*c := by simpa [hxform,htform,pow_two,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using htx
      exact Nat.lt_of_mul_lt_mul_left hmul
    have hpe : p+r=4*a*c*d := by simpa [hxform,Nat.add_comm,Nat.mul_assoc] using hrsum
    exact Or.inr ⟨a,c,b,d,r,ha,haclt,hb,hd,hr,hac,by nlinarith only [hcb],hpe⟩

theorem primeCertificate_iff_full_rosati {p : ℕ} (hp : p.Prime) (hp4 : p%4=1) :
    PrimeCertificate p ↔ FullI p ∨ FullII p := by
  exact ⟨certificate_full_rosati hp hp4,fun h => h.elim fullI_certificate fullII_certificate⟩


end Erdos242Aux
