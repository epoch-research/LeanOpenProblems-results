import Submission.OrthogonalGlobal
import Submission.ProductCrossZeroSum

/-! Elementary descent for the quartic in the crossed zero-sum reduction.
This file concerns a restricted construction, not arbitrary point sets. -/
namespace Erdos213.CrossQuarticDescent
open OrthogonalGlobal
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

/-- Homogeneous quartic, with subtraction avoided over the naturals. -/
def Quartic (a b c : ℕ) : Prop := c^2+4*a^2*b^2=a^4+20*b^4

lemma Quartic.cast {a b c : ℕ} (h : Quartic a b c) {R : Type*} [CommSemiring R] :
    (c : R)^2+4*(a : R)^2*(b : R)^2=(a : R)^4+20*(b : R)^4 := by
  have hh := congrArg (fun n : ℕ => (n : R)) h
  push_cast at hh
  exact hh

private lemma twenty_not_square : ∀ c : ZMod 32, c^2 ≠ 20 := by decide +kernel

private lemma even_numerator_value : ∀ a b : ZMod 32,
    a.val%2=0 → b.val%2=1 → a^4+20*b^4-4*a^2*b^2=20 := by decide +kernel

private lemma quartic_mod32 {a b c : ZMod 32}
    (h : c^2+4*a^2*b^2=a^4+20*b^4) (ha : a.val%2=0) : b.val%2=0 := by
  by_contra hb
  have hb' : b.val%2=1 := by omega
  have he := even_numerator_value a b ha hb'
  exact twenty_not_square c (by linear_combination h+he)

lemma primitive_odd {a b c : ℕ} (hcp : a.Coprime b) (h : Quartic a b c) :
    a%2=1 ∧ c%2=1 := by
  have hm := quartic_mod32 (a := (a : ZMod 32)) (b := (b : ZMod 32))
    (c := (c : ZMod 32)) (Quartic.cast h)
  simp only [ZMod.val_natCast, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 32)] at hm
  have ha : a%2=1 := by
    by_contra hn
    have ha0 : a%2=0 := by omega
    have hb0 := hm ha0
    have hd := hcp.gcd_eq_one ▸ Nat.dvd_gcd
      (Nat.dvd_of_mod_eq_zero ha0) (Nat.dvd_of_mod_eq_zero hb0)
    norm_num at hd
  refine ⟨ha,?_⟩
  by_contra hn
  have hc0 : c%2=0 := by omega
  have hh := congrArg (fun z : ℕ => z%2) h
  norm_num [Nat.add_mod,Nat.mul_mod,Nat.pow_mod,ha,hc0] at hh

lemma quartic_coprime {a b c : ℕ} (hcp : a.Coprime b) (h : Quartic a b c) :
    c.Coprime b := by
  by_contra hn
  obtain ⟨p,hp,hpc,hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  letI : Fact p.Prime := ⟨hp⟩
  have hc0 : (c : ZMod p)=0 := (ZMod.natCast_eq_zero_iff c p).mpr hpc
  have hb0 : (b : ZMod p)=0 := (ZMod.natCast_eq_zero_iff b p).mpr hpb
  have he : (c : ZMod p)^2+4*(a : ZMod p)^2*(b : ZMod p)^2=
      (a : ZMod p)^4+20*(b : ZMod p)^4 := Quartic.cast h
  simp only [hc0,hb0,zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0),
    mul_zero,add_zero] at he
  have ha0 : (a : ZMod p)=0 := eq_zero_of_pow_eq_zero he.symm
  have hpa := (ZMod.natCast_eq_zero_iff a p).mp ha0
  exact hp.not_dvd_one (hcp.gcd_eq_one ▸ Nat.dvd_gcd hpa hpb)

lemma coprime_four_fourth_factors {a b c : ℕ} (hab : a.Coprime b)
    (h : a*b=4*c^4) :
    ∃ m n : ℕ, c=m*n ∧ m.Coprime n ∧
      ((a=m^4 ∧ b=4*n^4) ∨ (a=4*n^4 ∧ b=m^4)) := by
  have he : a*b=(2*c^2)^2 := by linear_combination h
  obtain ⟨r,s,ha,hb,hrs,hcop⟩ := coprime_square_factors hab he
  have he' : r*s=2*c^2 := hrs.symm
  obtain ⟨m,n,hc,hmn,hfac⟩ := coprime_prime_square_factors Nat.prime_two hcop he'
  rcases hfac with ⟨hr,hs⟩ | ⟨hr,hs⟩
  · refine ⟨m,n,hc,hmn,Or.inl ⟨?_,?_⟩⟩
    · rw [ha,hr]; ring
    · rw [hb,hs]; ring
  · refine ⟨n,m,by simpa [mul_comm] using hc,hmn.symm,Or.inr ⟨?_,?_⟩⟩
    · rw [ha,hr]; ring
    · rw [hb,hs]; ring

lemma coprime_twenty_fourth_sum {a b c : ℕ} (hab : a.Coprime b)
    (h : a*b=20*c^4) :
    ∃ m n : ℕ, c=m*n ∧ m.Coprime n ∧
      (a+b=20*m^4+n^4 ∨ a+b=4*m^4+5*n^4) := by
  have he : a*b=5*(2*c^2)^2 := by linear_combination h
  obtain ⟨r,s,hrs,hcop,hfac⟩ := coprime_prime_square_factors (by norm_num : Nat.Prime 5) hab he
  have he' : r*s=2*c^2 := hrs.symm
  obtain ⟨m,n,hc,hmn,hfac'⟩ := coprime_prime_square_factors Nat.prime_two hcop he'
  rcases hfac with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
    rcases hfac' with ⟨hr,hs⟩ | ⟨hr,hs⟩
  · refine ⟨n,m,by simpa [mul_comm] using hc,hmn.symm,Or.inl ?_⟩
    rw [ha,hb,hr,hs]; ring
  · refine ⟨m,n,hc,hmn,Or.inr ?_⟩
    rw [ha,hb,hr,hs]; ring
  · refine ⟨n,m,by simpa [mul_comm] using hc,hmn.symm,Or.inr ?_⟩
    rw [ha,hb,hr,hs]; ring
  · refine ⟨m,n,hc,hmn,Or.inl ?_⟩
    rw [ha,hb,hr,hs]; ring

lemma coprime_power_two {a k : ℕ} (ha : a%2=1) : a.Coprime (2^k) := by
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  intro hd
  have hh := Nat.mod_eq_zero_of_dvd hd
  omega

lemma difference_factors {a b c : ℕ} (hb : 0 < b) (hcp : a.Coprime b)
    (h : Quartic a b c) :
    ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ A.Coprime B ∧ A+B=c ∧ A*B=4*b^4 := by
  obtain ⟨ha,hc⟩ := primitive_odd hcp h
  let d : ℕ := ((a : ℤ)^2-2*(b : ℤ)^2).natAbs
  have hd : (d : ℤ)^2=((a : ℤ)^2-2*(b : ℤ)^2)^2 := Int.natAbs_sq _
  have he : c^2=d^2+16*b^4 := by
    have h' : (c : ℤ)^2+4*(a : ℤ)^2*(b : ℤ)^2=(a : ℤ)^4+20*(b : ℤ)^4 := Quartic.cast h
    have h'' : (c : ℤ)^2=(d : ℤ)^2+16*(b : ℤ)^4 := by linear_combination h'-hd
    exact_mod_cast h''
  have hdodd : d%2=1 := by
    have hh := congrArg (fun z : ℕ => z%2) he
    dsimp only at hh
    rw [square_mod_two,Nat.add_mod,square_mod_two,Nat.mul_mod] at hh
    norm_num at hh
    omega
  have hcb := quartic_coprime hcp h
  have hco : c.Coprime (16*b^4) := by
    apply Nat.Coprime.mul_right
    · exact (by simpa using (coprime_power_two (k := 4) hc))
    · exact hcb.pow_right 4
  have hcd : c.Coprime d := by
    apply Nat.coprime_iff_gcd_eq_one.mpr
    have hcdiv := Nat.gcd_dvd_left c d
    have hddiv := Nat.gcd_dvd_right c d
    have hsdiv := Nat.dvd_sub (dvd_pow hcdiv (by decide : 2 ≠ 0))
      (dvd_pow hddiv (by decide : 2 ≠ 0))
    have hdif : c^2-d^2=16*b^4 := by omega
    rw [hdif] at hsdiv
    exact Nat.dvd_one.mp (hco.gcd_eq_one ▸ Nat.dvd_gcd hcdiv hsdiv)
  obtain ⟨A,B,hA,hB,hAB,hs,hp⟩ := half_difference_factors hc hdodd
    (by decide : 0 < 4) (sq_pos_of_pos hb) hcd
    (show c^2=d^2+4*4*(b^2)^2 by linear_combination he)
  exact ⟨A,B,hA,hB,hAB,hs,by linear_combination hp⟩

private lemma reject_reverse_mod16 : ∀ a m n : ZMod 16, m.val%2=1 →
    a^2+m^4=2*m^2*n^2+4*n^4 → False := by decide +kernel

private lemma first_parity_mod16 : ∀ a m n : ZMod 16, m.val%2=1 →
    a^2+4*n^4=m^4+2*m^2*n^2 → n.val%2=0 := by decide +kernel

lemma first_stage {a b c : ℕ} (hb : 0 < b) (hcp : a.Coprime b)
    (h : Quartic a b c) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ m.Coprime n ∧ m%2=1 ∧ n%2=0 ∧
      b=m*n ∧ a^2+4*n^4=m^4+2*m^2*n^2 := by
  obtain ⟨ha,hc⟩ := primitive_odd hcp h
  obtain ⟨A,B,hA,hB,hAB,hs,hp⟩ := difference_factors hb hcp h
  obtain ⟨m,n,hbmn,hmn,hfac⟩ := coprime_four_fourth_factors hAB hp
  have hcs : c=m^4+4*n^4 := by
    rcases hfac with ⟨heA,heB⟩ | ⟨heA,heB⟩ <;> omega
  have hm : 0 < m := by nlinarith [hbmn]
  have hn : 0 < n := by nlinarith [hbmn]
  have hmo : m%2=1 := by
    by_contra hmo
    have hm0 : m%2=0 := by omega
    have hh := congrArg (fun z : ℕ => z%2) hcs
    norm_num [Nat.add_mod,Nat.mul_mod,Nat.pow_mod,hm0,hc] at hh
  have hq : a^2+4*n^4=m^4+2*m^2*n^2 := by
    have heq : ((a : ℤ)^2-2*(m : ℤ)^2*(n : ℤ)^2)^2 =
        ((m : ℤ)^4-4*(n : ℤ)^4)^2 := by
      have hh : (c : ℤ)^2+4*(a : ℤ)^2*(b : ℤ)^2=(a : ℤ)^4+20*(b : ℤ)^4 := Quartic.cast h
      have hc' : (c : ℤ)=(m : ℤ)^4+4*(n : ℤ)^4 := by exact_mod_cast hcs
      have hb' : (b : ℤ)=(m : ℤ)*(n : ℤ) := by exact_mod_cast hbmn
      rw [hc',hb'] at hh
      linear_combination -hh
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp heq with heq | heq
    · have hh : (a : ℤ)^2+4*(n : ℤ)^4=(m : ℤ)^4+2*(m : ℤ)^2*(n : ℤ)^2 := by linarith
      exact_mod_cast hh
    · have hz : (a : ZMod 16)^2+(m : ZMod 16)^4 =
          2*(m : ZMod 16)^2*(n : ZMod 16)^2+4*(n : ZMod 16)^4 := by
        have hh : (a : ℤ)^2+(m : ℤ)^4=2*(m : ℤ)^2*(n : ℤ)^2+4*(n : ℤ)^4 := by linarith
        exact_mod_cast congrArg (fun z : ℤ => (z : ZMod 16)) hh
      have hm16 : (m : ZMod 16).val%2=1 := by
        simpa only [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 16)] using hmo
      exact (reject_reverse_mod16 _ _ _ hm16 hz).elim
  have hne : n%2=0 := by
    have hz : (a : ZMod 16)^2+4*(n : ZMod 16)^4=
        (m : ZMod 16)^4+2*(m : ZMod 16)^2*(n : ZMod 16)^2 := by
      exact_mod_cast congrArg (fun z : ℕ => (z : ZMod 16)) hq
    have hm16 : (m : ZMod 16).val%2=1 := by
      simpa only [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 16)] using hmo
    simpa only [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 16)] using
      first_parity_mod16 _ _ _ hm16 hz
  exact ⟨m,n,hm,hn,hmn,hmo,hne,hbmn,hq⟩

lemma second_coprime {a m n : ℕ} (hmn : m.Coprime n)
    (h : a^2+5*n^4=(m^2+n^2)^2) : a.Coprime (m^2+n^2) := by
  by_contra hn
  obtain ⟨p,hp,hpa,hpt⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  have hd : p ∣ 5*n^4 := by
    have hh := Nat.dvd_sub (dvd_pow hpt (by decide : 2 ≠ 0))
      (dvd_pow hpa (by decide : 2 ≠ 0))
    have he : (m^2+n^2)^2-a^2=5*n^4 := by omega
    simpa only [he] using hh
  have hpn : p ∣ n := by
    rcases hp.dvd_mul.mp hd with h5 | hn'
    · have hp5 : p=5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5
      subst p
      obtain ⟨a',ha'⟩ := hpa
      obtain ⟨t',ht'⟩ := hpt
      have he : n^4+5*a'^2=5*t'^2 := by rw [ha',ht'] at h; nlinarith [h]
      have hdiv : 5 ∣ n^4 := by
        have he' : 5*t'^2-5*a'^2=n^4 := by omega
        rw [← he']
        exact Nat.dvd_sub (dvd_mul_right 5 _) (dvd_mul_right 5 _)
      exact (show Nat.Prime 5 by norm_num).dvd_of_dvd_pow hdiv
    · exact hp.dvd_of_dvd_pow hn'
  have hpm : p ∣ m := by
    apply hp.dvd_of_dvd_pow (n := 2)
    have hh := Nat.dvd_sub hpt (dvd_pow hpn (by decide : 2 ≠ 0))
    simpa only [Nat.add_sub_cancel_right] using hh
  exact hp.not_dvd_one (hmn.gcd_eq_one ▸ Nat.dvd_gcd hpm hpn)

private lemma reject_second_mod16 : ∀ m r s : ZMod 16, m.val%2=1 →
    m^2+4*r^2*s^2=4*r^4+5*s^4 → False := by decide +kernel

lemma descent_step {a b c : ℕ} (hb : 0 < b) (hcp : a.Coprime b)
    (h : Quartic a b c) :
    ∃ a' b' c' : ℕ, 0 < b' ∧ b' < b ∧ a'.Coprime b' ∧ Quartic a' b' c' := by
  have hao := (primitive_odd hcp h).1
  obtain ⟨m,n,hm,hn,hmn,hmo,hne,hbmn,hfirst⟩ := first_stage hb hcp h
  obtain ⟨N,hnN⟩ : 2 ∣ n := Nat.dvd_of_mod_eq_zero hne
  have hN : 0 < N := by omega
  have hmo' : (m^2+n^2)%2=1 := by
    rw [Nat.add_mod,square_mod_two,square_mod_two,hmo,hne]
  have hq : a^2+5*n^4=(m^2+n^2)^2 := by linear_combination hfirst
  have hcop := second_coprime hmn hq
  have hq' : (m^2+n^2)^2=a^2+4*20*(N^2)^2 := by
    rw [hnN] at hq ⊢
    linear_combination -hq
  obtain ⟨A,B,hA,hB,hAB,hs,hp⟩ := half_difference_factors hmo' hao
    (by decide : 0 < 20) (sq_pos_of_pos hN) hcop.symm hq'
  have hp' : A*B=20*N^4 := by linear_combination hp
  obtain ⟨r,s,hNrs,hrs,hcases⟩ := coprime_twenty_fourth_sum hAB hp'
  have hr : 0 < r := by nlinarith [hNrs]
  have hsr : 0 < s := by nlinarith [hNrs]
  have hnr : n=2*r*s := by rw [hnN,hNrs]; ring
  have hrn : r < n := by nlinarith [hnr]
  have hnb : n ≤ b := by nlinarith [hbmn]
  rcases hcases with he | he
  · have hnew : Quartic s r m := by
      dsimp [Quartic]
      rw [hnr] at hs
      linear_combination he-hs
    exact ⟨s,r,m,hr,hrn.trans_le hnb,hrs.symm,hnew⟩
  · have he' : m^2+4*r^2*s^2=4*r^4+5*s^4 := by
      rw [hnr] at hs
      linear_combination he-hs
    have hz : (m : ZMod 16)^2+4*(r : ZMod 16)^2*(s : ZMod 16)^2=
        4*(r : ZMod 16)^4+5*(s : ZMod 16)^4 := by
      exact_mod_cast congrArg (fun z : ℕ => (z : ZMod 16)) he'
    have hm16 : (m : ZMod 16).val%2=1 := by
      simpa only [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 16)] using hmo
    exact (reject_second_mod16 _ _ _ hm16 hz).elim

/-- The positive denominator strictly decreases in the preceding factorization. -/
theorem no_primitive_quartic (b : ℕ) : ∀ a c : ℕ,
    0 < b → a.Coprime b → Quartic a b c → False := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro a c hb hcp hq
    obtain ⟨a',b',c',hb',hlt,hcp',hq'⟩ := descent_step hb hcp hq
    exact ih b' hlt a' c' hb' hcp' hq'

lemma numerator_mul_denominator (t : ℚ) : (t.num : ℚ)=t*(t.den : ℚ) := by
  have hd : (t.den : ℚ) ≠ 0 := by exact_mod_cast t.den_ne_zero
  calc
    (t.num : ℚ)=((t.num : ℚ)/(t.den : ℚ))*(t.den : ℚ) := by field_simp
    _=t*(t.den : ℚ) := by rw [Rat.num_div_den]

lemma clear_quartic_denominator {t w : ℚ} (h : w^2=t^4-4*t^2+20) :
    ∃ c : ℕ, Quartic t.num.natAbs t.den c := by
  let z : ℤ := t.num^4-4*t.num^2*(t.den : ℤ)^2+20*(t.den : ℤ)^4
  have hz : IsSquare (z : ℚ) := by
    refine ⟨w*(t.den : ℚ)^2,?_⟩
    dsimp [z]
    push_cast
    rw [numerator_mul_denominator t]
    linear_combination -(t.den : ℚ)^4*h
  obtain ⟨c,hc⟩ := Rat.isSquare_intCast_iff.mp hz
  have hn2 : (t.num.natAbs : ℤ)^2=t.num^2 := Int.natAbs_sq t.num
  have hn4 : (t.num.natAbs : ℤ)^4=t.num^4 := by
    calc
      (t.num.natAbs : ℤ)^4=((t.num.natAbs : ℤ)^2)^2 := by ring
      _=(t.num^2)^2 := by rw [hn2]
      _=t.num^4 := by ring
  have hq : (c.natAbs : ℤ)^2+4*(t.num.natAbs : ℤ)^2*(t.den : ℤ)^2=
      (t.num.natAbs : ℤ)^4+20*(t.den : ℤ)^4 := by
    rw [Int.natAbs_sq c,hn2,hn4]
    dsimp [z] at hc
    linear_combination -hc
  exact ⟨c.natAbs,by dsimp [Quartic]; exact_mod_cast hq⟩

/-- Complete rational nonsquare theorem, by elementary infinite descent. -/
theorem rational_quartic_impossible {t w : ℚ} (h : w^2=t^4-4*t^2+20) : False := by
  obtain ⟨c,hc⟩ := clear_quartic_denominator h
  exact no_primitive_quartic t.den t.num.natAbs c t.den_pos t.reduced hc

/-- The duplication formula written solely as a rational polynomial identity. -/
lemma duplication_to_quartic {x y : ℚ} (hy : y ≠ 0)
    (h : y^2=x^3-4*x^2+20*x) :
    ((x^4-8*x^3+120*x^2-160*x+400)/(4*y^2))^2 =
      ((x^2-20)/(2*y))^4-4*((x^2-20)/(2*y))^2+20 := by
  field_simp
  linear_combination
    256*(x^4-20*x^3+40*x^2-400*x-20*y^2+400)*h

/-- All rational affine points on the rank-zero quotient have x=y=0.
No external rank computation or finite-generation assertion is used. -/
theorem elliptic_points {x y : ℚ} (h : y^2=x^3-4*x^2+20*x) : x=0 ∧ y=0 := by
  have hy : y=0 := by
    by_contra hn
    exact rational_quartic_impossible (duplication_to_quartic hn h)
  have hp : 0 < x^2-4*x+20 := by nlinarith [sq_nonneg (x-2)]
  have he : x*(x^2-4*x+20)=0 := by rw [hy] at h; nlinarith [h]
  exact ⟨(mul_eq_zero.mp he).resolve_right (ne_of_gt hp),hy⟩

/-- Complete classification of the rational radius quotient. -/
theorem quotient_classification {U P : ℚ}
    (h : (3*U+1)*P^2=(U-1)*(U^2+1)) : U=1 ∧ P=0 := by
  have hd : 3*U+1 ≠ 0 := by
    intro hd
    have hu : U= -1/3 := by linarith
    rw [hu] at h
    norm_num at h
  have he := ProductCrossZeroSum.quotient_to_elliptic hd h
  have hx := (elliptic_points he).1
  dsimp [ProductCrossZeroSum.ellipticX] at hx
  have hz : 10*(U-1)=0 := (div_eq_zero_iff.mp hx).resolve_right hd
  have hu : U=1 := by linarith
  refine ⟨hu,?_⟩
  rw [hu] at h
  nlinarith [sq_nonneg P]

lemma radius_zero {D x y : ℚ} (hD : 0 < D)
    (h : ProductNormMatching.radius D x y=0) : x=0 ∧ y=0 := by
  dsimp [ProductNormMatching.radius] at h
  have he := (add_eq_zero_iff_of_nonneg (sq_nonneg x)
    (mul_nonneg hD.le (sq_nonneg y))).mp h
  exact ⟨eq_zero_of_pow_eq_zero he.1,
    eq_zero_of_pow_eq_zero ((mul_eq_zero.mp he.2).resolve_left (ne_of_gt hD))⟩

/-- Even without a nonreal hypothesis, every matching input here is degenerate:
one of b and c is zero. This still concerns only the zero-sum source. -/
theorem zero_sum_matching_degenerate {D x y q : ℚ} (hD : 0 < D)
    (hr : IsSquare (ProductNormMatching.radius D x y))
    (hs : IsSquare (ProductNormMatching.radius D (-1-x) (-y)))
    (h : ProductCrossZeroSum.Crossed D x y q) : y=0 ∧ (x=0 ∨ x= -1) := by
  obtain ⟨R,hR⟩ := hr
  obtain ⟨S,hS⟩ := hs
  rw [← pow_two] at hR hS
  have he : ProductCrossZeroSum.v D x y=(R*S)^2 := by
    dsimp [ProductCrossZeroSum.v]
    rw [hR,hS]
    ring
  have hh := ProductCrossZeroSum.radius_relation h
  rw [he] at hh
  have hp := (quotient_classification hh).2
  have hv : ProductNormMatching.radius D x y *
      ProductNormMatching.radius D (-1-x) (-y)=0 := by
    change ProductCrossZeroSum.v D x y=0
    rw [he,hp]
    norm_num
  rcases mul_eq_zero.mp hv with hb | hc
  · obtain ⟨hx,hy⟩ := radius_zero hD hb
    exact ⟨hy,Or.inl hx⟩
  · obtain ⟨hx,hy⟩ := radius_zero hD hc
    exact ⟨by linarith,Or.inr (by linarith)⟩

/-- This excludes the crossed matching only in the zero-sum source. -/
theorem no_crossed_zero_sum {D x y q : ℚ} (hD : 0 < D) (hy : y ≠ 0)
    (hr : IsSquare (ProductNormMatching.radius D x y))
    (hs : IsSquare (ProductNormMatching.radius D (-1-x) (-y)))
    (h : ProductCrossZeroSum.Crossed D x y q) : False := by
  obtain ⟨X,Y,hX,he⟩ := ProductCrossZeroSum.crossed_produces_nonzero_elliptic_point
    hD hy hr hs h
  exact hX (elliptic_points he).1

#print axioms descent_step
#print axioms no_primitive_quartic
#print axioms rational_quartic_impossible
#print axioms duplication_to_quartic
#print axioms elliptic_points
#print axioms quotient_classification
#print axioms zero_sum_matching_degenerate
#print axioms no_crossed_zero_sum
end Erdos213.CrossQuarticDescent
