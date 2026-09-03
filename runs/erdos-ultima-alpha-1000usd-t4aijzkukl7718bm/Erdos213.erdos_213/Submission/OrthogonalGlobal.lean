import Mathlib.Tactic
import Mathlib.NumberTheory.FLT.Four

/-! A complete global descent for the orthogonal-grid specialization. This file
concerns only the simultaneous square conditions u²+1 and u²+4, not arbitrary
point sets. -/
namespace Erdos213.OrthogonalGlobal
set_option maxHeartbeats 2000000

lemma coprime_square_factors {a b c : ℕ} (hab : a.Coprime b)
    (h : a*b=c^2) : ∃ r s : ℕ, a=r^2 ∧ b=s^2 ∧ c=r*s ∧ r.Coprime s := by
  have hu : IsUnit (gcd a b) := by
    change IsUnit (Nat.gcd a b)
    rw [hab.gcd_eq_one]
    exact isUnit_one
  obtain ⟨r, hr⟩ := exists_eq_pow_of_mul_eq_pow hu h
  have hu' : IsUnit (gcd b a) := by
    change IsUnit (Nat.gcd b a)
    rw [hab.symm.gcd_eq_one]
    exact isUnit_one
  obtain ⟨s, hs⟩ := exists_eq_pow_of_mul_eq_pow hu' (by simpa [mul_comm] using h)
  refine ⟨r,s,hr,hs,?_,?_⟩
  · apply Nat.pow_left_injective (by decide : 2 ≠ 0)
    change c^2=(r*s)^2
    rw [← h,hr,hs]
    ring
  · apply Nat.Coprime.of_dvd_left (dvd_pow_self r (by decide : 2 ≠ 0))
    apply Nat.Coprime.of_dvd_right (dvd_pow_self s (by decide : 2 ≠ 0))
    simpa [hr,hs] using hab

lemma coprime_prime_square_factors {a b c p : ℕ} (hp : p.Prime)
    (hab : a.Coprime b) (h : a*b=p*c^2) :
    ∃ r s : ℕ, c=r*s ∧ r.Coprime s ∧
      ((a=r^2 ∧ b=p*s^2) ∨ (a=p*r^2 ∧ b=s^2)) := by
  have hd : p ∣ a*b := by rw [h]; exact dvd_mul_right _ _
  rcases hp.dvd_mul.mp hd with ha | hb
  · obtain ⟨a', rfl⟩ := ha
    have hc : a'*b=c^2 := by nlinarith [hp.pos]
    have hg : a'.Coprime b := hab.of_dvd_left (dvd_mul_left _ _)
    obtain ⟨r,s,hr,hs,hc',hrs⟩ := coprime_square_factors hg hc
    exact ⟨r,s,hc',hrs,Or.inr ⟨by rw [hr],hs⟩⟩
  · obtain ⟨b', rfl⟩ := hb
    have hc : a*b'=c^2 := by nlinarith [hp.pos]
    have hg : a.Coprime b' := hab.of_dvd_right (dvd_mul_left _ _)
    obtain ⟨r,s,hr,hs,hc',hrs⟩ := coprime_square_factors hg hc
    exact ⟨r,s,hc',hrs,Or.inl ⟨hr,by rw [hs]⟩⟩

private lemma mod_three : ∀ x y : ZMod 3, x^2+y^2=0 → x=0 ∧ y=0 := by
  decide

lemma three_dvd_sum_sq {x y : ℕ} (h : 3 ∣ x^2+y^2) : 3 ∣ x ∧ 3 ∣ y := by
  have he : (x : ZMod 3)^2+(y : ZMod 3)^2=0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff (x^2+y^2) 3).mpr h
  have ht := mod_three _ _ he
  exact ⟨(ZMod.natCast_eq_zero_iff x 3).mp ht.1,
    (ZMod.natCast_eq_zero_iff y 3).mp ht.2⟩

lemma coprime_hypotenuses {m n a b : ℕ} (hmn : m.Coprime n)
    (ha : a^2=m^2+n^2) (hb : b^2=m^2+4*n^2) : a.Coprime b := by
  apply Nat.coprime_iff_gcd_eq_one.mpr
  by_contra he
  obtain ⟨p,hp,hpg⟩ := Nat.exists_prime_and_dvd he
  have hpa : p ∣ a := hpg.trans (Nat.gcd_dvd_left _ _)
  have hpb : p ∣ b := hpg.trans (Nat.gcd_dvd_right _ _)
  have hpd : p ∣ 3*n^2 := by
    have hd := Nat.dvd_sub (dvd_pow hpb (by decide : 2 ≠ 0)) (dvd_pow hpa (by decide : 2 ≠ 0))
    have hd' : b^2-a^2=3*n^2 := by omega
    simpa [hd'] using hd
  have hpn : p ∣ n := by
    rcases hp.dvd_mul.mp hpd with hp3 | hpn
    · have hp_eq : p=3 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp3
      subst p
      apply (three_dvd_sum_sq (x := m) (y := n) ?_).2
      rw [← ha]
      exact dvd_pow hpa (by decide : 2 ≠ 0)
    · exact hp.dvd_of_dvd_pow hpn
  have hpm : p ∣ m := by
    apply hp.dvd_of_dvd_pow (n := 2)
    apply (Nat.dvd_add_iff_left (dvd_pow hpn (by decide : 2 ≠ 0))).mpr
    rw [← ha]
    exact dvd_pow hpa (by decide : 2 ≠ 0)
  exact hp.not_dvd_one (hmn.gcd_eq_one ▸ Nat.dvd_gcd hpm hpn)

lemma square_mod_two (a : ℕ) : a^2 % 2=a%2 := by
  rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [Nat.pow_mod,h]

lemma odd_hypotenuses {m n a b : ℕ} (hm : m%2=1) (hn : n%2=0)
    (ha : a^2=m^2+n^2) (hb : b^2=m^2+4*n^2) : a%2=1 ∧ b%2=1 := by
  have h1 := congrArg (fun x : ℕ => x%2) ha
  have h2 := congrArg (fun x : ℕ => x%2) hb
  dsimp only at h1 h2
  rw [square_mod_two,Nat.add_mod,square_mod_two,square_mod_two,hm,hn] at h1
  rw [square_mod_two,Nat.add_mod,Nat.mul_mod,square_mod_two,square_mod_two,hm,hn] at h2
  norm_num at h1 h2
  exact ⟨h1,h2⟩

lemma half_difference_factors {A B c n : ℕ} (hA : A%2=1) (hB : B%2=1)
    (hc : 0<c) (hn : 0<n) (hab : A.Coprime B)
    (hsq : A^2=B^2+4*c*n^2) :
    ∃ x y : ℕ, 0<x ∧ 0<y ∧ x.Coprime y ∧ x+y=A ∧ x*y=c*n^2 := by
  have hlt : B<A := by nlinarith
  let x := A/2+B/2+1
  let y := A/2-B/2
  have hsum : x+y=A := by dsimp [x,y]; omega
  have hdiff : y+B=x := by dsimp [x,y]; omega
  have hx : 0<x := by dsimp [x]; omega
  have hy : 0<y := by dsimp [y]; omega
  have hcop : x.Coprime y := by
    have hdx := Nat.gcd_dvd_left x y
    have hdy := Nat.gcd_dvd_right x y
    have hdA : Nat.gcd x y ∣ A := hsum ▸ dvd_add hdx hdy
    have hdB : Nat.gcd x y ∣ B := by
      have he : x-y=B := by omega
      simpa [he] using Nat.dvd_sub hdx hdy
    exact Nat.coprime_iff_gcd_eq_one.mpr
      (Nat.dvd_one.mp (hab.gcd_eq_one ▸ Nat.dvd_gcd hdA hdB))
  refine ⟨x,y,hx,hy,hcop,hsum,?_⟩
  rw [← hsum,← hdiff] at hsq
  rw [← hdiff]
  nlinarith

lemma first_descent_stage {m n a b : ℕ} (hm : 0<m) (hn : 0<n)
    (hcp : m.Coprime n) (hmo : m%2=1) (hne : n%2=0)
    (ha : a^2=m^2+n^2) (hb : b^2=m^2+4*n^2) :
    ∃ r s : ℕ, 0<r ∧ 0<s ∧ r.Coprime s ∧ n=2*r*s ∧
      m^2+10*r^2*s^2=r^4+9*s^4 := by
  have hab := coprime_hypotenuses hcp ha hb
  obtain ⟨hao,hbo⟩ := odd_hypotenuses hmo hne ha hb
  obtain ⟨k,hk⟩ : 2 ∣ n := Nat.dvd_of_mod_eq_zero hne
  have hkpos : 0<k := by omega
  have he : b^2=a^2+4*3*k^2 := by rw [hk] at ha hb; nlinarith
  obtain ⟨x,y,hx,hy,hxy,hsum,hprod⟩ :=
    half_difference_factors hbo hao (by decide : 0<3) hkpos hab.symm he
  obtain ⟨r,s,hrs,hcop,hfac⟩ :=
    coprime_prime_square_factors (by norm_num : Nat.Prime 3) hxy hprod
  have hr : 0<r := by nlinarith
  have hs : 0<s := by nlinarith
  rcases hfac with ⟨hxr,hys⟩ | ⟨hxr,hys⟩
  · refine ⟨r,s,hr,hs,hcop,by nlinarith,?_⟩
    rw [hxr,hys] at hsum
    rw [← hsum,hk,hrs] at hb
    nlinarith [hb]
  · refine ⟨s,r,hs,hr,hcop.symm,by nlinarith,?_⟩
    rw [hxr,hys] at hsum
    rw [← hsum,hk,hrs] at hb
    nlinarith [hb]

lemma quartic_factor_coprime {m r s : ℕ} (hmo : m%2=1) (hcp : r.Coprime s)
    (hq : m^2+10*r^2*s^2=r^4+9*s^4) :
    IsCoprime ((r : ℤ)^2-s^2) ((r : ℤ)^2-9*s^2) := by
  have hq' : (m : ℤ)^2+10*(r : ℤ)^2*s^2=(r : ℤ)^4+9*s^4 := by exact_mod_cast hq
  have he : ((r : ℤ)^2-s^2)*((r : ℤ)^2-9*s^2)=(m : ℤ)^2 := by nlinarith
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  by_contra hc
  change ¬ Nat.Coprime (((r : ℤ)^2-s^2).natAbs) (((r : ℤ)^2-9*s^2).natAbs) at hc
  obtain ⟨p,hp,hpa,hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  have hpa' := Int.natCast_dvd.mpr hpa
  have hpb' := Int.natCast_dvd.mpr hpb
  have hp8 : (p : ℤ) ∣ 8*(s : ℤ)^2 := by
    convert dvd_sub hpa' hpb' using 1 <;> ring
  rcases Int.Prime.dvd_mul' hp hp8 with hp8 | hps
  · have hd8 : p ∣ 2^3 := by exact_mod_cast hp8
    have hd2 : p ∣ 2 := hp.dvd_of_dvd_pow hd8
    have hpeq : p=2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd2
    subst p
    have hm2 : (2 : ℤ) ∣ (m : ℤ)^2 := by
      rw [← he]
      exact dvd_mul_of_dvd_left hpa' _
    have hm2' : 2 ∣ m := by exact_mod_cast (Int.Prime.dvd_pow' Nat.prime_two hm2)
    have hh := Nat.mod_eq_zero_of_dvd hm2'
    omega
  · have hps' := Int.Prime.dvd_pow' hp hps
    have hprsq : (p : ℤ) ∣ (r : ℤ)^2 := by
      have hh := dvd_add hpa' (dvd_pow hps' (by decide : 2 ≠ 0))
      simpa using hh
    have hpr' := Int.Prime.dvd_pow' hp hprsq
    have hpr : p ∣ r := by exact_mod_cast hpr'
    have hps : p ∣ s := by exact_mod_cast hps'
    exact hp.not_dvd_one (hcp.gcd_eq_one ▸ Nat.dvd_gcd hpr hps)

lemma quartic_square_roots {m r s : ℕ} (hm : 0<m) (hmo : m%2=1)
    (hcp : r.Coprime s) (hq : m^2+10*r^2*s^2=r^4+9*s^4) :
    ∃ A B : ℕ, 0<A ∧ 0<B ∧ A.Coprime B ∧ A^2=B^2+8*s^2 ∧
      (r^2=A^2+s^2 ∨ r^2+B^2=s^2) := by
  have hc := quartic_factor_coprime hmo hcp hq
  have hq' : (m : ℤ)^2+10*(r : ℤ)^2*s^2=(r : ℤ)^4+9*s^4 := by exact_mod_cast hq
  have he : ((r : ℤ)^2-s^2)*((r : ℤ)^2-9*s^2)=(m : ℤ)^2 := by nlinarith
  obtain ⟨a,ha⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hc) he
  obtain ⟨b,hb⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hc.symm)
    (by simpa [mul_comm] using he)
  have hmpos : 0<(m : ℤ)^2 := by exact_mod_cast (sq_pos_of_pos hm)
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · have hr : IsCoprime (a^2) (b^2) := by simpa only [ha,hb] using hc
    have hr' := (IsCoprime.pow_iff (by decide : 0<2) (by decide : 0<2)).mp hr
    have ha0 : a ≠ 0 := by intro hh; rw [ha,hb,hh] at he; norm_num at he; omega
    have hb0 : b ≠ 0 := by intro hh; rw [ha,hb,hh] at he; norm_num at he; omega
    refine ⟨a.natAbs,b.natAbs,Int.natAbs_pos.mpr ha0,Int.natAbs_pos.mpr hb0,
      Int.isCoprime_iff_gcd_eq_one.mp hr',?_,Or.inl ?_⟩
    · have hh : (a.natAbs : ℤ)^2=(b.natAbs : ℤ)^2+8*(s : ℤ)^2 := by
        rw [Int.natAbs_sq,Int.natAbs_sq]
        nlinarith
      exact_mod_cast hh
    · have hh : (r : ℤ)^2=(a.natAbs : ℤ)^2+(s : ℤ)^2 := by
        rw [Int.natAbs_sq]
        nlinarith
      exact_mod_cast hh
  · rw [ha,hb] at he
    nlinarith [sq_nonneg (a*b)]
  · rw [ha,hb] at he
    nlinarith [sq_nonneg (a*b)]
  · have hr : IsCoprime (a^2) (b^2) := by
      simpa only [ha,hb,IsCoprime.neg_left_iff,IsCoprime.neg_right_iff] using hc
    have hr' := (IsCoprime.pow_iff (by decide : 0<2) (by decide : 0<2)).mp hr
    have ha0 : a ≠ 0 := by intro hh; rw [ha,hb,hh] at he; norm_num at he; omega
    have hb0 : b ≠ 0 := by intro hh; rw [ha,hb,hh] at he; norm_num at he; omega
    refine ⟨b.natAbs,a.natAbs,Int.natAbs_pos.mpr hb0,Int.natAbs_pos.mpr ha0,
      Int.isCoprime_iff_gcd_eq_one.mp hr'.symm,?_,Or.inr ?_⟩
    · have hh : (b.natAbs : ℤ)^2=(a.natAbs : ℤ)^2+8*(s : ℤ)^2 := by
        rw [Int.natAbs_sq,Int.natAbs_sq]
        nlinarith
      exact_mod_cast hh
    · have hh : (r : ℤ)^2+(a.natAbs : ℤ)^2=(s : ℤ)^2 := by
        rw [Int.natAbs_sq]
        nlinarith
      exact_mod_cast hh

lemma odd_square_gap {A B s : ℕ} (hcp : A.Coprime B)
    (he : A^2=B^2+8*s^2) : A%2=1 ∧ B%2=1 := by
  have hh := congrArg (fun x : ℕ => x%2) he
  dsimp only at hh
  rw [square_mod_two,Nat.add_mod,Nat.mul_mod,square_mod_two,square_mod_two] at hh
  norm_num at hh
  have hne : A%2 ≠ 0 := by
    intro hA
    have hB : B%2=0 := by omega
    have hdA : 2 ∣ A := Nat.dvd_of_mod_eq_zero hA
    have hdB : 2 ∣ B := Nat.dvd_of_mod_eq_zero hB
    have hd1 := hcp.gcd_eq_one ▸ Nat.dvd_gcd hdA hdB
    norm_num at hd1
  omega

lemma second_descent_stage {m r s : ℕ} (hm : 0<m) (hmo : m%2=1)
    (hr : 0<r) (hs : 0<s) (hcp : r.Coprime s)
    (hq : m^2+10*r^2*s^2=r^4+9*s^4) :
    ∃ p q : ℕ, 0<p ∧ 0<q ∧ p.Coprime q ∧ p%2=1 ∧ s=p*q ∧
      (r^2=(p^2+q^2)*(p^2+4*q^2) ∨ r^2+p^4+4*q^4=5*p^2*q^2) := by
  obtain ⟨A,B,hA,hB,hAB,hgap,hrel⟩ := quartic_square_roots hm hmo hcp hq
  obtain ⟨hAo,hBo⟩ := odd_square_gap hAB hgap
  obtain ⟨x,y,hx,hy,hxy,hsum,hprod⟩ :=
    half_difference_factors hAo hBo (by decide : 0<2) hs hAB (by nlinarith [hgap])
  obtain ⟨p,q,hspq,hpq,hfac⟩ := coprime_prime_square_factors Nat.prime_two hxy hprod
  have hp : 0<p := by nlinarith
  have hq : 0<q := by nlinarith
  have haux : ∀ p q : ℕ, 0<p → 0<q → p.Coprime q → s=p*q → A=p^2+2*q^2 →
      ∃ p q : ℕ, 0<p ∧ 0<q ∧ p.Coprime q ∧ p%2=1 ∧ s=p*q ∧
        (r^2=(p^2+q^2)*(p^2+4*q^2) ∨ r^2+p^4+4*q^4=5*p^2*q^2) := by
    intro p q hp hq hpq hspq hAeq
    have hpo : p%2=1 := by
      rw [hAeq,Nat.add_mod,Nat.mul_mod,square_mod_two,square_mod_two] at hAo
      norm_num at hAo
      exact hAo
    refine ⟨p,q,hp,hq,hpq,hpo,hspq,?_⟩
    rw [hAeq,hspq] at hgap hrel
    rcases hrel with hrel | hrel
    · left
      nlinarith [hrel]
    · right
      nlinarith [hrel,hgap]
  rcases hfac with ⟨hxp,hyq⟩ | ⟨hxp,hyq⟩
  · apply haux p q hp hq hpq hspq
    rw [hxp,hyq] at hsum
    exact hsum.symm
  · apply haux q p hq hp hpq.symm (by nlinarith)
    rw [hxp,hyq] at hsum
    nlinarith

lemma coprime_sum_forms {p q : ℕ} (hcp : p.Coprime q) :
    (p^2+q^2).Coprime (p^2+4*q^2) := by
  have h3 : (p^2+q^2).Coprime 3 := by
    apply Nat.Coprime.symm
    apply (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mpr
    intro hd
    obtain ⟨hp,hq⟩ := three_dvd_sum_sq hd
    have hh := hcp.gcd_eq_one ▸ Nat.dvd_gcd hp hq
    norm_num at hh
  have hq : (p^2+q^2).Coprime (q^2) := by
    rw [Nat.coprime_add_self_left]
    exact hcp.pow 2 2
  have he : (p^2+q^2).Coprime (3*q^2+(p^2+q^2)) :=
    Nat.coprime_add_self_right.mpr (h3.mul_right hq)
  convert he using 1 <;> ring

lemma other_leg_even {p q a : ℕ} (hcp : p.Coprime q) (hpo : p%2=1)
    (he : a^2=p^2+q^2) : q%2=0 := by
  have hp : PythagoreanTriple (p : ℤ) (q : ℤ) (a : ℤ) := by
    dsimp [PythagoreanTriple]
    exact_mod_cast (by nlinarith [he] : p*p+q*q=a*a)
  have hg : Int.gcd (p : ℤ) (q : ℤ)=1 := by exact_mod_cast hcp
  have hpo' : (p : ℤ)%2=1 := by exact_mod_cast hpo
  have hpar := hp.even_odd_of_coprime hg
  have hqe : (q : ℤ)%2=0 := by omega
  exact_mod_cast hqe

lemma negative_stage_solution {p q r : ℕ} (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (hcp : p.Coprime q) (hpo : p%2=1)
    (he : r^2+p^4+4*q^4=5*p^2*q^2) :
    ∃ a b : ℕ, 0<a ∧ 0<b ∧ b.Coprime a ∧ b%2=1 ∧ a%2=0 ∧
      a ≤ q ∧ q^2=b^2+a^2 ∧ p^2=b^2+4*a^2 := by
  have he' : (r : ℤ)^2+(p : ℤ)^4+4*(q : ℤ)^4=5*(p : ℤ)^2*q^2 := by
    exact_mod_cast he
  have hp' : 0<((p : ℤ)^2-q^2)*(4*(q : ℤ)^2-p^2) := by
    have hr' : 0<(r : ℤ)^2 := by exact_mod_cast (sq_pos_of_pos hr)
    nlinarith
  have hbds : (q : ℤ)^2<(p : ℤ)^2 ∧ (p : ℤ)^2<4*(q : ℤ)^2 := by
    rcases mul_pos_iff.mp hp' with hh | hh
    · constructor <;> linarith [hh.1,hh.2]
    · nlinarith [hh.1,hh.2,sq_nonneg (q : ℤ)]
  have hbds' : q^2<p^2 ∧ p^2<4*q^2 := by exact_mod_cast hbds
  let A := p^2-q^2
  let B := 4*q^2-p^2
  have hA : 0<A := Nat.sub_pos_of_lt hbds'.1
  have hB : 0<B := Nat.sub_pos_of_lt hbds'.2
  have heA : A+q^2=p^2 := Nat.sub_add_cancel hbds'.1.le
  have heB : B+p^2=4*q^2 := Nat.sub_add_cancel hbds'.2.le
  have hsum : A+B=3*q^2 := by omega
  have hprod : A*B=r^2 := by
    have hhA : (A : ℤ)=(p : ℤ)^2-q^2 := by
      have hh : (A : ℤ)+(q : ℤ)^2=(p : ℤ)^2 := by exact_mod_cast heA
      linarith
    have hhB : (B : ℤ)=4*(q : ℤ)^2-p^2 := by
      have hh : (B : ℤ)+(p : ℤ)^2=4*(q : ℤ)^2 := by exact_mod_cast heB
      linarith
    have hh : (A : ℤ)*(B : ℤ)=(r : ℤ)^2 := by rw [hhA,hhB]; nlinarith
    exact_mod_cast hh
  have hAq : A.Coprime (q^2) := by
    dsimp [A]
    rw [Nat.coprime_sub_self_left hbds'.1.le]
    exact hcp.pow 2 2
  have hgdA := Nat.gcd_dvd_left A B
  have hgdB := Nat.gcd_dvd_right A B
  have hgd : Nat.gcd A B ∣ 3*q^2 := hsum ▸ dvd_add hgdA hgdB
  have hgq : (Nat.gcd A B).Coprime (q^2) := hAq.of_dvd_left hgdA
  have hg3 : Nat.gcd A B ∣ 3 := hgq.dvd_mul_right.mp hgd
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hg3 with hg | hg
  · have hg' : A.Coprime B := hg
    obtain ⟨a,b,ha,hb,_,hab⟩ := coprime_square_factors hg' hprod
    have hthree : 3 ∣ a^2+b^2 := by rw [← ha,← hb,hsum]; exact dvd_mul_right _ _
    obtain ⟨hda,hdb⟩ := three_dvd_sum_sq hthree
    have hh := hab.gcd_eq_one ▸ Nat.dvd_gcd hda hdb
    norm_num at hh
  · have hdA : 3 ∣ A := hg ▸ hgdA
    have hdB : 3 ∣ B := hg ▸ hgdB
    obtain ⟨a',ha'⟩ := hdA
    obtain ⟨b',hb'⟩ := hdB
    have hcp' : a'.Coprime b' := by
      rw [ha',hb',Nat.gcd_mul_left] at hg
      exact Nat.coprime_iff_gcd_eq_one.mpr (by omega)
    have hr3 : 3 ∣ r := by
      apply (show Nat.Prime 3 by norm_num).dvd_of_dvd_pow (n := 2)
      rw [← hprod]
      rw [ha']
      exact dvd_mul_of_dvd_left (dvd_mul_right 3 a') B
    obtain ⟨r',hr'⟩ := hr3
    have heprod : a'*b'=r'^2 := by rw [ha',hb',hr'] at hprod; nlinarith
    obtain ⟨a,b,ha,hb,_,hab⟩ := coprime_square_factors hcp' heprod
    have hAeq : A=3*a^2 := by rw [ha',ha]
    have hBeq : B=3*b^2 := by rw [hb',hb]
    have ha0 : 0<a := by nlinarith
    have hb0 : 0<b := by nlinarith
    have hqeq : q^2=b^2+a^2 := by nlinarith [hsum]
    have hpeq : p^2=b^2+4*a^2 := by nlinarith [heA]
    have hbo : b%2=1 := by
      have hh := congrArg (fun x : ℕ => x%2) hpeq
      dsimp only at hh
      rw [square_mod_two,Nat.add_mod,Nat.mul_mod,square_mod_two,square_mod_two,hpo] at hh
      norm_num at hh
      exact hh.symm
    exact ⟨a,b,ha0,hb0,hab.symm,hbo,other_leg_even hab.symm hbo hqeq,
      by nlinarith [hqeq],hqeq,hpeq⟩

theorem no_normalized_solution (n : ℕ) : ∀ m a b : ℕ,
    0<m → 0<n → m.Coprime n → m%2=1 → n%2=0 →
    a^2=m^2+n^2 → b^2=m^2+4*n^2 → False := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro m a b hm hn hcp hmo hne ha hb
    obtain ⟨r,s,hr,hs,hrs,hnrs,hquartic⟩ := first_descent_stage hm hn hcp hmo hne ha hb
    obtain ⟨p,q,hp,hq,hpq,hpo,hspq,hforms⟩ := second_descent_stage hm hmo hr hs hrs hquartic
    have hsle : s ≤ r*s := by
      calc s=1*s := by ring
           _ ≤ r*s := Nat.mul_le_mul_right s (by omega)
    have hslt : s<n := by nlinarith [hnrs]
    have hqle : q ≤ s := by
      calc q=1*q := by ring
           _ ≤ p*q := Nat.mul_le_mul_right q (by omega)
           _ = s := hspq.symm
    have hq_lt : q<n := hqle.trans_lt hslt
    rcases hforms with hforms | hforms
    · obtain ⟨a',b',ha',hb',_,_⟩ :=
        coprime_square_factors (coprime_sum_forms hpq) hforms.symm
      exact ih q hq_lt p a' b' hp hq hpq hpo
        (other_leg_even hpq hpo ha'.symm) ha'.symm hb'.symm
    · obtain ⟨a',b',ha',hb',hcop',hbo',hae',hale',hqeq,hpeq⟩ :=
        negative_stage_solution hp hq hr hpq hpo hforms
      exact ih a' (hale'.trans_lt hq_lt) b' q p hb' ha' hcop' hbo' hae' hqeq hpeq

theorem no_primitive_solution {m n a b : ℕ} (hm : 0<m) (hn : 0<n)
    (hcp : m.Coprime n) (ha : a^2=m^2+n^2) (hb : b^2=m^2+4*n^2) : False := by
  have ht : PythagoreanTriple (m : ℤ) (n : ℤ) (a : ℤ) := by
    dsimp [PythagoreanTriple]
    exact_mod_cast (by nlinarith [ha] : m*m+n*n=a*a)
  have hg : Int.gcd (m : ℤ) (n : ℤ)=1 := by exact_mod_cast hcp
  have hpar : (m%2=0 ∧ n%2=1) ∨ (m%2=1 ∧ n%2=0) := by
    exact_mod_cast ht.even_odd_of_coprime hg
  rcases hpar with ⟨hme,hno⟩ | ⟨hmo,hne⟩
  · obtain ⟨k,hmk⟩ : 2 ∣ m := Nat.dvd_of_mod_eq_zero hme
    have hk : 0<k := by omega
    have hbk : 2 ∣ b := by
      apply Nat.prime_two.dvd_of_dvd_pow (n := 2)
      rw [hb,hmk]
      exact ⟨2*(k^2+n^2),by ring⟩
    obtain ⟨b',hbb'⟩ := hbk
    have hbp : b'^2=n^2+k^2 := by rw [hmk,hbb'] at hb; nlinarith
    have hnk : n.Coprime k := hcp.symm.of_dvd_right (by rw [hmk]; exact dvd_mul_left _ _)
    have hke := other_leg_even hnk hno hbp
    apply no_normalized_solution k n b' a hn hk hnk hno hke hbp
    rw [hmk] at ha
    nlinarith
  · exact no_normalized_solution n m a b hm hn hcp hmo hne ha hb

lemma clear_square_denominator {u : ℚ} {k : ℕ} (h : IsSquare (u^2+k)) :
    IsSquare (u.num.natAbs^2+k*u.den^2) := by
  obtain ⟨v,hv⟩ := h
  have hd : (u.den : ℚ) ≠ 0 := by exact_mod_cast u.den_ne_zero
  have hn : (u.num : ℚ)=u*(u.den : ℚ) := by
    calc
      (u.num : ℚ)=((u.num : ℚ)/(u.den : ℚ))*(u.den : ℚ) := by field_simp
      _=u*(u.den : ℚ) := by rw [Rat.num_div_den]
  have hm : (u.num.natAbs : ℚ)^2=(u.num : ℚ)^2 := by
    have hh := congrArg (fun z : ℤ => (z : ℚ)) (Int.natAbs_sq u.num)
    simpa only [Int.cast_natCast, Nat.cast_pow, Int.cast_pow] using hh
  apply Rat.isSquare_natCast_iff.mp
  refine ⟨v*(u.den : ℚ),?_⟩
  push_cast
  rw [hm,hn]
  linear_combination (u.den : ℚ)^2*hv

/-- There is no nonzero rational u for which both u²+1 and u²+4 are squares.
This completes the previously missing global descent for the orthogonal-grid
specialization; it is not a theorem about arbitrary configurations. -/
theorem no_simultaneous_squares {u : ℚ} (hu : u ≠ 0) :
    ¬ (IsSquare (u^2+1) ∧ IsSquare (u^2+4)) := by
  rintro ⟨h1,h4⟩
  obtain ⟨a,ha⟩ := clear_square_denominator (u := u) (k := 1) h1
  obtain ⟨b,hb⟩ := clear_square_denominator (u := u) (k := 4) h4
  apply no_primitive_solution (a := a) (b := b)
    (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hu)) u.den_pos u.reduced
  · simpa only [one_mul, pow_two] using ha.symm
  · simpa only [pow_two] using hb.symm

theorem simultaneous_squares_iff_zero (u : ℚ) :
    (IsSquare (u^2+1) ∧ IsSquare (u^2+4)) ↔ u=0 := by
  constructor
  · intro h
    by_contra hu
    exact no_simultaneous_squares hu h
  · rintro rfl
    norm_num

#print axioms no_normalized_solution
#print axioms no_primitive_solution
#print axioms no_simultaneous_squares
#print axioms simultaneous_squares_iff_zero
end Erdos213.OrthogonalGlobal
