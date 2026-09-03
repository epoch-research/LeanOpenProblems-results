import FormalConjecturesUtil

/-! Elementary descent for a quartic arising in the Morley investigation.
This file does not settle the unrestricted Erdős conjecture. -/
namespace Erdos213.MorleyQuarticDescent
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

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



lemma coprime_prime_fourth_factors {a b c p : ℕ} (hp : p.Prime)
    (hab : a.Coprime b) (h : a*b=p*c^4) :
    ∃ r s : ℕ, c=r*s ∧ r.Coprime s ∧
      ((a=r^4 ∧ b=p*s^4) ∨ (a=p*r^4 ∧ b=s^4)) := by
  have hh : a*b=p*(c^2)^2 := by nlinarith [h]
  obtain ⟨u,v,hc,huv,hfac⟩ := coprime_prime_square_factors hp hab hh
  obtain ⟨r,s,hu,hv,hc',hrs⟩ := coprime_square_factors huv hc.symm
  refine ⟨r,s,hc',hrs,?_⟩
  rcases hfac with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · left
    constructor
    · rw [ha,hu]; ring
    · rw [hb,hv]; ring
  · right
    constructor
    · rw [ha,hu]; ring
    · rw [hb,hv]; ring

def Quartic (a b c : ℕ) : Prop := c^2+3*a^2*b^2=a^4+3*b^4

lemma Quartic.cast {a b c : ℕ} (h : Quartic a b c) {R : Type*} [CommSemiring R] :
    (c : R)^2+3*(a : R)^2*(b : R)^2=(a : R)^4+3*(b : R)^4 := by
  have hh := congrArg (fun n : ℕ => (n : R)) h
  push_cast at hh
  exact hh

private lemma mod_four : ∀ a b c : ZMod 4,
    c^2+3*a^2*b^2=a^4+3*b^4 →
    (a.val%2=0 → b.val%2=0) ∧ (c.val%2=0 → a.val%2=0 ∧ b.val%2=0) := by decide

private lemma mod_nine : ∀ a b c : ZMod 9,
    c^2+3*a^2*b^2=a^4+3*b^4 → a.val%3=0 → b.val%3=0 := by decide

lemma primitive_congruences {a b c : ℕ} (hcp : a.Coprime b) (h : Quartic a b c) :
    a%2=1 ∧ c%2=1 ∧ ¬3 ∣ a := by
  have h4 : (c : ZMod 4)^2+3*(a : ZMod 4)^2*(b : ZMod 4)^2 =
      (a : ZMod 4)^4+3*(b : ZMod 4)^4 := Quartic.cast h
  have hm := mod_four _ _ _ h4
  simp only [ZMod.val_natCast, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 4)] at hm
  have ha : a%2=1 := by
    by_contra ha
    have ha0 : a%2=0 := by omega
    have hb0 := hm.1 ha0
    have hd := hcp.gcd_eq_one ▸ Nat.dvd_gcd
      (Nat.dvd_of_mod_eq_zero ha0) (Nat.dvd_of_mod_eq_zero hb0)
    norm_num at hd
  have hc : c%2=1 := by
    by_contra hc
    have hc0 : c%2=0 := by omega
    have hh := (hm.2 hc0).1
    omega
  refine ⟨ha,hc,?_⟩
  intro h3a
  have h9 : (c : ZMod 9)^2+3*(a : ZMod 9)^2*(b : ZMod 9)^2 =
      (a : ZMod 9)^4+3*(b : ZMod 9)^4 := Quartic.cast h
  have hh := mod_nine _ _ _ h9
  simp only [ZMod.val_natCast, Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 9)] at hh
  have h3b := Nat.dvd_of_mod_eq_zero (hh (Nat.mod_eq_zero_of_dvd h3a))
  have hd := hcp.gcd_eq_one ▸ Nat.dvd_gcd h3a h3b
  norm_num at hd

lemma quartic_coprime_right {a b c : ℕ} (hcp : a.Coprime b) (h : Quartic a b c) :
    c.Coprime b := by
  by_contra hn
  obtain ⟨p,hp,hpc,hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  letI : Fact p.Prime := ⟨hp⟩
  have hc0 : (c : ZMod p)=0 := (ZMod.natCast_eq_zero_iff c p).mpr hpc
  have hb0 : (b : ZMod p)=0 := (ZMod.natCast_eq_zero_iff b p).mpr hpb
  have he : (c : ZMod p)^2+3*(a : ZMod p)^2*(b : ZMod p)^2 =
      (a : ZMod p)^4+3*(b : ZMod p)^4 := Quartic.cast h
  simp only [hc0,hb0,zero_pow (by decide : 2 ≠ 0),zero_pow (by decide : 4 ≠ 0),
    mul_zero,add_zero] at he
  have ha0 : (a : ZMod p)=0 := eq_zero_of_pow_eq_zero he.symm
  have hpa := (ZMod.natCast_eq_zero_iff a p).mp ha0
  exact hp.not_dvd_one (hcp.gcd_eq_one ▸ Nat.dvd_gcd hpa hpb)

lemma quartic_coprime_three {a b c : ℕ} (hcp : a.Coprime b) (h : Quartic a b c) :
    c.Coprime 3 := by
  apply Nat.Coprime.symm
  apply (Nat.prime_three.coprime_iff_not_dvd).mpr
  intro hc
  have hc0 : (c : ZMod 3)=0 := (ZMod.natCast_eq_zero_iff c 3).mpr hc
  have he : (c : ZMod 3)^2+3*(a : ZMod 3)^2*(b : ZMod 3)^2 =
      (a : ZMod 3)^4+3*(b : ZMod 3)^4 := Quartic.cast h
  have hm : ∀ x y z : ZMod 3, z^2+3*x^2*y^2=x^4+3*y^4 → z=0 → x=0 := by decide
  have ha0 : (a : ZMod 3)=0 := hm _ _ _ he hc0
  exact (primitive_congruences hcp h).2.2 ((ZMod.natCast_eq_zero_iff a 3).mp ha0)

lemma first_factor_coprime {a b c A : ℕ} (hcp : a.Coprime b) (h : Quartic a b c)
    (hA : A+3*b^2=2*a^2+2*c) : A.Coprime c := by
  let g := Nat.gcd A c
  have hA0 : (A : ZMod g)=0 := (ZMod.natCast_eq_zero_iff A g).mpr (Nat.gcd_dvd_left A c)
  have hc0 : (c : ZMod g)=0 := (ZMod.natCast_eq_zero_iff c g).mpr (Nat.gcd_dvd_right A c)
  have he : (c : ZMod g)^2+3*(a : ZMod g)^2*(b : ZMod g)^2 =
      (a : ZMod g)^4+3*(b : ZMod g)^4 := Quartic.cast h
  have heA : (A : ZMod g)+3*(b : ZMod g)^2=2*(a : ZMod g)^2+2*(c : ZMod g) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ZMod g)) hA
  simp only [hA0,hc0,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_add,add_zero] at he heA
  have hz : (3 : ZMod g)*(b : ZMod g)^4=0 := by
    linear_combination -4*he - (3*(b : ZMod g)^2-2*(a : ZMod g)^2)*heA
  have hdiv : g ∣ 3*b^4 := (ZMod.natCast_eq_zero_iff (3*b^4) g).mp (by exact_mod_cast hz)
  have hco := (quartic_coprime_three hcp h).mul_right ((quartic_coprime_right hcp h).pow_right 4)
  have hg1 := hco.gcd_eq_one ▸ Nat.dvd_gcd (Nat.gcd_dvd_right A c) hdiv
  exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp hg1)

lemma first_factors {a b c : ℕ} (hb : 0 < b) (hc : 0 < c) (h : Quartic a b c) :
    ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ A+3*b^2=2*a^2+2*c ∧
      B+2*a^2=3*b^2+2*c ∧ A+B=4*c ∧ A*B=3*b^4 := by
  let X : ℤ := 2*(a : ℤ)^2+2*c-3*(b : ℤ)^2
  let Y : ℤ := 3*(b : ℤ)^2+2*c-2*(a : ℤ)^2
  have hq : (c : ℤ)^2+3*(a : ℤ)^2*(b : ℤ)^2=(a : ℤ)^4+3*(b : ℤ)^4 := Quartic.cast h
  have hprod : X*Y=3*(b : ℤ)^4 := by dsimp [X,Y]; nlinarith [hq]
  have hsum : X+Y=4*(c : ℤ) := by dsimp [X,Y]; ring
  have hp : 0 < X*Y := by rw [hprod]; positivity
  have hpos : 0 < X ∧ 0 < Y := by
    rcases mul_pos_iff.mp hp with hh | hh
    · exact hh
    · have hc' : (0 : ℤ)<c := by exact_mod_cast hc
      omega
  let A := X.toNat
  let B := Y.toNat
  have hAX : (A : ℤ)=X := Int.toNat_of_nonneg hpos.1.le
  have hBY : (B : ℤ)=Y := Int.toNat_of_nonneg hpos.2.le
  have hAp : 0 < A := by exact_mod_cast (show (0 : ℤ)<A by rw [hAX]; exact hpos.1)
  have hBp : 0 < B := by exact_mod_cast (show (0 : ℤ)<B by rw [hBY]; exact hpos.2)
  refine ⟨A,B,hAp,hBp,?_,?_,?_,?_⟩
  · have he : (A : ℤ)+3*(b : ℤ)^2=2*(a : ℤ)^2+2*c := by rw [hAX]; dsimp [X]; ring
    exact_mod_cast he
  · have he : (B : ℤ)+2*(a : ℤ)^2=3*(b : ℤ)^2+2*c := by rw [hBY]; dsimp [Y]; ring
    exact_mod_cast he
  · have he : (A : ℤ)+(B : ℤ)=4*(c : ℤ) := by rw [hAX,hBY]; exact hsum
    exact_mod_cast he
  · have he : (A : ℤ)*(B : ℤ)=3*(b : ℤ)^4 := by rw [hAX,hBY]; exact hprod
    exact_mod_cast he

private lemma divisor_four {g : ℕ} (h : g ∣ 4) : g=1 ∨ g=2 ∨ g=4 := by
  have hb : g ≤ 4 := Nat.le_of_dvd (by decide : 0 < 4) h
  interval_cases g <;> norm_num at *

private lemma factor_mod_four : ∀ a b c A B : ZMod 4,
    a.val%2=1 → c.val%2=1 → A.val%2=0 →
    A+3*b^2=2*a^2+2*c → B+2*a^2=3*b^2+2*c → A=0 ∧ B=0 := by decide

lemma first_factors_gcd {a b c A B : ℕ} (hcp : a.Coprime b) (h : Quartic a b c)
    (hA : A+3*b^2=2*a^2+2*c) (hB : B+2*a^2=3*b^2+2*c) (hs : A+B=4*c) :
    Nat.gcd A B=1 ∨ Nat.gcd A B=4 := by
  let g := Nat.gcd A B
  have hAc := first_factor_coprime hcp h hA
  have hgc : g.Coprime c := hAc.of_dvd_left (Nat.gcd_dvd_left A B)
  have hg4c : g ∣ 4*c := hs ▸ dvd_add (Nat.gcd_dvd_left A B) (Nat.gcd_dvd_right A B)
  have hg4 : g ∣ 4 := hgc.dvd_mul_right.mp hg4c
  rcases divisor_four hg4 with hg | hg | hg
  · exact Or.inl hg
  · have h2A : 2 ∣ A := hg ▸ Nat.gcd_dvd_left A B
    have hA2 := Nat.mod_eq_zero_of_dvd h2A
    obtain ⟨ha2,hc2,_⟩ := primitive_congruences hcp h
    have hm := factor_mod_four (a : ZMod 4) b c A B
    simp only [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 4)] at hm
    have eA : (A : ZMod 4)+3*(b : ZMod 4)^2=2*(a : ZMod 4)^2+2*(c : ZMod 4) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ZMod 4)) hA
    have eB : (B : ZMod 4)+2*(a : ZMod 4)^2=3*(b : ZMod 4)^2+2*(c : ZMod 4) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ZMod 4)) hB
    have hh := hm ha2 hc2 hA2 eA eB
    have h4A := (ZMod.natCast_eq_zero_iff A 4).mp hh.1
    have h4B := (ZMod.natCast_eq_zero_iff B 4).mp hh.2
    have h4g : 4 ∣ g := Nat.dvd_gcd h4A h4B
    rw [hg] at h4g
    norm_num at h4g
  · exact Or.inr hg

private lemma mod_three_sum : ∀ x y : ZMod 3, x^2+y^4=0 → x=0 := by decide

lemma reject_swapped {a b c m n d : ℕ} (h3a : ¬3 ∣ a) (hd : d=1 ∨ d=4)
    (hA : d*(3*m^4)+3*b^2=2*a^2+2*c)
    (hB : d*n^4+2*a^2=3*b^2+2*c) : False := by
  have eA : (d : ZMod 3)*(3*(m : ZMod 3)^4)+3*(b : ZMod 3)^2=
      2*(a : ZMod 3)^2+2*(c : ZMod 3) := by
    exact_mod_cast congrArg (fun z : ℕ => (z : ZMod 3)) hA
  have eB : (d : ZMod 3)*(n : ZMod 3)^4+2*(a : ZMod 3)^2=
      3*(b : ZMod 3)^2+2*(c : ZMod 3) := by
    exact_mod_cast congrArg (fun z : ℕ => (z : ZMod 3)) hB
  have hd3 : (d : ZMod 3)=1 := by rcases hd with rfl | rfl <;> decide
  have hm : ∀ a b c m n d : ZMod 3, d=1 →
      d*(3*m^4)+3*b^2=2*a^2+2*c → d*n^4+2*a^2=3*b^2+2*c → a=0 := by decide
  exact h3a ((ZMod.natCast_eq_zero_iff a 3).mp (hm _ _ _ _ _ _ hd3 eA eB))

lemma first_descent_stage {a b c : ℕ} (hb : 0 < b) (hc : 0 < c)
    (hcp : a.Coprime b) (h : Quartic a b c) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ m.Coprime n ∧
      ((b=m*n ∧ 4*a^2+3*n^4=m^4+6*m^2*n^2) ∨
       (b=2*m*n ∧ a^2+3*n^4=m^4+6*m^2*n^2)) := by
  obtain ⟨A,B,hAp,hBp,hA,hB,hs,hp⟩ := first_factors hb hc h
  have h3a := (primitive_congruences hcp h).2.2
  rcases first_factors_gcd hcp h hA hB hs with hg | hg
  · obtain ⟨m,n,hbmn,hmn,hfac⟩ :=
      coprime_prime_fourth_factors Nat.prime_three (show A.Coprime B from hg) hp
    rcases hfac with ⟨hAm,hBn⟩ | ⟨hAm,hBn⟩
    · have hm : 0 < m := by
        by_contra hn
        have hz : m=0 := by omega
        simp [hz] at hAm
        omega
      have hn : 0 < n := by
        by_contra hn
        have hz : n=0 := by omega
        simp [hz] at hBn
        omega
      refine ⟨m,n,hm,hn,hmn,Or.inl ⟨hbmn,?_⟩⟩
      rw [hAm,hbmn] at hA
      rw [hBn,hbmn] at hB
      nlinarith [hA,hB]
    · exact (reject_swapped (d := 1) h3a (Or.inl rfl)
        (by simpa [hAm] using hA) (by simpa [hBn] using hB)).elim
  · have hdA : 4 ∣ A := hg ▸ Nat.gcd_dvd_left A B
    have hdB : 4 ∣ B := hg ▸ Nat.gcd_dvd_right A B
    obtain ⟨A',hAA⟩ := hdA
    obtain ⟨B',hBB⟩ := hdB
    have hg' : A'.Coprime B' := by
      rw [hAA,hBB,Nat.gcd_mul_left] at hg
      exact Nat.coprime_iff_gcd_eq_one.mpr (by omega)
    have h2prod : 2 ∣ 3*b^4 := by
      rw [← hp,hAA]
      exact ⟨2*A'*B,by ring⟩
    have h2b : 2 ∣ b := Nat.prime_two.dvd_of_dvd_pow
      ((Nat.prime_two.dvd_mul.mp h2prod).resolve_left (by decide))
    obtain ⟨d,hbd⟩ := h2b
    have hp' : A'*B'=3*d^4 := by
      rw [hAA,hBB,hbd] at hp
      nlinarith [hp]
    obtain ⟨m,n,hdmn,hmn,hfac⟩ := coprime_prime_fourth_factors Nat.prime_three hg' hp'
    rcases hfac with ⟨hAm,hBn⟩ | ⟨hAm,hBn⟩
    · have hm : 0 < m := by
        by_contra hn
        have hz : m=0 := by omega
        simp [hz] at hAm
        omega
      have hn : 0 < n := by
        by_contra hn
        have hz : n=0 := by omega
        simp [hz] at hBn
        omega
      refine ⟨m,n,hm,hn,hmn,Or.inr ⟨by rw [hbd,hdmn]; ring,?_⟩⟩
      rw [hAA,hAm,hbd,hdmn] at hA
      rw [hBB,hBn,hbd,hdmn] at hB
      nlinarith [hA,hB]
    · exact (reject_swapped (d := 4) h3a (Or.inr rfl)
        (by simpa [hAA,hAm] using hA) (by simpa [hBB,hBn] using hB)).elim

lemma three_not_left {a m n d : ℕ} (h3a : ¬3 ∣ a) (hd : d=1 ∨ d=4)
    (he : d*a^2+3*n^4=m^4+6*m^2*n^2) : ¬3 ∣ m := by
  intro h3m
  have he' : (d : ZMod 3)*(a : ZMod 3)^2+3*(n : ZMod 3)^4=
      (m : ZMod 3)^4+6*(m : ZMod 3)^2*(n : ZMod 3)^2 := by
    exact_mod_cast congrArg (fun z : ℕ => (z : ZMod 3)) he
  have hd' : (d : ZMod 3)=1 := by rcases hd with rfl | rfl <;> decide
  have hm : ∀ a m n d : ZMod 3, d=1 →
      d*a^2+3*n^4=m^4+6*m^2*n^2 → m=0 → a=0 := by decide
  have ha0 := hm _ _ _ _ hd' he' ((ZMod.natCast_eq_zero_iff m 3).mpr h3m)
  exact h3a ((ZMod.natCast_eq_zero_iff a 3).mp ha0)

lemma half_factors {L A n : ℕ} (hn : 0 < n) (he : L^2=A^2+12*n^4) :
    ∃ M N : ℕ, 0 < M ∧ 0 < N ∧ M+N=L ∧ M*N=3*n^4 := by
  have hlt : A<L := by nlinarith [pow_pos hn 4]
  have hpar : L%2=A%2 := by
    have hh := congrArg (fun z : ℕ => z%2) he
    rcases Nat.mod_two_eq_zero_or_one L with hL | hL <;>
      rcases Nat.mod_two_eq_zero_or_one A with hA | hA <;>
      norm_num [Nat.add_mod,Nat.mul_mod,Nat.pow_mod,hL,hA] at hh <;> omega
  let M := (L+A)/2
  let N := (L-A)/2
  have hsum : M+N=L := by dsimp [M,N]; omega
  have hdiff : N+A=M := by dsimp [M,N]; omega
  have hMp : 0 < M := by dsimp [M]; omega
  have hNp : 0 < N := by dsimp [N]; omega
  refine ⟨M,N,hMp,hNp,hsum,?_⟩
  have hL : L=A+2*N := by omega
  have hM : M=A+N := by omega
  rw [hL] at he
  rw [hM]
  nlinarith [he]

lemma second_sum_coprime {m n : ℕ} (hcp : m.Coprime n) (h3m : ¬3 ∣ m) :
    (m^2+3*n^2).Coprime (3*n^4) := by
  have hLn : (m^2+3*n^2).Coprime n := by
    convert (Nat.coprime_add_mul_left_left (m^2) n (3*n)).mpr (hcp.pow_left 2) using 1
    ring
  have hL3 : (m^2+3*n^2).Coprime 3 := by
    apply Nat.Coprime.symm
    apply (Nat.prime_three.coprime_iff_not_dvd).mpr
    intro hd
    have hh : 3 ∣ m^2 := (Nat.dvd_add_iff_left (dvd_mul_right 3 (n^2))).mpr hd
    exact h3m (Nat.prime_three.dvd_of_dvd_pow hh)
  exact hL3.mul_right (hLn.pow_right 4)

lemma second_descent_stage {m n A : ℕ} (hn : 0 < n) (hcp : m.Coprime n)
    (h3m : ¬3 ∣ m) (he : A^2+3*n^4=m^4+6*m^2*n^2) :
    ∃ r s : ℕ, 0 < r ∧ 0 < s ∧ r.Coprime s ∧ n=r*s ∧ Quartic r s m := by
  have hL : (m^2+3*n^2)^2=A^2+12*n^4 := by nlinarith [he]
  obtain ⟨M,N,hMp,hNp,hs,hp⟩ := half_factors hn hL
  have hMN : M.Coprime N := by
    have hco := second_sum_coprime hcp h3m
    have hdL : Nat.gcd M N ∣ m^2+3*n^2 := hs ▸ dvd_add (Nat.gcd_dvd_left M N) (Nat.gcd_dvd_right M N)
    have hdp : Nat.gcd M N ∣ 3*n^4 := hp ▸ dvd_mul_of_dvd_left (Nat.gcd_dvd_left M N) N
    have hd1 := hco.gcd_eq_one ▸ Nat.dvd_gcd hdL hdp
    exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp hd1)
  obtain ⟨r,s,hnrs,hrs,hfac⟩ := coprime_prime_fourth_factors Nat.prime_three hMN hp
  have hr : 0 < r := by
    by_contra hh
    have hr0 : r=0 := by omega
    rcases hfac with ⟨hM,hN⟩ | ⟨hM,hN⟩ <;> simp [hr0] at hM <;> omega
  have hs' : 0 < s := by
    by_contra hh
    have hs0 : s=0 := by omega
    rcases hfac with ⟨hM,hN⟩ | ⟨hM,hN⟩ <;> simp [hs0] at hN <;> omega
  rcases hfac with ⟨hM,hN⟩ | ⟨hM,hN⟩
  · refine ⟨r,s,hr,hs',hrs,hnrs,?_⟩
    rw [hM,hN,hnrs] at hs
    dsimp [Quartic]
    nlinarith [hs]
  · refine ⟨s,r,hs',hr,hrs.symm,by simpa [mul_comm] using hnrs,?_⟩
    rw [hM,hN,hnrs] at hs
    dsimp [Quartic]
    nlinarith [hs]

lemma unit_first_factor {a n : ℕ} (ha : 0 < a) (hn : 0 < n)
    (he : 4*a^2+3*n^4=1+6*n^2) : a=1 ∧ n=1 := by
  have he' : 4*(a : ℤ)^2+3*(n : ℤ)^4=1+6*(n : ℤ)^2 := by exact_mod_cast he
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have ha1 : (a : ℤ)=1 := by nlinarith [sq_nonneg ((n : ℤ)^2-1)]
  have hs : ((n : ℤ)^2-1)^2=0 := by rw [ha1] at he'; nlinarith [he']
  have hn1 : (n : ℤ)=1 := by
    have hh := eq_zero_of_pow_eq_zero hs
    nlinarith [hh]
  exact ⟨by exact_mod_cast ha1, by exact_mod_cast hn1⟩

lemma diagonal_primitive {r s m : ℕ} (hcp : r.Coprime s)
    (hq : Quartic r s m) (he : r=s) : r=1 ∧ s=1 ∧ m=1 := by
  have hr : r=1 := hcp.eq_one_of_dvd (by rw [he])
  have hs : s=1 := he ▸ hr
  have hm : m=1 := by
    dsimp [Quartic] at hq
    rw [hr,hs] at hq
    norm_num at hq
    nlinarith
  exact ⟨hr,hs,hm⟩

/-- Every primitive positive natural solution is diagonal. -/
theorem primitive_quartic (b : ℕ) : ∀ a c : ℕ,
    0 < a → 0 < b → 0 < c → a.Coprime b → Quartic a b c → a=b := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro a c ha hb hc hcp hq
    by_cases hab : a=b
    · exact hab
    obtain ⟨m,n,hm,hn,hmn,hcases⟩ := first_descent_stage hb hc hcp hq
    have h3a := (primitive_congruences hcp hq).2.2
    rcases hcases with ⟨hbn,he⟩ | ⟨hbn,he⟩
    · have hm1 : 1 < m := by
        by_contra hh
        have hm' : m=1 := by omega
        have hunit := unit_first_factor ha hn (by simpa [hm'] using he)
        exact hab (by rw [hunit.1,hbn,hm',hunit.2])
      have h3m : ¬3 ∣ m := three_not_left h3a (Or.inr rfl) he
      obtain ⟨r,s,hr,hs,hrs,hnrs,hnew⟩ := second_descent_stage hn hmn h3m
        (A := 2*a) (by nlinarith [he])
      have hsle : s ≤ n := by rw [hnrs]; nlinarith
      have hnlt : n < b := by rw [hbn]; nlinarith
      have heq := ih s (hsle.trans_lt hnlt) r m hr hs hm hrs hnew
      have hh := diagonal_primitive hrs hnew heq
      omega
    · have h3m : ¬3 ∣ m := three_not_left h3a (Or.inl rfl) (by simpa using he)
      obtain ⟨r,s,hr,hs,hrs,hnrs,hnew⟩ := second_descent_stage hn hmn h3m he
      have hsle : s ≤ n := by rw [hnrs]; nlinarith
      have hnlt : n < b := by rw [hbn]; nlinarith
      have heq := ih s (hsle.trans_lt hnlt) r m hr hs hm hrs hnew
      obtain ⟨hr1,hs1,hm1⟩ := diagonal_primitive hrs hnew heq
      have hn1 : n=1 := by rw [hnrs,hr1,hs1]
      rw [hm1,hn1] at he hbn
      norm_num at he hbn
      nlinarith

lemma numerator_mul_denominator (v : ℚ) : (v.num : ℚ)=v*(v.den : ℚ) := by
  have hd : (v.den : ℚ) ≠ 0 := by exact_mod_cast v.den_ne_zero
  calc
    (v.num : ℚ)=((v.num : ℚ)/(v.den : ℚ))*(v.den : ℚ) := by field_simp
    _=v*(v.den : ℚ) := by rw [Rat.num_div_den]

lemma clear_quartic_denominator {v w : ℚ} (h : w^2=v^4-3*v^2+3) :
    ∃ c : ℕ, Quartic v.num.natAbs v.den c := by
  let z : ℤ := v.num^4-3*v.num^2*(v.den : ℤ)^2+3*(v.den : ℤ)^4
  have hz : IsSquare (z : ℚ) := by
    refine ⟨w*(v.den : ℚ)^2,?_⟩
    dsimp [z]
    push_cast
    rw [numerator_mul_denominator v]
    linear_combination -(v.den : ℚ)^4*h
  obtain ⟨c,hc⟩ := Rat.isSquare_intCast_iff.mp hz
  have hn2 : (v.num.natAbs : ℤ)^2=v.num^2 := Int.natAbs_sq v.num
  have hn4 : (v.num.natAbs : ℤ)^4=v.num^4 := by
    calc
      (v.num.natAbs : ℤ)^4=((v.num.natAbs : ℤ)^2)^2 := by ring
      _=(v.num^2)^2 := by rw [hn2]
      _=v.num^4 := by ring
  have hq : (c.natAbs : ℤ)^2+3*(v.num.natAbs : ℤ)^2*(v.den : ℤ)^2=
      (v.num.natAbs : ℤ)^4+3*(v.den : ℤ)^4 := by
    rw [Int.natAbs_sq c,hn2,hn4]
    dsimp [z] at hc
    nlinarith [hc]
  exact ⟨c.natAbs, by dsimp [Quartic]; exact_mod_cast hq⟩

/-- An elementary rational-point classification for this quartic; no
elliptic-curve rank computation is used in the proof. -/
theorem rational_quartic {v w : ℚ} (h : w^2=v^4-3*v^2+3) : v^2=1 := by
  obtain ⟨c,hq⟩ := clear_quartic_denominator h
  have hcong := primitive_congruences v.reduced hq
  have ha : 0 < v.num.natAbs := by omega
  have hc : 0 < c := by omega
  have he := primitive_quartic v.den v.num.natAbs c ha v.den_pos hc v.reduced hq
  have hm : (v.num.natAbs : ℚ)^2=(v.num : ℚ)^2 := by
    have hh := congrArg (fun z : ℤ => (z : ℚ)) (Int.natAbs_sq v.num)
    simpa only [Int.cast_natCast,Nat.cast_pow,Int.cast_pow] using hh
  have hs : (v.num : ℚ)^2=(v.den : ℚ)^2 := by rw [← hm,he]
  rw [numerator_mul_denominator v,mul_pow] at hs
  have hd : (v.den : ℚ)^2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast v.den_ne_zero)
  exact (mul_right_cancel₀ hd) (by simpa only [one_mul] using hs)

theorem rational_quartic_iff (v : ℚ) :
    IsSquare (v^4-3*v^2+3) ↔ v=1 ∨ v=-1 := by
  constructor
  · rintro ⟨w,hw⟩
    have h := rational_quartic (v := v) (w := w) (by nlinarith [hw])
    exact sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa using h : v^2=(1 : ℚ)^2)
  · rintro (rfl | rfl) <;> norm_num

#print axioms primitive_quartic
#print axioms rational_quartic
#print axioms rational_quartic_iff
end Erdos213.MorleyQuarticDescent
