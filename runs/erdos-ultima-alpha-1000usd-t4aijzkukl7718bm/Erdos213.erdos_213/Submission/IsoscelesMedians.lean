import Submission.OrthogonalGlobal

/-! An elementary descent for the conductor-48 simultaneous-square problem.
This auxiliary development does not settle Erdős 213. -/
namespace Erdos213.IsoscelesMedians
open OrthogonalGlobal
set_option maxHeartbeats 3000000

private lemma parity_mod8 : ∀ m n b : ZMod 8,
    b^2=m^2+4*n^2 → m.val%2=1 → n.val%2=0 := by decide

lemma primitive_parity {m n a b : ℕ} (hcp : m.Coprime n)
    (ha : a^2=m^2+3*n^2) (hb : b^2=m^2+4*n^2) :
    m%2=1 ∧ n%2=0 ∧ a%2=1 ∧ b%2=1 := by
  have hmo : m%2=1 := by
    by_contra hn
    have hm : 2 ∣ m := Nat.dvd_of_mod_eq_zero (by omega)
    have hno : n%2=1 := by
      by_contra hn
      have hd : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
      have hh := hcp.gcd_eq_one ▸ Nat.dvd_gcd hm hd
      norm_num at hh
    have hh := congrArg (fun x : ℕ => x%4) ha
    have hm4 : m%4=0 ∨ m%4=2 := by omega
    have hn4 : n%4=1 ∨ n%4=3 := by omega
    have ha4 : a%4<4 := Nat.mod_lt _ (by decide)
    rcases hm4 with h | h <;> rcases hn4 with h' | h' <;>
      interval_cases ha' : a%4 <;> simp [Nat.add_mod,Nat.mul_mod,Nat.pow_mod,h,h',ha'] at hh
  have hb8 : (b : ZMod 8)^2=(m : ZMod 8)^2+4*(n : ZMod 8)^2 := by
    have hh := congrArg (fun z : ℕ => (z : ZMod 8)) hb
    push_cast at hh
    exact hh
  have hm8 : (m : ZMod 8).val%2=1 := by
    simp only [ZMod.val_natCast]
    omega
  have hne : n%2=0 := by
    have hh := parity_mod8 _ _ _ hb8 hm8
    simp only [ZMod.val_natCast] at hh
    omega
  have ha2 := congrArg (fun x : ℕ => x%2) ha
  have hb2 := congrArg (fun x : ℕ => x%2) hb
  simp [square_mod_two,Nat.add_mod,Nat.mul_mod,hmo,hne] at ha2 hb2
  norm_num at ha2 hb2
  exact ⟨hmo,hne,ha2,hb2⟩

lemma hypotenuses_coprime {m n a b : ℕ} (hcp : m.Coprime n)
    (ha : a^2=m^2+3*n^2) (hb : b^2=m^2+4*n^2) : a.Coprime b := by
  by_contra h
  obtain ⟨p,hp,hpa,hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hpn2 : p ∣ n^2 := by
    have hd := Nat.dvd_sub (dvd_pow hpb (by decide : 2≠0)) (dvd_pow hpa (by decide : 2≠0))
    have he : b^2-a^2=n^2 := by omega
    simpa [he] using hd
  have hpn := hp.dvd_of_dvd_pow hpn2
  have hpm2 : p ∣ m^2 := by
    apply (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right hpn2 3)).mpr
    rw [add_comm,← ha]
    exact dvd_pow hpa (by decide : 2≠0)
  have hpm := hp.dvd_of_dvd_pow hpm2
  exact hp.not_dvd_one (hcp.gcd_eq_one ▸ Nat.dvd_gcd hpm hpn)

lemma first_stage {m n a b : ℕ} (hm : 0<m) (hn : 0<n) (hcp : m.Coprime n)
    (ha : a^2=m^2+3*n^2) (hb : b^2=m^2+4*n^2) :
    ∃ r s : ℕ, 0<r ∧ 0<s ∧ r.Coprime s ∧ b=r^2+s^2 ∧
      m^2+14*r^2*s^2=r^4+s^4 := by
  obtain ⟨_,hne,hao,hbo⟩ := primitive_parity hcp ha hb
  obtain ⟨k,hk⟩ : 2 ∣ n := Nat.dvd_of_mod_eq_zero hne
  have hk0 : 0<k := by omega
  obtain ⟨x,y,hx,hy,hxy,hsum,hprod⟩ :=
    half_difference_factors hbo hao (by decide : 0<1) hk0
      (hypotenuses_coprime hcp ha hb).symm (by rw [hk] at ha hb; nlinarith)
  simp only [one_mul] at hprod
  obtain ⟨r,s,hxr,hys,hkrs,hrs⟩ := coprime_square_factors hxy hprod
  have hr : 0<r := by nlinarith
  have hs : 0<s := by nlinarith
  have hbeq : b=r^2+s^2 := by rw [hxr,hys] at hsum; omega
  refine ⟨r,s,hr,hs,hrs,hbeq,?_⟩
  rw [hbeq,hk,hkrs] at hb
  nlinarith [hb]

lemma quartic_factors_coprime {r s : ℕ} (hcp : r.Coprime s)
    (hro : r%2=1) (hse : s%2=0) :
    IsCoprime ((r : ℤ)^2+s^2-4*r*s) ((r : ℤ)^2+s^2+4*r*s) := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  by_contra h
  obtain ⟨p,hp,hpa,hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hpa' := Int.natCast_dvd.mpr hpa
  have hpb' := Int.natCast_dvd.mpr hpb
  have hd : (p : ℤ) ∣ 8*(r : ℤ)*s := by
    convert dvd_sub hpb' hpa' using 1 <;> ring
  rcases Int.Prime.dvd_mul' hp hd with hd | hds
  · rcases Int.Prime.dvd_mul' hp hd with hd8 | hdr
    · have hd8' : p ∣ 2^3 := by exact_mod_cast hd8
      have he : p=2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow hd8')
      subst p
      have hh := Int.emod_eq_zero_of_dvd hpa'
      have hr' : (r : ℤ)%2=1 := by exact_mod_cast hro
      have hs' : (s : ℤ)%2=0 := by exact_mod_cast hse
      norm_num [Int.add_emod,Int.sub_emod,Int.mul_emod,pow_two,hr',hs'] at hh
    · have hds2 : (p : ℤ) ∣ (s : ℤ)^2 := by
        convert dvd_sub hpa' (dvd_mul_of_dvd_right hdr ((r : ℤ)-4*s)) using 1 <;> ring
      have hds := Int.Prime.dvd_pow' hp hds2
      have hh : p ∣ Nat.gcd r s := Nat.dvd_gcd (by exact_mod_cast hdr) (by exact_mod_cast hds)
      exact hp.not_dvd_one (hcp.gcd_eq_one ▸ hh)
  · have hdr2 : (p : ℤ) ∣ (r : ℤ)^2 := by
      convert dvd_sub hpa' (dvd_mul_of_dvd_right hds ((s : ℤ)-4*r)) using 1 <;> ring
    have hdr := Int.Prime.dvd_pow' hp hdr2
    have hh : p ∣ Nat.gcd r s := Nat.dvd_gcd (by exact_mod_cast hdr) (by exact_mod_cast hds)
    exact hp.not_dvd_one (hcp.gcd_eq_one ▸ hh)

lemma quartic_roots {m r s : ℕ} (hm : 0<m) (hr : 0<r) (hs : 0<s)
    (hcp : r.Coprime s) (hro : r%2=1) (hse : s%2=0)
    (he : m^2+14*r^2*s^2=r^4+s^4) :
    ∃ u v : ℕ, 0<u ∧ 0<v ∧ u.Coprime v ∧ u%2=1 ∧ v%2=1 ∧
      u^2+4*r*s=r^2+s^2 ∧ v^2=r^2+s^2+4*r*s := by
  have he' : (m : ℤ)^2+14*(r : ℤ)^2*s^2=(r : ℤ)^4+s^4 := by exact_mod_cast he
  have hf : ((r : ℤ)^2+s^2-4*r*s)*((r : ℤ)^2+s^2+4*r*s)=(m : ℤ)^2 := by nlinarith
  have hc := quartic_factors_coprime hcp hro hse
  obtain ⟨u,hu⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hc) hf
  obtain ⟨v,hv⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hc.symm)
    (by simpa [mul_comm] using hf)
  have hp : 0<(r : ℤ)^2+s^2+4*r*s := by positivity
  have hv' : (r : ℤ)^2+s^2+4*r*s=v^2 := hv.resolve_right (by nlinarith [sq_nonneg v])
  have hu' : (r : ℤ)^2+s^2-4*r*s=u^2 := hu.resolve_right (by
    intro hu
    rw [hu,hv'] at hf
    have hm' : 0<(m : ℤ)^2 := by exact_mod_cast sq_pos_of_pos hm
    nlinarith [sq_nonneg (u*v)])
  have hu0 : u≠0 := by
    intro h
    rw [hu',h] at hf
    have hm' : 0<(m : ℤ) := by exact_mod_cast hm
    nlinarith
  have hv0 : v≠0 := by intro h; rw [hv',h] at hp; norm_num at hp
  have hc' : IsCoprime u v := by
    rw [hu',hv'] at hc
    exact (IsCoprime.pow_iff (by decide : 0<2) (by decide : 0<2)).mp hc
  have huN : u.natAbs^2+4*r*s=r^2+s^2 := by
    have hh : (u.natAbs : ℤ)^2+4*r*s=(r : ℤ)^2+s^2 := by rw [Int.natAbs_sq]; linarith
    exact_mod_cast hh
  have hvN : v.natAbs^2=r^2+s^2+4*r*s := by
    have hh : (v.natAbs : ℤ)^2=(r : ℤ)^2+s^2+4*r*s := by rw [Int.natAbs_sq]; linarith
    exact_mod_cast hh
  have hu2 := congrArg (fun z : ℕ => z%2) huN
  have hv2 := congrArg (fun z : ℕ => z%2) hvN
  simp [Nat.add_mod,Nat.mul_mod,square_mod_two,hro,hse] at hu2 hv2
  norm_num at hu2 hv2
  exact ⟨u.natAbs,v.natAbs,Int.natAbs_pos.mpr hu0,Int.natAbs_pos.mpr hv0,
    Int.isCoprime_iff_gcd_eq_one.mp hc',hu2,hv2,huN,hvN⟩

lemma product_allocation {r s h j : ℕ} (hr : 0<r) (hs : 0<s)
    (hh : 0<h) (hj : 0<j) (hhj : h.Coprime j) (hje : j%2=1)
    (hhe : h%2=0) (hse : s%2=0) (hp : h*j=2*r*s) :
    ∃ a b c d : ℕ, 0<a ∧ 0<b ∧ 0<c ∧ 0<d ∧
      r=a*b ∧ s=c*d ∧ h=2*a*c ∧ j=b*d ∧
      b.Coprime c ∧ a.Coprime d ∧ b%2=1 ∧ c%2=0 ∧ d%2=1 := by
  obtain ⟨H,hH⟩ : 2 ∣ h := Nat.dvd_of_mod_eq_zero hhe
  have hH0 : 0<H := by omega
  let a := Nat.gcd r H
  have ha0 : 0<a := Nat.gcd_pos_of_pos_left H hr
  obtain ⟨b,hb⟩ : a ∣ r := Nat.gcd_dvd_left r H
  obtain ⟨c,hc⟩ : a ∣ H := Nat.gcd_dvd_right r H
  have hb0 : 0<b := by nlinarith [hb]
  have hc0 : 0<c := by nlinarith [hc]
  have hbc : b.Coprime c := by
    have he : Nat.gcd r H=a := rfl
    rw [hb,hc,Nat.gcd_mul_left] at he
    exact Nat.coprime_iff_gcd_eq_one.mpr (by nlinarith)
  have he : c*j=b*s := by rw [hH,hb,hc] at hp; nlinarith
  have hbj : b ∣ j := hbc.dvd_mul_left.mp (by rw [he]; exact dvd_mul_right _ _)
  obtain ⟨d,hd⟩ := hbj
  have hd0 : 0<d := by nlinarith [hd]
  have hsd : s=c*d := by rw [hd] at he; nlinarith
  have hhad : h=2*a*c := by rw [hH,hc]; ring
  have had : a.Coprime d := hhj.of_dvd
    (by rw [hhad]; exact ⟨2*c,by ring⟩) (by rw [hd]; exact dvd_mul_left _ _)
  have hpar := congrArg (fun z : ℕ => z%2) hd
  have hbo : b%2=1 := by
    simp [Nat.mul_mod,hje] at hpar
    have hbm := Nat.mod_two_eq_zero_or_one b
    rcases hbm with hbm | hbm
    · rw [hbm] at hpar; norm_num at hpar
    · exact hbm
  have hdo : d%2=1 := by
    simp [Nat.mul_mod,hje,hbo] at hpar
    omega
  have hce : c%2=0 := by
    have hh := congrArg (fun z : ℕ => z%2) hsd
    simp [Nat.mul_mod,hse,hdo] at hh
    omega
  exact ⟨a,b,c,d,ha0,hb0,hc0,hd0,hb,hsd,hhad,hd,hbc,had,hbo,hce,hdo⟩

private lemma odd_even_squares_mod8 : ∀ b c d : ZMod 8,
    b.val%2=1 → c.val%2=0 → d.val%2=1 → b^2-4*c^2=1 ∧ d^2=1 := by decide

lemma square_class_one {a b c d : ℕ} (ha : 0<a) (hbc : b.Coprime c)
    (had : a.Coprime d) (hbo : b%2=1) (hce : c%2=0) (hdo : d%2=1)
    (he : 4*a^2*c^2+b^2*d^2=a^2*b^2+c^2*d^2) :
    a^2+c^2=b^2 ∧ d^2+4*c^2=b^2 := by
  have he' : (a : ℤ)^2*((b : ℤ)^2-4*c^2)=(d : ℤ)^2*((b : ℤ)^2-c^2) := by
    have hh : 4*(a : ℤ)^2*c^2+(b : ℤ)^2*d^2=(a : ℤ)^2*b^2+(c : ℤ)^2*d^2 := by exact_mod_cast he
    nlinarith
  have had' : IsCoprime (a : ℤ) (d : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast had)
  have hdF : (a : ℤ)^2 ∣ (b : ℤ)^2-c^2 :=
    (show IsCoprime ((a : ℤ)^2) ((d : ℤ)^2) from had'.pow).dvd_of_dvd_mul_left (by rw [← he']; exact dvd_mul_right _ _)
  obtain ⟨e,heF⟩ := hdF
  have heG : (b : ℤ)^2-4*c^2=(d : ℤ)^2*e := by
    rw [heF] at he'
    have ha' : 0<(a : ℤ) := by exact_mod_cast ha
    nlinarith only [he',sq_pos_of_pos ha']
  have hbc' : IsCoprime (b : ℤ) (c : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast hbc)
  have hFc : IsCoprime ((b : ℤ)^2-c^2) ((c : ℤ)^2) := by
    simpa only [mul_neg_one,sub_eq_add_neg] using (show IsCoprime ((b : ℤ)^2) ((c : ℤ)^2) from hbc'.pow).add_mul_left_left (-1)
  have hec : IsCoprime e ((c : ℤ)^2) := hFc.of_isCoprime_of_dvd_left
    (by rw [heF]; exact dvd_mul_left _ _)
  have he3c : e ∣ 3*(c : ℤ)^2 := by
    convert dvd_sub (show e ∣ (b : ℤ)^2-c^2 by rw [heF]; exact dvd_mul_left _ _)
      (show e ∣ (b : ℤ)^2-4*c^2 by rw [heG]; exact dvd_mul_left _ _) using 1 <;> ring
  have he3 : e ∣ 3 := hec.dvd_of_dvd_mul_right he3c
  have hbits := odd_even_squares_mod8 (b : ZMod 8) (c : ZMod 8) (d : ZMod 8)
    (by simp only [ZMod.val_natCast]; omega)
    (by simp only [ZMod.val_natCast]; omega)
    (by simp only [ZMod.val_natCast]; omega)
  have he8 := congrArg (fun z : ℤ => (z : ZMod 8)) heG
  push_cast at he8
  rw [hbits.1,hbits.2,one_mul] at he8
  have hemod : e%8=1 := by
    have hh := (ZMod.intCast_eq_intCast_iff' e 1 8).mp (by simpa using he8.symm)
    simpa using hh
  have hle : e≤3 := Int.le_of_dvd (by norm_num : (0 : ℤ)<3) he3
  have hge : -e≤3 := Int.le_of_dvd (by norm_num : (0 : ℤ)<3) (neg_dvd.mpr he3)
  have he1 : e=1 := by omega
  rw [he1,mul_one] at heF heG
  constructor
  · have hh : (a : ℤ)^2+(c : ℤ)^2=(b : ℤ)^2 := by linarith
    exact_mod_cast hh
  · have hh : (d : ℤ)^2+4*(c : ℤ)^2=(b : ℤ)^2 := by linarith
    exact_mod_cast hh

lemma quartic_descent {m r s : ℕ} (hm : 0<m) (hr : 0<r) (hs : 0<s)
    (hcp : r.Coprime s) (hro : r%2=1) (hse : s%2=0)
    (he : m^2+14*r^2*s^2=r^4+s^4) :
    ∃ m' n' a' b' : ℕ, 0<m' ∧ 0<n' ∧ m'.Coprime n' ∧
      a'^2=m'^2+3*n'^2 ∧ b'^2=m'^2+4*n'^2 ∧ b'<r^2+s^2 := by
  obtain ⟨u,v,hu,hv,huv,huo,hvo,hu2,hv2⟩ := quartic_roots hm hr hs hcp hro hse he
  obtain ⟨x,y,hx,hy,hxy,hsum,hprod⟩ :=
    half_difference_factors hvo huo (show 0<2*r*s by positivity) (by decide : 0<1)
      huv.symm (by nlinarith)
  norm_num at hprod
  have hnorm : x^2+y^2=r^2+s^2 := by rw [← hsum] at hv2; nlinarith
  have haux : ∀ h j : ℕ, 0<h → 0<j → h.Coprime j → h%2=0 → j%2=1 →
      h*j=2*r*s → h^2+j^2=r^2+s^2 →
      ∃ m' n' a' b' : ℕ, 0<m' ∧ 0<n' ∧ m'.Coprime n' ∧
        a'^2=m'^2+3*n'^2 ∧ b'^2=m'^2+4*n'^2 ∧ b'<r^2+s^2 := by
    intro h j hh hj hhj hhe hjo hprod hnorm
    obtain ⟨a,b,c,d,ha,hb,hc,hd,hrab,hscd,hhac,hjbd,hbc,had,hbo,hce,hdo⟩ :=
      product_allocation hr hs hh hj hhj hjo hhe hse hprod
    have hde : 4*a^2*c^2+b^2*d^2=a^2*b^2+c^2*d^2 := by
      rw [hhac,hjbd,hrab,hscd] at hnorm
      nlinarith only [hnorm]
    obtain ⟨habc,hdbc⟩ := square_class_one ha hbc had hbo hce hdo hde
    have hdc : d.Coprime c := (hhj.of_dvd
      (show c ∣ h by rw [hhac]; exact dvd_mul_left _ _)
      (show d ∣ j by rw [hjbd]; exact dvd_mul_left _ _)).symm
    have hble : b≤r := by rw [hrab]; exact Nat.le_mul_of_pos_left b ha
    refine ⟨d,c,a,b,hd,hc,hdc,by nlinarith,by nlinarith,?_⟩
    nlinarith
  have hpar := congrArg (fun z : ℕ => z%2) hsum
  simp [Nat.add_mod,hvo] at hpar
  rcases Nat.mod_two_eq_zero_or_one x with hxe | hxo
  · exact haux x y hx hy hxy hxe (by omega) hprod hnorm
  · exact haux y x hy hx hxy.symm (by omega) hxo
      (by nlinarith only [hprod]) (by nlinarith only [hnorm])

/-- The descent decreases the final hypotenuse, not an unproved elliptic
height. No rank computation is used. -/
theorem no_primitive_solution (b : ℕ) : ∀ m n a : ℕ,
    0<m → 0<n → m.Coprime n → a^2=m^2+3*n^2 → b^2=m^2+4*n^2 → False := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro m n a hm hn hcp ha hb
    obtain ⟨r,s,hr,hs,hrs,hbeq,hquartic⟩ := first_stage hm hn hcp ha hb
    obtain ⟨_,_,_,hbo⟩ := primitive_parity hcp ha hb
    have hpar := congrArg (fun z : ℕ => z%2) hbeq
    simp [Nat.add_mod,square_mod_two,hbo] at hpar
    have haux : ∀ r s : ℕ, 0<r → 0<s → r.Coprime s → r%2=1 → s%2=0 →
        b=r^2+s^2 → m^2+14*r^2*s^2=r^4+s^4 → False := by
      intro r s hr hs hrs hro hse hbeq hq
      obtain ⟨m',n',a',b',hm',hn',hcp',ha',hb',hlt⟩ := quartic_descent hm hr hs hrs hro hse hq
      exact ih b' (hbeq ▸ hlt) m' n' a' hm' hn' hcp' ha' hb'
    rcases Nat.mod_two_eq_zero_or_one r with hre | hro
    · exact haux s r hs hr hrs.symm (by omega) hre
        (by nlinarith only [hbeq]) (by nlinarith only [hquartic])
    · exact haux r s hr hs hrs hro (by omega) hbeq hquartic

/-- No rational number has both its square plus 3 and its square plus 4 square. -/
theorem no_three_four (x : ℚ) : ¬(IsSquare (x^2+3) ∧ IsSquare (x^2+4)) := by
  rintro ⟨h3,h4⟩
  by_cases hx : x=0
  · rw [hx] at h3
    norm_num at h3
  · obtain ⟨a,ha⟩ := clear_square_denominator (u := x) (k := 3) h3
    obtain ⟨b,hb⟩ := clear_square_denominator (u := x) (k := 4) h4
    exact no_primitive_solution b x.num.natAbs x.den a
      (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hx)) x.den_pos x.reduced
      (by simpa only [pow_two] using ha.symm) (by simpa only [pow_two] using hb.symm)

#print axioms no_primitive_solution
#print axioms no_three_four
end Erdos213.IsoscelesMedians
