import FormalConjecturesUtil

/-! Fermat's square-area obstruction. Auxiliary to the norm-template analysis. -/
namespace Erdos213.FermatArea

private lemma square_of_positive_coprime_mul {a b : ℤ} (ha : 0 < a)
    (hab : IsCoprime a b) (hs : IsSquare (a*b)) : ∃ c : ℤ, a=c^2 := by
  obtain ⟨c,hc⟩ := hs
  obtain ⟨d,hd⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hab)
    (show a*b=c^2 by simpa [pow_two] using hc)
  refine ⟨d, hd.resolve_right ?_⟩
  intro he
  nlinarith [sq_nonneg d]

private lemma sum_sub_coprime {m n : ℤ} (hmn : IsCoprime m n)
    (hp : m%2=0 ∧ n%2=1 ∨ m%2=1 ∧ n%2=0) : IsCoprime (m+n) (m-n) := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  by_contra hc
  obtain ⟨p,hp',hpa,hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  have ha : (p : ℤ) ∣ m+n := Int.natCast_dvd.mpr hpa
  have hb : (p : ℤ) ∣ m-n := Int.natCast_dvd.mpr hpb
  have hm : (p : ℤ) ∣ 2*m := by convert dvd_add ha hb using 1 <;> ring
  have hn : (p : ℤ) ∣ 2*n := by convert dvd_sub ha hb using 1 <;> ring
  have hpi : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp')
  have hp2 : p=2 := by
    by_contra hne
    have hn2 : ¬(p : ℤ) ∣ 2 := by
      intro hd
      have hd' : p ∣ 2 := by exact_mod_cast hd
      have hh := (Nat.dvd_prime Nat.prime_two).mp hd'
      rcases hh with hh|hh
      · exact hp'.ne_one hh
      · exact hne hh
    have hpm := (hpi.dvd_mul.mp hm).resolve_left hn2
    have hpn := (hpi.dvd_mul.mp hn).resolve_left hn2
    have hh := hmn.isUnit_of_dvd' hpm hpn
    exact hpi.not_unit hh
  subst p
  have he : (m+n)%2=0 := Int.emod_eq_zero_of_dvd ha
  rcases hp with ⟨hm,hn⟩|⟨hm,hn⟩ <;> simp [Int.add_emod,hm,hn] at he

set_option maxHeartbeats 2000000 in
private lemma primitive_descent {x y z : ℤ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (ht : PythagoreanTriple x y z) (hc : Int.gcd x y=1) (hp : x%2=1)
    (hs : IsSquare (((x : ℚ)*y)/2)) :
    ∃ a b c : ℤ, 0 < a ∧ 0 < b ∧ 0 < c ∧ c < z ∧ PythagoreanTriple a b c ∧
      IsSquare (((a : ℚ)*b)/2) := by
  obtain ⟨m,n,hm,hn,hz',hco,hpar,hm0⟩ := ht.coprime_classification' hc hp hz
  have hmpos : 0 < m := by nlinarith
  have hnpos : 0 < n := by nlinarith
  have hmn : n < m := by nlinarith
  have hcop : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hco
  have hmx : IsCoprime m (m^2-n^2) := by
    apply IsCoprime.of_add_mul_right_right (z := -m)
    convert (hcop.pow_right (n := 2)).neg_right using 1 <;> ring
  have hnx : IsCoprime n (m^2-n^2) := by
    apply IsCoprime.of_add_mul_right_right (z := n)
    convert hcop.symm.pow_right (n := 2) using 1 <;> ring
  have hsint : IsSquare (m*(n*(m^2-n^2))) := by
    apply Rat.isSquare_intCast_iff.mp
    convert hs using 1
    push_cast
    rw [hm,hn]
    push_cast
    ring
  obtain ⟨a,ha⟩ := square_of_positive_coprime_mul hmpos (hcop.mul_right hmx) hsint
  have hnint : IsSquare (n*(m*(m^2-n^2))) := by convert hsint using 1 <;> ring
  obtain ⟨b,hb⟩ := square_of_positive_coprime_mul hnpos (hcop.symm.mul_right hnx) hnint
  have hxint : IsSquare ((m^2-n^2)*(m*n)) := by convert hsint using 1 <;> ring
  obtain ⟨c,hc'⟩ := square_of_positive_coprime_mul (by omega : 0 < m^2-n^2)
    (hmx.symm.mul_right hnx.symm) hxint
  have hpm : 0 < m+n := by omega
  have hpm' : 0 < m-n := by omega
  have hsprod : IsSquare ((m+n)*(m-n)) := ⟨c, by nlinarith [hc']⟩
  have hpco := sum_sub_coprime hcop hpar
  obtain ⟨d,hd⟩ := square_of_positive_coprime_mul hpm hpco hsprod
  obtain ⟨e,he⟩ := square_of_positive_coprime_mul hpm' hpco.symm
    (by simpa [mul_comm] using hsprod)
  let D := |d|
  let E := |e|
  let A := |a|
  have hD : D^2=m+n := by dsimp [D]; simpa using hd.symm
  have hE : E^2=m-n := by dsimp [E]; simpa using he.symm
  have hA : A^2=m := by dsimp [A]; simpa using ha.symm
  have hDpos : 0 < D := by have := abs_nonneg d; dsimp [D] at hD ⊢; nlinarith only [hD, hpm, abs_nonneg d]
  have hEpos : 0 < E := by have := abs_nonneg e; dsimp [E] at hE ⊢; nlinarith only [hE, hpm', abs_nonneg e]
  have hApos : 0 < A := by have := abs_nonneg a; dsimp [A] at hA ⊢; nlinarith only [hA, hmpos, abs_nonneg a]
  have hDE : E < D := by nlinarith only [hD,hE,hnpos,hEpos,hDpos]
  refine ⟨D+E,D-E,2*A,by omega,by omega,by omega,?_,?_,?_⟩
  · have hAle : A ≤ m := by nlinarith only [hA,hApos]
    have hm2 : 2 ≤ m := by omega
    nlinarith only [hAle,hm2,hnpos,hz',sq_nonneg (m-1)]
  · dsimp [PythagoreanTriple]
    nlinarith only [hD,hE,hA]
  · refine ⟨(b : ℚ),?_⟩
    have hD' : (D : ℚ)^2=m+n := by exact_mod_cast hD
    have hE' : (E : ℚ)^2=m-n := by exact_mod_cast hE
    have hb' : (n : ℚ)=(b : ℚ)^2 := by exact_mod_cast hb
    push_cast
    nlinarith only [hD',hE',hb']

private lemma primitive_reduction {x y z : ℤ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (ht : PythagoreanTriple x y z) (hs : IsSquare (((x : ℚ)*y)/2)) :
    ∃ a b c : ℤ, 0 < a ∧ 0 < b ∧ 0 < c ∧ c ≤ z ∧ PythagoreanTriple a b c ∧
      Int.gcd a b=1 ∧ IsSquare (((a : ℚ)*b)/2) := by
  have hg : 0 < Int.gcd x y := by
    apply Nat.pos_of_ne_zero
    intro he
    have hh := Nat.eq_zero_of_gcd_eq_zero_left he
    have hh' := Int.natAbs_eq_zero.mp hh
    omega
  obtain ⟨k,a,b,hk,hcop,hx',hy'⟩ := Int.exists_gcd_one' hg
  have hgk : Int.gcd x y=k := by
    rw [hx',hy',Int.gcd_mul_right,hcop,Int.natAbs_natCast,one_mul]
  obtain ⟨c,hc⟩ := ht.gcd_dvd
  rw [hgk] at hc
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have ha : 0 < a := by nlinarith only [hx',hx,hkZ]
  have hb : 0 < b := by nlinarith only [hy',hy,hkZ]
  have hcpos : 0 < c := by nlinarith only [hc,hz,hkZ]
  have hcle : c ≤ z := by nlinarith only [hc,hcpos,hkZ]
  refine ⟨a,b,c,ha,hb,hcpos,hcle,?_,hcop,?_⟩
  · apply (PythagoreanTriple.mul_iff (k : ℤ) (ne_of_gt hkZ)).mp
    simpa only [hx',hy',hc,mul_comm] using ht
  · obtain ⟨r,hr⟩ := hs
    refine ⟨r/(k : ℚ),?_⟩
    rw [hx',hy'] at hr
    push_cast at hr
    field_simp
    linear_combination 2*hr

lemma no_integer_square_area (N : ℕ) : ∀ x y z : ℤ, z.natAbs=N →
    0 < x → 0 < y → 0 < z → PythagoreanTriple x y z →
    ¬IsSquare (((x : ℚ)*y)/2) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro x y z hN hx hy hz ht hs
    obtain ⟨a,b,c,ha,hb,hc,hcz,ht',hcop,hs'⟩ := primitive_reduction hx hy hz ht hs
    have he : ∃ d e f : ℤ, 0 < d ∧ 0 < e ∧ 0 < f ∧ f < c ∧
        PythagoreanTriple d e f ∧ IsSquare (((d : ℚ)*e)/2) := by
      rcases ht'.even_odd_of_coprime hcop with hp|hp
      · exact primitive_descent hb ha hc ht'.symm (by simpa [Int.gcd_comm] using hcop)
          hp.2 (by simpa [mul_comm] using hs')
      · exact primitive_descent ha hb hc ht' hcop hp.1 hs'
    obtain ⟨d,e,f,hd,he,hf,hfc,hP,hS⟩ := he
    have hlt : f.natAbs < N := by
      rw [← hN]
      apply Int.ofNat_lt.mp
      rw [← Int.eq_natAbs_of_nonneg (le_of_lt hf),← Int.eq_natAbs_of_nonneg (le_of_lt hz)]
      omega
    exact ih f.natAbs hlt d e f rfl hd he hf hP hS

lemma no_rational_square_area {x y z : ℚ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (ht : x^2+y^2=z^2) : ¬IsSquare (x*y/2) := by
  intro hs
  let D : ℤ := x.den*y.den*z.den
  let A : ℤ := x.num*y.den*z.den
  let B : ℤ := y.num*x.den*z.den
  let C : ℤ := z.num*x.den*y.den
  have hD : (0 : ℚ) < D := by dsimp [D]; positivity
  have hnum (q : ℚ) : (q.num : ℚ)=q*q.den := by
    exact (div_eq_iff (by exact_mod_cast q.den_ne_zero)).mp q.num_div_den
  have hxD : (A : ℚ)=x*D := by
    dsimp [A,D]
    push_cast
    rw [hnum x]
    ring
  have hyD : (B : ℚ)=y*D := by
    dsimp [B,D]
    push_cast
    rw [hnum y]
    ring
  have hzD : (C : ℚ)=z*D := by
    dsimp [C,D]
    push_cast
    rw [hnum z]
    ring
  have hA : 0 < A := by exact_mod_cast (show (0 : ℚ)<A by rw [hxD]; positivity)
  have hB : 0 < B := by exact_mod_cast (show (0 : ℚ)<B by rw [hyD]; positivity)
  have hC : 0 < C := by exact_mod_cast (show (0 : ℚ)<C by rw [hzD]; positivity)
  have hP : PythagoreanTriple A B C := by
    change A*A+B*B=C*C
    have hh : (A : ℚ)*A+B*B=C*C := by rw [hxD,hyD,hzD]; linear_combination (D : ℚ)^2*ht
    exact_mod_cast hh
  apply no_integer_square_area C.natAbs A B C rfl hA hB hC hP
  rw [hxD,hyD]
  convert hs.mul (IsSquare.sq (D : ℚ)) using 1 <;> ring

/-- A quartic form of the square-area obstruction. -/
lemma quartic_not_square {t : ℚ} (ht : t≠0) : ¬IsSquare (t^4+6*t^2+1) := by
  rintro ⟨c,hc⟩
  have hc' : c^2=t^4+6*t^2+1 := by nlinarith only [hc]
  have hpos := sq_pos_of_ne_zero ht
  have habs : |c|^2=c^2 := sq_abs c
  have ha : 0 < |c|+(t^2-1) := by nlinarith [abs_nonneg c]
  have hb : 0 < |c|-(t^2-1) := by nlinarith [abs_nonneg c]
  have hz : 0 < 2*(t^2+1) := by positivity
  apply no_rational_square_area ha hb hz
    (show (|c|+(t^2-1))^2+(|c|-(t^2-1))^2=(2*(t^2+1))^2 by
      nlinarith only [hc',habs])
  refine ⟨2*t,?_⟩
  nlinarith only [hc',habs]

#print axioms primitive_descent
#print axioms no_integer_square_area
#print axioms no_rational_square_area
#print axioms quartic_not_square
end Erdos213.FermatArea
