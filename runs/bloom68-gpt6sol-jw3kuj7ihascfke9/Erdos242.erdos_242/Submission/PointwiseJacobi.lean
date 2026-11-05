import Submission.SquareFactorObstruction

/-!
# A Jacobi transfer between a hard numerator and a Type-I first denominator

For `p ≡ 1 (mod 8)`, `a = 4x-p > 0`, every divisor `c | x²` has the SAME
Jacobi character at `a` and `p`. This is a pointwise necessary condition for
Type I, not a way to construct a witness.
-/
namespace Erdos242

/-- Local prime-factor transfer. Even primes are included: `2|x` forces
`a ≡ 7 (mod 8)` and `p ≡ 1 (mod 8)`, so both symbols at `2` equal `1`. -/
private theorem jacobi_prime_factor_transfer (p a x ell : ℕ)
    (hp8 : p % 8 = 1) (ha3 : a % 4 = 3) (hax : a + p = 4 * x)
    (hp : ell.Prime) (hellx : ell ∣ x) :
    jacobiSym (ell : ℤ) a = jacobiSym (ell : ℤ) p := by
  rcases hp.eq_two_or_odd' with heq | hellodd
  · subst ell
    have ha8 : a % 8 = 7 := by
      obtain ⟨u, hu⟩ := hellx
      rw [hu] at hax
      omega
    have haodd : Odd a := Nat.odd_iff.mpr (by omega)
    have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
    change jacobiSym 2 a = jacobiSym 2 p
    rw [jacobiSym.at_two haodd, jacobiSym.at_two hpodd,
      ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₈_nat_eq_if_mod_eight]
    have ha2 : a % 2 = 1 := Nat.odd_iff.mp haodd
    have hp2 : p % 2 = 1 := Nat.odd_iff.mp hpodd
    simp [ha2, hp2, ha8, hp8]
  · have haxZ : (a : ℤ) + (p : ℤ) = 4 * (x : ℤ) := by exact_mod_cast hax
    obtain ⟨u, hu⟩ := hellx
    have hux : (x : ℤ) = (ell : ℤ) * (u : ℤ) := by exact_mod_cast hu
    have hmod : (a : ℤ) % ell = (-(p : ℤ)) % ell := by
      calc
        (a : ℤ) % ell = ((a : ℤ) + (p : ℤ) - (p : ℤ)) % ell := by simp
        _ = ((4 : ℤ) * (x : ℤ) - (p : ℤ)) % ell := by rw [haxZ]
        _ = ((ell : ℤ) * (4 * (u : ℤ)) + (-(p : ℤ))) % ell := by
          rw [hux]
          ring_nf
        _ = (-(p : ℤ)) % ell := by simp [Int.add_emod]
    have hJa : jacobiSym (a : ℤ) ell =
        jacobiSym (-1) ell * jacobiSym (p : ℤ) ell := by
      calc
        jacobiSym (a : ℤ) ell = jacobiSym (-(p : ℤ)) ell :=
          jacobiSym.mod_left' hmod
        _ = jacobiSym ((-1 : ℤ) * (p : ℤ)) ell := by simp
        _ = _ := jacobiSym.mul_left _ _ _
    have hp4 : p % 4 = 1 := by omega
    have hprec : jacobiSym (p : ℤ) ell = jacobiSym (ell : ℤ) p :=
      jacobiSym.quadratic_reciprocity_one_mod_four hp4 hellodd
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hellodd) with heq1 | heq3
    · have hrec : jacobiSym (ell : ℤ) a = jacobiSym (a : ℤ) ell :=
        jacobiSym.quadratic_reciprocity_one_mod_four heq1 (Nat.odd_iff.mpr (by omega))
      rw [hrec, hJa, jacobiSym.at_neg_one hellodd,
        ZMod.χ₄_nat_one_mod_four heq1, one_mul, hprec]
    · have hrec : jacobiSym (ell : ℤ) a = -jacobiSym (a : ℤ) ell :=
        jacobiSym.quadratic_reciprocity_three_mod_four heq3 ha3
      rw [hrec, hJa, jacobiSym.at_neg_one hellodd,
        ZMod.χ₄_nat_three_mod_four heq3, hprec]
      ring

/-- **Every** divisor `c | x²` (not just `c | x`) has equal Jacobi
symbols modulo `a` and `p` when `p ≡ 1 mod 8` and `a+p=4x`.
This does not require primality or coprimality of any of `a,p,x,c`. -/
theorem jacobi_divisor_transfer (p a x c : ℕ)
    (hp8 : p % 8 = 1) (ha3 : a % 4 = 3) (hax : a + p = 4 * x)
    (hcdvd : c ∣ x ^ 2) :
    jacobiSym (c : ℤ) a = jacobiSym (c : ℤ) p := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    by_cases hc1 : c = 1
    · subst c
      simp
    · obtain ⟨ell, hp, hellc⟩ := Nat.exists_prime_and_dvd hc1
      have hellc' : ell ∣ c := hellc
      obtain ⟨c', hc'⟩ := hellc
      have hccpos : 0 < c := by
        have hxpos : 0 < x := by omega
        exact Nat.pos_of_dvd_of_pos hcdvd (by positivity)
      have hcp : 0 < c' := by
        rw [hc'] at hccpos
        by_contra hn
        have hc'0 : c' = 0 := by omega
        simp [hc'0] at hccpos
      have hc'lt : c' < c := by
        rw [hc']
        have hp2 : 1 < ell := hp.one_lt
        nlinarith
      have hcdvd' : c' ∣ x ^ 2 :=
        dvd_trans (by rw [hc']; exact dvd_mul_left _ _) hcdvd
      have hellx : ell ∣ x := hp.dvd_of_dvd_pow (dvd_trans hellc' hcdvd)
      have hJell := jacobi_prime_factor_transfer p a x ell hp8 ha3 hax hp hellx
      have hJc' := ih c' hc'lt hcdvd'
      rw [hc', Nat.cast_mul, jacobiSym.mul_left, jacobiSym.mul_left, hJell, hJc']

/-- An actual Type-I cofactor for any `p≡1 (mod 8)` MUST be a Jacobi
nonresidue modulo `p` (even when `p` is composite), with no extra `c|x`
restriction. This is a necessary condition, not a pointwise existence proof. -/
theorem typeI_cofactor_jacobi_neg_one (p x c : ℕ) (hp8 : p % 8 = 1)
    (hlo : p < 4 * x) (hcdvd : c ∣ x ^ 2)
    (hac : (4 * x - p) ∣ 4 * c + 1) :
    jacobiSym (c : ℤ) p = -1 := by
  let a := 4 * x - p
  have ha3 : a % 4 = 3 := by dsimp [a]; omega
  have hax : a + p = 4 * x := by dsimp [a]; omega
  have htrans := jacobi_divisor_transfer p a x c hp8 ha3 hax hcdvd
  have haodd : Odd a := Nat.odd_iff.mpr (by omega)
  have hcop2 : (2 : ℤ).gcd a = 1 := by
    have hn : Nat.Coprime 2 a := Nat.coprime_two_left.mpr haodd
    simpa only [Int.gcd_natCast_natCast] using hn.gcd_eq_one
  have hJfour : jacobiSym ((4 : ℤ) * (c : ℤ)) a = jacobiSym (c : ℤ) a := by
    calc
      jacobiSym ((4 : ℤ) * (c : ℤ)) a =
          jacobiSym (((2 : ℤ) ^ 2) * (c : ℤ)) a := by norm_num
      _ = jacobiSym ((2 : ℤ) ^ 2) a * jacobiSym (c : ℤ) a :=
        jacobiSym.mul_left _ _ _
      _ = jacobiSym (c : ℤ) a := by rw [jacobiSym.sq_one' hcop2, one_mul]
  obtain ⟨u, hu⟩ := hac
  have hsumZ : (4 : ℤ) * (c : ℤ) + 1 = (a : ℤ) * (u : ℤ) := by exact_mod_cast hu
  have hmod : ((4 : ℤ) * (c : ℤ)) % a = (-1 : ℤ) % a := by
    calc
      ((4 : ℤ) * (c : ℤ)) % a =
          (((4 : ℤ) * (c : ℤ) + 1) - 1) % a := by simp
      _ = ((a : ℤ) * (u : ℤ) - 1) % a := by rw [hsumZ]
      _ = ((a : ℤ) * (u : ℤ) + (-1 : ℤ)) % a := by simp only [sub_eq_add_neg]
      _ = (-1 : ℤ) % a := by simp [Int.add_emod]
  have hJneg : jacobiSym (-1) a = -1 := by
    rw [jacobiSym.at_neg_one haodd, ZMod.χ₄_nat_three_mod_four ha3]
  have hcong := jacobiSym.mod_left' hmod
  rw [hJfour, hJneg] at hcong
  exact htrans.symm.trans hcong


/-- Extract an actual prime factor of the numerator witnessing a negative
Jacobi symbol. Applied to `c∣x²`, that prime also divides `x`. -/
private theorem jacobi_neg_one_has_prime_factor (p c : ℕ) (hc : 0 < c)
    (hJ : jacobiSym (c : ℤ) p = -1) :
    ∃ ell : ℕ, ell.Prime ∧ ell ∣ c ∧ jacobiSym (ell : ℤ) p = -1 := by
  let l := c.primeFactorsList
  have hval : (l.map (Nat.cast : ℕ → ℤ)).prod = (c : ℤ) := by
    rw [← Nat.cast_list_prod, Nat.prod_primeFactorsList (by omega)]
  have hJ' : jacobiSym (l.map (Nat.cast : ℕ → ℤ)).prod p = -1 := by
    rw [hval]
    exact hJ
  rw [jacobiSym.list_prod_left] at hJ'
  have hprod : (l.map (fun ell : ℕ => jacobiSym (ell : ℤ) p)).prod = -1 := by
    simpa [List.map_map, Function.comp_def] using hJ'
  obtain ⟨ell, hmem, hneg⟩ := List.mem_map.mp
    (List.neg_one_mem_of_prod_eq_neg_one hprod)
  exact ⟨ell, Nat.prime_of_mem_primeFactorsList hmem,
    Nat.dvd_of_mem_primeFactorsList hmem, hneg⟩

/-- A **full** Type-I certificate at `p≡1 (mod 8)` needs an odd prime
factor `ell|x` which is a Jacobi nonresidue modulo `p`. Neither this nor
the auxiliary-factor nonresidue criterion produces a Type-I witness. -/
theorem typeI_has_odd_prime_nonresidue (p x : ℕ) (hp8 : p % 8 = 1)
    (hlo : p < 4 * x) (hI : TypeI p x) :
    ∃ ell : ℕ, ell.Prime ∧ Odd ell ∧ ell ∣ x ∧
      jacobiSym (ell : ℤ) p = -1 := by
  obtain ⟨c, hc, hcdvd, hac⟩ := hI
  have hJc := typeI_cofactor_jacobi_neg_one p x c hp8 hlo hcdvd hac
  obtain ⟨ell, hp, hellc, hJell⟩ := jacobi_neg_one_has_prime_factor p c hc hJc
  have hellx : ell ∣ x := hp.dvd_of_dvd_pow (dvd_trans hellc hcdvd)
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have h2J : jacobiSym (2 : ℤ) p = 1 := by
    rw [jacobiSym.at_two hpodd, ZMod.χ₈_nat_eq_if_mod_eight]
    have hp2 : p % 2 = 1 := Nat.odd_iff.mp hpodd
    simp [hp2, hp8]
  have hellodd : Odd ell := by
    rcases hp.eq_two_or_odd' with heq | hodd
    · subst ell
      change jacobiSym 2 p = -1 at hJell
      rw [h2J] at hJell
      norm_num at hJell
    · exact hodd
  exact ⟨ell, hp, hellodd, hellx, hJell⟩

/-- If `p=s²≡1 (mod 8)`, full Type I is impossible: its mandatory
cofactor character `−1` cannot be a Jacobi symbol modulo a square.
This is about composite squares and says NOTHING about Type II. -/
theorem odd_square_no_full_typeI (s x : ℕ) (hsodd : Odd s) :
    ¬TypeI (s ^ 2) x := by
  intro hI
  by_cases hlo : s ^ 2 < 4 * x
  · have hp8 : s ^ 2 % 8 = 1 := by
      have h8 := Nat.pow_mod s 2 8
      have hmod : s % 8 = 1 ∨ s % 8 = 3 ∨ s % 8 = 5 ∨ s % 8 = 7 := by
        have hs2 := Nat.odd_iff.mp hsodd
        omega
      rcases hmod with h | h | h | h <;> simp [h8, h]
    obtain ⟨c, hc, hcdvd, hac⟩ := hI
    have hJ := typeI_cofactor_jacobi_neg_one (s ^ 2) x c hp8 hlo hcdvd hac
    have hJpow : jacobiSym (c : ℤ) (s ^ 2) = jacobiSym (c : ℤ) s ^ 2 :=
      jacobiSym.pow_right _ _ _
    rw [hJpow] at hJ
    rcases jacobiSym.trichotomy (c : ℤ) s with h | h | h <;> rw [h] at hJ <;> norm_num at hJ
  · obtain ⟨c, hc, hcdvd, hac⟩ := hI
    have hzero : 4 * x - s ^ 2 = 0 := by omega
    rw [hzero] at hac
    obtain ⟨u, hu⟩ := hac
    simp at hu

/-- In fact **no natural square numerator at all** can satisfy the Type-I
divisor criterion. For odd squares use Jacobi transfer; for even squares,
`4x-s²` is divisible by four and cannot divide `4c+1`. These are
local statements only: Type II can solve square numerators. -/
theorem square_no_typeI_anywhere (s x : ℕ) : ¬TypeI (s ^ 2) x := by
  by_cases hsodd : Odd s
  · exact odd_square_no_full_typeI s x hsodd
  · have hsmod2 : s % 2 = 0 := by
      have hcases : s % 2 = 0 ∨ s % 2 = 1 := by omega
      rcases hcases with h | h
      · exact h
      · exact False.elim (hsodd (Nat.odd_iff.mpr h))
    have hsmod4 : s ^ 2 % 4 = 0 := by
      have hcases : s % 4 = 0 ∨ s % 4 = 2 := by omega
      rcases hcases with h | h <;> simp [Nat.pow_mod, h]
    rintro ⟨c, hc, hcdvd, hac⟩
    have ha4 : (4 * x - s ^ 2) % 4 = 0 := by omega
    have hdiv4 : 4 ∣ 4 * c + 1 :=
      dvd_trans (Nat.dvd_of_mod_eq_zero ha4) hac
    have hcontr := Nat.mod_eq_zero_of_dvd hdiv4
    omega

/-- A square hard input `s²=24k+1` fails **every full Type-I predicate**,
without requiring an ordered first denominator. It can still have Type-II
ordered solutions, e.g. `p=25,x=10,d=5`. -/
theorem square_no_full_typeI (k s x : ℕ) (hsq : s ^ 2 = 24 * k + 1) :
    ¬TypeI (24 * k + 1) x := by
  rw [← hsq]
  exact square_no_typeI_anywhere s x

/-- Concrete square with a Type-II certificate and an ordered solution,
illustrating why the square Type-I obstruction is not an ESC counterexample. -/
theorem square_25_typeII : TypeII 25 10 := by
  refine ⟨5, by norm_num, by norm_num, ⟨20, by norm_num⟩, by norm_num⟩

theorem square_25_good : Good 25 := by
  refine ⟨10, 20, 100, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num


/-- The *other* exact divisor criterion interacts with the same transfer:
for `p≡1 (mod 8)`, `d|x²` and `4x-p|x+d` imply
`J(d|p) = -J(x|p)`. The identity also holds if either side is zero. -/
theorem typeII_divisor_jacobi_opposite (p x d : ℕ) (hp8 : p % 8 = 1)
    (hlo : p < 4 * x) (hdsq : d ∣ x ^ 2)
    (hadiv : (4 * x - p) ∣ x + d) :
    jacobiSym (d : ℤ) p = -jacobiSym (x : ℤ) p := by
  let a := 4 * x - p
  have ha3 : a % 4 = 3 := by dsimp [a]; omega
  have hax : a + p = 4 * x := by dsimp [a]; omega
  have hdtrans := jacobi_divisor_transfer p a x d hp8 ha3 hax hdsq
  have hxdiv : x ∣ x ^ 2 := ⟨x, by ring⟩
  have hxtrans := jacobi_divisor_transfer p a x x hp8 ha3 hax hxdiv
  have haodd : Odd a := Nat.odd_iff.mpr (by omega)
  have hJneg : jacobiSym (-1) a = -1 := by
    rw [jacobiSym.at_neg_one haodd, ZMod.χ₄_nat_three_mod_four ha3]
  obtain ⟨u, hu⟩ := hadiv
  have hsumZ : (x : ℤ) + (d : ℤ) = (a : ℤ) * (u : ℤ) := by exact_mod_cast hu
  have hmod : (d : ℤ) % a = (-(x : ℤ)) % a := by
    calc
      (d : ℤ) % a = ((x : ℤ) + (d : ℤ) - (x : ℤ)) % a := by congr 1; ring
      _ = ((a : ℤ) * (u : ℤ) - (x : ℤ)) % a := by rw [hsumZ]
      _ = ((a : ℤ) * (u : ℤ) + (-(x : ℤ))) % a := by simp only [sub_eq_add_neg]
      _ = (-(x : ℤ)) % a := by simp [Int.add_emod]
  have hJd : jacobiSym (d : ℤ) a = -jacobiSym (x : ℤ) a := by
    calc
      jacobiSym (d : ℤ) a = jacobiSym (-(x : ℤ)) a := jacobiSym.mod_left' hmod
      _ = jacobiSym ((-1 : ℤ) * (x : ℤ)) a := by simp
      _ = jacobiSym (-1) a * jacobiSym (x : ℤ) a := jacobiSym.mul_left _ _ _
      _ = -jacobiSym (x : ℤ) a := by rw [hJneg]; ring
  calc
    jacobiSym (d : ℤ) p = jacobiSym (d : ℤ) a := hdtrans.symm
    _ = -jacobiSym (x : ℤ) a := hJd
    _ = -jacobiSym (x : ℤ) p := by rw [hxtrans]

/-- At a prime numerator `p≡1 (mod 8)`, Type II ALSO requires some odd
prime factor of the first denominator `x` to be a nonresidue modulo `p`.
This uses `0<x<p` to avoid the `J(x|p)=0` case; composite squares such as
`p=25` do admit Type II. -/
theorem typeII_has_odd_prime_nonresidue (p x : ℕ)
    (hpp : p.Prime) (hp8 : p % 8 = 1) (hlo : p < 4 * x)
    (hhi : x < p) (hII : TypeII p x) :
    ∃ ell : ℕ, ell.Prime ∧ Odd ell ∧ ell ∣ x ∧
      jacobiSym (ell : ℤ) p = -1 := by
  obtain ⟨d, hd, hdx, hdsq, hadiv⟩ := hII
  have hJopp := typeII_divisor_jacobi_opposite p x d hp8 hlo hdsq hadiv
  have hxpos : 0 < x := lt_trans hd hdx
  have hcop : x.Coprime p := (hpp.coprime_iff_not_dvd.mpr (by
    intro hpx
    have hple := Nat.le_of_dvd hxpos hpx
    omega)).symm
  have hcopZ : (x : ℤ).gcd p = 1 := by
    simpa only [Int.gcd_natCast_natCast] using hcop.gcd_eq_one
  obtain ⟨c, hc, hcdvd, hJc⟩ : ∃ c : ℕ, 0 < c ∧ c ∣ x ^ 2 ∧
      jacobiSym (c : ℤ) p = -1 := by
    rcases jacobiSym.eq_one_or_neg_one hcopZ with hx1 | hxneg
    · refine ⟨d, hd, hdsq, ?_⟩
      rw [hx1] at hJopp
      simpa using hJopp
    · exact ⟨x, hxpos, ⟨x, by ring⟩, hxneg⟩
  obtain ⟨ell, hpell, hellc, hJell⟩ := jacobi_neg_one_has_prime_factor p c hc hJc
  have hellx : ell ∣ x := hpell.dvd_of_dvd_pow (dvd_trans hellc hcdvd)
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have h2J : jacobiSym (2 : ℤ) p = 1 := by
    rw [jacobiSym.at_two hpodd, ZMod.χ₈_nat_eq_if_mod_eight]
    have hp2 : p % 2 = 1 := Nat.odd_iff.mp hpodd
    simp [hp2, hp8]
  have hellodd : Odd ell := by
    rcases hpell.eq_two_or_odd' with heq | hodd
    · subst ell
      change jacobiSym 2 p = -1 at hJell
      rw [h2J] at hJell
      norm_num at hJell
    · exact hodd
  exact ⟨ell, hpell, hellodd, hellx, hJell⟩

/-- A single **local** sieve for both full Type-I and full Type-II:
if all prime factors of a candidate `x` are residues modulo a hard prime
`p`, neither divisor condition can hold *at this x*. It says nothing about
other `x` in the full candidate interval, so it is not an ESC proof. -/
theorem no_types_if_prime_factors_residue (p x : ℕ)
    (hpp : p.Prime) (hp8 : p % 8 = 1) (hlo : p < 4 * x)
    (hhi : x < p)
    (hres : ∀ ell : ℕ, ell.Prime → ell ∣ x → jacobiSym (ell : ℤ) p = 1) :
    ¬TypeI p x ∧ ¬TypeII p x := by
  constructor
  · intro hI
    obtain ⟨ell, hpell, hodd, hellx, hJell⟩ :=
      typeI_has_odd_prime_nonresidue p x hp8 hlo hI
    have hJplus := hres ell hpell hellx
    omega
  · intro hII
    obtain ⟨ell, hpell, hodd, hellx, hJell⟩ :=
      typeII_has_odd_prime_nonresidue p x hpp hp8 hlo hhi hII
    have hJplus := hres ell hpell hellx
    omega


/-- A **single-fiber** failure for both full divisor criteria at a certified
hard prime: `p=66529`, `x=16650=2·3²·5²·37`. Every prime factor of
`x` has positive Jacobi symbol modulo `p`, even though `x²` has 225
divisors. This does not rule out other first denominators for this prime. -/
theorem no_types_66529_at_16650 :
    ¬TypeI 66529 16650 ∧ ¬TypeII 66529 16650 := by
  apply no_types_if_prime_factors_residue 66529 16650
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro ell hpell hellx
  have hfactor : (16650 : ℕ) = 2 * (3 ^ 2 * (5 ^ 2 * 37)) := by norm_num
  rw [hfactor] at hellx
  rcases (hpell.dvd_mul).mp hellx with h2 | hrest
  · have heq : ell = 2 :=
      ((Nat.Prime.dvd_iff_eq (by norm_num : Nat.Prime 2) hpell.ne_one).mp h2).symm
    subst ell
    norm_num
  rcases (hpell.dvd_mul).mp hrest with h3 | hrest
  · have heq : ell = 3 :=
      ((Nat.Prime.dvd_iff_eq (by norm_num : Nat.Prime 3) hpell.ne_one).mp
        (hpell.dvd_of_dvd_pow h3)).symm
    subst ell
    norm_num
  rcases (hpell.dvd_mul).mp hrest with h5 | h37
  · have heq : ell = 5 :=
      ((Nat.Prime.dvd_iff_eq (by norm_num : Nat.Prime 5) hpell.ne_one).mp
        (hpell.dvd_of_dvd_pow h5)).symm
    subst ell
    norm_num
  · have heq : ell = 37 :=
      ((Nat.Prime.dvd_iff_eq (by norm_num : Nat.Prime 37) hpell.ne_one).mp h37).symm
    subst ell
    norm_num


/-- The same prime has a different, strictly ordered solution; failure at
`x=16650` is emphatically not a prime counterexample. -/
theorem good_66529_via_different_x : Good 66529 := by
  refine ⟨17060, 665290, 226996948,
    by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num


/-- For any hard numerator, the prime `3` (and also `2`) has positive
Jacobi symbol; therefore a negative-character prime factor must be `≥5`.
This is a necessary sieve, never a sufficient divisor criterion. -/
theorem hard_three_jacobi_one (k : ℕ) :
    jacobiSym (3 : ℤ) (24 * k + 1) = 1 := by
  have hcast : (((24 * k + 1 : ℕ) : ℤ)) = 3 * (8 * (k : ℤ)) + 1 := by
    push_cast
    ring
  have hmod : (((24 * k + 1 : ℕ) : ℤ)) % 3 = (1 : ℤ) % 3 := by
    rw [hcast]
    simp [Int.add_emod]
  have hJp3 : jacobiSym (((24 * k + 1 : ℕ) : ℤ)) 3 = 1 := by
    calc
      jacobiSym (((24 * k + 1 : ℕ) : ℤ)) 3 = jacobiSym (1 : ℤ) 3 :=
        jacobiSym.mod_left' hmod
      _ = 1 := by simp
  have hrec : jacobiSym (((24 * k + 1 : ℕ) : ℤ)) 3 =
      jacobiSym (3 : ℤ) (24 * k + 1) :=
    jacobiSym.quadratic_reciprocity_one_mod_four (by omega) (by decide)
  exact hrec.symm.trans hJp3

theorem hard_negative_prime_at_least_five (k ell : ℕ) (hpell : ell.Prime)
    (hneg : jacobiSym (ell : ℤ) (24 * k + 1) = -1) : 5 ≤ ell := by
  have h2J : jacobiSym (2 : ℤ) (24 * k + 1) = 1 := by
    have hpodd : Odd (24 * k + 1) := Nat.odd_iff.mpr (by omega)
    rw [jacobiSym.at_two hpodd, ZMod.χ₈_nat_eq_if_mod_eight]
    have hp2 : (24 * k + 1) % 2 = 1 := by omega
    have hp8 : (24 * k + 1) % 8 = 1 := by omega
    simp [hp2, hp8]
  have hne4 : ell ≠ 4 := by
    intro h
    subst ell
    norm_num at hpell
  have hcase : ell = 2 ∨ ell = 3 ∨ 5 ≤ ell := by
    have h2le := hpell.two_le
    omega
  rcases hcase with h2 | h3 | h5
  · subst ell
    change jacobiSym 2 (24 * k + 1) = -1 at hneg
    rw [h2J] at hneg
    omega
  · subst ell
    change jacobiSym 3 (24 * k + 1) = -1 at hneg
    rw [hard_three_jacobi_one k] at hneg
    omega
  · exact h5

/-- For any hard prime, success of **either full type** at one first
denominator forces a prime factor of that denominator of size at least
five which is a nonresidue modulo `p`. It does not guarantee a success
for any prescribed `p` or any prescribed `x`. -/
theorem hard_types_need_large_nonresidue (k x : ℕ)
    (hpp : (24 * k + 1).Prime) (hlo : 24 * k + 1 < 4 * x)
    (hhi : x < 24 * k + 1)
    (hw : TypeI (24 * k + 1) x ∨ TypeII (24 * k + 1) x) :
    ∃ ell : ℕ, ell.Prime ∧ 5 ≤ ell ∧ ell ∣ x ∧
      jacobiSym (ell : ℤ) (24 * k + 1) = -1 := by
  have hp8 : (24 * k + 1) % 8 = 1 := by omega
  rcases hw with hI | hII
  · obtain ⟨ell, hpell, hodd, hellx, hJell⟩ :=
      typeI_has_odd_prime_nonresidue (24 * k + 1) x hp8 hlo hI
    exact ⟨ell, hpell, hard_negative_prime_at_least_five k ell hpell hJell,
      hellx, hJell⟩
  · obtain ⟨ell, hpell, hodd, hellx, hJell⟩ :=
      typeII_has_odd_prime_nonresidue (24 * k + 1) x hpp hp8 hlo hhi hII
    exact ⟨ell, hpell, hard_negative_prime_at_least_five k ell hpell hJell,
      hellx, hJell⟩

/-- In contrast with the full Type-I impossibility, Type II *can* work
for odd squares, but its first denominator must share a nontrivial factor
with the square root. This is precisely where the prime-input coprimality
step in `typeII_has_odd_prime_nonresidue` does not apply. -/
theorem odd_square_typeII_not_coprime (s x : ℕ) (hsodd : Odd s)
    (hlo : s ^ 2 < 4 * x) (hII : TypeII (s ^ 2) x) :
    ¬x.Coprime s := by
  intro hcop
  have hp8 : s ^ 2 % 8 = 1 := by
    have h8 := Nat.pow_mod s 2 8
    have hmod : s % 8 = 1 ∨ s % 8 = 3 ∨ s % 8 = 5 ∨ s % 8 = 7 := by
      have hs2 := Nat.odd_iff.mp hsodd
      omega
    rcases hmod with h | h | h | h <;> simp [h8, h]
  obtain ⟨d, hd, hdx, hdsq, hadiv⟩ := hII
  have hopp := typeII_divisor_jacobi_opposite (s ^ 2) x d hp8 hlo hdsq hadiv
  have hcopZ : (x : ℤ).gcd s = 1 := by
    simpa only [Int.gcd_natCast_natCast] using hcop.gcd_eq_one
  have hxJ : jacobiSym (x : ℤ) (s ^ 2) = 1 := by
    rw [jacobiSym.pow_right]
    rcases jacobiSym.eq_one_or_neg_one hcopZ with h | h <;> simp [h]
  have hdJ : jacobiSym (d : ℤ) (s ^ 2) ≠ -1 := by
    rw [jacobiSym.pow_right]
    rcases jacobiSym.trichotomy (d : ℤ) s with h | h | h <;> rw [h] <;> norm_num
  rw [hxJ] at hopp
  exact hdJ (by simpa using hopp)

end Erdos242
