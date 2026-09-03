import Submission.QuadraticSquareLatticeCover

/-! Uniform divisibility bounds for primes and products of two primes.
Constants depend on the fixed binary quadratic form. -/
namespace Erdos1206.QuadraticSemiprimeDivisibility
open Finset QuadraticLatticeLines QuadraticRootLattice QuadraticPrimeDivisibility
  QuadraticLatticeCover QuadraticSquareLatticeCover
open scoped Classical
set_option maxHeartbeats 2000000

def coefficientSize (a b c : ℤ) : ℕ := mass a b c+(b^2-4*a*c).natAbs+1
def constant (a b c : ℤ) : ℕ := 144*(coefficientSize a b c)^2

def LowComplexity (d : ℕ) : Prop :=
  d.Prime ∨ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ d=p*q

lemma LowComplexity.one_lt {d : ℕ} (hd : LowComplexity d) : 1 < d := by
  rcases hd with hd | ⟨p,q,hp,hq,rfl⟩
  · exact hd.one_lt
  · nlinarith [hp.two_le,hq.two_le]

lemma size_pos (a b c : ℤ) : 0 < coefficientSize a b c := by dsimp [coefficientSize]; omega
lemma mass_le_size (a b c : ℤ) : mass a b c ≤ coefficientSize a b c := by dsimp [coefficientSize]; omega
lemma mass_le_size_sq (a b c : ℤ) : mass a b c ≤ (coefficientSize a b c)^2 := by
  have := size_pos a b c
  have := mass_le_size a b c
  nlinarith

lemma leading_ne_zero {a b c : ℤ} (hQ : Anisotropic a b c) : a≠0 := by
  simpa only [form,one_pow,mul_one,mul_zero,zero_pow (by decide : 2≠0),add_zero] using
    hQ (1,0) (by decide)

lemma prime_le_size_of_dvd_leading {a b c : ℤ} (hQ : Anisotropic a b c)
    {p : ℕ} (hpa : (p:ℤ)∣a) : p ≤ coefficientSize a b c := by
  have hp := Int.natAbs_le_of_dvd_ne_zero hpa (leading_ne_zero hQ)
  simp only [Int.natAbs_natCast] at hp
  dsimp [coefficientSize,mass]
  omega

lemma prime_le_size_of_dvd_discriminant {a b c : ℤ} (hD : b^2-4*a*c ≠ 0)
    {p : ℕ} (hpd : (p:ℤ)∣b^2-4*a*c) : p ≤ coefficientSize a b c := by
  have hp := Int.natAbs_le_of_dvd_ne_zero hpd hD
  simp only [Int.natAbs_natCast] at hp
  dsimp [coefficientSize]
  omega

lemma points_subset_of_dvd {a b c : ℤ} {N d e : ℕ} (hde : d∣e) :
    points a b c N e ⊆ points a b c N d := by
  intro x hx
  obtain ⟨hxbox,hx0,hdiv⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨hxbox,hx0,(Int.natCast_dvd_natCast.mpr hde).trans hdiv⟩

lemma points_empty_of_large {a b c : ℤ} (hQ : Anisotropic a b c) {N d : ℕ}
    (hlarge : mass a b c*N^2 < d) : points a b c N d=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (not_le_of_gt hlarge) (prime_le_height hQ hx)

lemma points_card_le {a b c : ℤ} {N d : ℕ} (hN : 0 < N) :
    (points a b c N d).card ≤ 9*N^2 := by
  have hh := card_le_card (filter_subset (fun x : Vec => x≠0 ∧ (d:ℤ)∣form a b c x)
    (QuadraticLatticeLines.box N))
  rw [card_box] at hh
  change (points a b c N d).card ≤ (2*N+1)^2 at hh
  nlinarith

lemma product_bound_of_small_left {a b c : ℤ} (hQ : Anisotropic a b c)
    (N p q : ℕ) (hq : q.Prime) (hp : p ≤ coefficientSize a b c) :
    (p*q)*(points a b c N (p*q)).card ≤ constant a b c*N^2 := by
  have hc := card_le_card (points_subset_of_dvd (a := a) (b := b) (c := c) (N := N) (dvd_mul_left q p))
  have hh := (Nat.mul_le_mul_left q hc).trans (prime_divisibility_bound hQ N q hq)
  calc
    (p*q)*(points a b c N (p*q)).card = p*(q*(points a b c N (p*q)).card) := by ring
    _ ≤ p*(48*mass a b c*N^2) := Nat.mul_le_mul_left p hh
    _ = 48*(p*mass a b c)*N^2 := by ring
    _ ≤ 48*((coefficientSize a b c)^2)*N^2 := by
      have hprod := Nat.mul_le_mul hp (mass_le_size a b c)
      exact Nat.mul_le_mul_right (N^2) (Nat.mul_le_mul_left 48 (by simpa only [pow_two] using hprod))
    _ ≤ constant a b c*N^2 := by dsimp [constant]; nlinarith

/-- The distinct-prime case combines at most nine root lattices. -/
lemma distinct_product_bound {a b c : ℤ} (hQ : Anisotropic a b c)
    (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) :
    (p*q)*(points a b c N (p*q)).card ≤ constant a b c*N^2 := by
  by_cases hpa : (p:ℤ)∣a
  · exact product_bound_of_small_left hQ N p q hq (prime_le_size_of_dvd_leading hQ hpa)
  by_cases hqa : (q:ℤ)∣a
  · simpa only [mul_comm q p] using
      product_bound_of_small_left hQ N q p hp (prime_le_size_of_dvd_leading hQ hqa)
  obtain ⟨I,hI,hIc⟩ := covers_prime (a := a) (b := b) (c := c) N p hp hpa
  obtain ⟨J,hJ,hJc⟩ := covers_prime (a := a) (b := b) (c := c) N q hq hqa
  obtain ⟨K,hK,hKc⟩ := covers_coprime_mul hIc hJc ((Nat.coprime_primes hp hq).mpr hpq)
  have hK9 : K.card ≤ 9 := hK.trans (by nlinarith)
  have hh := cover_mass_bound hQ (Nat.mul_pos hp.pos hq.pos) hK9 hKc
  have hm := Nat.mul_le_mul_left (144*N^2) (mass_le_size_sq a b c)
  dsimp [constant]
  nlinarith only [hh,hm]

/-- Prime squares require the Hensel root cover, not a coprime product step. -/
lemma square_bound {a b c : ℤ} (hQ : Anisotropic a b c) (hD : b^2-4*a*c≠0)
    (N p : ℕ) (hp : p.Prime) :
    p^2*(points a b c N (p^2)).card ≤ constant a b c*N^2 := by
  by_cases hsize : p^2 ≤ mass a b c*N^2
  swap
  · rw [points_empty_of_large hQ (by omega),card_empty,mul_zero]
    omega
  have hN : 0 < N := by
    by_contra! hN
    have hz : N=0 := by omega
    simp only [hz,zero_pow (by decide : 2≠0),mul_zero] at hsize
    have := pow_pos hp.pos 2
    omega
  by_cases hregular : ¬(p:ℤ)∣a ∧ ¬(p:ℤ)∣b^2-4*a*c
  · have ha' : (a:ZMod p)≠0 := fun hz => hregular.1 ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hz)
    have hD' : (b:ZMod p)^2-4*a*c≠0 := by
      intro hz
      apply hregular.2
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simpa only [Int.cast_sub,Int.cast_pow,Int.cast_mul,Int.cast_ofNat] using hz
    obtain ⟨I,hI,hIc⟩ := covers_prime_square (a := a) (b := b) (c := c) N p hp ha' hD'
    have hh := cover_mass_bound hQ (pow_pos hp.pos 2) hI hIc
    have hm := Nat.mul_le_mul_left (144*N^2) (mass_le_size_sq a b c)
    dsimp [constant]
    nlinarith only [hh,hm]
  · have hpC : p ≤ coefficientSize a b c := by
      by_cases hpa : (p:ℤ)∣a
      · exact prime_le_size_of_dvd_leading hQ hpa
      · exact prime_le_size_of_dvd_discriminant hD (by tauto)
    have hh := Nat.mul_le_mul (Nat.pow_le_pow_left hpC 2)
      (points_card_le (a := a) (b := b) (c := c) (d := p^2) hN)
    dsimp [constant]
    nlinarith only [hh]

/-- A uniform bound for all moduli with one or two prime factors, counted
with multiplicity. No estimate uniform in the number of factors is claimed. -/
theorem low_complexity_bound {a b c : ℤ} (hQ : Anisotropic a b c)
    (hD : b^2-4*a*c≠0) (N d : ℕ) (hd : LowComplexity d) :
    d*(points a b c N d).card ≤ constant a b c*N^2 := by
  rcases hd with hp | ⟨p,q,hp,hq,rfl⟩
  · have hh := prime_divisibility_bound hQ N d hp
    have hm := Nat.mul_le_mul_left (144*N^2) (mass_le_size_sq a b c)
    dsimp [constant]
    nlinarith only [hh,hm]
  · by_cases hpq : p=q
    · subst q
      simpa only [pow_two] using square_bound hQ hD N p hp
    · exact distinct_product_bound hQ N p q hp hq hpq

#print axioms low_complexity_bound
end Erdos1206.QuadraticSemiprimeDivisibility
