import FormalConjecturesUtil

/-!
# Normalized quadratics in unit residue classes

If `m ∣ a` and `b` is a unit modulo `m`, the polynomial `a*x^2+b*x`
permutes the residues modulo every power of `m`. This explains a limitation
of repeated-modulus residue arguments; it is not a bound for Erdős 773.
-/
namespace Erdos773.NormalizedQuadraticPermutation

set_option maxHeartbeats 1000000

/-- A quadratic with its constant term removed. -/
def quadratic (a b x : ℤ) : ℤ := a*x^2+b*x

lemma difference (a b x y : ℤ) :
    quadratic a b y - quadratic a b x = (a*(x+y)+b)*(y-x) := by
  dsimp [quadratic]
  ring

/-- The non-difference factor is a unit at every power of the modulus. -/
lemma factor_coprime (m a b x y : ℤ) (k : ℕ)
    (hma : m ∣ a) (hmb : IsCoprime m b) :
    IsCoprime (m^k) (a*(x+y)+b) := by
  obtain ⟨t, rfl⟩ := hma
  have h := (hmb.add_mul_left_right (t*(x+y))).pow_left (m := k)
  convert h using 1
  ring

/-- Equal output residues are equivalent to equal input residues. No
primality, oddness, or positive-exponent assumption is necessary. -/
theorem modEq_iff (m a b x y : ℤ) (k : ℕ)
    (hma : m ∣ a) (hmb : IsCoprime m b) :
    quadratic a b x ≡ quadratic a b y [ZMOD m^k] ↔
      x ≡ y [ZMOD m^k] := by
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd, difference]
  constructor
  · exact (factor_coprime m a b x y k hma hmb).dvd_of_dvd_mul_left
  · intro h
    exact dvd_mul_of_dvd_right h _

/-- The corresponding polynomial function on a finite residue ring is
bijective, not merely a map with a large image. -/
theorem bijective (m : ℕ) (hm : 0 < m) (a b : ℤ) (k : ℕ)
    (hma : (m : ℤ) ∣ a) (hmb : IsCoprime (m : ℤ) b) :
    Function.Bijective
      (fun x : ZMod (m^k) => (a : ZMod (m^k))*x^2+(b : ZMod (m^k))*x) := by
  letI : NeZero (m^k) := ⟨pow_ne_zero _ hm.ne'⟩
  have hinj : Function.Injective
      (fun x : ZMod (m^k) => (a : ZMod (m^k))*x^2+(b : ZMod (m^k))*x) := by
    intro x y he
    let u : ℤ := x.val
    let v : ℤ := y.val
    have hx : (u : ZMod (m^k)) = x := by simp [u]
    have hy : (v : ZMod (m^k)) = y := by simp [v]
    have he' : ((quadratic a b u : ℤ) : ZMod (m^k)) =
        ((quadratic a b v : ℤ) : ZMod (m^k)) := by
      simpa [quadratic, hx, hy] using he
    have hout : quadratic a b u ≡ quadratic a b v [ZMOD (m : ℤ)^k] := by
      simpa only [Nat.cast_pow] using
        (ZMod.intCast_eq_intCast_iff _ _ (m^k)).mp he'
    have hin := (modEq_iff (m : ℤ) a b u v k hma hmb).mp hout
    have hcast : (u : ZMod (m^k)) = (v : ZMod (m^k)) := by
      apply (ZMod.intCast_eq_intCast_iff _ _ (m^k)).mpr
      simpa only [Nat.cast_pow] using hin
    simpa only [hx, hy] using hcast
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

/-- In particular, there are no missing output residue classes. -/
theorem range_eq_univ (m : ℕ) (hm : 0 < m) (a b : ℤ) (k : ℕ)
    (hma : (m : ℤ) ∣ a) (hmb : IsCoprime (m : ℤ) b) :
    Set.range (fun x : ZMod (m^k) => (a : ZMod (m^k))*x^2+
      (b : ZMod (m^k))*x) = Set.univ :=
  Set.range_eq_univ.mpr (bijective m hm a b k hma hmb).surjective

/-- Splitting the index into one residue class changes both coefficients.
The outer multiplier `p` must be retained when comparing heights. -/
lemma renormalize (q r p s x : ℤ) :
    quadratic q (2*r) (p*x+s) =
      p * quadratic (q*p) (2*(q*s+r)) x + quadratic q (2*r) s := by
  dsimp [quadratic]
  ring

/-- The linear coefficient remains a unit at a modulus already dividing
`q`, even after an arbitrary further index restriction. -/
lemma renormalized_unit (m q r s : ℤ) (hmq : m ∣ q)
    (hmr : IsCoprime m (2*r)) : IsCoprime m (2*(q*s+r)) := by
  obtain ⟨t, rfl⟩ := hmq
  have h := hmr.add_mul_left_right (2*t*s)
  convert h using 1
  ring

/-- Reusing a modulus that already divides the leading coefficient still
leaves every prime-power (indeed, every modulus-power) residue available. -/
theorem renormalized_bijective (m : ℕ) (hm : 0 < m) (q r p s : ℤ) (k : ℕ)
    (hmq : (m : ℤ) ∣ q) (hmr : IsCoprime (m : ℤ) (2*r)) :
    Function.Bijective
      (fun x : ZMod (m^k) => ((q*p : ℤ) : ZMod (m^k))*x^2+
        ((2*(q*s+r) : ℤ) : ZMod (m^k))*x) := by
  exact bijective m hm (q*p) (2*(q*s+r)) k (dvd_mul_of_dvd_left hmq p)
    (renormalized_unit (m : ℤ) q r s hmq hmr)

end Erdos773.NormalizedQuadraticPermutation

#print axioms Erdos773.NormalizedQuadraticPermutation.factor_coprime
#print axioms Erdos773.NormalizedQuadraticPermutation.modEq_iff
#print axioms Erdos773.NormalizedQuadraticPermutation.bijective
#print axioms Erdos773.NormalizedQuadraticPermutation.range_eq_univ
#print axioms Erdos773.NormalizedQuadraticPermutation.renormalize
#print axioms Erdos773.NormalizedQuadraticPermutation.renormalized_bijective
