import FormalConjecturesUtil

/-! A homogeneous modular obstruction to rational roots, with explicit Horner
coefficient lists. This utility asserts no bound on representation counts. -/
namespace Erdos322Research.RationalPolynomialModularObstruction

/-- Coefficients are stored in ascending order. -/
def evalList {R : Type*} [CommRing R] : List ℤ → R → R
  | [], _ => 0
  | c::cs, x => (c : R)+x*evalList cs x

/-- Homogenized Horner evaluation. -/
def homList {R : Type*} [CommRing R] : List ℤ → R → R → R
  | [], _, _ => 0
  | c::cs, a, b => (c : R)*b^cs.length+a*homList cs a b

theorem evalList_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (cs : List ℤ) (a : R) :
    f (evalList cs a) = evalList cs (f a) := by
  induction cs with
  | nil => simp [evalList]
  | cons c cs ih => simp [evalList, ih]

theorem homList_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (cs : List ℤ) (a b : R) :
    f (homList cs a b) = homList cs (f a) (f b) := by
  induction cs with
  | nil => simp [homList]
  | cons c cs ih => simp [homList, ih]

theorem homList_one {R : Type*} [CommRing R] (cs : List ℤ) (a : R) :
    homList cs a 1 = evalList cs a := by
  induction cs with
  | nil => simp [homList, evalList]
  | cons c cs ih => simp [homList, evalList, ih]

theorem homogenize {R : Type*} [Field R] (cs : List ℤ) (a b : R) (hb : b ≠ 0) :
    b*homList cs a b = b^cs.length*evalList cs (a/b) := by
  induction cs with
  | nil => simp [homList, evalList]
  | cons c cs ih =>
    simp only [homList, evalList, List.length_cons, pow_succ]
    field_simp
    linear_combination a*ih

/-- A homogeneous polynomial with no projective point modulo a prime has no
rational root. Reduction uses primitive numerator and denominator. -/
theorem no_rational_root {p : ℕ} [Fact p.Prime] (cs : List ℤ)
    (hmod : ∀ a b : ZMod p, homList cs a b = 0 → a = 0 ∧ b = 0)
    (x : ℚ) : evalList cs x ≠ 0 := by
  intro hx
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hh := homogenize cs (x.num : ℚ) (x.den : ℚ) hd
  rw [x.num_div_den, hx, mul_zero] at hh
  have hr : homList cs (x.num : ℚ) (x.den : ℚ) = 0 :=
    (mul_eq_zero.mp hh).resolve_left hd
  have hi : homList cs x.num (x.den : ℤ) = 0 := by
    have he := homList_map (Int.castRingHom ℚ) cs x.num (x.den : ℤ)
    change ((homList cs x.num (x.den : ℤ) : ℤ) : ℚ) =
      homList cs (x.num : ℚ) ((x.den : ℤ) : ℚ) at he
    simp only [Int.cast_natCast] at he
    have hz : ((homList cs x.num (x.den : ℤ) : ℤ) : ℚ) = 0 := he.trans hr
    exact_mod_cast hz
  have hm : homList cs (x.num : ZMod p) (x.den : ZMod p) = 0 := by
    have he := homList_map (Int.castRingHom (ZMod p)) cs x.num (x.den : ℤ)
    change ((homList cs x.num (x.den : ℤ) : ℤ) : ZMod p) =
      homList cs (x.num : ZMod p) ((x.den : ℤ) : ZMod p) at he
    simpa only [Int.cast_natCast, hi, Int.cast_zero] using he.symm
  obtain ⟨hn, hd⟩ := hmod _ _ hm
  obtain ⟨u, v, huv⟩ := x.isCoprime_num_den
  have he := congrArg (Int.castRingHom (ZMod p)) huv
  norm_num [hn, hd] at he

end Erdos322Research.RationalPolynomialModularObstruction
