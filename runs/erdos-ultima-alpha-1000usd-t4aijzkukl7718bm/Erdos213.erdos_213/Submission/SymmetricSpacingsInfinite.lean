import Submission.SymmetricSpacings
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.NormNum

/-! An infinite family of symmetric rational-distance spacings on a line.
The resulting anchors are collinear, so this is not a proof of Erdos 213. -/
namespace Erdos213.SymmetricSpacings

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local notation "ν" => padicValRat 2

private lemma val_pow (r : ℚ) (n : ℕ) : ν (r^n) = (n : ℤ)*ν r := by
  by_cases hr : r = 0
  · subst r
    cases n <;> simp
  · exact padicValRat.pow hr

private lemma dominant_add {r s : ℚ} (hr : r ≠ 0) (h : ν r < ν s) :
    r+s ≠ 0 ∧ ν (r+s) = ν r := by
  by_cases hs : s = 0
  · simpa [hs] using And.intro hr (rfl : ν r = ν r)
  have hn : r+s ≠ 0 := by
    intro he
    have he' : r = -s := eq_neg_of_add_eq_zero_left he
    have hv := congrArg (padicValRat 2) he'
    rw [padicValRat.neg] at hv
    omega
  exact ⟨hn, padicValRat.add_eq_of_lt hn hr hs h⟩

private lemma dominant_sub {r s : ℚ} (hr : r ≠ 0) (h : ν r < ν s) :
    r-s ≠ 0 ∧ ν (r-s) = ν r := by
  simpa only [sub_eq_add_neg, padicValRat.neg] using
    (dominant_add (r := r) (s := -s) hr (by simpa only [padicValRat.neg] using h))

private lemma val_two : ν (2 : ℚ) = 1 := padicValRat.self (by decide)
private lemma val_four : ν (4 : ℚ) = 2 := by
  rw [show (4 : ℚ) = 2^2 by norm_num, val_pow, val_two]
  norm_num

lemma double_spacing_valuation (x a r y : ℚ) (hx : 0 ≤ ν x) (ha : 0 ≤ ν a)
    (hrv : ν r < 0) (he : y^2 = (r^2+a^2)^2-4*x^2*r^2) :
    y ≠ 0 ∧ ν (doubleSpacing a r y) = ν r - 1 := by
  have hr : r ≠ 0 := by intro h; simp [h] at hrv
  have hsum := dominant_add (pow_ne_zero 2 hr)
    (show ν (r^2) < ν (a^2) by rw [val_pow, val_pow]; norm_num; omega)
  have hsumval : ν (r^2+a^2) = 2*ν r := by simpa [val_pow] using hsum.2
  have hterm : ν ((r^2+a^2)^2) < ν (4*x^2*r^2) := by
    rw [val_pow, hsumval]
    by_cases hx0 : x = 0
    · simp [hx0]
      omega
    · rw [padicValRat.mul (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx0))
        (pow_ne_zero 2 hr), padicValRat.mul (by norm_num : (4 : ℚ) ≠ 0)
        (pow_ne_zero 2 hx0), val_four, val_pow, val_pow]
      norm_num
      omega
  have hd := dominant_sub (pow_ne_zero 2 hsum.1) hterm
  have hy : y ≠ 0 := by
    intro h
    have hh : (r^2+a^2)^2-4*x^2*r^2 = 0 := by simpa [h] using he.symm
    exact hd.1 hh
  have hyv : ν y = 2*ν r := by
    have hh := congrArg (padicValRat 2) he
    rw [val_pow, hd.2, val_pow, hsumval] at hh
    norm_num at hh
    omega
  have hn := dominant_sub (pow_ne_zero 4 hr)
    (show ν (r^4) < ν (a^4) by rw [val_pow, val_pow]; norm_num; omega)
  have hvn : ν (r^4-a^4) = 4*ν r := by simpa [val_pow] using hn.2
  refine ⟨hy, ?_⟩
  unfold doubleSpacing
  rw [padicValRat.div hn.1 (mul_ne_zero (mul_ne_zero (by norm_num) hr) hy),
    padicValRat.mul (mul_ne_zero (by norm_num) hr) hy,
    padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) hr, val_two, hyv, hvn]
  omega

private lemma val_odd_nat (n : ℕ) (h : ¬2 ∣ n) : ν (n : ℚ) = 0 := by
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd h]
  rfl

private def fixedX : ℚ := -17081/41905
private def fixedA : ℚ := 131/85

private lemma fixed_valuations : ν fixedX = 0 ∧ ν fixedA = 0 := by
  have h17081 : ν (17081 : ℚ) = 0 := by
    simpa only [Nat.cast_ofNat] using val_odd_nat 17081 (by norm_num)
  have h41905 : ν (41905 : ℚ) = 0 := by
    simpa only [Nat.cast_ofNat] using val_odd_nat 41905 (by norm_num)
  have h131 : ν (131 : ℚ) = 0 := by
    simpa only [Nat.cast_ofNat] using val_odd_nat 131 (by norm_num)
  have h85 : ν (85 : ℚ) = 0 := by
    simpa only [Nat.cast_ofNat] using val_odd_nat 85 (by norm_num)
  constructor
  · unfold fixedX
    rw [padicValRat.div (by norm_num) (by norm_num), padicValRat.neg, h17081, h41905]
    rfl
  · unfold fixedA
    rw [padicValRat.div (by norm_num) (by norm_num), h131, h85]
    rfl

private lemma first_valuation : ν (957/578 : ℚ) = -1 := by
  have h957 : ν (957 : ℚ) = 0 := by
    simpa only [Nat.cast_ofNat] using val_odd_nat 957 (by norm_num)
  have h289 : ν (289 : ℚ) = 0 := by
    simpa only [Nat.cast_ofNat] using val_odd_nat 289 (by norm_num)
  rw [padicValRat.div (by norm_num) (by norm_num), h957,
    show (578 : ℚ) = 2*289 by norm_num,
    padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) (by norm_num : (289 : ℚ) ≠ 0),
    val_two, h289]
  rfl

private lemma pair_product (x a r u v : ℚ)
    (hu : r^2+2*x*r+a^2 = u*u) (hv : r^2-2*x*r+a^2 = v*v) :
    (u*v)^2 = (r^2+a^2)^2-4*x^2*r^2 := by
  calc
    (u*v)^2 = (u*u)*(v*v) := by ring
    _ = (r^2+2*x*r+a^2)*(r^2-2*x*r+a^2) := by rw [hu, hv]
    _ = (r^2+a^2)^2-4*x^2*r^2 := by ring

/-- The line parameters have arbitrarily negative 2-adic valuation. -/
theorem spacings_arbitrarily_negative (n : ℕ) :
    ∃ r y : ℚ, y^2 = (r^2+fixedA^2)^2-4*fixedX^2*r^2 ∧
      ν r = -(n : ℤ)-1 ∧
      IsSquare (r^2+2*fixedX*r+fixedA^2) ∧
      IsSquare (r^2-2*fixedX*r+fixedA^2) := by
  induction n with
  | zero =>
    refine ⟨957/578, (5609/2890)*(7349/2890), ?_, ?_, ?_, ?_⟩
    · norm_num [fixedA, fixedX]
    · simpa using first_valuation
    · refine ⟨5609/2890, ?_⟩
      norm_num [fixedA, fixedX]
    · refine ⟨7349/2890, ?_⟩
      norm_num [fixedA, fixedX]
  | succ n ih =>
    obtain ⟨r,y,he,hrv,hp,hm⟩ := ih
    have hx : 0 ≤ ν fixedX := by rw [fixed_valuations.1]
    have ha : 0 ≤ ν fixedA := by rw [fixed_valuations.2]
    have hn : ν r < 0 := by rw [hrv]; omega
    have hr : r ≠ 0 := by intro h; simp [h] at hn
    obtain ⟨hy,hnext⟩ := double_spacing_valuation fixedX fixedA r y hx ha hn he
    obtain ⟨hp',hm'⟩ := double_spacing_squares fixedX fixedA r y hr hy he
    obtain ⟨u,hu⟩ := hp'
    obtain ⟨v,hv⟩ := hm'
    refine ⟨doubleSpacing fixedA r y,u*v,pair_product _ _ _ _ _ hu hv,?_,
      ⟨u,hu⟩,⟨v,hv⟩⟩
    rw [hnext, hrv]
    push_cast
    ring

/-- Infinitely many distinct symmetric spacings, not a general-position set. -/
theorem infinite_symmetric_spacings :
    ∃ r : ℕ → ℚ, Function.Injective r ∧ ∀ n,
      IsSquare ((r n)^2+2*(-17081/41905)*(r n)+(131/85)^2) ∧
      IsSquare ((r n)^2-2*(-17081/41905)*(r n)+(131/85)^2) := by
  classical
  choose r y he hval hp hm using spacings_arbitrarily_negative
  refine ⟨r, ?_, ?_⟩
  · intro m n hmn
    have hv := congrArg (padicValRat 2) hmn
    rw [hval m, hval n] at hv
    omega
  · intro n
    exact ⟨hp n,hm n⟩

#print axioms double_spacing_valuation
#print axioms spacings_arbitrarily_negative
#print axioms infinite_symmetric_spacings
end Erdos213.SymmetricSpacings
