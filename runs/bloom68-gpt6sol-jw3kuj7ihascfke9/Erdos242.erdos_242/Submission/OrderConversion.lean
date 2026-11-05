import Submission.OrderedAudit

/-!
# Strict order does not strengthen the positive three-fraction conjecture

For every `n > 2`, an unordered positive integer-denominator decomposition
exists if and only if a strictly ordered one exists. This is an equivalence,
**not** a proof that either exists for all `n`.
-/

namespace Erdos242

/-- An integer multiple of `t` cannot have a nonzero remainder strictly below `t`. -/
private theorem no_natural_quotient (m k t r : ℕ) (hr : 0 < r) (hrt : r < t)
    (heq : m * t = k * t + r) : False := by
  rcases le_total m k with hmk | hkm
  · have hmul : m * t ≤ k * t := Nat.mul_le_mul_right t hmk
    omega
  · have hge : k + 1 ≤ m := by
      by_contra h
      have hle : m ≤ k := by omega
      have hmul : m * t ≤ k * t := Nat.mul_le_mul_right t hle
      omega
    have hmul : (k + 1) * t ≤ m * t := Nat.mul_le_mul_right t hge
    simp only [add_mul, one_mul] at hmul
    omega

/-- Splitting a unit fraction into two *different* positive unit fractions. -/
private theorem unit_split (v : ℕ) (hv : 1 < v) :
    (1 / (v : ℚ)) = 1 / ((v + 1 : ℕ) : ℚ) +
      1 / ((v * (v + 1) : ℕ) : ℚ) := by
  have hvq : (v : ℚ) ≠ 0 := by exact_mod_cast (by omega : v ≠ 0)
  push_cast
  field_simp

/-- A two-term representation can be expanded to a strictly ordered triple
whenever `n > 2` (excluding the exceptional identity `4/2 = 1+1`). -/
private theorem good_of_two_units_sorted (n u v : ℕ) (hn : 2 < n)
    (hu : 0 < u) (huv : u ≤ v)
    (heq : (4 / n : ℚ) = 1 / u + 1 / v) : Good n := by
  have hvpos : 0 < v := lt_of_lt_of_le hu huv
  have hv2 : 1 < v := by
    by_contra h
    have hv1 : v = 1 := by omega
    have hu1 : u = 1 := by omega
    have htwo : (4 / n : ℚ) = 2 := by
      norm_num [hu1, hv1] at heq
      exact heq
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hcross : (4 : ℚ) = 2 * n := (div_eq_iff hnq).mp htwo
    have hn2 : n = 2 := by
      have hq : (n : ℚ) = 2 := by linarith
      exact_mod_cast hq
    omega
  refine ⟨u, v + 1, v * (v + 1), by omega, by omega, ?_, ?_⟩
  · nlinarith
  · calc
      (4 / n : ℚ) = 1 / u + 1 / v := heq
      _ = 1 / (u : ℚ) + 1 / ((v + 1 : ℕ) : ℚ) +
          1 / ((v * (v + 1) : ℕ) : ℚ) := by
        rw [unit_split v hv2]
        ring

private theorem good_of_two_units (n u v : ℕ) (hn : 2 < n)
    (hu : 0 < u) (hv : 0 < v)
    (heq : (4 / n : ℚ) = 1 / u + 1 / v) : Good n := by
  rcases le_total u v with huv | hvu
  · exact good_of_two_units_sorted n u v hn hu huv heq
  · apply good_of_two_units_sorted n v u hn hv hvu
    simpa only [add_comm] using heq

/-- A cleared-denominator version of the repeated-fraction equation. -/
private theorem repeated_equation (n a b : ℕ) (hn : 0 < n) (ha : 0 < a)
    (hb : 0 < b) (heq : (4 / n : ℚ) = 1 / a + 1 / a + 1 / b) :
    4 * a * b = n * (a + 2 * b) := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hp : 4 * (a : ℚ) * b = n * (a + 2 * b) := by
    field_simp at heq
    nlinarith [heq]
  exact_mod_cast hp

/-- Any solution with two equal denominators admits a *strictly ordered*
solution with the same three-term numerator. An odd repeated denominator `a`
is replaced using `2/a = 1/((a+1)/2) + 1/(a(a+1)/2)`; its two possible
collisions with the remaining denominator cannot occur for integral `n`. -/
private theorem good_of_repeated (n a b : ℕ) (hn : 2 < n)
    (ha : 0 < a) (hb : 0 < b)
    (heq : (4 / n : ℚ) = 1 / a + 1 / a + 1 / b) : Good n := by
  have hpoly : 4 * a * b = n * (a + 2 * b) :=
    repeated_equation n a b (by omega) ha hb heq
  by_cases heven : a % 2 = 0
  · let c := a / 2
    have hc : 0 < c := by dsimp [c]; omega
    have hac : a = 2 * c := by dsimp [c]; omega
    have hfrac : 1 / (a : ℚ) + 1 / (a : ℚ) = 1 / (c : ℚ) := by
      have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
      have hacq : (a : ℚ) = 2 * c := by exact_mod_cast hac
      rw [hacq]
      field_simp
      norm_num
    have htwo : (4 / n : ℚ) = 1 / c + 1 / b := by
      calc
        (4 / n : ℚ) = 1 / (a : ℚ) + 1 / (a : ℚ) + 1 / (b : ℚ) := heq
        _ = 1 / (c : ℚ) + 1 / (b : ℚ) := by rw [hfrac]
    exact good_of_two_units n c b hn hc hb htwo
  · have ha3 : 3 ≤ a := by
      by_contra hsmall
      have ha1 : a = 1 := by omega
      have hmul : 3 * (1 + 2 * b) ≤ n * (1 + 2 * b) :=
        Nat.mul_le_mul_right (1 + 2 * b) (by omega : 3 ≤ n)
      rw [ha1] at hpoly
      nlinarith [hpoly, hmul]
    let c := (a + 1) / 2
    let d := a * c
    have hc : 0 < c := by dsimp [c]; omega
    have hc2 : 2 ≤ c := by dsimp [c]; omega
    have hac : a + 1 = 2 * c := by dsimp [c]; omega
    have hcd : c < d := by
      have hmul := Nat.mul_le_mul_right c ha3
      dsimp [d]
      omega
    have hbc : b ≠ c := by
      intro h
      have hp := hpoly
      rw [h] at hp
      have hmul := congrArg (fun t : ℕ => a * t) hac
      have hkey : n * (a + 2 * c) = a * (a + 2 * c) + a := by
        nlinarith only [hp, hmul]
      exact no_natural_quotient n a (a + 2 * c) a ha (by omega) hkey
    have hbd : b ≠ d := by
      intro h
      have hp := hpoly
      rw [h] at hp
      dsimp [d] at hp
      have hfact : a * (4 * a * c) = a * (n * (1 + 2 * c)) := by
        calc
          a * (4 * a * c) = 4 * a * (a * c) := by ring
          _ = n * (a + 2 * (a * c)) := hp
          _ = a * (n * (1 + 2 * c)) := by ring
      have hquot : 4 * a * c = n * (1 + 2 * c) :=
        Nat.eq_of_mul_eq_mul_left ha hfact
      let k := 2 * a - 2
      have hk : k + 2 = 2 * a := by dsimp [k]; omega
      have hm := congrArg (fun t : ℕ => t * (1 + 2 * c)) hk
      have hrem : 4 * a * c = k * (1 + 2 * c) + 4 := by
        nlinarith only [hm, hac]
      have hkey : n * (1 + 2 * c) = k * (1 + 2 * c) + 4 := by
        rw [← hquot]
        exact hrem
      exact no_natural_quotient n k (1 + 2 * c) 4 (by norm_num) (by omega) hkey
    have hfrac : 1 / (a : ℚ) + 1 / (a : ℚ) =
        1 / (c : ℚ) + 1 / (d : ℚ) := by
      have haq : (a : ℚ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
      have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
      have hdq : (d : ℚ) = (a : ℚ) * c := by
        dsimp [d]
        push_cast
        ring
      have hacq : (a : ℚ) + 1 = 2 * c := by exact_mod_cast hac
      rw [hdq]
      field_simp
      nlinarith [hacq]
    have hnew : (4 / n : ℚ) = 1 / c + 1 / d + 1 / b := by
      calc
        (4 / n : ℚ) = 1 / (a : ℚ) + 1 / (a : ℚ) + 1 / (b : ℚ) := heq
        _ = 1 / (c : ℚ) + 1 / (d : ℚ) + 1 / (b : ℚ) := by rw [hfrac]
    rcases le_total b c with hle | hle
    · have hbc' : b < c := by omega
      refine ⟨b, c, d, by omega, hbc', hcd, ?_⟩
      convert hnew using 1; ring
    · rcases le_total b d with hbdle | hdble
      · have hcb' : c < b := by omega
        have hbd' : b < d := by omega
        refine ⟨c, b, d, by omega, hcb', hbd', ?_⟩
        convert hnew using 1; ring
      · have hdb' : d < b := by omega
        exact ⟨c, d, b, by omega, hcd, hdb', hnew⟩


/-- For every `n > 2`, allowing equal positive Nat denominators makes
*no difference* to the existence statement: an unordered representation
can always be replaced by one with `1 ≤ x < y < z`. -/
theorem unordered_nat_iff_ordered_nat (n : ℕ) (hn : 2 < n) :
    UnorderedNat n ↔ Good n := by
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, heq⟩
    by_cases hxy : x = y
    · subst y
      exact good_of_repeated n x z hn (by omega) (by omega) heq
    by_cases hxz : x = z
    · subst z
      have hrepeat : (4 / n : ℚ) = 1 / x + 1 / x + 1 / y := by
        calc
          (4 / n : ℚ) = 1 / x + 1 / y + 1 / x := heq
          _ = 1 / x + 1 / x + 1 / y := by ring
      exact good_of_repeated n x y hn (by omega) (by omega) hrepeat
    by_cases hyz : y = z
    · subst z
      have hrepeat : (4 / n : ℚ) = 1 / y + 1 / y + 1 / x := by
        calc
          (4 / n : ℚ) = 1 / x + 1 / y + 1 / y := heq
          _ = 1 / y + 1 / y + 1 / x := by ring
      exact good_of_repeated n y x hn (by omega) (by omega) hrepeat
    rcases le_total x y with hxy' | hyx'
    · rcases le_total y z with hyz' | hzy'
      · exact ⟨x, y, z, hx, by omega, by omega, heq⟩
      · rcases le_total x z with hxz' | hzx'
        · refine ⟨x, z, y, hx, by omega, by omega, ?_⟩
          convert heq using 1; ring
        · refine ⟨z, x, y, hz, by omega, by omega, ?_⟩
          convert heq using 1; ring
    · rcases le_total x z with hxz' | hzx'
      · refine ⟨y, x, z, hy, by omega, by omega, ?_⟩
        convert heq using 1; ring
      · rcases le_total y z with hyz' | hzy'
        · refine ⟨y, z, x, hy, by omega, by omega, ?_⟩
          convert heq using 1; ring
        · refine ⟨z, y, x, hz, by omega, by omega, ?_⟩
          convert heq using 1; ring
  · exact ordered_implies_unordered_nat

/-- Allowing Int instead of Nat denominators makes no change if all
three denominators are stipulated to be positive; equality is permitted
on both sides. -/
theorem unordered_nat_iff_unordered_int (n : ℕ) :
    UnorderedNat n ↔ UnorderedInt n := by
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, heq⟩
    refine ⟨(x : ℤ), (y : ℤ), (z : ℤ), ?_, ?_, ?_, ?_⟩
    · exact_mod_cast hx
    · exact_mod_cast hy
    · exact_mod_cast hz
    · simpa only [Int.cast_natCast] using heq
  · rintro ⟨x, y, z, hx, hy, hz, heq⟩
    have hx' : (x.toNat : ℤ) = x := Int.toNat_of_nonneg (by omega)
    have hy' : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
    have hz' : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (by omega)
    refine ⟨x.toNat, y.toNat, z.toNat, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · have hxq : (x.toNat : ℚ) = (x : ℚ) := by exact_mod_cast hx'
      have hyq : (y.toNat : ℚ) = (y : ℚ) := by exact_mod_cast hy'
      have hzq : (z.toNat : ℚ) = (z : ℚ) := by exact_mod_cast hz'
      simpa only [hxq, hyq, hzq] using heq

/-- The same *unconditional conversion of positive unordered solutions*
works for integer denominators, whenever `n > 2`. -/
theorem unordered_int_iff_ordered_int (n : ℕ) (hn : 2 < n) :
    UnorderedInt n ↔ OrderedInt n := by
  calc
    UnorderedInt n ↔ UnorderedNat n := (unordered_nat_iff_unordered_int n).symm
    _ ↔ Good n := unordered_nat_iff_ordered_nat n hn
    _ ↔ OrderedInt n := ordered_nat_iff_ordered_int n

/-- The actual universal ordered Nat *proposition* (not the theorem from
`Spec.lean`) is equivalent to the unrestricted positive-Nat proposition.
Neither universal proposition is asserted by this conditional equivalence. -/
theorem all_ordered_iff_all_unordered_nat :
    (∀ n : ℕ, 2 < n → Good n) ↔ (∀ n : ℕ, 2 < n → UnorderedNat n) := by
  constructor
  · intro h n hn
    exact (unordered_nat_iff_ordered_nat n hn).mpr (h n hn)
  · intro h n hn
    exact (unordered_nat_iff_ordered_nat n hn).mp (h n hn)

/-- Pointwise formulation of the result: any genuine ordered counterexample
for `n>2` would simultaneously be an unordered counterexample. This is an
implication/equivalence, not the assertion that a counterexample exists. -/
theorem bad_ordered_iff_bad_unordered_nat (n : ℕ) (hn : 2 < n) :
    (¬ Good n) ↔ (¬ UnorderedNat n) := by
  constructor
  · intro h hg
    exact h ((unordered_nat_iff_ordered_nat n hn).mp hg)
  · intro h hg
    exact h ((unordered_nat_iff_ordered_nat n hn).mpr hg)

/-- The precise right-hand side of the proposition in `Spec.lean`, expanded
rather than referenced, is equivalent to the unrestricted positive version.
The admitted theorem from `Spec.lean` is not imported or used. -/
theorem raw_ordered_iff_unordered_nat (n : ℕ) (hn : 2 < n) :
    (∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z) ↔
    (∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z) := by
  exact (unordered_nat_iff_ordered_nat n hn).symm

end Erdos242

#print axioms Erdos242.good_of_two_units
#print axioms Erdos242.unordered_nat_iff_ordered_nat
#print axioms Erdos242.unordered_int_iff_ordered_int
#print axioms Erdos242.all_ordered_iff_all_unordered_nat
#print axioms Erdos242.bad_ordered_iff_bad_unordered_nat
#print axioms Erdos242.raw_ordered_iff_unordered_nat
