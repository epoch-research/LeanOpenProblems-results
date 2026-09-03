import FormalConjecturesUtil

/-!
One-step lifting of the pair sum in an equal-square-sum relation in a unit
residue class. This is auxiliary work, not a proof of Erdős 773.
-/
namespace Erdos773.UnitResidueLift

set_option maxHeartbeats 1000000

/-- A common invertible root residue supplies two powers of the modulus in
    the difference of pair sums. No bound on the roots is needed. -/
lemma pair_sum_lift (q r a b c d : ℤ) (hq : q ≠ 0)
    (hcop : IsCoprime q (2 * r))
    (ha : q ∣ a - r) (hb : q ∣ b - r)
    (hc : q ∣ c - r) (hd : q ∣ d - r)
    (he : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) :
    q ^ 2 ∣ a + b - c - d := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  obtain ⟨z, hz⟩ := hc
  obtain ⟨w, hw⟩ := hd
  have ha' : a = r + q * x := by omega
  have hb' : b = r + q * y := by omega
  have hc' : c = r + q * z := by omega
  have hd' : d = r + q * w := by omega
  rw [ha', hb', hc', hd'] at he ⊢
  have he' : q * (x ^ 2 + y ^ 2 - z ^ 2 - w ^ 2) +
      2 * r * (x + y - z - w) = 0 := by
    apply mul_left_cancel₀ hq
    linear_combination he
  have hdiv : q ∣ 2 * r * (x + y - z - w) := by
    refine ⟨-(x ^ 2 + y ^ 2 - z ^ 2 - w ^ 2), ?_⟩
    linear_combination he'
  obtain ⟨t, ht⟩ := hcop.dvd_of_dvd_mul_left hdiv
  refine ⟨t, ?_⟩
  linear_combination q * ht

lemma pair_sum_congruence (q r a b c d : ℤ) (hq : q ≠ 0)
    (hcop : IsCoprime q (2 * r))
    (ha : a ≡ r [ZMOD q]) (hb : b ≡ r [ZMOD q])
    (hc : c ≡ r [ZMOD q]) (hd : d ≡ r [ZMOD q])
    (he : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) :
    a + b ≡ c + d [ZMOD q ^ 2] := by
  apply Int.modEq_iff_dvd.mpr
  have h := pair_sum_lift q r a b c d hq hcop
    ha.symm.dvd hb.symm.dvd hc.symm.dvd hd.symm.dvd he
  convert dvd_neg.mpr h using 1
  ring

lemma pairs_identified_of_sum_eq (a b c d : ℤ)
    (hs : a + b = c + d) (he : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hf : (a - c) * (a - d) = 0 := by
    have hb : b = c + d - a := by omega
    rw [hb] at he
    nlinarith only [he]
  rcases mul_eq_zero.mp hf with hh | hh
  · left
    constructor <;> omega
  · right
    constructor <;> omega

/-- The one-step lift identifies the roots if the difference of pair sums
    has absolute value smaller than the new modulus. -/
lemma pairs_identified_of_small_sum_gap (q r a b c d : ℤ) (hq : q ≠ 0)
    (hcop : IsCoprime q (2 * r))
    (ha : q ∣ a - r) (hb : q ∣ b - r)
    (hc : q ∣ c - r) (hd : q ∣ d - r)
    (he : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2)
    (hgap : (a + b - c - d).natAbs < (q ^ 2).natAbs) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    (pair_sum_lift q r a b c d hq hcop ha hb hc hd he) hgap
  exact pairs_identified_of_sum_eq a b c d (by omega) he

-- An exact family showing why the lift cannot simply be iterated.
def rootA (q : ℤ) : ℤ := 2 * q ^ 2 + 4 * q + 1
def rootB (q : ℤ) : ℤ := 9 * q ^ 2 + 7 * q + 1
def rootC (q : ℤ) : ℤ := 6 * q ^ 2 + 6 * q + 1
def rootD (q : ℤ) : ℤ := 7 * q ^ 2 + 5 * q + 1

lemma family_collision (q : ℤ) :
    rootA q ^ 2 + rootB q ^ 2 = rootC q ^ 2 + rootD q ^ 2 := by
  unfold rootA rootB rootC rootD
  ring

lemma family_common_residue (q : ℤ) :
    q ∣ rootA q - 1 ∧ q ∣ rootB q - 1 ∧
    q ∣ rootC q - 1 ∧ q ∣ rootD q - 1 := by
  refine ⟨⟨2 * q + 4, ?_⟩, ⟨9 * q + 7, ?_⟩,
    ⟨6 * q + 6, ?_⟩, ⟨7 * q + 5, ?_⟩⟩ <;>
    simp only [rootA, rootB, rootC, rootD] <;> ring

lemma family_order (q : ℤ) (hq : 2 ≤ q) :
    0 < rootA q ∧ rootA q < rootC q ∧
    rootC q < rootD q ∧ rootD q < rootB q := by
  have hs : 2 * q ≤ q ^ 2 := by nlinarith
  unfold rootA rootB rootC rootD
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma family_sum_gap (q : ℤ) :
    rootA q + rootB q - rootC q - rootD q = -2 * q ^ 2 := by
  unfold rootA rootB rootC rootD
  ring

lemma family_no_third_lift (q : ℤ) (hq : 3 ≤ q) :
    ¬ q ^ 3 ∣ rootA q + rootB q - rootC q - rootD q := by
  rw [family_sum_gap]
  intro h
  have hq0 : q ^ 2 ≠ 0 := pow_ne_zero _ (by omega)
  have hh : q ^ 2 * q ∣ q ^ 2 * (-2) := by
    convert h using 1 <;> ring
  have hh' := (mul_dvd_mul_iff_left hq0).mp hh
  have h2 : q ∣ 2 := by simpa using dvd_neg.mp hh'
  have := Int.le_of_dvd (by norm_num : (0 : ℤ) < 2) h2
  omega

lemma family_not_sidon (q : ℤ) (hq : 2 ≤ q) :
    ¬ IsSidon ({rootA q ^ 2, rootB q ^ 2, rootC q ^ 2, rootD q ^ 2} : Set ℤ) := by
  intro hs
  obtain ⟨hA, hAC, hCD, hDB⟩ := family_order q hq
  have hh := hs (rootA q ^ 2) (by simp) (rootC q ^ 2) (by simp)
    (rootB q ^ 2) (by simp) (rootD q ^ 2) (by simp) (family_collision q)
  rcases hh with hh | hh <;> nlinarith [hh.1]

/-- A convenient unbounded class of odd moduli. -/
def familyModulus (t : ℕ) : ℤ := 9282 * t + 4641

private lemma isCoprime_of_one_mod (a k : ℤ) (h : k ∣ a - 1) :
    IsCoprime a k := by
  obtain ⟨v, hv⟩ := h
  exact ⟨1, -v, by linear_combination hv⟩

private lemma isCoprime_of_linear_certificate (a b k u v : ℤ)
    (hcop : IsCoprime a k) (he : u * a + v * b = k) :
    IsCoprime a b := by
  obtain ⟨s, t, ht⟩ := hcop
  refine ⟨s + t * u, t * v, ?_⟩
  linear_combination ht + t * he

lemma familyModulus_unit (t : ℕ) :
    3 ≤ familyModulus t ∧ IsCoprime (familyModulus t) 2 := by
  constructor
  · unfold familyModulus
    omega
  · exact ⟨1, -(4641 * t + 2320), by unfold familyModulus; ring⟩

/-- The failure of further lifting persists with pairwise coprime roots. -/
lemma family_pairwise_coprime (t : ℕ) :
    IsCoprime (rootA (familyModulus t)) (rootB (familyModulus t)) ∧
    IsCoprime (rootA (familyModulus t)) (rootC (familyModulus t)) ∧
    IsCoprime (rootA (familyModulus t)) (rootD (familyModulus t)) ∧
    IsCoprime (rootB (familyModulus t)) (rootC (familyModulus t)) ∧
    IsCoprime (rootB (familyModulus t)) (rootD (familyModulus t)) ∧
    IsCoprime (rootC (familyModulus t)) (rootD (familyModulus t)) := by
  let q := familyModulus t
  have hA17 : IsCoprime (rootA q) 17 := by
    apply isCoprime_of_one_mod
    rw [Int.dvd_iff_emod_eq_zero]
    norm_num [rootA, q, familyModulus, Int.add_emod, Int.sub_emod,
      Int.mul_emod, pow_two]
  have hA7 : IsCoprime (rootA q) 7 := by
    apply isCoprime_of_one_mod
    rw [Int.dvd_iff_emod_eq_zero]
    norm_num [rootA, q, familyModulus, Int.add_emod, Int.sub_emod,
      Int.mul_emod, pow_two]
  have hB6 : IsCoprime (rootB q) 6 := by
    apply isCoprime_of_one_mod
    rw [Int.dvd_iff_emod_eq_zero]
    norm_num [rootB, q, familyModulus, Int.add_emod, Int.sub_emod,
      Int.mul_emod, pow_two]
  have hC13 : IsCoprime (rootC q) 13 := by
    apply isCoprime_of_one_mod
    rw [Int.dvd_iff_emod_eq_zero]
    norm_num [rootC, q, familyModulus, Int.add_emod, Int.sub_emod,
      Int.mul_emod, pow_two]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply isCoprime_of_linear_certificate _ _ 17 (198 * q + 91) (-44 * q - 74) hA17
    unfold rootA rootB
    ring
  · refine ⟨9 * q + 6, -3 * q - 5, ?_⟩
    unfold rootA rootC
    ring
  · apply isCoprime_of_linear_certificate _ _ 7 (-126 * q - 55) (36 * q + 62) hA7
    unfold rootA rootD
    ring
  · refine ⟨-24 * q - 18, 36 * q + 19, ?_⟩
    unfold rootB rootC
    ring
  · apply isCoprime_of_linear_certificate _ _ 6 (-14 * q - 17) (18 * q + 23) hB6
    unfold rootB rootD
    ring
  · apply isCoprime_of_linear_certificate _ _ 13 (-84 * q - 53) (72 * q + 66) hC13
    unfold rootC rootD
    ring

#print axioms family_pairwise_coprime
#print axioms pair_sum_lift
#print axioms pairs_identified_of_small_sum_gap
#print axioms family_no_third_lift
#print axioms family_not_sidon
end Erdos773.UnitResidueLift
