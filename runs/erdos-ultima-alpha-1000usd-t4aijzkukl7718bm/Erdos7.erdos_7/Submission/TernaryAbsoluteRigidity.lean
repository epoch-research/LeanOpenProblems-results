import Submission.NoThreeHoleSpan

/-!
# Ternary rigidity without global cardinality minimality

These are consequences of the absolute one-exception sieve, not a settlement
of the odd covering problem.
-/
namespace Erdos7TernaryAbsoluteRigidity
open Erdos7Reduction Erdos7PrivateReplacement
open Erdos7NoThreeHoleSpan
set_option maxHeartbeats 4000000

/-- Fixed-period cardinality minimality supplies private points. -/
lemma fixed_minimum_private {I : Type} [Fintype I]
    (N : ℕ) (hN : 0 < N) (m : I → ℕ) (a : I → ℤ)
    (hc : IsOddArithmeticCover m a) (hperiod : ∀ i, m i ∣ N)
    (hmin : ∀ K, HasOddArithmeticCover N K → Fintype.card I ≤ K) :
    ∀ j, ∃ x, Private m a j x := by
  classical
  intro j
  by_contra hn
  have hcover : ∀ x : ℤ, ∃ k, k ≠ j ∧ (m k : ℤ) ∣ x-a k := by
    intro x
    by_contra hx
    apply hn
    obtain ⟨k,hk⟩ := hc.2.2 x
    have hkj : k=j := by by_contra h; exact hx ⟨k,h,hk⟩
    subst k
    exact ⟨x,hk,fun k hkj hk => hx ⟨k,hkj,hk⟩⟩
  have hnew : HasOddArithmeticCover N (Fintype.card {k : I // k≠j}) := by
    refine ⟨hN,{k : I // k≠j},inferInstance,(fun k => m k),(fun k => a k),
      hc.1.comp Subtype.val_injective,(fun k => hc.2.1 k),?_,(fun k => hperiod k),le_rfl⟩
    intro x
    obtain ⟨k,hkj,hk⟩ := hcover x
    exact ⟨⟨k,hkj⟩,hk⟩
  have hle := hmin _ hnew
  have hlt := Fintype.card_subtype_lt (p := fun k : I => k≠j) (x := j) (by simp)
  simp only [Fintype.card_subtype] at hle hlt
  omega

/-- Every fixed-period minimum-cardinality odd cover contains actual modulus3. -/
theorem fixed_minimum_contains_three {I : Type} [Fintype I]
    (N : ℕ) (hN : 0 < N) (m : I → ℕ) (a : I → ℤ)
    (hc : IsOddArithmeticCover m a) (hperiod : ∀ i, m i ∣ N)
    (hmin : ∀ K, HasOddArithmeticCover N K → Fintype.card I ≤ K) :
    ∃ j, m j=3 := by
  classical
  by_contra! hmissing
  obtain ⟨j,hj3⟩ := Erdos7No23Sieve.arithmetic_exists_three m a hc
  have hnew := (replace_modulus_by_divisor m a hc j 3 (by omega) hj3 hmissing).1
  have hpnew : ∀ k, Function.update m j 3 k ∣ N := by
    intro k
    by_cases hk : k=j
    · subst k; simpa using hj3.trans (hperiod j)
    · simpa [hk] using hperiod k
  have hp := fixed_minimum_private N hN _ a hnew hpnew hmin
  have hiso : ∀ k, k ≠ j → 3 ∣ m k → ¬ (3 : ℤ) ∣ a k-a j := by
    intro k hkj hk3 ha
    obtain ⟨x,hx⟩ := hp k
    have hmx : (m k : ℤ) ∣ x-a k := by simpa [hkj] using hx.1
    have h3x := (Int.natCast_dvd_natCast.mpr hk3).trans hmx
    apply hx.2 j (Ne.symm hkj)
    simpa using dvd_add h3x ha
  exact hmissing j (isolated_ternary_modulus m a hc j hj3 hiso)

/-- An invertible affine restriction is an equivalence, not just an implication. -/
lemma affine_hit_iff (m : ℕ) (hm : ¬ 3 ∣ m) (a r : ℤ) :
    ∃ b : ℤ, ∀ x : ℤ, (m : ℤ) ∣ 3*x+r-a ↔ (m : ℤ) ∣ x-b := by
  have hcp : IsCoprime (3 : ℤ) (m : ℤ) :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr hm).isCoprime
  obtain ⟨u,v,hu⟩ := hcp
  refine ⟨u*(a-r),fun x => ⟨?_,?_⟩⟩
  · rintro ⟨t,ht⟩
    refine ⟨u*t+v*x,?_⟩
    nlinarith [congrArg (fun z : ℤ => z*x) hu,
      congrArg (fun z : ℤ => u*z) ht]
  · rintro ⟨t,ht⟩
    refine ⟨3*t-v*(a-r),?_⟩
    nlinarith [congrArg (fun z : ℤ => z*(a-r)) hu]

/-- In an irredundant family, the ternary class is disjoint from every other
class with a factor3. Coverage of the whole family is not needed here. -/
lemma ternary_separated {I : Type*} (m : I → ℕ) (a : I → ℤ)
    (hprivate : ∀ j, ∃ x, Private m a j x) (i : I) (hi : m i=3) :
    ∀ j, j≠i → 3 ∣ m j → ¬ (3 : ℤ) ∣ a j-a i := by
  intro j hji hj3 ha
  obtain ⟨x,hx⟩ := hprivate j
  have hh := (Int.natCast_dvd_natCast.mpr hj3).trans hx.1
  apply hx.2 i (Ne.symm hji)
  rw [hi]
  simpa only [sub_add_sub_cancel] using dvd_add hh ha

/-- Private points of an irredundant ternary class are exactly the pulled-back
holes of the no-3 subfamily. -/
lemma private_iff_hole {I : Type*} (m : I → ℕ) (a : I → ℤ)
    (hprivate : ∀ j, ∃ x, Private m a j x) (i : I) (hi : m i=3) :
    ∃ b : {j // ¬ 3 ∣ m j} → ℤ, ∀ x : ℤ,
      Private m a i (3*x+a i) ↔ Hole (fun j : {j // ¬ 3 ∣ m j} => m j) b x := by
  classical
  choose b hb using fun j : {j // ¬ 3 ∣ m j} =>
    affine_hit_iff (m j) j.property (a j) (a i)
  refine ⟨b,fun x => ⟨?_,?_⟩⟩
  · intro hx j hj
    have hji : (j : I)≠i := by intro h; exact j.property (by rw [h,hi])
    exact hx.2 j hji ((hb j x).mpr hj)
  · intro hx
    refine ⟨?_,?_⟩
    · rw [hi]; exact ⟨x,by ring⟩
    · intro j hji hj
      by_cases hj3 : 3 ∣ m j
      · apply ternary_separated m a hprivate i hi j hji hj3
        have hh := (Int.natCast_dvd_natCast.mpr hj3).trans hj
        omega
      · exact hx ⟨j,hj3⟩ ((hb ⟨j,hj3⟩ x).mp hj)

/-- Even for a partial irredundant odd family, differences of private points of
its ternary class have no common natural divisor not dividing3. -/
theorem private_difference_divisor {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ j, 1 < m j ∧ Odd (m j)) (hprivate : ∀ j, ∃ x, Private m a j x)
    (i : I) (hi : m i=3) (d : ℕ)
    (hspan : ∀ x y : ℤ, Private m a i x → Private m a i y → (d : ℤ) ∣ x-y) :
    d ∣ 3 := by
  classical
  obtain ⟨b,hb⟩ := private_iff_hole m a hprivate i hi
  have hmul : ∀ x y : ℤ,
      Hole (fun j : {j // ¬ 3 ∣ m j} => m j) b x →
      Hole (fun j : {j // ¬ 3 ∣ m j} => m j) b y → (d : ℤ) ∣ 3*(x-y) := by
    intro x y hx hy
    convert hspan (3*x+a i) (3*y+a i) ((hb x).mpr hx) ((hb y).mpr hy) using 1 <;> ring
  by_cases hd3 : 3 ∣ d
  · obtain ⟨e,he⟩ := hd3
    have heq : e=1 := by
      apply hole_difference_divisor (fun j : {j // ¬ 3 ∣ m j} => m j) b
        (hinj.comp Subtype.val_injective) (fun j => hm j) (fun j => j.property) e
      intro x y hx hy
      obtain ⟨t,ht⟩ := hmul x y hx hy
      refine ⟨t,?_⟩
      rw [he] at ht
      push_cast at ht
      nlinarith
    rw [he,heq]
  · have hcp : IsCoprime (d : ℤ) (3 : ℤ) :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr hd3).symm.isCoprime
    have heq : d=1 := by
      apply hole_difference_divisor (fun j : {j // ¬ 3 ∣ m j} => m j) b
        (hinj.comp Subtype.val_injective) (fun j => hm j) (fun j => j.property) d
      intro x y hx hy
      exact hcp.dvd_of_dvd_mul_left (hmul x y hx hy)
    rw [heq]
    exact one_dvd _

/-- The affine arithmetic span of the ternary class's private points is its
full original progression. No cardinality minimality or full coverage is used. -/
theorem private_residue_iff {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ j, 1 < m j ∧ Odd (m j)) (hprivate : ∀ j, ∃ x, Private m a j x)
    (i : I) (hi : m i=3) (d : ℕ) (b : ℤ) :
    (∀ x, Private m a i x → (d : ℤ) ∣ x-b) ↔ d ∣ 3 ∧ (d : ℤ) ∣ a i-b := by
  constructor
  · intro hh
    have hd := private_difference_divisor m a hinj hm hprivate i hi d (by
      intro x y hx hy
      convert dvd_sub (hh x hx) (hh y hy) using 1 <;> ring)
    refine ⟨hd,?_⟩
    obtain ⟨x,hx⟩ := hprivate i
    have hdx : (d : ℤ) ∣ x-a i :=
      (Int.natCast_dvd_natCast.mpr (by simpa only [hi] using hd)).trans hx.1
    convert dvd_sub (hh x hx) hdx using 1 <;> ring
  · rintro ⟨hd,ha⟩ x hx
    have hdx : (d : ℤ) ∣ x-a i :=
      (Int.natCast_dvd_natCast.mpr (by simpa only [hi] using hd)).trans hx.1
    simpa only [sub_add_sub_cancel] using dvd_add hdx ha

#print axioms fixed_minimum_contains_three
#print axioms private_difference_divisor
#print axioms private_residue_iff
end Erdos7TernaryAbsoluteRigidity
