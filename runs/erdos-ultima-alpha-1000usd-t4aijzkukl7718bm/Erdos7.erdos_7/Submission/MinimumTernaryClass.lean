import Submission.SingleExceptionCompression
import Submission.PrivateRefinementIsolation

/-!
# The ternary class in globally minimum-cardinality odd covers

Restriction to a ternary residue and single-exception compression constrain
isolated classes. All conclusions are conditional on an odd cover; no odd
cover is constructed unconditionally here.
-/
namespace Erdos7MinimumTernaryClass
open Erdos7Reduction Erdos7SingleExceptionCompression
open Erdos7PrivateReplacement
set_option maxHeartbeats 4000000

/-- Package an arithmetic cover with its positive least common period. -/
lemma has_period {I : Type} [Fintype I] (m : I → ℕ) (a : I → ℤ)
    (hc : IsOddArithmeticCover m a) :
    ∃ N, HasOddArithmeticCover N (Fintype.card I) := by
  classical
  let N := Finset.univ.lcm m
  have hn : N ≠ 0 := Finset.lcm_ne_zero_iff.mpr (by
    intro i _
    have := (hc.2.1 i).1
    omega)
  exact ⟨N, Nat.pos_of_ne_zero hn, I, inferInstance, m, a,
    hc.1, hc.2.1, hc.2.2, fun i => Finset.dvd_lcm (Finset.mem_univ i), le_rfl⟩

/-- Pull a class with no factor 3 back along an affine ternary progression. -/
lemma affine_residue (m : ℕ) (hm : ¬ 3 ∣ m) (a r : ℤ) :
    ∃ b : ℤ, ∀ x : ℤ, (m : ℤ) ∣ 3*x+r-a → (m : ℤ) ∣ x-b := by
  have hcp : IsCoprime (3 : ℤ) (m : ℤ) :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr hm).isCoprime
  obtain ⟨u,v,hu⟩ := hcp
  refine ⟨u*(a-r),fun x hx => ?_⟩
  obtain ⟨t,ht⟩ := hx
  refine ⟨u*t+v*x,?_⟩
  nlinarith [congrArg (fun z : ℤ => z*x) hu,
    congrArg (fun z : ℤ => u*z) ht]

/-- The no-3 classes of a cover restrict injectively with unchanged moduli. -/
lemma restrict_base {I : Type*} (m : I → ℕ) (a : I → ℤ) (r : ℤ) :
    ∃ b : {i // ¬ 3 ∣ m i} → ℤ,
      ∀ i : {i // ¬ 3 ∣ m i}, ∀ x : ℤ,
        (m i : ℤ) ∣ 3*x+r-a i → (m i : ℤ) ∣ x-b i := by
  classical
  choose b hb using fun i : {i // ¬ 3 ∣ m i} =>
    affine_residue (m i) i.property (a i) r
  exact ⟨b,hb⟩

/-- Every ternary residue must contain a class whose modulus has a factor 3. -/
theorem every_ternary_residue {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a) (r : ℤ) :
    ∃ j, 3 ∣ m j ∧ (3 : ℤ) ∣ a j-r := by
  classical
  by_contra hn
  obtain ⟨b,hb⟩ := restrict_base m a r
  have hnew : IsOddArithmeticCover (fun i : {i // ¬ 3 ∣ m i} => m i) b := by
    refine ⟨hc.1.comp Subtype.val_injective,fun i => hc.2.1 i,?_⟩
    intro x
    obtain ⟨j,hj⟩ := hc.2.2 (3*x+r)
    have hj3 : ¬ 3 ∣ m j := by
      intro hj3
      have h3 : (3 : ℤ) ∣ (m j : ℤ) := by exact_mod_cast hj3
      have hh := h3.trans hj
      apply hn
      exact ⟨j,hj3,by omega⟩
    exact ⟨⟨j,hj3⟩,hb ⟨j,hj3⟩ x hj⟩
  obtain ⟨j,hj⟩ := Erdos7No23Sieve.arithmetic_exists_three _ _ hnew
  exact j.property hj

/-- In particular at least two distinct labels have a factor 3. -/
lemma another_ternary_label {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a) (j : I) :
    ∃ k, k ≠ j ∧ 3 ∣ m k := by
  obtain ⟨k,hk,ha⟩ := every_ternary_residue m a hc (a j+1)
  refine ⟨k,?_,hk⟩
  intro h
  subst k
  omega

/-- Global cardinality minimality entails private points for every label. -/
lemma global_minimum_private {I : Type} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hmin : ∀ N K, HasOddArithmeticCover N K → Fintype.card I ≤ K) :
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
  have hc' : IsOddArithmeticCover (fun k : {k // k ≠ j} => m k)
      (fun k => a k) := by
    refine ⟨hc.1.comp Subtype.val_injective,fun k => hc.2.1 k,?_⟩
    intro x
    obtain ⟨k,hkj,hk⟩ := hcover x
    exact ⟨⟨k,hkj⟩,hk⟩
  obtain ⟨N,hN⟩ := has_period _ _ hc'
  have hle : Fintype.card I ≤ Fintype.card {k : I // k ≠ j} := hmin N _ hN
  have hlt := Fintype.card_subtype_lt (p := fun k : I => k ≠ j) (x := j) (by simp)
  simp only [Fintype.card_subtype] at hle hlt
  omega

/-- A class isolated in its ternary residue restricts to one exceptional class. -/
lemma isolated_restriction {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (j : I) (d : ℕ) (hjd : m j = 3*d)
    (hiso : ∀ k, k ≠ j → 3 ∣ m k → ¬ (3 : ℤ) ∣ a k-a j) :
    ∃ b : {i // ¬ 3 ∣ m i} → ℤ,
      ∀ x : ℤ, (∃ i : {i // ¬ 3 ∣ m i}, (m i : ℤ) ∣ x-b i) ∨ (d : ℤ) ∣ x := by
  classical
  obtain ⟨b,hb⟩ := restrict_base m a (a j)
  refine ⟨b,fun x => ?_⟩
  obtain ⟨k,hk⟩ := hc.2.2 (3*x+a j)
  by_cases hk3 : 3 ∣ m k
  · have h3 : (3 : ℤ) ∣ (m k : ℤ) := by exact_mod_cast hk3
    have ha := h3.trans hk
    have hkj : k=j := by
      by_contra h
      exact hiso k h hk3 (by omega)
    subst k
    right
    obtain ⟨t,ht⟩ := hk
    refine ⟨t,?_⟩
    rw [hjd] at ht
    push_cast at ht
    nlinarith
  · exact Or.inl ⟨⟨k,hk3⟩,hb ⟨k,hk3⟩ x hk⟩

/-- A globally minimum-cardinality odd cover has no isolated ternary class
with modulus strictly greater than 3. -/
theorem isolated_ternary_modulus {I : Type} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hmin : ∀ N K, HasOddArithmeticCover N K → Fintype.card I ≤ K)
    (j : I) (hj3 : 3 ∣ m j)
    (hiso : ∀ k, k ≠ j → 3 ∣ m k → ¬ (3 : ℤ) ∣ a k-a j) :
    m j = 3 := by
  classical
  by_contra hjne
  obtain ⟨d,hjd⟩ := hj3
  have hd : 1 < d ∧ Odd d := by
    have hm := hc.2.1 j
    refine ⟨by omega,?_⟩
    exact hm.2.of_dvd_nat (hjd ▸ dvd_mul_left d 3)
  obtain ⟨b,hb⟩ := isolated_restriction m a hc j d hjd hiso
  let K := {i : I // ¬ 3 ∣ m i}
  have h3j : 3 ∣ m j := ⟨d,hjd⟩
  have hlt : Fintype.card K < Fintype.card I :=
    Fintype.card_subtype_lt (x := j) (by simpa using h3j)
  by_cases hd3 : 3 ∣ d
  · let n : K ⊕ Unit → ℕ := Sum.elim (fun k => m k) (fun _ => d)
    let c : K ⊕ Unit → ℤ := Sum.elim b (fun _ => 0)
    have hnew : IsOddArithmeticCover n c := by
      refine ⟨?_,?_,?_⟩
      · intro u v huv
        cases u with
        | inl u =>
          cases v with
          | inl v => exact congrArg Sum.inl (Subtype.ext (hc.1 huv))
          | inr v => exact False.elim (u.property (by change m u = d at huv; rw [huv]; exact hd3))
        | inr u =>
          cases v with
          | inl v => exact False.elim (v.property (by change d = m v at huv; rw [← huv]; exact hd3))
          | inr v => cases u; cases v; rfl
      · intro u
        cases u with
        | inl u => exact hc.2.1 u
        | inr u => exact hd
      · intro x
        rcases hb x with ⟨i,hi⟩ | hi
        · exact ⟨Sum.inl i,hi⟩
        · exact ⟨Sum.inr (),by simpa [c] using hi⟩
    obtain ⟨N,hN⟩ := has_period n c hnew
    have hle : Fintype.card I ≤ Fintype.card (K ⊕ Unit) := hmin N _ hN
    obtain ⟨k,hkj,hk3⟩ := another_ternary_label m a hc j
    have htwo : 1 < Fintype.card {i : I // 3 ∣ m i} :=
      Fintype.one_lt_card_iff.mpr ⟨⟨k,hk3⟩,⟨j,h3j⟩,fun h => hkj (congrArg Subtype.val h)⟩
    have htwoI : 1 < Fintype.card I := Fintype.one_lt_card_iff.mpr ⟨k,j,hkj⟩
    have heq := Fintype.card_subtype_compl (fun i => 3 ∣ m i)
    change Fintype.card K = _ at heq
    simp only [Fintype.card_sum,Fintype.card_unit] at hle
    simp only [Fintype.card_subtype] at heq htwo hlt
    omega
  · obtain ⟨n,c,hnew⟩ := odd_cover_from_single_exception
      (fun i : K => m i) b (hc.1.comp Subtype.val_injective)
      (fun i => hc.2.1 i) (fun i => i.property) d hd hd3 0
      (by simpa only [sub_zero] using hb)
    obtain ⟨N,hN⟩ := has_period n c hnew
    have hle := hmin N _ hN
    omega

/-- The actual modulus 3, not merely a factor 3, occurs in every globally
minimum-cardinality odd cover. -/
theorem minimum_contains_three {I : Type} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hmin : ∀ N K, HasOddArithmeticCover N K → Fintype.card I ≤ K) :
    ∃ j, m j = 3 := by
  classical
  by_contra! hmissing
  obtain ⟨j,hj3⟩ := Erdos7No23Sieve.arithmetic_exists_three m a hc
  have hnew := (replace_modulus_by_divisor m a hc j 3 (by omega) hj3 hmissing).1
  have hp := global_minimum_private _ a hnew hmin
  have hiso : ∀ k, k ≠ j → 3 ∣ m k → ¬ (3 : ℤ) ∣ a k-a j := by
    intro k hkj hk3 ha
    obtain ⟨x,hx⟩ := hp k
    have hmx : (m k : ℤ) ∣ x-a k := by simpa [hkj] using hx.1
    have h3m : (3 : ℤ) ∣ (m k : ℤ) := by exact_mod_cast hk3
    have h3x := h3m.trans hmx
    apply hx.2 j (Ne.symm hkj)
    simpa using (dvd_add h3x ha)
  exact hmissing j (isolated_ternary_modulus m a hc hmin j hj3 hiso)

#print axioms every_ternary_residue
#print axioms isolated_ternary_modulus
#print axioms minimum_contains_three
end Erdos7MinimumTernaryClass
