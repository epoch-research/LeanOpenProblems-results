import Mathlib

/-!
# Uniqueness of sums from well-separated canonical layers

For any natural base `q ≥ 2`, not necessarily prime, write a positive integer
canonically as `q^j * u` with `q ∤ u`. If all coefficients lie in `[1, D]`,
and the two exponents in each sum satisfy `j < k` and `D < q^(k-j)`, equality
of two such sums identifies both exponents and both coefficients.

The argument uses only divisibility and remainders, not prime factorization.
In particular, there is no bound on, or constant depending on, the exponents.
Addition is therefore injective on the unordered far pairs (`Sym2 ℕ`), giving
`(farPairs A q D).card ≤ (A + A).card` for every finite `A`. A further corollary
states the bound using explicit exponent and coefficient functions on `A`.

This file is independent of `Submission.Spec` and the other submission files.
These are layer-separation results, not a proof of the unrestricted
sum-product conjecture or of a concentration statement.
-/

open scoped Pointwise

namespace Erdos52.LayerSeparation

/-- Canonical powers have unique exponents and coefficients, even for a
composite base. Nondivisibility of the coefficients implies they are positive. -/
theorem canonical_power_mul_unique {q j k u v : ℕ}
    (hq : 0 < q) (hu : ¬q ∣ u) (hv : ¬q ∣ v)
    (heq : q ^ j * u = q ^ k * v) : j = k ∧ u = v := by
  have hnot (i w : ℕ) (hw : ¬q ∣ w) : ¬q ^ (i + 1) ∣ q ^ i * w := by
    simpa only [pow_succ, Nat.mul_dvd_mul_iff_left (pow_pos hq i)] using hw
  have hjk : j = k := by
    rcases lt_trichotomy j k with h | h | h
    · exfalso
      apply hnot j u hu
      rw [heq]
      exact (pow_dvd_pow q (Nat.succ_le_of_lt h)).trans (dvd_mul_right _ _)
    · exact h
    · exfalso
      apply hnot k v hv
      rw [← heq]
      exact (pow_dvd_pow q (Nat.succ_le_of_lt h)).trans (dvd_mul_right _ _)
  subst k
  exact ⟨rfl, Nat.mul_left_cancel (pow_pos hq j) heq⟩

/-- Factor a layer sum by its lower power. -/
lemma factor_layer_sum {q j k u v : ℕ} (hjk : j ≤ k) :
    q ^ j * u + q ^ k * v = q ^ j * (u + q ^ (k - j) * v) := by
  rw [mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hjk]

/-- Adding a term from a strictly higher layer preserves nondivisibility
of the normalized lower coefficient. No primality assumption is needed. -/
lemma not_dvd_normalized_layer_sum {q j k u v : ℕ}
    (hjk : j < k) (hu : ¬q ∣ u) : ¬q ∣ u + q ^ (k - j) * v := by
  have hpow : q ∣ q ^ (k - j) := by
    simpa only [pow_one] using pow_dvd_pow q (show 1 ≤ k - j by omega)
  have hd : q ∣ q ^ (k - j) * v := hpow.trans (dvd_mul_right _ _)
  exact fun h => hu ((Nat.dvd_add_iff_left hd).mpr h)

/-- If one modulus divides the other, equality of the two sums identifies
lower terms that are both smaller than the first modulus. -/
lemma small_part_eq_of_dvd {a b u u' v v' : ℕ}
    (hu : u < a) (hu' : u' < a) (hab : a ∣ b)
    (heq : u + a * v = u' + b * v') : u = u' := by
  have hm : (u + a * v) % a = (u' + b * v') % a :=
    congrArg (fun n => n % a) heq
  have hb : (b * v') % a = 0 :=
    Nat.mod_eq_zero_of_dvd (hab.trans (dvd_mul_right _ _))
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu] at hm
  simpa only [Nat.add_mod, hb, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hu'] using hm

/-- **Far-layer sum uniqueness.** All parameters are natural numbers.
Each coefficient is positive, at most `D`, and not divisible by `q`.
In each representation the exponents are strictly increasing, with
`q^(upper - lower) > D`. Equality of the sums then identifies the entire
representation. The base `q ≥ 2` need not be prime. -/
theorem far_layer_sum_unique {q D j k j' k' u v u' v' : ℕ}
    (hq : 2 ≤ q)
    (hu : 0 < u ∧ u ≤ D ∧ ¬q ∣ u)
    (hv : 0 < v ∧ v ≤ D ∧ ¬q ∣ v)
    (hu' : 0 < u' ∧ u' ≤ D ∧ ¬q ∣ u')
    (hv' : 0 < v' ∧ v' ≤ D ∧ ¬q ∣ v')
    (hjk : j < k) (hjk' : j' < k')
    (hgap : D < q ^ (k - j)) (hgap' : D < q ^ (k' - j'))
    (hsum : q ^ j * u + q ^ k * v = q ^ j' * u' + q ^ k' * v') :
    j = j' ∧ u = u' ∧ k = k' ∧ v = v' := by
  have hqpos : 0 < q := by omega
  have hfactor : q ^ j * (u + q ^ (k - j) * v) =
      q ^ j' * (u' + q ^ (k' - j') * v') := by
    rw [← factor_layer_sum hjk.le, ← factor_layer_sum hjk'.le]
    exact hsum
  obtain ⟨hj, hnormalized⟩ := canonical_power_mul_unique hqpos
    (not_dvd_normalized_layer_sum hjk hu.2.2)
    (not_dvd_normalized_layer_sum hjk' hu'.2.2) hfactor
  subst j'
  have huu' : u = u' := by
    rcases le_total k k' with hkk' | hk'k
    · exact small_part_eq_of_dvd (hu.2.1.trans_lt hgap) (hu'.2.1.trans_lt hgap)
        (pow_dvd_pow q (Nat.sub_le_sub_right hkk' j)) hnormalized
    · exact (small_part_eq_of_dvd (hu'.2.1.trans_lt hgap') (hu.2.1.trans_lt hgap')
        (pow_dvd_pow q (Nat.sub_le_sub_right hk'k j)) hnormalized.symm).symm
  subst u'
  have hhigh : q ^ k * v = q ^ k' * v' := Nat.add_left_cancel hsum
  obtain ⟨hk, hvv'⟩ := canonical_power_mul_unique hqpos hv.2.2 hv'.2.2 hhigh
  exact ⟨rfl, rfl, hk, hvv'⟩

/-- An unordered pair has far-separated canonical layers if it admits
an orientation with lower exponent `j < k`, bounded canonical coefficients,
and `D < q^(k-j)`. The equality in `Sym2` makes the definition independent
of the order in which the pair is presented. -/
def IsFarPair (q D : ℕ) (p : Sym2 ℕ) : Prop :=
  ∃ j k u v : ℕ,
    (0 < u ∧ u ≤ D ∧ ¬q ∣ u) ∧
    (0 < v ∧ v ≤ D ∧ ¬q ∣ v) ∧
    j < k ∧ D < q ^ (k - j) ∧ p = s(q ^ j * u, q ^ k * v)

/-- Addition is injective on all unordered far-separated canonical pairs,
without any height restriction on their exponents. -/
theorem sum_injOn_isFarPair {q D : ℕ} (hq : 2 ≤ q) :
    Set.InjOn (Sym2.add : Sym2 ℕ → ℕ) {p | IsFarPair q D p} := by
  intro p hp p' hp' heq
  rcases hp with ⟨j, k, u, v, hu, hv, hjk, hgap, rfl⟩
  rcases hp' with ⟨j', k', u', v', hu', hv', hjk', hgap', rfl⟩
  change q ^ j * u + q ^ k * v = q ^ j' * u' + q ^ k' * v' at heq
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    far_layer_sum_unique hq hu hv hu' hv' hjk hjk' hgap hgap' heq
  rfl

/-- The finite set of unordered far pairs in `A`. This uses actual
unordered pairs (`Sym2`), rather than counting both orientations. -/
noncomputable def farPairs (A : Finset ℕ) (q D : ℕ) : Finset (Sym2 ℕ) := by
  classical
  exact A.sym2.filter (IsFarPair q D)

@[simp]
theorem mem_farPairs {A : Finset ℕ} {q D : ℕ} {p : Sym2 ℕ} :
    p ∈ farPairs A q D ↔ p ∈ A.sym2 ∧ IsFarPair q D p := by
  classical
  exact Finset.mem_filter

/-- Injectivity of addition restricted to the unordered far pairs in `A`. -/
theorem farPairs_add_injOn (A : Finset ℕ) {q D : ℕ} (hq : 2 ≤ q) :
    Set.InjOn (Sym2.add : Sym2 ℕ → ℕ) (farPairs A q D) := by
  intro p hp p' hp' heq
  exact sum_injOn_isFarPair hq (mem_farPairs.mp hp).2 (mem_farPairs.mp hp').2 heq

/-- The number of unordered far-separated canonical pairs is at most
`|A + A|`. No representation hypothesis on the other elements of `A` is
needed: membership in `farPairs` already requires bounded canonical
coefficients for both endpoints. In particular, this applies when every
element of `A` has such a representation. -/
theorem farPairs_card_le_sumset_card (A : Finset ℕ) {q D : ℕ} (hq : 2 ≤ q) :
    (farPairs A q D).card ≤ (A + A).card := by
  apply Finset.card_le_card_of_injOn Sym2.add
  · intro p hp
    obtain ⟨hpA, hpFar⟩ := mem_farPairs.mp hp
    rcases hpFar with ⟨j, k, u, v, _, _, _, _, rfl⟩
    obtain ⟨ha, hb⟩ := Finset.mk_mem_sym2_iff.mp hpA
    exact Finset.mem_add.mpr ⟨q ^ j * u, ha, q ^ k * v, hb, rfl⟩
  · exact farPairs_add_injOn A hq

/-- An explicit representation-based version of the unordered-pair bound.
Suppose `a = q^(e a) * c a` for every `a ∈ A`, with `c a` positive, at most
`D`, and not divisible by `q`. Select the pairs with increasing exponents
and `D < q^(e b - e a)`, then forget their orientation using `Sym2.mk`.
The number of resulting unordered pairs is at most `|A + A|`.
There is no hypothesis bounding `e`, and the constant is exactly one. -/
theorem card_far_pairs_of_representation_le (A : Finset ℕ) {q D : ℕ}
    (e c : ℕ → ℕ) (hq : 2 ≤ q)
    (hcoeff : ∀ a ∈ A, 0 < c a ∧ c a ≤ D ∧ ¬q ∣ c a)
    (hrepr : ∀ a ∈ A, a = q ^ (e a) * c a) :
    (((A ×ˢ A).filter fun ab =>
      e ab.1 < e ab.2 ∧ D < q ^ (e ab.2 - e ab.1)).image Sym2.mk).card ≤
        (A + A).card := by
  classical
  refine (Finset.card_le_card ?_).trans (farPairs_card_le_sumset_card (D := D) A hq)
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨⟨a, b⟩, hab, rfl⟩
  obtain ⟨habA, hlt, hgap⟩ := Finset.mem_filter.mp hab
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp habA
  apply mem_farPairs.mpr
  refine ⟨Finset.mk_mem_sym2_iff.mpr ⟨ha, hb⟩, ?_⟩
  refine ⟨e a, e b, c a, c b, hcoeff a ha, hcoeff b hb, hlt, hgap, ?_⟩
  exact congrArg Sym2.mk (Prod.ext (hrepr a ha) (hrepr b hb))

end Erdos52.LayerSeparation

#print axioms Erdos52.LayerSeparation.canonical_power_mul_unique
#print axioms Erdos52.LayerSeparation.factor_layer_sum
#print axioms Erdos52.LayerSeparation.not_dvd_normalized_layer_sum
#print axioms Erdos52.LayerSeparation.small_part_eq_of_dvd
#print axioms Erdos52.LayerSeparation.far_layer_sum_unique
#print axioms Erdos52.LayerSeparation.sum_injOn_isFarPair
#print axioms Erdos52.LayerSeparation.mem_farPairs
#print axioms Erdos52.LayerSeparation.farPairs_add_injOn
#print axioms Erdos52.LayerSeparation.farPairs_card_le_sumset_card
#print axioms Erdos52.LayerSeparation.card_far_pairs_of_representation_le
