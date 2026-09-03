import Submission.CarmichaelAlgebra
import Submission.CarmichaelReduction

/-!
# Finite product-one subset counting and the actual Carmichael count

The combinatorial results below assume an explicit product-one extraction
hypothesis.  They do not assume or assert an unconditional Davenport bound or
any asymptotic statement about Carmichael numbers.

The counting argument encodes each `t`-element subset as the union of a good
subset and a remainder of size less than `D`.  Consequently the number of
`t`-element subsets is at most the number of good subsets times
`∑ j ∈ Finset.range D, P.card.choose j`.

## Main results

* `choose_le_smallSubsets_mul_goodSubsets`: the general finite counting lemma
  for any predicate closed under disjoint unions and true of the empty set.
* `choose_le_mul_card_product_one` and `choose_le_mul_card_modEq`: its
  commutative-monoid and natural-congruence specializations.
* `goodSubset_carmichael_and_le` and `prod_injOn_prime_subsets`: every selected
  prime subset gives a Carmichael number below the cutoff, without collisions.
* `choose_le_mul_count_of_modEq`, `choose_le_mul_C_of_modEq`, and
  `choose_div_le_C_of_modEq`: the quantitative bounds for the original count.
* `choose_le_mul_C_of_coprime_moduli` and
  `choose_div_le_C_of_coprime_moduli`: the original `k, L` formulation via CRT.

No hypothesis `t ≤ P.card` is needed for the inequalities (the numerator is
zero otherwise).  The finite count needs only `D ≤ t`; the Carmichael step
needs `D + 1 ≤ t`.  The divided bounds additionally assume `1 ≤ D`.

Only the two existing scratch files are imported.  They both use
`FormalConjecturesUtil`, the unchanged import of `Spec.lean`, and `C` is
exactly the original set-cardinality definition.  `Spec.lean` is not imported.
-/

open scoped BigOperators

namespace CarmichaelSubsetCounting

section FiniteCounting

variable {α : Type*}

/-- Subsets of `P` of size less than `D`, used to encode the remainders. -/
def smallSubsets (P : Finset α) (D : ℕ) : Finset (Finset α) :=
  P.powerset.filter (fun R => R.card < D)

/-- The good subsets whose cardinalities lie in the required interval. -/
noncomputable def goodSubsets (P : Finset α) (Q : Finset α → Prop) (D t : ℕ) :
    Finset (Finset α) := by
  classical
  exact P.powerset.filter (fun U => Q U ∧ t - D + 1 ≤ U.card ∧ U.card ≤ t)

@[simp]
theorem mem_smallSubsets {P R : Finset α} {D : ℕ} :
    R ∈ smallSubsets P D ↔ R ⊆ P ∧ R.card < D := by
  simp [smallSubsets]

@[simp]
theorem mem_goodSubsets {P U : Finset α} {Q : Finset α → Prop} {D t : ℕ} :
    U ∈ goodSubsets P Q D t ↔
      U ⊆ P ∧ Q U ∧ t - D + 1 ≤ U.card ∧ U.card ≤ t := by
  classical
  simp [goodSubsets]

/-- There are exactly `∑ j < D, choose P.card j` possible remainders. -/
theorem card_smallSubsets (P : Finset α) (D : ℕ) :
    (smallSubsets P D).card = ∑ j ∈ Finset.range D, P.card.choose j := by
  classical
  have hfiber (j : ℕ) :
      P.powerset.filter (fun R => R.card = j) = P.powersetCard j := by
    ext R
    simp
  simpa only [Finset.mem_range, hfiber, Finset.card_powersetCard, smallSubsets] using
    (Finset.sum_card_fiberwise_eq_card_filter P.powerset (Finset.range D)
      Finset.card).symm

variable [DecidableEq α]

/-- Maximal disjoint-union packing: a good subset can leave fewer than `D`
elements.  This is the finite greedy-removal argument, expressed by choosing
a good subset of maximal cardinality. -/
theorem exists_good_subset_small_remainder
    {P : Finset α} {Q : Finset α → Prop} {D : ℕ}
    (hempty : Q ∅)
    (hunion : ∀ U V : Finset α, Disjoint U V → Q U → Q V → Q (U ∪ V))
    (hextract : ∀ S ⊆ P, D ≤ S.card → ∃ T ⊆ S, T.Nonempty ∧ Q T)
    {S : Finset α} (hSP : S ⊆ P) :
    ∃ U ⊆ S, Q U ∧ (S \ U).card < D := by
  classical
  let F := S.powerset.filter Q
  have hF : F.Nonempty := ⟨∅, by simp [F, hempty]⟩
  obtain ⟨U, hUF, hmax⟩ := F.exists_max_image Finset.card hF
  obtain ⟨hUS, hQU⟩ := Finset.mem_filter.mp hUF
  have hUS' : U ⊆ S := Finset.mem_powerset.mp hUS
  refine ⟨U, hUS', hQU, ?_⟩
  by_contra hsmall
  obtain ⟨T, hTR, hTne, hQT⟩ :=
    hextract (S \ U) (Finset.sdiff_subset.trans hSP) (by omega)
  have hUT : Disjoint U T := Finset.disjoint_sdiff.mono_right hTR
  have hUTF : U ∪ T ∈ F := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr
      (Finset.union_subset hUS' (hTR.trans Finset.sdiff_subset)),
      hunion U T hUT hQU hQT⟩
  have hle := hmax (U ∪ T) hUTF
  rw [Finset.card_union_of_disjoint hUT] at hle
  have hpos := Finset.card_pos.mpr hTne
  omega

/-- The abstract finite counting bound.  Only closure under disjoint unions
and an explicit nonempty-subset extraction hypothesis are used.

No upper bound on `t` is needed: if `P.card < t`, the left side is zero. -/
theorem choose_le_smallSubsets_mul_goodSubsets
    {P : Finset α} {Q : Finset α → Prop} {D t : ℕ}
    (hempty : Q ∅)
    (hunion : ∀ U V : Finset α, Disjoint U V → Q U → Q V → Q (U ∪ V))
    (hextract : ∀ S ⊆ P, D ≤ S.card → ∃ T ⊆ S, T.Nonempty ∧ Q T)
    (hDt : D ≤ t) :
    P.card.choose t ≤
      (∑ j ∈ Finset.range D, P.card.choose j) * (goodSubsets P Q D t).card := by
  classical
  let G := goodSubsets P Q D t
  let R := smallSubsets P D
  have hcover : P.powersetCard t ⊆
      (G ×ˢ R).image (fun UR => UR.1 ∪ UR.2) := by
    intro S hS
    obtain ⟨hSP, hSt⟩ := Finset.mem_powersetCard.mp hS
    obtain ⟨U, hUS, hQU, hrem⟩ :=
      exists_good_subset_small_remainder hempty hunion hextract hSP
    have hUcard : U.card ≤ t := hSt ▸ Finset.card_le_card hUS
    have hUlow : t - D + 1 ≤ U.card := by
      have hcard := Finset.card_sdiff_add_card_eq_card hUS
      omega
    have hUG : U ∈ G :=
      mem_goodSubsets.mpr ⟨hUS.trans hSP, hQU, hUlow, hUcard⟩
    have hRR : S \ U ∈ R :=
      mem_smallSubsets.mpr ⟨Finset.sdiff_subset.trans hSP, hrem⟩
    exact Finset.mem_image.mpr
      ⟨(U, S \ U), Finset.mem_product.mpr ⟨hUG, hRR⟩,
        Finset.union_sdiff_of_subset hUS⟩
  calc
    P.card.choose t = (P.powersetCard t).card := (Finset.card_powersetCard t P).symm
    _ ≤ ((G ×ˢ R).image (fun UR => UR.1 ∪ UR.2)).card := Finset.card_le_card hcover
    _ ≤ (G ×ˢ R).card := Finset.card_image_le
    _ = (∑ j ∈ Finset.range D, P.card.choose j) * (goodSubsets P Q D t).card := by
      rw [Finset.card_product]
      dsimp [G, R]
      rw [card_smallSubsets, Nat.mul_comm]

/-- Product-one version in any commutative monoid; in particular it applies
to a map into a finite abelian group or a group of units. -/
theorem choose_le_mul_card_product_one
    {G : Type*} [CommMonoid G] {P : Finset α} {f : α → G} {D t : ℕ}
    (hextract : ∀ S ⊆ P, D ≤ S.card →
      ∃ T ⊆ S, T.Nonempty ∧ (∏ a ∈ T, f a) = 1)
    (hDt : D ≤ t) :
    P.card.choose t ≤ (∑ j ∈ Finset.range D, P.card.choose j) *
      (goodSubsets P (fun U => (∏ a ∈ U, f a) = 1) D t).card := by
  apply choose_le_smallSubsets_mul_goodSubsets (by simp) _ hextract hDt
  intro U V hUV hU hV
  simp [Finset.prod_union hUV, hU, hV]

end FiniteCounting

/-- Congruence version of the finite subset-counting theorem. -/
theorem choose_le_mul_card_modEq
    {P : Finset ℕ} {M D t : ℕ}
    (hextract : ∀ S ⊆ P, D ≤ S.card →
      ∃ T ⊆ S, T.Nonempty ∧ Nat.ModEq M (∏ p ∈ T, p) 1)
    (hDt : D ≤ t) :
    P.card.choose t ≤ (∑ j ∈ Finset.range D, P.card.choose j) *
      (goodSubsets P (fun U => Nat.ModEq M (∏ p ∈ U, p) 1) D t).card := by
  apply choose_le_smallSubsets_mul_goodSubsets (by simp [Nat.ModEq]) _ hextract hDt
  intro U V hUV hU hV
  simpa only [Finset.prod_union hUV, one_mul] using hU.mul hV

/-- The denominator is positive as soon as `D ≥ 1`, since its `j = 0`
term is one. -/
theorem choose_sum_pos (N : ℕ) {D : ℕ} (hD : 1 ≤ D) :
    0 < ∑ j ∈ Finset.range D, N.choose j := by
  have h := Finset.single_le_sum (f := fun j => N.choose j)
    (fun j _ => Nat.zero_le (N.choose j))
    (Finset.mem_range.mpr (by omega : 0 < D))
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (by simpa only [Nat.choose_zero_right] using h)

/-- The lower cardinality cutoff is at least two under the hypothesis used
in the Carmichael construction. -/
theorem two_le_card_of_mem_goodSubsets
    {α : Type*} {P U : Finset α} {Q : Finset α → Prop} {D t : ℕ}
    (ht : D + 1 ≤ t) (hU : U ∈ goodSubsets P Q D t) : 2 ≤ U.card := by
  have hlow := (mem_goodSubsets.mp hU).2.2.1
  omega

/-- Unique prime factorization recovers a finite set of primes from its
product, including the empty set. -/
theorem eq_of_prod_eq_prod_of_primes {U V : Finset ℕ}
    (hU : ∀ p ∈ U, p.Prime) (hV : ∀ p ∈ V, p.Prime)
    (hprod : (∏ p ∈ U, p) = ∏ p ∈ V, p) : U = V := by
  have h := congrArg Nat.primeFactors hprod
  simpa only [Nat.primeFactors_prod hU, Nat.primeFactors_prod hV] using h

/-- In particular, distinct subsets of a fixed set of primes have distinct
products. -/
theorem prod_injOn_prime_subsets {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun U : Finset ℕ => ∏ p ∈ U, p)
      (↑P.powerset : Set (Finset ℕ)) := by
  intro U hU V hV hprod
  exact eq_of_prod_eq_prod_of_primes
    (fun p hp => hP p ((Finset.mem_powerset.mp hU) hp))
    (fun p hp => hP p ((Finset.mem_powerset.mp hV) hp)) hprod

/-- A subset of at most `t` integers, each at most `z`, has product at most
`z ^ t` when `z ≥ 1`. -/
theorem prod_le_pow_of_subset {P U : Finset ℕ} {z : ℝ} {t : ℕ}
    (hz : 1 ≤ z) (hbound : ∀ p ∈ P, (p : ℝ) ≤ z)
    (hUP : U ⊆ P) (hcard : U.card ≤ t) :
    ((∏ p ∈ U, p : ℕ) : ℝ) ≤ z ^ t := by
  calc
    ((∏ p ∈ U, p : ℕ) : ℝ) = ∏ p ∈ U, (p : ℝ) := by simp
    _ ≤ ∏ _p ∈ U, z := Finset.prod_le_prod
      (fun p _ => Nat.cast_nonneg p) (fun p hp => hbound p (hUP hp))
    _ = z ^ U.card := Finset.prod_const z
    _ ≤ z ^ t := pow_le_pow_right₀ hz hcard

/-- Every good subset in the common-modulus construction has at least two
primes and gives an actual Carmichael number at most `z ^ t`. -/
theorem goodSubset_carmichael_and_le
    {P U : Finset ℕ} {M D t : ℕ} {z : ℝ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hz : 1 ≤ z) (hbound : ∀ p ∈ P, (p : ℝ) ≤ z)
    (hdiv : ∀ p ∈ P, p - 1 ∣ M) (ht : D + 1 ≤ t)
    (hU : U ∈ goodSubsets P (fun U => Nat.ModEq M (∏ p ∈ U, p) 1) D t) :
    2 ≤ U.card ∧ IsCarmichael (∏ p ∈ U, p) ∧
      ((∏ p ∈ U, p : ℕ) : ℝ) ≤ z ^ t := by
  obtain ⟨hUP, hmod, _hlow, hcard⟩ := mem_goodSubsets.mp hU
  have htwo := two_le_card_of_mem_goodSubsets ht hU
  exact ⟨htwo,
    CarmichaelAlgebra.isCarmichael_prod_of_modEq
      (fun p hp => hprime p (hUP hp)) htwo (fun p hp => hdiv p (hUP hp)) hmod,
    prod_le_pow_of_subset hz hbound hUP hcard⟩

/-- Injecting good subsets into their products bounds their cardinality by
the exact natural cardinality underlying the original counting function. -/
theorem card_goodSubsets_le_count
    {P : Finset ℕ} {M D t : ℕ} {z : ℝ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hz : 1 ≤ z) (hbound : ∀ p ∈ P, (p : ℝ) ≤ z)
    (hdiv : ∀ p ∈ P, p - 1 ∣ M) (ht : D + 1 ≤ t) :
    (goodSubsets P (fun U => Nat.ModEq M (∏ p ∈ U, p) 1) D t).card ≤
      {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ z ^ t}.ncard := by
  classical
  let F := goodSubsets P (fun U => Nat.ModEq M (∏ p ∈ U, p) 1) D t
  have hmap : ∀ U ∈ (↑F : Set (Finset ℕ)),
      (∏ p ∈ U, p) ∈ {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ z ^ t} := by
    intro U hU
    exact (goodSubset_carmichael_and_le hprime hz hbound hdiv ht hU).2
  have hinj : Set.InjOn (fun U : Finset ℕ => ∏ p ∈ U, p)
      (↑F : Set (Finset ℕ)) := by
    apply (prod_injOn_prime_subsets hprime).mono
    intro U hU
    exact Finset.mem_powerset.mpr (mem_goodSubsets.mp hU).1
  have h := Set.ncard_le_ncard_of_injOn (fun U : Finset ℕ => ∏ p ∈ U, p)
    hmap hinj (Erdos1057Research.finite_counting_set (z ^ t))
  simpa only [Set.ncard_coe_finset] using h

/-- The same injection bound, stated using the actual real-valued count `C`. -/
theorem card_goodSubsets_le_C
    {P : Finset ℕ} {M D t : ℕ} {z : ℝ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hz : 1 ≤ z) (hbound : ∀ p ∈ P, (p : ℝ) ≤ z)
    (hdiv : ∀ p ∈ P, p - 1 ∣ M) (ht : D + 1 ≤ t) :
    ((goodSubsets P (fun U => Nat.ModEq M (∏ p ∈ U, p) 1) D t).card : ℝ) ≤
      Erdos1057Research.C (z ^ t) := by
  unfold Erdos1057Research.C
  exact_mod_cast card_goodSubsets_le_count hprime hz hbound hdiv ht

/-- **Finite quantitative Carmichael bound, natural-number form.**
The product-one guarantee is an explicit hypothesis, not an axiom.
The count on the right is exactly the one in the definition of `C`. -/
theorem choose_le_mul_count_of_modEq
    {P : Finset ℕ} {M D t : ℕ} {z : ℝ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hz : 1 ≤ z) (hbound : ∀ p ∈ P, (p : ℝ) ≤ z)
    (hdiv : ∀ p ∈ P, p - 1 ∣ M)
    (hextract : ∀ S ⊆ P, D ≤ S.card →
      ∃ T ⊆ S, T.Nonempty ∧ Nat.ModEq M (∏ p ∈ T, p) 1)
    (ht : D + 1 ≤ t) :
    P.card.choose t ≤ (∑ j ∈ Finset.range D, P.card.choose j) *
      {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ z ^ t}.ncard := by
  exact (choose_le_mul_card_modEq hextract (by omega)).trans
    (Nat.mul_le_mul_left _ (card_goodSubsets_le_count hprime hz hbound hdiv ht))

/-- **Finite quantitative Carmichael bound for the original `C`**, without
division.  It applies in particular when `1 ≤ D` and `D + 1 ≤ t ≤ P.card`. -/
theorem choose_le_mul_C_of_modEq
    {P : Finset ℕ} {M D t : ℕ} {z : ℝ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hz : 1 ≤ z) (hbound : ∀ p ∈ P, (p : ℝ) ≤ z)
    (hdiv : ∀ p ∈ P, p - 1 ∣ M)
    (hextract : ∀ S ⊆ P, D ≤ S.card →
      ∃ T ⊆ S, T.Nonempty ∧ Nat.ModEq M (∏ p ∈ T, p) 1)
    (ht : D + 1 ≤ t) :
    (P.card.choose t : ℝ) ≤
      ((∑ j ∈ Finset.range D, P.card.choose j : ℕ) : ℝ) *
        Erdos1057Research.C (z ^ t) := by
  unfold Erdos1057Research.C
  exact_mod_cast choose_le_mul_count_of_modEq hprime hz hbound hdiv hextract ht

/-- Division form of the lower bound, with a proved positive denominator. -/
theorem choose_div_le_C_of_modEq
    {P : Finset ℕ} {M D t : ℕ} {z : ℝ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hz : 1 ≤ z) (hbound : ∀ p ∈ P, (p : ℝ) ≤ z)
    (hdiv : ∀ p ∈ P, p - 1 ∣ M) (hD : 1 ≤ D)
    (hextract : ∀ S ⊆ P, D ≤ S.card →
      ∃ T ⊆ S, T.Nonempty ∧ Nat.ModEq M (∏ p ∈ T, p) 1)
    (ht : D + 1 ≤ t) :
    (P.card.choose t : ℝ) / ((∑ j ∈ Finset.range D, P.card.choose j : ℕ) : ℝ) ≤
      Erdos1057Research.C (z ^ t) := by
  have hpos : (0 : ℝ) < ((∑ j ∈ Finset.range D, P.card.choose j : ℕ) : ℝ) := by
    exact_mod_cast choose_sum_pos P.card hD
  apply (div_le_iff₀ hpos).mpr
  simpa only [mul_comm] using
    choose_le_mul_C_of_modEq hprime hz hbound hdiv hextract ht

/-- CRT upgrades a product-one congruence modulo `L` to one modulo `k * L`
when all the factors are already one modulo `k`. -/
theorem prod_modEq_mul_of_subset
    {P U : Finset ℕ} {k L : ℕ} (hcop : k.Coprime L)
    (hmodk : ∀ p ∈ P, Nat.ModEq k p 1) (hUP : U ⊆ P)
    (hmodL : Nat.ModEq L (∏ p ∈ U, p) 1) :
    Nat.ModEq (k * L) (∏ p ∈ U, p) 1 := by
  exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
    ⟨Nat.ModEq.prod_one (fun p hp => hmodk p (hUP hp)), hmodL⟩

/-- The bound in the original coprime-moduli formulation.  Coprimality of
each prime with `L` is unnecessary here: once the product-one extraction
hypothesis is supplied, it is only used upstream to formulate that hypothesis
in the group of units. -/
theorem choose_le_mul_C_of_coprime_moduli
    {P : Finset ℕ} {k L D t : ℕ} {z : ℝ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hz : 1 ≤ z) (hbound : ∀ p ∈ P, (p : ℝ) ≤ z)
    (hcop : k.Coprime L) (hdiv : ∀ p ∈ P, p - 1 ∣ k * L)
    (hmodk : ∀ p ∈ P, Nat.ModEq k p 1)
    (hextract : ∀ S ⊆ P, D ≤ S.card →
      ∃ T ⊆ S, T.Nonempty ∧ Nat.ModEq L (∏ p ∈ T, p) 1)
    (ht : D + 1 ≤ t) :
    (P.card.choose t : ℝ) ≤
      ((∑ j ∈ Finset.range D, P.card.choose j : ℕ) : ℝ) *
        Erdos1057Research.C (z ^ t) := by
  apply choose_le_mul_C_of_modEq hprime hz hbound hdiv _ ht
  intro S hSP hDS
  obtain ⟨T, hTS, hTne, hTL⟩ := hextract S hSP hDS
  exact ⟨T, hTS, hTne, prod_modEq_mul_of_subset hcop hmodk (hTS.trans hSP) hTL⟩

/-- Division form for coprime `k, L` and an explicit extraction hypothesis
modulo `L`. -/
theorem choose_div_le_C_of_coprime_moduli
    {P : Finset ℕ} {k L D t : ℕ} {z : ℝ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hz : 1 ≤ z) (hbound : ∀ p ∈ P, (p : ℝ) ≤ z)
    (hcop : k.Coprime L) (hdiv : ∀ p ∈ P, p - 1 ∣ k * L)
    (hmodk : ∀ p ∈ P, Nat.ModEq k p 1) (hD : 1 ≤ D)
    (hextract : ∀ S ⊆ P, D ≤ S.card →
      ∃ T ⊆ S, T.Nonempty ∧ Nat.ModEq L (∏ p ∈ T, p) 1)
    (ht : D + 1 ≤ t) :
    (P.card.choose t : ℝ) / ((∑ j ∈ Finset.range D, P.card.choose j : ℕ) : ℝ) ≤
      Erdos1057Research.C (z ^ t) := by
  have hpos : (0 : ℝ) < ((∑ j ∈ Finset.range D, P.card.choose j : ℕ) : ℝ) := by
    exact_mod_cast choose_sum_pos P.card hD
  apply (div_le_iff₀ hpos).mpr
  simpa only [mul_comm] using
    choose_le_mul_C_of_coprime_moduli hprime hz hbound hcop hdiv hmodk hextract ht

end CarmichaelSubsetCounting

-- Kernel-axiom audit of every theorem in this file.
#print axioms CarmichaelSubsetCounting.mem_smallSubsets
#print axioms CarmichaelSubsetCounting.mem_goodSubsets
#print axioms CarmichaelSubsetCounting.card_smallSubsets
#print axioms CarmichaelSubsetCounting.exists_good_subset_small_remainder
#print axioms CarmichaelSubsetCounting.choose_le_smallSubsets_mul_goodSubsets
#print axioms CarmichaelSubsetCounting.choose_le_mul_card_product_one
#print axioms CarmichaelSubsetCounting.choose_le_mul_card_modEq
#print axioms CarmichaelSubsetCounting.choose_sum_pos
#print axioms CarmichaelSubsetCounting.two_le_card_of_mem_goodSubsets
#print axioms CarmichaelSubsetCounting.eq_of_prod_eq_prod_of_primes
#print axioms CarmichaelSubsetCounting.prod_injOn_prime_subsets
#print axioms CarmichaelSubsetCounting.prod_le_pow_of_subset
#print axioms CarmichaelSubsetCounting.goodSubset_carmichael_and_le
#print axioms CarmichaelSubsetCounting.card_goodSubsets_le_count
#print axioms CarmichaelSubsetCounting.card_goodSubsets_le_C
#print axioms CarmichaelSubsetCounting.choose_le_mul_count_of_modEq
#print axioms CarmichaelSubsetCounting.choose_le_mul_C_of_modEq
#print axioms CarmichaelSubsetCounting.choose_div_le_C_of_modEq
#print axioms CarmichaelSubsetCounting.prod_modEq_mul_of_subset
#print axioms CarmichaelSubsetCounting.choose_le_mul_C_of_coprime_moduli
#print axioms CarmichaelSubsetCounting.choose_div_le_C_of_coprime_moduli
