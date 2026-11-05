import Submission.Counting
import Submission.ProductOneCounting

/-!
# Finite prime-pool transfer to Carmichael counting

This file turns a relative Davenport-bound hypothesis on a finite prime pool
into an explicit finite Carmichael-counting lower bound. It includes all
Korselt, size, and subset-to-integer injectivity checks. The required prime
pool and Davenport bound are hypotheses; no density assertion is made.
The admitted conjecture and its negation are not imported or used.
-/

open Finset

namespace Erdos1057.PrimePool

/-- A product of distinct primes is squarefree. -/
theorem squarefree_prod {T : Finset ℕ} (hp : ∀ p ∈ T, p.Prime) :
    Squarefree (∏ p ∈ T, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hpT q hqT hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hp p hpT) (hp q hqT)).mpr hpq)
  · intro p hpT
    exact (Nat.prime_iff.mp (hp p hpT)).squarefree

/-- A product of at least two distinct primes is composite. -/
theorem composite_prod {T : Finset ℕ} (hp : ∀ p ∈ T, p.Prime) (hcard : 2 ≤ T.card) :
    Nat.Composite (∏ p ∈ T, p) := by
  have hpos : 0 < ∏ p ∈ T, p := Finset.prod_pos (fun p hpT => (hp p hpT).pos)
  have hne : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hpT⟩ := hne
  have hple : p ≤ ∏ p ∈ T, p := Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem id hpT)
  refine ⟨(hp p hpT).one_lt.trans_le hple, ?_⟩
  intro hprime
  have hc : T.card = 1 := by
    rw [← Nat.primeFactors_prod hp, hprime.primeFactors]
    simp
  omega

/-- The product map is injective on subsets of a pool of distinct primes. -/
theorem prod_injOn_subsets {P : Finset ℕ} (hp : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) {T | T ⊆ P} := by
  intro T hT U hU heq
  have hTf := Nat.primeFactors_prod (fun p hpT => hp p (hT hpT))
  have hUf := Nat.primeFactors_prod (fun p hpU => hp p (hU hpU))
  rw [← hTf, ← hUf]
  exact congrArg Nat.primeFactors (by simpa using heq)

/-- Natural congruence `a = 1 (mod m)` is divisibility of `a - 1`, for positive `a`. -/
theorem dvd_pred_of_zmod_eq_one {a m : ℕ} (ha : 1 ≤ a) (h : (a : ZMod m) = 1) :
    m ∣ a - 1 := by
  have hm : Nat.ModEq m a 1 :=
    (ZMod.natCast_eq_natCast_iff a 1 m).mp (by simpa using h)
  exact (Nat.modEq_iff_dvd' ha).mp hm.symm

/-- If every prime is `1 (mod k)`, so is its product. -/
theorem prod_zmod_eq_one {T : Finset ℕ} {k : ℕ}
    (hp : ∀ p ∈ T, p.Prime) (hk : ∀ p ∈ T, k ∣ p - 1) :
    ((∏ p ∈ T, p : ℕ) : ZMod k) = 1 := by
  rw [Nat.cast_prod]
  have hcast : ∀ p ∈ T, (p : ZMod k) = 1 := by
    intro p hpT
    have hmod : Nat.ModEq k 1 p :=
      (Nat.modEq_iff_dvd' (hp p hpT).one_le).mpr (hk p hpT)
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff p 1 k).mpr hmod.symm
  rw [Finset.prod_congr rfl hcast]
  simp

/-- Full Korselt transfer for a product-one subset. `k` is omitted from the
subset group because every selected prime is already `1 (mod k)`. -/
theorem isCarmichael_prod_of_product_one {T : Finset ℕ} {k L : ℕ}
    (hp : ∀ p ∈ T, p.Prime) (hcard : 2 ≤ T.card)
    (hkL : k.Coprime L)
    (hk : ∀ p ∈ T, k ∣ p - 1)
    (hshift : ∀ p ∈ T, p - 1 ∣ k * L)
    (hprod : (∏ p ∈ T, (p : ZMod L)) = 1) :
    IsCarmichael (∏ p ∈ T, p) := by
  have hcomp := composite_prod hp hcard
  have hkdiv : k ∣ (∏ p ∈ T, p) - 1 :=
    dvd_pred_of_zmod_eq_one hcomp.1.le (prod_zmod_eq_one hp hk)
  have hLdiv : L ∣ (∏ p ∈ T, p) - 1 :=
    dvd_pred_of_zmod_eq_one hcomp.1.le (by simpa only [Nat.cast_prod] using hprod)
  have hframe : k * L ∣ (∏ p ∈ T, p) - 1 :=
    hkL.mul_dvd_of_dvd_of_dvd hkdiv hLdiv
  apply (CarmichaelKorselt.isCarmichael_iff_korselt _).mpr
  refine ⟨hcomp, squarefree_prod hp, ?_⟩
  intro p hpprime hpn
  have hmem : p ∈ (∏ q ∈ T, q).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpprime, hpn, by have := hcomp.1; omega⟩
  rw [Nat.primeFactors_prod hp] at hmem
  exact (hshift p hmem).trans hframe

/-- Products of subsets with at most `t` primes bounded by `Y` have height at most `Y ^ t`. -/
theorem prod_le_pow {P T : Finset ℕ} {Y t : ℕ} (hY : 1 ≤ Y)
    (hbound : ∀ p ∈ P, p ≤ Y) (hT : T ⊆ P) (ht : T.card ≤ t) :
    (∏ p ∈ T, p) ≤ Y ^ t := by
  exact (Finset.prod_le_pow_card T id Y (fun p hp => hbound p (hT hp))).trans
    (Nat.pow_le_pow_right (by omega) ht)

/-- Injecting the good product-one subsets into the bounded Carmichael set
counts each output once, by unique prime factorization. -/
theorem goodSubsets_card_le_carmichael_ncard
    {P : Finset ℕ} {k L Y D t : ℕ}
    (hp : ∀ p ∈ P, p.Prime) (hY : 1 ≤ Y) (hbound : ∀ p ∈ P, p ≤ Y)
    (hkL : k.Coprime L) (hk : ∀ p ∈ P, k ∣ p - 1)
    (hshift : ∀ p ∈ P, p - 1 ∣ k * L) (ht : D + 1 ≤ t) :
    (ProductOneCounting.goodSubsets P (fun p => (p : ZMod L)) D t).card ≤
      {n : ℕ | IsCarmichael n ∧ n ≤ Y ^ t}.ncard := by
  classical
  let good := ProductOneCounting.goodSubsets P (fun p => (p : ZMod L)) D t
  let f : Finset ℕ → ℕ := fun T => ∏ p ∈ T, p
  have hinj : Set.InjOn f (good : Set (Finset ℕ)) := by
    intro T hT U hU heq
    exact prod_injOn_subsets hp
      (ProductOneCounting.mem_goodSubsets.mp hT).1
      (ProductOneCounting.mem_goodSubsets.mp hU).1 heq
  have himage : (good.image f : Set ℕ) ⊆ {n : ℕ | IsCarmichael n ∧ n ≤ Y ^ t} := by
    intro n hn
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hTP, hprod, hlow, hupp⟩ := ProductOneCounting.mem_goodSubsets.mp hT
    have htwo : 2 ≤ T.card := by omega
    refine ⟨isCarmichael_prod_of_product_one (fun p hpT => hp p (hTP hpT)) htwo
      hkL (fun p hpT => hk p (hTP hpT)) (fun p hpT => hshift p (hTP hpT)) hprod,
      prod_le_pow hY hbound hTP hupp⟩
  have hfinite : {n : ℕ | IsCarmichael n ∧ n ≤ Y ^ t}.Finite :=
    (Set.finite_le_nat (Y ^ t)).subset (fun _ hn => hn.2)
  have hcard := Set.ncard_le_ncard himage hfinite
  rw [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj] at hcard
  exact hcard

/-- Exact finite lower bound, conditional on a relative Davenport bound for
this actual prime pool. The group modulus is `L`, not `k * L`. -/
theorem choose_le_carmichael_ncard_mul_sum_choose
    {P : Finset ℕ} {k L Y D t : ℕ}
    (hp : ∀ p ∈ P, p.Prime) (hY : 1 ≤ Y) (hbound : ∀ p ∈ P, p ≤ Y)
    (hkL : k.Coprime L) (hk : ∀ p ∈ P, k ∣ p - 1)
    (hshift : ∀ p ∈ P, p - 1 ∣ k * L)
    (hD : ProductOneCounting.DavenportBound P (fun p => (p : ZMod L)) D)
    (ht : D + 1 ≤ t) :
    Nat.choose P.card t ≤ {n : ℕ | IsCarmichael n ∧ n ≤ Y ^ t}.ncard *
      ∑ j ∈ Finset.range D, Nat.choose P.card j := by
  exact (ProductOneCounting.count_bound hD t).trans
    (Nat.mul_le_mul_right _
      (goodSubsets_card_le_carmichael_ncard hp hY hbound hkL hk hshift ht))

/-- A simpler finite lower bound with a crude power bound for the discarded subsets. -/
theorem choose_le_carmichael_ncard_mul_pow
    {P : Finset ℕ} {k L Y D t : ℕ}
    (hp : ∀ p ∈ P, p.Prime) (hY : 1 ≤ Y) (hbound : ∀ p ∈ P, p ≤ Y)
    (hkL : k.Coprime L) (hk : ∀ p ∈ P, k ∣ p - 1)
    (hshift : ∀ p ∈ P, p - 1 ∣ k * L)
    (hD : ProductOneCounting.DavenportBound P (fun p => (p : ZMod L)) D)
    (ht : D + 1 ≤ t) :
    Nat.choose P.card t ≤ {n : ℕ | IsCarmichael n ∧ n ≤ Y ^ t}.ncard * (P.card + 1) ^ D := by
  exact (choose_le_carmichael_ncard_mul_sum_choose hp hY hbound hkL hk hshift hD ht).trans
    (Nat.mul_le_mul_left _ (ProductOneCounting.sum_choose_le_pow P.card D))

/-- The preceding finite bound expressed using the independent real counting function. -/
theorem choose_le_count_mul_pow
    {P : Finset ℕ} {k L Y D t : ℕ}
    (hp : ∀ p ∈ P, p.Prime) (hY : 1 ≤ Y) (hbound : ∀ p ∈ P, p ≤ Y)
    (hkL : k.Coprime L) (hk : ∀ p ∈ P, k ∣ p - 1)
    (hshift : ∀ p ∈ P, p - 1 ∣ k * L)
    (hD : ProductOneCounting.DavenportBound P (fun p => (p : ZMod L)) D)
    (ht : D + 1 ≤ t) :
    (Nat.choose P.card t : ℝ) ≤ Preparation.count ((Y ^ t : ℕ) : ℝ) *
      ((P.card + 1 : ℕ) : ℝ) ^ D := by
  have hset : {n : ℕ | IsCarmichael n ∧ n ≤ Y ^ t} =
      {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ ((Y ^ t : ℕ) : ℝ)} := by
    ext n
    constructor
    · rintro ⟨hn, hb⟩
      exact ⟨hn, Nat.cast_le.mpr hb⟩
    · rintro ⟨hn, hb⟩
      exact ⟨hn, Nat.cast_le.mp hb⟩
  have h := choose_le_carmichael_ncard_mul_pow hp hY hbound hkL hk hshift hD ht
  unfold Preparation.count
  rw [← hset]
  exact_mod_cast h

end Erdos1057.PrimePool
