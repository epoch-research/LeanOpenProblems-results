import FormalConjecturesUtil

/-! Counting obstruction for covers by boxes with distinct nonempty supports. -/

namespace Erdos7Reduction
open Finset

private theorem choose_forbidden_singleton {ι κ : Type*}
    (A : ι → Type*) [∀ i, Nonempty (A i)]
    (s : κ → Finset ι) (hs : Function.Injective s) (a : κ → ∀ i, A i) :
    ∃ t : ∀ i, A i, ∀ k i, s k = {i} → a k i = t i := by
  classical
  have h (i : ι) : ∃ t : A i, ∀ k, s k = {i} → a k i = t := by
    by_cases hex : ∃ k, s k = {i}
    · obtain ⟨k, hk⟩ := hex
      refine ⟨a k i, ?_⟩
      intro j hj
      have heq : j = k := hs (hj.trans hk.symm)
      simp [heq]
    · refine ⟨Classical.choice inferInstance, ?_⟩
      intro k hk
      exact False.elim (hex ⟨k, hk⟩)
  choose t ht using h
  exact ⟨t, fun k i hi => ht i k hi⟩

/-- After avoiding every singleton-supported box, the remaining boxes must
cover the product of the punctured coordinate sets. -/
theorem distinct_box_composite_bound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (s : κ → Finset ι) (hs : Function.Injective s) (hs0 : ∀ k, (s k).Nonempty)
    (a : κ → ∀ i, A i)
    (hcover : ∀ x : ∀ i, A i, ∃ k, ∀ i ∈ s k, x i = a k i) :
    (∏ i, (Fintype.card (A i) - 1)) ≤
      ∑ S ∈ (Finset.univ : Finset ι).powerset with 2 ≤ S.card,
        ∏ i ∈ Finset.univ \ S, (Fintype.card (A i) - 1) := by
  classical
  obtain ⟨t, ht⟩ := choose_forbidden_singleton A s hs a
  let T (i : ι) : Finset (A i) := Finset.univ.erase (t i)
  let Ω := Fintype.piFinset T
  let B (k : κ) := Ω.filter (fun x => ∀ i ∈ s k, x i = a k i)
  let K := Finset.univ.filter (fun k => 2 ≤ (s k).card)
  have hBsub (k : κ) : B k ⊆ Fintype.piFinset
      (fun i => if i ∈ s k then {a k i} else T i) := by
    intro x hx
    obtain ⟨hxΩ, hxmatch⟩ := Finset.mem_filter.mp hx
    apply Fintype.mem_piFinset.mpr
    intro i
    split_ifs with hi
    · simpa using hxmatch i hi
    · exact Fintype.mem_piFinset.mp hxΩ i
  have hBcard (k : κ) : (B k).card ≤
      ∏ i ∈ Finset.univ \ s k, (Fintype.card (A i) - 1) := by
    have h := Finset.card_le_card (hBsub k)
    rw [Fintype.card_piFinset] at h
    have heq : (∏ i, (if i ∈ s k then ({a k i} : Finset (A i)) else T i).card) =
        ∏ i ∈ Finset.univ \ s k, (Fintype.card (A i) - 1) := by
      simp only [apply_ite Finset.card, Finset.card_singleton, T,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      rw [Finset.prod_ite]
      simp only [Finset.prod_const_one, one_mul]
      congr 1
      ext i
      simp
    rwa [heq] at h
  have hcov : Ω ⊆ K.biUnion B := by
    intro x hx
    obtain ⟨k, hk⟩ := hcover x
    have hklarge : 2 ≤ (s k).card := by
      by_contra hlt
      have hcard : (s k).card = 1 := by
        have := (hs0 k).card_pos
        omega
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
      have hxi := Fintype.mem_piFinset.mp hx i
      have hne : x i ≠ t i := (Finset.mem_erase.mp hxi).1
      apply hne
      exact (hk i (by simp [hi])).trans (ht k i hi)
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hklarge⟩,
      Finset.mem_filter.mpr ⟨hx, hk⟩⟩
  have hcount : Ω.card ≤ ∑ k ∈ K, ∏ i ∈ Finset.univ \ s k, (Fintype.card (A i) - 1) := by
    exact (Finset.card_le_card hcov).trans
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun k _ => hBcard k)))
  have hΩ : Ω.card = ∏ i, (Fintype.card (A i) - 1) := by
    simp only [Ω, Fintype.card_piFinset, T,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rw [hΩ] at hcount
  have himg : K.image s ⊆ (Finset.univ : Finset ι).powerset.filter (fun S => 2 ≤ S.card) := by
    intro S hS
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
      (Finset.mem_filter.mp hk).2⟩
  have heq : (∑ S ∈ K.image s, ∏ i ∈ Finset.univ \ S, (Fintype.card (A i) - 1)) =
      ∑ k ∈ K, ∏ i ∈ Finset.univ \ s k, (Fintype.card (A i) - 1) :=
    Finset.sum_image (fun k _ l _ h => hs h)
  rw [← heq] at hcount
  exact hcount.trans (Finset.sum_le_sum_of_subset himg)

#print axioms distinct_box_composite_bound
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

private theorem composite_capacity_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) :
    (∑ S ∈ (Finset.univ : Finset ι).powerset with 2 ≤ S.card,
      ∏ i ∈ Finset.univ \ S, q i) + (∏ i, q i) +
        (∑ j, ∏ i ∈ Finset.univ.erase j, q i) = ∏ i, (1 + q i) := by
  classical
  let minor : Finset (Finset ι) := insert ∅ (Finset.univ.image (fun i : ι => {i}))
  let cap (S : Finset ι) := ∏ i ∈ Finset.univ \ S, q i
  have hmem (S : Finset ι) : S ∈ minor ↔ S.card ≤ 1 := by
    simp only [minor, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (rfl | ⟨i, rfl⟩) <;> simp
    · intro h
      by_cases h0 : S = ∅
      · exact Or.inl h0
      · have hp : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (by omega : S.card = 1)
        exact Or.inr ⟨i, hi.symm⟩
  have hminor : minor ⊆ (Finset.univ : Finset ι).powerset := by
    intro S _
    exact Finset.mem_powerset.mpr (Finset.subset_univ _)
  have hmajor : (Finset.univ : Finset ι).powerset.filter (fun S => 2 ≤ S.card) =
      (Finset.univ : Finset ι).powerset \ minor := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_sdiff, hmem]
    exact and_congr_right (fun _ => by omega)
  have hnone : (∅ : Finset ι) ∉ Finset.univ.image (fun i : ι => {i}) := by simp
  have hminsum : ∑ S ∈ minor, cap S =
      (∏ i, q i) + ∑ j, ∏ i ∈ Finset.univ.erase j, q i := by
    rw [Finset.sum_insert hnone, Finset.sum_image]
    · simp only [cap, Finset.sdiff_empty, Finset.sdiff_singleton_eq_erase]
    · intro i _ j _ h
      exact Finset.singleton_injective h
  have hall : ∑ S ∈ (Finset.univ : Finset ι).powerset, cap S = ∏ i, (1 + q i) := by
    simpa only [cap, Finset.prod_const_one, one_mul] using
      (Finset.prod_add (fun _ : ι => (1 : ℕ)) q Finset.univ).symm
  have hsum := Finset.sum_sdiff (f := cap) hminor
  rw [← hmajor, hminsum, hall] at hsum
  simpa only [cap, add_assoc] using hsum

/-- A volume inequality independent of the residues for a box cover with
at most one box for every nonempty coordinate support. -/
theorem distinct_box_volume_bound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (s : κ → Finset ι) (hs : Function.Injective s) (hs0 : ∀ k, (s k).Nonempty)
    (a : κ → ∀ i, A i)
    (hcover : ∀ x : ∀ i, A i, ∃ k, ∀ i ∈ s k, x i = a k i) :
    2 * (∏ i, (Fintype.card (A i) - 1)) +
      (∑ j, ∏ i ∈ Finset.univ.erase j, (Fintype.card (A i) - 1)) ≤
        ∏ i, Fintype.card (A i) := by
  have h := distinct_box_composite_bound A s hs hs0 a hcover
  have hid := composite_capacity_identity (fun i => Fintype.card (A i) - 1)
  have hc (i : ι) : 1 + (Fintype.card (A i) - 1) = Fintype.card (A i) := by
    have := Fintype.card_pos (α := A i)
    omega
  simp_rw [hc] at hid
  omega

#print axioms distinct_box_volume_bound
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

/-- CRT converts a cover by products of distinct coprime coordinate moduli into
a box cover, giving the same punctured-volume obstruction. -/
theorem coprime_support_cover_bound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (s : κ → Finset ι) (hs : Function.Injective s) (hs0 : ∀ k, (s k).Nonempty)
    (a : κ → ℤ)
    (hcover : ∀ x : ℤ, ∃ k, ((∏ i ∈ s k, p i : ℕ) : ℤ) ∣ x - a k) :
    2 * (∏ i, (p i - 1)) + (∑ j, ∏ i ∈ Finset.univ.erase j, (p i - 1)) ≤ ∏ i, p i := by
  classical
  letI (i : ι) : NeZero (p i) := ⟨by have := hp i; omega⟩
  let A (i : ι) := ZMod (p i)
  let b (k : κ) (i : ι) : A i := (a k : ZMod (p i))
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i ∈ s k, x i = b k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) p Finset.univ
      (fun i _ => by have := hp i; omega) (fun i _ j _ hij => hcop hij)
    have hz (i : ι) : (z.val : ZMod (p i)) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hcover (z.val : ℤ)
    refine ⟨k, ?_⟩
    intro i hi
    have hpi : p i ∣ ∏ j ∈ s k, p j := Finset.dvd_prod_of_mem p hi
    have hpi' : (p i : ℤ) ∣ ((∏ j ∈ s k, p j : ℕ) : ℤ) := by exact_mod_cast hpi
    have heq : (a k : ZMod (p i)) = ((z.val : ℤ) : ZMod (p i)) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (hpi'.trans hk)
    change x i = (a k : ZMod (p i))
    rw [← hz i]
    simpa only [Int.cast_natCast] using heq.symm
  simpa only [A, ZMod.card] using distinct_box_volume_bound A s hs hs0 b hbox

#print axioms coprime_support_cover_bound
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

private theorem divisor_prime_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (m : ℕ) (hm : m ∣ ∏ i, p i) :
    ∃ S : Finset ι, m = ∏ i ∈ S, p i := by
  classical
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hinj h))
  have hsf : Squarefree (∏ i, p i) :=
    Finset.squarefree_prod_of_pairwise_isCoprime
      (fun i _ j _ hij => Nat.coprime_iff_isRelPrime.mp (hcop hij))
      (fun i _ => (hp i).squarefree)
  have hmsf : Squarefree m := Squarefree.squarefree_of_dvd hm hsf
  let P := Finset.univ.image p
  have hPprime : ∀ r ∈ P, r.Prime := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact hp i
  have hprodP : (∏ r ∈ P, r) = ∏ i, p i :=
    Finset.prod_image (fun i _ j _ hij => hinj hij)
  have hPF : (∏ i, p i).primeFactors = P := by
    rw [← hprodP]
    exact Nat.primeFactors_prod hPprime
  have hsub : m.primeFactors ⊆ P := by
    rw [← hPF]
    exact Nat.primeFactors_mono hm hsf.ne_zero
  let S := Finset.univ.filter (fun i => p i ∈ m.primeFactors)
  have heq : S.image p = m.primeFactors := by
    ext r
    constructor
    · intro hr
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
      exact (Finset.mem_filter.mp hi).2
    · intro hr
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hsub hr)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, by simpa [hi] using hr⟩, hi⟩
  refine ⟨S, ?_⟩
  rw [← Nat.prod_primeFactors_of_squarefree hmsf, ← heq,
    Finset.prod_image (fun i _ j _ hij => hinj hij)]

/-- A necessary bound for a covering whose moduli divide a squarefree prime product. -/
theorem prime_product_cover_bound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hp_inj : Function.Injective p)
    (m : κ → ℕ) (a : κ → ℤ) (hm : ∀ k, 1 < m k) (hm_inj : Function.Injective m)
    (hdiv : ∀ k, m k ∣ ∏ i, p i)
    (hcover : ∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k) :
    2 * (∏ i, (p i - 1)) + (∑ j, ∏ i ∈ Finset.univ.erase j, (p i - 1)) ≤ ∏ i, p i := by
  classical
  choose S hS using fun k => divisor_prime_support p hp hp_inj (m k) (hdiv k)
  have hSi : Function.Injective S := by
    intro k l hkl
    apply hm_inj
    rw [hS k, hS l, hkl]
  have hS0 (k : κ) : (S k).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hh := hm k
    rw [hS k, he, Finset.prod_empty] at hh
    omega
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hp_inj h))
  apply coprime_support_cover_bound p (fun i => (hp i).pos) hcop S hSi hS0 a
  intro x
  obtain ⟨k, hk⟩ := hcover x
  exact ⟨k, by rwa [← hS k]⟩

#print axioms prime_product_cover_bound
end Erdos7Reduction

namespace Erdos7Reduction

private def firstTenOddPrimes : Fin 10 → ℕ := ![3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

/-- No arithmetic cover with distinct nontrivial moduli can have every modulus
dividing the product of the first ten odd primes. -/
theorem not_arithmetic_cover_period_100280245065 {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hm : ∀ k, 1 < m k) (hm_inj : Function.Injective m)
    (hdiv : ∀ k, m k ∣ 100280245065) :
    ¬ (∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k) := by
  intro hcover
  have hp : ∀ i, (firstTenOddPrimes i).Prime := by decide
  have hinj : Function.Injective firstTenOddPrimes := by decide
  have hprod : (∏ i, firstTenOddPrimes i) = 100280245065 := by decide
  have hbound := prime_product_cover_bound firstTenOddPrimes hp hinj m a hm hm_inj
    (fun k => by rw [hprod]; exact hdiv k) hcover
  have hnum : ¬ (2 * (∏ i, (firstTenOddPrimes i - 1)) +
      (∑ j, ∏ i ∈ Finset.univ.erase j, (firstTenOddPrimes i - 1)) ≤
      ∏ i, firstTenOddPrimes i) := by decide
  exact hnum hbound

#print axioms not_arithmetic_cover_period_100280245065
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

/-- Restricting each coordinate set cannot destroy the existence of a cover with
specified supports: boxes missing the restriction may be relocated arbitrarily. -/
theorem box_cover_restrict_coordinates {ι κ : Type*}
    (A B : ι → Type*) [∀ i, Nonempty (B i)] (f : ∀ i, B i ↪ A i)
    (s : κ → Finset ι) (a : κ → ∀ i, A i)
    (hcover : ∀ x : ∀ i, A i, ∃ k, ∀ i ∈ s k, x i = a k i) :
    ∃ b : κ → ∀ i, B i, ∀ x : ∀ i, B i, ∃ k, ∀ i ∈ s k, x i = b k i := by
  classical
  let b (k : κ) (i : ι) := Function.invFun (f i) (a k i)
  refine ⟨b, ?_⟩
  intro x
  obtain ⟨k, hk⟩ := hcover (fun i => f i (x i))
  refine ⟨k, ?_⟩
  intro i hi
  change x i = Function.invFun (f i) (a k i)
  rw [← hk i hi, Function.leftInverse_invFun (f i).injective]

/-- The prime-product obstruction can be evaluated on any smaller coordinate sizes. -/
theorem prime_product_cover_bound_mono {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hp_inj : Function.Injective p)
    (q : ι → ℕ) (hq : ∀ i, 0 < q i) (hqp : ∀ i, q i ≤ p i)
    (m : κ → ℕ) (a : κ → ℤ) (hm : ∀ k, 1 < m k) (hm_inj : Function.Injective m)
    (hdiv : ∀ k, m k ∣ ∏ i, p i)
    (hcover : ∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k) :
    2 * (∏ i, (q i - 1)) + (∑ j, ∏ i ∈ Finset.univ.erase j, (q i - 1)) ≤ ∏ i, q i := by
  classical
  choose S hS using fun k => divisor_prime_support p hp hp_inj (m k) (hdiv k)
  have hSi : Function.Injective S := by
    intro k l hkl
    apply hm_inj
    rw [hS k, hS l, hkl]
  have hS0 (k : κ) : (S k).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hh := hm k
    rw [hS k, he, Finset.prod_empty] at hh
    omega
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hp_inj h))
  letI (i : ι) : NeZero (p i) := ⟨(hp i).ne_zero⟩
  letI (i : ι) : NeZero (q i) := ⟨by have := hq i; omega⟩
  let A (i : ι) := ZMod (p i)
  let B (i : ι) := ZMod (q i)
  let b (k : κ) (i : ι) : A i := (a k : ZMod (p i))
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i ∈ S k, x i = b k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) p Finset.univ
      (fun i _ => (hp i).ne_zero) (fun i _ j _ hij => hcop hij)
    have hz (i : ι) : (z.val : ZMod (p i)) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hcover (z.val : ℤ)
    refine ⟨k, ?_⟩
    intro i hi
    have hpi : p i ∣ m k := by rw [hS k]; exact Finset.dvd_prod_of_mem p hi
    have hpi' : (p i : ℤ) ∣ (m k : ℤ) := by exact_mod_cast hpi
    have heq : (a k : ZMod (p i)) = ((z.val : ℤ) : ZMod (p i)) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (hpi'.trans hk)
    change x i = (a k : ZMod (p i))
    rw [← hz i]
    simpa only [Int.cast_natCast] using heq.symm
  let f (i : ι) : B i ↪ A i := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa only [A, B, ZMod.card] using hqp i))
  obtain ⟨c, hc⟩ := box_cover_restrict_coordinates A B f S b hbox
  simpa only [B, ZMod.card] using distinct_box_volume_bound B S hSi hS0 c hc

#print axioms prime_product_cover_bound_mono
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

private theorem first_ten_prime_lower_bound (p : Fin 10 → ℕ)
    (hp : ∀ i, (p i).Prime) (ho : ∀ i, Odd (p i)) (hmono : StrictMono p) :
    ∀ i, firstTenOddPrimes i ≤ p i := by
  have htable : ∀ i : Fin 9, ∀ n : Fin 32, n.val.Prime →
      firstTenOddPrimes i.castSucc < n.val → firstTenOddPrimes i.succ ≤ n.val := by decide
  have hmax : ∀ i, firstTenOddPrimes i ≤ 31 := by decide
  have H (k : ℕ) : ∀ hk : k < 10, firstTenOddPrimes ⟨k, hk⟩ ≤ p ⟨k, hk⟩ := by
    induction k with
    | zero =>
      intro hk
      have h2 := (hp ⟨0, hk⟩).two_le
      have hodd := Nat.odd_iff.mp (ho ⟨0, hk⟩)
      change 3 ≤ p ⟨0, hk⟩
      omega
    | succ k ih =>
      intro hk
      have hk' : k < 10 := by omega
      have hprev := ih hk'
      have hinc := hmono (show (⟨k, hk'⟩ : Fin 10) < ⟨k+1, hk⟩ by simp)
      by_cases hb : p ⟨k+1, hk⟩ < 32
      · have ht := htable ⟨k, by omega⟩ ⟨p ⟨k+1, hk⟩, hb⟩ (hp ⟨k+1, hk⟩)
        apply ht
        exact lt_of_le_of_lt hprev hinc
      · exact (hmax ⟨k+1, hk⟩).trans (by omega)
  exact fun i => H i.val i.isLt

private theorem not_cover_ten_odd_primes {κ : Type*} [Fintype κ]
    (P : Finset ℕ) (hPcard : P.card = 10)
    (hP : ∀ p ∈ P, p.Prime ∧ Odd p)
    (m : κ → ℕ) (a : κ → ℤ) (hm : ∀ k, 1 < m k) (hm_inj : Function.Injective m)
    (hdiv : ∀ k, m k ∣ ∏ p ∈ P, p)
    (hcover : ∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k) : False := by
  let p := P.orderEmbOfFin hPcard
  have hp (i : Fin 10) : (p i).Prime := (hP _ (P.orderEmbOfFin_mem hPcard i)).1
  have ho (i : Fin 10) : Odd (p i) := (hP _ (P.orderEmbOfFin_mem hPcard i)).2
  have hprod : (∏ i, p i) = ∏ r ∈ P, r := by
    conv_rhs => rw [← P.map_orderEmbOfFin_univ hPcard]
    exact (Finset.prod_map _ _ (fun n : ℕ => n)).symm
  have hbound := prime_product_cover_bound_mono p hp p.injective firstTenOddPrimes
    (by decide) (first_ten_prime_lower_bound p hp ho p.strictMono) m a hm hm_inj
    (fun k => by rw [hprod]; exact hdiv k) hcover
  have hnum : ¬ (2 * (∏ i, (firstTenOddPrimes i - 1)) +
      (∑ j, ∏ i ∈ Finset.univ.erase j, (firstTenOddPrimes i - 1)) ≤
      ∏ i, firstTenOddPrimes i) := by decide
  exact hnum hbound

private theorem extend_odd_primes_to_ten (P : Finset ℕ) (hcard : P.card ≤ 10)
    (hP : ∀ p ∈ P, p.Prime ∧ Odd p) :
    ∃ T : Finset ℕ, P ⊆ T ∧ T.card = 10 ∧ ∀ p ∈ T, p.Prime ∧ Odd p := by
  classical
  let A : Set ℕ := {p | p.Prime} \ {2}
  have hA : A.Infinite := Nat.infinite_setOf_prime.diff (Set.finite_singleton 2)
  have hAP : (A \ (P : Set ℕ)).Infinite := hA.diff P.finite_toSet
  obtain ⟨U, hU, hUc⟩ := hAP.exists_subset_card_eq (10 - P.card)
  have hdis : Disjoint P U := by
    apply Finset.disjoint_left.mpr
    intro p hp hu
    exact (hU hu).2 hp
  refine ⟨P ∪ U, Finset.subset_union_left, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdis, hUc]
    omega
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hP p hp
    · have hh := (hU hp).1
      exact ⟨hh.1, hh.1.odd_of_ne_two (by simpa using hh.2)⟩

/-- Every odd covering system with squarefree distinct moduli involves at least
eleven distinct prime factors. -/
theorem squarefree_arithmetic_cover_prime_count {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hm : ∀ k, 1 < m k) (hm_inj : Function.Injective m)
    (hsf : ∀ k, Squarefree (m k)) (hodd : ∀ k, Odd (m k))
    (hcover : ∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k) :
    11 ≤ (Finset.univ.biUnion (fun k => (m k).primeFactors)).card := by
  classical
  let P := Finset.univ.biUnion (fun k => (m k).primeFactors)
  have hP : ∀ p ∈ P, p.Prime ∧ Odd p := by
    intro p hp
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hp
    have hpf := Nat.mem_primeFactors.mp hk
    exact ⟨hpf.1, (hodd k).of_dvd_nat hpf.2.1⟩
  by_contra hc
  have hcard : P.card ≤ 10 := by dsimp [P]; omega
  obtain ⟨T, hPT, hTc, hT⟩ := extend_odd_primes_to_ten P hcard hP
  apply not_cover_ten_odd_primes T hTc hT m a hm hm_inj _ hcover
  intro k
  rw [← Nat.prod_primeFactors_of_squarefree (hsf k)]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  apply hPT
  exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hp⟩

#print axioms squarefree_arithmetic_cover_prime_count
end Erdos7Reduction
