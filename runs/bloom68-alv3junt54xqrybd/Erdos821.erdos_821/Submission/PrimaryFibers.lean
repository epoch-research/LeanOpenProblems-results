import Submission.TotientFiber
import Mathlib.NumberTheory.Fermat
import Mathlib.Algebra.Ring.GeomSum

/-!
# Unconditional bound on pure two-power totient fibers

The theorem `fiberCard_two_pow_le` proves `fiberCard (2 ^ K) ≤ K + 2`.
It is a partial family bound, not a proof or disproof of the endpoint conjecture.
It does not assume that Fermat primes are finite or infinite.
This file does not import `Submission.Spec` or the conditional endpoint helper.
-/

namespace Erdos821Fresh

open Nat Finset

set_option maxHeartbeats 1000000

private theorem sum_two_pow_lt {S : Finset ℕ} {K : ℕ}
    (hS : S ⊆ range K) : (∑ i ∈ S, 2 ^ i) < 2 ^ K := by
  have hle : (∑ i ∈ S, 2 ^ i) ≤ ∑ i ∈ range K, 2 ^ i :=
    sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.zero_le _)
  have hgeom : (∑ i ∈ range K, (2 : ℕ) ^ i) + 1 = 2 ^ K := by
    simpa using geom_sum_mul_add (1 : ℕ) K
  omega

private theorem sum_two_pow_inj_bounded (K : ℕ) :
    ∀ S T : Finset ℕ, S ⊆ range K → T ⊆ range K →
      (∑ i ∈ S, 2 ^ i) = (∑ i ∈ T, 2 ^ i) → S = T := by
  induction K with
  | zero =>
      intro S T hS hT _
      have hs : S = ∅ := by simpa using hS
      have ht : T = ∅ := by simpa using hT
      exact hs.trans ht.symm
  | succ K ih =>
      intro S T hS hT hsum
      have hS0 : S.erase K ⊆ range K := by
        intro i hi
        obtain ⟨hne, hiS⟩ := mem_erase.mp hi
        have := mem_range.mp (hS hiS)
        exact mem_range.mpr (by omega)
      have hT0 : T.erase K ⊆ range K := by
        intro i hi
        obtain ⟨hne, hiT⟩ := mem_erase.mp hi
        have := mem_range.mp (hT hiT)
        exact mem_range.mpr (by omega)
      have hSl := sum_two_pow_lt hS0
      have hTl := sum_two_pow_lt hT0
      by_cases hK : K ∈ S
      · have hKT : K ∈ T := by
          by_contra hKT
          have ht : T.erase K = T := erase_eq_of_notMem hKT
          have hs : (∑ i ∈ S.erase K, 2 ^ i) + 2 ^ K = ∑ i ∈ S, 2 ^ i :=
            sum_erase_add S (fun i : ℕ => 2 ^ i) hK
          rw [ht] at hTl
          omega
        have hs : (∑ i ∈ S.erase K, 2 ^ i) + 2 ^ K = ∑ i ∈ S, 2 ^ i :=
            sum_erase_add S (fun i : ℕ => 2 ^ i) hK
        have ht : (∑ i ∈ T.erase K, 2 ^ i) + 2 ^ K = ∑ i ∈ T, 2 ^ i :=
            sum_erase_add T (fun i : ℕ => 2 ^ i) hKT
        have herase := ih (S.erase K) (T.erase K) hS0 hT0 (by omega)
        simpa only [insert_erase hK, insert_erase hKT] using congrArg (insert K) herase
      · have hKT : K ∉ T := by
          intro hKT
          have hs : S.erase K = S := erase_eq_of_notMem hK
          have ht : (∑ i ∈ T.erase K, 2 ^ i) + 2 ^ K = ∑ i ∈ T, 2 ^ i :=
            sum_erase_add T (fun i : ℕ => 2 ^ i) hKT
          rw [hs] at hSl
          omega
        simpa only [erase_eq_of_notMem hK, erase_eq_of_notMem hKT] using
          ih (S.erase K) (T.erase K) hS0 hT0
            (by simpa only [erase_eq_of_notMem hK, erase_eq_of_notMem hKT] using hsum)

/-- Distinct finite subsets of powers of two have distinct sums. -/
theorem sum_two_pow_injective :
    Function.Injective (fun S : Finset ℕ => ∑ i ∈ S, (2 : ℕ) ^ i) := by
  intro S T hsum
  let K := (S ∪ T).sup id + 1
  apply sum_two_pow_inj_bounded K S T ?_ ?_ hsum
  · intro i hi
    apply mem_range.mpr
    have hle : i ≤ (S ∪ T).sup id := le_sup (f := id) (mem_union_left T hi)
    omega
  · intro i hi
    apply mem_range.mpr
    have hle : i ≤ (S ∪ T).sup id := le_sup (f := id) (mem_union_right S hi)
    omega

/-- Canonical index for a Fermat prime, used only after proving it is one. -/
def fermatIndex (p : ℕ) : ℕ := Nat.log 2 (Nat.log 2 (p - 1))

@[simp] theorem fermatIndex_fermatNumber (i : ℕ) :
    fermatIndex (Nat.fermatNumber i) = i := by
  simp [fermatIndex, Nat.fermatNumber, Nat.log_pow (by decide : 1 < 2)]

/-- An odd prime whose predecessor divides a power of two is a Fermat prime. -/
theorem eq_fermatNumber_of_predecessor_dvd {p K : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p - 1 ∣ 2 ^ K) :
    p = Nat.fermatNumber (fermatIndex p) := by
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j ≠ 0 := by
    intro hj0
    have hpge := hp.two_le
    simp only [hj0, pow_zero] at hj
    omega
  have hpj : p = 2 ^ j + 1 := by
    have := hp.two_le
    omega
  have hjprime : (2 ^ j + 1).Prime := hpj ▸ hp
  obtain ⟨i, hi⟩ := Nat.pow_of_pow_add_prime (by decide : 1 < 2) hj0 hjprime
  have hpi : p = Nat.fermatNumber i := by
    rw [hpj, hi, Nat.fermatNumber]
  rw [hpi, fermatIndex_fermatNumber]

/-- Indices of the odd prime support of a preimage. -/
def fermatSupport (m : ℕ) : Finset ℕ := (m.primeFactors.erase 2).image fermatIndex

/-- The sum of the two-adic costs of the Fermat primes in a support. -/
def supportExponent (m : ℕ) : ℕ := ∑ i ∈ fermatSupport m, 2 ^ i

theorem prime_factor_fermat {m K p : ℕ} (hm : Nat.totient m = 2 ^ K)
    (hp : p ∈ m.primeFactors.erase 2) : p = Nat.fermatNumber (fermatIndex p) := by
  obtain ⟨hp2, hpm⟩ := mem_erase.mp hp
  have hprime := Nat.prime_of_mem_primeFactors hpm
  apply eq_fermatNumber_of_predecessor_dvd hprime hp2
  have hdiv := Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hpm)
  rwa [Nat.totient_prime hprime, hm] at hdiv

theorem fermatIndex_injOn_odd_support {m K : ℕ} (hm : Nat.totient m = 2 ^ K) :
    Set.InjOn fermatIndex (m.primeFactors.erase 2) := by
  intro p hp q hq hpq
  exact (prime_factor_fermat hm hp).trans
    ((congrArg Nat.fermatNumber hpq).trans (prime_factor_fermat hm hq).symm)

/-- The odd prime support is recoverable from its Fermat indices. -/
theorem odd_support_reconstruction {m K : ℕ} (hm : Nat.totient m = 2 ^ K) :
    (fermatSupport m).image Nat.fermatNumber = m.primeFactors.erase 2 := by
  unfold fermatSupport
  rw [image_image]
  ext p
  simp only [mem_image, Function.comp_apply]
  constructor
  · rintro ⟨q, hq, hqp⟩
    have hqp' : q = p := (prime_factor_fermat hm hq).trans hqp
    exact hqp' ▸ hq
  · intro hp
    exact ⟨p, hp, (prime_factor_fermat hm hp).symm⟩

/-- The totient of the radical of a two-power preimage has a binary support exponent. -/
theorem totient_rad_eq_two_pow_supportExponent {m K : ℕ}
    (hm : Nat.totient m = 2 ^ K) :
    Nat.totient (Erdos821Aux.rad m) = 2 ^ supportExponent m := by
  rw [Erdos821Aux.totient_rad, ← Finset.prod_erase m.primeFactors
    (f := fun p : ℕ => p - 1) (by decide : (2 : ℕ) - 1 = 1)]
  have hpred : ∀ p ∈ m.primeFactors.erase 2, p - 1 = 2 ^ (2 ^ fermatIndex p) := by
    intro p hp
    calc
      p - 1 = Nat.fermatNumber (fermatIndex p) - 1 :=
        congrArg (fun q : ℕ => q - 1) (prime_factor_fermat hm hp)
      _ = 2 ^ (2 ^ fermatIndex p) := by simp [Nat.fermatNumber]
  simp_rw [Finset.prod_congr rfl hpred]
  rw [prod_pow_eq_pow_sum]
  unfold supportExponent fermatSupport
  rw [sum_image (fermatIndex_injOn_odd_support hm)]

/-- The support exponent fits into the valuation budget of the target. -/
theorem supportExponent_le {m K : ℕ} (hm : Nat.totient m = 2 ^ K) :
    supportExponent m ≤ K := by
  have hdiv := Erdos821Aux.totient_rad_dvd m
  rw [hm, totient_rad_eq_two_pow_supportExponent hm] at hdiv
  have hle := Nat.le_of_dvd (pow_pos (by decide : 0 < (2 : ℕ)) K) hdiv
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle

/-- Equal binary support costs and equal two-membership recover the full support. -/
theorem primeFactors_eq_of_supportExponent_eq {a b K : ℕ}
    (ha : Nat.totient a = 2 ^ K) (hb : Nat.totient b = 2 ^ K)
    (h2 : 2 ∈ a.primeFactors ↔ 2 ∈ b.primeFactors)
    (he : supportExponent a = supportExponent b) : a.primeFactors = b.primeFactors := by
  have hF : fermatSupport a = fermatSupport b := sum_two_pow_injective he
  have hodd : a.primeFactors.erase 2 = b.primeFactors.erase 2 := by
    rw [← odd_support_reconstruction ha, ← odd_support_reconstruction hb, hF]
  ext p
  by_cases hp : p = 2
  · simpa only [hp] using h2
  · have he := Finset.ext_iff.mp hodd p
    simpa [mem_erase, hp, Ne.symm hp] using he

/-- A preimage without a factor two consumes the entire binary support budget. -/
theorem supportExponent_eq_of_two_notMem {m K : ℕ}
    (hm : Nat.totient m = 2 ^ K) (h2 : 2 ∉ m.primeFactors) :
    supportExponent m = K := by
  have hm0 : m ≠ 0 := by
    intro h0
    have ht : Nat.totient m ≠ 0 := by rw [hm]; exact pow_ne_zero _ (by decide)
    exact ht (by simp [h0])
  have h2nd : ¬ 2 ∣ m := by
    intro hd
    exact h2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd, hm0⟩)
  have hle := supportExponent_le hm
  have hformula : m = 2 ^ (K - supportExponent m) * Erdos821Aux.rad m := by
    calc
      m = (Nat.totient m / Nat.totient (Erdos821Aux.rad m)) * Erdos821Aux.rad m :=
        Erdos821Aux.radical_encoding m
      _ = 2 ^ (K - supportExponent m) * Erdos821Aux.rad m := by
        rw [hm, totient_rad_eq_two_pow_supportExponent hm,
          Nat.pow_div hle (by decide : 0 < (2 : ℕ))]
  apply le_antisymm hle
  by_contra hlt
  have hpos : 0 < K - supportExponent m := by omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hd : 2 ∣ 2 ^ (K - supportExponent m) := by
    rw [hj, pow_succ]
    exact dvd_mul_left 2 (2 ^ j)
  apply h2nd
  rw [hformula]
  exact dvd_mul_of_dvd_left hd _

/-- At most one odd input has any specified pure two-power totient. -/
theorem odd_preimage_unique {a b K : ℕ}
    (ha : Nat.totient a = 2 ^ K) (hb : Nat.totient b = 2 ^ K)
    (ha2 : 2 ∉ a.primeFactors) (hb2 : 2 ∉ b.primeFactors) : a = b := by
  apply Erdos821Aux.eq_of_primeFactors_eq_of_totient_eq
  · exact primeFactors_eq_of_supportExponent_eq ha hb (by simp only [ha2, hb2])
      ((supportExponent_eq_of_two_notMem ha ha2).trans
        (supportExponent_eq_of_two_notMem hb hb2).symm)
  · exact ha.trans hb.symm

/-- Unconditional uniform linear bound on the pure two-power target family.
No assumption about the infinitude or finitude of Fermat primes is used. -/
theorem fiberCard_two_pow_le (K : ℕ) : Erdos821Aux.fiberCard (2 ^ K) ≤ K + 2 := by
  classical
  let F : Finset ℕ := (Erdos821Aux.totient_fiber_finite (2 ^ K)).toFinset
  have hF : ∀ m ∈ F, Nat.totient m = 2 ^ K := by
    intro m hm
    exact (Set.Finite.mem_toFinset (Erdos821Aux.totient_fiber_finite (2 ^ K))).mp hm
  have hcard : F.card = Erdos821Aux.fiberCard (2 ^ K) := by
    exact (Set.ncard_eq_toFinset_card _ (Erdos821Aux.totient_fiber_finite (2 ^ K))).symm
  let E := F.filter (fun m => 2 ∈ m.primeFactors)
  let O := F.filter (fun m => 2 ∉ m.primeFactors)
  have hE : E.card ≤ K + 1 := by
    have hcount : E.card ≤ (range (K + 1)).card := by
      apply Finset.card_le_card_of_injOn supportExponent
      · intro m hm
        have hmF := (mem_filter.mp hm).1
        exact mem_range.mpr (Nat.lt_succ_of_le (supportExponent_le (hF m hmF)))
      · intro a ha b hb he
        obtain ⟨haF, ha2⟩ := mem_filter.mp ha
        obtain ⟨hbF, hb2⟩ := mem_filter.mp hb
        apply Erdos821Aux.eq_of_primeFactors_eq_of_totient_eq
        · exact primeFactors_eq_of_supportExponent_eq (hF a haF) (hF b hbF)
            (by simp only [ha2, hb2]) he
        · exact (hF a haF).trans (hF b hbF).symm
    simpa only [card_range] using hcount
  have hO : O.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haF, ha2⟩ := mem_filter.mp ha
    obtain ⟨hbF, hb2⟩ := mem_filter.mp hb
    exact odd_preimage_unique (hF a haF) (hF b hbF) ha2 hb2
  have hsplit : E.card + O.card = F.card :=
    card_filter_add_card_filter_not (s := F) (fun m => 2 ∈ m.primeFactors)
  omega

end Erdos821Fresh

#print axioms Erdos821Fresh.sum_two_pow_injective
#print axioms Erdos821Fresh.eq_fermatNumber_of_predecessor_dvd
#print axioms Erdos821Fresh.totient_rad_eq_two_pow_supportExponent
#print axioms Erdos821Fresh.supportExponent_le
#print axioms Erdos821Fresh.odd_preimage_unique
#print axioms Erdos821Fresh.fiberCard_two_pow_le
