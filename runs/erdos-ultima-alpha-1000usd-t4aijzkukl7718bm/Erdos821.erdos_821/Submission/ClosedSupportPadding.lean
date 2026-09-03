import Submission.CommonCore
import Submission.IteratedRadicalLift

/-!
# Padding a fiber to a closed prime support

These finite bounds account for both the increase in output and collisions
in the padding map. They do not assert an improvement of the multiplicity
exponent and do not settle Erdős 821.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821.ClosedPadding

set_option maxHeartbeats 2000000

noncomputable def primeProduct (C : Finset ℕ) : ℕ := ∏ p ∈ C, p
noncomputable def predProduct (C : Finset ℕ) : ℕ := ∏ p ∈ C, (p - 1)

lemma primeProduct_pos (C : Finset ℕ) (hC : ∀ p ∈ C, p.Prime) :
    0 < primeProduct C := Finset.prod_pos (fun p hp => (hC p hp).pos)

lemma predProduct_pos (C : Finset ℕ) (hC : ∀ p ∈ C, p.Prime) :
    0 < predProduct C := Finset.prod_pos (fun p hp => Nat.sub_pos_of_lt (hC p hp).one_lt)

lemma predProduct_eq_totient (C : Finset ℕ) (hC : ∀ p ∈ C, p.Prime) :
    predProduct C = totient (primeProduct C) := (totient_prod_primes C hC).symm

lemma predProduct_subset_dvd {A C : Finset ℕ} (h : A ⊆ C) :
    predProduct A ∣ predProduct C := Finset.prod_dvd_prod_of_subset A C (fun p : ℕ => p - 1) h

lemma union_mem_admissible {n : ℕ} (hn : 0 < n) (C : Finset ℕ)
    (hC : ∀ p ∈ C, p.Prime) (hclosed : (predProduct C).primeFactors ⊆ C)
    {S : Finset ℕ} (hS : S ∈ admissibleSupports n) :
    S ∪ C ∈ admissibleSupports (n * predProduct C) := by
  obtain ⟨hSp, hSn, hSq⟩ := Finset.mem_filter.mp hS
  change predProduct S ∣ n at hSn
  change (n / predProduct S).primeFactors ⊆ S at hSq
  have hSsub := Finset.mem_powerset.mp hSp
  have hSpr : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp (hSsub hp)).2.1
  have hA := predProduct_pos S hSpr
  have hB := predProduct_pos C hC
  have hU := predProduct_pos (S ∪ C) (fun p hp =>
    (Finset.mem_union.mp hp).elim (hSpr p) (hC p))
  have hN : 0 < n * predProduct C := Nat.mul_pos hn hB
  have hprod : predProduct (S ∪ C) * predProduct (S ∩ C) =
      predProduct S * predProduct C := Finset.prod_union_inter
  have hfactor : n * predProduct C =
      predProduct (S ∪ C) * ((n / predProduct S) * predProduct (S ∩ C)) := by
    calc
      n * predProduct C = (n / predProduct S * predProduct S) * predProduct C := by
        rw [Nat.div_mul_cancel hSn]
      _ = (n / predProduct S) * (predProduct S * predProduct C) := by ring
      _ = _ := by rw [← hprod]; ring
  have hquot : n * predProduct C / predProduct (S ∪ C) =
      (n / predProduct S) * predProduct (S ∩ C) := by
    rw [hfactor, Nat.mul_div_right _ hU]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr ?_, ?_, ?_⟩
  · intro p hp
    have hppr : p.Prime := (Finset.mem_union.mp hp).elim (hSpr p) (hC p)
    have hd : p - 1 ∣ n * predProduct C := by
      rcases Finset.mem_union.mp hp with hp | hp
      · exact dvd_mul_of_dvd_left (Finset.mem_filter.mp (hSsub hp)).2.2 _
      · exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun q : ℕ => q - 1) hp) _
    have hle := Nat.le_of_dvd hN hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hppr, hd⟩
  · exact ⟨_, hfactor⟩
  · change (n * predProduct C / predProduct (S ∪ C)).primeFactors ⊆ S ∪ C
    rw [hquot]
    have hqpos : 0 < n / predProduct S := Nat.div_pos (Nat.le_of_dvd hn hSn) hA
    have hIpos := predProduct_pos (S ∩ C) (fun p hp => hC p (Finset.mem_inter.mp hp).2)
    rw [Nat.primeFactors_mul hqpos.ne' hIpos.ne']
    exact Finset.union_subset_union hSq
      ((Nat.primeFactors_mono (predProduct_subset_dvd Finset.inter_subset_right) hB.ne').trans hclosed)

/-- Adjoining a closed prime core has at most one collision for each subset
of that core. No monotonicity of `g` under arbitrary divisibility is used. -/
theorem multiplicity_padding_bound {n : ℕ} (hn : 0 < n) (C : Finset ℕ)
    (hC : ∀ p ∈ C, p.Prime) (hclosed : (predProduct C).primeFactors ⊆ C) :
    g n ≤ 2 ^ C.card * g (n * predProduct C) := by
  have hN : 0 < n * predProduct C := Nat.mul_pos hn (predProduct_pos C hC)
  rw [g_eq_card_admissibleSupports hn, g_eq_card_admissibleSupports hN]
  let f (S : Finset ℕ) := (S ∩ C, S ∪ C)
  have hmap : Set.MapsTo f (admissibleSupports n : Set (Finset ℕ))
      (C.powerset ×ˢ admissibleSupports (n * predProduct C) : Finset (Finset ℕ × Finset ℕ)) := by
    intro S hS
    exact Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
      union_mem_admissible hn C hC hclosed hS⟩
  have hinj : Set.InjOn f (admissibleSupports n : Set (Finset ℕ)) := by
    intro S hS T hT heq
    have hi := congrArg Prod.fst heq
    have hu := congrArg Prod.snd heq
    change S ∩ C = T ∩ C at hi
    change S ∪ C = T ∪ C at hu
    ext p
    by_cases hp : p ∈ C
    · have h := Finset.ext_iff.mp hi p
      simpa only [Finset.mem_inter, hp, and_true] using h
    · have h := Finset.ext_iff.mp hu p
      simpa only [Finset.mem_union, hp, or_false] using h
  simpa only [Finset.card_product, Finset.card_powerset] using
    Finset.card_le_card_of_injOn f hmap hinj

lemma two_pow_card_le_primeProduct (C : Finset ℕ) (hC : ∀ p ∈ C, p.Prime) :
    2 ^ C.card ≤ primeProduct C := by
  simpa only [Finset.prod_const] using
    Finset.prod_le_prod' (s := C) (f := fun _ => 2) (g := id)
      (fun p hp => (hC p hp).two_le)

lemma padded_primeFactors_subset {n : ℕ} (hn : 0 < n) (C : Finset ℕ)
    (hC : ∀ p ∈ C, p.Prime) (hclosed : (predProduct C).primeFactors ⊆ C)
    (hnC : n.primeFactors ⊆ C) : (n * predProduct C).primeFactors ⊆ C := by
  rw [Nat.primeFactors_mul hn.ne' (predProduct_pos C hC).ne']
  exact Finset.union_subset hnC hclosed

lemma radical_le_primeProduct {n : ℕ} (C : Finset ℕ)
    (hC : ∀ p ∈ C, p.Prime) (hnC : n.primeFactors ⊆ C) :
    RadicalLift.radical n ≤ primeProduct C :=
  Finset.prod_le_prod_of_subset_of_one_le' hnC (fun p hp _ => (hC p hp).pos)

/-- Padding gives both a controlled radical and the divisibility needed for
a closed output. These properties alone do not amplify the fiber. -/
theorem padded_output_structure {n : ℕ} (hn : 0 < n) (C : Finset ℕ)
    (hC : ∀ p ∈ C, p.Prime) (hclosed : (predProduct C).primeFactors ⊆ C)
    (hnC : n.primeFactors ⊆ C) :
    n ≤ n * predProduct C ∧ n * predProduct C ≤ n * primeProduct C ∧
    RadicalLift.radical (n * predProduct C) ≤ primeProduct C ∧
    totient (RadicalLift.radical (n * predProduct C)) ∣ n * predProduct C := by
  have hsub := padded_primeFactors_subset hn C hC hclosed hnC
  refine ⟨Nat.le_mul_of_pos_right n (predProduct_pos C hC), ?_,
    radical_le_primeProduct C hC hsub, ?_⟩
  · apply Nat.mul_le_mul_left
    rw [predProduct_eq_totient C hC]
    exact Nat.totient_le _
  · have hd : RadicalLift.radical (n * predProduct C) ∣ primeProduct C :=
      Finset.prod_dvd_prod_of_subset _ _ id hsub
    have h := Nat.totient_dvd_of_dvd hd
    rw [← predProduct_eq_totient C hC] at h
    exact h.trans (dvd_mul_left _ _)

/-- The exact exponent budget of this padding bound. In particular, it
preserves any strictly smaller exponent when the core is subpower-sized;
it does not produce an exponent larger than the input exponent. -/
theorem padding_power_bound {n : ℕ} (hn : 0 < n) (C : Finset ℕ)
    (hC : ∀ p ∈ C, p.Prime) (hclosed : (predProduct C).primeFactors ⊆ C)
    (α γ η : ℝ) (hγ : 0 ≤ γ) (hbudget : (1 + η) * γ + η ≤ α)
    (hcore : (primeProduct C : ℝ) ≤ (n : ℝ) ^ η)
    (hg : (n : ℝ) ^ α < g n) :
    ((n * predProduct C : ℕ) : ℝ) ^ γ < g (n * predProduct C) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsize : ((n * predProduct C : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 + η) := by
    rw [Real.rpow_add hnR, Real.rpow_one, Nat.cast_mul]
    apply mul_le_mul_of_nonneg_left _ hnR.le
    exact (show (predProduct C : ℝ) ≤ primeProduct C by
      exact_mod_cast (by rw [predProduct_eq_totient C hC]; exact Nat.totient_le _)).trans hcore
  have hcount : (g n : ℝ) ≤ (n : ℝ) ^ η * g (n * predProduct C) := by
    have h := multiplicity_padding_bound hn C hC hclosed
    calc
      (g n : ℝ) ≤ (2 : ℝ) ^ C.card * (g (n * predProduct C) : ℝ) := by exact_mod_cast h
      _ ≤ (primeProduct C : ℝ) * (g (n * predProduct C) : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast two_pow_card_le_primeProduct C hC)
          (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hcore (Nat.cast_nonneg _)
  have hexp : (n : ℝ) ^ ((1 + η) * γ) < g (n * predProduct C) := by
    apply (mul_lt_mul_iff_right₀ (Real.rpow_pos_of_pos hnR η)).mp
    calc
      (n : ℝ) ^ η * (n : ℝ) ^ ((1 + η) * γ) =
          (n : ℝ) ^ ((1 + η) * γ + η) := by rw [Real.rpow_add hnR]; ring
      _ ≤ (n : ℝ) ^ α := Real.rpow_le_rpow_of_exponent_le hn1 hbudget
      _ < g n := hg
      _ ≤ _ := hcount
  have hpow : ((n * predProduct C : ℕ) : ℝ) ^ γ ≤ (n : ℝ) ^ ((1 + η) * γ) := by
    calc
      ((n * predProduct C : ℕ) : ℝ) ^ γ ≤ ((n : ℝ) ^ (1 + η)) ^ γ :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hsize hγ
      _ = (n : ℝ) ^ ((1 + η) * γ) := (Real.rpow_mul hnR.le _ _).symm
  exact hpow.trans_lt hexp

lemma primesBelow_closed (y : ℕ) :
    (predProduct y.primesBelow).primeFactors ⊆ y.primesBelow := by
  intro q hq
  have hqpr := Nat.prime_of_mem_primeFactors hq
  obtain ⟨p, hp, hqp⟩ := (hqpr.prime.dvd_finset_prod_iff _).mp
    (Nat.dvd_of_mem_primeFactors hq)
  obtain ⟨hpy, hppr⟩ := Nat.mem_primesBelow.mp hp
  have hqle := Nat.le_of_dvd (Nat.sub_pos_of_lt hppr.one_lt) hqp
  exact Nat.mem_primesBelow.mpr ⟨by omega, hqpr⟩

lemma primeProduct_primesBelow_le (y B : ℕ) (hB : 1 ≤ B) (hyB : y ≤ B) :
    primeProduct y.primesBelow ≤ B ^ y := by
  have hcard : y.primesBelow.card ≤ y := by
    have hsub : y.primesBelow ⊆ Finset.range y :=
      fun p hp => Finset.mem_range.mpr (Nat.mem_primesBelow.mp hp).1
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  calc
    primeProduct y.primesBelow ≤ B ^ y.primesBelow.card :=
      Finset.prod_le_pow_card _ id B (fun p hp => (Nat.mem_primesBelow.mp hp).1.le.trans hyB)
    _ ≤ _ := Nat.pow_le_pow_right hB hcard

end Erdos821.ClosedPadding
