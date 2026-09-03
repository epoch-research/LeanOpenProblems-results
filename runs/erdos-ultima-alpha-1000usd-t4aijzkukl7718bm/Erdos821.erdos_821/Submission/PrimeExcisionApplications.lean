import Submission.PrimeExcision
import Submission.CompositeMultiplicityGain

/-!
# Large fibers and primitive pairs outside arbitrary fixed prime supports

These applications preserve the earlier fixed multiplicity threshold. They
supply new, disjoint input-prime supports but do not amplify the exponent.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

/-- The previously attained exponent holds outside any fixed prime support. -/
theorem infinite_gAvoiding_composite_range (K : ℕ) (hK : 0 < K) (γ : ℝ)
    (hγ : 0 < γ)
    (hupper : γ < 1/2 + 1/(80000000*Sieve.totientRatioAverageConstant+10)) :
    {n : ℕ | 0 < n ∧ (n : ℝ)^γ < (gAvoiding K n : ℝ)}.Infinite := by
  let α := 1/2 + 1/(80000000*Sieve.totientRatioAverageConstant+10)
  have hgap : 0 < (α-γ)/2 := by dsimp [α]; linarith
  apply infinite_gAvoiding_of_infinite_g K hK γ ((α-γ)/2) hγ hgap
  apply infinite_g_gt_composite_uniform
  change γ+(α-γ)/2 < α
  linarith

/-- Extracting a primitive pair from a restricted fiber preserves avoidance. -/
lemma exists_primitive_avoiding_of_one_lt (K n : ℕ) (hcard : 1 < gAvoiding K n) :
    ∃ p : PrimitiveCollisions.Distinct,
      Nat.Coprime p.val.val.val.1 K ∧ Nat.Coprime p.val.val.val.2 K := by
  let S := (finite_avoiding_totient_fiber K n).toFinset
  have hS (m : ℕ) : m ∈ S ↔
      Squarefree m ∧ Nat.Coprime m K ∧ Nat.totient m = n :=
    (finite_avoiding_totient_fiber K n).mem_toFinset
  have hSCard : S.card = gAvoiding K n :=
    (Set.ncard_eq_toFinset_card _ (finite_avoiding_totient_fiber K n)).symm
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (hSCard ▸ hcard)
  obtain ⟨haSq, haK, haφ⟩ := (hS a).mp ha
  obtain ⟨hbSq, hbK, hbφ⟩ := (hS b).mp hb
  let c : PrimitiveCollisions.Collision := ⟨(a,b), haSq, hbSq, haφ.trans hbφ.symm⟩
  let p := PrimitiveCollisions.primitivePart c
  have hne : p.val.val.1 ≠ p.val.val.2 := by
    change a / Nat.gcd a b ≠ b / Nat.gcd a b
    intro h
    apply hab
    calc
      a = Nat.gcd a b * (a / Nat.gcd a b) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
      _ = Nat.gcd a b * (b / Nat.gcd a b) := by rw [h]
      _ = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  refine ⟨⟨p, hne⟩, ?_, ?_⟩
  · exact Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left a b)) haK
  · exact Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right a b)) hbK

/-- A genuinely new primitive relation exists outside every fixed finite set
of input primes. This says nothing about its size relative to that set. -/
theorem exists_distinct_primitive_avoiding (K : ℕ) (hK : 0 < K) :
    ∃ p : PrimitiveCollisions.Distinct,
      Nat.Coprime p.val.val.val.1 K ∧ Nat.Coprime p.val.val.val.2 K := by
  have hC := totientRatioAverageConstant_ge_one
  have H := infinite_gAvoiding_composite_range K hK (1/4) (by norm_num)
    (by have : 0 < 1/(80000000*Sieve.totientRatioAverageConstant+10) := by positivity
        linarith)
  obtain ⟨n, hn, hn1⟩ := H.exists_gt 1
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn1
  have hcard : (1 : ℝ) < gAvoiding K n :=
    (Real.one_lt_rpow hnR (by norm_num : (0 : ℝ) < 1/4)).trans hn.2
  exact exists_primitive_avoiding_of_one_lt K n (by exact_mod_cast hcard)

/-- In particular every prime factor of both inputs can be forced above an
arbitrary cutoff. The inputs remain distinct, coprime, and squarefree. -/
theorem exists_primitive_with_large_prime_factors (B : ℕ) :
    ∃ p : PrimitiveCollisions.Distinct,
      (∀ q : ℕ, q.Prime → q ∣ p.val.val.val.1 → B < q) ∧
      (∀ q : ℕ, q.Prime → q ∣ p.val.val.val.2 → B < q) := by
  obtain ⟨p, hp1, hp2⟩ := exists_distinct_primitive_avoiding B.factorial (Nat.factorial_pos _)
  refine ⟨p, ?_, ?_⟩
  · intro q hq hqp
    by_contra h
    have hd : q ∣ B.factorial := hq.dvd_factorial.mpr (le_of_not_gt h)
    exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hp1 hqp hd)
  · intro q hq hqp
    by_contra h
    have hd : q ∣ B.factorial := hq.dvd_factorial.mpr (le_of_not_gt h)
    exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hp2 hqp hd)

end Erdos821
