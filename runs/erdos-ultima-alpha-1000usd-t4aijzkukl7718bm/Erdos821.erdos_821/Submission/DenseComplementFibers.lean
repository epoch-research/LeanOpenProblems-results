import Submission.DenseDivisorEntropy
import Submission.SquarefreeInput

/-!
# Complementary subset fibers at a comparable-sized divisor output

Complementation preserves restricted prime-subset fiber counts. This gives
squarefree fibers above the square root of the full predecessor product,
with small radicals and an explicit divisor-count loss. It is not a
near-linear multiplicity bound and does not settle Erdős 821.
-/

open Nat Finset Filter
open scoped Classical BigOperators Topology

namespace Erdos821.DensePredecessors

set_option maxHeartbeats 2000000

noncomputable def predProduct (P : Finset ℕ) : ℕ := ∏ p ∈ P, (p-1)

noncomputable def subsetPredFiber (P : Finset ℕ) (d : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun T => predProduct T = d)

lemma mem_subsetPredFiber (P T : Finset ℕ) (d : ℕ) :
    T ∈ subsetPredFiber P d ↔ T ⊆ P ∧ predProduct T = d := by
  simp [subsetPredFiber]

lemma predProduct_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : 0 < predProduct P :=
  prod_pos (fun p hp => Nat.sub_pos_of_lt (hP p hp).one_lt)

lemma subsetPredFiber_card_le_squarefree (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (d : ℕ) :
    (subsetPredFiber P d).card ≤ gSquarefree d := by
  let I := (subsetPredFiber P d).image (fun T => ∏ p ∈ T, p)
  have hinj : Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p)
      (↑(subsetPredFiber P d) : Set (Finset ℕ)) := by
    intro T hT U hU he
    have hTP := ((mem_subsetPredFiber P T d).mp hT).1
    have hUP := ((mem_subsetPredFiber P U d).mp hU).1
    have h := congrArg Nat.primeFactors he
    simpa only [Nat.primeFactors_prod (fun p hp => hP p (hTP hp)),
      Nat.primeFactors_prod (fun p hp => hP p (hUP hp))] using h
  have hc : I.card = (subsetPredFiber P d).card := card_image_of_injOn hinj
  have hsub : (↑I : Set ℕ) ⊆ {m : ℕ | Squarefree m ∧ Nat.totient m = d} := by
    intro m hm
    obtain ⟨T,hT,rfl⟩ := mem_image.mp hm
    obtain ⟨hTP,hTd⟩ := (mem_subsetPredFiber P T d).mp hT
    refine ⟨squarefree_prod_of_primes T (fun p hp => hP p (hTP hp)),?_⟩
    rw [totient_prod_primes T (fun p hp => hP p (hTP hp))]
    exact hTd
  have h := Set.ncard_le_ncard hsub (finite_squarefree_totient_fiber d)
  simpa only [Set.ncard_coe_finset,hc,gSquarefree] using h

/-- Complementing each subset gives an injection into the complementary
output fiber. The reverse injection is available by applying this again. -/
lemma subsetPredFiber_complement_card_le (P : Finset ℕ) (d : ℕ) (hd : 0 < d) :
    (subsetPredFiber P d).card ≤ (subsetPredFiber P (predProduct P/d)).card := by
  let F := subsetPredFiber P d
  have hsub : F.image (fun T => P\T) ⊆ subsetPredFiber P (predProduct P/d) := by
    intro U hU
    obtain ⟨T,hT,rfl⟩ := mem_image.mp hU
    obtain ⟨hTP,hTd⟩ := (mem_subsetPredFiber P T d).mp hT
    apply (mem_subsetPredFiber _ _ _).mpr
    refine ⟨sdiff_subset,?_⟩
    have he : predProduct (P\T)*d = predProduct P := by
      rw [← hTd]
      exact prod_sdiff hTP
    rw [← he,Nat.mul_div_cancel _ hd]
  have hinj : Set.InjOn (fun T : Finset ℕ => P\T) (↑F : Set (Finset ℕ)) := by
    intro T hT U hU he
    have hTP := ((mem_subsetPredFiber P T d).mp hT).1
    have hUP := ((mem_subsetPredFiber P U d).mp hU).1
    have h := congrArg (fun V : Finset ℕ => P\V) he
    simpa only [sdiff_sdiff_eq_self hTP,sdiff_sdiff_eq_self hUP] using h
  have h := card_le_card hsub
  rwa [Finset.card_image_of_injOn hinj] at h

/-- A largest restricted subset fiber can be chosen on the upper side of
the complementary pair. The output stays at least sqrt(N). -/
theorem exists_large_complementary_squarefree_fiber (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    ∃ d ∈ (predProduct P).divisors, predProduct P ≤ d^2 ∧
      2^P.card ≤ (predProduct P).divisors.card*gSquarefree d := by
  have hN := predProduct_pos P hP
  obtain ⟨d,hd,hmax⟩ := exists_max_image (predProduct P).divisors
    (fun d => (subsetPredFiber P d).card)
    ⟨1,Nat.mem_divisors.mpr ⟨one_dvd _,hN.ne'⟩⟩
  have hmap : Set.MapsTo predProduct (↑P.powerset : Set (Finset ℕ))
      (↑(predProduct P).divisors : Set ℕ) := by
    intro T hT
    exact Nat.mem_divisors.mpr ⟨prod_dvd_prod_of_subset _ _ _ (mem_powerset.mp hT),hN.ne'⟩
  have hc : 2^P.card ≤ (predProduct P).divisors.card*(subsetPredFiber P d).card := by
    calc
      _ = P.powerset.card := (card_powerset P).symm
      _ = ∑ a ∈ (predProduct P).divisors, (subsetPredFiber P a).card :=
        card_eq_sum_card_fiberwise hmap
      _ ≤ ∑ _a ∈ (predProduct P).divisors, (subsetPredFiber P d).card := sum_le_sum hmax
      _ = _ := by simp
  by_cases hbig : predProduct P ≤ d^2
  · exact ⟨d,hd,hbig,hc.trans (Nat.mul_le_mul_left _
      (subsetPredFiber_card_le_squarefree P hP d))⟩
  let e := predProduct P/d
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have heq : e*d = predProduct P := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
  have heMem : e ∈ (predProduct P).divisors := Nat.mem_divisors.mpr
    ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd),hN.ne'⟩
  have hde : d ≤ e := by nlinarith only [heq,hbig]
  have heBig : predProduct P ≤ e^2 := by
    nlinarith only [heq,Nat.mul_le_mul_left e hde]
  refine ⟨e,heMem,heBig,hc.trans (Nat.mul_le_mul_left _ ?_)⟩
  exact (subsetPredFiber_complement_card_le P d hd0).trans
    (subsetPredFiber_card_le_squarefree P hP e)

lemma exists_dense_complementary_fiber (X : ℕ) :
    ∃ d ∈ (predecessorProduct X).divisors, predecessorProduct X ≤ d^2 ∧
      2^(X+1).primesBelow.card ≤ (predecessorProduct X).divisors.card*gSquarefree d := by
  exact exists_large_complementary_squarefree_fiber (X+1).primesBelow
    (fun p hp => (Nat.mem_primesBelow.mp hp).2)

lemma radical_divisor_le_pool (X d : ℕ) (hd : d ∣ predecessorProduct X) :
    (∏ q ∈ d.primeFactors, q) ≤ radicalPool X := by
  have hsub := Nat.primeFactors_mono hd (predecessorProduct_pos X).ne'
  rw [predecessorProduct_primeFactors] at hsub
  exact prod_le_prod_of_subset_of_one_le' hsub (fun q hq _ => (support_prime hq).pos)

/-- The selected squarefree fiber has a comparable-sized output, a subpower
radical, and only an exp(o(X/log X)) loss from all prime-subset choices.
The count here is not a fixed positive power of the selected output. -/
theorem eventually_dense_complementary_fiber (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∃ d ∈ (predecessorProduct (2^(128*m^2))).divisors,
      predecessorProduct (2^(128*m^2)) ≤ d^2 ∧
      ((∏ q ∈ d.primeFactors, q : ℕ) : ℝ) ≤ (d : ℝ)^ε ∧
      (2 : ℝ)^((2^(128*m^2)+1).primesBelow.card) ≤
        Real.exp (η*(2 : ℝ)^(128*m^2)/(m : ℝ)^2)*(gSquarefree d : ℝ) := by
  filter_upwards [eventually_radicalPool_le_predecessorProduct_rpow (ε/2) (by positivity),
    eventually_divisors_le_exp_prime_scale η hη] with m hrad hcount
  obtain ⟨d,hd,hsize,hfiber⟩ := exists_dense_complementary_fiber (2^(128*m^2))
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  refine ⟨d,hd,hsize,?_,?_⟩
  · calc
      _ ≤ (radicalPool (2^(128*m^2)) : ℝ) := by
        exact_mod_cast radical_divisor_le_pool _ d (Nat.dvd_of_mem_divisors hd)
      _ ≤ (predecessorProduct (2^(128*m^2)) : ℝ)^(ε/2) := hrad
      _ ≤ ((d : ℝ)^2)^(ε/2) := Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast hsize) (by positivity)
      _ = _ := by
        rw [← Real.rpow_natCast_mul (Nat.cast_nonneg d)]
        congr 1
        push_cast
        ring
  · have hf : (2 : ℝ)^((2^(128*m^2)+1).primesBelow.card) ≤
        ((predecessorProduct (2^(128*m^2))).divisors.card : ℝ)*(gSquarefree d : ℝ) := by
      exact_mod_cast hfiber
    exact hf.trans (mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _))

end Erdos821.DensePredecessors
