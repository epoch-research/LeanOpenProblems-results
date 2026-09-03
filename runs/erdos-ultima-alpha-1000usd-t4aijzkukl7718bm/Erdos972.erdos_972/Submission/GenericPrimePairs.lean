import Submission.PrimeRatioDensity
import Submission.TailTopology

/-!
A comeagre-set result and genuine fixed irrational slopes with infinitely many
prime pairs. This does not exclude exceptional irrational slopes and hence does
not settle the conjecture in `Submission/Spec.lean`.
-/
namespace Erdos972GenericPrimePairs

open Erdos972PrimeRatioDensity Erdos972Topology

lemma exists_irrational_in_primeTail (N : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ α : ℝ, a < α ∧ α < b ∧ Irrational α ∧ α ∈ primeTail N := by
  obtain ⟨p, q, hpN, _, hp, hq, hqa, hqb⟩ := exists_primes_ratio_mem ha hab N
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hstep : (q : ℝ) / p < ((q : ℝ) + 1) / p :=
    div_lt_div_of_pos_right (by linarith) hpR
  have hbnd : (q : ℝ) / p < min b (((q : ℝ) + 1) / p) := lt_min hqb hstep
  obtain ⟨α, hI, hlo, hhi⟩ := exists_irrational_btwn hbnd
  refine ⟨α, hqa.trans hlo, hhi.trans_le (min_le_left _ _), hI, p, q, hpN, hp, hq, ?_, ?_⟩
  · exact (div_lt_iff₀ hpR).mp hlo
  · exact (lt_div_iff₀ hpR).mp (hhi.trans_le (min_le_right _ _))

/-- The harmless open part below one allows us to apply the Baire theorem on all
of `ℝ`, while retaining the exact prime-pair tail condition above one. -/
def augmentedTail (N : ℕ) : Set ℝ := Set.Iio 1 ∪ primeTail N

lemma isOpen_augmentedTail (N : ℕ) : IsOpen (augmentedTail N) :=
  isOpen_Iio.union (isOpen_primeTail N)

lemma dense_augmentedTail (N : ℕ) : Dense (augmentedTail N) := by
  apply dense_iff_exists_between.mpr
  intro a b hab
  by_cases ha : a < 1
  · obtain ⟨α, hlo, hhi⟩ := exists_between (lt_min hab ha)
    exact ⟨α, Or.inl (hhi.trans_le (min_le_right _ _)), hlo,
      hhi.trans_le (min_le_left _ _)⟩
  · obtain ⟨α, hlo, hhi, _, htail⟩ := exists_irrational_in_primeTail N
      (show 0 < a by linarith [le_of_not_gt ha]) hab
    exact ⟨α, Or.inr htail, hlo, hhi⟩

def genericSlopes : Set ℝ := {α | Irrational α} ∩ ⋂ N : ℕ, augmentedTail N

lemma isGδ_genericSlopes : IsGδ genericSlopes :=
  IsGδ.setOf_irrational.inter (IsGδ.iInter (fun N => (isOpen_augmentedTail N).isGδ))

lemma dense_genericSlopes : Dense genericSlopes :=
  Dense.inter_of_Gδ IsGδ.setOf_irrational (IsGδ.iInter (fun N => (isOpen_augmentedTail N).isGδ))
    dense_irrational (dense_iInter_of_isOpen_nat isOpen_augmentedTail dense_augmentedTail)

lemma infinite_primeSet_of_mem_generic {α : ℝ} (hα : α ∈ genericSlopes) (ha : 1 < α) :
    (primeSet α).Infinite := by
  apply (infinite_iff_mem_all_primeTail (by linarith) hα.1).mpr
  intro N
  have h := Set.mem_iInter.mp hα.2 N
  rcases h with h | h
  · exact (not_lt_of_ge ha.le h).elim
  · exact h

/-- Every nonempty real interval above one contains a fixed irrational slope
with infinitely many genuine prime pairs. -/
theorem exists_irrational_infinite_pairs {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) :
    ∃ α : ℝ, a < α ∧ α < b ∧ Irrational α ∧ (primeSet α).Infinite := by
  obtain ⟨α, hα, hlo, hhi⟩ := dense_genericSlopes.exists_mem_open isOpen_Ioo
    (Set.nonempty_Ioo.mpr hab)
  exact ⟨α, hlo, hhi, hα.1, infinite_primeSet_of_mem_generic hα (ha.trans_lt hlo)⟩

open Filter in
/-- The desired implication holds on a comeagre set of irrational real slopes.
The residual quantifier is strictly weaker than the original universal one. -/
theorem eventually_residual_infinite_pairs :
    ∀ᶠ α : ℝ in residual ℝ, Irrational α ∧ (1 < α → (primeSet α).Infinite) := by
  apply Filter.mem_of_superset (residual_of_dense_Gδ isGδ_genericSlopes dense_genericSlopes)
  intro α hα
  exact ⟨hα.1, infinite_primeSet_of_mem_generic hα⟩

#print axioms exists_irrational_infinite_pairs
#print axioms eventually_residual_infinite_pairs

end Erdos972GenericPrimePairs
