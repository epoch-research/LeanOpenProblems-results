import Submission.Reduction

/-! A finite obstruction to a greedy-prefix compression proof of the harmonic
bound. This does not disprove an infinite greedy-weight bound or Erdős 3. -/
namespace Erdos3GreedyCompressionCheck

open Finset Erdos3Reduction
set_option maxHeartbeats 1000000

def FinThreeFree (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a+c=b+b → a=b

instance (S : Finset ℕ) : Decidable (FinThreeFree S) := by
  unfold FinThreeFree
  infer_instance

lemma finThreeFree_iff (S : Finset ℕ) :
    FinThreeFree S ↔ ThreeAPFree (S : Set ℕ) := by
  constructor
  · exact fun h a ha b hb c hc he ↦ h a ha b hb c hc he
  · exact fun h a ha b hb c hc he ↦ h ha hb hc he

/-- Scan the positive integers in order, accepting an integer whenever possible. -/
def greedy : ℕ → Finset ℕ
  | 0 => ∅
  | n+1 => if FinThreeFree (insert (n+1) (greedy n)) then
      insert (n+1) (greedy n) else greedy n

lemma greedy_free (n : ℕ) : ThreeAPFree (greedy n : Set ℕ) := by
  rw [← finThreeFree_iff]
  induction n with
  | zero => simp [greedy, FinThreeFree]
  | succ n ih =>
    rw [greedy]
    split
    · assumption
    · exact ih

lemma greedy_nine : greedy 9 = {1,2,4,5} := by decide +kernel

def witness : Finset ℕ := {1,2,4,8,9}

lemma witness_free : ThreeAPFree (witness : Set ℕ) := by
  rw [← finThreeFree_iff]
  decide +kernel

lemma witness_range : witness ⊆ Icc 1 9 := by decide +kernel

lemma witness_weight : recipWeight witness = 143/72 := by
  norm_num [recipWeight, witness]

lemma greedy_nine_weight : recipWeight (greedy 9) = 39/20 := by
  rw [greedy_nine]
  norm_num [recipWeight]

/-- An extremal-weight set cannot in general be replaced by the greedy prefix
at the same endpoint without losing reciprocal weight. -/
theorem no_greedy_prefix_domination :
    ¬ (∀ N : ℕ, ∀ S : Finset ℕ, S ⊆ Icc 1 N →
      ThreeAPFree (S : Set ℕ) → recipWeight S ≤ recipWeight (greedy N)) := by
  intro h
  have hh := h 9 witness witness_range witness_free
  rw [witness_weight, greedy_nine_weight] at hh
  norm_num at hh

#print axioms greedy_free
#print axioms no_greedy_prefix_domination
end Erdos3GreedyCompressionCheck
