import Submission.GeometricThresholdSummability

/-! Reciprocal summability of three-term-progression-free subsets of the naturals.
This is the three-term case, not the arbitrary-length Erdős conjecture. -/
namespace Erdos3ThreeAPReciprocalSummability
open Finset Erdos3GeometricThresholdSummability
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

noncomputable def harmonicScale (A : Set ℕ) (j : ℕ) : ℝ :=
  (initialCount A (2^(j+1))).card/(2 : ℝ)^j

lemma harmonicScale_eq (A : Set ℕ) (j : ℕ) : harmonicScale A j = 2*scaleDensity A (j+1) := by
  unfold harmonicScale scaleDensity
  rw [pow_succ]
  ring

lemma harmonicScale_summable (A : Set ℕ) (hfree : ThreeAPFree A) : Summable (harmonicScale A) := by
  have h := ((summable_nat_add_iff 1).mpr (threeAPFree_scaleDensity_summable A hfree)).mul_left (2 : ℝ)
  change Summable (fun j ↦ harmonicScale A j)
  simpa only [harmonicScale_eq] using h

lemma finite_harmonic_le (A : Set ℕ) (hfree : ThreeAPFree A) (S : Finset ℕ)
    (hSA : (S : Set ℕ) ⊆ A) :
    (∑ n ∈ S, 1/(n : ℝ)) ≤ ∑' j : ℕ, harmonicScale A j := by
  let S' := S.erase 0
  let J := S'.image (Nat.log 2)
  have hfiber (j : ℕ) :
      (∑ n ∈ S'.filter (fun n ↦ Nat.log 2 n = j), 1/(n : ℝ)) ≤ harmonicScale A j := by
    let T := S'.filter (fun n ↦ Nat.log 2 n = j)
    have hTsub : T ⊆ initialCount A (2^(j+1)) := by
      intro n hn
      obtain ⟨hnS,hnj⟩ := mem_filter.mp hn
      apply mem_filter.mpr
      refine ⟨mem_range.mpr ?_,hSA (erase_subset _ _ hnS)⟩
      simpa only [hnj] using Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n
    have hcard : T.card ≤ (initialCount A (2^(j+1))).card := card_le_card hTsub
    calc
      _ ≤ ∑ _n ∈ T, 1/(2 : ℝ)^j := by
        apply sum_le_sum
        intro n hn
        obtain ⟨hnS,hnj⟩ := mem_filter.mp hn
        have hn0 := (mem_erase.mp hnS).1
        have hp : 2^j ≤ n := by simpa only [hnj] using Nat.pow_log_le_self 2 hn0
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hp)
      _ = (T.card : ℝ)/(2 : ℝ)^j := by simp [div_eq_mul_inv]
      _ ≤ harmonicScale A j := div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have he : (∑ n ∈ S, 1/(n : ℝ)) = ∑ n ∈ S', 1/(n : ℝ) := by
    by_cases h0 : 0 ∈ S
    · simpa only [Nat.cast_zero, div_zero, add_zero] using
        (sum_erase_add S (fun n : ℕ ↦ 1/(n : ℝ)) h0).symm
    · simp only [S',erase_eq_of_notMem h0]
  calc
    _ = ∑ n ∈ S', 1/(n : ℝ) := he
    _ = ∑ j ∈ J, ∑ n ∈ S'.filter (fun n ↦ Nat.log 2 n = j), 1/(n : ℝ) :=
      (sum_fiberwise_of_maps_to (fun n hn ↦ mem_image_of_mem (Nat.log 2) hn)
        (fun n : ℕ ↦ 1/(n : ℝ))).symm
    _ ≤ ∑ j ∈ J, harmonicScale A j := sum_le_sum (fun j _ ↦ hfiber j)
    _ ≤ _ := (harmonicScale_summable A hfree).sum_le_tsum J (fun j _ ↦ by unfold harmonicScale; positivity)

/-- Every three-term-progression-free subset of the naturals has convergent reciprocal sum. -/
theorem threeAPFree_reciprocal_summable (A : Set ℕ) (hfree : ThreeAPFree A) :
    Summable (fun a : A ↦ 1/(a : ℝ)) := by
  apply summable_of_sum_le (c := ∑' j : ℕ, harmonicScale A j) (fun a ↦ by positivity)
  intro F
  let e : A ↪ ℕ := ⟨Subtype.val,Subtype.val_injective⟩
  have hsub : (F.map e : Set ℕ) ⊆ A := by
    intro n hn
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hn
    exact a.property
  simpa [e] using finite_harmonic_le A hfree (F.map e) hsub

lemma nat_progression (a d k : ℕ) (hd : 0 < d) :
    ((fun i : ℕ ↦ a+i*d) '' Set.Iio k).IsAPOfLengthWith k a d := by
  have hinj : Function.Injective (fun i : ℕ ↦ a+i*d) := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
  constructor
  · change ((fun i : ℕ ↦ a+i*d) '' Set.Iio k).encard = (k : ℕ∞)
    rw [hinj.encard_image]
    exact Set.Nat.encard_range k
  · ext x
    simp [Set.mem_image]

/-- The exact three-term special case of the requested conclusion. -/
theorem nonsummable_contains_three_term_AP (A : Set ℕ)
    (hdiv : ¬ Summable (fun a : A ↦ 1/(a : ℝ))) : ∃ S ⊆ A, S.IsAPOfLength 3 := by
  have hnot : ¬ ThreeAPFree A := fun hf ↦ hdiv (threeAPFree_reciprocal_summable A hf)
  unfold ThreeAPFree at hnot
  push_neg at hnot
  obtain ⟨a,ha,b,hb,c,hc,he,hab⟩ := hnot
  have hordered : ∃ a b c : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a < b ∧ a+c = b+b := by
    by_cases hlt : a < b
    · exact ⟨a,b,c,ha,hb,hc,hlt,he⟩
    · exact ⟨c,b,a,hc,hb,ha,by omega,by omega⟩
  obtain ⟨a,b,c,ha,hb,hc,hab,he⟩ := hordered
  let d := b-a
  have hd : 0 < d := by dsimp [d]; omega
  have hmem : ∀ i < 3, a+i*d ∈ A := by
    intro i hi
    interval_cases i
    · simpa using ha
    · convert hb using 1 <;> dsimp [d] <;> omega
    · convert hc using 1 <;> dsimp [d] <;> omega
  refine ⟨(fun i : ℕ ↦ a+i*d) '' Set.Iio 3,?_,a,d,nat_progression a d 3 hd⟩
  rintro n ⟨i,hi,rfl⟩
  exact hmem i hi

#print axioms threeAPFree_reciprocal_summable
#print axioms nonsummable_contains_three_term_AP
end Erdos3ThreeAPReciprocalSummability
