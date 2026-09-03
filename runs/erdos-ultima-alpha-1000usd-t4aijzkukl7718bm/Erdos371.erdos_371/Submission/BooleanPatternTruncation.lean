import Submission.FiniteBrunSieve

/-! A finite-pattern Taylor expansion with an explicit factorial-moment
remainder. This is an auxiliary approximation theorem, not a density result. -/
namespace Erdos371.FiniteSieve
open Finset
variable {ι : Type*}

noncomputable def patternDifference (F : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ T ∈ S.powerset, (-1 : ℝ)^(S.card-T.card)*F T

lemma patternDifference_insert [DecidableEq ι] (F : Finset ι → ℝ)
    (S : Finset ι) (a : ι) (ha : a ∉ S) :
    patternDifference F (insert a S) =
      patternDifference (fun T => F (insert a T)-F T) S := by
  unfold patternDifference
  rw [sum_powerset_insert ha, ← sum_add_distrib]
  apply sum_congr rfl
  intro T hT
  have hTS := mem_powerset.mp hT
  have haT : a ∉ T := notMem_mono hTS ha
  have hc := card_le_card hTS
  rw [card_insert_of_notMem ha,card_insert_of_notMem haT]
  rw [show S.card+1-T.card = (S.card-T.card)+1 by omega,
    show S.card+1-(T.card+1) = S.card-T.card by omega,pow_succ]
  ring

lemma patternDifference_inversion (F : Finset ι → ℝ) (S : Finset ι) :
    (∑ T ∈ S.powerset, patternDifference F T) = F S := by
  classical
  induction S using Finset.induction_on generalizing F with
  | empty => simp [patternDifference]
  | @insert a S ha ih =>
    rw [sum_powerset_insert ha,ih]
    have he : (∑ T ∈ S.powerset, patternDifference F (insert a T)) =
        ∑ T ∈ S.powerset, patternDifference (fun U => F (insert a U)-F U) T := by
      apply sum_congr rfl
      intro T hT
      exact patternDifference_insert F T a (notMem_mono (mem_powerset.mp hT) ha)
    rw [he,ih]
    ring

lemma patternDifference_abs_le (F : Finset ι → ℝ) (S : Finset ι)
    (hF : ∀ T ⊆ S, |F T| ≤ 1) : |patternDifference F S| ≤ (2 : ℝ)^S.card := by
  unfold patternDifference
  calc
    _ ≤ ∑ T ∈ S.powerset, |(-1 : ℝ)^(S.card-T.card)*F T| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ S.powerset, (1 : ℝ) := by
      apply sum_le_sum
      intro T hT
      simpa only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] using hF T (mem_powerset.mp hT)
    _ = _ := by simp

noncomputable def patternTruncation (F : Finset ι → ℝ) (S : Finset ι) (L : ℕ) : ℝ :=
  ∑ T ∈ S.powerset, if T.card < L then patternDifference F T else 0

lemma patternTruncation_exact (F : Finset ι → ℝ) (S : Finset ι) (L : ℕ)
    (hL : S.card < L) : patternTruncation F S L = F S := by
  unfold patternTruncation
  have he (T : Finset ι) (hT : T ∈ S.powerset) : T.card < L :=
    (card_le_card (mem_powerset.mp hT)).trans_lt hL
  calc
    _ = ∑ T ∈ S.powerset, patternDifference F T := sum_congr rfl fun T hT => if_pos (he T hT)
    _ = F S := patternDifference_inversion F S

lemma sum_powerset_two_pow_card (S : Finset ι) :
    (∑ T ∈ S.powerset, (2 : ℝ)^T.card) = 3^S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [sum_powerset_insert ha,ih]
    have he : (∑ T ∈ S.powerset, (2 : ℝ)^(insert a T).card) = 2*3^S.card := by
      calc
        _ = ∑ T ∈ S.powerset, (2 : ℝ)*2^T.card := by
          apply sum_congr rfl
          intro T hT
          rw [card_insert_of_notMem (notMem_mono (mem_powerset.mp hT) ha),pow_succ]
          ring
        _ = _ := by rw [← mul_sum,ih]
    rw [he,card_insert_of_notMem ha,pow_succ]
    ring

lemma truncated_powerset_weight_bound (S : Finset ι) (L : ℕ) (hL : L ≤ S.card) :
    (∑ T ∈ S.powerset, if T.card < L then (2 : ℝ)^T.card else 0) ≤
      3^L*(S.card.choose L) := by
  classical
  calc
    _ ≤ ∑ T ∈ S.powerset, ∑ U ∈ S.powersetCard L,
        if T ⊆ U then (2 : ℝ)^T.card else 0 := by
      apply sum_le_sum
      intro T hT
      by_cases hc : T.card < L
      · rw [if_pos hc]
        obtain ⟨U,hTU,hUS,hUc⟩ := exists_subsuperset_card_eq (mem_powerset.mp hT) hc.le hL
        have hu : U ∈ S.powersetCard L := mem_powersetCard.mpr ⟨hUS,hUc⟩
        have hb := single_le_sum (s := S.powersetCard L) (a := U)
          (f := fun U => if T ⊆ U then (2 : ℝ)^T.card else 0)
          (fun U _ => by dsimp only; split_ifs <;> positivity) hu
        simpa only [if_pos hTU] using hb
      · rw [if_neg hc]
        exact sum_nonneg fun U _ => by split_ifs <;> positivity
    _ = ∑ U ∈ S.powersetCard L, 3^L := by
      rw [sum_comm]
      apply sum_congr rfl
      intro U hU
      obtain ⟨hUS,hUc⟩ := mem_powersetCard.mp hU
      rw [← sum_filter]
      have he : S.powerset.filter (fun T => T ⊆ U) = U.powerset := by
        ext T
        simp only [mem_filter,mem_powerset]
        exact ⟨And.right,fun h => ⟨h.trans hUS,h⟩⟩
      rw [he,sum_powerset_two_pow_card,hUc]
    _ = _ := by simp [mul_comm]

/-- The first omitted factorial moment controls arbitrary bounded patterns,
not only avoidance indicators. The constant is deliberately coarse. -/
theorem patternTruncation_error (F : Finset ι → ℝ) (S : Finset ι) (L : ℕ)
    (hF : ∀ T ⊆ S, |F T| ≤ 1) :
    |F S-patternTruncation F S L| ≤ (1+3^L)*(S.card.choose L) := by
  by_cases hL : S.card < L
  · rw [patternTruncation_exact F S L hL,sub_self,abs_zero,
      Nat.choose_eq_zero_of_lt hL,Nat.cast_zero,mul_zero]
  · have hLc : L ≤ S.card := Nat.le_of_not_gt hL
    have hchoose : (1 : ℝ) ≤ S.card.choose L := by
      exact_mod_cast Nat.choose_pos hLc
    have hb : |patternTruncation F S L| ≤ 3^L*(S.card.choose L) := by
      unfold patternTruncation
      calc
        _ ≤ ∑ T ∈ S.powerset, |if T.card < L then patternDifference F T else 0| :=
          abs_sum_le_sum_abs _ _
        _ ≤ ∑ T ∈ S.powerset, if T.card < L then (2 : ℝ)^T.card else 0 := by
          apply sum_le_sum
          intro T hT
          split_ifs
          · exact patternDifference_abs_le F T fun U hU => hF U (hU.trans (mem_powerset.mp hT))
          · simp
        _ ≤ _ := truncated_powerset_weight_bound S L hLc
    have ht := abs_sub (F S) (patternTruncation F S L)
    have hf := hF S Subset.rfl
    nlinarith

#print axioms patternTruncation_error
end Erdos371.FiniteSieve
