import Submission.SharpPairSieve

/-!
# Grouping sieve errors by the union of their prime supports

Both the number of support pairs in a union fiber and their local weights
cost only a fixed exponential in the union's prime-factor count.
-/
open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.Sieve
set_option maxHeartbeats 3000000

lemma union_pair_fiber_card_le {ι : Type*} [DecidableEq ι]
    (W : Finset (Finset ι)) (U : Finset ι) :
    (((W ×ˢ W).filter (fun st => st.1∪st.2=U)).card : ℝ) ≤ (4 : ℝ)^U.card := by
  have hs : (W ×ˢ W).filter (fun st => st.1∪st.2=U) ⊆ U.powerset ×ˢ U.powerset := by
    intro st hst
    have he := (mem_filter.mp hst).2
    exact mem_product.mpr ⟨mem_powerset.mpr (he ▸ subset_union_left),
      mem_powerset.mpr (he ▸ subset_union_right)⟩
  have hh : (((W ×ˢ W).filter (fun st => st.1∪st.2=U)).card : ℝ) ≤
      (U.powerset ×ˢ U.powerset).card := by exact_mod_cast card_le_card hs
  apply hh.trans_eq
  rw [card_product,card_powerset,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,← mul_pow]
  norm_num

lemma weighted_union_error_sum_le {ι : Type*} [DecidableEq ι]
    (W V : Finset (Finset ι)) (w : Finset ι → ℝ) (E : Finset ι → ℝ)
    (hmap : ∀ S ∈ W, ∀ T ∈ W, S∪T ∈ V)
    (hw : ∀ S ∈ W, |w S| ≤ (2 : ℝ)^S.card) (hE : ∀ U ∈ V, 0 ≤ E U) :
    (∑ S ∈ W, ∑ T ∈ W, |w S*w T| *E (S∪T)) ≤
      ∑ U ∈ V, (16 : ℝ)^U.card*E U := by
  rw [← sum_product W W (fun st => |w st.1*w st.2| * E (st.1∪st.2))]
  have hmaps : ∀ st ∈ W ×ˢ W, st.1∪st.2 ∈ V := by
    intro st hst
    exact hmap st.1 (mem_product.mp hst).1 st.2 (mem_product.mp hst).2
  rw [← sum_fiberwise_of_maps_to hmaps]
  apply sum_le_sum
  intro U hU
  have hpoint (st : Finset ι × Finset ι) (hst : st ∈ (W ×ˢ W).filter (fun st => st.1∪st.2=U)) :
      |w st.1*w st.2| *E (st.1∪st.2) ≤ (4 : ℝ)^U.card*E U := by
    obtain ⟨hst,he⟩ := mem_filter.mp hst
    obtain ⟨hS,hT⟩ := mem_product.mp hst
    have hSU : st.1 ⊆ U := he ▸ subset_union_left
    have hTU : st.2 ⊆ U := he ▸ subset_union_right
    have hSbound := (hw st.1 hS).trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (card_le_card hSU))
    have hTbound := (hw st.2 hT).trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (card_le_card hTU))
    rw [he,abs_mul]
    apply mul_le_mul_of_nonneg_right _ (hE U hU)
    have hh := mul_le_mul hSbound hTbound (abs_nonneg _) (by positivity)
    simpa only [← mul_pow,show (2 : ℝ)*2=4 by norm_num] using hh
  calc
    _ ≤ ∑ _st ∈ (W ×ˢ W).filter (fun st => st.1∪st.2=U), (4 : ℝ)^U.card*E U := sum_le_sum hpoint
    _ = (((W ×ˢ W).filter (fun st => st.1∪st.2=U)).card : ℝ)*((4 : ℝ)^U.card*E U) := by
      rw [sum_const,nsmul_eq_mul]
    _ ≤ (4 : ℝ)^U.card*((4 : ℝ)^U.card*E U) :=
      mul_le_mul_of_nonneg_right (union_pair_fiber_card_le W U) (mul_nonneg (by positivity) (hE U hU))
    _ = _ := by rw [← mul_assoc,← mul_pow]; norm_num

lemma prime_union_product_le (P S T : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hS : S ⊆ P) (_hT : T ⊆ P) :
    (∏ p ∈ S∪T, p) ≤ (∏ p ∈ S, p)*(∏ p ∈ T, p) := by
  have hI : 1 ≤ ∏ p ∈ S∩T, p := prod_pos (fun p hp => (hP p (hS (mem_inter.mp hp).1)).pos)
  calc
    _ ≤ (∏ p ∈ S∪T, p)*(∏ p ∈ S∩T, p) := Nat.le_mul_of_pos_right _ hI
    _ = _ := prod_union_inter

lemma prime_support_product_inj (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) (↑P.powerset : Set (Finset ℕ)) := by
  intro S hS T hT he
  have hh := congrArg Nat.primeFactors he
  simpa only [Nat.primeFactors_prod (fun p hp => hP p (mem_powerset.mp hS hp)),
    Nat.primeFactors_prod (fun p hp => hP p (mem_powerset.mp hT hp))] using hh

/-- A single fixed subpower constant handles every growing finite prime pool. -/
theorem exists_union_error_mean_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ Q : ℕ,
      ∀ E : ℕ → ℝ, (∀ d ∈ Icc 1 Q, 0 ≤ E d) →
        (∑ U ∈ P.powerset with (∏ p ∈ U, p) ≤ Q, (16 : ℝ)^U.card*E (∏ p ∈ U, p)) ≤
          C*(Q : ℝ)^ε*∑ d ∈ Icc 1 Q, E d := by
  obtain ⟨C,hC,HC⟩ := exists_card_pow_le_const_product_rpow 16 ε (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro P hP Q E hE
  let V := P.powerset.filter (fun U => (∏ p ∈ U, p) ≤ Q)
  have hprod (U : Finset ℕ) (hU : U ∈ V) : (∏ p ∈ U, p) ∈ Icc 1 Q := by
    exact mem_Icc.mpr ⟨prod_pos (fun p hp => (hP p (mem_powerset.mp (mem_filter.mp hU).1 hp)).pos),
      (mem_filter.mp hU).2⟩
  have hsum : (∑ U ∈ V, E (∏ p ∈ U, p)) ≤ ∑ d ∈ Icc 1 Q, E d := by
    rw [← sum_image ((prime_support_product_inj P hP).mono (filter_subset _ _))]
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨U,hU,rfl⟩ := mem_image.mp hd
      exact hprod U hU
    · exact fun d hd _ => hE d hd
  calc
    _ ≤ ∑ U ∈ V, (C*(Q : ℝ)^ε)*E (∏ p ∈ U, p) := by
      apply sum_le_sum
      intro U hU
      apply mul_le_mul_of_nonneg_right _ (hE _ (hprod U hU))
      apply (HC U (fun p hp => (hP p (mem_powerset.mp (mem_filter.mp hU).1 hp)).pos)).trans
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast (mem_filter.mp hU).2) hε.le) hC.le
    _ = C*(Q : ℝ)^ε*∑ U ∈ V, E (∏ p ∈ U, p) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

end Erdos821.Sieve
