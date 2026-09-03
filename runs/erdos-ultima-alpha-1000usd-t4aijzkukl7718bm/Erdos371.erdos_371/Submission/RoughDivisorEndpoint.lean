import Submission.HighComplementAlgebra
import Submission.SparseTailExplore

/-! Sampling bounds for squarefree rough divisors of consecutive integers. -/
namespace Erdos371
open Finset

lemma consecutive_shifted_root_count_le (d N : ℕ) (hd : 0 < d) :
    ((range N).filter fun n => d ∣ (n+1)*(n+2)).card ≤ (N/d+1)*d.divisors.card := by
  have hh : ((range N).filter fun n => d ∣ (n+1)*(n+2)).card ≤
      ((range (N/d+1)) ×ˢ ((range d).filter fun r => d ∣ r*(r+1))).card := by
    apply card_le_card_of_injOn (fun n => ((n+1)/d,(n+1)%d))
    · intro n hn
      change n ∈ (range N).filter (fun n => d ∣ (n+1)*(n+2)) at hn
      obtain ⟨hn,hr⟩ := mem_filter.mp hn
      have hnN : n+1 ≤ N := by have := mem_range.mp hn; omega
      change ((n+1)/d,(n+1)%d) ∈ _
      apply mem_product.mpr
      refine ⟨mem_range.mpr (by have := Nat.div_le_div_right (c := d) hnN; omega), ?_⟩
      apply mem_filter.mpr
      refine ⟨mem_range.mpr (Nat.mod_lt _ hd), ?_⟩
      rw [Nat.dvd_iff_mod_eq_zero] at hr ⊢
      calc
        ((n+1)%d*((n+1)%d+1))%d = ((n+1)*(n+2))%d := by
          simp only [Nat.mul_mod,Nat.mod_mod,Nat.mod_add_mod]
        _ = 0 := hr
    · intro n hn m hm he
      have hq := congrArg Prod.fst he
      have hr := congrArg Prod.snd he
      dsimp only at hq hr
      have heq : n+1=m+1 := by
        rw [← Nat.div_add_mod (n+1) d,← Nat.div_add_mod (m+1) d,hq,hr]
      omega
  rw [card_product,card_range] at hh
  exact hh.trans (Nat.mul_le_mul_left _ (consecutive_root_count_le_divisors d))

lemma consecutive_shifted_root_proportion_le (d N : ℕ) (hd : 0 < d) (hdN : d ≤ N) :
    (((range N).filter fun n => d ∣ (n+1)*(n+2)).card : ℝ)/N ≤ 2*(d.divisors.card : ℝ)/d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNR : (0 : ℝ) < N := hdR.trans_le (by exact_mod_cast hdN)
  have hdiv : ((N/d : ℕ) : ℝ)+1 ≤ 2*(N : ℝ)/d := by
    have hdiv := Nat.cast_div_le (α := ℝ) (m := N) (n := d)
    have hfrac : (1 : ℝ) ≤ (N : ℝ)/d := (le_div_iff₀ hdR).mpr (by simpa only [one_mul] using (show (d : ℝ) ≤ N by exact_mod_cast hdN))
    calc
      _ ≤ (N : ℝ)/d+(N : ℝ)/d := add_le_add hdiv hfrac
      _ = _ := by ring
  calc
    _ ≤ (((N/d+1)*d.divisors.card : ℕ) : ℝ)/N := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast consecutive_shifted_root_count_le d N hd) hNR.le
    _ ≤ (2*(N : ℝ)/d)*(d.divisors.card : ℝ)/N := by
      push_cast
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg _)) hNR.le
    _ = _ := by field_simp

lemma rough_squarefree_divisors_card_le (W L N d : ℕ) (hW : 1 < W) (hWN : N ≤ W^L)
    (hd : Squarefree d) (hdN : d ≤ N) (hrough : ∀ p ∈ d.primeFactors, W < p) :
    d.divisors.card ≤ 2^L := by
  have hc : d.primeFactors.card ≤ L := by
    apply FiniteSieve.short_prime_product_card_le _ W L hW hrough
    rw [Nat.prod_primeFactors_of_squarefree hd]
    exact hdN.trans hWN
  exact (squarefree_divisors_card_le d hd).trans (Nat.pow_le_pow_right (by norm_num) hc)

/-- Union bound retaining the rough reciprocal mass rather than the number
of possible moduli. -/
theorem rough_divisor_event_proportion_le (S : Finset ℕ) (W L N : ℕ)
    (hW : 1 < W) (hWN : N ≤ W^L)
    (hS : ∀ d ∈ S, Squarefree d ∧ d ≤ N ∧ ∀ p ∈ d.primeFactors, W < p) :
    (((range N).filter fun n => ∃ d ∈ S, d ∣ (n+1)*(n+2)).card : ℝ)/N ≤
      (2 : ℝ)^(L+1)*(∑ d ∈ S, (1 : ℝ)/d) := by
  classical
  have hc : ((range N).filter fun n => ∃ d ∈ S, d ∣ (n+1)*(n+2)).card ≤
      ∑ d ∈ S, ((range N).filter fun n => d ∣ (n+1)*(n+2)).card := by
    apply le_trans (b := (S.biUnion (fun d => (range N).filter fun n => d ∣ (n+1)*(n+2))).card)
    · apply card_le_card
      intro n hn
      obtain ⟨hn,d,hd,hdiv⟩ := mem_filter.mp hn
      exact mem_biUnion.mpr ⟨d,hd,mem_filter.mpr ⟨hn,hdiv⟩⟩
    · exact card_biUnion_le
  calc
    _ ≤ (∑ d ∈ S, (((range N).filter fun n => d ∣ (n+1)*(n+2)).card : ℝ))/N := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg N)
    _ = ∑ d ∈ S, (((range N).filter fun n => d ∣ (n+1)*(n+2)).card : ℝ)/N := sum_div ..
    _ ≤ ∑ d ∈ S, (2 : ℝ)^(L+1)/d := by
      apply sum_le_sum
      intro d hd
      obtain ⟨hdSq,hdN,hr⟩ := hS d hd
      apply (consecutive_shifted_root_proportion_le d N (Nat.pos_of_ne_zero hdSq.ne_zero) hdN).trans
      have hdcard : (d.divisors.card : ℝ) ≤ (2 : ℝ)^L := by
        exact_mod_cast rough_squarefree_divisors_card_le W L N d hW hWN hdSq hdN hr
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
      rw [pow_succ]
      nlinarith
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intros; ring

#print axioms rough_divisor_event_proportion_le
#print axioms consecutive_shifted_root_proportion_le
#print axioms rough_squarefree_divisors_card_le
end Erdos371
