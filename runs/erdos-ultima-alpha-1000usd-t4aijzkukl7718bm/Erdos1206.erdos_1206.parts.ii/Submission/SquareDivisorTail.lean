import Submission.PrimeBlockVariance

/-! Large square divisors have uniformly small density in every prefix. -/
namespace Erdos1206.SquareDivisorTail
open Finset Filter PrimeBlockVariance
open scoped Classical Topology

lemma finite_tail_small (f : ℕ → ℝ) (hf : ∀ n,0 ≤ f n) (hs : Summable f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ,0 < K ∧ ∀ P : Finset ℕ,(∀ b ∈ P,K < b) → ∑b∈P,f b ≤ ε := by
  have ht := hs.hasSum.tendsto_sum_nat
  have hev : ∀ᶠ K : ℕ in atTop,(∑'b,f b)-ε < ∑b∈range K,f b :=
    ht.eventually (eventually_gt_nhds (by linarith))
  obtain ⟨K,hK⟩ := hev.exists
  refine ⟨K+1,by omega,fun P hP => ?_⟩
  have hdis : Disjoint (range K) P := by
    apply disjoint_left.mpr
    intro b hb hp
    have := hP b hp
    have := mem_range.mp hb
    omega
  have hh := hs.sum_le_tsum (range K ∪ P) (fun b _ => hf b)
  rw [sum_union hdis] at hh
  linarith

noncomputable def bad (K N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => ∃ b : ℕ,K < b ∧ b^2 ∣ n)

lemma count_le (K N : ℕ) {ε : ℝ}
    (ht : ∀ P : Finset ℕ,(∀ b ∈ P,K < b) → ∑b∈P,(1:ℝ)/(b:ℝ)^2 ≤ ε) :
    (bad K N).card ≤ (N:ℝ)*ε := by
  let P := (range (N+1)).filter (fun b => K < b)
  let B (b : ℕ) := (Icc 1 N).filter (fun n => b^2 ∣ n)
  have hsub : bad K N ⊆ P.biUnion B := by
    intro n hn
    obtain ⟨hn, b,hb,hbn⟩ := mem_filter.mp hn
    have hbN : b ≤ N := by
      have hsq : b^2 ≤ n := Nat.le_of_dvd (mem_Icc.mp hn).1 hbn
      have hb2 : b ≤ b^2 := Nat.le_self_pow (by decide) b
      exact (hb2.trans hsq).trans (mem_Icc.mp hn).2
    exact mem_biUnion.mpr ⟨b,mem_filter.mpr ⟨mem_range.mpr (by omega),hb⟩,mem_filter.mpr ⟨hn,hbn⟩⟩
  have hcard : ((bad K N).card:ℝ) ≤ ∑b∈P,((B b).card:ℝ) := by
    exact_mod_cast (card_le_card hsub).trans card_biUnion_le
  have hc (b : ℕ) : ((B b).card:ℝ)=((N/b^2:ℕ):ℝ) := by
    simpa only [indicator,sum_boole] using sum_indicator N (b^2)
  calc
    _ ≤ ∑b∈P,((N/b^2:ℕ):ℝ) := by simpa only [hc] using hcard
    _ ≤ ∑b∈P,(N:ℝ)/(b:ℝ)^2 := by
      apply sum_le_sum
      intro b _
      simpa only [Nat.cast_pow] using (Nat.cast_div_le (m := N) (n := b^2) : ((N/b^2:ℕ):ℝ) ≤ (N:ℝ)/(b^2:ℕ))
    _ = (N:ℝ)*(∑b∈P,(1:ℝ)/(b:ℝ)^2) := by simp [mul_sum,div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (ht P (fun _ hp => (mem_filter.mp hp).2)) (Nat.cast_nonneg N)

theorem uniform_tail {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ,0 < K ∧ ∀ N : ℕ,((bad K N).card:ℝ) ≤ ε*N := by
  obtain ⟨K,hK,hbound⟩ := finite_tail_small (fun b : ℕ => (1:ℝ)/(b:ℝ)^2)
    (fun _ => by positivity) (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)) hε
  exact ⟨K,hK,fun N => by simpa only [mul_comm] using count_le K N hbound⟩

#print axioms uniform_tail
end Erdos1206.SquareDivisorTail
