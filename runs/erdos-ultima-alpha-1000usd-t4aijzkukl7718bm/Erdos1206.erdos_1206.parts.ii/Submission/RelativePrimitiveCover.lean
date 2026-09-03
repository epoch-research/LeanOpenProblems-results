import Submission.FiniteRatioSource
import Submission.CountableBandDensity
import Submission.StrictCubeCollision

/-! A source-relative sufficient criterion using normalized primitive maxima.
An arbitrary source-relative divisor cover would NOT suffice. -/
namespace Erdos1206.RelativePrimitiveCover
open Finset Filter
open scoped Topology Classical

lemma divisible_second_moment (d N : ℕ) :
    (∑ n ∈ Icc 1 N, (if d ∣ n then (2:ℝ) else 0)^2) ≤ (N:ℝ)*(4/(d:ℝ)) := by
  have hc : ((Icc 1 N).filter (fun n => d ∣ n)).card=N/d := by
    have he : (Icc 1 N).filter (fun n => d ∣ n)=
        (range (N+1)).filter (fun n => n ≠ 0 ∧ d ∣ n) := by
      ext n
      simp only [mem_filter,mem_Icc,mem_range]
      omega
    rw [he]
    exact Nat.card_multiples' N d
  have he : (∑ n ∈ Icc 1 N, (if d ∣ n then (2:ℝ) else 0)^2)=
      4*(((Icc 1 N).filter (fun n => d ∣ n)).card:ℝ) := by
    calc
      _ = ∑ n ∈ (Icc 1 N).filter (fun n => d ∣ n), (4:ℝ) := by
        rw [sum_filter]
        apply sum_congr rfl
        intro n _
        split_ifs <;> norm_num
      _ = _ := by simp [mul_comm]
  rw [he,hc]
  have hh := mul_le_mul_of_nonneg_left (show ((N/d:ℕ):ℝ) ≤ (N:ℝ)/d from Nat.cast_div_le) (by norm_num : (0:ℝ) ≤ 4)
  calc
    _ ≤ 4*((N:ℝ)/d) := hh
    _ = _ := by ring

/-- A reciprocal-small tail may be deleted from an arbitrary positive source.
Only the tail is removed, not the potentially fatal finite set of divisors. -/
theorem exists_avoiding_tail {S B : Set ℕ} (hS : 0 < S.lowerDensity)
    (hpos : ∀ n ∈ S, 0 < n)
    (hs : Summable (fun d : ℕ => if d ∈ B then (1:ℝ)/d else 0)) :
    ∃ (M : ℕ) (A : Set ℕ), 0 < M ∧ A ⊆ S ∧ 0 < A.lowerDensity ∧
      ∀ n ∈ A, ∀ d ∈ B, M < d → ¬ d ∣ n := by
  obtain ⟨δ,hδ,C,hpre⟩ := prefix_bound_of_positive_lowerDensity hS
  let g : ℕ → ℝ := fun d => if d ∈ B then 1/(d:ℝ) else 0
  have ht := (tendsto_sum_nat_add g).const_mul (4:ℝ)
  have hev : ∀ᶠ M : ℕ in atTop, 4*(∑' j, g (j+M)) < δ :=
    ht.eventually (by simpa only [mul_zero] using (gt_mem_nhds hδ))
  obtain ⟨M,hM,hM0⟩ := (hev.and (eventually_gt_atTop 0)).exists
  let f : ℕ → ℕ → ℝ := fun j n => if j+M ∈ B ∧ j+M ∣ n then 2 else 0
  let c : ℕ → ℝ := fun j => 4*g (j+M)
  have hc (j : ℕ) : 0 ≤ c j := by dsimp only [c,g]; split_ifs <;> positivity
  have hcs : Summable c := ((summable_nat_add_iff M).mpr hs).mul_left 4
  have hsum : ∑' j, c j < δ := by simpa only [c,tsum_mul_left] using hM
  have hm (j N : ℕ) : (∑ n ∈ Icc 1 N, (f j n)^2) ≤ (N:ℝ)*c j := by
    by_cases hd : j+M ∈ B
    · simpa only [f,c,g,hd,true_and,if_true,mul_one_div] using divisible_second_moment (j+M) N
    · simp only [f,c,g,hd,false_and,if_false,zero_pow (by decide : 2 ≠ 0),sum_const_zero,mul_zero,le_refl]
  let A : Set ℕ := {n | n ∈ S ∧ ∀ j, |f j n| ≤ 1}
  have hAd : 0 < A.lowerDensity := CountableBandDensity.lowerDensity_pos_of_prefix
    S f c hpos hpre hc hcs hm hsum
  refine ⟨M,A,hM0,fun n hn => hn.1,hAd,?_⟩
  intro n hn d hd hMd hdn
  have he : d-M+M=d := Nat.sub_add_cancel hMd.le
  have hh := hn.2 (d-M)
  simp only [f,he,hd,hdn,and_self,if_true,abs_of_pos (by norm_num : (0:ℝ) < 2)] at hh
  norm_num at hh

/-- The cover divisor also bounds a rational relation between the minimum
and maximum roots. This extra condition is what makes its finite head safe. -/
def RatioCompatibleCover (S B : Set ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    0 < a → a < b → b < c → c < d → a^3+d^3=b^3+c^3 →
    ∃ q ∈ B, q ∣ d ∧ ∃ r ∈ Set.Icc 1 q, ∃ s ∈ Set.Icc 1 q, r*a=s*d

/-- A global source-relative cover with the primitive-ratio compatibility
would settle the conjecture. The global cover is an explicit hypothesis. -/
theorem ratio_compatible_cover_suffices {S B : Set ℕ}
    (hS : 0 < S.lowerDensity) (hpos : ∀ n ∈ S, 0 < n)
    (hs : Summable (fun d : ℕ => if d ∈ B then (1:ℝ)/d else 0))
    (hcover : RatioCompatibleCover S B) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧ IsSidon ((fun n : ℕ => n^3) '' A) := by
  obtain ⟨M,T,hM,hTS,hTd,havoid⟩ := exists_avoiding_tail hS hpos hs
  obtain ⟨A,hAT,hAd,hsep⟩ := FiniteRatioSource.exists_positive_separated hTd hM
  refine ⟨A,?_,hAd,?_⟩
  · by_contra hh
    have hz : A.lowerDensity=0 := (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hh)).liminf_eq
    linarith
  · apply (cubeSidon_iff_no_strict_positive A).mpr
    intro a ha b hb c hc d hd ha0 hab hbc hcd he
    obtain ⟨q,hq,hqd,r,hr,s,hs,hrel⟩ := hcover a (hTS (hAT ha)) b (hTS (hAT hb))
      c (hTS (hAT hc)) d (hTS (hAT hd)) ha0 hab hbc hcd he
    have hqM : q ≤ M := by
      by_contra hh
      exact havoid d (hAT hd) q hq (lt_of_not_ge hh) hqd
    have heq := hsep a ha d hd r ⟨hr.1,hr.2.trans hqM⟩ s ⟨hs.1,hs.2.trans hqM⟩ hrel
    omega

#print axioms divisible_second_moment
#print axioms exists_avoiding_tail
#print axioms ratio_compatible_cover_suffices
end Erdos1206.RelativePrimitiveCover
