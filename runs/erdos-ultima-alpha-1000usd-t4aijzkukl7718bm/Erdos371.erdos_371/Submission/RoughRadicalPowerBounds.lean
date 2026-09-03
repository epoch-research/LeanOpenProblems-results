import Submission.RoughPartPowerBounds
import Submission.RoughRadicalComplement

/-! On density one the rough radical of n(n+1) exceeds every fixed power
N^(2-2/(q+1)). This supplies almost-quadratic size thresholds. -/
namespace Erdos371
open Finset Filter
open scoped Topology

lemma large_squarefree_rough_pair_radical (B q M n : ℕ) (hM : 0 < M) (hn : 0 < n)
    (ha : M^q < (roughPrimePart B n)^(q+1))
    (hb : M^q < (roughPrimePart B (n+1))^(q+1))
    (hsa : ∀ p, p.Prime → B < p → ¬p^2 ∣ n)
    (hsb : ∀ p, p.Prime → B < p → ¬p^2 ∣ n+1) :
    M^(2*q) < (roughRadical B (n*(n+1)))^(q+1) := by
  have hapos := roughPrimePart_pos B n
  have hbpos := roughPrimePart_pos B (n+1)
  have hMp : 1 ≤ M^q := Nat.pow_pos hM
  have ha1 : 1 < roughPrimePart B n := by
    by_contra h
    have he : roughPrimePart B n=1 := by omega
    rw [he,one_pow] at ha
    omega
  have hb1 : 1 < roughPrimePart B (n+1) := by
    by_contra h
    have he : roughPrimePart B (n+1)=1 := by omega
    rw [he,one_pow] at hb
    omega
  have hada := roughPrimePart_dvd B n hn.ne'
  have hbdb := roughPrimePart_dvd B (n+1) (by omega)
  have had : roughPrimePart B n ∣ roughRadical B (n*(n+1)) :=
    squarefree_rough_dvd_radical B _ _ (by positivity) (hada.trans (dvd_mul_right _ _))
      (roughPrimePart_squarefree B n hn.ne' hsa) (roughPrimePart_minFac B n ha1)
  have hbd : roughPrimePart B (n+1) ∣ roughRadical B (n*(n+1)) :=
    squarefree_rough_dvd_radical B _ _ (by positivity) (hbdb.trans (dvd_mul_left _ _))
      (roughPrimePart_squarefree B (n+1) (by omega) hsb) (roughPrimePart_minFac B (n+1) hb1)
  have hpd := (divisor_pair_coprime n _ _ hada hbdb).mul_dvd_of_dvd_of_dvd had hbd
  have hle := Nat.le_of_dvd (roughRadical_pos B _) hpd
  have hp : M^(2*q) < (roughPrimePart B n*roughPrimePart B (n+1))^(q+1) := by
    rw [mul_pow,show 2*q=q*2 by omega,pow_mul,pow_two]
    nlinarith
  exact hp.trans_le (Nat.pow_le_pow_left hle _)

lemma roughRadical_small_power_count_bound (B D q N : ℕ)
    (hD : D^(q+1) ≤ (N+1)^(2*q)) :
    ((range N).filter (fun n => roughRadical B ((n+1)*(n+2)) ≤ D)).card ≤
      2*(smallRoughPartPowerCount B q (N+1)+largePrimeSquareCount B (N+1)) := by
  classical
  let T : ℕ → Prop := fun m => (roughPrimePart B m)^(q+1) ≤ (N+1)^q ∨
    ∃ p, p.Prime ∧ B < p ∧ p^2 ∣ m
  have hT (n : ℕ) : roughRadical B ((n+1)*(n+2)) ≤ D → T (n+1) ∨ T (n+2) := by
    intro hr
    by_contra ht
    simp only [T,not_or] at ht
    have hpa : ∀ p, p.Prime → B < p → ¬p^2 ∣ n+1 := by
      intro p hp hpB hpd
      exact ht.1.2 ⟨p,hp,hpB,hpd⟩
    have hpb : ∀ p, p.Prime → B < p → ¬p^2 ∣ n+2 := by
      intro p hp hpB hpd
      exact ht.2.2 ⟨p,hp,hpB,hpd⟩
    have hg := large_squarefree_rough_pair_radical B q (N+1) (n+1) (by omega) (by omega)
      (by omega) (by simpa only [Nat.add_assoc,Nat.reduceAdd] using Nat.lt_of_not_ge ht.2.1) hpa
      (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hpb)
    simp only [Nat.add_assoc,Nat.reduceAdd] at hg
    exact (not_lt_of_ge ((Nat.pow_le_pow_left hr _).trans hD)) hg
  have hsub : (range N).filter (fun n => roughRadical B ((n+1)*(n+2)) ≤ D) ⊆
      (range N).filter (fun n => T (n+1)) ∪ (range N).filter (fun n => T (n+2)) := by
    intro n hn
    obtain ⟨hn,hr⟩ := mem_filter.mp hn
    rcases hT n hr with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨hn,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hn,h⟩)
  have hc : ((range (N+1)).filter (fun n => T (n+1))).card ≤
      smallRoughPartPowerCount B q (N+1)+largePrimeSquareCount B (N+1) := by
    dsimp only [T]
    rw [filter_or]
    exact card_union_le _ _
  have h1 : ((range N).filter (fun n => T (n+1))).card ≤
      smallRoughPartPowerCount B q (N+1)+largePrimeSquareCount B (N+1) :=
    (card_le_card (filter_subset_filter _ (range_mono (by omega)))).trans hc
  have h2 := (shifted_predicate_card_le T N).trans hc
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  omega

/-- The exponent q is fixed before N tends to infinity. There is no
unjustified moving-exponent or near-linear endpoint claim here. -/
theorem roughRadical_small_power_proportion_zero (B D : ℕ → ℕ) (q : ℕ)
    (hBt : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hD : ∀ᶠ N in atTop, (D N)^(q+1) ≤ (N+1)^(2*q)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      if roughRadical (B N) ((n+1)*(n+2)) ≤ D N then (1 : ℝ) else 0)/N) atTop (𝓝 0) := by
  have ht := ((smallRoughPartPowerCount_succ_tendsto_zero B q hB).add
    (largePrimeSquareCount_succ_tendsto_zero B hBt)).const_mul (2 : ℝ)
  simp only [add_zero,mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg
    (sum_nonneg fun n _ => by split_ifs <;> norm_num) (Nat.cast_nonneg N)) _ ht
  filter_upwards [hD] with N hd
  rw [sum_boole,← add_div,← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast roughRadical_small_power_count_bound (B N) (D N) q N hd

#print axioms roughRadical_small_power_proportion_zero
end Erdos371
