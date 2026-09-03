import Submission.RecursivePositiveScaling

/-! Density-sensitive prefix comparison for positive plain certificates.
This sharpens within-model source domination, not the original conjecture. -/
namespace Erdos970.RecursiveSieve
open Finset

lemma prefixDensity_antitone (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    Antitone (prefixDensity q) := by
  apply antitone_nat_of_succ_le
  intro n
  have he : prefixDensity q (n+1) = prefixDensity q n*(1-q n) := prod_range_succ _ n
  rw [he]
  have hm := mul_le_mul_of_nonneg_left (show 1-q n ≤ 1 by linarith [(hq n).1])
    (prefixDensity_nonneg q n (fun i _ => hq i))
  simpa only [mul_one] using hm

lemma prefixDensity_sum (q : ℕ → ℝ) (x : ℝ) (n : ℕ) :
    (∑ i ∈ range n, x*q i*prefixDensity q i) = x*(1-prefixDensity q n) := by
  rw [prefixDensity_first_hit q n,sub_sub_cancel,
    Fin.sum_univ_eq_sum_range (fun i => q i*prefixDensity q i) n,mul_sum]
  exact sum_congr rfl (fun i hi => mul_assoc _ _ _)

/-- Positivity must pay every upper child's independent density AND unit cost. -/
theorem positive_linearEnvelope_density_mass_gt (q : ℕ → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (k : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hpos : 0 < (linearEnvelope q k x).1) :
    (k : ℝ)+1 < x*prefixDensity q k := by
  have hu (i : Fin k) : x*q i.val*prefixDensity q i.val+1 ≤
      (linearEnvelope q i.val (x*q i.val)).2 :=
    (linearEnvelope_density_bounds q i.val (fun j _ => hq j) (x*q i.val)
      (mul_nonneg hx (hq i.val).1)).2
  have hs := sum_le_sum (s := (univ : Finset (Fin k))) (fun i _ => hu i)
  rw [sum_add_distrib, Fin.sum_univ_eq_sum_range
    (fun i => x*q i*prefixDensity q i) k, prefixDensity_sum] at hs
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hs
  rw [linearEnvelope_lower_eq_max q k (fun i _ => hq i) x hx] at hpos
  have hr : 0 < x-1-∑ i : Fin k, (linearEnvelope q i.val (x*q i.val)).2 := by
    by_contra hh
    rw [max_eq_left (le_of_not_gt hh)] at hpos
    exact lt_irrefl _ hpos
  nlinarith only [hs,hr]

/-- The prefix gap includes all intervening independent mass, not just units. -/
theorem linearEnvelope_positive_density_prefix_gap (q : ℕ → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (i j : ℕ) (hij : i ≤ j)
    (x : ℝ) (hx : 0 ≤ x) (hpos : 0 < (linearEnvelope q j x).1) :
    ((j : ℝ)-(i : ℝ))+x*(prefixDensity q i-prefixDensity q j)+
      (linearEnvelope q j x).1 ≤ (linearEnvelope q i x).1 := by
  let U (n : ℕ) := (linearEnvelope q n (x*q n)).2
  let V (n : ℕ) := x*q n*prefixDensity q n+1
  have hU (n : ℕ) (hn : n < j) : V n ≤ U n :=
    (linearEnvelope_density_bounds q n (fun t _ => hq t) (x*q n)
      (mul_nonneg hx (hq n).1)).2
  have hVs (n : ℕ) : (∑ t ∈ range n, V t) = x*(1-prefixDensity q n)+(n : ℝ) := by
    dsimp only [V]
    rw [sum_add_distrib,prefixDensity_sum]
    simp
  have hs := sum_le_sum (s := Ico i j) (fun n hn => hU n (mem_Ico.mp hn).2)
  have heU := sum_range_add_sum_Ico U hij
  have heV := sum_range_add_sum_Ico V hij
  rw [hVs i,hVs j] at heV
  have hje : (linearEnvelope q j x).1 = max 0 (x-1-∑ n ∈ range j, U n) := by
    rw [linearEnvelope_lower_eq_max q j (fun t _ => hq t) x hx,
      Fin.sum_univ_eq_sum_range (fun n => (linearEnvelope q n (x*q n)).2) j]
  have hr : 0 < x-1-∑ n ∈ range j, U n := by
    rw [hje] at hpos
    by_contra hh
    rw [max_eq_left (le_of_not_gt hh)] at hpos
    exact lt_irrefl _ hpos
  rw [max_eq_right hr.le] at hje
  have hil : x-1-∑ n ∈ range i, U n ≤ (linearEnvelope q i x).1 := by
    rw [linearEnvelope_lower_eq_max q i (fun n _ => hq n) x hx,
      Fin.sum_univ_eq_sum_range (fun n => (linearEnvelope q n (x*q n)).2) i]
    exact le_max_right _ _
  nlinarith only [hs,heU,heV,hje,hil]

/-- Positive later certificates control earlier slopes after density scaling. -/
theorem positive_prefix_density_ratio (q : ℕ → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (i j : ℕ) (hij : i ≤ j)
    (g : ℝ) (hg : 0 ≤ g) (hpos : 0 < (linearEnvelope q j g).1) :
    ((j : ℝ)+1)*prefixDensity q i ≤
      prefixDensity q j*((linearEnvelope q i g).1+(i : ℝ)+1) := by
  have hm := positive_linearEnvelope_density_mass_gt q hq j g hg hpos
  have hgap := linearEnvelope_positive_density_prefix_gap q hq i j hij g hg hpos
  have hdn := prefixDensity_nonneg q j (fun n _ => hq n)
  have hdi := prefixDensity_antitone q hq hij
  have hs := mul_le_mul_of_nonneg_left hgap hdn
  have hr := mul_le_mul_of_nonneg_right hm.le (sub_nonneg.mpr hdi)
  have hn := mul_nonneg hdn hpos.le
  nlinarith only [hs,hr,hn]

/-- The exact local positive-branch slope is the relevant source gain cap. -/
theorem affineSource_le_of_local_positive (q : ℕ → ℝ) (i : ℕ)
    (hq : ∀ n < i, 0 ≤ q n ∧ q n ≤ 1) (g : ℝ) (hg : 0 < g)
    (hpos : 0 < (linearEnvelope q i g).1) (t : ℝ) (ht : 0 ≤ t)
    (htL : t ≤ (linearEnvelope q i g).1+(i : ℝ)+1) (x : ℝ) :
    max 0 (t/g*(x-1)-t) ≤ (linearEnvelope q i x).1 := by
  apply max_le (linearEnvelope_lower_nonneg q i x)
  by_cases hxg : x ≤ g
  · have hm := mul_le_mul_of_nonneg_left (show x-1 ≤ g by linarith) (div_nonneg ht hg.le)
    rw [div_mul_cancel₀ _ hg.ne'] at hm
    exact (by linarith : t/g*(x-1)-t ≤ 0).trans (linearEnvelope_lower_nonneg q i x)
  · have hc : 1 ≤ x/g := (one_le_div hg).mpr (le_of_not_ge hxg)
    have hs := linearEnvelope_positive_scale q i hq g (x/g) hg.le hc hpos
    rw [div_mul_cancel₀ _ hg.ne'] at hs
    have hm := mul_le_mul_of_nonneg_right htL (show 0 ≤ x/g-1 by linarith)
    have hn : 0 ≤ t/g := div_nonneg ht hg.le
    have he : t/g*(x-1)-t = t*(x/g-1)-t/g := by ring
    rw [he]
    nlinarith only [hs,hm,hn,hpos]

#print axioms positive_linearEnvelope_density_mass_gt
#print axioms linearEnvelope_positive_density_prefix_gap
#print axioms positive_prefix_density_ratio
#print axioms affineSource_le_of_local_positive
end Erdos970.RecursiveSieve
