import Submission.SquarefreeSmallDivisorWeights
import Submission.SquarefreeSummablePrimeObstruction

/-! Strict squarefree cube collisions with arbitrarily small summable
prime/semiprime divisor weight, also coprime to any prescribed positive integer. -/
namespace Erdos1206.SquarefreeSmallWeightCollision
open Finset SquarefreeConicFamily QuadraticSemiprimeDivisibility
open scoped Classical
set_option maxHeartbeats 2000000

lemma collision_small_total (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p)
    (hsupp : ∀ d, ¬LowComplexity d → w d=0)
    (hs : Summable (fun d : ℕ => w d/d))
    {t : ℝ} (ht : 0 < t) :
    ∃ n : Fin 4 → ℕ, (∀ i, 0 < n i ∧ Squarefree (n i)) ∧
      n 0 < n 1 ∧ n 1 < n 2 ∧ n 2 < n 3 ∧
      (n 0)^3+(n 3)^3=(n 1)^3+(n 2)^3 ∧ (∑i,divisorWeight w (n i)) < t := by
  obtain ⟨x,hxpos,hxsf,hx⟩ := SquarefreeSmallDivisorWeights.exists_small_total a b c
    (by intro i; fin_cases i <;> norm_num [a])
    (by intro i; fin_cases i <;> norm_num [c])
    SquarefreeSummablePrimeObstruction.anisotropic_reversed
    (by intro i; fin_cases i <;> norm_num [a,b,c])
    SquarefreeSummablePrimeObstruction.local_units_nat w hw hsupp hs ht
  obtain ⟨h0,h01,h12,h23⟩ := SquarefreeSummablePrimeObstruction.ordered_of_first_pos x.1 x.2 hxpos
  refine ⟨fun i => F i x.1 x.2,?_,h01,h12,h23,identity x.1 x.2,hx⟩
  intro i
  refine ⟨?_,hxsf i⟩
  fin_cases i <;> dsimp <;> omega

/-- Finite prime exclusions can be imposed by a finite weight perturbation. -/
theorem collision_small_total_coprime (w : ℕ → ℝ) (hw : ∀ d, 0 ≤ w d)
    (hsupp : ∀ d, ¬LowComplexity d → w d=0)
    (hs : Summable (fun d : ℕ => w d/d)) (q : ℕ) (hq : 0 < q)
    {t : ℝ} (ht : 0 < t) :
    ∃ n : Fin 4 → ℕ, (∀ i, 0 < n i ∧ Squarefree (n i) ∧ (n i).Coprime q) ∧
      n 0 < n 1 ∧ n 1 < n 2 ∧ n 2 < n 3 ∧
      (n 0)^3+(n 3)^3=(n 1)^3+(n 2)^3 ∧ (∑i,divisorWeight w (n i)) < t := by
  let v (d : ℕ) : ℝ := w d+if d.Prime ∧ d∣q then t else 0
  have hv (d : ℕ) : 0 ≤ v d := by
    dsimp [v]
    split_ifs <;> linarith [hw d]
  have hwv (d : ℕ) : w d ≤ v d := by
    dsimp [v]
    split_ifs <;> linarith
  have hvsupp (d : ℕ) (hd : ¬LowComplexity d) : v d=0 := by
    have hdp : ¬d.Prime := fun h => hd (Or.inl h)
    simp only [v,hsupp d hd,hdp,false_and,if_false,add_zero]
  have hfinite : Summable (fun d : ℕ => (if d.Prime ∧ d∣q then t else 0)/(d:ℝ)) := by
    apply summable_of_ne_finset_zero (s := q.divisors)
    intro d hd
    have hn : ¬(d.Prime ∧ d∣q) := fun h => hd (Nat.mem_divisors.mpr ⟨h.2,hq.ne'⟩)
    simp only [if_neg hn,zero_div]
  have hvs : Summable (fun d : ℕ => v d/d) := by
    simpa only [v,add_div] using hs.add hfinite
  obtain ⟨n,hn,h01,h12,h23,he,hsmall⟩ := collision_small_total v hv hvsupp hvs ht
  have hscore (i : Fin 4) : divisorWeight v (n i)<t := by
    apply lt_of_le_of_lt _ hsmall
    exact single_le_sum (fun j _ => divisorWeight_nonneg hv (n j)) (mem_univ i)
  have hcop (i : Fin 4) : (n i).Coprime q := by
    by_contra hh
    obtain ⟨p,hp,hpn,hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hh
    have hweight : t ≤ v p := by
      simp only [v,hp,hpq,and_self,if_true]
      linarith [hw p]
    have hmem : p∈(n i).divisors := Nat.mem_divisors.mpr ⟨hpn,(hn i).1.ne'⟩
    have hsum : v p ≤ divisorWeight v (n i) := single_le_sum (fun d _ => hv d) hmem
    exact (not_le_of_gt (hscore i)) (hweight.trans hsum)
  refine ⟨n,fun i => ⟨(hn i).1,(hn i).2,hcop i⟩,h01,h12,h23,he,?_⟩
  apply lt_of_le_of_lt _ hsmall
  exact sum_le_sum (fun i _ => sum_le_sum (fun d _ => hwv d))

/-- Even on squarefree roots coprime to q, no such positive low-weight band
has Sidon cubes. No assertion is made about arbitrary composite weights. -/
theorem low_squarefree_divisorWeight_not_sidon (w : ℕ → ℝ) (hw : ∀ d, 0 ≤ w d)
    (hsupp : ∀ d, ¬LowComplexity d → w d=0)
    (hs : Summable (fun d : ℕ => w d/d)) (q : ℕ) (hq : 0 < q)
    {t : ℝ} (ht : 0 < t) :
    ¬IsSidon ((fun n : ℕ => n^3) ''
      {n : ℕ | Squarefree n ∧ n.Coprime q ∧ divisorWeight w n<t}) := by
  intro hsidon
  obtain ⟨n,hn,h01,h12,h23,he,hsmall⟩ := collision_small_total_coprime w hw hsupp hs q hq ht
  have hmem (i : Fin 4) : n i∈{n : ℕ | Squarefree n ∧ n.Coprime q ∧ divisorWeight w n<t} := by
    refine ⟨(hn i).2.1,(hn i).2.2,lt_of_le_of_lt ?_ hsmall⟩
    exact single_le_sum (fun j _ => divisorWeight_nonneg hw (n j)) (mem_univ i)
  have hh := hsidon _ ⟨n 0,hmem 0,rfl⟩ _ ⟨n 1,hmem 1,rfl⟩
    _ ⟨n 3,hmem 3,rfl⟩ _ ⟨n 2,hmem 2,rfl⟩ he
  rcases hh with hh | hh
  · have heq := Nat.pow_left_injective (by decide : 3≠0) hh.1
    omega
  · have heq := Nat.pow_left_injective (by decide : 3≠0) hh.1
    omega

#print axioms collision_small_total_coprime
#print axioms low_squarefree_divisorWeight_not_sidon
end Erdos1206.SquarefreeSmallWeightCollision
