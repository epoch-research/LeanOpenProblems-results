import Submission.SmallQuadraticPrimeScores
import Submission.SquarefreeSummablePrimeObstruction
import Submission.WeightedDivisorCover

/-! Summable nonnegative prime-supported weights cannot fractionally cover
all cubic collisions. This does not exclude composite-supported divisor weights. -/
namespace Erdos1206.PrimeWeightedCoverObstruction
open Finset SquarefreeConicFamily QuadraticPrimeMoments
open scoped Classical
set_option maxHeartbeats 2000000

lemma collision_small_total (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p)
    (hs : Summable (fun p : ℕ => if p.Prime then w p/p else 0))
    {t : ℝ} (ht : 0 < t) :
    ∃ n : Fin 4 → ℕ, (∀ i, 0 < n i) ∧
      n 0 < n 1 ∧ n 1 < n 2 ∧ n 2 < n 3 ∧
      (n 0)^3+(n 3)^3=(n 1)^3+(n 2)^3 ∧ (∑i,primeScore w (n i)) < t := by
  obtain ⟨x,hxpos,hx⟩ := SmallQuadraticPrimeScores.exists_small_total a b c
    (by intro i; fin_cases i <;> norm_num [c])
    SquarefreeSummablePrimeObstruction.anisotropic_reversed
    SquarefreeSummablePrimeObstruction.local_units_nat w hw hs ht
  obtain ⟨h0,h01,h12,h23⟩ := SquarefreeSummablePrimeObstruction.ordered_of_first_pos x.1 x.2 hxpos
  refine ⟨fun i => F i x.1 x.2,?_,h01,h12,h23,identity x.1 x.2,hx⟩
  intro i
  fin_cases i <;> dsimp <;> omega

lemma divisorWeight_eq_primeScore (w : ℕ → ℝ)
    (hsupp : ∀ d : ℕ, ¬d.Prime → w d=0) (n : ℕ) :
    divisorWeight w n=primeScore w n := by
  have he : n.divisors.filter Nat.Prime=n.primeFactors := by
    ext p
    simp only [mem_filter,Nat.mem_divisors,Nat.mem_primeFactors]
    tauto
  calc
    divisorWeight w n = ∑p∈n.divisors,if p.Prime then w p else 0 := by
      apply sum_congr rfl
      intro p hp
      by_cases hprime : p.Prime
      · simp [hprime]
      · simp [hprime,hsupp p hprime]
    _ = ∑p∈n.divisors.filter Nat.Prime,w p := (sum_filter _ _).symm
    _ = primeScore w n := by rw [he]; rfl

/-- Unlike whole-root mass divergence, this excludes even arbitrarily reused
fractional prime weights. Composite-divisor weights remain outside the result. -/
theorem no_summable_prime_weight_cover (w : ℕ → ℝ) (hw : ∀ d, 0 ≤ w d)
    (hsupp : ∀ d : ℕ, ¬d.Prime → w d=0)
    (hs : Summable (fun d : ℕ => w d/d)) :
    ¬IsWeightedCubeDivisorCover w := by
  intro hcover
  have hsp : Summable (fun p : ℕ => if p.Prime then w p/p else 0) := by
    apply hs.congr
    intro p
    by_cases hp : p.Prime <;> simp [hp,hsupp p]
  obtain ⟨n,hn,h01,h12,h23,he,hsmall⟩ := collision_small_total w hw hsp (by norm_num : (0:ℝ)<1)
  have hh := hcover (n 0) (n 3) (n 1) (n 2) (hn 0) (hn 3) (hn 1) (hn 2)
    he h01.ne (h01.trans h12).ne
  simp only [divisorWeight_eq_primeScore w hsupp] at hh
  simp only [Fin.sum_univ_succ] at hsmall
  change primeScore w (n 0)+(primeScore w (n 1)+(primeScore w (n 2)+(primeScore w (n 3)+0))) < 1 at hsmall
  linarith

/-- No fixed positive low-score band of a summable nonnegative prime score
has Sidon cubes. The score counts distinct prime factors. -/
theorem low_primeScore_not_sidon (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p)
    (hs : Summable (fun p : ℕ => if p.Prime then w p/p else 0))
    {t : ℝ} (ht : 0 < t) :
    ¬IsSidon ((fun n : ℕ => n^3) '' {n : ℕ | 0 < n ∧ primeScore w n < t}) := by
  intro hsidon
  obtain ⟨n,hn,h01,h12,h23,he,hsmall⟩ := collision_small_total w hw hs ht
  have hmem (i : Fin 4) : n i∈{n : ℕ | 0 < n ∧ primeScore w n < t} := by
    refine ⟨hn i,lt_of_le_of_lt ?_ hsmall⟩
    apply single_le_sum (f := fun j => primeScore w (n j)) _ (mem_univ i)
    intro j _
    exact sum_nonneg (fun p _ => hw p)
  have hh := hsidon _ ⟨n 0,hmem 0,rfl⟩ _ ⟨n 1,hmem 1,rfl⟩
    _ ⟨n 3,hmem 3,rfl⟩ _ ⟨n 2,hmem 2,rfl⟩ he
  rcases hh with hh | hh
  · have heq := Nat.pow_left_injective (by decide : 3≠0) hh.1
    omega
  · have heq := Nat.pow_left_injective (by decide : 3≠0) hh.1
    omega

#print axioms collision_small_total
#print axioms no_summable_prime_weight_cover
#print axioms low_primeScore_not_sidon
end Erdos1206.PrimeWeightedCoverObstruction
