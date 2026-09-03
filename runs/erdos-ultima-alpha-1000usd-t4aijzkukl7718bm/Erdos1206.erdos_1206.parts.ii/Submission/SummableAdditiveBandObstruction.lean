import Submission.SquarefreeSmallWeightCollision

/-! Nonempty fixed open bands of completely additive real scores with finite
reciprocal-prime absolute first moment cannot have Sidon cubes, even after
restriction to squarefree roots. Finite square energy alone is not assumed
sufficient for this argument. -/
namespace Erdos1206.SummableAdditiveBandObstruction
open Finset QuadraticSemiprimeDivisibility
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def primeAbsWeight (f : ℕ → ℝ) (d : ℕ) : ℝ :=
  if d.Prime then |f d| else 0

lemma score_prod (f : ℕ → ℝ)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → f (a*b)=f a+f b)
    (P : Finset ℕ) (hP : ∀ p∈P, 0 < p) : f (∏p∈P,p)=∑p∈P,f p := by
  have h1 : f 1=0 := by
    have hh := hmul 1 1 (by decide) (by decide)
    norm_num only [mul_one] at hh
    linarith
  induction P using Finset.induction_on with
  | empty => simp only [prod_empty,sum_empty,h1]
  | @insert p P hp ih =>
    rw [prod_insert hp,sum_insert hp,hmul p (∏q∈P,q) (hP p (mem_insert_self _ _))
      (prod_pos (fun q hq => hP q (mem_insert_of_mem hq))),ih]
    exact fun q hq => hP q (mem_insert_of_mem hq)

lemma abs_score_le (f : ℕ → ℝ)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → f (a*b)=f a+f b)
    {n : ℕ} (hn : Squarefree n) : |f n| ≤ divisorWeight (primeAbsWeight f) n := by
  have he : f n=∑p∈n.primeFactors,f p := by
    conv_lhs => rw [←Nat.prod_primeFactors_of_squarefree hn]
    exact score_prod f hmul _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  rw [he]
  calc
    _ ≤ ∑p∈n.primeFactors,|f p| := abs_sum_le_sum_abs _ _
    _ = ∑p∈n.primeFactors,primeAbsWeight f p := by
      apply sum_congr rfl
      intro p hp
      exact (if_pos (Nat.prime_of_mem_primeFactors hp)).symm
    _ ≤ divisorWeight (primeAbsWeight f) n := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact Nat.mem_divisors.mpr ⟨(Nat.mem_primeFactors.mp hp).2.1,hn.ne_zero⟩
      · intro p _ _
        dsimp only [primeAbsWeight]
        split_ifs
        · exact abs_nonneg _
        · exact le_rfl

/-- All four scores can be made arbitrarily small at a strict squarefree
collision, while avoiding any prescribed finite prime support. -/
theorem collision_small_scores (f : ℕ → ℝ)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → f (a*b)=f a+f b)
    (hs : Summable (fun p : ℕ => if p.Prime then |f p|/p else 0))
    (q : ℕ) (hq : 0 < q) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : Fin 4 → ℕ, (∀ i, 0 < n i ∧ Squarefree (n i) ∧ (n i).Coprime q ∧ |f (n i)|<ε) ∧
      n 0 < n 1 ∧ n 1 < n 2 ∧ n 2 < n 3 ∧
      (n 0)^3+(n 3)^3=(n 1)^3+(n 2)^3 := by
  have hw (p : ℕ) : 0 ≤ primeAbsWeight f p := by
    dsimp only [primeAbsWeight]
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  have hsupp (d : ℕ) (hd : ¬LowComplexity d) : primeAbsWeight f d=0 := by
    exact if_neg (fun h => hd (Or.inl h))
  have hcost : Summable (fun p : ℕ => primeAbsWeight f p/p) := by
    apply hs.congr
    intro p
    by_cases hp : p.Prime <;> simp only [primeAbsWeight,hp,if_true,if_false,zero_div]
  obtain ⟨n,hn,h01,h12,h23,he,hsmall⟩ := SquarefreeSmallWeightCollision.collision_small_total_coprime
    (primeAbsWeight f) hw hsupp hcost q hq hε
  refine ⟨n,fun i => ⟨(hn i).1,(hn i).2.1,(hn i).2.2,?_⟩,h01,h12,h23,he⟩
  calc
    |f (n i)| ≤ divisorWeight (primeAbsWeight f) (n i) := abs_score_le f hmul (hn i).2.1
    _ ≤ ∑j,divisorWeight (primeAbsWeight f) (n j) :=
      single_le_sum (fun j _ => divisorWeight_nonneg hw (n j)) (mem_univ i)
    _ < ε := hsmall

/-- No nonempty fixed open score band is cube-Sidon on the squarefree source.
The moment hypothesis is L1 in reciprocal-prime weight, not merely L2. -/
theorem nonempty_band_not_sidon (f : ℕ → ℝ)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → f (a*b)=f a+f b)
    (hs : Summable (fun p : ℕ => if p.Prime then |f p|/p else 0))
    (μ t : ℝ) (q : ℕ) (hqsf : Squarefree q) (hqband : |f q-μ|<t) :
    ¬IsSidon ((fun n : ℕ => n^3) '' {n : ℕ | Squarefree n ∧ |f n-μ|<t}) := by
  intro hsidon
  have hq : 0 < q := Nat.pos_of_ne_zero hqsf.ne_zero
  let ε := t-|f q-μ|
  have hε : 0 < ε := sub_pos.mpr hqband
  obtain ⟨n,hn,h01,h12,h23,he⟩ := collision_small_scores f hmul hs q hq hε
  have hmem (i : Fin 4) : q*n i∈{n : ℕ | Squarefree n ∧ |f n-μ|<t} := by
    refine ⟨(Nat.squarefree_mul (hn i).2.2.1.symm).mpr ⟨hqsf,(hn i).2.1⟩,?_⟩
    calc
      |f (q*n i)-μ| = |(f q-μ)+f (n i)| := by rw [hmul q (n i) hq (hn i).1]; congr 1; ring
      _ ≤ |f q-μ|+|f (n i)| := abs_add_le _ _
      _ < |f q-μ|+ε := by linarith [(hn i).2.2.2]
      _ = t := by dsimp only [ε]; ring
  have hid : (q*n 0)^3+(q*n 3)^3=(q*n 1)^3+(q*n 2)^3 := by
    simpa only [mul_pow,←mul_add] using congrArg (fun z : ℕ => q^3*z) he
  have hh := hsidon _ ⟨q*n 0,hmem 0,rfl⟩ _ ⟨q*n 1,hmem 1,rfl⟩
    _ ⟨q*n 3,hmem 3,rfl⟩ _ ⟨q*n 2,hmem 2,rfl⟩ hid
  rcases hh with hh | hh
  · have h := Nat.pow_left_injective (by decide : 3≠0) hh.1
    have h' := Nat.eq_of_mul_eq_mul_left hq h
    omega
  · have h := Nat.pow_left_injective (by decide : 3≠0) hh.1
    have h' := Nat.eq_of_mul_eq_mul_left hq h
    omega

#print axioms collision_small_scores
#print axioms nonempty_band_not_sidon
end Erdos1206.SummableAdditiveBandObstruction
