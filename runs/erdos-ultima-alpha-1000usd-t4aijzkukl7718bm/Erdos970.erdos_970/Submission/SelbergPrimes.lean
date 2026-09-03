import Submission.SelbergInterval

/-! Selberg upper bounds for intervals sieved by distinct primes. -/
namespace Erdos970.FiniteSelberg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem prime_hits_intersection_error (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (r : ℕ → ℕ) (m : ℕ) (T : Finset ι) :
    |(∑ j ∈ Finset.range m, hitMonomial T (fun i => decide (j ≡ r (p i) [MOD p i]))) -
      (m : ℝ) * ∏ i ∈ T, (1 / (p i : ℝ))| ≤ 1 := by
  classical
  have himage : ∀ a ∈ T.image p, a.Prime := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact hp i
  have hh := Erdos970.BrunCriterion.intersection_count_error (T.image p) himage r m
  have hprod : (∏ a ∈ T.image p, (a : ℝ)) = ∏ i ∈ T, (p i : ℝ) :=
    Finset.prod_image hpinj.injOn
  rw [hprod] at hh
  have hcount : (∑ j ∈ Finset.range m,
      hitMonomial T (fun i => decide (j ≡ r (p i) [MOD p i]))) =
      (((Finset.range m).filter (fun j => ∀ a ∈ T.image p, j ≡ r a [MOD a])).card : ℝ) := by
    simp [hitMonomial_eq, ← Finset.sum_filter]
  rw [hcount]
  simpa only [Finset.prod_div_distrib, Finset.prod_const_one, mul_one_div] using hh

theorem prime_survivors_le (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (D : Finset (Finset ι)) (hDn : D.Nonempty)
    (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D) (r : ℕ → ℕ) (m : ℕ) :
    (((Finset.range m).filter (fun j => ∀ i, ¬j ≡ r (p i) [MOD p i])).card : ℝ) ≤
      (m : ℝ) / normalizer (fun i => 1 / (p i : ℝ)) D + (D.card : ℝ)^2 := by
  have hq (i : ι) : 0 < 1 / (p i : ℝ) ∧ 1 / (p i : ℝ) < 1 := by
    have hpi : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    constructor
    · positivity
    · exact (div_lt_iff₀ (by linarith : (0 : ℝ) < p i)).mpr (by simpa using hpi)
  simpa using survivors_le (fun i => 1 / (p i : ℝ)) hq D hDn hD m
    (fun j i => decide (j ≡ r (p i) [MOD p i]))
    (prime_hits_intersection_error p hp hpinj r m)

/-- The divisor support consists of prime subsets whose product is at most the cutoff. -/
noncomputable def divisorSupport (p : ι → ℕ) (R : ℕ) : Finset (Finset ι) :=
  Finset.univ.filter (fun T => ∏ i ∈ T, p i ≤ R)

theorem mem_divisorSupport (p : ι → ℕ) (R : ℕ) (T : Finset ι) :
    T ∈ divisorSupport p R ↔ ∏ i ∈ T, p i ≤ R := by
  simp [divisorSupport]

theorem divisorSupport_downward (p : ι → ℕ) (hp : ∀ i, 1 ≤ p i) (R : ℕ) :
    ∀ A ∈ divisorSupport p R, ∀ B ⊆ A, B ∈ divisorSupport p R := by
  intro A hA B hBA
  rw [mem_divisorSupport] at hA ⊢
  exact (Finset.prod_le_prod_of_subset_of_one_le' hBA (fun i hi hBi => hp i)).trans hA

theorem divisorSupport_nonempty (p : ι → ℕ) (R : ℕ) (hR : 0 < R) :
    (divisorSupport p R).Nonempty := by
  refine ⟨∅, ?_⟩
  simp only [mem_divisorSupport, Finset.prod_empty]
  omega

theorem prime_subset_product_injective (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) :
    Function.Injective (fun T : Finset ι => ∏ i ∈ T, p i) := by
  intro A B hAB
  dsimp only at hAB
  have hA : (∏ i ∈ A, p i).primeFactors = A.image p := by
    rw [← Finset.prod_image (f := fun n : ℕ => n) hpinj.injOn]
    apply Nat.primeFactors_prod
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact hp i
  have hB : (∏ i ∈ B, p i).primeFactors = B.image p := by
    rw [← Finset.prod_image (f := fun n : ℕ => n) hpinj.injOn]
    apply Nat.primeFactors_prod
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact hp i
  have hi : A.image p = B.image p := by rw [← hA, ← hB, hAB]
  ext i
  constructor
  · intro hiA
    have := hi ▸ Finset.mem_image.mpr ⟨i, hiA, rfl⟩
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp this
    exact hpinj hji ▸ hj
  · intro hiB
    have := hi.symm ▸ Finset.mem_image.mpr ⟨i, hiB, rfl⟩
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp this
    exact hpinj hji ▸ hj

theorem divisorSupport_card_le (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (R : ℕ) :
    (divisorSupport p R).card ≤ R := by
  have hh := Finset.card_le_card_of_injOn (s := divisorSupport p R)
    (t := Finset.Icc 1 R) (fun T => ∏ i ∈ T, p i) (fun T hT => ?_)
    (prime_subset_product_injective p hp hpinj).injOn
  · simpa using hh
  · change (∏ i ∈ T, p i) ∈ Finset.Icc 1 R
    apply Finset.mem_Icc.mpr
    exact ⟨Finset.prod_pos (fun i hi => (hp i).pos), (mem_divisorSupport p R T).mp hT⟩

/-- A classical Selberg upper bound with cutoff-squared error. -/
theorem prime_survivors_le_cutoff (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (r : ℕ → ℕ) (m R : ℕ) (hR : 0 < R) :
    (((Finset.range m).filter (fun j => ∀ i, ¬j ≡ r (p i) [MOD p i])).card : ℝ) ≤
      (m : ℝ) / normalizer (fun i => 1 / (p i : ℝ)) (divisorSupport p R) + (R : ℝ)^2 := by
  apply (prime_survivors_le p hp hpinj (divisorSupport p R)
    (divisorSupport_nonempty p R hR)
    (divisorSupport_downward p (fun i => (hp i).one_lt.le) R) r m).trans
  gcongr
  exact_mod_cast divisorSupport_card_le p hp hpinj R

#print axioms prime_survivors_le_cutoff

end Erdos970.FiniteSelberg
