import Submission.PrimeLogMoments

/-! An unconditional uniform polynomial bound from the soft Selberg profile.
The exponent here is six, not the conjectured exponent two. -/
namespace Erdos970.FiniteSelberg
open Finset Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma prime_marginals (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (i : ι) :
    0 < 1 / (p i : ℝ) ∧ 1 / (p i : ℝ) < 1 := by
  have hh : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
  constructor
  · positivity
  · exact (div_lt_iff₀ (by linarith : (0 : ℝ) < p i)).mpr (by linarith)

lemma prime_soft_support (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (L : ℝ) (Q : Finset ι) (hQ : Q ∉ divisorSupport p ⌊exp L⌋₊) :
    softProfile (fun i => log (p i)) L Q = 0 := by
  have hprod : (0 : ℝ) < ∏ i ∈ Q, (p i : ℝ) := prod_pos (fun i _ => by exact_mod_cast (hp i).pos)
  have he : (∑ i ∈ Q, log (p i)) = log (∏ i ∈ Q, (p i : ℝ)) :=
    (log_prod (fun i _ => by exact_mod_cast (hp i).ne_zero)).symm
  apply max_eq_right
  apply sub_nonpos.mpr
  by_contra hlt
  have hh : (∏ i ∈ Q, (p i : ℝ)) ≤ exp L := by
    rw [← exp_log hprod]
    exact exp_le_exp.mpr (by rw [← he]; linarith)
  apply hQ
  rw [mem_divisorSupport]
  apply Nat.le_floor
  simpa only [Nat.cast_prod] using hh

lemma prime_soft_cost_le (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (L : ℝ) (hL : 0 ≤ L) :
    kernelCost (fun i => 1 / (p i : ℝ))
      (fun Q => weight (fun i => 1 / (p i : ℝ)) Q * softProfile (fun i => log (p i)) L Q) ≤
        L * exp 2 * exp L := by
  let f := softProfile (fun i => log (p i)) L
  let D := divisorSupport p ⌊exp L⌋₊
  have hu (i : ι) : 0 ≤ log (p i : ℝ) := log_nonneg (by exact_mod_cast (hp i).one_le)
  have hpred (i : ι) : 0 < (p i : ℝ) - 1 := by
    have hh : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    linarith
  have hfactor (i : ι) : (1 + 1 / (p i : ℝ)) / (1 - 1 / (p i : ℝ)) =
      ((p i : ℝ) + 1) / (p i - 1) := by
    have hpi : (p i : ℝ) ≠ 0 := by exact_mod_cast (hp i).ne_zero
    field_simp [hpi, (hpred i).ne']
    <;> ring
  rw [kernelCost_weighted _ (prime_marginals p hp) _ (softProfile_nonneg _ L)]
  simp_rw [hfactor]
  calc
    _ = ∑ Q ∈ D, f Q * ∏ i ∈ Q, ((p i : ℝ) + 1) / (p i - 1) := by
      symm
      apply sum_subset (subset_univ _)
      intro Q hQ hQD
      rw [show f Q = 0 from prime_soft_support p hp L Q hQD, zero_mul]
    _ ≤ L * ∑ Q ∈ D, ∏ i ∈ Q, ((p i : ℝ) + 1) / (p i - 1) := by
      rw [mul_sum]
      apply sum_le_sum
      intro Q hQ
      apply mul_le_mul_of_nonneg_right (softProfile_le _ hu L hL Q)
      apply prod_nonneg
      intro i hi
      apply div_nonneg (by positivity) (hpred i).le
    _ ≤ L * (exp 2 * ⌊exp L⌋₊) := mul_le_mul_of_nonneg_left
      (divisor_cost_sum_le p hp hinj ⌊exp L⌋₊) hL
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (Nat.floor_le (exp_pos L).le)
        (mul_nonneg hL (exp_pos 2).le)
      nlinarith only [hh]

noncomputable def softBoundConstant : ℝ := (25 / 4) * exp 4 * 256 ^ 5

lemma softBoundConstant_pos : 0 < softBoundConstant := by unfold softBoundConstant; positivity

/-- Positive energy and a controlled cost, uniformly over all prime sets with
at most k members. There is no upper-size restriction on their primes. -/
theorem exists_soft_prime_kernel (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (k : ℕ) (hcard : Fintype.card ι ≤ k) :
    ∃ c : Finset ι → ℝ, 0 < kernelEnergy (fun i => 1 / (p i : ℝ)) c ∧
      (Fintype.card ι + 1 : ℝ) * kernelCost (fun i => 1 / (p i : ℝ)) c ^ 2 ≤
        softBoundConstant * ((k : ℝ) + 1) ^ 6 * kernelEnergy (fun i => 1 / (p i : ℝ)) c := by
  classical
  let P := univ.image p
  let z : ℕ := 64 * (k + 1)
  let M := log (z : ℝ) + log 4
  let L := (5 / 2 : ℝ) * M
  let q := fun i => 1 / (p i : ℝ)
  let u := fun i => log (p i : ℝ)
  let c := fun Q => weight q Q * softProfile u L Q
  have hP : ∀ a ∈ P, a.Prime := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    exact hp i
  have hPcard : P.card ≤ k := by
    exact (card_image_le.trans_eq (card_univ : (univ : Finset ι).card = Fintype.card ι)).trans hcard
  have hz : 64 ≤ z := by dsimp [z]; omega
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hM : 0 < M := by
    have hh := WeightedMertens.two_le_log_of_sixty_four_le (z := (z : ℝ)) (by exact_mod_cast hz)
    have h4 := log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp [M]; linarith
  have hmom := WeightedMertens.prime_log_moments P hP z hz (by dsimp [z]; omega)
  dsimp only [P] at hmom
  rw [sum_image hinj.injOn, sum_image hinj.injOn] at hmom
  have henergy : M ^ 2 ≤ kernelEnergy q c := by
    apply softProfile_energy_pos q u (prime_marginals p hp)
      (fun i => log_nonneg (by exact_mod_cast (hp i).one_le)) M hM
    · simpa [q, u, M, div_eq_mul_inv, mul_comm] using hmom.1
    · simpa [q, u, M, div_eq_mul_inv, mul_comm] using hmom.2
  have hL : 0 < L := by dsimp [L]; positivity
  have hcost : kernelCost q c ≤ L * exp 2 * exp L := prime_soft_cost_le p hp hinj L hL.le
  have hcost0 : 0 ≤ kernelCost q c := sum_nonneg (fun _ _ => abs_nonneg _)
  have hexp : exp (2 * L) = (4 * (z : ℝ)) ^ 5 := by
    have he : 2 * L = log ((4 * (z : ℝ)) ^ 5) := by
      rw [log_pow, log_mul (by norm_num) hz0.ne']
      dsimp [L, M]
      norm_num
      ring
    rw [he, exp_log (by positivity)]
  have hcostsq : kernelCost q c ^ 2 ≤ (25 / 4) * M ^ 2 * exp 4 * (4 * (z : ℝ)) ^ 5 := by
    have hh := (sq_le_sq₀ hcost0 (by positivity : 0 ≤ L * exp 2 * exp L)).mpr hcost
    have he : (L * exp 2 * exp L) ^ 2 = L ^ 2 * exp 4 * exp (2 * L) := by
      rw [mul_pow, mul_pow, ← exp_nat_mul, ← exp_nat_mul]
      norm_num
    rw [he, hexp] at hh
    dsimp [L] at hh
    nlinarith only [hh]
  refine ⟨c, lt_of_lt_of_le (sq_pos_of_pos hM) henergy, ?_⟩
  have hc : (Fintype.card ι + 1 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hcard 1
  calc
    _ ≤ ((k : ℝ) + 1) * kernelCost q c ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ ≤ ((k : ℝ) + 1) * ((25 / 4) * M ^ 2 * exp 4 * (4 * (z : ℝ)) ^ 5) :=
      mul_le_mul_of_nonneg_left hcostsq (by positivity)
    _ = softBoundConstant * ((k : ℝ) + 1) ^ 6 * M ^ 2 := by
      dsimp [softBoundConstant, z]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left henergy
      (mul_nonneg softBoundConstant_pos.le (by positivity))

/-- An unconditional prime-class survivor bound with a sixth-power threshold. -/
theorem prime_survivor_soft (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (k : ℕ) (hcard : Fintype.card ι ≤ k)
    (r : ℕ → ℕ) (m : ℕ)
    (hm : softBoundConstant * ((k : ℝ) + 1) ^ 6 < m) :
    ∃ j < m, ∀ i, ¬j ≡ r (p i) [MOD p i] := by
  obtain ⟨c, he, hc⟩ := exists_soft_prime_kernel p hp hinj k hcard
  have hh := survivor_of_kernelEnergy (fun i => 1 / (p i : ℝ))
    (fun i => (prime_marginals p hp i).1.ne') c m
    (fun j i => decide (j ≡ r (p i) [MOD p i]))
    (prime_hits_intersection_error p hp hinj r m)
    (hc.trans_lt (mul_lt_mul_of_pos_right hm he))
  simpa using hh

#print axioms exists_soft_prime_kernel
#print axioms prime_survivor_soft
end Erdos970.FiniteSelberg
