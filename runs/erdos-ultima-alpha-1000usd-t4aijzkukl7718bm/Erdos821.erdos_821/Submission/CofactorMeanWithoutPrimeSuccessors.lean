import Submission.PrimeSuccessorAvoidance
import Submission.SquarefreeCofactorScales

/-!
# The two-cofactor mean does not force prime successors

The actual squarefree-modulus relative mean can coexist with the complete
absence of prime successors in a finite cofactor rectangle. The constructed
prime input may be extremely large compared with the cofactor lengths.
Thus this is not a counterexample to a distribution statement at a large
level relative to the size of the successors themselves.
-/
open Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.SuccessorAvoidance
open Erdos821.Kloosterman Erdos821.AnalyticSieve

noncomputable def singletonPrimeWeight (p : ℕ) (hp : p.Prime) : ArithmeticFunction ℝ :=
  ⟨fun n => if n=p then 1 else 0, by simp [hp.ne_zero.symm]⟩

lemma singletonPrimeWeight_nonneg (p : ℕ) (hp : p.Prime) (n : ℕ) :
    0 ≤ singletonPrimeWeight p hp n := by
  simp only [singletonPrimeWeight, ArithmeticFunction.coe_mk]
  split_ifs <;> norm_num

lemma singletonPrimeWeight_support (p : ℕ) (hp : p.Prime) (n : ℕ)
    (hn : singletonPrimeWeight p hp n ≠ 0) : n=p := by
  by_contra h
  exact hn (by simp [singletonPrimeWeight, h])

lemma singletonPrimeWeight_mass (p : ℕ) (hp : p.Prime) :
    restrictedMass (singletonPrimeWeight p hp) p = 1 := by
  simp [restrictedMass, singletonPrimeWeight, hp.one_le]

lemma singletonPrimeWeight_cofactor (p : ℕ) (hp : p.Prime) (q : ℕ) (u : (ZMod q)ˣ)
    (M N : ℤ) (B C : ℕ) :
    doubleCofactorWeight (singletonPrimeWeight p hp) q u M N B C p =
      doubleCofactorRow q u p M N B C := by
  simp [doubleCofactorWeight, singletonPrimeWeight, hp.one_le]

/-- In a fixed sufficiently long cofactor rectangle, the relative mean is
uniform for every prime input above Q, regardless of the successor primes. -/
theorem eventually_prime_input_rectangle_mean (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ p : ℕ, p.Prime → rectangleModulusScale m < p →
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ rectangleModulusScale m) →
      ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
        (∑ q ∈ P, |doubleCofactorRow q (u q) p 1 1
          (rectangleIntervalScale m) (rectangleIntervalScale m) -
          (rectangleIntervalScale m : ℝ)^2*q.totient/(q : ℝ)^2|) ≤
            η*(rectangleIntervalScale m : ℝ)^2 := by
  filter_upwards [eventually_doubleCofactor_squarefree_prime_weight η hη] with m hm
  intro p hp hQp P hP u
  have hf : ∀ n, singletonPrimeWeight p hp n ≠ 0 → n.Prime ∧ rectangleModulusScale m < n := by
    intro n hn
    rw [singletonPrimeWeight_support p hp n hn]
    exact ⟨hp,hQp⟩
  have hh := hm (singletonPrimeWeight p hp) (singletonPrimeWeight_nonneg p hp)
    hf P hP p 1 1 u
  simpa only [singletonPrimeWeight_cofactor, squarefreeCofactorMain,
    singletonPrimeWeight_mass, mul_one, sq] using hh

/-- All successors are composite, with an explicit proper prime divisor
above Q, while the already proved squarefree-modulus relative mean holds.
This disproves no statement about the actual totient multiplicities. -/
theorem eventually_rectangle_mean_and_no_prime_successors (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ T : ℕ, ∃ p : ℕ,
      T < p ∧ rectangleModulusScale m < p ∧ p.Prime ∧
      (∀ a ∈ Icc 1 (rectangleIntervalScale m), ∀ b ∈ Icc 1 (rectangleIntervalScale m),
        ∃ q : ℕ, rectangleModulusScale m < q ∧ q.Prime ∧
          q ∣ a*b*p+1 ∧ q < a*b*p+1) ∧
      ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ rectangleModulusScale m) →
      ∀ u : ∀ q : ℕ, (ZMod q)ˣ,
        (∑ q ∈ P, |doubleCofactorRow q (u q) p 1 1
          (rectangleIntervalScale m) (rectangleIntervalScale m) -
          (rectangleIntervalScale m : ℝ)^2*q.totient/(q : ℝ)^2|) ≤
            η*(rectangleIntervalScale m : ℝ)^2 := by
  filter_upwards [eventually_prime_input_rectangle_mean η hη] with m hm
  intro T
  obtain ⟨p,hpT,hp,H⟩ := exists_prime_no_rectangle_successors
    (rectangleIntervalScale m) (rectangleIntervalScale m) (rectangleModulusScale m)
    (T+rectangleModulusScale m)
  have hQp : rectangleModulusScale m < p := by omega
  exact ⟨p,by omega,hQp,hp,H,hm p hp hQp⟩

/-- The scale identity relative to the full product, rather than just
 the two free cofactors. -/
lemma rectangle_ambient_scale_identity (m : ℕ) :
    rectangleModulusScale m ^ 25 =
      (rectangleModulusScale m * rectangleIntervalScale m ^ 2)^9 := by
  rw [mul_pow, ← rectangleScale_power_relation, ← pow_add]

/-- If the prime input lies above Q, the declared Q cutoff has exponent
at most 9/25 relative to the full product size p*L^2, not exponent 9/16. -/
lemma prime_input_ambient_scale_bound (m p : ℕ) (hp : rectangleModulusScale m < p) :
    rectangleModulusScale m ^ 25 < (p * rectangleIntervalScale m ^ 2)^9 := by
  rw [rectangle_ambient_scale_identity]
  exact Nat.pow_lt_pow_left (Nat.mul_lt_mul_of_pos_right hp
    (by unfold rectangleIntervalScale; positivity)) (by decide)

lemma prime_input_cutoff_below_ambient_half (m p : ℕ) (hp : rectangleModulusScale m < p) :
    rectangleModulusScale m ^ 2 < p * rectangleIntervalScale m ^ 2 := by
  have hL : rectangleModulusScale m ≤ rectangleIntervalScale m ^ 2 := by
    unfold rectangleModulusScale rectangleIntervalScale
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    omega
  calc
    _ = rectangleModulusScale m * rectangleModulusScale m := by rw [sq]
    _ ≤ rectangleModulusScale m * rectangleIntervalScale m ^ 2 := Nat.mul_le_mul_left _ hL
    _ < _ := Nat.mul_lt_mul_of_pos_right hp (by unfold rectangleIntervalScale; positivity)

end Erdos821.SuccessorAvoidance
