import Submission.APPrimeProducts

/-! Near-linear power bounds for initial prime sets in a reduced progression,
infinitely often. Dirichlet nonsummability suffices; no PNT is used. -/
namespace Erdos322Research.APPrimeProductsSharp
noncomputable section
open Finset Filter APPrimeProducts
open scoped Classical Topology
set_option Elab.async false
set_option maxHeartbeats 0

lemma weight_nth_not_summable {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    ¬Summable (weight a ∘ nthPrime a) := by
  have hinf : {p : ℕ | primeClass a p}.Infinite := Nat.infinite_setOf_prime_and_eq_mod ha
  have hinj : Function.Injective (nthPrime a) := Nat.nth_injective hinf
  intro hs
  apply ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div ha
  apply (hinj.summable_iff ?_).mp hs
  intro n hn
  have hsupport := ArithmeticFunction.vonMangoldt.support_residueClass_prime_div a
  have hrange : Set.range (nthPrime a)={p : ℕ | primeClass a p} := Nat.range_nth_of_infinite hinf
  have hn' : n ∉ Function.support (weight a) := by
    change n ∉ Function.support (fun n : ℕ ↦
      (if n.Prime then ArithmeticFunction.vonMangoldt.residueClass a n else 0)/n)
    rw [hsupport]
    simpa only [hrange,primeClass] using hn
  exact not_not.mp hn'

/-- For every exponent a>1, the rth prime is at most (r+1)^a infinitely often. -/
theorem frequently_nthPrime_le_rpow {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) (α : ℝ) (hα : 1 < α) :
    ∃ᶠ r : ℕ in atTop, (nthPrime a r : ℝ) ≤ ((r : ℝ)+1)^α := by
  have hα0 : 0 < α := by linarith
  let β := (α+1)/2
  have hβ : 1 < β := by dsimp [β]; linarith
  have hβα : β < α := by dsimp [β]; linarith
  let η := 1-β/α
  have hη : 0 < η := by
    dsimp [η]
    exact sub_pos.mpr ((div_lt_one hα0).mpr hβα)
  have hη1 : η-1 < 0 := by
    dsimp [η]
    have h := div_pos (show 0 < β by linarith) hα0
    linarith
  have hηmul : α*(η-1)= -β := by dsimp [η]; field_simp; ring
  have hinf : {p : ℕ | primeClass a p}.Infinite := Nat.infinite_setOf_prime_and_eq_mod ha
  by_contra h
  have he : ∀ᶠ r : ℕ in atTop, ((r : ℝ)+1)^α < (nthPrime a r : ℝ) := by
    simpa only [not_le] using Filter.not_frequently.mp h
  apply weight_nth_not_summable a ha
  have hs : Summable (fun r : ℕ ↦ η⁻¹*((r : ℝ)+1)^(-β)) := by
    have hh := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -β < -1))
    simpa only [Nat.cast_add,Nat.cast_one] using hh.mul_left η⁻¹
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [he] with r hr
  have hp : primeClass a (nthPrime a r) := Nat.nth_mem_of_infinite hinf r
  have hp0 : (0 : ℝ) < nthPrime a r := by exact_mod_cast hp.1.pos
  have hp1 : (1 : ℝ) ≤ nthPrime a r := by exact_mod_cast hp.1.one_lt.le
  have hr0 : (0 : ℝ) < (r : ℝ)+1 := by positivity
  change ‖weight a (nthPrime a r)‖ ≤ _
  rw [weight_at_prime hp,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (Real.log_nonneg hp1) hp0.le)]
  calc
    Real.log (nthPrime a r : ℝ)/(nthPrime a r : ℝ) ≤
        (((nthPrime a r : ℝ)^η)/η)/(nthPrime a r : ℝ) := by
      exact div_le_div_of_nonneg_right (Real.log_le_rpow_div hp0.le hη) hp0.le
    _ = η⁻¹*(nthPrime a r : ℝ)^(η-1) := by
      conv_rhs => rw [Real.rpow_sub hp0,Real.rpow_one]
      ring
    _ ≤ η⁻¹*(((r : ℝ)+1)^α)^(η-1) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hη.le)
      exact Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hr0 _) hr.le hη1.le
    _ = η⁻¹*((r : ℝ)+1)^(-β) := by rw [← Real.rpow_mul hr0.le,hηmul]

/-- Products of arbitrarily many primes satisfy the sharp power scale along
a subsequence of cardinalities. This is not an estimate for every cardinality. -/
theorem exists_prime_set_small_product {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) (α : ℝ) (hα : 1 < α) (R : ℕ) :
    ∃ S : Finset ℕ, R ≤ S.card ∧ 0 < S.card ∧
      (∀ p ∈ S, primeClass a p) ∧
      ((∏ p ∈ S,p : ℕ) : ℝ) ≤ (S.card : ℝ)^(α*S.card) := by
  obtain ⟨r,hr,hR⟩ := ((frequently_nthPrime_le_rpow a ha α hα).and_eventually
    (eventually_ge_atTop R)).exists
  have hinf : {p : ℕ | primeClass a p}.Infinite := Nat.infinite_setOf_prime_and_eq_mod ha
  let S := (range (r+1)).image (nthPrime a)
  have hcard : S.card=r+1 := by
    dsimp only [S,nthPrime]
    rw [card_image_of_injective _ (Nat.nth_injective hinf),card_range]
  refine ⟨S,by omega,by omega,?_,?_⟩
  · intro p hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact Nat.nth_mem_of_infinite hinf i
  · calc
      ((∏ p ∈ S,p : ℕ) : ℝ) ≤ ∏ _p ∈ S, ((r : ℝ)+1)^α := by
        rw [Nat.cast_prod]
        apply prod_le_prod (fun _ _ ↦ Nat.cast_nonneg _)
        intro p hp
        obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
        have hm : nthPrime a i ≤ nthPrime a r :=
          (Nat.nth_monotone hinf) (by have := mem_range.mp hi; omega)
        exact (by exact_mod_cast hm : (nthPrime a i : ℝ) ≤ nthPrime a r).trans hr
      _ = (S.card : ℝ)^(α*S.card) := by
        rw [prod_const,← Real.rpow_mul_natCast (by positivity),hcard]
        simp only [Nat.cast_add,Nat.cast_one]

end
end Erdos322Research.APPrimeProductsSharp
