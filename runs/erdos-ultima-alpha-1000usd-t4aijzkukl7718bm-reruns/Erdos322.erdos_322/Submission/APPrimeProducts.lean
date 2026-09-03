import FormalConjecturesUtil

/-! Polynomially bounded initial prime sets in a reduced residue class,
infinitely often. Only nonsummability, not a prime number theorem, is used. -/
namespace Erdos322Research.APPrimeProducts
noncomputable section
open Finset Filter
open scoped Classical Topology
set_option maxHeartbeats 0
set_option Elab.async false

def primeClass {q : ℕ} (a : ZMod q) (p : ℕ) : Prop := p.Prime ∧ (p : ZMod q) = a

def nthPrime {q : ℕ} (a : ZMod q) : ℕ → ℕ := Nat.nth (primeClass a)

def weight {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  (if n.Prime then ArithmeticFunction.vonMangoldt.residueClass a n else 0) / n

lemma weight_at_prime {q : ℕ} {a : ZMod q} {p : ℕ} (hp : primeClass a p) :
    weight a p = Real.log p / p := by
  simp [weight, hp.1, ArithmeticFunction.vonMangoldt.residueClass,
    hp.2, ArithmeticFunction.vonMangoldt_apply_prime hp.1]

lemma log_div_le_two_div_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x / x ≤ 2 / Real.sqrt x := by
  have hlog := Real.log_le_rpow_div hx.le (by norm_num : (0 : ℝ) < 1/2)
  rw [← Real.sqrt_eq_rpow] at hlog
  have hsq := Real.sq_sqrt hx.le
  have hs := Real.sqrt_pos.mpr hx
  apply (div_le_iff₀ hx).mpr
  calc
    Real.log x ≤ 2 * Real.sqrt x := by linarith
    _ = (2 / Real.sqrt x) * x := by field_simp; nlinarith

/-- The rth prime in a reduced residue class is at most (r+1)^4 for
arbitrarily large r. This weak, non-effective estimate follows from Dirichlet
nonsummability and is enough for small prime products along a subsequence. -/
theorem frequently_nthPrime_le_fourth {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    ∃ᶠ r : ℕ in atTop, nthPrime a r ≤ (r+1)^4 := by
  have hinf : {p : ℕ | primeClass a p}.Infinite := Nat.infinite_setOf_prime_and_eq_mod ha
  have hinj : Function.Injective (nthPrime a) := Nat.nth_injective hinf
  have hmem (r : ℕ) : primeClass a (nthPrime a r) := Nat.nth_mem_of_infinite hinf r
  have hns : ¬ Summable (weight a ∘ nthPrime a) := by
    intro hs
    apply ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div ha
    apply (hinj.summable_iff ?_).mp hs
    intro n hn
    have hsupport := ArithmeticFunction.vonMangoldt.support_residueClass_prime_div a
    have hrange : Set.range (nthPrime a) = {p : ℕ | primeClass a p} := Nat.range_nth_of_infinite hinf
    have hn' : n ∉ Function.support (weight a) := by
      change n ∉ Function.support (fun n : ℕ ↦
        (if n.Prime then ArithmeticFunction.vonMangoldt.residueClass a n else 0) / n)
      rw [hsupport]
      simpa only [hrange, primeClass] using hn
    exact not_not.mp hn'
  by_contra h
  have he : ∀ᶠ r : ℕ in atTop, (r+1)^4 < nthPrime a r := by
    simpa only [not_le] using Filter.not_frequently.mp h
  apply hns
  have hs : Summable (fun r : ℕ ↦ 2 / ((r : ℝ)+1)^2) := by
    have hh := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
    simpa [Nat.cast_add, Nat.cast_one, mul_div_assoc] using hh.mul_left (2 : ℝ)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [he] with r hr
  have hp := hmem r
  have hp0 : (0 : ℝ) < nthPrime a r := by exact_mod_cast hp.1.pos
  have hp1 : (1 : ℝ) ≤ nthPrime a r := by exact_mod_cast hp.1.one_lt.le
  have hr0 : (0 : ℝ) < (r : ℝ)+1 := by positivity
  have hrp : ((r : ℝ)+1)^4 ≤ (nthPrime a r : ℝ) := by exact_mod_cast hr.le
  have hroot : ((r : ℝ)+1)^2 ≤ Real.sqrt (nthPrime a r : ℝ) := by
    have hh := Real.sqrt_le_sqrt hrp
    rw [show ((r : ℝ)+1)^4=(((r : ℝ)+1)^2)^2 by ring,
      Real.sqrt_sq (sq_nonneg _)] at hh
    exact hh
  change ‖weight a (nthPrime a r)‖ ≤ _
  rw [weight_at_prime hp, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.log_nonneg hp1) hp0.le)]
  exact (log_div_le_two_div_sqrt hp0).trans
    (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hr0) hroot)

/-- Arbitrarily many primes from a reduced residue class fit into a box
of polynomial size, along a subsequence of cardinalities. -/
theorem exists_prime_set_small_product {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) (R : ℕ) :
    ∃ S : Finset ℕ, R ≤ S.card ∧ 0 < S.card ∧
      (∀ p ∈ S, primeClass a p) ∧ ∏ p ∈ S, p ≤ S.card^(4*S.card) := by
  obtain ⟨r,hr,hR⟩ := ((frequently_nthPrime_le_fourth a ha).and_eventually
    (eventually_ge_atTop R)).exists
  have hinf : {p : ℕ | primeClass a p}.Infinite := Nat.infinite_setOf_prime_and_eq_mod ha
  let S := (range (r+1)).image (nthPrime a)
  have hcard : S.card = r+1 := by
    dsimp only [S, nthPrime]
    rw [card_image_of_injective _ (Nat.nth_injective hinf), card_range]
  refine ⟨S,by omega,by omega,?_,?_⟩
  · intro p hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact Nat.nth_mem_of_infinite hinf i
  · calc
      ∏ p ∈ S, p ≤ ∏ _p ∈ S, (r+1)^4 := by
        apply prod_le_prod'
        intro p hp
        obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
        exact ((Nat.nth_monotone hinf) (by have := mem_range.mp hi; omega)).trans hr
      _ = S.card^(4*S.card) := by rw [prod_const, hcard, ← pow_mul]

end
end Erdos322Research.APPrimeProducts
