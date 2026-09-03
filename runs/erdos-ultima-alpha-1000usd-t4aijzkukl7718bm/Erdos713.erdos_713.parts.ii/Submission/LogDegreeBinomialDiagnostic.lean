import FormalConjecturesUtil
import Submission.PolynomialInequalityCriterion

/-! Logarithmic-degree binomial bounds do not imply rationality. No sequence
here is asserted to be the extremal number for a fixed forbidden graph. -/

open Filter Asymptotics
open scoped Topology
namespace Erdos713LogDegreeBinomialDiagnostic

/-- At a single order, a binomial of degree at most `A*q` bounds any positive
objective `f ≤ n^A` sharply within factor two, provided `n ≤ 2^q`. -/
theorem finite_certificate {n f A q : ℕ} (hn : 1 < n) (hf : 0 < f)
    (hbound : f ≤ n^A) (hq : 0 < q) (hscale : n ≤ 2^q) :
    ∃ p : ℕ, p ≤ A*q ∧ f^q ≤ n^p ∧
      ∀ m : ℕ, m^q ≤ n^p → m ≤ 2*f := by
  let p := Nat.clog n (f^q)
  have hfeas : f^q ≤ n^p := Nat.le_pow_clog hn _
  have hpbound : p ≤ A*q := by
    apply Nat.clog_le_of_le_pow
    simpa only [pow_mul] using Nat.pow_le_pow_left hbound q
  refine ⟨p, hpbound, hfeas, ?_⟩
  intro m hm
  by_cases hp : p = 0
  · have hm1 : m^q ≤ 1^q := by simpa [hp] using hm
    have hmle : m ≤ 1 := (Nat.pow_le_pow_iff_left hq.ne').mp hm1
    omega
  · have hpred : n^(p-1) < f^q := by
      apply Nat.pow_lt_of_lt_clog
      change p - 1 < p
      omega
    have hpow : n^p ≤ (2*f)^q := calc
      n^p = n^(p-1)*n := by
        rw [← pow_succ]
        congr 1
        omega
      _ ≤ f^q*n := Nat.mul_le_mul_right n hpred.le
      _ ≤ f^q*2^q := Nat.mul_le_mul_left _ hscale
      _ = (2*f)^q := by rw [mul_pow, mul_comm]
    exact (Nat.pow_le_pow_iff_left hq.ne').mp (hm.trans hpow)

def denominator (n : ℕ) : ℕ := Nat.log 2 n + 1

def numerator (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.clog n ((f n)^(denominator n))

/-- The same explicit bound works independently at every order. Its two
coefficients are constant; only its monomial exponents change. -/
theorem logarithmic_certificate (f : ℕ → ℕ) {n A : ℕ} (hn : 1 < n)
    (hf : 0 < f n) (hbound : f n ≤ n^A) :
    0 < denominator n ∧ numerator f n ≤ A*denominator n ∧
      (f n)^(denominator n) ≤ n^(numerator f n) ∧
      ∀ m : ℕ, m^(denominator n) ≤ n^(numerator f n) → m ≤ 2*f n := by
  have hq : 0 < denominator n := by simp [denominator]
  have hscale : n ≤ 2^(denominator n) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
  have h := finite_certificate hn hf hbound hq hscale
  -- The construction in the finite proof is made explicit here by the
  -- defining properties of ceiling logarithms.
  refine ⟨hq, ?_, Nat.le_pow_clog hn _, ?_⟩
  · apply Nat.clog_le_of_le_pow
    simpa only [pow_mul] using Nat.pow_le_pow_left hbound (denominator n)
  · obtain ⟨p, _, hp, hsharp⟩ := h
    have hnp : numerator f n ≤ p := Nat.clog_le_of_le_pow hp
    intro m hm
    apply hsharp m
    exact hm.trans (Nat.pow_le_pow_right hn.le hnp)

noncomputable def floorPower (α : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ)^α⌋₊

lemma floorPower_bounds {α : ℝ} (hα : 0 ≤ α) (hαtwo : α ≤ 2)
    {n : ℕ} (hn : 1 < n) : 0 < floorPower α n ∧ floorPower α n ≤ n^2 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn.le
  have hlo : (1 : ℝ) ≤ (n : ℝ)^α := Real.one_le_rpow hnR hα
  have hhi : (n : ℝ)^α ≤ (n : ℝ)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hnR hαtwo
  constructor
  · have h : (1 : ℕ) ≤ ⌊(n : ℝ)^α⌋₊ := (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ (n : ℝ)^α)).mpr (by simpa using hlo)
    change 0 < ⌊(n : ℝ)^α⌋₊
    omega
  · change ⌊(n : ℝ)^α⌋₊ ≤ n^2
    apply Nat.floor_le_of_le
    simpa only [Nat.cast_pow, Real.rpow_two] using hhi

/-- An irrational pure-power sequence with factor-two-sharp binomial
certificates, coefficient height one, and degree at most twice log₂(n)+2. -/
theorem irrational_example :
    ∃ (f : ℕ → ℕ) (α : ℝ), Irrational α ∧ 1 < α ∧ α < 2 ∧
      (fun n : ℕ => (f n : ℝ)) ~[atTop]
        (fun n : ℕ => (1 : ℝ)*(n : ℝ)^α) ∧
      ∀ n : ℕ, 1 < n →
        0 < denominator n ∧ numerator f n ≤ 2*denominator n ∧
        (f n)^(denominator n) ≤ n^(numerator f n) ∧
        ∀ m : ℕ, m^(denominator n) ≤ n^(numerator f n) → m ≤ 2*f n := by
  have hsquare : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hnonneg := Real.sqrt_nonneg (2 : ℝ)
  have hαlo : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  have hαhi : Real.sqrt 2 < (2 : ℝ) := by nlinarith
  refine ⟨floorPower (Real.sqrt 2), Real.sqrt 2, irrational_sqrt_two,
    hαlo, hαhi, ?_, ?_⟩
  · exact Erdos713PolynomialInequality.floor_rpow_asymptotic (by positivity)
  · intro n hn
    obtain ⟨hf, hbound⟩ := floorPower_bounds (by positivity) hαhi.le hn
    exact logarithmic_certificate _ hn hf hbound

end Erdos713LogDegreeBinomialDiagnostic
