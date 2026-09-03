import FormalConjecturesUtil
import Submission.PolynomialInequalityCriterion

/-! Under a positive power asymptotic, rationality is equivalent to a sharp
single-binomial relaxation. This is a reformulation, not a derivation of
such a relaxation for arbitrary graph extremal numbers. -/
open Filter Asymptotics
open scoped Topology
namespace Erdos713BinomialRelaxation
open Erdos713PolynomialRate Erdos713PolynomialInequality
set_option maxHeartbeats 1000000

/-- The single inequality y^q <= A*n^p is feasible at f and, among integer
values of y, bounds f within a constant factor. -/
def HasBinomialRelaxation (f : ℕ → ℕ) : Prop :=
  ∃ p q A : ℕ, 0 < q ∧ 0 < A ∧ ∃ K : ℝ,
    (∀ᶠ n : ℕ in atTop, f n ^ q ≤ A * n ^ p) ∧
    (∀ᶠ n : ℕ in atTop, ∀ m : ℕ, m ^ q ≤ A * n ^ p → (m : ℝ) ≤ K * f n)

lemma nat_fraction_of_positive_rational {α : ℝ} (hα : 0 < α)
    (hrat : α ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∃ p q : ℕ, 0 < q ∧ α * (q : ℝ) = p := by
  obtain ⟨r, rfl⟩ := hrat
  have hr : 0 ≤ r.num := Rat.num_nonneg.mpr (Rat.cast_nonneg.mp hα.le)
  refine ⟨r.num.toNat, r.den, r.den_pos, ?_⟩
  have hnum : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hr
  rw [hnum, Rat.cast_def, div_mul_cancel₀]
  exact_mod_cast r.den_pos.ne'

lemma relaxation_of_rational {f : ℕ → ℕ} {α c : ℝ} (hα : 0 < α) (hc : 0 < c)
    (hf : (fun n => (f n : ℝ)) ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ α))
    (hrat : α ∈ Set.range ((↑) : ℚ → ℝ)) : HasBinomialRelaxation f := by
  obtain ⟨p, q, hq, hpq⟩ := nat_fraction_of_positive_rational hα hrat
  obtain ⟨B, hB⟩ := exists_nat_gt (2 * c)
  have hBpos : 0 < B := by
    have hh : (0 : ℝ) < B := by linarith
    exact_mod_cast hh
  have hlim := ratio_limit hf
  have hsmall := hlim.eventually_lt_const (show c < (B : ℝ) by linarith)
  have hlarge := hlim.eventually_const_lt (show c / 2 < c by linarith)
  have hpow (n : ℕ) : ((n : ℝ) ^ α) ^ q = (n : ℝ) ^ p := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n), hpq, Real.rpow_natCast]
  refine ⟨p, q, B ^ q, hq, pow_pos hBpos _, 2 * B / c, ?_, ?_⟩
  · filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with n hn hnp
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnp
    have hupper : (f n : ℝ) ≤ B * (n : ℝ) ^ α :=
      ((div_lt_iff₀ (Real.rpow_pos_of_pos hnR α)).mp hn).le
    have hpower := pow_le_pow_left₀ (Nat.cast_nonneg (f n)) hupper q
    rw [mul_pow, hpow] at hpower
    exact_mod_cast hpower
  · filter_upwards [hlarge, eventually_gt_atTop (0 : ℕ)] with n hn hnp m hm
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnp
    have hlower : c / 2 * (n : ℝ) ^ α ≤ f n :=
      ((lt_div_iff₀ (Real.rpow_pos_of_pos hnR α)).mp hn).le
    have hmR : (m : ℝ) ^ q ≤ (B : ℝ) ^ q * (n : ℝ) ^ p := by exact_mod_cast hm
    rw [← hpow, ← mul_pow] at hmR
    have hupper : (m : ℝ) ≤ B * (n : ℝ) ^ α :=
      (pow_le_pow_iff_left₀ (Nat.cast_nonneg m) (by positivity) hq.ne').mp hmR
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    have h1 := mul_le_mul_of_nonneg_left hupper hc.le
    have h2 := mul_le_mul_of_nonneg_left hlower (show (0 : ℝ) ≤ 2 * B by positivity)
    nlinarith

lemma rational_of_relaxation {f : ℕ → ℕ} {α c : ℝ} (hα : 0 < α) (hc : 0 < c)
    (hf : (fun n => (f n : ℝ)) ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ α))
    (hrel : HasBinomialRelaxation f) : α ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  obtain ⟨p, q, A, hq, hA, K, hfeas, hsharp⟩ := hrel
  let s : Finset (ℕ × ℕ) := {(p, 0), (0, q)}
  let a : (ℕ × ℕ) → ℝ := fun t => if t = (p, 0) then A else -1
  have hne : (p, 0) ≠ (0, q) := by
    intro he
    have hh := congrArg Prod.snd he
    omega
  have heval (x y : ℝ) : eval s a x y = A * x ^ p - y ^ q := by
    simp [eval, s, a, hne, hne.symm, sub_eq_add_neg]
  have hs : s.Nonempty := ⟨(p, 0), by simp [s]⟩
  have ha : ∀ t ∈ s, a t ≠ 0 := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · simp only [a, if_pos rfl]
      exact_mod_cast hA.ne'
    · have ht' : t = (0, q) := Finset.mem_singleton.mp ht
      simp [a, ht', hne.symm]
  apply rational_of_finite_sharp_relaxation (I := Unit) hα hc hf
    (fun _ => s) (fun _ => hs) (fun _ => a) (fun _ => ha) ?_ K ?_
  · intro _
    filter_upwards [hfeas] with n hn
    rw [heval]
    have hnR : (f n : ℝ) ^ q ≤ (A : ℝ) * (n : ℝ) ^ p := by exact_mod_cast hn
    linarith
  · filter_upwards [hsharp] with n hn m hm
    apply hn m
    have hmR := hm ()
    rw [heval] at hmR
    have hh : (m : ℝ) ^ q ≤ (A : ℝ) * (n : ℝ) ^ p := by linarith
    exact_mod_cast hh

/-- The certificate criterion is equivalent to the rationality conclusion
under the stated asymptotic, not a consequence of that asymptotic alone. -/
theorem rational_iff_binomial_relaxation {f : ℕ → ℕ} {α c : ℝ}
    (hα : 0 < α) (hc : 0 < c)
    (hf : (fun n => (f n : ℝ)) ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ α)) :
    α ∈ Set.range ((↑) : ℚ → ℝ) ↔ HasBinomialRelaxation f :=
  ⟨relaxation_of_rational hα hc hf, rational_of_relaxation hα hc hf⟩

#print axioms relaxation_of_rational
#print axioms rational_of_relaxation
#print axioms rational_iff_binomial_relaxation
end Erdos713BinomialRelaxation
