import Submission.AffinePotentialCertificates

/-! Multiplicative and matrix-valued certificate criteria. No sufficient
witness is asserted, and these results do not settle Erdős 406. -/
namespace Erdos406Matrix
open Erdos406AffineCertificate Erdos406GroupedCertificate Erdos406AffinePotential
open scoped BigOperators Matrix

lemma power_rates_subcritical (lam ρ : ℝ) (_hlam : 1 < lam) (hρ : 1 ≤ ρ)
    (p q : ℕ) (hq : 0 < q) (hupper : ρ ^ q < 3 ^ p) (hlower : 4 ^ p < lam ^ q) :
    Real.log ρ * Real.log 4 < Real.log lam * Real.log 3 := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have ha := Real.log_lt_log (by positivity : (0 : ℝ) < 4 ^ p) hlower
  have hb := Real.log_lt_log (pow_pos (by linarith : 0 < ρ) q) hupper
  rw [Real.log_pow, Real.log_pow] at ha hb
  have hA := mul_lt_mul_of_pos_right ha h3
  have hB := mul_lt_mul_of_pos_right hb h4
  apply (mul_lt_mul_iff_right₀ hqR).mp
  nlinarith

/-- Exponential growth and a slower good-word rate suffice. The scalar
function need not be positive away from the actual orbit. -/
theorem multiplicative_affine_criterion (S : ℕ → ℝ) (lam ρ K : ℝ)
    (hlam : 1 < lam) (hρ : 1 ≤ ρ) (hK : 0 < K) (hzero : 0 < S 0)
    (hgrow : ∀ n, lam * S n ≤ S (4 * n + 1))
    (hgood : ∀ n, Good n → S n ≤ K * ρ ^ (Nat.digits 3 n).length)
    (hcrit : Real.log ρ * Real.log 4 < Real.log lam * Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  have hlam0 : 0 < lam := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogρ : 0 ≤ Real.log ρ := Real.log_nonneg hρ
  have hgap : 0 < Real.log lam * Real.log 3 - Real.log ρ * Real.log 4 := by linarith
  have horbit : ∀ t : ℕ, lam ^ t * S 0 ≤ S (orbit 4 1 t) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hs := hgrow (orbit 4 1 t)
      have hh := mul_le_mul_of_nonneg_left ih hlam0.le
      rw [orbit_succ, pow_succ]
      nlinarith
  obtain ⟨M, hM⟩ := exists_nat_gt
    ((Real.log K - Real.log (S 0)) * Real.log 3 /
      (Real.log lam * Real.log 3 - Real.log ρ * Real.log 4))
  have hlarge := (div_lt_iff₀ hgap).mp hM
  have hcut : ∀ t : ℕ, M ≤ t → ¬ Good (orbit 4 1 t) := by
    intro t ht hg
    have hb := (horbit t).trans (hgood _ hg)
    have hl := Real.log_le_log (mul_pos (pow_pos hlam0 t) hzero) hb
    rw [Real.log_mul (ne_of_gt (pow_pos hlam0 t)) (ne_of_gt hzero),
      Real.log_mul (ne_of_gt hK) (ne_of_gt (pow_pos hρ0 _)),
      Real.log_pow, Real.log_pow] at hl
    have hl' := mul_le_mul_of_nonneg_right hl hlog3.le
    have hlen := mul_le_mul_of_nonneg_left (orbit_length_log_le t) hlogρ
    have htR : (M : ℝ) ≤ t := by exact_mod_cast ht
    have hmul := mul_le_mul_of_nonneg_right htR hgap.le
    nlinarith
  apply Erdos406SingleAffine.single_affine_criterion
  refine ((Finset.range M).finite_toSet.image (orbit 4 1)).subset ?_
  rintro n ⟨⟨t, rfl⟩, hg⟩
  refine ⟨t, ?_, rfl⟩
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hn
  exact hcut t (by omega) hg

variable {σ : Type*} [Fintype σ]

lemma dot_mono_left {a b v : σ → ℝ} (hab : a ≤ b) (hv : 0 ≤ v) :
    a ⬝ᵥ v ≤ b ⬝ᵥ v := by
  apply Finset.sum_le_sum
  intro i _hi
  exact mul_le_mul_of_nonneg_right (hab i) (hv i)

lemma dot_mono_right {a v w : σ → ℝ} (ha : 0 ≤ a) (hvw : v ≤ w) :
    a ⬝ᵥ v ≤ a ⬝ᵥ w := by
  apply Finset.sum_le_sum
  intro i _hi
  exact mul_le_mul_of_nonneg_left (hvw i) (ha i)

lemma mulVec_mono_right {A : Matrix σ σ ℝ} {v w : σ → ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hvw : v ≤ w) : A *ᵥ v ≤ A *ᵥ w := by
  intro i
  exact dot_mono_right (hA i) hvw

lemma mulVec_mono_left {A B : Matrix σ σ ℝ} {v : σ → ℝ}
    (hAB : ∀ i j, A i j ≤ B i j) (hv : 0 ≤ v) : A *ᵥ v ≤ B *ᵥ v := by
  intro i
  exact dot_mono_left (hAB i) hv

structure Dynamics (σ : Type*) [Fintype σ] where
  A : ℕ → Matrix σ σ ℝ
  v : ℕ → (σ → ℝ)
  nonneg : ∀ d < 3, ∀ i j, 0 ≤ A d i j
  initial_nonneg : 0 ≤ v 0
  recurrence : ∀ n, 0 < n → v n = A (n % 3) *ᵥ v (n / 3)
  H : ℕ → Matrix σ σ ℝ
  seed : ∀ c < 4, H c *ᵥ v 0 ≤ v c
  step : ∀ c d e cp, c < 4 → d < 3 → e < 3 → cp < 4 →
    4 * d + cp = 3 * c + e → ∀ i j, (H cp * A d) i j ≤ (A e * H c) i j

namespace Dynamics
variable (D : Dynamics σ)

lemma value_nonneg (n : ℕ) : 0 ≤ D.v n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; exact D.initial_nonneg
    have hp : 0 < n := Nat.pos_of_ne_zero hn
    have hi := ih (n / 3) (Nat.div_lt_self hp (by decide))
    rw [D.recurrence n hp]
    intro i
    apply Finset.sum_nonneg
    intro j _hj
    exact mul_nonneg (D.nonneg _ (Nat.mod_lt _ (by decide)) i j) (hi j)

lemma simulate (n c : ℕ) (hc : c < 4) : D.H c *ᵥ D.v n ≤ D.v (4 * n + c) := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; simpa using D.seed c hc
    have hp : 0 < n := Nat.pos_of_ne_zero hn
    let d := n % 3
    let cp := (4 * d + c) / 3
    let e := (4 * d + c) % 3
    have hd : d < 3 := Nat.mod_lt _ (by decide)
    have hcp : cp < 4 := by dsimp [cp]; omega
    have he : e < 3 := Nat.mod_lt _ (by decide)
    have har : 4 * d + c = 3 * cp + e := by dsimp [cp,e]; omega
    have hi := ih (n / 3) (Nat.div_lt_self hp (by decide)) cp hcp
    have hs := mulVec_mono_left (D.step cp d e c hcp hd he hc har) (D.value_nonneg (n / 3))
    have hm := mulVec_mono_right (D.nonneg e he) hi
    rw [Matrix.mulVec_mulVec] at hm
    obtain ⟨hq, hr⟩ := affine_div_mod 3 4 n c (by decide)
    rw [D.recurrence n hp, D.recurrence (4 * n + c) (by omega), hq, hr,
      Matrix.mulVec_mulVec]
    exact hs.trans hm

lemma scalar_growth (u : σ → ℝ) (lam : ℝ) (hu : 0 ≤ u)
    (hfinish : ∀ j, lam * u j ≤ Matrix.vecMul u (D.H 1) j) (n : ℕ) :
    lam * (u ⬝ᵥ D.v n) ≤ u ⬝ᵥ D.v (4 * n + 1) := by
  have hl := dot_mono_left hfinish (D.value_nonneg n)
  have hh := dot_mono_right hu (D.simulate n 1 (by decide))
  rw [Matrix.dotProduct_mulVec] at hh
  have he : (fun j => lam * u j) ⬝ᵥ D.v n = lam * (u ⬝ᵥ D.v n) := by
    simp only [dotProduct, Finset.mul_sum, mul_assoc]
  rw [he] at hl
  exact hl.trans hh

lemma good_rate (ell : σ → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hgood : ∀ d < 2, ∀ j, Matrix.vecMul ell (D.A d) j ≤ ρ * ell j)
    (n : ℕ) (hn : Good n) :
    ell ⬝ᵥ D.v n ≤ ρ ^ (Nat.digits 3 n).length * (ell ⬝ᵥ D.v 0) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n; simp
    have hp : 0 < n := Nat.pos_of_ne_zero hz
    have hg : Good (n / 3) := by
      simpa using Erdos406SparseTriple.good_div_pow hn 1
    have hi := ih (n / 3) (Nat.div_lt_self hp (by decide)) hg
    have hd : n % 3 < 2 := by
      have hm := hn (by rw [Nat.digits_of_two_le_of_pos (by decide) hp]; exact List.mem_cons_self ..)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      omega
    have hs := dot_mono_left (hgood _ hd) (D.value_nonneg (n / 3))
    have hm := mul_le_mul_of_nonneg_left hi hρ
    rw [D.recurrence n hp, Matrix.dotProduct_mulVec,
      Nat.digits_of_two_le_of_pos (by decide) hp, List.length_cons, pow_succ]
    have he : (fun j => ρ * ell j) ⬝ᵥ D.v (n / 3) = ρ * (ell ⬝ᵥ D.v (n / 3)) := by
      simp only [dotProduct, Finset.mul_sum, mul_assoc]
    rw [he] at hs
    nlinarith
end Dynamics

/-- A genuinely sufficient matrix witness would prove the exact original
conjecture. No such witness has been found. Signed H matrices are allowed;
only the digit update matrices are required to be nonnegative. -/
theorem matrix_affine_criterion (D : Dynamics σ) (u ell : σ → ℝ) (lam ρ : ℝ)
    (hu : 0 ≤ u) (hul : u ≤ ell) (hzero : 0 < u ⬝ᵥ D.v 0)
    (hlam : 1 < lam) (hρ : 1 ≤ ρ)
    (hfinish : ∀ j, lam * u j ≤ Matrix.vecMul u (D.H 1) j)
    (hgood : ∀ d < 2, ∀ j, Matrix.vecMul ell (D.A d) j ≤ ρ * ell j)
    (hcrit : Real.log ρ * Real.log 4 < Real.log lam * Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  have hK : 0 < ell ⬝ᵥ D.v 0 := hzero.trans_le (dot_mono_left hul (D.value_nonneg 0))
  apply multiplicative_affine_criterion (fun n => u ⬝ᵥ D.v n) lam ρ
    (ell ⬝ᵥ D.v 0) hlam hρ hK hzero (D.scalar_growth u lam hu hfinish) ?_ hcrit
  intro n hn
  have hh := (dot_mono_left hul (D.value_nonneg n)).trans (D.good_rate ell ρ (by linarith) hgood n hn)
  simpa [mul_comm] using hh

#print axioms multiplicative_affine_criterion
#print axioms Dynamics.simulate
#print axioms matrix_affine_criterion
end Erdos406Matrix
