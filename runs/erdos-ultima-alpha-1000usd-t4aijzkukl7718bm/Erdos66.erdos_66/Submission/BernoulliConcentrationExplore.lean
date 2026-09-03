import Submission.FiniteBernoulliExplore

/-! Finite Chernoff estimates and a simultaneous-existence criterion, expressed
as finite weighted averages rather than measure-theoretic probabilities. -/
namespace Erdos66BernoulliConcentration
open Erdos66FiniteBernoulli
open scoped Classical
variable {ι κ : Type*} [Fintype ι]

lemma product_probability_bounds (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset ι) :
    0 ≤ (∏ i ∈ S, p i) ∧ (∏ i ∈ S, p i) ≤ 1 := by
  exact ⟨Finset.prod_nonneg (fun i _ ↦ (hp i).1),
    Finset.prod_le_one (fun i _ ↦ (hp i).1) (fun i _ ↦ (hp i).2)⟩

/-- The variance proxy is proportional to the mean, not the number of possible
summands. The summands may have any weights between zero and two. -/
theorem centered_mgf_bound (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset κ) (E : κ → Finset ι)
    (hE : (S : Set κ).Pairwise (fun i j ↦ Disjoint (E i) (E j)))
    (w : κ → ℝ) (hw : ∀ k ∈ S, 0 ≤ w k ∧ w k ≤ 2) (t : ℝ) (ht : |t| ≤ 1 / 2) :
    expect p (fun ω ↦ Real.exp (t * ((∑ k ∈ S, w k * monomial (E k) ω) -
      ∑ k ∈ S, w k * ∏ i ∈ E k, p i))) ≤
      Real.exp (2 * t ^ 2 * (∑ k ∈ S, w k * ∏ i ∈ E k, p i)) := by
  let m : ℝ := ∑ k ∈ S, w k * ∏ i ∈ E k, p i
  let v (k : κ) : ℝ := ∏ i ∈ E k, p i
  have hv (k : κ) : 0 ≤ v k ∧ v k ≤ 1 := product_probability_bounds p hp (E k)
  have hfactor (k : κ) : 0 ≤ 1 + (Real.exp (t * w k) - 1) * v k := by
    have hh := Real.exp_pos (t * w k)
    have hh' := mul_nonneg hh.le (hv k).1
    nlinarith [(hv k).1, (hv k).2]
  have hprod : (∏ k ∈ S, (1 + (Real.exp (t * w k) - 1) * v k)) ≤
      Real.exp (∑ k ∈ S, (Real.exp (t * w k) - 1) * v k) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro k hk; exact hfactor k
    · intro k hk
      simpa only [add_comm] using Real.add_one_le_exp ((Real.exp (t * w k) - 1) * v k)
  have hexp : (∑ k ∈ S, (Real.exp (t * w k) - 1) * v k) - t * m ≤ 2 * t ^ 2 * m := by
    have hterm (k : κ) (hk : k ∈ S) :
        (Real.exp (t * w k) - 1 - t * w k) * v k ≤ 2 * t ^ 2 * (w k * v k) := by
      have htw : |t * w k| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg (hw k hk).1]
        nlinarith [mul_le_mul ht (hw k hk).2 (hw k hk).1 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      have hh := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le htw)).2
      have hw2 : w k ^ 2 ≤ 2 * w k := by nlinarith [(hw k hk).1, (hw k hk).2]
      have h₁ := mul_le_mul_of_nonneg_right hh (hv k).1
      have h₂ := mul_le_mul_of_nonneg_left hw2 (mul_nonneg (sq_nonneg t) (hv k).1)
      nlinarith
    have hh := Finset.sum_le_sum hterm
    dsimp [m]
    simp only [Finset.sum_sub_distrib, sub_mul, Finset.mul_sum, mul_assoc] at hh ⊢
    simpa only [mul_assoc] using hh
  have heq (ω : ι → Bool) : Real.exp (t * ((∑ k ∈ S, w k * monomial (E k) ω) - m)) =
      Real.exp (-t * m) * Real.exp (t * ∑ k ∈ S, w k * monomial (E k) ω) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change expect p (fun ω ↦ Real.exp (t * ((∑ k ∈ S, w k * monomial (E k) ω) - m))) ≤ _
  simp_rw [heq]
  rw [expect_const_mul, expect_exp_disjoint_monomials p S E hE w t]
  calc
    _ ≤ Real.exp (-t * m) * Real.exp (∑ k ∈ S, (Real.exp (t * w k) - 1) * v k) :=
      mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp ((∑ k ∈ S, (Real.exp (t * w k) - 1) * v k) - t * m) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hexp

lemma exists_lt_of_expect_lt (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (F : (ι → Bool) → ℝ) (r : ℝ) (h : expect p F < r) : ∃ ω, F ω < r := by
  by_contra hh
  push_neg at hh
  have hb := expect_mono p hp (fun _ ↦ r) F hh
  rw [expect_const] at hb
  linarith

/-- A finite family of mean-scale MGF estimates has a simultaneous good
realization when the union-bound potential is strictly below one. -/
theorem exists_simultaneous_bound_with_potential (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset κ) (F : κ → (ι → Bool) → ℝ) (m : κ → ℝ) (V ε : ℝ)
    (hV : 0 < V) (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : ∀ k ∈ S, m k ≤ V)
    (hmgf : ∀ k ∈ S, ∀ t : ℝ, |t| ≤ 1 / 2 →
      expect p (fun ω ↦ Real.exp (t * (F k ω - m k))) ≤ Real.exp (2 * t ^ 2 * m k))
    (Ψ : (ι → Bool) → ℝ) (hΨ : ∀ ω, 0 ≤ Ψ ω)
    (hsmall : 2 * S.card * Real.exp (-ε ^ 2 * V / 8) + expect p Ψ < 1) :
    ∃ ω : ι → Bool, (∀ k ∈ S, |F k ω - m k| < ε * V) ∧ Ψ ω < 1 := by
  let t := ε / 4
  have ht : 0 < t := by dsimp [t]; positivity
  have htbound : |t| ≤ 1 / 2 := by rw [abs_of_pos ht]; dsimp [t]; linarith
  have hntbound : |-t| ≤ 1 / 2 := by simpa only [abs_neg] using htbound
  let P (ω : ι → Bool) : ℝ := ∑ k ∈ S,
    (Real.exp (t * (F k ω - m k - ε * V)) + Real.exp (-t * (F k ω - m k + ε * V)))
  have hterm (k : κ) (hk : k ∈ S) :
      expect p (fun ω ↦ Real.exp (t * (F k ω - m k - ε * V)) +
        Real.exp (-t * (F k ω - m k + ε * V))) ≤ 2 * Real.exp (-ε ^ 2 * V / 8) := by
    have hsplit₁ (ω : ι → Bool) : Real.exp (t * (F k ω - m k - ε * V)) =
        Real.exp (-t * ε * V) * Real.exp (t * (F k ω - m k)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hsplit₂ (ω : ι → Bool) : Real.exp (-t * (F k ω - m k + ε * V)) =
        Real.exp (-t * ε * V) * Real.exp (-t * (F k ω - m k)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [expect_add]
    simp_rw [hsplit₁, hsplit₂]
    rw [expect_const_mul, expect_const_mul]
    have h₁ := hmgf k hk t htbound
    have h₂ := hmgf k hk (-t) hntbound
    have hmono : Real.exp (2 * t ^ 2 * m k) ≤ Real.exp (2 * t ^ 2 * V) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hm k hk) (by positivity))
    have h₁' := mul_le_mul_of_nonneg_left (h₁.trans hmono) (Real.exp_pos (-t * ε * V)).le
    have h₂' := mul_le_mul_of_nonneg_left (show expect p (fun ω ↦ Real.exp (-t * (F k ω - m k))) ≤
        Real.exp (2 * t ^ 2 * V) by simpa only [neg_sq] using h₂.trans (by simpa only [neg_sq] using hmono))
      (Real.exp_pos (-t * ε * V)).le
    have he : Real.exp (-t * ε * V) * Real.exp (2 * t ^ 2 * V) = Real.exp (-ε ^ 2 * V / 8) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [t]
      ring
    rw [he] at h₁' h₂'
    linarith
  have hP : expect p P ≤ 2 * S.card * Real.exp (-ε ^ 2 * V / 8) := by
    change expect p (fun ω ↦ ∑ k ∈ S, _) ≤ _
    rw [expect_sum]
    have hh := Finset.sum_le_sum hterm
    simp only [Finset.sum_const, nsmul_eq_mul] at hh
    nlinarith
  have htotal : expect p (fun ω ↦ P ω + Ψ ω) < 1 := by
    rw [expect_add]
    linarith
  obtain ⟨ω, htω⟩ := exists_lt_of_expect_lt p hp (fun ω ↦ P ω + Ψ ω) 1 htotal
  have hPnon : 0 ≤ P ω := Finset.sum_nonneg (fun k hk ↦ by positivity)
  have hω : P ω < 1 := by linarith [hΨ ω]
  refine ⟨ω,fun k hk ↦ ?_,by linarith⟩
  have hle : Real.exp (t * (F k ω - m k - ε * V)) +
      Real.exp (-t * (F k ω - m k + ε * V)) ≤ P ω := by
    dsimp only [P]
    exact Finset.single_le_sum (f := fun j ↦
      Real.exp (t * (F j ω - m j - ε * V)) +
      Real.exp (-t * (F j ω - m j + ε * V))) (fun j hj ↦ by positivity) hk
  have h₁ : Real.exp (t * (F k ω - m k - ε * V)) < 1 := by
    linarith [Real.exp_pos (-t * (F k ω - m k + ε * V))]
  have h₂ : Real.exp (-t * (F k ω - m k + ε * V)) < 1 := by
    linarith [Real.exp_pos (t * (F k ω - m k - ε * V))]
  have he₁ := Real.exp_lt_one_iff.mp h₁
  have he₂ := Real.exp_lt_one_iff.mp h₂
  rw [abs_lt]
  constructor <;> nlinarith

theorem exists_simultaneous_bound (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset κ) (F : κ → (ι → Bool) → ℝ) (m : κ → ℝ) (V ε : ℝ)
    (hV : 0 < V) (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : ∀ k ∈ S, m k ≤ V)
    (hmgf : ∀ k ∈ S, ∀ t : ℝ, |t| ≤ 1 / 2 →
      expect p (fun ω ↦ Real.exp (t * (F k ω - m k))) ≤ Real.exp (2 * t ^ 2 * m k))
    (hsmall : 2 * S.card * Real.exp (-ε ^ 2 * V / 8) < 1) :
    ∃ ω : ι → Bool, ∀ k ∈ S, |F k ω - m k| < ε * V := by
  have hs : 2 * S.card * Real.exp (-ε ^ 2 * V / 8) + expect p (fun _ ↦ (0 : ℝ)) < 1 := by
    simpa only [expect_const,add_zero] using hsmall
  obtain ⟨ω,hω,_⟩ := exists_simultaneous_bound_with_potential p hp S F m V ε hV hε hε1 hm hmgf
    (fun _ ↦ 0) (fun _ ↦ le_rfl) hs
  exact ⟨ω,hω⟩

end Erdos66BernoulliConcentration
