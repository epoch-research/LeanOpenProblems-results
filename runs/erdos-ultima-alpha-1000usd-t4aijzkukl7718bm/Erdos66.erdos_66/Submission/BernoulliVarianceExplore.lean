import Submission.SummedBernoulliBoundsExplore

/-! Variance-sensitive finite Bernoulli estimates. These supply a sufficient
selection criterion, not a construction settling Erdos 66. -/
namespace Erdos66BernoulliVariance
open Erdos66FiniteBernoulli Erdos66BernoulliConcentration
  Erdos66SummedBernoulliBounds
open scoped Classical
variable {ι κ : Type*} [Fintype ι]
set_option maxHeartbeats 1600000

lemma scalar_centered_mgf (u s : ℝ) (hu : 0 ≤ u ∧ u ≤ 1) (hs : |s| ≤ 1) :
    Real.exp (-s*u)*(1+(Real.exp s-1)*u) ≤ Real.exp (s^2*u*(1-u)) := by
  have h₀ : |-s*u| ≤ 1 := by
    rw [abs_mul,abs_neg,abs_of_nonneg hu.1]
    exact (mul_le_mul hs hu.2 hu.1 (by norm_num)).trans_eq (by ring)
  have h₁ : |s*(1-u)| ≤ 1 := by
    rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr hu.2)]
    exact (mul_le_mul hs (show 1-u ≤ 1 by linarith) (by linarith) (by norm_num)).trans_eq (by ring)
  have he₀ := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le h₀)).2
  have he₁ := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le h₁)).2
  have hb₀ := mul_le_mul_of_nonneg_left he₀ (show 0 ≤ 1-u by linarith)
  have hb₁ := mul_le_mul_of_nonneg_left he₁ hu.1
  have hid : Real.exp (-s*u)*(1+(Real.exp s-1)*u)=
      (1-u)*Real.exp (-s*u)+u*Real.exp (s*(1-u)) := by
    have he : Real.exp (s*(1-u))=Real.exp s*Real.exp (-s*u) := by
      rw [←Real.exp_add]; congr 1; ring
    rw [he]; ring
  rw [hid]
  calc
    _ ≤ 1+s^2*u*(1-u) := by nlinarith only [hb₀,hb₁]
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (s^2*u*(1-u))

/-- The variance proxy vanishes for a deterministic monomial, unlike its mean. -/
theorem centered_mgf_variance (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset κ) (E : κ → Finset ι)
    (hE : (S : Set κ).Pairwise (fun i j ↦ Disjoint (E i) (E j)))
    (w : κ → ℝ) (hw : ∀ k∈S, 0 ≤ w k ∧ w k ≤ 2) (t : ℝ) (ht : |t| ≤ 1/2) :
    expect p (fun ω ↦ Real.exp (t*((∑ k∈S, w k*monomial (E k) ω)-
      ∑ k∈S, w k*∏ i∈E k, p i))) ≤
      Real.exp (2*t^2*(∑ k∈S, w k*(∏ i∈E k, p i)*(1-∏ i∈E k, p i))) := by
  let u : κ → ℝ := fun k ↦ ∏ i∈E k, p i
  have hu (k : κ) : 0 ≤ u k ∧ u k ≤ 1 := product_probability_bounds p hp (E k)
  have hid (ω : ι → Bool) :
      Real.exp (t*((∑ k∈S, w k*monomial (E k) ω)-∑ k∈S, w k*u k))=
      Real.exp (-t*(∑ k∈S, w k*u k))*Real.exp (t*(∑ k∈S, w k*monomial (E k) ω)) := by
    rw [←Real.exp_add]; congr 1; ring
  change expect p (fun ω ↦ Real.exp (t*((∑ k∈S, w k*monomial (E k) ω)-
    ∑ k∈S, w k*u k))) ≤ _
  simp_rw [hid]
  rw [expect_const_mul,expect_exp_disjoint_monomials p S E hE w t]
  have hprod : Real.exp (-t*(∑ k∈S, w k*u k))=
      ∏ k∈S, Real.exp (-t*w k*u k) := by
    rw [Finset.mul_sum,Real.exp_sum]
    simp only [mul_assoc]
  rw [hprod,←Finset.prod_mul_distrib]
  calc
    _ ≤ ∏ k∈S, Real.exp ((t*w k)^2*u k*(1-u k)) := by
      apply Finset.prod_le_prod
      · intro k hk
        apply mul_nonneg (Real.exp_pos _).le
        have hh := mul_nonneg (Real.exp_pos (t*w k)).le (hu k).1
        nlinarith [(hu k).1,(hu k).2]
      · intro k hk
        have htw : |t*w k| ≤ 1 := by
          rw [abs_mul,abs_of_nonneg (hw k hk).1]
          nlinarith [mul_le_mul ht (hw k hk).2 (hw k hk).1 (by norm_num : (0:ℝ) ≤ 1/2)]
        simpa only [neg_mul] using scalar_centered_mgf (u k) (t*w k) (hu k) htw
    _ ≤ _ := by
      rw [←Real.exp_sum]
      apply Real.exp_le_exp.mpr
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      have hw₂ : (w k)^2 ≤ 2*w k := by nlinarith [(hw k hk).1,(hw k hk).2]
      have hh := mul_le_mul_of_nonneg_right hw₂
        (mul_nonneg (sq_nonneg t) (mul_nonneg (hu k).1 (sub_nonneg.mpr (hu k).2)))
      dsimp only [u] at hh ⊢
      nlinarith only [hh]

/-- A separate variance proxy can be substituted into the existing summed-tail
selection theorem without charging the deterministic part of the mean. -/
theorem exists_summed_variance_bound (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset κ) (F : κ → (ι → Bool) → ℝ) (m V : κ → ℝ) (ε : ℝ)
    (hε : 0<ε) (hε1 : ε ≤ 1)
    (hmgf : ∀ k∈S, ∀ t : ℝ, |t| ≤ 1/2 →
      expect p (fun ω ↦ Real.exp (t*(F k ω-m k))) ≤ Real.exp (2*t^2*V k))
    (hsmall : (∑ k∈S, 2*Real.exp (-ε^2*V k/8))<1) :
    ∃ ω, 0<weight p ω ∧ ∀ k∈S, |F k ω-m k|<ε*V k := by
  obtain ⟨ω,hw,hω⟩ := exists_summed_bound p hp S
    (fun k ω ↦ F k ω-m k+V k) V V ε hε hε1 (fun _ _ ↦ le_rfl)
    (fun k hk t ht ↦ by simpa only [add_sub_cancel_right] using hmgf k hk t ht) hsmall
  exact ⟨ω,hw,fun k hk ↦ by simpa only [add_sub_cancel_right] using hω k hk⟩

end Erdos66BernoulliVariance
