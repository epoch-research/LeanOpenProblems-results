import Submission.FiniteSupportSchur

/-! The finite-support Schur argument with arbitrary row-dependent cutoffs. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma sum_range_ite_below (B L : ℕ) (hBL : B≤L) (h : ℕ → ℝ) :
    (∑ p ∈ range L, if p<B then h p else 0)=∑ p ∈ range B, h p := by
  rw [← sum_filter]
  congr 1
  ext p
  simp only [mem_filter,mem_range]
  omega

/-- Convergence against fixed sign tests implies convergence of the whole
row l1 norm. No relation between the row number and its cutoff is required. -/
theorem variable_cutoff_schur_of_sign_tests (f : ℕ → ℕ → ℝ) (B : ℕ → ℕ)
    (hweak : ∀ s : ℕ → ℝ, (∀ p, s p=1 ∨ s p= -1) →
      Tendsto (fun N => ∑ p ∈ range (B N), s p*f N p) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ p ∈ range (B N), |f N p|) atTop (𝓝 0) := by
  classical
  let e (N : ℕ) := ∑ j ∈ range (N+1), (B j+1)
  have he : StrictMono e := by
    apply strictMono_nat_of_lt_succ
    intro N
    dsimp only [e]
    rw [sum_range_succ (fun j => B j+1) (N+1)]
    omega
  have hBe (N : ℕ) : B N≤e N := by
    have h := single_le_sum (s := range (N+1)) (f := fun j => B j+1)
      (fun j _ => Nat.zero_le _) (mem_range.mpr (Nat.lt_succ_self N))
    change B N+1≤e N at h
    exact (Nat.le_succ _).trans h
  let g (n p : ℕ) : ℝ := Function.extend e
    (fun N => if p<B N then f N p else 0) (fun _ => 0) n
  have hg (N p : ℕ) : g (e N) p=if p<B N then f N p else 0 := by
    exact he.injective.extend_apply _ _ N
  have htest (N : ℕ) (s : ℕ → ℝ) :
      (∑ p ∈ range (e N), s p*g (e N) p)=∑ p ∈ range (B N), s p*f N p := by
    simp only [hg,mul_ite,mul_zero]
    exact sum_range_ite_below (B N) (e N) (hBe N) _
  have hn (N : ℕ) :
      (∑ p ∈ range (e N), |g (e N) p|)=∑ p ∈ range (B N), |f N p| := by
    simp only [hg,apply_ite,abs_zero]
    exact sum_range_ite_below (B N) (e N) (hBe N) _
  have hw : ∀ s : ℕ → ℝ, (∀ p, s p=1 ∨ s p= -1) →
      Tendsto (fun n => ∑ p ∈ range n, s p*g n p) atTop (𝓝 0) := by
    intro s hs
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨K,hK⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp (hweak s hs)) ε hε)
    filter_upwards [eventually_ge_atTop (e K)] with n hnK
    by_cases hx : ∃ N, e N=n
    · obtain ⟨N,rfl⟩ := hx
      rw [htest]
      exact hK N (he.le_iff_le.mp hnK)
    · have hz (p : ℕ) : g n p=0 := by
        exact Function.extend_apply' _ _ _ hx
      simpa only [hz,mul_zero,sum_const_zero,dist_self] using hε
  have h := (triangular_schur_of_sign_tests g hw).comp he.tendsto_atTop
  apply h.congr
  intro N
  exact hn N

#print axioms variable_cutoff_schur_of_sign_tests
end Erdos371.FiniteInformation
