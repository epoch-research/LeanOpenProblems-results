import Submission.MovingPrimeBlockVariance
import Submission.CountableBandDensity
import Submission.SquarefreeColoringReduction

/-!
Positive-density sources satisfying countably many quantitatively bounded
prime-score bands. This is a source construction, not a cube-Sidon theorem.
-/
namespace Erdos1206.PrimeBlockBandDensity
open Finset PrimeBlockVariance MovingPrimeBlockVariance
open scoped Classical

noncomputable def energy (P : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  (∑ p ∈ P, w p^2/p)+4

lemma energy_pos (P : Finset ℕ) (w : ℕ → ℝ) : 0 < energy P w := by
  dsimp [energy]
  positivity

/-- The single K depends on the source, not on the prime blocks. The price
for the j-th block grows geometrically, but only linearly in its variance. -/
theorem exists_good_bands (S : Set ℕ) (hS : 0 < S.lowerDensity)
    (hpos : ∀ n ∈ S, 0 < n) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ),
      (∀ j p, p ∈ P j → p.Prime) → (∀ j p, p ∈ P j → |w j p| ≤ 1) →
      ∃ A : Set ℕ, A ⊆ S ∧ 0 < A.lowerDensity ∧
        ∀ n ∈ A, ∀ j : ℕ,
          (primeSum (P j) (w j) n-movingMean (P j) (w j) n)^2 ≤
            K*2^j*energy (P j) (w j) := by
  obtain ⟨δ,hδ,C,hpre⟩ := prefix_bound_of_positive_lowerDensity hS
  let K : ℝ := 48/δ
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro P w hP hw
  let c : ℕ → ℝ := fun j => δ/(4*2^j)
  have hc (j : ℕ) : 0 < c j := by dsimp [c]; positivity
  have hgeo := (hasSum_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)| < 1)).mul_left (δ/4)
  have hcgeo (j : ℕ) : (δ/4)*(1/2:ℝ)^j=c j := by
    dsimp [c]
    simp only [div_pow,one_pow]
    ring
  have hcs : HasSum c (δ/2) := by
    have hh := hgeo.congr_fun (fun j => (hcgeo j).symm)
    convert hh using 1; ring
  let R : ℕ → ℝ := fun j => Real.sqrt (12*energy (P j) (w j)/c j)
  have hR (j : ℕ) : 0 < R j := by
    dsimp [R]
    apply Real.sqrt_pos.mpr
    exact div_pos (mul_pos (by norm_num) (energy_pos _ _)) (hc j)
  have hR2 (j : ℕ) : (R j)^2=12*energy (P j) (w j)/c j := by
    apply Real.sq_sqrt
    exact (div_pos (mul_pos (by norm_num) (energy_pos _ _)) (hc j)).le
  let f : ℕ → ℕ → ℝ := fun j n =>
    (primeSum (P j) (w j) n-movingMean (P j) (w j) n)/R j
  have hmoment (j N : ℕ) : (∑ n ∈ Icc 1 N, (f j n)^2) ≤ (N:ℝ)*c j := by
    have hh := moving_variance_le N (P j) (w j) (hP j) (hw j)
    change _ ≤ 12*(N:ℝ)*energy (P j) (w j) at hh
    dsimp only [f]
    simp_rw [div_pow]
    rw [←sum_div]
    apply (div_le_iff₀ (sq_pos_of_pos (hR j))).mpr
    rw [hR2]
    have he : (N:ℝ)*c j*(12*energy (P j) (w j)/c j)=12*N*energy (P j) (w j) := by
      field_simp [(hc j).ne']
    rwa [he]
  let A : Set ℕ := {n | n ∈ S ∧ ∀ j, |f j n| ≤ 1}
  have hA : 0 < A.lowerDensity := CountableBandDensity.lowerDensity_pos_of_prefix
    S f c hpos hpre (fun j => (hc j).le) hcs.summable hmoment (by rw [hcs.tsum_eq]; linarith)
  refine ⟨A,fun _ h => h.1,hA,fun n hn j => ?_⟩
  have hfn := hn.2 j
  have hab : |primeSum (P j) (w j) n-movingMean (P j) (w j) n| ≤ R j := by
    apply (div_le_one (hR j)).mp
    simpa only [f,abs_div,abs_of_pos (hR j)] using hfn
  have hs := (sq_le_sq₀ (abs_nonneg _) (hR j).le).mpr hab
  rw [sq_abs,hR2] at hs
  have he : 12*energy (P j) (w j)/c j=K*2^j*energy (P j) (w j) := by
    dsimp [c,K]
    field_simp
    ring
  rwa [he] at hs

/-- In particular, all the controlled-score roots may be kept squarefree.
No Sidon property of this source is asserted. -/
theorem exists_squarefree_good_bands :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ),
      (∀ j p, p ∈ P j → p.Prime) → (∀ j p, p ∈ P j → |w j p| ≤ 1) →
      ∃ A : Set ℕ, (∀ n ∈ A, Squarefree n) ∧ 0 < A.lowerDensity ∧
        ∀ n ∈ A, ∀ j : ℕ,
          (primeSum (P j) (w j) n-movingMean (P j) (w j) n)^2 ≤
            K*2^j*energy (P j) (w j) := by
  exact exists_good_bands {n : ℕ | Squarefree n} squarefree_lowerDensity_pos
    (fun n hn => Nat.pos_of_ne_zero hn.ne_zero)

#print axioms exists_good_bands
#print axioms exists_squarefree_good_bands
end Erdos1206.PrimeBlockBandDensity
