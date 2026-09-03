import Submission.LambertUniformRawNonvanishing
import Submission.LambertBoundaryForms

/-!\nPositive definite Toeplitz matrices from rapidly decaying raw tails.
This supplies nonvanishing with rational boundaries, not small integer forms.
-/

namespace TailDominantToeplitz

open Finset Matrix

/-- An approximate maximum of the exponentially normalized tail. -/
lemma exists_geometric_peak (f : ℕ → ℝ) (H : ℕ)
    (hb : ∃ C : ℝ, ∀ n ≥ H, (6 : ℝ)^n * |f n| ≤ C)
    (hne : ∃ n ≥ H, f n ≠ 0) :
    ∃ n ≥ H, f n ≠ 0 ∧ ∀ k : ℕ, |f (n+k)| ≤ 2*|f n|/(6 : ℝ)^k := by
  let S : Set ℝ := {x | ∃ n ≥ H, x = (6 : ℝ)^n * |f n|}
  obtain ⟨u, hu, hfu⟩ := hne
  have hmem : (6 : ℝ)^u * |f u| ∈ S := ⟨u, hu, rfl⟩
  have hs : S.Nonempty := ⟨_, hmem⟩
  have hbd : BddAbove S := by
    obtain ⟨C, hC⟩ := hb
    refine ⟨C, ?_⟩
    rintro x ⟨n, hn, rfl⟩
    exact hC n hn
  have hpos : 0 < sSup S :=
    (mul_pos (by positivity) (abs_pos.mpr hfu)).trans_le (le_csSup hbd hmem)
  obtain ⟨x, ⟨n, hn, rfl⟩, hx⟩ := exists_lt_of_lt_csSup hs
    (show sSup S / 2 < sSup S by linarith)
  have hfn : f n ≠ 0 := by
    intro he
    rw [he, abs_zero, mul_zero] at hx
    linarith
  refine ⟨n, hn, hfn, fun k => ?_⟩
  have ht : (6 : ℝ)^(n+k)*|f (n+k)| ≤ sSup S :=
    le_csSup hbd ⟨n+k, by omega, rfl⟩
  rw [pow_add] at ht
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 6^k)).mpr
  have hp : (0 : ℝ) < 6^n := by positivity
  nlinarith

lemma summable_int_geometric : Summable (fun z : ℤ => (1/6 : ℝ)^z.natAbs) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor <;> simpa using
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/6 : ℝ)‖ < 1))

lemma tsum_int_geometric : (∑' z : ℤ, (1/6 : ℝ)^z.natAbs) = 7/5 := by
  have hs := summable_geometric_of_norm_lt_one (by norm_num : ‖(1/6 : ℝ)‖ < 1)
  have ht := tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/6 : ℝ)‖ < 1)
  have he (n : ℕ) : (-(↑n + 1 : ℤ)).natAbs = n+1 := by
    rw [Int.natAbs_neg, show (↑n + 1 : ℤ) = ↑(n+1) by omega, Int.natAbs_natCast]
  rw [tsum_of_nat_of_neg_add_one (by simpa only [Int.natAbs_natCast] using hs)
    (by simpa only [he] using (summable_nat_add_iff 1).mpr hs)]
  simp only [Int.natAbs_natCast, he, pow_succ, tsum_mul_right, ht]
  norm_num

lemma geometric_row_bound (D : ℕ) (i : Fin D) :
    (∑ j ∈ univ.erase i, (1/6 : ℝ)^((j : ℤ)-(i : ℤ)).natAbs) ≤ 2/5 := by
  classical
  let e : Fin D → ℤ := fun j => (j : ℤ)-(i : ℤ)
  have he : Function.Injective e := by
    intro j k h
    apply Fin.ext
    dsimp [e] at h
    omega
  have hsum : (∑ j : Fin D, (1/6 : ℝ)^(e j).natAbs) ≤ 7/5 := by
    have heq := sum_image (f := fun z : ℤ => (1/6 : ℝ)^z.natAbs)
      (s := (univ : Finset (Fin D))) (fun j _ k _ h => he h)
    rw [← heq]
    exact (summable_int_geometric.sum_le_tsum _ (fun _ _ => by positivity)).trans_eq
      tsum_int_geometric
  rw [sum_erase_eq_sub (mem_univ i)]
  change (∑ j : Fin D, (1/6 : ℝ)^(e j).natAbs) - (1/6 : ℝ)^((i : ℤ)-(i : ℤ)).natAbs ≤ _
  simp only [sub_self, Int.natAbs_zero, pow_zero]
  linarith

/-- Real symmetric strict diagonal dominance with positive diagonals. -/
lemma posDef_of_strict_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.IsHermitian)
    (hd : ∀ i, ∑ j ∈ univ.erase i, ‖M i j‖ < M i i) : M.PosDef := by
  apply hM.posDef_iff_eigenvalues_pos.mpr
  intro j
  have hev : Module.End.HasEigenvalue (Matrix.toLin' M) (hM.eigenvalues j) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
      (x := (hM.eigenvectorBasis j).ofLp)
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · simpa only [Matrix.toLin'_apply, RCLike.real_smul_eq_coe_smul] using
        hM.mulVec_eigenvectorBasis j
    · intro he
      have hz : hM.eigenvectorBasis j = 0 := (WithLp.ofLp_eq_zero 2).mp he
      have := hM.eigenvectorBasis.norm_eq_one j
      rw [hz, norm_zero] at this
      norm_num at this
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hev
  rw [Metric.mem_closedBall, Real.dist_eq] at hi
  have hl := (abs_le.mp hi).1
  linarith [hd i]

/-- A sign-normalized reflected geometric peak is positive definite at
EVERY finite matrix size. No boundary-integrality assertion is included. -/
theorem peak_toeplitz_posDef (f : ℕ → ℝ) (H D : ℕ) (s : ℝ)
    (hs : |s| = 1) (hsgn : s*f H = |f H|) (hn : f H ≠ 0)
    (hb : ∀ k : ℕ, |f (H+k)| ≤ 2*|f H|/(6 : ℝ)^k) :
    Matrix.PosDef (fun i j : Fin D => s*f (H+((j : ℤ)-(i : ℤ)).natAbs)) := by
  classical
  let M : Matrix (Fin D) (Fin D) ℝ := fun i j => s*f (H+((j : ℤ)-(i : ℤ)).natAbs)
  have hM : M.IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, M]
    congr 2
    rw [← Int.natAbs_neg, neg_sub]
  apply posDef_of_strict_diagonal M hM
  intro i
  have ha : 0 < |f H| := abs_pos.mpr hn
  calc
    (∑ j ∈ univ.erase i, ‖M i j‖) ≤
        ∑ j ∈ univ.erase i, 2*|f H| *(1/6 : ℝ)^((j : ℤ)-(i : ℤ)).natAbs := by
      apply sum_le_sum
      intro j _
      simp only [M, Real.norm_eq_abs, abs_mul, hs, one_mul]
      simpa only [div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow] using hb ((j : ℤ)-(i : ℤ)).natAbs
    _ = 2*|f H| *(∑ j ∈ univ.erase i, (1/6 : ℝ)^((j : ℤ)-(i : ℤ)).natAbs) := by rw [mul_sum]
    _ ≤ 2*|f H| *(2/5) := mul_le_mul_of_nonneg_left (geometric_row_bound D i) (by positivity)
    _ < |f H| := by linarith
    _ = M i i := by simp [M, hsgn]

open LambertUniformRawNonvanishing Erdos68Development

lemma six_pow_bound (K n : ℕ) (hK : 35 ≤ K) :
    (6 : ℝ)^n ≤ 6*((K+1 : ℕ) : ℝ)^(n/2) := by
  have h36 : (36 : ℝ) ≤ (K+1 : ℕ) := by exact_mod_cast (by omega : 36 ≤ K+1)
  have he : n = 2*(n/2)+n%2 := by omega
  calc
    (6 : ℝ)^n = (36 : ℝ)^(n/2)*6^(n%2) := by
      conv_lhs => rw [he]
      rw [pow_add, pow_mul]
      norm_num
    _ ≤ ((K+1 : ℕ) : ℝ)^(n/2)*6 := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by norm_num) h36 _
      · exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 6) (by omega : n%2 ≤ 1)).trans_eq (by simp)
      · positivity
      · positivity
    _ = _ := by ring

lemma raw_normalized_bound (K n : ℕ) (hK : 35 ≤ K) (hn : 4 ≤ n) :
    (6 : ℝ)^n * |rawTail K n| ≤ 6*(K+1)*2^(K+1) := by
  have hb := LambertTotalBounds.range_operator_explicit_bound K n hn
  change |rawTail K n| ≤ _ at hb
  have he : ((K+1 : ℕ) : ℝ)^(n/2) =
      ((K+1 : ℕ) : ℝ)^(n/2-1)*((K+1 : ℕ) : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    _ ≤ (6*((K+1 : ℕ) : ℝ)^(n/2)) *
        (2^(K+1)/((K+1 : ℕ) : ℝ)^(n/2-1)) :=
      mul_le_mul (six_pow_bound K n hK) hb (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [he]
      have hp : ((K+1 : ℕ) : ℝ)^(n/2-1) ≠ 0 := by positivity
      push_cast
      field_simp

/-- Arbitrarily late raw tails are geometric peaks. -/
theorem raw_geometric_peaks (K H : ℕ) (hK : 35 ≤ K) :
    ∃ n ≥ H, rawTail K n ≠ 0 ∧
      ∀ k : ℕ, |rawTail K (n+k)| ≤ 2*|rawTail K n|/(6 : ℝ)^k := by
  have hbound : ∃ C : ℝ, ∀ n ≥ max H 4, (6 : ℝ)^n * |rawTail K n| ≤ C :=
    ⟨6*(K+1)*2^(K+1), fun n hn =>
      raw_normalized_bound K n hK ((le_max_right _ _).trans hn)⟩
  have hnonzero : ∃ n ≥ max H 4, rawTail K n ≠ 0 := by
    let L := (K+3)*(2*((K+2).log2+1)+130)
    obtain ⟨n, hn, _, hne⟩ := raw_nonzero_in_every_window K (max (max H 4) L)
      (by omega) (le_max_right _ _)
    exact ⟨n, (le_max_left _ _).trans hn, hne⟩
  obtain ⟨n, hn, hne, hb⟩ := exists_geometric_peak (rawTail K) (max H 4) hbound hnonzero
  exact ⟨n, (le_max_left _ _).trans hn, hne, hb⟩

/-- A sign and starting index work simultaneously for all matrix sizes.
The entries are affine in the exact target, with integer retained coefficient
and rational boundary. No useful integer normalization bound is proved. -/
theorem raw_positive_toeplitz_family (K H : ℕ) (hK : 35 ≤ K) :
    ∃ n ≥ H, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ D : ℕ,
      Matrix.PosDef (fun i j : Fin D =>
        ((s * LambertBoundaryForms.coefficient (List.range' 2 K) : ℤ) : ℝ) *
          (∑' k : ℕ, term k) -
        ((s : ℚ) * LambertBoundaryClearing.boundary (List.range' 2 K)
          (n+((j : ℤ)-(i : ℤ)).natAbs) : ℚ)) := by
  obtain ⟨n, hn, hne, hb⟩ := raw_geometric_peaks K H hK
  have hex : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ |(s : ℝ)| = 1 ∧
      (s : ℝ)*rawTail K n = |rawTail K n| := by
    by_cases hpos : 0 < rawTail K n
    · exact ⟨1, Or.inl rfl, by norm_num, by simp [abs_of_pos hpos]⟩
    · have hneg : rawTail K n < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hne
      exact ⟨-1, Or.inr rfl, by norm_num, by simp [abs_of_neg hneg]⟩
  obtain ⟨s, hs, habs, hsign⟩ := hex
  refine ⟨n, hn, s, hs, fun D => ?_⟩
  have hm := peak_toeplitz_posDef (rawTail K) n D (s : ℝ) habs hsign hne hb
  convert hm using 1
  ext i j
  rw [rawTail, LambertBoundaryForms.form_identity]
  push_cast
  ring

#print axioms exists_geometric_peak
#print axioms peak_toeplitz_posDef
#print axioms raw_geometric_peaks
#print axioms raw_positive_toeplitz_family

end TailDominantToeplitz
