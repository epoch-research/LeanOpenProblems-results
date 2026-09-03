import Submission.BinaryBlockTransferExplore
import Submission.CarryAveragingExplore
import Submission.NatPairAlgebraExplore

/-! Repeating one cyclic pattern gives a triangular integer profile.  The
estimate is uniform in the repetition length, but does not compare patterns
at different cyclic moduli. -/
namespace Erdos66RepeatedBlockProfile
open AdditiveCombinatorics Erdos66IntegerBlock Erdos66BinaryBlockTransfer
  Erdos66CarryAveraging Erdos66NatPairAlgebra
open scoped Classical

lemma interval_sumRep (K q : ℕ) :
    (sumRep (Finset.range K : Set ℕ) q : ℤ) = triangle K q := by
  rw [← pairs_self, pairs, Finset.product_eq_sprod]
  convert triangle_count K q using 2
  congr 1
  ext ab
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

lemma triangle_le (K : ℕ) (z : ℤ) : triangle K z ≤ K := by
  unfold triangle
  omega

lemma triangle_neg_one (K : ℕ) : triangle K (-1) = 0 := by
  unfold triangle
  omega

lemma triangle_zero (K : ℕ) (hK : 0 < K) : triangle K 0 = 1 := by
  unfold triangle
  omega

noncomputable def repeatedBlock (M : ℕ) [NeZero M] (B : Finset (ZMod M)) (K : ℕ) : Set ℕ :=
  binaryBlocks M B (Finset.range K : Set ℕ)

variable (M : ℕ) [NeZero M]

/-- The carry interpolates between neighboring triangular weights. -/
lemma repeated_block_formula (B : Finset (ZMod M)) (K q t : ℕ) (ht : t < M) :
    (sumRep (repeatedBlock M B K) (q*M+t) : ℝ) =
      (triangle K q : ℝ) * lower M B B t +
        (triangle K ((q : ℤ)-1) : ℝ) * upper M B B t := by
  by_cases hq : q = 0
  · subst q
    rw [Nat.zero_mul, Nat.zero_add, repeatedBlock, binary_block_formula_zero M _ _ _ ht]
    by_cases hK : K = 0
    · simp [hK, triangle]
    · have hK' : 0 < K := Nat.pos_of_ne_zero hK
      simp [hK', triangle_zero K hK', triangle_neg_one]
  · rw [repeatedBlock, binary_block_formula M _ _ q t (Nat.pos_of_ne_zero hq) ht]
    push_cast
    have he₁ : (sumRep (Finset.range K : Set ℕ) q : ℝ) = (triangle K q : ℝ) := by
      exact_mod_cast interval_sumRep K q
    have he₂ : (sumRep (Finset.range K : Set ℕ) (q-1) : ℝ) =
        (triangle K ((q : ℤ)-1) : ℝ) := by
      have hh := interval_sumRep K (q-1)
      rw [Nat.cast_sub (show 1 ≤ q by omega), Nat.cast_one] at hh
      exact_mod_cast hh
    simpa only [Finset.coe_range] using congrArg₂ (fun x y : ℝ ↦
      x * lower M B B t + y * upper M B B t) he₁ he₂

/-- A single-step carry error is independent of the repetition length. -/
theorem repeated_block_error (B : Finset (ZMod M)) (K q t : ℕ) (ht : t < M)
    (μ E : ℝ)
    (hB : |(((B.filter (fun a ↦ (t : ZMod M)-a ∈ B)).card : ℝ)-μ)| ≤ E) :
    |(sumRep (repeatedBlock M B K) (q*M+t) : ℝ)-μ*(triangle K q : ℝ)| ≤
      E*(triangle K q : ℝ)+μ+E := by
  let l : ℝ := lower M B B t
  let u : ℝ := upper M B B t
  let T : ℝ := triangle K q
  let T' : ℝ := triangle K ((q : ℤ)-1)
  have hl : 0 ≤ l := Nat.cast_nonneg _
  have hu : 0 ≤ u := Nat.cast_nonneg _
  have hT : 0 ≤ T := by
    dsimp [T]
    exact_mod_cast triangle_nonneg K q
  have hstep : |T'-T| ≤ 1 := by
    rw [abs_sub_comm]
    dsimp [T,T']
    exact_mod_cast triangle_step K q
  have hcount : |l+u-μ| ≤ E := by
    have hh := lower_add_upper M B B t
    dsimp [l,u]
    rw [← hh, Nat.cast_add] at hB
    exact hB
  have hupper : u ≤ μ+E := by
    have hh := (abs_le.mp hcount).2
    linarith
  have heq : (sumRep (repeatedBlock M B K) (q*M+t) : ℝ)-μ*T =
      T*(l+u-μ)+(T'-T)*u := by
    rw [repeated_block_formula M B K q t ht]
    dsimp [l,u,T,T']
    ring
  change |(sumRep (repeatedBlock M B K) (q*M+t) : ℝ)-μ*T| ≤ E*T+μ+E
  rw [heq]
  calc
    _ ≤ |T*(l+u-μ)|+|(T'-T)*u| := abs_add_le _ _
    _ = T * |l+u-μ|+|T'-T| * u := by rw [abs_mul,abs_mul,abs_of_nonneg hT,abs_of_nonneg hu]
    _ ≤ T*E+1*u := add_le_add (mul_le_mul_of_nonneg_left hcount hT)
        (mul_le_mul_of_nonneg_right hstep hu)
    _ ≤ E*T+μ+E := by linarith

/-- Global triangular approximation, including the first and last coarse
blocks.  No term proportional to the square of the repetition length occurs. -/
theorem repeated_block_uniform_error (B : Finset (ZMod M)) (K : ℕ) (μ E : ℝ)
    (hE : 0 ≤ E)
    (hB : ∀ z : ZMod M, |(((B.filter (fun a ↦ z-a ∈ B)).card : ℝ)-μ)| ≤ E)
    (n : ℕ) :
    |(sumRep (repeatedBlock M B K) n : ℝ)-μ*(triangle K (n/M : ℕ) : ℝ)| ≤
      (K : ℝ)*E+μ+E := by
  have hh := repeated_block_error M B K (n/M) (n%M) (Nat.mod_lt _ (NeZero.pos M))
    μ E (hB (n%M))
  rw [Nat.div_add_mod'] at hh
  have hT : (triangle K (n/M : ℕ) : ℝ) ≤ K := by exact_mod_cast triangle_le K (n/M)
  have hprod := mul_le_mul_of_nonneg_left hT hE
  exact hh.trans (by nlinarith)

end Erdos66RepeatedBlockProfile
