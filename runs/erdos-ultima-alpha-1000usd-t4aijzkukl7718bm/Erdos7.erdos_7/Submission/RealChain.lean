import FormalConjecturesUtil

/-! Real scalar chain compression, for use with exact fiber retention. -/

namespace Erdos7RealChain
open scoped BigOperators
set_option maxHeartbeats 1500000

/-- The increasing-increments property of a convex scalar function. -/
def IncreasingIncrements (φ : ℝ → ℝ) : Prop :=
  ∀ x y d, x ≤ y → 0 ≤ d → φ (x+d)-φ x ≤ φ (y+d)-φ y

lemma convex_increasingIncrements (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) :
    IncreasingIncrements φ := by
  intro x y d hxy hd
  by_cases hzero : y-x+d = 0
  · have hyx : y = x := by linarith
    have hd0 : d = 0 := by linarith
    simp [hyx, hd0]
  have hpos : 0 < y-x+d := lt_of_le_of_ne (by linarith) (Ne.symm hzero)
  let a := d/(y-x+d)
  let b := (y-x)/(y-x+d)
  have ha : 0 ≤ a := div_nonneg hd hpos.le
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hxy) hpos.le
  have hab : a+b = 1 := by dsimp [a,b]; field_simp; ring
  have heq1 : a*(y+d)+b*x = x+d := by dsimp [a,b]; field_simp; ring
  have heq2 : b*(y+d)+a*x = y := by dsimp [a,b]; field_simp; ring
  have h1 := hφ.2 (Set.mem_univ (y+d)) (Set.mem_univ x) ha hb hab
  have h2 := hφ.2 (Set.mem_univ (y+d)) (Set.mem_univ x) hb ha (by linarith : b+a = 1)
  simp only [smul_eq_mul] at h1 h2
  rw [heq1] at h1
  rw [heq2] at h2
  have heq3 : (a*φ (y+d)+b*φ x)+(b*φ (y+d)+a*φ x) = φ (y+d)+φ x := by
    calc
      _ = (a+b)*φ (y+d)+(a+b)*φ x := by ring
      _ = _ := by rw [hab]; ring
  linarith

noncomputable def prefixWeight (w : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, w i
noncomputable def selectedWeight (w : ℕ → ℝ) (b : ℕ → Bool) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, if b i then w i else 0
noncomputable def chainIncrement (φ : ℝ → ℝ) (a : ℝ) (w : ℕ → ℝ) (i : ℕ) : ℝ :=
  φ (a+prefixWeight w (i+1))-φ (a+prefixWeight w i)

lemma convex_chord_majorant (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (a s W : ℝ) (hs : 0 ≤ s) (hsW : s ≤ W) :
    φ (a+s) ≤ φ a + (φ (a+W)-φ a)/W*s := by
  by_cases hW : W = 0
  · have hs0 : s = 0 := by linarith
    simp [hW, hs0]
  have hWp : 0 < W := lt_of_le_of_ne (hs.trans hsW) (Ne.symm hW)
  have hu : 0 ≤ s/W := div_nonneg hs hWp.le
  have hv : 0 ≤ 1-s/W := by have := (div_le_one hWp).mpr hsW; linarith
  have hh := hφ.2 (Set.mem_univ (a+W)) (Set.mem_univ a) hu hv (by ring : s/W+(1-s/W)=1)
  simp only [smul_eq_mul] at hh
  have hx : s/W*(a+W)+(1-s/W)*a = a+s := by field_simp; ring
  rw [hx] at hh
  convert hh using 1 <;> ring

/-- A continuous version of the Boolean-chain majorant. -/
theorem bounded_chain_majorant (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (a : ℝ) (W s : ℕ → ℝ) (R : ℕ)
    (hs : ∀ j<R, 0 ≤ s j) (hsW : ∀ j<R, s j ≤ W j) :
    φ (a+prefixWeight s R) ≤ φ a +
      ∑ j ∈ Finset.range R, chainIncrement φ a W j / W j * s j := by
  induction R with
  | zero => simp [prefixWeight]
  | succ R ih =>
    have hs0 : ∀ j<R, 0 ≤ s j := fun j hj => hs j (by omega)
    have hsW0 : ∀ j<R, s j ≤ W j := fun j hj => hsW j (by omega)
    have hprev : prefixWeight s R ≤ prefixWeight W R :=
      Finset.sum_le_sum (fun j hj => hsW0 j (Finset.mem_range.mp hj))
    have hincr := convex_increasingIncrements φ hφ
      (a+prefixWeight s R) (a+prefixWeight W R) (s R) (by linarith) (hs R (by omega))
    have hchord := convex_chord_majorant φ hφ (a+prefixWeight W R) (s R) (W R)
      (hs R (by omega)) (hsW R (by omega))
    have hih := ih hs0 hsW0
    rw [Finset.sum_range_succ]
    have heq : prefixWeight s (R+1) = prefixWeight s R+s R := Finset.sum_range_succ _ _
    have heq' : chainIncrement φ a W R =
        φ (a+prefixWeight W R+W R)-φ (a+prefixWeight W R) := by
      simp only [chainIncrement, prefixWeight, Finset.sum_range_succ, add_assoc]
    rw [heq, heq']
    simp only [add_assoc] at hincr hchord ⊢
    linarith

lemma chain_summation_by_parts (f q : ℕ → ℝ) (n : ℕ) :
    f 0 + ∑ i ∈ Finset.range n, q i * (f (i+1)-f i) =
      (1-q 0)*f 0 + ∑ i ∈ Finset.range n, (q i-q (i+1))*f (i+1) + q n*f n := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith



end Erdos7RealChain
