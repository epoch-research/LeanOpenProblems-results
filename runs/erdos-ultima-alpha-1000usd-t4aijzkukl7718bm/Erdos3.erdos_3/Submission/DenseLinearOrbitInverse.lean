import Submission.LinearOrbitCompression

/-! Density-form corollary of the lattice compression lemma. The approximation
error has the inverse-square interval-length scale needed for quadratic Weyl
inverse estimates. -/
namespace Erdos3DenseLinearOrbitInverse
open Finset Erdos3LinearOrbitCompression
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

/-- If at least N/R integer indices have fractional error <=E/N, a denominator
q<4R approximates the slope to error <=64 R^2 E(6E+1)/N^2. -/
theorem dense_linear_orbit_inverse (α : ℝ) (H : Finset ℕ) (z : ℕ → ℤ)
    {N R E : ℕ} (hR : 0 < R) (hN : 8*R*(6*E+1) ≤ N)
    (hH : H ⊆ range N) (hdensity : N ≤ R*H.card)
    (happrox : ∀ h ∈ H, |α*(h : ℝ)-(z h : ℝ)| ≤ (E : ℝ)/(N : ℝ)) :
    ∃ q : ℕ, ∃ b : ℤ, 0 < q ∧ q < 4*R ∧
      |α*(q : ℝ)-(b : ℝ)| ≤ 64*(R : ℝ)^2*(E : ℝ)*(6*(E : ℝ)+1)/(N : ℝ)^2 := by
  let K := 6*E+1
  let D := 4*R*K
  let m := N/D
  have hK : 0 < K := by dsimp only [K]; omega
  have hD : 0 < D := Nat.mul_pos (Nat.mul_pos (by decide) hR) hK
  have hD2 : 2*D ≤ N := by
    change 8*R*K ≤ N at hN
    dsimp only [D]
    nlinarith only [hN]
  have hN0 : 0 < N := by omega
  have hm : 0 < m := Nat.div_pos (by omega : D ≤ N) hD
  have hcard8 : 8 ≤ H.card := by
    have hR8 : R*8 ≤ R*H.card := by
      have hK1 : 1 ≤ K := hK
      have hh := Nat.mul_le_mul_left (8*R) hK1
      change 8*R*K ≤ N at hN
      nlinarith only [hh,hN,hdensity]
    exact Nat.le_of_mul_le_mul_left hR8 hR
  have hQ0 : 0 < 4*R := Nat.mul_pos (by decide) hR
  have hQN : 4*R ≤ N := by
    have hK1 : 1 ≤ K := hK
    have hh := Nat.mul_le_mul_left (4*R) hK1
    dsimp only [D] at hD2
    nlinarith only [hh,hD2]
  have hshort : N/(4*R)+1 < H.card := by
    have hd := Nat.mul_div_le N (4*R)
    have hx : R*(4*(N/(4*R))) ≤ R*H.card := by nlinarith only [hd,hdensity]
    have hh := Nat.le_of_mul_le_mul_left hx hR
    omega
  have hmN : D*m ≤ N := Nat.mul_div_le N D
  have hwide : (6*E+1)*m < H.card := by
    have hh : R*(4*K*m) ≤ R*H.card := by
      dsimp only [D] at hmN
      nlinarith only [hmN,hdensity]
    have he := Nat.le_of_mul_le_mul_left hh hR
    change K*m < H.card
    rw [Nat.mul_assoc] at he
    omega
  have hNm : N ≤ 8*R*K*m := by
    have ht := Nat.lt_mul_div_succ N hD
    change N < D*(m+1) at ht
    have he : m+1 ≤ 2*m := by omega
    have hmul := Nat.mul_le_mul_left D he
    dsimp only [D] at ht hmul
    nlinarith only [ht,hmul]
  obtain ⟨q,b,hq,hqb,he⟩ := compress_linear_orbit α H z hN0 hQ0 hQN hm hH hshort hwide happrox
  refine ⟨q,b,hq,hqb,he.trans ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hNmR : (N : ℝ) ≤ 8*(R : ℝ)*(6*(E : ℝ)+1)*(m : ℝ) := by
    exact_mod_cast hNm
  have hnonneg : 0 ≤ 8*(R : ℝ)*(E : ℝ) := by positivity
  have hbound := mul_le_mul_of_nonneg_left hNmR hnonneg
  push_cast
  apply (div_le_div_iff₀ (mul_pos hNr hmr) (sq_pos_of_pos hNr)).mpr
  have hh := mul_le_mul_of_nonneg_left hbound hNr.le
  nlinarith only [hh]

#print axioms dense_linear_orbit_inverse
end Erdos3DenseLinearOrbitInverse
