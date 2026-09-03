import Submission.FullMovingBandDensity
import Submission.RadicalSourceDensity

/-! Short moving bands of finite-square-energy prime scores contain a
positive-lower-density set of squarefree integers, for a suitable shift. -/
namespace Erdos1206.SquarefreeMovingBandDensity
open FullPrimeScoreVariance PowerWindowMeanOscillation QuadraticPrimeMoments
  RadicalSourceDensity UniqueFactorizationMonoid PositiveDensityTransfer
open scoped Classical

lemma primeScore_radical (w : ℕ → ℝ) (n : ℕ) : primeScore w (radical n)=primeScore w n := by
  simp only [primeScore,nat_primeFactors_radical]

/-- This transfers a positive-density full moving band to a slightly wider
squarefree band. Radicalization is used only for scores, not for cube identities. -/
theorem exists_squarefree_band (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ => if p.Prime then w p^2/p else 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ,0 < ({n : ℕ | Squarefree n ∧ |deviation w n-μ| < ε} : Set ℕ).lowerDensity := by
  obtain ⟨μ,hA⟩ := FullMovingBandDensity.exists_band w hs (half_pos hε)
  let A : Set ℕ := {n | 0 < n ∧ |deviation w n-μ| < ε/2}
  obtain ⟨K,hK,S,hSA,hS,hbound⟩ := exists_bounded_source (A := A) hA
  obtain ⟨H,hH⟩ := center_power_oscillation w hs (half_pos hε)
  let L := max H (K^4+1)
  let T := S ∩ Set.Ici (K^2*L)
  have hT : 0 < T.lowerDensity := trim hS (K^2*L)
  have hK2 : 0 < K^2 := pow_pos hK 2
  have hrad : 0 < (radical '' T).lowerDensity :=
    bounded_image_density hT hK2 (fun n hn => hbound n hn.1)
  refine ⟨μ,superset hrad ?_⟩
  rintro m ⟨n,hn,rfl⟩
  obtain ⟨hn0,hnK⟩ := hbound n hn.1
  have hrL : L ≤ radical n := Nat.le_of_mul_le_mul_left (hn.2.trans hnK) hK2
  have hrH : H ≤ radical n := (le_max_left _ _).trans hrL
  have hrK : K^4 ≤ radical n := (Nat.le_succ _).trans ((le_max_right _ _).trans hrL)
  have hrn : radical n ≤ n := radical_le hn0
  have hnr : n^2 ≤ (radical n)^3 := by
    calc
      _ ≤ (K^2*radical n)^2 := Nat.pow_le_pow_left hnK 2
      _ = K^4*(radical n)^2 := by ring
      _ ≤ radical n*(radical n)^2 := Nat.mul_le_mul_right _ hrK
      _ = _ := by ring
  have hrn' : (radical n)^2 ≤ n^3 :=
    (Nat.pow_le_pow_left hrn 2).trans (Nat.pow_le_pow_right hn0 (by decide : 2 ≤ 3))
  have hcent := hH n (radical n) (hrH.trans hrn) hrH hnr hrn'
  have hband := (hSA hn.1).2
  have he : deviation w (radical n)-μ=(deviation w n-μ)+(center w n-center w (radical n)) := by
    rw [deviation,deviation,primeScore_radical]
    ring
  refine ⟨squarefree_radical,?_⟩
  rw [he]
  have hh := abs_add_le (deviation w n-μ) (center w n-center w (radical n))
  linarith

#print axioms exists_squarefree_band
end Erdos1206.SquarefreeMovingBandDensity
