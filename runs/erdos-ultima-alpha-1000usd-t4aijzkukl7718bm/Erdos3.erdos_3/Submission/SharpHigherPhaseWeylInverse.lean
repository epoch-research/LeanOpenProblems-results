import Submission.HigherPhaseWeylInverse
import Submission.DilatedQuadraticShift
import Submission.DyadicFineOrbitInverse

/-! Leading-coefficient Weyl inverse estimates with the natural inverse-degree
length scale, for circle polynomial phases of every positive degree. -/
namespace Erdos3SharpHigherPhaseWeylInverse
open Finset Erdos3HigherPhaseDifferences Erdos3HigherPhaseWeylInverse
  Erdos3QuadraticRecurrenceAverages Erdos3DilatedQuadraticShift
  Erdos3DyadicFineOrbitInverse
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

lemma dyadic_dilated_shift (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ = 1) (s N t : ℕ)
    (hN : 0 < N) (hmean : (1/2 : ℝ)^s ≤ ‖intervalMean N f‖)
    (ht : t < N/2^(3*s+6)) :
    ∃ i j : Fin (2^(2*s+4)), j.val < i.val ∧ (1/2 : ℝ)^(2*s+4) <
      ‖𝔼 n : Fin N, f (n.val+i.val*t)*conj (f (n.val+j.val*t))‖ := by
  let H := 2^(2*s+4)
  have hH : 0 < H := Nat.two_pow_pos _
  have hδ : 0 < (1/2 : ℝ)^s := pow_pos (by norm_num) _
  have hDt : 2^(3*s+6)*t ≤ N := (Nat.mul_le_mul_left _ ht.le).trans (Nat.mul_div_le N _)
  have hDeq : 2^(3*s+6) = 4*H*2^s := by
    dsimp only [H]
    rw [show 4 = 2^2 by norm_num,← pow_add,← pow_add]
    congr 1
    omega
  rw [hDeq] at hDt
  have hDtr : 4*(H : ℝ)*(2 : ℝ)^s*(t : ℝ) ≤ N := by exact_mod_cast hDt
  have hshift : 2*(H : ℝ)*(t : ℝ)/(N : ℝ) ≤ (1/2 : ℝ)^s/2 := by
    rw [div_pow,one_pow,div_div]
    apply (div_le_div_iff₀ (Nat.cast_pos.mpr hN) (by positivity : 0 < (2 : ℝ)^s*2)).mpr
    nlinarith only [hDtr]
  have hdiag : 1/(H : ℝ) ≤ ((1/2 : ℝ)^s)^2/8 := by
    have he : 1/(H : ℝ) = ((1/2 : ℝ)^s)^2/16 := by
      rw [dyadic_square_div16,div_pow,one_pow]
      simp only [H,Nat.cast_pow,Nat.cast_ofNat]
    rw [he]
    nlinarith only [sq_nonneg ((1/2 : ℝ)^s)]
  obtain ⟨i,j,hji,hcorr⟩ := dilated_short_shift_correlation f hf hN hH hδ hmean hshift hdiag
  exact ⟨i,j,hji,by simpa only [dyadic_square_div16] using hcorr⟩

/-- Index k corresponds to degree k+1. -/
def sharpWeylConstant : ℕ → ℕ
  | 0 => 2
  | k+1 => 30*sharpWeylConstant k+50

lemma sharpWeylConstant_pos (k : ℕ) : 0 < sharpWeylConstant k := by
  cases k <;> simp only [sharpWeylConstant] <;> omega

/-- A large mean of a degree-(k+1) circle polynomial gives a bounded denominator
approximating its top difference with error O_{k,s}(N^-(k+1)). -/
theorem sharp_leading_phase_inverse (k : ℕ) (f : ℕ → Additive Circle) (z : Additive Circle)
    (hf : diffIter (k+1) f = fun _ ↦ z) (s N : ℕ)
    (hN : 2^(sharpWeylConstant k*(s+1)) ≤ N)
    (hmean : (1/2 : ℝ)^s ≤ ‖intervalMean N (fun n ↦ phase (f n))‖) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 2^(sharpWeylConstant k*(s+1)) ∧
      ‖(phase z)^q-1‖ ≤ (2 : ℝ)^(sharpWeylConstant k*(s+1))/(N : ℝ)^(k+1) := by
  induction k generalizing f z s N with
  | zero =>
    have hm : ‖intervalMean N (fun n ↦ phase (f n))‖ =
        ‖𝔼 n : Fin N, (phase z)^n.val‖ := by
      have he : intervalMean N (fun n ↦ phase (f n)) =
          𝔼 n : Fin N, phase (f 0)*(phase z)^n.val := by
        apply expect_congr rfl
        intro n _
        exact first_difference_phase f z hf n.val
      rw [he,← mul_expect,norm_mul,phase_norm,one_mul]
    have hgeo := geometric_mean_norm (phase z) (phase_norm z) N
    have hmul : (1/2 : ℝ)^s*‖phase z-1‖ ≤ 2/(N : ℝ) := by
      rw [hm] at hmean
      exact (mul_le_mul_of_nonneg_right hmean (norm_nonneg _)).trans hgeo
    refine ⟨1,by decide,Nat.one_le_pow _ _ (by decide),?_⟩
    rw [pow_one,show 0+1=1 by omega,pow_one]
    have hsmall : ‖phase z-1‖ ≤ (2 : ℝ)^(s+1)/(N : ℝ) := by
      calc
        _ ≤ (2/(N : ℝ))/((1/2 : ℝ)^s) :=
          (le_div_iff₀ (pow_pos (by norm_num) _)).mpr (by linarith only [hmul])
        _ = _ := by rw [div_pow,one_pow,pow_succ]; field_simp
    exact hsmall.trans (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) (by simp only [sharpWeylConstant]; omega)) (Nat.cast_nonneg N))
  | succ k ih =>
    let A := sharpWeylConstant k
    let v := A*(2*s+5)
    let h := 2*s+4+v
    let d := 3*s+6
    have hN0 : 0 < N := (Nat.two_pow_pos _).trans_le hN
    have hbudget : 13+2*d+3*h+2*v ≤ sharpWeylConstant (k+1)*(s+1) := by
      dsimp only [d,h,v,A]
      rw [sharpWeylConstant]
      nlinarith only [Nat.zero_le (sharpWeylConstant k*s),Nat.zero_le (sharpWeylConstant k)]
    have hNfine : 2^(13+2*d+3*h+2*v) ≤ N :=
      (Nat.pow_le_pow_right (by decide) hbudget).trans hN
    have hNind : 2^(sharpWeylConstant k*((2*s+4)+1)) ≤ N := by
      apply le_trans _ hN
      apply Nat.pow_le_pow_right (by decide)
      rw [sharpWeylConstant]
      nlinarith only [Nat.zero_le (sharpWeylConstant k*s),Nat.zero_le (sharpWeylConstant k)]
    have hgood : ∀ t < N/2^d, ∃ a : ℕ, 0 < a ∧ a < 2^h ∧
        ‖(phase z)^(a*t)-1‖ ≤ (2 : ℝ)^v/(N : ℝ)^(k+1) := by
      intro t ht
      obtain ⟨i,j,hji,hcorr⟩ := dyadic_dilated_shift (fun n ↦ phase (f n))
        (fun n ↦ phase_norm _) s N t hN0 hmean ht
      let l := i.val-j.val
      have hl : 0 < l := by dsimp only [l]; omega
      have hlH : l < 2^(2*s+4) := by dsimp only [l]; omega
      let g : ℕ → Additive Circle := fun n ↦ f (n+i.val*t)-f (n+j.val*t)
      have hg : diffIter (k+1) g = fun _ ↦ (l*t) • z := by
        have hh := shifted_difference_top f z (k+1) hf (Nat.mul_le_mul_right t hji.le)
        simpa only [g,l,Nat.sub_mul] using hh
      have hgmean : (1/2 : ℝ)^(2*s+4) ≤ ‖intervalMean N (fun n ↦ phase (g n))‖ := by
        simpa only [intervalMean,g,phase_sub] using hcorr.le
      obtain ⟨a,ha,hab,hsmall⟩ := ih g ((l*t) • z) hg (2*s+4) N hNind hgmean
      have hav : a ≤ 2^v := by simpa only [v,A,show 2*s+4+1 = 2*s+5 by omega] using hab
      refine ⟨a*l,Nat.mul_pos ha hl,?_,?_⟩
      · calc
          _ < a*2^(2*s+4) := Nat.mul_lt_mul_of_pos_left hlH ha
          _ ≤ 2^v*2^(2*s+4) := Nat.mul_le_mul_right _ hav
          _ = 2^h := by rw [← pow_add]; congr 1; dsimp only [h]; omega
      · rw [phase_nsmul,← pow_mul,show (l*t)*a=(a*l)*t by ring] at hsmall
        simpa only [v,A,show 2*s+4+1 = 2*s+5 by omega] using hsmall
    obtain ⟨q,hq,hqb,herr⟩ := dyadic_fine_orbit_inverse (phase z) (phase_norm z)
      d h v (k+1) N (by omega) hNfine hgood
    refine ⟨q,hq,?_,?_⟩
    · apply hqb.le.trans
      apply Nat.pow_le_pow_right (by decide)
      dsimp only [d,h,v,A]
      rw [sharpWeylConstant]
      nlinarith only [Nat.zero_le (sharpWeylConstant k*s),Nat.zero_le (sharpWeylConstant k)]
    · apply herr.trans
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply pow_le_pow_right₀ (by norm_num)
      dsimp only [d,h,v,A]
      rw [sharpWeylConstant]
      nlinarith only [Nat.zero_le (sharpWeylConstant k*s),Nat.zero_le (sharpWeylConstant k)]

#print axioms sharp_leading_phase_inverse
end Erdos3SharpHigherPhaseWeylInverse
