import Submission.HigherPhaseDifferences

/-! A finite quantitative leading-coefficient estimate for polynomial phases
of every fixed degree, proved by repeated short-shift differencing. This is
NOT a Gowers inverse theorem for arbitrary functions. -/
namespace Erdos3HigherPhaseWeylInverse
open Finset Erdos3HigherPhaseDifferences Erdos3QuadraticRecurrenceExtraction
  Erdos3QuadraticRecurrenceAverages
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

lemma dyadic_square_div16 (s : ℕ) : ((1/2 : ℝ)^s)^2/16 = (1/2 : ℝ)^(2*s+4) := by
  calc
    _ = ((1/2 : ℝ)^s)^2*(1/2 : ℝ)^4 := by norm_num; ring
    _ = (1/2 : ℝ)^(s*2+4) := by rw [← pow_mul,← pow_add]
    _ = _ := by congr 1; omega

lemma dyadic_short_shift (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ = 1) (s N : ℕ)
    (hN : 2^(3*s+6) ≤ N) (hmean : (1/2 : ℝ)^s ≤ ‖intervalMean N f‖) :
    ∃ i j : Fin (2^(2*s+4)), j.val < i.val ∧ (1/2 : ℝ)^(2*s+4) <
      ‖𝔼 n : Fin N, f (n.val+i.val)*conj (f (n.val+j.val))‖ := by
  let H := 2^(2*s+4)
  have hH : 0 < H := Nat.two_pow_pos _
  have hN0 : 0 < N := (Nat.two_pow_pos _).trans_le hN
  have hNreal : 4*(H : ℝ)*(2 : ℝ)^s ≤ N := by
    have he : 4*H*2^s = 2^(3*s+6) := by
      dsimp [H]
      rw [show 4 = 2^2 by norm_num,← pow_add,← pow_add]
      congr 1
      omega
    exact_mod_cast (show 4*H*2^s ≤ N by rw [he]; exact hN)
  have hδ : 0 < (1/2 : ℝ)^s := pow_pos (by norm_num) _
  have hshift : 2*(H : ℝ)/(N : ℝ) ≤ (1/2 : ℝ)^s/2 := by
    rw [div_pow,one_pow,div_div]
    apply (div_le_div_iff₀ (Nat.cast_pos.mpr hN0) (by positivity : 0 < (2 : ℝ)^s*2)).mpr
    nlinarith only [hNreal]
  have hdiag : 1/(H : ℝ) ≤ ((1/2 : ℝ)^s)^2/8 := by
    have he : 1/(H : ℝ) = ((1/2 : ℝ)^s)^2/16 := by
      rw [dyadic_square_div16,div_pow,one_pow]
      simp only [H,Nat.cast_pow,Nat.cast_ofNat]
    rw [he]
    nlinarith only [sq_nonneg ((1/2 : ℝ)^s)]
  obtain ⟨i,j,hij,hcorr⟩ := short_shift_correlation f hf hN0 hH hδ hmean hshift hdiag
  rw [dyadic_square_div16] at hcorr
  rcases lt_trichotomy j.val i.val with h|h|h
  · exact ⟨i,j,h,hcorr⟩
  · exact (hij (Fin.ext h.symm)).elim
  · refine ⟨j,i,h,?_⟩
    rw [norm_pair_swap]
    exact hcorr

/-- Index k governs phases of degree k+1. -/
def weylConstant : ℕ → ℕ
  | 0 => 2
  | k+1 => 5*weylConstant k+10

lemma weylConstant_pos (k : ℕ) : 0 < weylConstant k := by
  cases k <;> simp only [weylConstant] <;> omega

/-- A large mean of a degree-(k+1) circle phase forces a bounded multiple of
its top difference close to zero on the circle. The denominator and error
numerator are polynomial in inverse mean size, at each fixed degree. -/
theorem leading_phase_inverse (k : ℕ) (f : ℕ → Additive Circle) (z : Additive Circle)
    (hf : diffIter (k+1) f = fun _ ↦ z) (s N : ℕ)
    (hN : 2^(weylConstant k*(s+1)) ≤ N)
    (hmean : (1/2 : ℝ)^s ≤ ‖intervalMean N (fun n ↦ phase (f n))‖) :
    ∃ d : ℕ, 0 < d ∧ d ≤ 2^(weylConstant k*(s+1)) ∧
      ‖(phase z)^d-1‖ ≤ (2 : ℝ)^(weylConstant k*(s+1))/(N : ℝ) := by
  induction k generalizing f z s N with
  | zero =>
    have hN0 : 0 < N := (Nat.two_pow_pos _).trans_le hN
    have hδ : 0 < (1/2 : ℝ)^s := pow_pos (by norm_num) _
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
    rw [pow_one]
    have hsmall : ‖phase z-1‖ ≤ (2 : ℝ)^(s+1)/(N : ℝ) := by
      have hh := (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hmul)
      calc
        _ ≤ (2/(N : ℝ))/((1/2 : ℝ)^s) := hh
        _ = _ := by rw [div_pow,one_pow,pow_succ]; field_simp
    exact hsmall.trans (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) (by simp only [weylConstant]; omega)) (Nat.cast_nonneg N))
  | succ k ih =>
    have hNshort : 2^(3*s+6) ≤ N := by
      apply le_trans _ hN
      apply Nat.pow_le_pow_right (by decide)
      rw [weylConstant]
      nlinarith only [Nat.zero_le (weylConstant k*(s+1))]
    obtain ⟨i,j,hji,hcorr⟩ := dyadic_short_shift (fun n ↦ phase (f n))
      (fun n ↦ phase_norm _) s N hNshort hmean
    let l := i.val-j.val
    have hl : 0 < l := by dsimp [l]; omega
    have hlH : l ≤ 2^(2*s+4) := by dsimp [l]; omega
    let g : ℕ → Additive Circle := fun n ↦ f (n+i.val)-f (n+j.val)
    have hg : diffIter (k+1) g = fun _ ↦ l • z :=
      shifted_difference_top f z (k+1) hf hji.le
    have hgmean : (1/2 : ℝ)^(2*s+4) ≤ ‖intervalMean N (fun n ↦ phase (g n))‖ := by
      simpa only [intervalMean,g,phase_sub] using hcorr.le
    have hexp : weylConstant k*((2*s+4)+1)+(2*s+4) ≤ weylConstant (k+1)*(s+1) := by
      rw [weylConstant]
      nlinarith only [Nat.zero_le (weylConstant k*s)]
    have hexp' : weylConstant k*((2*s+4)+1) ≤ weylConstant (k+1)*(s+1) := by omega
    have hNind : 2^(weylConstant k*((2*s+4)+1)) ≤ N :=
      (Nat.pow_le_pow_right (by decide) hexp').trans hN
    obtain ⟨a,ha,hab,hsmall⟩ := ih g (l • z) hg (2*s+4) N hNind hgmean
    refine ⟨a*l,Nat.mul_pos ha hl,?_,?_⟩
    · calc
        _ ≤ 2^(weylConstant k*((2*s+4)+1))*2^(2*s+4) := Nat.mul_le_mul hab hlH
        _ = 2^(weylConstant k*((2*s+4)+1)+(2*s+4)) := (pow_add ..).symm
        _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp
    · rw [phase_nsmul,← pow_mul,Nat.mul_comm l a] at hsmall
      exact hsmall.trans (div_le_div_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) hexp') (Nat.cast_nonneg N))

#print axioms dyadic_short_shift
#print axioms leading_phase_inverse
end Erdos3HigherPhaseWeylInverse
