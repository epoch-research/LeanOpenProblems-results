import Submission.QuadraticRecurrenceExtraction
import Submission.LocalQuadraticProgressions

/-! Polynomial quantitative recurrence for one quadratic unit phase. -/
namespace Erdos3PolynomialSquareRecurrence
open Finset Erdos3QuadraticRecurrenceAverages Erdos3QuadraticRecurrenceExtraction
  Erdos3FiniteUniformity Erdos3LocalQuadraticProgressions
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000

lemma quadratic_pair_formula (z : ℂ) (hz : ‖z‖ = 1) (n j l : ℕ) :
    z^((n+(j+l)+1)^2)*conj (z^((n+j+1)^2)) =
      z^(l*(2*j+l+2))*(z^(2*l))^n := by
  have he : (n+(j+l)+1)^2 = l*(2*j+l+2)+2*l*n+(n+j+1)^2 := by ring
  rw [he, pow_add, mul_assoc, mul_conj_eq_one (by rw [norm_pow, hz, one_pow]),
    mul_one, pow_add]
  simp only [pow_mul]

lemma quadratic_correlation_bound (z : ℂ) (hz : ‖z‖ = 1) (N i j : ℕ)
    (hji : j ≤ i) :
    ‖𝔼 n : Fin N, z^((n.val+i+1)^2)*conj (z^((n.val+j+1)^2))‖ *
      ‖z^(2*(i-j))-1‖ ≤ 2/(N : ℝ) := by
  have he : ∀ n : Fin N,
      z^((n.val+i+1)^2)*conj (z^((n.val+j+1)^2)) =
        z^((i-j)*(2*j+(i-j)+2))*(z^(2*(i-j)))^n.val := by
    intro n
    have hh := quadratic_pair_formula z hz n.val j (i-j)
    simpa only [Nat.add_sub_of_le hji] using hh
  simp_rw [he]
  rw [← mul_expect, norm_mul, norm_pow, hz, one_pow, one_mul]
  exact geometric_mean_norm (z^(2*(i-j))) (by rw [norm_pow, hz, one_pow]) N

/-- Parameter form of a polynomial single-phase square recurrence bound. -/
theorem square_recurrence_parameters (v : ℂ) (hv : ‖v‖ = 1)
    {ε : ℝ} (hε : 0 < ε) {K H N : ℕ} (hK : 0 < K) (hH : 0 < H) (hN : 0 < N)
    (hscale : 8 ≤ (K : ℝ)*ε^2)
    (hshifts : 16*(K : ℝ)*H ≤ N)
    (hdiagonal : 128*(K : ℝ)^2 ≤ H)
    (herror : 1024*(K : ℝ)^3*H ≤ ε*N) :
    ∃ d : ℕ, 0 < d ∧ d ≤ N ∧ ‖v^(d^2)-1‖ ≤ ε := by
  letI : NeZero N := ⟨by omega⟩
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hHr : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  by_contra hn
  push_neg at hn
  have havoid (n : Fin N) : ε ≤ ‖v^((n.val+1)^2)-1‖ :=
    (hn (n.val+1) (by omega) (by omega)).le
  obtain ⟨k,hk,hkK,hfreq⟩ := avoidance_frequency
    (fun n : Fin N ↦ v^((n.val+1)^2))
    (fun n ↦ by rw [norm_pow, hv, one_pow]) hε havoid hK hscale
  let δ : ℝ := 1/(4*(K : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let f : ℕ → ℂ := fun n ↦ (v^k)^((n+1)^2)
  have hf (n : ℕ) : ‖f n‖ = 1 := by simp only [f, norm_pow, hv, one_pow]
  have hmean : δ ≤ ‖intervalMean N f‖ := by
    have he : ∀ n : Fin N, (v^((n.val+1)^2))^k = (v^k)^((n.val+1)^2) := by
      intro n
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    simp_rw [he] at hfreq
    exact hfreq.le
  have hshift : 2*(H : ℝ)/(N : ℝ) ≤ δ/2 := by
    dsimp [δ]
    rw [div_div]
    apply (div_le_div_iff₀ hNr (by positivity : 0 < 4*(K : ℝ)*2)).mpr
    nlinarith only [hshifts]
  have hdiag : 1/(H : ℝ) ≤ δ^2/8 := by
    have he : δ^2/8 = 1/(128*(K : ℝ)^2) := by dsimp [δ]; ring
    rw [he]
    exact one_div_le_one_div_of_le (by positivity) hdiagonal
  obtain ⟨i,j,hij,hcorr⟩ := short_shift_correlation f hf hN hH hδ hmean hshift hdiag
  have hordered : ∃ i j : Fin H, j.val < i.val ∧ δ^2/16 <
      ‖𝔼 n : Fin N, f (n.val+i.val)*conj (f (n.val+j.val))‖ := by
    rcases lt_trichotomy j.val i.val with h|h|h
    · exact ⟨i,j,h,hcorr⟩
    · exact (hij (Fin.ext h.symm)).elim
    · refine ⟨j,i,h,?_⟩
      rw [norm_pair_swap]
      exact hcorr
  obtain ⟨i,j,hji,hcorr⟩ := hordered
  let l := i.val-j.val
  have hl : 0 < l := by dsimp [l]; omega
  have hlH : l < H := by dsimp [l]; omega
  let d := 2*k*l
  have hd : 0 < d := Nat.mul_pos (Nat.mul_pos (by decide) hk) hl
  have hdsize : (d : ℝ) ≤ 2*(K : ℝ)*H := by
    dsimp [d]
    push_cast
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hkK.le) (by norm_num)
    · exact_mod_cast hlH.le
    · exact Nat.cast_nonneg l
    · positivity
  have hdN : d ≤ N := by
    have hh : (d : ℝ) ≤ N := by
      have hp : 0 ≤ (K : ℝ)*H := mul_nonneg hKr.le hHr.le
      nlinarith only [hdsize,hshifts,hp]
    exact_mod_cast hh
  let R := ‖v^d-1‖
  have hR : 0 ≤ R := norm_nonneg _
  have hgeom :
      ‖𝔼 n : Fin N, f (n.val+i.val)*conj (f (n.val+j.val))‖*R ≤ 2/(N : ℝ) := by
    have hh := quadratic_correlation_bound (v^k) (by rw [norm_pow, hv, one_pow])
      N i.val j.val hji.le
    have he : (v^k)^(2*(i.val-j.val)) = v^d := by
      rw [← pow_mul]
      congr 1
      dsimp [d,l]
      ring
    simpa only [he] using hh
  have hsmall : R ≤ 512*(K : ℝ)^2/(N : ℝ) := by
    have hh : δ^2/16*R ≤ 2/(N : ℝ) :=
      (mul_le_mul_of_nonneg_right hcorr.le hR).trans hgeom
    have he : δ^2/16 = 1/(256*(K : ℝ)^2) := by dsimp [δ]; ring
    rw [he, one_div_mul_eq_div] at hh
    have hh' := (div_le_iff₀ (by positivity : 0 < 256*(K : ℝ)^2)).mp hh
    calc
      _ ≤ (2/(N : ℝ))*(256*(K : ℝ)^2) := hh'
      _ = _ := by ring
  have hosc : ‖v^(d^2)-1‖ ≤ (d : ℝ)*R := by
    have hh := unit_power_oscillation (v^d) (by rw [norm_pow, hv, one_pow]) d
    simpa only [← pow_mul, ← pow_two] using hh
  have hfinal : ‖v^(d^2)-1‖ ≤ ε := by
    calc
      _ ≤ (d : ℝ)*R := hosc
      _ ≤ (2*(K : ℝ)*H)*(512*(K : ℝ)^2/(N : ℝ)) :=
        mul_le_mul hdsize hsmall hR (by positivity)
      _ = (1024*(K : ℝ)^3*H)/(N : ℝ) := by ring
      _ ≤ ε := (div_le_iff₀ hNr).mpr herror
  exact (not_lt_of_ge hfinal) (hn d hd hdN)

/-- Degree-eleven bound in the reciprocal of the dyadic accuracy. -/
def singleRecurrenceBound (t : ℕ) : ℕ := 2^38*(2^t)^11+1

/-- One unit phase admits a square recurrence with a polynomial bound in
inverse accuracy. No coloring or arithmetic-progression theorem is used. -/
theorem single_square_recurrence (v : ℂ) (hv : ‖v‖ = 1) (t : ℕ) :
    ∃ d : ℕ, 0 < d ∧ d < singleRecurrenceBound t ∧
      ‖v^(d^2)-1‖ ≤ (1/2 : ℝ)^t := by
  let r : ℕ := 2^t
  let K : ℕ := 16*r^2
  let H : ℕ := 128*K^2
  let N : ℕ := 2048*K^3*H*r
  have hr : 0 < r := by dsimp [r]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hr0 : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hH0 : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  have hKr : (K : ℝ) = 16*(r : ℝ)^2 := by simp only [K, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  have hHr : (H : ℝ) = 128*(K : ℝ)^2 := by simp only [H, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  have hNr : (N : ℝ) = 2048*(K : ℝ)^3*H*r := by simp only [N, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  have he : (1/2 : ℝ)^t = 1/(r : ℝ) := by
    dsimp [r]
    rw [div_pow, one_pow, Nat.cast_pow, Nat.cast_ofNat]
  have hscale : 8 ≤ (K : ℝ)*(1/(r : ℝ))^2 := by
    rw [hKr]
    have hh : 16*(r : ℝ)^2*(1/(r : ℝ))^2 = 16 := by field_simp
    rw [hh]
    norm_num
  have hshifts : 16*(K : ℝ)*H ≤ N := by
    rw [hNr]
    have hfac : 1 ≤ 128*(K : ℝ)^2*r := by
      have hsq : 1 ≤ (K : ℝ)^2 := one_le_pow₀ hK1
      calc
        (1 : ℝ) ≤ 128*1*1 := by norm_num
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hsq (by norm_num)) hr1
          (by norm_num) (by positivity)
    calc
      _ = (16*(K : ℝ)*H)*1 := (mul_one _).symm
      _ ≤ (16*(K : ℝ)*H)*(128*(K : ℝ)^2*r) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = _ := by ring
  have herror : 1024*(K : ℝ)^3*H ≤ (1/(r : ℝ))*N := by
    rw [hNr]
    have heq : (1/(r : ℝ))*(2048*(K : ℝ)^3*H*r) = 2048*(K : ℝ)^3*H := by
      field_simp
    rw [heq]
    nlinarith only [show 0 ≤ (K : ℝ)^3*H by positivity]
  obtain ⟨d,hd,hdN,hrec⟩ := square_recurrence_parameters v hv
    (by positivity : 0 < 1/(r : ℝ)) hK hH hN hscale hshifts hHr.ge herror
  refine ⟨d,hd,?_,by simpa only [he] using hrec⟩
  have hbound : N+1 = singleRecurrenceBound t := by
    dsimp [N,H,K,r,singleRecurrenceBound]
    ring
  omega

lemma singleRecurrenceBound_eq (t : ℕ) :
    singleRecurrenceBound t = 2^(11*t+38)+1 := by
  unfold singleRecurrenceBound
  rw [pow_add, Nat.mul_comm 11 t, pow_mul]
  ring

#print axioms square_recurrence_parameters
#print axioms single_square_recurrence
end Erdos3PolynomialSquareRecurrence
