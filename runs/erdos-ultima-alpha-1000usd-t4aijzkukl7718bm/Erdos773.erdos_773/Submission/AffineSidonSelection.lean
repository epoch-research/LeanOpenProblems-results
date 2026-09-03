import Submission.AffineCollisionBounds
import Submission.MonotoneSidonSelection

/-!
Sidon extraction in a single unit affine progression. Cardinalities here are
measured relative to its index length N; its roots may be as large as qN+r.
-/
namespace Erdos773.AffineSidonSelection
open Finset Filter AffineCollisionBounds
set_option maxHeartbeats 2000000

private lemma affine_square_strictMono {q : ℕ} (hq : 0 < q) (r : ℕ) :
    StrictMono (fun n : ℕ => (q*n+r)^2) := by
  intro a b hab
  exact Nat.pow_lt_pow_left
    (Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hab hq) _) (by decide : (2 : ℕ) ≠ 0)

/-- All three-entry obstructions are included by weak-Sidon extraction. -/
theorem affine_alteration (N q r : ℕ) (hq : 0 < q) (hcop : q.Coprime (2*r))
    (p K : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hK : 0 ≤ K)
    (hdiv : ∀ D : ℕ, 0 < D → D ≤ N^2 → (D.divisors.card : ℝ) ≤ K) :
    (p*N-p^4*N*defectRange N q r*K)/4 ≤
      (maxSidonSubsetCard ((Icc 1 N).image (fun n => (q*n+r)^2)) : ℝ) := by
  have hh := MonotoneSidonSelection.alteration (Icc 1 N)
    (fun n => (q*n+r)^2) (affine_square_strictMono hq r) p hp hp1
  have hc := uniform_divisor_bound N q r hq hcop K hK hdiv
  change ((collisions N q r).card : ℝ) ≤ _ at hc
  have hm := mul_le_mul_of_nonneg_left hc (pow_nonneg hp 4)
  simp only [Nat.card_Icc,Nat.add_sub_cancel] at hh
  change (p*N-p^4*(collisions N q r).card)/4 ≤ _ at hh
  nlinarith only [hh,hm]

/-- The optimized coefficient-dependent finite Sidon lower bound. -/
theorem affine_finite_lower (N q r : ℕ) (hq : 0 < q) (hcop : q.Coprime (2*r))
    (K : ℝ) (hK : 0 ≤ K)
    (hdiv : ∀ D : ℕ, 0 < D → D ≤ N^2 → (D.divisors.card : ℝ) ≤ K) :
    7*N/(64*(max 1 ((defectRange N q r : ℝ)*K))^(1/3 : ℝ)) ≤
      (maxSidonSubsetCard ((Icc 1 N).image (fun n => (q*n+r)^2)) : ℝ) := by
  have hc := uniform_divisor_bound N q r hq hcop K hK hdiv
  have hh := MonotoneSidonSelection.finite_lower (Icc 1 N)
    (fun n => (q*n+r)^2) (affine_square_strictMono hq r)
    ((defectRange N q r : ℝ)*K) (by simpa [mul_assoc] using hc)
  simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hh

private lemma eventual_divisors (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℕ, 0 < D → D ≤ N^2 →
      (D.divisors.card : ℝ) ≤ (N : ℝ)^ε := by
  obtain ⟨C,hC,hdiv⟩ := divisor_card_subpower (ε/4) (by positivity)
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(ε/2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < ε/2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [tendsto_atTop.mp ht C,eventually_ge_atTop 1] with N hC hN
  intro D hD hDN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ C*(D : ℝ)^(ε/4) := hdiv D
    _ ≤ (N : ℝ)^(ε/2)*((N : ℝ)^2)^(ε/4) := mul_le_mul hC
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hDN) (by positivity))
      (by positivity) (by positivity)
    _ = (N : ℝ)^ε := by
      rw [← Real.rpow_natCast_mul hNp.le,← Real.rpow_add hNp]
      congr 1
      norm_num
      ring

/-- A uniform one-shift saving: for q<=N the cardinality is at least
N^(2/3-epsilon) q^(1/3), eventually uniformly in q and r. This is relative
to the index length N, not the affine root height qN+r. -/
theorem uniform_denominator_lower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ q r : ℕ, 0 < q → q ≤ N → q.Coprime (2*r) →
      (N : ℝ)^(2/3-ε)*(q : ℝ)^(1/3 : ℝ) ≤
        (maxSidonSubsetCard ((Icc 1 N).image (fun n => (q*n+r)^2)) : ℝ) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(-(2*ε/3))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by positivity : 0 < 2*ε/3)).comp tendsto_natCast_atTop_atTop
  have hsmall := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 7/64) ht
  filter_upwards [eventual_divisors ε hε,hsmall,eventually_ge_atTop 1] with N hdiv hsmall hN
  intro q r hq hqN hcop
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hqNR : (q : ℝ) ≤ N := by exact_mod_cast hqN
  let K : ℝ := (N : ℝ)^ε
  let R : ℝ := (max 1 ((defectRange N q r : ℝ)*K))^(1/3 : ℝ)
  let U : ℝ := (N : ℝ)^((1+ε)/3)*(q : ℝ)^(-(1/3 : ℝ))
  let target : ℝ := (N : ℝ)^(2/3-ε)*(q : ℝ)^(1/3 : ℝ)
  have hK1 : 1 ≤ K := Real.one_le_rpow hN1 hε.le
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hR3 : R^3 = max 1 ((defectRange N q r : ℝ)*K) := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (by positivity :
      (0 : ℝ) ≤ max 1 ((defectRange N q r : ℝ)*K))]
    norm_num
  have hU3 : U^3 = (N : ℝ)/q*K := by
    dsimp [U,K]
    rw [mul_pow,← Real.rpow_mul_natCast hNp.le,← Real.rpow_mul_natCast hqp.le]
    norm_num
    rw [Real.rpow_add hNp,Real.rpow_one,Real.rpow_neg_one]
    ring
  have hratio : 1 ≤ (N : ℝ)/q := (one_le_div hqp).mpr hqNR
  have hT : (defectRange N q r : ℝ) ≤ (N : ℝ)/q := by
    have hh : defectRange N q r*q ≤ N := by
      have hle : defectRange N q r ≤ N/(2*q) := min_le_left _ _
      have hh := (Nat.le_div_iff_mul_le (by positivity : 0 < 2*q)).mp hle
      nlinarith only [hh,Nat.zero_le (defectRange N q r*q)]
    apply (le_div_iff₀ hqp).mpr
    exact_mod_cast hh
  have hRU : R ≤ U := by
    apply le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) hU.le
    rw [hR3,hU3]
    exact max_le (one_le_mul_of_one_le_of_one_le hratio hK1)
      (mul_le_mul_of_nonneg_right hT hK)
  have htargetU : target*U = (N : ℝ)*(N : ℝ)^(-(2*ε/3)) := by
    dsimp [target,U]
    calc
      _ = ((N : ℝ)^(2/3-ε)*(N : ℝ)^((1+ε)/3))*
          ((q : ℝ)^(1/3 : ℝ)*(q : ℝ)^(-(1/3 : ℝ))) := by ring
      _ = (N : ℝ)^(1-(2*ε/3)) := by
        rw [← Real.rpow_add hNp,← Real.rpow_add hqp]
        norm_num
        congr 1
        ring
      _ = _ := by rw [Real.rpow_sub hNp,Real.rpow_one,Real.rpow_neg hNp.le]; ring
  have htargetpos : 0 ≤ target := by dsimp [target]; positivity
  have hprod := mul_le_mul_of_nonneg_left hRU htargetpos
  rw [htargetU] at hprod
  have hsmallN := mul_le_mul_of_nonneg_left hsmall hNp.le
  have hmain := affine_finite_lower N q r hq hcop K hK hdiv
  change 7*N/(64*R) ≤ _ at hmain
  apply le_trans _ hmain
  change target ≤ 7*N/(64*R)
  apply (le_div_iff₀ (by positivity : 0 < 64*R)).mpr
  nlinarith only [hprod,hsmallN]

/-- The denominator-dependent guaranteed term is still at most the 2/3
power of the actual root height. This bounds the displayed lower-bound
expression, not the actual Sidon maximum. -/
theorem denominator_term_le_height_power (N q r : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (N : ℝ)^(2/3-ε)*(q : ℝ)^(1/3 : ℝ) ≤
      ((q*N+r : ℕ) : ℝ)^(2/3 : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  calc
    _ ≤ (N : ℝ)^(2/3 : ℝ)*(q : ℝ)^(2/3 : ℝ) := mul_le_mul
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
      (Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num))
      (by positivity) (by positivity)
    _ = ((q*N : ℕ) : ℝ)^(2/3 : ℝ) := by
      push_cast
      rw [Real.mul_rpow (Nat.cast_nonneg q) (Nat.cast_nonneg N)]
      ring
    _ ≤ _ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_add_right (q*N) r)
      (by norm_num)

#print axioms affine_alteration
#print axioms affine_finite_lower
#print axioms uniform_denominator_lower
#print axioms denominator_term_le_height_power
end Erdos773.AffineSidonSelection
