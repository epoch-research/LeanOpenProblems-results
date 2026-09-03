import Submission.SelbergBasis

/-! A quadratic Selberg upper-bound sieve with a divisor-product cutoff.
The residue-product basis makes its main term diagonal. -/

namespace Erdos371
namespace FiniteSieve
open Finset
variable {ι : Type*} [DecidableEq ι]

noncomputable def selbergWeight (s : ι → ℕ) (R : ι → Finset ℕ) (T : Finset ι) : ℝ :=
  ∏ i ∈ T, ((R i).card : ℝ)/((s i : ℝ)-(R i).card)

noncomputable def selbergMass (s : ι → ℕ) (R : ι → Finset ℕ) (D : Finset (Finset ι)) : ℝ :=
  ∑ T ∈ D, selbergWeight s R T

lemma selbergWeight_pos (s : ι → ℕ) (R : ι → Finset ℕ) (T : Finset ι)
    (hr : ∀ i ∈ T, 0 < (R i).card ∧ (R i).card < s i) : 0 < selbergWeight s R T := by
  apply prod_pos
  intro i hi
  exact div_pos (by exact_mod_cast (hr i hi).1) (sub_pos.mpr (by exact_mod_cast (hr i hi).2))

lemma selbergWeight_mul_norm (s : ι → ℕ) (R : ι → Finset ℕ) (T : Finset ι)
    (hr : ∀ i ∈ T, 0 < (R i).card ∧ (R i).card < s i) :
    selbergWeight s R T * sieveBasisNorm s R T = 1 := by
  unfold selbergWeight sieveBasisNorm
  rw [← prod_mul_distrib]
  apply prod_eq_one
  intro i hi
  have hri : ((R i).card : ℝ) ≠ 0 := by exact_mod_cast (hr i hi).1.ne'
  have hsi : (s i : ℝ)-(R i).card ≠ 0 := (sub_pos.mpr (by exact_mod_cast (hr i hi).2)).ne'
  field_simp

lemma selbergMass_pos (s : ι → ℕ) (R : ι → Finset ℕ) (D : Finset (Finset ι))
    (hD : ∅ ∈ D) (hr : ∀ T ∈ D, ∀ i ∈ T, 0 < (R i).card ∧ (R i).card < s i) :
    0 < selbergMass s R D := by
  apply sum_pos (fun T hT => selbergWeight_pos s R T (hr T hT))
  exact ⟨∅,hD⟩

/-- A product-cutoff upper sieve. The error `2*Z^4` is deliberately coarse;
unlike degree-truncated Brun errors, it stays polynomial in the cutoff. -/
theorem quadratic_residue_sieve (S : Finset ι) (s : ι → ℕ) (R : ι → Finset ℕ)
    (hs : ∀ i ∈ S, s i ≠ 0)
    (hc : (↑S : Set ι).Pairwise (Function.onFun Nat.Coprime s))
    (hR : ∀ i ∈ S, R i ⊆ range (s i))
    (hr : ∀ i ∈ S, 0 < (R i).card ∧ (R i).card < s i)
    (D : Finset (Finset ι)) (hD : ∀ T ∈ D, T ⊆ S) (hDe : ∅ ∈ D)
    (Z : ℝ) (hZ : 0 ≤ Z) (hDZ : ∀ T ∈ D, (∏ i ∈ T, (s i : ℝ)) ≤ Z) (N : ℕ) :
    (avoidanceCount (range N) (fun i n => n%s i ∈ R i) S : ℝ) ≤
      N/selbergMass s R D + 2*Z^4 := by
  classical
  let w := selbergWeight s R
  let G := selbergMass s R D
  let F : ℕ → ℝ := fun n => ∑ T ∈ D, w T*sieveBasis s R T n
  have hw (T : Finset ι) (hT : T ∈ D) : 0 < w T :=
    selbergWeight_pos s R T (fun i hi => hr i (hD T hT hi))
  have hG : 0 < G := selbergMass_pos s R D hDe (fun T hT i hi => hr i (hD T hT hi))
  have havoid : (avoidanceCount (range N) (fun i n => n%s i ∈ R i) S : ℝ)*G^2 ≤
      ∑ n ∈ range N, (F n)^2 := by
    have hpoint (n : ℕ) : (if ∀ i ∈ S, ¬n%s i ∈ R i then (1 : ℝ) else 0)*G^2 ≤ (F n)^2 := by
      split_ifs with h
      · have hb (T : Finset ι) (hT : T ∈ D) : sieveBasis s R T n = 1 := by
          apply prod_eq_one
          intro i hi
          exact if_neg (h i (hD T hT hi))
        have he : F n = G := by
          dsimp only [F]
          rw [sum_congr rfl (fun T hT => by rw [hb T hT,mul_one])]
          rfl
        simp only [he,one_mul,le_refl]
      · simp only [zero_mul]
        exact sq_nonneg _
    have h := sum_le_sum (s := range N) (fun n _ => hpoint n)
    simp only [← sum_mul,sum_boole] at h
    unfold avoidanceCount
    convert h using 1
    apply congrArg (fun t : Finset ℕ => (t.card : ℝ)*G^2)
    ext n
    simp only [mem_filter]
  have hsum : (∑ n ∈ range N, (F n)^2) = ∑ T ∈ D, ∑ U ∈ D,
      w T*w U*(∑ n ∈ range N, sieveBasis s R T n*sieveBasis s R U n) := by
    simp only [F,pow_two,sum_mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro T hT
    rw [sum_comm]
    apply sum_congr rfl
    intro U hU
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    ring
  have hcov (T U : Finset ι) (hT : T ∈ D) (hU : U ∈ D) :
      (∑ n ∈ range N, sieveBasis s R T n*sieveBasis s R U n) ≤
        N*(if T=U then sieveBasisNorm s R T else 0)+2*Z^4 := by
    have h := sieveBasis_covariance_error S s R hs hc hR (fun i hi => (hr i hi).1)
      T U (hD T hT) (hD U hU) Z hZ (hDZ T hT) (hDZ U hU) N
    have h' := (le_abs_self _).trans h
    linarith
  have hterm (T U : Finset ι) (hT : T ∈ D) :
      w T*w U*(N*(if T=U then sieveBasisNorm s R T else 0)+2*Z^4) =
        (if T=U then N*w T else 0)+2*Z^4*w T*w U := by
    by_cases he : T=U
    · subst U
      simp only [if_true]
      have hn : w T*sieveBasisNorm s R T = 1 := selbergWeight_mul_norm s R T (fun i hi => hr i (hD T hT hi))
      calc
        _ = N*w T*(w T*sieveBasisNorm s R T)+2*Z^4*w T*w T := by ring
        _ = _ := by rw [hn]; ring
    · simp only [if_neg he]
      ring
  have hupper : (∑ n ∈ range N, (F n)^2) ≤ N*G+2*Z^4*G^2 := by
    rw [hsum]
    calc
      _ ≤ ∑ T ∈ D, ∑ U ∈ D, w T*w U*(N*(if T=U then sieveBasisNorm s R T else 0)+2*Z^4) :=
        sum_le_sum fun T hT => sum_le_sum fun U hU =>
          mul_le_mul_of_nonneg_left (hcov T U hT hU) (mul_nonneg (hw T hT).le (hw U hU).le)
      _ = ∑ T ∈ D, (N*w T+2*Z^4*w T*G) := by
        apply sum_congr rfl
        intro T hT
        simp_rw [hterm T _ hT]
        rw [sum_add_distrib,sum_ite_eq,if_pos hT,← mul_sum]
        rfl
      _ = _ := by
        rw [sum_add_distrib,← mul_sum,← sum_mul,← mul_sum]
        change N*G+2*Z^4*G*G = N*G+2*Z^4*G^2
        ring
  have hfinal := havoid.trans hupper
  calc
    _ ≤ (N*G+2*Z^4*G^2)/G^2 := (le_div_iff₀ (sq_pos_of_pos hG)).mpr hfinal
    _ = _ := by
      change (N*G+2*Z^4*G^2)/G^2 = N/G+2*Z^4
      field_simp

#print axioms quadratic_residue_sieve
end FiniteSieve
end Erdos371
