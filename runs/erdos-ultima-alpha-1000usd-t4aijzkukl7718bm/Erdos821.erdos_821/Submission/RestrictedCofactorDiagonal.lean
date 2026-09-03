import Submission.RestrictedCofactorWeights
import Submission.CofactorProductScales

/-!
# The single cofactor is not an averaged cofactor

The singleton prefix recovers the original shifted-prime progression.
The natural main term for a long cofactor interval does not extend to it:
already at modulus 2 there is an exact half-mass discrepancy for a weight
supported on odd integers. This is an obstruction to that extrapolation,
not a disproof of Erdős 821 or of the principal-character identity.
-/

open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def mangoldtRestriction (S : Set ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ∈ S then vonMangoldt n else 0, by simp⟩

lemma mangoldtRestriction_nonneg (S : Set ℕ) (n : ℕ) :
    0 ≤ mangoldtRestriction S n := by
  simp only [mangoldtRestriction,ArithmeticFunction.coe_mk]
  split_ifs <;> first | exact vonMangoldt_nonneg | exact le_rfl

lemma mangoldtRestriction_le (S : Set ℕ) (n : ℕ) :
    mangoldtRestriction S n ≤ vonMangoldt n := by
  simp only [mangoldtRestriction,ArithmeticFunction.coe_mk]
  split_ifs <;> first | exact le_rfl | exact vonMangoldt_nonneg

/-- Setting B=1 recovers the actual shifted progression, without an average. -/
lemma restricted_cofactor_singleton (f : ArithmeticFunction ℝ) (d N : ℕ) :
    restrictedCofactorWeight f d 1 0 1 N =
      ∑ n ∈ Icc 1 N, if d ∣ n-1 then f n else 0 := by
  simp only [restrictedCofactorWeight,zero_add,Icc_self,sum_singleton,
    Units.val_one,Nat.cast_one,one_mul]
  apply sum_congr rfl
  intro n hn
  simp only [residue_one_iff_dvd_pred (mem_Icc.mp hn).1]

lemma cofactorMaxPrefix_one {d : ℕ} (χ : DirichletCharacter ℂ d) :
    cofactorMaxPrefix χ 1 = 1 := by
  apply le_antisymm (by simpa using cofactorMaxPrefix_le χ 1)
  have h := cofactor_prefix_le_max χ 1 1 le_rfl
  simpa using h

/-- At a singleton, the natural density 1/d is not the principal density
1/phi(d). The latter remains exact in `restricted_cofactor_discrepancy`. -/
lemma restricted_cofactor_two_singleton (f : ArithmeticFunction ℝ)
    (hf : ∀ n, ¬Odd n → f n = 0) (N : ℕ) :
    restrictedCofactorWeight f 2 1 0 1 N = restrictedMass f N := by
  simp only [restrictedCofactorWeight,zero_add,Icc_self,sum_singleton,
    Units.val_one,Nat.cast_one,one_mul,restrictedMass]
  apply sum_congr rfl
  intro n hn
  simp only [ZMod.natCast_eq_one_iff_odd]
  by_cases h : Odd n
  · simp only [h,if_true]
  · simp only [h,if_false,hf n h]

lemma restricted_diagonal_natural_error_two (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hodd : ∀ n, ¬Odd n → f n = 0) (N : ℕ) :
    |restrictedCofactorWeight f 2 1 0 1 N-restrictedMass f N/2| =
      restrictedMass f N/2 := by
  rw [restricted_cofactor_two_singleton f hodd N]
  have hm := restrictedMass_nonneg f hf N
  rw [abs_of_nonneg (by linarith)]
  ring

lemma restricted_diagonal_natural_error_lower (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hodd : ∀ n, ¬Odd n → f n = 0)
    (Q N : ℕ) (hQ : 2 ≤ Q) :
    restrictedMass f N/2 ≤
      ∑ d ∈ Icc 1 Q, |restrictedCofactorWeight f d 1 0 1 N-restrictedMass f N/(d : ℝ)| := by
  have hh := single_le_sum
    (f := fun d : ℕ => |restrictedCofactorWeight f d 1 0 1 N-restrictedMass f N/(d : ℝ)|)
    (fun d _ => abs_nonneg _) (mem_Icc.mpr ⟨by decide,hQ⟩ : 2 ∈ Icc 1 Q)
  simpa only [Nat.cast_ofNat,restricted_diagonal_natural_error_two f hf hodd N] using hh

/-- A relative power saving cannot simply be extrapolated to B=1. -/
theorem restricted_diagonal_error_not_small (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hodd : ∀ n, ¬Odd n → f n = 0)
    (Q N : ℕ) (hQ : 2 ≤ Q) (hM : 0 < restrictedMass f N)
    (c : ℝ) (hc : c < 1/2) :
    ¬(∑ d ∈ Icc 1 Q, |restrictedCofactorWeight f d 1 0 1 N-restrictedMass f N/(d : ℝ)|) ≤
      c*restrictedMass f N := by
  have hh := restricted_diagonal_natural_error_lower f hf hodd Q N hQ
  have hcM := mul_lt_mul_of_pos_right hc hM
  intro h
  linarith

/-- The hypotheses of the proved product-level scale bound themselves exclude
a singleton prefix at every positive scale. -/
lemma cofactorScale_singleton_excluded (l m : ℕ) (hl : 1 ≤ l) (hm : 1 ≤ m) :
    ¬cofactorScale l m ≤ 1 := by
  rw [cofactorScale_eq]
  have he : 0 < 256*l*m := by positivity
  exact not_le.mpr (Nat.one_lt_pow he.ne' (by decide))

end Erdos821.AnalyticSieve
