import Submission.RestrictedProductMean
import Submission.RestrictedCofactorDiagonal

/-!
# Relative restricted-weight discrepancy under an explicit mass lower bound

The lower bound on the mass is a hypothesis, not a consequence of character
orthogonality. All constants are uniform in the restricted weight, which
may vary with the scale. This does not remove the cofactor average.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

lemma restricted_relative_error_algebra (K B F N : ℝ) (m : ℕ)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hNF : N ≤ (2 : ℝ)^m*F) :
    K*((2*(m : ℝ))+1)^6/(2 : ℝ)^(2*m)*B*N ≤
      (64*K)*((m : ℝ)+1)^6/(2 : ℝ)^m*B*F := by
  have hpoly : (2*(m : ℝ)+1)^6 ≤ 64*((m : ℝ)+1)^6 := by
    have hh := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2*(m : ℝ)+1 by positivity)
      (show 2*(m : ℝ)+1 ≤ 2*((m : ℝ)+1) by linarith) 6
    simpa only [mul_pow,show (2 : ℝ)^6=64 by norm_num] using hh
  have hh := mul_le_mul
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpoly hK) (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(2*m))) hB)
    hNF hN (by positivity)
  apply hh.trans_eq
  rw [show 2*m=m+m by omega,pow_add]
  field_simp

/-- At doubled scales, an exponentially small ambient density is enough
to retain a relative exponential saving. The mass lower bound is explicit. -/
theorem exists_restricted_relative_power_saving (a b l v t : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hl : 2*a+1 ≤ l) (ht : b+1 ≤ t)
    (hlevel : 2*b+1 ≤ l+t) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ArithmeticFunction ℝ,
      (∀ n, 0 ≤ f n) → (∀ n, f n ≤ vonMangoldt n) → ∀ m B X : ℕ,
      cofactorScale l (2*m) ≤ B → B ≤ cofactorScale v (2*m) → X ≤ cofactorScale t (2*m) →
      (cofactorScale t (2*m) : ℝ) ≤ (2 : ℝ)^m*restrictedMass f X →
      ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
        (∑ d ∈ Icc 1 (cofactorScale b (2*m)), |restrictedCofactorWeight f d (u d) 0 B X-
          (B : ℝ)*restrictedMass f X/(d : ℝ)|) ≤
            K*((m : ℝ)+1)^6/(2 : ℝ)^m*(B : ℝ)*restrictedMass f X := by
  obtain ⟨K,hK,HK⟩ := exists_restricted_product_natural_power_saving a b l v t ha hab hl ht hlevel
  refine ⟨64*K,by positivity,?_⟩
  intro f hf hΛ m B X hB hBup hX hmass u
  have hh := HK f hf hΛ (2*m) B X hB hBup hX u
  have hnorm := restricted_relative_error_algebra K B (restrictedMass f X) (cofactorScale t (2*m)) m
    hK.le (Nat.cast_nonneg _) (Nat.cast_nonneg _) hmass
  apply hh.trans
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hnorm

lemma tendsto_shifted_poly_div_two_pow (d : ℕ) :
    Tendsto (fun m : ℕ => ((m : ℝ)+1)^d/(2 : ℝ)^m) atTop (𝓝 0) := by
  have hh := (tendsto_pow_const_mul_const_pow_of_lt_one d
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1 : ℝ)/2 < 1)).comp (tendsto_add_atTop_nat 1)
  have hh' := hh.const_mul 2
  simp only [mul_zero] at hh'
  apply hh'.congr
  intro m
  simp only [Function.comp_apply,Nat.cast_add,Nat.cast_one,div_pow,one_pow,pow_succ]
  field_simp

/-- Uniform in f, the cofactor prefix, the prime cutoff and all residues.
This requires the stated restricted-mass lower bound at each scale. -/
theorem eventually_restricted_relative_mean (a b l v t : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hl : 2*a+1 ≤ l) (ht : b+1 ≤ t)
    (hlevel : 2*b+1 ≤ l+t) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ f : ArithmeticFunction ℝ,
      (∀ n, 0 ≤ f n) → (∀ n, f n ≤ vonMangoldt n) → ∀ B X : ℕ,
      cofactorScale l (2*m) ≤ B → B ≤ cofactorScale v (2*m) → X ≤ cofactorScale t (2*m) →
      (cofactorScale t (2*m) : ℝ) ≤ (2 : ℝ)^m*restrictedMass f X →
      ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
        (∑ d ∈ Icc 1 (cofactorScale b (2*m)), |restrictedCofactorWeight f d (u d) 0 B X-
          (B : ℝ)*restrictedMass f X/(d : ℝ)|) ≤ η*(B : ℝ)*restrictedMass f X := by
  obtain ⟨K,hK,HK⟩ := exists_restricted_relative_power_saving a b l v t ha hab hl ht hlevel
  have htend := (tendsto_shifted_poly_div_two_pow 6).const_mul K
  simp only [mul_zero] at htend
  filter_upwards [htend.eventually_lt_const hη] with m hm
  intro f hf hΛ B X hB hBup hX hmass u
  have hmain := HK f hf hΛ m B X hB hBup hX hmass u
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hm.le (Nat.cast_nonneg B)) (restrictedMass_nonneg f hf X)
  apply hmain.trans
  simpa only [← mul_div_assoc] using hh

/-- Every set restriction is admitted. The theorem does not supply the
required lower bound for the mass of that set. -/
theorem eventually_set_restricted_relative_mean (a b l v t : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hl : 2*a+1 ≤ l) (ht : b+1 ≤ t)
    (hlevel : 2*b+1 ≤ l+t) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ S : Set ℕ, ∀ B X : ℕ,
      cofactorScale l (2*m) ≤ B → B ≤ cofactorScale v (2*m) → X ≤ cofactorScale t (2*m) →
      (cofactorScale t (2*m) : ℝ) ≤ (2 : ℝ)^m*restrictedMass (mangoldtRestriction S) X →
      ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
        (∑ d ∈ Icc 1 (cofactorScale b (2*m)),
          |restrictedCofactorWeight (mangoldtRestriction S) d (u d) 0 B X-
            (B : ℝ)*restrictedMass (mangoldtRestriction S) X/(d : ℝ)|) ≤
          η*(B : ℝ)*restrictedMass (mangoldtRestriction S) X := by
  filter_upwards [eventually_restricted_relative_mean a b l v t ha hab hl ht hlevel η hη] with m hm
  intro S B X hB hBup hX hmass u
  exact hm (mangoldtRestriction S) (mangoldtRestriction_nonneg S) (mangoldtRestriction_le S)
    B X hB hBup hX hmass u

end Erdos821.AnalyticSieve
