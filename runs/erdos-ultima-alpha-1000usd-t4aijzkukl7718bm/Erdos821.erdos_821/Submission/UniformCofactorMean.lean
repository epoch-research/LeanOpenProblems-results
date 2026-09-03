import Submission.CofactorNaturalMean
import Submission.UniformRoughHalfMean

/-!
# Cofactor progression means with arbitrary initial prime cutoffs

The error is measured at a fixed ambient scale N, while the Mangoldt
sum and the progression count may stop at any X <= N.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

lemma primitive_interval_mean_blocks_cutoff (a n t m X : ℕ) (hXN : X ≤ progressionScaleN (t*m)) (ha : 1 ≤ a) (ht : 22 ≤ t)
    (hlevel : 2*(a+n)+5 ≤ t) :
    primitivePoolMean (Ioc (progressionScaleN (a*m)) (progressionScaleN ((a+n)*m)))
      X ≤
        (n : ℝ)*(wideMeanConstant t : ℝ)*((m : ℝ)+1)^5*(2 : ℝ)^((64*t-1)*m) := by
  induction n with
  | zero => simp [primitivePoolMean]
  | succ n ih =>
    have hlow := ih (by omega : 2*(a+n)+5 ≤ t)
    have hmid := wide_primitive_mean_bound_cutoff
      (Ioc (progressionScaleN ((a+n)*m)) (progressionScaleN ((a+(n+1))*m)))
      (a+n) (a+(n+1)) t m X hXN (by omega) (by omega) (by omega) (by omega) (by omega) (by
        intro d hd
        have hh := mem_Ioc.mp hd
        have hone : 1 ≤ progressionScaleN ((a+n)*m) := by unfold progressionScaleN; exact Nat.one_le_pow _ _ (by decide)
        exact ⟨by omega,hh.1.le,hh.2⟩)
    have h1 : progressionScaleN (a*m) ≤ progressionScaleN ((a+n)*m) :=
      progressionScaleN_monotone (Nat.mul_le_mul_right m (by omega))
    have h2 : progressionScaleN ((a+n)*m) ≤ progressionScaleN ((a+(n+1))*m) :=
      progressionScaleN_monotone (Nat.mul_le_mul_right m (by omega))
    have he : primitivePoolMean
        (Ioc (progressionScaleN (a*m)) (progressionScaleN ((a+(n+1))*m))) X =
        primitivePoolMean (Ioc (progressionScaleN (a*m)) (progressionScaleN ((a+n)*m))) X+
        primitivePoolMean (Ioc (progressionScaleN ((a+n)*m)) (progressionScaleN ((a+(n+1))*m))) X := by
      unfold primitivePoolMean
      rw [← Finset.Ioc_union_Ioc_eq_Ioc h1 h2,sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
    rw [he]
    have hh := _root_.add_le_add hlow hmid
    convert hh using 1; push_cast; ring

/-- The interval can start at any positive fixed power, however small. The
upper endpoint remains strictly below the square-root distribution level. -/
theorem primitive_full_interval_mean_bound_cutoff (a b t m X : ℕ) (hXN : X ≤ progressionScaleN (t*m)) (ha : 1 ≤ a) (hab : a ≤ b)
    (ht : 22 ≤ t) (hlevel : 2*b+5 ≤ t) :
    primitivePoolMean (Ioc (progressionScaleN (a*m)) (progressionScaleN (b*m)))
      X ≤
        ((b-a : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*((m : ℝ)+1)^5*(2 : ℝ)^((64*t-1)*m) := by
  have he : a+(b-a)=b := Nat.add_sub_of_le hab
  simpa only [he] using primitive_interval_mean_blocks_cutoff a (b-a) t m X hXN ha ht (by omega)


lemma cofactorScale_primitive_saving_cutoff (a b t m X : ℕ) (hXN : X ≤ cofactorScale t m) (ha : 1 ≤ a) (hab : a ≤ b)
    (ht : 22 ≤ t) (hlevel : 2*b+5 ≤ t) :
    ((2 : ℝ)^m)^2*primitivePoolMean (Ioc (cofactorScale a m) (cofactorScale b m)) X ≤
      (((b-a : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*1024*((m : ℝ)+1)^5)*(cofactorScale t m : ℝ) := by
  have hh := primitive_full_interval_mean_bound_cutoff a b t (4*m) X hXN ha hab ht hlevel
  have hp : ((2 : ℝ)^m)^2*(2 : ℝ)^((64*t-1)*(4*m)) ≤ cofactorScale t m := by
    rw [cofactorScale_cast,← pow_mul,← pow_add]
    apply pow_le_pow_right₀ (by norm_num)
    have he := Nat.sub_add_cancel (show 1 ≤ 64*t by omega)
    nlinarith only [congrArg (fun z : ℕ => z*m) he,Nat.zero_le m]
  have hpoly : ((4*m : ℕ) : ℝ)+1 ≤ 4*((m : ℝ)+1) := by push_cast; linarith
  calc
    _ ≤ ((2 : ℝ)^m)^2*(((b-a : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*
        (((4*m : ℕ) : ℝ)+1)^5*(2 : ℝ)^((64*t-1)*(4*m))) := by
      exact mul_le_mul_of_nonneg_left hh (by positivity)
    _ = (((b-a : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*(((4*m : ℕ) : ℝ)+1)^5)*
        (((2 : ℝ)^m)^2*(2 : ℝ)^((64*t-1)*(4*m))) := by ring
    _ ≤ (((b-a : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*(4*((m : ℝ)+1))^5)*(cofactorScale t m : ℝ) := by gcongr
    _ = _ := by ring


/-- A power-saving all-modulus error, uniform in interval endpoints and residues. -/
theorem exists_cofactor_all_modulus_power_saving_cutoff (a b t l : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ b) (ht : 22 ≤ t) (hlevel : 2*b+5 ≤ t) (hl : 2*a+1 ≤ l) :
    ∃ K : ℝ, 0 < K ∧ ∀ m A B X : ℕ, X ≤ cofactorScale t m → cofactorScale l m ≤ B-A →
      ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
        (∑ d ∈ Icc 1 (cofactorScale b m), |cofactorCongruenceWeight d (u d) A B X-
          cofactorPrincipalMain d A B X|) ≤
            K*((m : ℝ)+1)^6/(2 : ℝ)^m*((B-A : ℕ) : ℝ)*(cofactorScale t m : ℝ) := by
  let ε : ℝ := 1/(256*(b : ℝ))
  have hb : 1 ≤ b := ha.trans hab
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C,hC,HC⟩ := exists_cofactor_all_modulus_mean_bound ε hε
  let D : ℝ := 6*(256*(b : ℝ)+1)*(256*(a : ℝ)+1)+
    (256*(b : ℝ)+1)*((b-a : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*1024+(256*(t : ℝ))*(256*(b : ℝ))
  refine ⟨C*D,mul_pos hC (by dsimp [D]; positivity),?_⟩
  intro m A B X hXN hAB u
  let E := ∑ d ∈ Icc 1 (cofactorScale b m), |cofactorCongruenceWeight d (u d) A B X-
    cofactorPrincipalMain d A B X|
  let L : ℝ := (B-A : ℕ)
  let N : ℝ := cofactorScale t m
  let Z : ℝ := (2 : ℝ)^m
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hmain0 := HC (cofactorScale b m) (cofactorScale a m) A B X u
  have hlogX : (Nat.log 2 X : ℝ) ≤ Nat.log 2 (cofactorScale t m) := by
    exact_mod_cast Nat.log_mono_right hXN
  have hmain : E ≤ C*(cofactorScale b m : ℝ)^ε*
      (mangoldtSum X*(harmonic (cofactorScale b m) : ℝ)*(cofactorScale a m : ℝ)*
        (Real.sqrt (cofactorScale a m)*(1+Real.log (cofactorScale a m)))+
        L*(harmonic (cofactorScale b m) : ℝ)*primitivePoolMean
          (Ioc (cofactorScale a m) (cofactorScale b m)) X+
        L*(cofactorScale b m : ℝ)*(Nat.log 2 (cofactorScale t m) : ℝ)*Real.log (cofactorScale b m)) := by
    apply hmain0.trans
    gcongr
  rw [show ε=1/(256*(b : ℝ)) from rfl,cofactorScale_rpow b m hb] at hmain
  have hsmall := (cofactorScale_small_saving a l m hl).trans (show (cofactorScale l m : ℝ) ≤ L by dsimp [L]; exact_mod_cast hAB)
  have hnorm := cofactor_error_normalize E C Z L N (mangoldtSum X)
    (harmonic (cofactorScale b m)) ((cofactorScale a m : ℝ)*Real.sqrt (cofactorScale a m))
    (1+Real.log (cofactorScale a m)) (primitivePoolMean (Ioc (cofactorScale a m) (cofactorScale b m)) X)
    (cofactorScale b m) (Nat.log 2 (cofactorScale t m)) (Real.log (cofactorScale b m))
    (((b-a : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*1024*((m : ℝ)+1)^5)
    hC.le hZ.le hL hN (mangoldtSum_nonneg _) (harmonic_natCast_nonneg _) (by positivity)
    (by linarith [Real.log_natCast_nonneg (cofactorScale a m)]) (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    (by convert hmain using 1; dsimp [E,L,N,Z]; ring)
    ((Erdos821.mangoldtSum_le_six_mul X).trans (by dsimp [N]; exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hXN) (by norm_num))) (by convert hsmall using 1; dsimp [Z]; ring)
    (cofactorScale_primitive_saving_cutoff a b t m X hXN ha hab ht hlevel) (cofactorScale_lift_saving b t m (by omega))
  have hpoly := mul_le_mul_of_nonneg_left (cofactor_polynomial_error_bound a b t m)
    (show 0 ≤ C*L*N by positivity)
  have hscaled : Z*E ≤ C*L*N*D*((m : ℝ)+1)^6 := by
    have hh := hnorm.trans hpoly
    convert hh using 1; dsimp [D]; ring
  change E ≤ (C*D*((m : ℝ)+1)^6/Z)*L*N
  apply (mul_le_mul_iff_right₀ hZ).mp
  apply hscaled.trans_eq
  field_simp


end Erdos821.AnalyticSieve
