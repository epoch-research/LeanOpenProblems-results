import Submission.PoolCofactorCompletion

/-!
# Product-half-level pool discrepancy on unit-supported sieve moduli

Small conductors use the short cofactor B; large conductors use D*B.
There is deliberately no requirement that the modulus cutoff be below
that of the arithmetic weight. The saving is relative to ambient mass.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

noncomputable def poolCofactorLogConstant (v : ℕ) : ℝ :=
  (256*(v : ℝ)+4)*(256*(v : ℝ)+1)^2

lemma poolCofactorLogConstant_pos (v : ℕ) : 0 < poolCofactorLogConstant v := by
  unfold poolCofactorLogConstant
  positivity

lemma poolCofactorLogLoss_scale (v m D B : ℕ) (hDB : 1 ≤ D*B)
    (hup : D*B ≤ cofactorScale v m) :
    poolCofactorLogLoss D B ≤ poolCofactorLogConstant v*((m : ℝ)+1)^3 := by
  have hD : 1 ≤ D := by nlinarith
  have hBup : B ≤ cofactorScale v m := (Nat.le_mul_of_pos_left B hD).trans hup
  have h1 := cofactorScale_log_add_two_le v m B hBup
  have h2 : 1+Real.log (D*B : ℕ) ≤ (256*(v : ℝ)+1)*((m : ℝ)+1) := by
    have hh := (log_nat_mono hup).trans (cofactorScale_log_le v m)
    nlinarith only [hh,Nat.cast_nonneg (α := ℝ) m]
  have hlog : 0 ≤ 1+Real.log (D*B : ℕ) := by linarith [Real.log_natCast_nonneg (D*B)]
  have hh := mul_le_mul h1 (pow_le_pow_left₀ hlog h2 2) (sq_nonneg _) (by positivity)
  apply hh.trans_eq
  unfold poolCofactorLogConstant
  ring

lemma pool_cofactor_error_normalize (E C Z D B N F H R T P W : ℝ)
    (hC : 0 ≤ C) (hZ : 0 ≤ Z) (hD : 0 ≤ D) (hN : 0 ≤ N)
    (hF : 0 ≤ F) (hH : 0 ≤ H) (hR : 1 ≤ R) (hT : 1 ≤ T)
    (hE : E ≤ C*Z*H*(F*(1+R*T)+P)) (hFN : F ≤ 6*D*N)
    (hsmall : Z^2*R ≤ B) (hlarge : Z^2*P ≤ W*D*B*N) :
    Z*E ≤ C*D*B*N*H*(12*T+W) := by
  have hRT : 1 ≤ R*T := one_le_mul_of_one_le_of_one_le hR hT
  have h1 : F*(1+R*T) ≤ F*(2*R*T) :=
    mul_le_mul_of_nonneg_left (by linarith) hF
  have h2 := mul_le_mul hFN hsmall (mul_nonneg (sq_nonneg Z) (by linarith)) (by positivity)
  have h3 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ 2*T by positivity)
  have h4 := mul_le_mul_of_nonneg_left h1 (sq_nonneg Z)
  have hs : Z^2*(F*(1+R*T)) ≤ 12*D*B*N*T := by nlinarith only [h3,h4]
  have hh := mul_le_mul_of_nonneg_left (_root_.add_le_add hs hlarge) (mul_nonneg hC hH)
  have he := mul_le_mul_of_nonneg_left hE hZ
  nlinarith only [hh,he]

noncomputable def poolCofactorErrorConstant (a b v t : ℕ) : ℝ :=
  (256*(b : ℝ)+1)*(12*(256*(a : ℝ)+1)+
    poolCofactorLogConstant v*cofactorProductMeanConstant b v t)

lemma poolCofactorErrorConstant_pos (a b v t : ℕ) :
    0 < poolCofactorErrorConstant a b v t := by
  have := cofactorProductMeanConstant_nonneg b v t
  have := (poolCofactorLogConstant_pos v).le
  unfold poolCofactorErrorConstant
  positivity

lemma pool_cofactor_polynomial_bound (a b v t m D B : ℕ)
    (hDB : 1 ≤ D*B) (hup : D*B ≤ cofactorScale v m) :
    (harmonic (cofactorScale b m) : ℝ)*(12*(1+Real.log (cofactorScale a m))+
      poolCofactorLogLoss D B*cofactorProductMeanConstant b v t*((m : ℝ)+1)^3) ≤
        poolCofactorErrorConstant a b v t*((m : ℝ)+1)^7 := by
  have hm : 1 ≤ (m : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hT : 1+Real.log (cofactorScale a m) ≤ (256*(a : ℝ)+1)*((m : ℝ)+1) := by
    nlinarith only [cofactorScale_log_le a m,Nat.cast_nonneg (α := ℝ) m]
  have hL := poolCofactorLogLoss_scale v m D B hDB hup
  have hp : (m : ℝ)+1 ≤ ((m : ℝ)+1)^6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hm (by decide : 1 ≤ 6)
  have h1 := mul_le_mul_of_nonneg_left (hT.trans
    (mul_le_mul_of_nonneg_left hp (by positivity))) (show (0 : ℝ) ≤ 12 by norm_num)
  have h2 := mul_le_mul_of_nonneg_right hL
    (mul_nonneg (cofactorProductMeanConstant_nonneg b v t) (by positivity : 0 ≤ ((m : ℝ)+1)^3))
  have hbr : 12*(1+Real.log (cofactorScale a m))+
      poolCofactorLogLoss D B*cofactorProductMeanConstant b v t*((m : ℝ)+1)^3 ≤
        (12*(256*(a : ℝ)+1)+poolCofactorLogConstant v*cofactorProductMeanConstant b v t)*
          ((m : ℝ)+1)^6 := by nlinarith only [h1,h2]
  have hbr0 : 0 ≤ 12*(1+Real.log (cofactorScale a m))+
      poolCofactorLogLoss D B*cofactorProductMeanConstant b v t*((m : ℝ)+1)^3 := by
    have := Real.log_natCast_nonneg (cofactorScale a m)
    have := poolCofactorLogLoss_nonneg D B
    have := cofactorProductMeanConstant_nonneg b v t
    positivity
  have hh := mul_le_mul (cofactorScale_harmonic_le b m) hbr hbr0 (by positivity)
  apply hh.trans_eq
  unfold poolCofactorErrorConstant
  ring

/-- No hypothesis `b+1 ≤ t` is needed: exact unit-supported lifting removes
that obstruction. The bound is uniform in the two supports. -/
theorem exists_pool_unit_natural_power_saving (a b s l v t : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hs : 2*a+1 ≤ s)
    (hl : 1 ≤ l) (ht : 1 ≤ t) (hlevel : 2*b+1 ≤ l+t) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ArithmeticFunction ℝ,
      (∀ n, 0 ≤ f n) → (∀ n, f n ≤ vonMangoldt n) →
      ∀ m D B X : ℕ, cofactorScale s m ≤ B →
        cofactorScale l m ≤ D*B → D*B ≤ cofactorScale v m → X ≤ cofactorScale t m →
      ∀ P S : Finset ℕ, P ⊆ Icc 1 D → S ⊆ Icc 1 (cofactorScale b m) →
      ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
      (∀ d ∈ S, ∀ c ∈ P, c.Coprime d) →
      (∀ d ∈ S, ∀ n ∈ Icc 1 X, f n ≠ 0 → n.Coprime d) →
      (∑ d ∈ S, |poolCofactorWeight f P d (u d) 0 B X-
        (P.card : ℝ)*(B : ℝ)*restrictedMass f X/(d : ℝ)|) ≤
          K*((m : ℝ)+1)^7/(2 : ℝ)^m*((D*B : ℕ) : ℝ)*(cofactorScale t m : ℝ) := by
  let ε : ℝ := 1/(256*(b : ℝ))
  have hb : 1 ≤ b := ha.trans hab
  obtain ⟨C,hC,HC⟩ := exists_pool_unit_natural_mean_bound ε (by dsimp [ε]; positivity)
  refine ⟨C*poolCofactorErrorConstant a b v t,
    mul_pos hC (poolCofactorErrorConstant_pos a b v t),?_⟩
  intro f hf hΛ m D B X hB hDB hDBup hX P S hP hS u hunitP hunit
  let E := ∑ d ∈ S, |poolCofactorWeight f P d (u d) 0 B X-
    (P.card : ℝ)*(B : ℝ)*restrictedMass f X/(d : ℝ)|
  let Z : ℝ := (2 : ℝ)^m
  let N : ℝ := cofactorScale t m
  let R : ℝ := (cofactorScale a m : ℝ)*Real.sqrt (cofactorScale a m)
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hR : 1 ≤ R := by
    have h := cofactorScale_pos a m
    have hR1 : (1 : ℝ) ≤ cofactorScale a m := by exact_mod_cast h
    have hroot : (1 : ℝ) ≤ Real.sqrt (cofactorScale a m) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hR1
    exact one_le_mul_of_one_le_of_one_le hR1 hroot
  have hmain := HC f hf P S (cofactorScale b m) (cofactorScale a m) B X hS u hunitP hunit
  rw [show ε=1/(256*(b : ℝ)) from rfl,cofactorScale_rpow b m hb] at hmain
  have hsmall := (cofactorScale_small_saving a s m hs).trans
    (show (cofactorScale s m : ℝ) ≤ B by exact_mod_cast hB)
  have hlarge := cofactorScale_pool_primitive_saving f hf hΛ P D a b l v t m B X
    hP ha hab hl ht hlevel hDB hDBup hX
  have hcard : (P.card : ℝ) ≤ D := by
    have hh := card_le_card hP
    simp only [Nat.card_Icc,Nat.add_sub_cancel] at hh
    exact_mod_cast hh
  have hmass : restrictedMass f X ≤ 6*N :=
    ((restrictedMass_le_mangoldt f hΛ X).trans (Erdos821.mangoldtSum_le_six_mul X)).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hX) (by norm_num))
  have hF : (P.card : ℝ)*restrictedMass f X ≤ 6*(D : ℝ)*N := by
    have hh := mul_le_mul hcard hmass (restrictedMass_nonneg f hf X) (Nat.cast_nonneg D)
    convert hh using 1; ring
  have hnorm := pool_cofactor_error_normalize E C Z D B N
    ((P.card : ℝ)*restrictedMass f X) (harmonic (cofactorScale b m)) R
    (1+Real.log (cofactorScale a m))
    (primitivePoolCofactorMean f (Ioc (cofactorScale a m) (cofactorScale b m)) P B X)
    (poolCofactorLogLoss D B*cofactorProductMeanConstant b v t*((m : ℝ)+1)^3)
    hC.le hZ.le (Nat.cast_nonneg D) (Nat.cast_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (restrictedMass_nonneg f hf X)) (harmonic_natCast_nonneg _) hR
    (by linarith [Real.log_natCast_nonneg (cofactorScale a m)])
    (by convert hmain using 1; dsimp [E,Z,R]; ring) hF
    (by convert hsmall using 1; dsimp [Z,R]; ring)
    (by convert hlarge using 1; push_cast; dsimp [Z,N]; ring)
  have hpoly := mul_le_mul_of_nonneg_left
    (pool_cofactor_polynomial_bound a b v t m D B ((cofactorScale_pos l m).trans_le hDB) hDBup)
    (show 0 ≤ C*(D : ℝ)*(B : ℝ)*N by dsimp [N]; positivity)
  have hscaled : Z*E ≤ C*(D : ℝ)*(B : ℝ)*N*poolCofactorErrorConstant a b v t*((m : ℝ)+1)^7 := by
    have hh := hnorm.trans (by convert hpoly using 1; ring)
    convert hh using 1; ring
  change E ≤ C*poolCofactorErrorConstant a b v t*((m : ℝ)+1)^7/Z*((D*B : ℕ) : ℝ)*N
  apply (mul_le_mul_iff_right₀ hZ).mp
  apply hscaled.trans_eq
  push_cast
  field_simp

end Erdos821.AnalyticSieve
