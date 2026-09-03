import Submission.GreedyHigherPromotionTails
import Submission.GreedyPromotionScales

/-! Explicit nonvacuous scales for the four-to-three promotion tail. -/
namespace Erdos773.GreedyHigherPromotionScales
open Finset GreedyHypergraphState GreedyCodegreeDrift GreedyHigherPromotionTails
open GreedyConfigurationTails StoppedGreedyMoments FourUniformRegularization HypergraphDegreeTrim
set_option maxHeartbeats 2500000
set_option exponentiation.threshold 1024
noncomputable section

lemma full_ratio {X D K p : ℝ} (hX : 36 ≤ X) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (hDb : D ≤ X^300) (hKb : K ≤ X^3) (hpb : p ≤ 1/X^97) :
    18*D*K*p/(X^209+1) ≤ 1/X^2 := by
  have hx : 0 < X := by linarith only [hX]
  have hnum : 18*D*K*p ≤ 18*X^300*X^3*(1/X^97) := by gcongr
  have hd := div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ X^209+1)
  have he : 18*X^300*X^3*(1/X^97)/X^209 = 18/X^3 := by field_simp
  apply hd.trans ((div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < X^209)
    (by linarith : X^209 ≤ X^209+1)).trans _)
  rw [he]
  apply (div_le_div_iff₀ (pow_pos hx 3) (pow_pos hx 2)).mpr
  have hb := mul_le_mul_of_nonneg_right (show 18 ≤ X by linarith only [hX]) (sq_nonneg X)
  nlinarith only [hb]

lemma light_ratio {X p : ℝ} (hX : 36 ≤ X) (hpb : p ≤ 1/X^97) :
    3*X^150*p/(X^56+1) ≤ 1/X^2 := by
  have hx : 0 < X := by linarith only [hX]
  have hnum : 3*X^150*p ≤ 3*X^150*(1/X^97) := by gcongr
  have hd := div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ X^56+1)
  have he : 3*X^150*(1/X^97)/X^56 = 3/X^3 := by field_simp
  apply hd.trans ((div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < X^56)
    (by linarith : X^56 ≤ X^56+1)).trans _)
  rw [he]
  apply (div_le_div_iff₀ (pow_pos hx 3) (pow_pos hx 2)).mpr
  have hb := mul_le_mul_of_nonneg_right (show 3 ≤ X by linarith only [hX]) (sq_nonneg X)
  nlinarith only [hb]

lemma heavy_ratio {X D K p : ℝ} (hX : 36 ≤ X) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (hDb : D ≤ X^300) (hKb : K ≤ X^3) (hpb : p ≤ 1/X^97) :
    36*D*K*p/(X^150*(X^59+1)) ≤ 1/X^2 := by
  have hx : 0 < X := by linarith only [hX]
  have hnum : 36*D*K*p ≤ 36*X^300*X^3*(1/X^97) := by gcongr
  have hd := div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ X^150*(X^59+1))
  have hden : X^150*X^59 ≤ X^150*(X^59+1) := by gcongr; linarith
  have he : 36*X^300*X^3*(1/X^97)/(X^150*X^59) = 36/X^3 := by field_simp
  apply hd.trans ((div_le_div_of_nonneg_left (by positivity) (by positivity) hden).trans _)
  rw [he]
  apply (div_le_div_iff₀ (pow_pos hx 3) (pow_pos hx 2)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hX (sq_nonneg X)]

lemma packed_ratio {X D K p : ℝ} (hX : 36 ≤ X) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hp : 0 ≤ p) (hDb : D ≤ X^300) (hKb : K ≤ X^3) (hpb : p ≤ 1/X^97) :
    18*D*K*p^2/(X^112+1) ≤ 1/X^2 := by
  apply le_trans _ (GreedyPromotionScales.ratio_two hX hD hK hp hDb hKb hpb)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hb : 0 ≤ D*K*p^2 := by positivity
  nlinarith only [hb]

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The higher-promotion correction is at most 54m^274 outside a
    superpolynomially small all-prefix event, at the same selection scale
    used for the two-promotion correction. -/
theorem prefix_power_tail {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (u : α) (D K m : ℕ) (hm : 36 ≤ m) (hD : degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (hDb : D ≤ m^300) (hKb : K ≤ m^3)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L) (hp : (n:ℝ)/L ≤ 1/(m:ℝ)^97) :
    expectation H L n (event (prefixBad H u (54*m^274))) ≤
      2*((Fintype.card α:ℝ)+1)*(1/(m:ℝ)^2)^(m^15+1) := by
  have hmR : (36:ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by linarith only [hmR]
  have hm0 : (0:ℝ) < m := by linarith only [hmR]
  have hmNat : 0 < m := by omega
  have hDbR : (D:ℝ) ≤ (m:ℝ)^300 := by exact_mod_cast hDb
  have hKbR : (K:ℝ) ≤ (m:ℝ)^3 := by exact_mod_cast hKb
  have hthresh : 18*K^2*m^209*m^59+36*K^2*m^56*m^112 ≤ 54*m^274 := by
    have hc : 18*K^2*m^209*m^59+36*K^2*m^56*m^112 ≤
        18*m^274+36*m^174 := by
      calc
        _ ≤ 18*(m^3)^2*m^209*m^59+36*(m^3)^2*m^56*m^112 := by gcongr
        _ = _ := by ring
    have hh := Nat.pow_le_pow_right hmNat (by omega : 174 ≤ 274)
    omega
  have ht := prefix_promotion_tail_of_le h4 h2 u D K hD hK L hL n hn
    (m^150) (m^209) (m^56) (m^59) (m^112) (54*m^274) (pow_pos hmNat _) hthresh
  have hp0 : (0:ℝ) ≤ (n:ℝ)/L := by positivity
  have hf := full_ratio hmR (Nat.cast_nonneg K) hp0 hDbR hKbR hp
  have hl := light_ratio hmR hp
  have hh := heavy_ratio hmR (Nat.cast_nonneg K) hp0 hDbR hKbR hp
  have hk := packed_ratio hmR (Nat.cast_nonneg D) (Nat.cast_nonneg K) hp0 hDbR hKbR hp
  have ha : 0 ≤ 1/(m:ℝ)^2 := by positivity
  have hb : 1/(m:ℝ)^2 ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ hm1)
  have hpower (a : ℝ) (ha0 : 0 ≤ a) (hab : a ≤ 1/(m:ℝ)^2) (e : ℕ) (he : 15 ≤ e) :
      a^(m^e+1) ≤ (1/(m:ℝ)^2)^(m^15+1) := by
    apply (pow_le_pow_left₀ ha0 hab _).trans
    exact pow_le_pow_of_le_one ha hb
      (Nat.add_le_add_right (Nat.pow_le_pow_right hmNat he) 1)
  have hf' := hpower _ (by positivity) hf 209 (by omega)
  have hl' := hpower _ (by positivity) hl 56 (by omega)
  have hh' := hpower _ (by positivity) hh 59 (by omega)
  have hk' := hpower _ (by positivity) hk 112 (by omega)
  have hsum := add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hf' (Nat.cast_nonneg (Fintype.card α)))
    (mul_le_mul_of_nonneg_left hl' (Nat.cast_nonneg (Fintype.card α)))) hh') hk'
  push_cast at ht
  apply ht.trans
  nlinarith only [hsum]

/-- All-vertex, all-prefix failure cost is at most 4/m^2 under polynomial
    ambient volume. Early stopping is not excluded by this statement. -/
theorem all_vertex_polynomial_tail {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (D K m A : ℕ) (hm : 36 ≤ m) (hAm : A ≤ m)
    (hV : Fintype.card α ≤ m^A) (hD : ∀ u : α, degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (hDb : D ≤ m^300) (hKb : K ≤ m^3)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L) (hp : (n:ℝ)/L ≤ 1/(m:ℝ)^97) :
    expectation H L n (fun I => ∑ u : α, event (prefixBad H u (54*m^274)) I) ≤ 4/(m:ℝ)^2 := by
  rw [expectation_sum]
  have hs : (∑ u : α, expectation H L n (event (prefixBad H u (54*m^274)))) ≤
      (Fintype.card α:ℝ)*(2*((Fintype.card α:ℝ)+1)*(1/(m:ℝ)^2)^(m^15+1)) := by
    calc
      _ ≤ ∑ _u : α, 2*((Fintype.card α:ℝ)+1)*(1/(m:ℝ)^2)^(m^15+1) := by
        apply sum_le_sum
        intro u _
        exact prefix_power_tail h4 h2 u D K m hm (hD u) hK hDb hKb L hL n hn hp
      _ = _ := by simp
  have hb := GreedyPromotionScales.volume_power_bound m A hm hAm
    (Nat.cast_nonneg (Fintype.card α)) (by exact_mod_cast hV)
  apply hs.trans
  convert mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 2) using 1 <;> ring

#print axioms full_ratio
#print axioms light_ratio
#print axioms heavy_ratio
#print axioms packed_ratio
#print axioms prefix_power_tail
#print axioms all_vertex_polynomial_tail
end
end Erdos773.GreedyHigherPromotionScales
