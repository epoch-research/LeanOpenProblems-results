import Submission.GreedyPromotionTails

/-! A concrete nonvacuous power regime for the nonlinear two-promotion tail. -/
namespace Erdos773.GreedyPromotionScales
open Finset GreedyHypergraphState GreedyCodegreeDrift GreedyPromotionTails
open GreedyConfigurationTails StoppedGreedyMoments FourUniformRegularization HypergraphDegreeTrim
set_option maxHeartbeats 2500000
noncomputable section

lemma ratio_two {X D K p : ℝ} (hX : 36 ≤ X) (_hD : 0 ≤ D) (hK : 0 ≤ K)
    (hp : 0 ≤ p) (hDb : D ≤ X^300) (hKb : K ≤ X^3) (hpb : p ≤ 1/X^97) :
    36*D*K*p^2/(X^112+1) ≤ 1/X^2 := by
  have hx : 0 < X := by linarith only [hX]
  have hnum : 36*D*K*p^2 ≤ 36*X^300*X^3*(1/X^97)^2 := by gcongr
  have hdiv := div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ X^112+1)
  have hden : 36*X^300*X^3*(1/X^97)^2/(X^112+1) ≤
      36*X^300*X^3*(1/X^97)^2/X^112 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have he : 36*X^300*X^3*(1/X^97)^2/X^112 = 36/X^3 := by field_simp
  apply hdiv.trans (hden.trans _)
  rw [he]
  apply (div_le_div_iff₀ (pow_pos hx 3) (pow_pos hx 2)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hX (sq_nonneg X)]

lemma ratio_three {X D K p : ℝ} (hX : 36 ≤ X) (_hD : 0 ≤ D) (hK : 0 ≤ K)
    (hp : 0 ≤ p) (hDb : D ≤ X^300) (hKb : K ≤ X^3) (hpb : p ≤ 1/X^97) :
    36*D*K*p^3/(X^15+1) ≤ 1/X^2 := by
  have hx : 0 < X := by linarith only [hX]
  have hnum : 36*D*K*p^3 ≤ 36*X^300*X^3*(1/X^97)^3 := by gcongr
  have hdiv := div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ X^15+1)
  have hden : 36*X^300*X^3*(1/X^97)^3/(X^15+1) ≤
      36*X^300*X^3*(1/X^97)^3/X^15 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have he : 36*X^300*X^3*(1/X^97)^3/X^15 = 36/X^3 := by field_simp
  apply hdiv.trans (hden.trans _)
  rw [he]
  apply (div_le_div_iff₀ (pow_pos hx 3) (pow_pos hx 2)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hX (sq_nonneg X)]

lemma volume_power_bound {V : ℝ} (m A : ℕ) (hm : 36 ≤ m) (hAm : A ≤ m)
    (hV0 : 0 ≤ V) (hV : V ≤ (m:ℝ)^A) :
    V*(V+1)*(1/(m:ℝ)^2)^(m^15+1) ≤ 2/(m:ℝ)^2 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have ha : 0 ≤ 1/(m:ℝ)^2 := by positivity
  have hb : 1/(m:ℝ)^2 ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ hm1)
  have hmpow : m ≤ m^15 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < m) (by omega : 1 ≤ 15)
  have hp := pow_le_pow_of_le_one ha hb (Nat.add_le_add_right (hAm.trans hmpow) 1)
  have hV1 : 1 ≤ (m:ℝ)^A := one_le_pow₀ hm1
  have hcoef : V*(V+1) ≤ 2*((m:ℝ)^A)^2 := by
    have hh : V*(V+1) ≤ (m:ℝ)^A*((m:ℝ)^A+1) := by gcongr
    nlinarith only [hh,mul_le_mul_of_nonneg_left hV1 (pow_nonneg hm0.le A)]
  have he : (((m:ℝ)^2)^A) = ((m:ℝ)^A)^2 := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
  calc
    _ ≤ 2*((m:ℝ)^A)^2*(1/(m:ℝ)^2)^(A+1) :=
      mul_le_mul hcoef hp (by positivity) (by positivity)
    _ = _ := by rw [div_pow,one_pow,pow_succ ((m:ℝ)^2) A,he]; field_simp

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- With D<=m^300, K<=m^3 and selection ratio p<=m^-97, a local
    promotion error above 288m^133 has a superpolynomially small prefix tail.
    No lower bound on the stopped process's running time is assumed. -/
theorem prefix_power_tail {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (u : α) (D K m : ℕ) (hm : 36 ≤ m) (hD : degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (hDb : D ≤ m^300) (hKb : K ≤ m^3)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L) (hp : (n:ℝ)/L ≤ 1/(m:ℝ)^97) :
    expectation H L n (event (prefixBad H u (288*m^133))) ≤
      ((Fintype.card α:ℝ)+1)*(1/(m:ℝ)^2)^(m^15+1) := by
  have hmR : (36:ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by linarith only [hmR]
  have hm0 : (0:ℝ) < m := by linarith only [hmR]
  have hDbR : (D:ℝ) ≤ (m:ℝ)^300 := by exact_mod_cast hDb
  have hKbR : (K:ℝ) ≤ (m:ℝ)^3 := by exact_mod_cast hKb
  have hthresh : 288*K^2*m^112*m^15 ≤ 288*m^133 := by
    calc
      _ ≤ 288*(m^3)^2*m^112*m^15 := by gcongr
      _ = _ := by ring
  have ht := prefix_promotion_tail_of_le h4 h2 u D K hD hK L hL n hn
    (m^112) (m^15) (288*m^133) hthresh
  have htwo := ratio_two hmR (Nat.cast_nonneg D) (Nat.cast_nonneg K)
    (by positivity : 0 ≤ (n:ℝ)/L) hDbR hKbR hp
  have hthree := ratio_three hmR (Nat.cast_nonneg D) (Nat.cast_nonneg K)
    (by positivity : 0 ≤ (n:ℝ)/L) hDbR hKbR hp
  have ha : 0 ≤ 1/(m:ℝ)^2 := by positivity
  have hb : 1/(m:ℝ)^2 ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact one_le_pow₀ hm1
  have he : m^15+1 ≤ m^112+1 := by
    exact Nat.add_le_add_right (Nat.pow_le_pow_right (by omega : 0 < m) (by omega)) 1
  have hp2 := pow_le_pow_left₀ (by positivity : 0 ≤ 36*(D:ℝ)*K*((n:ℝ)/L)^2/((m:ℝ)^112+1)) htwo (m^112+1)
  have hp3 := pow_le_pow_left₀ (by positivity : 0 ≤ 36*(D:ℝ)*K*((n:ℝ)/L)^3/((m:ℝ)^15+1)) hthree (m^15+1)
  have hp2' := hp2.trans (pow_le_pow_of_le_one ha hb he)
  push_cast at ht
  have hh := add_le_add (mul_le_mul_of_nonneg_left hp2' (Nat.cast_nonneg (Fintype.card α))) hp3
  apply ht.trans
  nlinarith only [hh]

/-- Union cost over every designated vertex, still controlling all prefixes. -/
theorem all_vertex_power_tail {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (D K m : ℕ) (hm : 36 ≤ m) (hD : ∀ u : α, degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (hDb : D ≤ m^300) (hKb : K ≤ m^3)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L) (hp : (n:ℝ)/L ≤ 1/(m:ℝ)^97) :
    expectation H L n (fun I => ∑ u : α, event (prefixBad H u (288*m^133)) I) ≤
      (Fintype.card α:ℝ)*((Fintype.card α:ℝ)+1)*(1/(m:ℝ)^2)^(m^15+1) := by
  rw [expectation_sum]
  calc
    _ ≤ ∑ _u : α, ((Fintype.card α:ℝ)+1)*(1/(m:ℝ)^2)^(m^15+1) := by
      apply sum_le_sum
      intro u _
      exact prefix_power_tail h4 h2 u D K m hm (hD u) hK hDb hKb L hL n hn hp
    _ = _ := by simp [mul_assoc]

/-- Under a polynomial volume bound, the total all-vertex prefix error
    probability is at most 2/m^2. -/
theorem all_vertex_polynomial_tail {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (D K m A : ℕ) (hm : 36 ≤ m) (hAm : A ≤ m)
    (hV : Fintype.card α ≤ m^A) (hD : ∀ u : α, degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (hDb : D ≤ m^300) (hKb : K ≤ m^3)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L) (hp : (n:ℝ)/L ≤ 1/(m:ℝ)^97) :
    expectation H L n (fun I => ∑ u : α, event (prefixBad H u (288*m^133)) I) ≤
      2/(m:ℝ)^2 := by
  apply (all_vertex_power_tail h4 h2 D K m hm hD hK hDb hKb L hL n hn hp).trans
  exact volume_power_bound m A hm hAm (Nat.cast_nonneg _) (by exact_mod_cast hV)

#print axioms ratio_two
#print axioms ratio_three
#print axioms volume_power_bound
#print axioms prefix_power_tail
#print axioms all_vertex_power_tail
#print axioms all_vertex_polynomial_tail
end
end Erdos773.GreedyPromotionScales
