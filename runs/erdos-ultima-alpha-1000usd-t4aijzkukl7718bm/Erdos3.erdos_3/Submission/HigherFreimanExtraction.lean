import Submission.HigherFreimanRestriction

/-! Polynomial higher-order Freiman-frequency extraction from large U³. -/
namespace Erdos3HigherFreimanExtraction
open Finset Erdos3FrequencyGraph Erdos3HigherFreimanRestriction
  Erdos3FiniteUniformity Erdos3FiniteFourier
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 4500000

variable {G : Type*} [AddCommGroup G] [Fintype G]
section
variable [DecidableEq G]

lemma higher_vertical_times_graph_le (n : ℕ) (H : Finset G) (ξ : G → AddChar G ℂ) :
    (verticalN n H ξ).card*(frequencyGraph H ξ).card ≤
      ((n+1) • frequencyGraph H ξ-n • frequencyGraph H ξ).card := by
  let Γ := frequencyGraph H ξ
  let V := verticalN n H ξ
  let f : (AddChar G ℂ) × (G × AddChar G ℂ) → G × AddChar G ℂ := fun p ↦ (0,p.1)+p.2
  rw [← card_product]
  apply card_le_card_of_injOn f
  · intro p hp
    obtain ⟨hpV,hpΓ⟩ := mem_product.mp hp
    have hv : (0,p.1) ∈ n • Γ-n • Γ := by
      simpa only [verticalN,mem_filter,mem_univ,true_and,Γ,V] using hpV
    obtain ⟨a,ha,b,hb,hab⟩ := mem_sub.mp hv
    have ha' : a+p.2 ∈ (n+1) • Γ := by
      have hh := add_mem_add ha hpΓ
      simpa only [add_nsmul,one_nsmul] using hh
    have hb' : b ∈ n • Γ := hb
    apply mem_sub.mpr
    refine ⟨a+p.2,ha',b,hb',?_⟩
    dsimp [f]
    rw [← hab]
    abel
  · intro p hp q hq he
    have hpΓ := (mem_product.mp hp).2
    have hqΓ := (mem_product.mp hq).2
    have hpξ := ((mem_frequencyGraph H ξ p.2).mp hpΓ).2
    have hqξ := ((mem_frequencyGraph H ξ q.2).mp hqΓ).2
    have hfst : p.2.1 = q.2.1 := by simpa only [f,Prod.fst_add,zero_add] using congrArg Prod.fst he
    have hΓ : p.2 = q.2 := Prod.ext hfst (by rw [hpξ,hqξ,hfst])
    have hchar : p.1 = q.1 := by
      have hh := congrArg Prod.snd he
      change p.1+p.2.2 = q.1+q.2.2 at hh
      rw [hΓ] at hh
      exact add_right_cancel hh
    exact Prod.ext hchar hΓ

/-- The vertical 2n-term obstructions have size at most K^(2n+1). -/
theorem higher_vertical_card_le_ratio (n : ℕ) (H : Finset G) (hH : H.Nonempty) (ξ : G → AddChar G ℂ) :
    ((verticalN n H ξ).card : ℝ) ≤
      (((frequencyGraph H ξ-frequencyGraph H ξ).card : ℝ)/(H.card : ℝ))^(2*n+1) := by
  let Γ := frequencyGraph H ξ
  have hΓ : Γ.Nonempty := by
    obtain ⟨h,hh⟩ := hH
    exact ⟨(h,ξ h),(mem_frequencyGraph H ξ _).mpr ⟨hh,rfl⟩⟩
  have hp := pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub hΓ Γ (n+1) n
  have hpR : (((n+1) • Γ-n • Γ).card : ℝ) ≤
      (((Γ-Γ).card : ℝ)/(Γ.card : ℝ))^(2*n+1)*(Γ.card : ℝ) := by
    have hh := (NNRat.cast_le (K := ℝ)).mpr hp
    simpa only [NNRat.cast_mul,NNRat.cast_pow,NNRat.cast_div,NNRat.cast_natCast,show n+1+n = 2*n+1 by omega] using hh
  have hv : ((verticalN n H ξ).card : ℝ)*(Γ.card : ℝ) ≤
      (((n+1) • Γ-n • Γ).card : ℝ) := by
    exact_mod_cast higher_vertical_times_graph_le n H ξ
  have hpos : (0 : ℝ) < Γ.card := by exact_mod_cast hΓ.card_pos
  have hh := hv.trans hpR
  have hh' : ((verticalN n H ξ).card : ℝ) ≤ (((Γ-Γ).card : ℝ)/(Γ.card : ℝ))^(2*n+1) := by
    nlinarith only [hh,hpos]
  simpa only [Γ,card_frequencyGraph] using hh'

/-- Every fixed-order Freiman restriction costs a polynomial in the difference ratio. -/
theorem small_difference_higher_restriction (n : ℕ) (hn : 0 < n) (H : Finset G) (hH : H.Nonempty)
    (ξ : G → AddChar G ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hsmall : ((frequencyGraph H ξ-frequencyGraph H ξ).card : ℝ) ≤ K*(H.card : ℝ)) :
    ∃ H' ⊆ H, (H.card : ℝ) ≤ (2*(K^(2*n+1)+1))^(restrictionExponent n)*(H'.card : ℝ) ∧ IsAddFreimanHom n (H' : Set G) Set.univ ξ := by
  have hpos : (0 : ℝ) < H.card := by exact_mod_cast hH.card_pos
  have hratio : ((frequencyGraph H ξ-frequencyGraph H ξ).card : ℝ)/(H.card : ℝ) ≤ K :=
    (div_le_iff₀ hpos).mpr hsmall
  have hv := (higher_vertical_card_le_ratio n H hH ξ).trans
    (pow_le_pow_left₀ (by positivity) hratio (2*n+1))
  obtain ⟨H',hsub,hcard,hFreiman⟩ := exists_higher_freiman_restriction n hn H ξ
  refine ⟨H',hsub,?_,hFreiman⟩
  have hcardR : (H.card : ℝ) ≤ (2*(((verticalN n H ξ).card : ℝ)+1))^(restrictionExponent n)*(H'.card : ℝ) := by
    exact_mod_cast hcard
  have hcost : (2*(((verticalN n H ξ).card : ℝ)+1))^(restrictionExponent n) ≤ (2*(K^(2*n+1)+1))^(restrictionExponent n) := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) (restrictionExponent n)
  exact hcardR.trans (mul_le_mul_of_nonneg_right hcost (by positivity))

end

/-- A one-bounded function with large U³ has a polynomially large family of
large derivative Fourier coefficients whose frequency assignment is an exact
Freiman homomorphism of any prescribed positive order. All losses are explicit. -/
theorem large_U3_higher_freiman_graph (n : ℕ) (hn : 0 < n) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ H : Finset G, ∃ ξ : G → AddChar G ℂ,
      H.Nonempty ∧ IsAddFreimanHom n (H : Set G) Set.univ ξ ∧
      (∀ h ∈ H, δ/2 ≤ ‖hat (derivative f h) (ξ h)‖^2) ∧
      δ^5/256*(Fintype.card G : ℝ) ≤
        (2*(((2 : ℝ)^65/δ^41)^(2*n+1)+1))^(restrictionExponent n)*(H.card : ℝ) := by
  obtain ⟨H₀,ξ,hsize,hcoef,hdiff⟩ := large_U3_small_difference_graph f hf hδ hU
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hH₀ : H₀.Nonempty := by
    apply card_pos.mp
    have hh : (0 : ℝ) < H₀.card := (by positivity : 0 < δ^5/256*(Fintype.card G : ℝ)).trans_le hsize
    exact_mod_cast hh
  let K : ℝ := (2 : ℝ)^65/δ^41
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsmall : ((frequencyGraph H₀ ξ-frequencyGraph H₀ ξ).card : ℝ) ≤ K*(H₀.card : ℝ) := by
    dsimp [K]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos hδ 41)).mpr
    have hh := mul_le_mul_of_nonneg_left hdiff (by positivity : 0 ≤ δ^5)
    norm_num at hh ⊢
    nlinarith only [hh,hsize]
  obtain ⟨H,hsub,hcard,hFreiman⟩ := small_difference_higher_restriction n hn H₀ hH₀ ξ hK hsmall
  have hbound : δ^5/256*(Fintype.card G : ℝ) ≤ (2*(K^(2*n+1)+1))^(restrictionExponent n)*(H.card : ℝ) := hsize.trans hcard
  have hH : H.Nonempty := by
    apply card_pos.mp
    by_contra hn
    have hz : H.card = 0 := by omega
    rw [hz,Nat.cast_zero,mul_zero] at hbound
    have hp : 0 < δ^5/256*(Fintype.card G : ℝ) := by positivity
    linarith
  exact ⟨H,ξ,hH,hFreiman,fun h hh ↦ hcoef h (hsub hh),hbound⟩

#print axioms higher_vertical_card_le_ratio
#print axioms small_difference_higher_restriction
#print axioms large_U3_higher_freiman_graph
end Erdos3HigherFreimanExtraction
