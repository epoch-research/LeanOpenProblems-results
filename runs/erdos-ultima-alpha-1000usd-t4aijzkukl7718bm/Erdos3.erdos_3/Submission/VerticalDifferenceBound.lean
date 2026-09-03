import Submission.FreimanFrequencyGraph

/-! Small difference sets control the vertical obstructions to a frequency
map being Freiman. Together with logarithmic separation, this gives polynomial
losses in the restriction step. -/
namespace Erdos3VerticalDifferenceBound
open Finset Erdos3FrequencyGraph Erdos3FreimanFrequencyGraph
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma vertical_times_graph_le (H : Finset G) (ξ : G → AddChar G ℂ) :
    (verticalDifferences H ξ).card*(frequencyGraph H ξ).card ≤
      ((3 : ℕ) • frequencyGraph H ξ-(2 : ℕ) • frequencyGraph H ξ).card := by
  let Γ := frequencyGraph H ξ
  let V := verticalDifferences H ξ
  let f : (AddChar G ℂ) × (G × AddChar G ℂ) → G × AddChar G ℂ := fun p ↦ (0,p.1)+p.2
  rw [← card_product]
  apply card_le_card_of_injOn f
  · intro p hp
    obtain ⟨hpV,hpΓ⟩ := mem_product.mp hp
    have hv : (0,p.1) ∈ (Γ+Γ)-(Γ+Γ) := by
      simpa only [verticalDifferences,mem_filter,mem_univ,true_and,Γ,V] using hpV
    obtain ⟨a,ha,b,hb,hab⟩ := mem_sub.mp hv
    have ha' : a+p.2 ∈ (3 : ℕ) • Γ := by
      have hh := add_mem_add ha hpΓ
      simpa only [show (3 : ℕ) = 2+1 by rfl,add_nsmul,two_nsmul,one_nsmul] using hh
    have hb' : b ∈ (2 : ℕ) • Γ := by simpa only [two_nsmul] using hb
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

/-- Plünnecke–Ruzsa bounds the number of vertical four-term differences by
the fifth power of the graph's difference ratio. -/
theorem vertical_card_le_ratio (H : Finset G) (hH : H.Nonempty) (ξ : G → AddChar G ℂ) :
    ((verticalDifferences H ξ).card : ℝ) ≤
      (((frequencyGraph H ξ-frequencyGraph H ξ).card : ℝ)/(H.card : ℝ))^5 := by
  let Γ := frequencyGraph H ξ
  have hΓ : Γ.Nonempty := by
    obtain ⟨h,hh⟩ := hH
    exact ⟨(h,ξ h),(mem_frequencyGraph H ξ _).mpr ⟨hh,rfl⟩⟩
  have hp := pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub hΓ Γ 3 2
  have hpR : (((3 : ℕ) • Γ-(2 : ℕ) • Γ).card : ℝ) ≤
      (((Γ-Γ).card : ℝ)/(Γ.card : ℝ))^5*(Γ.card : ℝ) := by
    have hh := (NNRat.cast_le (K := ℝ)).mpr hp
    simpa only [NNRat.cast_mul,NNRat.cast_pow,NNRat.cast_div,NNRat.cast_natCast] using hh
  have hv : ((verticalDifferences H ξ).card : ℝ)*(Γ.card : ℝ) ≤
      (((3 : ℕ) • Γ-(2 : ℕ) • Γ).card : ℝ) := by
    exact_mod_cast vertical_times_graph_le H ξ
  have hpos : (0 : ℝ) < Γ.card := by exact_mod_cast hΓ.card_pos
  have hh := hv.trans hpR
  have hh' : ((verticalDifferences H ξ).card : ℝ) ≤ (((Γ-Γ).card : ℝ)/(Γ.card : ℝ))^5 := by
    nlinarith only [hh,hpos]
  simpa only [Γ,card_frequencyGraph] using hh'

/-- The Freiman restriction costs only a polynomial in the difference ratio. -/
theorem small_difference_freiman_restriction (H : Finset G) (hH : H.Nonempty)
    (ξ : G → AddChar G ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hsmall : ((frequencyGraph H ξ-frequencyGraph H ξ).card : ℝ) ≤ K*(H.card : ℝ)) :
    ∃ H' ⊆ H, (H.card : ℝ) ≤ (2*(K^5+1))^20*(H'.card : ℝ) ∧ FreimanOn H' ξ := by
  have hpos : (0 : ℝ) < H.card := by exact_mod_cast hH.card_pos
  have hratio : ((frequencyGraph H ξ-frequencyGraph H ξ).card : ℝ)/(H.card : ℝ) ≤ K :=
    (div_le_iff₀ hpos).mpr hsmall
  have hv := (vertical_card_le_ratio H hH ξ).trans
    (pow_le_pow_left₀ (by positivity) hratio 5)
  obtain ⟨H',hsub,hcard,hFreiman⟩ := exists_freiman_restriction H ξ
  refine ⟨H',hsub,?_,hFreiman⟩
  have hcardR : (H.card : ℝ) ≤ (2*(((verticalDifferences H ξ).card : ℝ)+1))^20*(H'.card : ℝ) := by
    exact_mod_cast hcard
  have hcost : (2*(((verticalDifferences H ξ).card : ℝ)+1))^20 ≤ (2*(K^5+1))^20 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) 20
  exact hcardR.trans (mul_le_mul_of_nonneg_right hcost (by positivity))

#print axioms vertical_card_le_ratio
#print axioms small_difference_freiman_restriction
end Erdos3VerticalDifferenceBound
