import Submission.SpectralGraphEnergy
import Submission.FiniteSampling

/-! Logarithmically many evaluation points quantitatively separate any finite
family of nontrivial characters from the identity. -/
namespace Erdos3CharacterSeparation
open Finset Erdos3FiniteFourier Erdos3SpectralGraphEnergy Erdos3LinearFormsUniformity
  Erdos3FiniteSampling
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def passes (χ : AddChar G ℂ) (x : G) : ℝ := if ‖χ x-1‖ ≤ 1 then 1 else 0

lemma passes_nonneg (χ : AddChar G ℂ) (x : G) : 0 ≤ passes χ x := by
  unfold passes; split_ifs <;> norm_num

lemma mean_passes_le (χ : AddChar G ℂ) (hχ : χ ≠ 1) : (𝔼 x : G, passes χ x) ≤ 2/3 := by
  have hmean : (𝔼 x : G, (χ x).re) = 0 := by
    have hh := congrArg Complex.re (AddChar.expect_eq_zero_iff_ne_zero.mpr hχ)
    simpa only [expect_re,Complex.zero_re] using hh
  have hpt (x : G) : 3*passes χ x ≤ 2+2*(χ x).re := by
    have hre : |(χ x).re| ≤ 1 := (Complex.abs_re_le_norm _).trans_eq (χ.norm_apply x)
    by_cases hx : ‖χ x-1‖ ≤ 1
    · have he : ‖χ x-1‖^2 = 2-2*(χ x).re := by
        rw [Complex.sq_norm,Complex.normSq_sub,Complex.normSq_eq_norm_sq,χ.norm_apply]
        simp
        ring
      simp only [passes,if_pos hx,mul_one]
      nlinarith [norm_nonneg (χ x-1)]
    · simp only [passes,if_neg hx,mul_zero]
      linarith [(abs_le.mp hre).1]
  have hh := expect_le_expect (fun x (_ : x ∈ univ) ↦ hpt x)
  rw [← mul_expect,expect_add_distrib,Fintype.expect_const,← mul_expect,hmean] at hh
  linarith

lemma exists_separating_tuple (C : Finset (AddChar G ℂ)) (hC : ∀ χ ∈ C, χ ≠ 1)
    (m : ℕ) (hm : (C.card : ℝ)*(2/3 : ℝ)^m < 1) :
    ∃ v : Fin m → G, ∀ χ ∈ C, ∃ i, 1 < ‖χ (v i)-1‖ := by
  let score : (Fin m → G) → ℝ := fun v ↦
    ((C.filter (fun χ ↦ ∀ i : Fin m, ‖χ (v i)-1‖ ≤ 1)).card : ℝ)
  have he (v : Fin m → G) : score v = ∑ χ ∈ C, ∏ i : Fin m, passes χ (v i) := by
    have hp (χ : AddChar G ℂ) : (∏ i : Fin m, passes χ (v i)) =
        if ∀ i : Fin m, ‖χ (v i)-1‖ ≤ 1 then (1 : ℝ) else 0 := by
      by_cases hh : ∀ i : Fin m, ‖χ (v i)-1‖ ≤ 1
      · simp [passes,hh]
      · rw [if_neg hh]
        obtain ⟨i,hi⟩ := not_forall.mp hh
        apply prod_eq_zero (mem_univ i)
        simp [passes,hi]
    simp_rw [hp]
    exact (sum_boole (R := ℝ) (fun χ : AddChar G ℂ ↦ ∀ i : Fin m, ‖χ (v i)-1‖ ≤ 1) C).symm
  have havg : (𝔼 v : Fin m → G, score v) ≤ (C.card : ℝ)*(2/3 : ℝ)^m := by
    simp_rw [he]
    rw [expect_sum_comm]
    calc
      _ = ∑ χ ∈ C, (𝔼 x : G, passes χ x)^m := by
        apply sum_congr rfl
        intro χ _
        simp only [Fintype.expect_eq_sum_div_card,Fintype.card_pi,← Fintype.prod_sum,
          Nat.cast_prod,prod_div_distrib,prod_const,card_univ,Fintype.card_fin,Nat.cast_pow,div_pow]
      _ ≤ ∑ _χ ∈ C, (2/3 : ℝ)^m := by
        apply sum_le_sum
        intro χ hχ
        exact pow_le_pow_left₀ (expect_nonneg (fun x _ ↦ passes_nonneg χ x)) (mean_passes_le χ (hC χ hχ)) m
      _ = _ := by simp
  obtain ⟨v,_,hv⟩ := exists_min_image univ score univ_nonempty
  have hvlt : score v < 1 := (le_expect univ_nonempty hv).trans_lt (havg.trans_lt hm)
  have hz : (C.filter (fun χ ↦ ∀ i : Fin m, ‖χ (v i)-1‖ ≤ 1)).card = 0 := by
    change (((C.filter (fun χ ↦ ∀ i : Fin m, ‖χ (v i)-1‖ ≤ 1)).card : ℕ) : ℝ) < 1 at hvlt
    have hh : (C.filter (fun χ ↦ ∀ i : Fin m, ‖χ (v i)-1‖ ≤ 1)).card < 1 := by exact_mod_cast hvlt
    omega
  refine ⟨v,?_⟩
  intro χ hχ
  by_contra! hn
  have hh : χ ∈ C.filter (fun χ ↦ ∀ i : Fin m, ‖χ (v i)-1‖ ≤ 1) := mem_filter.mpr ⟨hχ,hn⟩
  rw [card_eq_zero.mp hz] at hh
  simp at hh

/-- Uniform separation by only O(log |C|) evaluations, with a fixed gap of one. -/
theorem exists_small_separating_set (C : Finset (AddChar G ℂ)) (hC : ∀ χ ∈ C, χ ≠ 1) :
    ∃ D : Finset G, D.card ≤ 2*(Nat.log 2 C.card+1) ∧
      ∀ χ ∈ C, ∃ x ∈ D, 1 < ‖χ x-1‖ := by
  let L := Nat.log 2 C.card+1
  have hpow : (C.card : ℝ) < (2 : ℝ)^L := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) C.card
  have hm : (C.card : ℝ)*(2/3 : ℝ)^(2*L) < 1 := by
    have hh : (2/3 : ℝ)^(2*L) ≤ (1/2 : ℝ)^L := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by positivity) (by norm_num : (2/3 : ℝ)^2 ≤ 1/2) L
    calc
      _ ≤ (C.card : ℝ)*(1/2 : ℝ)^L := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = (C.card : ℝ)/(2 : ℝ)^L := by rw [div_pow,one_pow]; ring
      _ < 1 := (div_lt_one (by positivity)).mpr hpow
  obtain ⟨v,hv⟩ := exists_separating_tuple C hC (2*L) hm
  refine ⟨univ.image v,?_,?_⟩
  · exact (card_image_le).trans_eq (by simp [L])
  · intro χ hχ
    obtain ⟨i,hi⟩ := hv χ hχ
    exact ⟨v i,mem_image.mpr ⟨i,mem_univ _,rfl⟩,hi⟩

/-- The constant-grid cost of logarithmically many tests is polynomial. -/
lemma separation_grid_cost (M m : ℕ) (hm : m ≤ 2*(Nat.log 2 M+1)) :
    17^(2*m) ≤ (2*(M+1))^20 := by
  let L := Nat.log 2 M+1
  have hpow : 2^L ≤ 2*(M+1) := by
    dsimp [L]
    rw [pow_succ]
    have hh := Nat.pow_log_le_add_one 2 M
    omega
  calc
    _ ≤ (2^5)^(2*m) := Nat.pow_le_pow_left (by decide) _
    _ = 2^(10*m) := by rw [← pow_mul]; congr 1; omega
    _ ≤ 2^(20*L) := Nat.pow_le_pow_right (by decide) (by dsimp [L]; omega)
    _ = (2^L)^20 := by rw [← pow_mul]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_left hpow _

#print axioms exists_small_separating_set
#print axioms separation_grid_cost
end Erdos3CharacterSeparation
