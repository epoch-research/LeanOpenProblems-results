import Submission.CharacterSeparation
import Submission.FrequencyGraph
import Submission.BohrCovering

/-! Restricting a frequency graph to a Freiman homomorphism, by separating its
nonzero vertical four-term differences. -/
namespace Erdos3FreimanFrequencyGraph
open Finset Erdos3FrequencyGraph Erdos3CharacterSeparation Erdos3FiniteBohr Erdos3BohrCovering
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 4000000

lemma exists_large_translate_fiber {I L : Type*} [AddCommGroup L] [Fintype L]
    [DecidableEq I] [DecidableEq L] (H : Finset I) (ξ : I → L) (U : Finset L)
    (hU : U.Nonempty) {K : ℕ} (hK : Fintype.card L ≤ K*U.card) :
    ∃ η : L, H.card ≤ K*(H.filter (fun h ↦ ξ h-η ∈ U)).card := by
  let count : L → ℕ := fun η ↦ (H.filter (fun h ↦ ξ h-η ∈ U)).card
  have hsum : (∑ η : L, count η) = H.card*U.card := by
    have hc (η : L) : count η = ∑ h ∈ H, if ξ h-η ∈ U then 1 else 0 := (sum_boole _ _).symm
    simp_rw [hc]
    rw [sum_comm]
    have he (h : I) : (∑ η : L, if ξ h-η ∈ U then 1 else 0) = U.card := by
      calc
        _ = ∑ z : L, if z ∈ U then 1 else 0 :=
          Fintype.sum_equiv (Equiv.subLeft (ξ h)) _ _ (fun _ ↦ rfl)
        _ = _ := by simp
    simp_rw [he]
    simp
  obtain ⟨η,_,hη⟩ := exists_max_image univ count univ_nonempty
  have hh : H.card*U.card ≤ Fintype.card L*count η := by
    rw [← hsum]
    exact (sum_le_sum hη).trans_eq (by simp)
  have hh' := hh.trans (Nat.mul_le_mul_right (count η) hK)
  refine ⟨η,?_⟩
  have hp := hU.card_pos
  nlinarith

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def verticalDifferences (H : Finset G) (ξ : G → AddChar G ℂ) : Finset (AddChar G ℂ) :=
  univ.filter (fun χ ↦ (0,χ) ∈
    (frequencyGraph H ξ+frequencyGraph H ξ)-(frequencyGraph H ξ+frequencyGraph H ξ))

def FreimanOn (H : Finset G) (ξ : G → AddChar G ℂ) : Prop :=
  ∀ a ∈ H, ∀ b ∈ H, ∀ c ∈ H, ∀ d ∈ H,
    a+b = c+d → ξ a+ξ b = ξ c+ξ d

lemma FreimanOn.isAddFreimanHom {H : Finset G} {ξ : G → AddChar G ℂ} (h : FreimanOn H ξ) :
    IsAddFreimanHom 2 (H : Set G) Set.univ ξ := by
  rw [isAddFreimanHom_two]
  exact ⟨fun _ _ ↦ Set.mem_univ _,h⟩

lemma separated_freiman_restriction (H : Finset G) (ξ : G → AddChar G ℂ) (D : Finset G)
    (hsep : ∀ χ ∈ verticalDifferences H ξ, χ ≠ 0 → ∃ x ∈ D, 1 < ‖χ x-1‖) :
    ∃ H' ⊆ H, H.card ≤ 17^(2*D.card)*H'.card ∧ FreimanOn H' ξ := by
  let E : Finset (AddChar (AddChar G ℂ) ℂ) := D.image AddChar.doubleDualEmb
  let U : Finset (AddChar G ℂ) := bohr E (1/4)
  have hU : U.Nonempty := ⟨0,bohr_zero E (by norm_num)⟩
  have hcardU : Fintype.card (AddChar G ℂ) ≤ 17^(2*D.card)*U.card := by
    have hh := card_le_grid_mul_bohr E (univ : Finset (AddChar G ℂ)) univ_nonempty
      (fun _ ↦ (0 : ℂ)) (by norm_num : (0 : ℝ) < 1)
      (fun χ _ e _ ↦ by simp only [sub_zero,AddChar.norm_apply,le_refl]) (q := 8) (by decide)
    norm_num only [card_univ,show 2*8+1 = 17 by decide,show 2*(1 : ℝ)/(8 : ℕ) = 1/4 by norm_num] at hh
    change Fintype.card (AddChar G ℂ) ≤ 17^(2*E.card)*U.card at hh
    exact hh.trans (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 2 card_image_le)))
  obtain ⟨η,hη⟩ := exists_large_translate_fiber H ξ U hU hcardU
  let H' := H.filter (fun h ↦ ξ h-η ∈ U)
  refine ⟨H',filter_subset _ _,hη,?_⟩
  intro a ha b hb c hc d hd habcd
  have haH := (mem_filter.mp ha).1
  have hbH := (mem_filter.mp hb).1
  have hcH := (mem_filter.mp hc).1
  have hdH := (mem_filter.mp hd).1
  let χ : AddChar G ℂ := (ξ a+ξ b)-(ξ c+ξ d)
  have hχV : χ ∈ verticalDifferences H ξ := by
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    have hmem (h : G) (hh : h ∈ H) : (h,ξ h) ∈ frequencyGraph H ξ :=
      (mem_frequencyGraph H ξ (h,ξ h)).mpr ⟨hh,rfl⟩
    have hh := sub_mem_sub (add_mem_add (hmem a haH) (hmem b hbH)) (add_mem_add (hmem c hcH) (hmem d hdH))
    have he : ((a,ξ a)+(b,ξ b))-((c,ξ c)+(d,ξ d)) = (0,χ) := by
      apply Prod.ext
      · change (a+b)-(c+d) = 0
        rw [habcd,sub_self]
      · rfl
    rwa [he] at hh
  have hχU : χ ∈ bohr E 1 := by
    have hh := bohr_add (bohr_add (mem_filter.mp ha).2 (mem_filter.mp hb).2)
      (bohr_neg (bohr_add (mem_filter.mp hc).2 (mem_filter.mp hd).2))
    have he : (ξ a-η+(ξ b-η)) + -(ξ c-η+(ξ d-η)) = χ := by dsimp [χ]; abel
    change _ ∈ bohr E ((1/4 : ℝ)+1/4+(1/4+1/4)) at hh
    norm_num only [show (1/4 : ℝ)+1/4+(1/4+1/4) = 1 by norm_num] at hh
    rwa [he] at hh
  have hz : χ = 0 := by
    by_contra hn
    obtain ⟨x,hx,hgt⟩ := hsep χ hχV hn
    have he : AddChar.doubleDualEmb x ∈ E := mem_image.mpr ⟨x,hx,rfl⟩
    have hle := mem_bohr.mp hχU _ he
    have hle' : ‖χ x-1‖ ≤ 1 := hle
    exact (not_lt_of_ge hle') hgt
  exact sub_eq_zero.mp hz

/-- A polynomial loss in the number of vertical differences suffices to make
the frequency map an exact Freiman homomorphism on a large restriction. -/
theorem exists_freiman_restriction (H : Finset G) (ξ : G → AddChar G ℂ) :
    ∃ H' ⊆ H, H.card ≤ (2*((verticalDifferences H ξ).card+1))^20*H'.card ∧ FreimanOn H' ξ := by
  let C := (verticalDifferences H ξ).erase 0
  obtain ⟨D,hD,hsep⟩ := exists_small_separating_set C (fun χ hχ ↦ (mem_erase.mp hχ).1)
  obtain ⟨H',hsub,hsize,hFreiman⟩ := separated_freiman_restriction H ξ D (by
    intro χ hχ hn
    exact hsep χ (mem_erase.mpr ⟨hn,hχ⟩))
  have hcost := separation_grid_cost C.card D.card hD
  have hC : C.card ≤ (verticalDifferences H ξ).card := card_le_card (erase_subset _ _)
  refine ⟨H',hsub,?_,hFreiman⟩
  exact hsize.trans (Nat.mul_le_mul_right _ (hcost.trans
    (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hC 1)) 20)))

#print axioms exists_freiman_restriction
end Erdos3FreimanFrequencyGraph
