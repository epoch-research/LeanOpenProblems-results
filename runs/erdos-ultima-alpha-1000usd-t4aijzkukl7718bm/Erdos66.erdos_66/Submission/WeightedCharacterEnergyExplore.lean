import Submission.TranslatedCharacterEnergyExplore

/-! The translation energy estimate remains valid with arbitrary bounded
signed weights. This is a finite-field estimate, not a proof of Erdős 66. -/
namespace Erdos66WeightedCharacterEnergy
open Erdos66CharacterEnergy Erdos66TranslatedCharacterEnergy
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def weightedShiftSum {ι : Type*} (S : Finset ι) (b : ι → F)
    (c : ι → ℤ) (x : F) : ℤ := ∑ i∈S, c i*quadraticChar F (x-b i)

lemma weightedShiftSum_energy_identity {ι : Type*} (hF : ringChar F ≠ 2)
    (S : Finset ι) (b : ι → F) (c : ι → ℤ) :
    (∑ x : F, (weightedShiftSum S b c x)^2) =
      (Fintype.card F : ℤ)*(∑ i∈S, ∑ j∈S, if b i=b j then c i*c j else 0) -
        (∑ i∈S, c i)^2 := by
  have he (x : F) : (weightedShiftSum S b c x)^2 =
      ∑ i∈S, ∑ j∈S, c i*c j*(quadraticChar F (x-b i)*quadraticChar F (x-b j)) := by
    unfold weightedShiftSum
    rw [pow_two]
    simp only [Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [he]
  rw [Finset.sum_comm]
  have hinner (i : ι) :
      (∑ x : F, ∑ j∈S, c i*c j*(quadraticChar F (x-b i)*quadraticChar F (x-b j))) =
        ∑ j∈S, ((Fintype.card F : ℤ)*(if b i=b j then c i*c j else 0)-c i*c j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.mul_sum,quadraticChar_correlation hF]
    split_ifs <;> ring
  simp_rw [hinner]
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul]
  ring

lemma weightedShiftSum_energy_le_card {ι : Type*} (hF : ringChar F ≠ 2)
    (S : Finset ι) (b : ι → F) (c : ι → ℤ)
    (hc : ∀ i∈S, |c i| ≤ 1)
    (hfiber : ∀ i∈S, (S.filter (fun j ↦ b i=b j)).card ≤ 2) :
    (∑ x : F, (weightedShiftSum S b c x)^2) ≤
      2*(Fintype.card F : ℤ)*S.card := by
  have hprod (i j : ι) (hi : i∈S) (hj : j∈S) : c i*c j ≤ 1 := by
    have hh := mul_le_mul (hc i hi) (hc j hj) (abs_nonneg (c j)) (by norm_num : (0 : ℤ) ≤ 1)
    rw [← abs_mul] at hh
    exact (le_abs_self _).trans (by simpa using hh)
  have hrow (i : ι) (hi : i∈S) :
      (∑ j∈S, if b i=b j then c i*c j else 0) ≤ 2 := by
    calc
      _ ≤ ∑ j∈S, if b i=b j then (1 : ℤ) else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        split_ifs
        · exact hprod i j hi hj
        · rfl
      _ = ((S.filter (fun j ↦ b i=b j)).card : ℤ) := by
        simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      _ ≤ 2 := by exact_mod_cast hfiber i hi
  have hsum : (∑ i∈S, ∑ j∈S, if b i=b j then c i*c j else 0) ≤ 2*S.card := by
    calc
      _ ≤ ∑ _i∈S, (2 : ℤ) := Finset.sum_le_sum hrow
      _ = _ := by simp [mul_comm]
  rw [weightedShiftSum_energy_identity hF]
  have hm := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (Fintype.card F))
  nlinarith [sq_nonneg (∑ i∈S, c i)]

noncomputable def weightedTranslatedFiber (U : Finset F) (g : F → ℤ) (a z : F) : ℤ :=
  ∑ x∈sumFiber U z, g x*g (z-x)*quadraticChar F (a+x)*quadraticChar F (a+(z-x))

noncomputable def weightedTranslatedEnergy (U : Finset F) (g : F → ℤ) (a : F) : ℤ :=
  ∑ z : F, (weightedTranslatedFiber U g a z)^2

lemma weightedTranslatedFiber_as_shiftSum (hF : ringChar F ≠ 2)
    (U : Finset F) (g : F → ℤ) (a z : F) :
    weightedTranslatedFiber U g a z =
      weightedShiftSum (sumFiber U z) (fun x ↦ (x-z/2)^2)
        (fun x ↦ g x*g (z-x)) ((a+z/2)^2) := by
  unfold weightedTranslatedFiber weightedShiftSum
  apply Finset.sum_congr rfl
  intro x hx
  rw [mul_assoc (g x*g (z-x)),character_product_square hF]

lemma average_weighted_fiber_energy (hF : ringChar F ≠ 2) (U : Finset F)
    (g : F → ℤ) (hg : ∀ x∈U, |g x| ≤ 1) (z : F) :
    (∑ a : F, (weightedTranslatedFiber U g a z)^2) ≤
      4*(Fintype.card F : ℤ)*(sumFiber U z).card := by
  simp_rw [weightedTranslatedFiber_as_shiftSum hF]
  have he := Equiv.sum_comp (Equiv.addRight (z/2))
    (fun a : F ↦ (weightedShiftSum (sumFiber U z) (fun x ↦ (x-z/2)^2)
      (fun x ↦ g x*g (z-x)) (a^2))^2)
  simp only [Equiv.coe_addRight] at he
  rw [he]
  have h₁ := sum_sq_comp_square_le_two
    (weightedShiftSum (sumFiber U z) (fun x ↦ (x-z/2)^2) (fun x ↦ g x*g (z-x)))
  have h₂ := weightedShiftSum_energy_le_card hF (sumFiber U z)
    (fun x ↦ (x-z/2)^2) (fun x ↦ g x*g (z-x)) (fun x hx ↦ ?_)
    (fun x _ ↦ symmetric_square_fiber_le_two hF (sumFiber U z) z x)
  · nlinarith
  · obtain ⟨hx,hzx⟩ := Finset.mem_filter.mp hx
    rw [abs_mul]
    simpa using mul_le_mul (hg x hx) (hg (z-x) hzx) (abs_nonneg _) (by norm_num : (0 : ℤ) ≤ 1)

/-- Multiplying the translated character by any fixed bounded signed sequence
preserves the same averaged fourth-energy bound. -/
theorem average_weighted_translated_energy (hF : ringChar F ≠ 2) (U : Finset F)
    (g : F → ℤ) (hg : ∀ x∈U, |g x| ≤ 1) :
    (∑ a : F, weightedTranslatedEnergy U g a) ≤
      4*(Fintype.card F : ℤ)*(U.card : ℤ)^2 := by
  unfold weightedTranslatedEnergy
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ z : F, 4*(Fintype.card F : ℤ)*(sumFiber U z).card :=
      Finset.sum_le_sum (fun z _ ↦ average_weighted_fiber_energy hF U g hg z)
    _ = _ := by rw [← Finset.mul_sum,sumFiber_mass]

end Erdos66WeightedCharacterEnergy
