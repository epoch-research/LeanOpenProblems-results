import Submission.WeightedCharacterEnergyExplore
import Submission.SharedParameterKernelExplore
import Submission.PolynomialMixedEnergyExplore

/-! Character energy on integer label fibers. Keeping the fibers in the
label space permits different prime fields to use the same labels. -/
namespace Erdos66IndexedCharacterEnergy
open Erdos66WeightedCharacterEnergy Erdos66CharacterEnergy
  Erdos66TranslatedCharacterEnergy Erdos66SharedParameterKernel
  Erdos66PolynomialMixedEnergy
open scoped Classical
set_option maxHeartbeats 1000000

noncomputable def pairFiber (h w : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range h) ×ˢ (Finset.range h)).filter (fun ij ↦ ij.1+ij.2=w)

lemma mem_pairFiber {h w : ℕ} {ij : ℕ × ℕ} :
    ij∈pairFiber h w ↔ ij.1<h ∧ ij.2<h ∧ ij.1+ij.2=w := by
  simp only [pairFiber,Finset.mem_filter,Finset.mem_product,Finset.mem_range]
  tauto

noncomputable def indexedFiber {p : ℕ} [Fact p.Prime] (h : ℕ) (g : ℕ → ℤ) (a : ZMod p) (w : ℕ) : ℤ :=
  ∑ i∈Finset.range h, ∑ j∈Finset.range h,
    if i+j=w then (g i*quadraticChar (ZMod p) (a+i))*(g j*quadraticChar (ZMod p) (a+j)) else 0

noncomputable def indexedEnergy {p : ℕ} [Fact p.Prime] (h : ℕ) (g : ℕ → ℤ) (a : ZMod p) : ℤ :=
  ∑ w∈Finset.range (2*h), (indexedFiber h g a w)^2

lemma indexedFiber_as_shiftSum {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (h : ℕ) (g : ℕ → ℤ) (a : ZMod p) (w : ℕ) :
    indexedFiber h g a w = weightedShiftSum (pairFiber h w)
      (fun ij ↦ ((ij.1 : ZMod p)-(w : ZMod p)/2)^2)
      (fun ij ↦ g ij.1*g ij.2) ((a+(w : ZMod p)/2)^2) := by
  unfold indexedFiber weightedShiftSum pairFiber
  rw [Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  split_ifs with hij
  · have he : (j : ZMod p)=(w : ZMod p)-i := by rw [← hij]; push_cast; ring
    rw [he]
    have hF : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp
    rw [show g i*quadraticChar (ZMod p) (a+i)*(g j*quadraticChar (ZMod p) (a+((w : ZMod p)-i))) =
      (g i*g j)*(quadraticChar (ZMod p) (a+i)*quadraticChar (ZMod p) (a+((w : ZMod p)-i))) by ring]
    rw [character_product_square hF]
  · rfl

lemma indexed_square_fiber_le_two {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (h w : ℕ) (hh : h ≤ p) (ij : ℕ × ℕ) (hij : ij∈pairFiber h w) :
    ((pairFiber h w).filter (fun kl ↦
      ((ij.1 : ZMod p)-(w : ZMod p)/2)^2 =
        ((kl.1 : ZMod p)-(w : ZMod p)/2)^2)).card ≤ 2 := by
  obtain ⟨hi,hj,hijsum⟩ := mem_pairFiber.mp hij
  have hinj := natCast_injOn_range p h hh
  apply le_trans (Finset.card_le_card (t := {ij,ij.swap}) ?_) Finset.card_le_two
  intro kl hkl
  obtain ⟨hkl,he⟩ := Finset.mem_filter.mp hkl
  obtain ⟨hk,hl,hklsum⟩ := mem_pairFiber.mp hkl
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
  · have hik : ij.1=kl.1 := hinj (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hk) (by linear_combination he)
    have heq : kl=ij := Prod.ext hik.symm (by omega)
    simp [heq]
  · have hcast : (ij.1 : ZMod p)+(ij.2 : ZMod p)=(w : ZMod p) := by rw [← Nat.cast_add,hijsum]
    have htwo : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero
      (by simpa only [ZMod.ringChar_zmod_n] using hp)
    have hjk : ij.2=kl.1 := hinj (Finset.mem_range.mpr hj) (Finset.mem_range.mpr hk) (by
      field_simp [htwo] at he
      have hkcast : (ij.1 : ZMod p)+(kl.1 : ZMod p)=(w : ZMod p) := by
        apply (mul_right_inj' htwo).mp
        linear_combination he
      linear_combination hcast-hkcast)
    have heq : kl=ij.swap := Prod.ext hjk.symm (by dsimp; omega)
    simp [heq]

lemma pairFiber_mass (h : ℕ) :
    (∑ w∈Finset.range (2*h), (pairFiber h w).card) = h^2 := by
  have hh : (((Finset.range h) ×ˢ (Finset.range h)).card) =
      ∑ w∈Finset.range (2*h),
        (((Finset.range h) ×ˢ (Finset.range h)).filter (fun ij ↦ ij.1+ij.2=w)).card := by
    apply Finset.card_eq_sum_card_fiberwise (f := fun ij : ℕ × ℕ ↦ ij.1+ij.2)
    intro ij hij
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hij
    have := Finset.mem_range.mp hi
    have := Finset.mem_range.mp hj
    change ij.1+ij.2∈Finset.range (2*h)
    simp only [Finset.mem_range]
    omega
  simpa only [pairFiber,Finset.card_product,Finset.card_range,pow_two] using hh.symm

lemma indexedEnergy_eq_labelEnergy {p : ℕ} [Fact p.Prime]
    (h : ℕ) (g : ℕ → ℤ) (a : ZMod p) :
    (indexedEnergy h g a : ℝ) =
      labelEnergy h (fun i ↦ (g i : ℝ)*(quadraticChar (ZMod p) (a+i) : ℝ)) := by
  simp only [indexedEnergy,indexedFiber,labelEnergy,labelFiber,
    Int.cast_sum,Int.cast_pow,Int.cast_ite,Int.cast_mul,Int.cast_zero]


lemma indexedEnergy_nonneg {p : ℕ} [Fact p.Prime]
    (h : ℕ) (g : ℕ → ℤ) (a : ZMod p) : 0 ≤ indexedEnergy h g a :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

lemma average_indexed_fiber_energy {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (h w : ℕ) (hh : h ≤ p) (g : ℕ → ℤ)
    (hg : ∀ i<h, |g i| ≤ 1) :
    (∑ a : ZMod p, (indexedFiber h g a w)^2) ≤
      4*(p : ℤ)*(pairFiber h w).card := by
  simp_rw [indexedFiber_as_shiftSum hp]
  have he := Equiv.sum_comp (Equiv.addRight ((w : ZMod p)/2))
    (fun a : ZMod p ↦ (weightedShiftSum (pairFiber h w)
      (fun ij ↦ ((ij.1 : ZMod p)-(w : ZMod p)/2)^2)
      (fun ij ↦ g ij.1*g ij.2) (a^2))^2)
  simp only [Equiv.coe_addRight] at he
  rw [he]
  have h₁ := sum_sq_comp_square_le_two (weightedShiftSum (pairFiber h w)
    (fun ij ↦ ((ij.1 : ZMod p)-(w : ZMod p)/2)^2) (fun ij ↦ g ij.1*g ij.2))
  have h₂ := weightedShiftSum_energy_le_card
    (by simpa only [ZMod.ringChar_zmod_n] using hp) (pairFiber h w)
    (fun ij ↦ ((ij.1 : ZMod p)-(w : ZMod p)/2)^2) (fun ij ↦ g ij.1*g ij.2)
    (fun ij hij ↦ ?_) (fun ij hij ↦ indexed_square_fiber_le_two hp h w hh ij hij)
  · rw [ZMod.card] at h₂
    nlinarith
  · obtain ⟨hi,hj,_⟩ := mem_pairFiber.mp hij
    rw [abs_mul]
    simpa using mul_le_mul (hg _ hi) (hg _ hj) (abs_nonneg _) (by norm_num : (0 : ℤ) ≤ 1)

/-- Averaging controls the energy on integer label fibers uniformly in the
prime, even after multiplication by a fixed bounded signed sequence. -/
theorem average_indexed_energy {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (h : ℕ) (hh : h ≤ p) (g : ℕ → ℤ)
    (hg : ∀ i<h, |g i| ≤ 1) :
    (∑ a : ZMod p, indexedEnergy h g a) ≤ 4*(p : ℤ)*(h : ℤ)^2 := by
  unfold indexedEnergy
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ w∈Finset.range (2*h), 4*(p : ℤ)*(pairFiber h w).card :=
      Finset.sum_le_sum (fun w _ ↦ average_indexed_fiber_energy hp h w hh g hg)
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact_mod_cast pairFiber_mass h

end Erdos66IndexedCharacterEnergy
