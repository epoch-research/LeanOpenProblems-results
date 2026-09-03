import Submission.TranslatedMixedFiberExplore

/-! Same-field character-fiber bounds for bounded positive dilations.
These estimates do not control integer carries or a change of field. -/
namespace Erdos66DilatedCharacterFiber
open Erdos66TranslatedMixedFiber Erdos66CharacterTranslateSelection
  Erdos66TranslatedCharacterEnergy Erdos66CrossGraph Erdos66MixedEnergy
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def dilate (t : F) (U : Finset F) : Finset F :=
  U.image (fun x ↦ t*x)

lemma crossCharFiber_dilate_both (U V : Finset F) (t : F) (ht : t ≠ 0) (z : F) :
    crossCharFiber (dilate t U) (dilate t V) (t*z) = crossCharFiber U V z := by
  unfold crossCharFiber dilate
  rw [Finset.sum_image (fun _ _ _ _ h ↦ mul_left_cancel₀ ht h)]
  simp_rw [Finset.sum_image (fun _ _ _ _ h ↦ mul_left_cancel₀ ht h)]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  have he : t*x+t*y=t*z ↔ x+y=z := by rw [← mul_add, mul_right_inj' ht]
  simp only [he]
  split_ifs
  · rw [map_mul,map_mul]
    have hh := quadraticChar_sq_one (F := F) ht
    calc
      _ = (quadraticChar F t)^2 * (quadraticChar F x*quadraticChar F y) := by ring
      _ = _ := by rw [hh,one_mul]
  · rfl

lemma energy_signed_dilate (U : Finset F) (t : F) (ht : t ≠ 0) :
    energy (signedFunction (dilate t U)) (signedFunction (dilate t U)) =
      energy (signedFunction U) (signedFunction U) := by
  unfold energy
  simp_rw [conv_signedFunction]
  rw [← Equiv.sum_comp (Equiv.mulLeft₀ t ht)]
  simp only [Equiv.mulLeft₀_apply,crossCharFiber_dilate_both U U t ht]

lemma energy_mixed_dilate_le (U V : Finset F) (t s : F)
    (ht : t ≠ 0) (hs : s ≠ 0) (C h k : ℝ)
    (hC : 0 ≤ C) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hU : energy (signedFunction U) (signedFunction U) ≤ C*h^2)
    (hV : energy (signedFunction V) (signedFunction V) ≤ C*k^2) :
    energy (signedFunction (dilate t U)) (signedFunction (dilate s V)) ≤ C*h*k := by
  apply mixed_energy_le_general hC hh hk
  · simpa only [energy_signed_dilate U t ht] using hU
  · simpa only [energy_signed_dilate V s hs] using hV

noncomputable def dilatedSumSupport (p : ℕ) (a : ZMod p) (r s h k : ℕ) :
    Finset (ZMod p) :=
  (Finset.range (r*h+s*k)).image (fun i : ℕ ↦ ((r+s : ℕ) : ZMod p)*a+(i : ZMod p))

lemma dilatedSumSupport_card (p : ℕ) (a : ZMod p) (r s h k : ℕ) :
    (dilatedSumSupport p a r s h k).card ≤ r*h+s*k := by
  unfold dilatedSumSupport
  exact Finset.card_image_le.trans_eq (Finset.card_range _)

lemma dilated_sum_mem_support (p : ℕ) [Fact p.Prime] (a : ZMod p) (r s h k : ℕ)
    (hr : 0 < r) (hs : 0 < s)
    (x : ZMod p) (hx : x∈dilate (r : ZMod p) (intervalTranslate p a h))
    (y : ZMod p) (hy : y∈dilate (s : ZMod p) (intervalTranslate p a k)) :
    x+y∈dilatedSumSupport p a r s h k := by
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨u₀,hu₀,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu₀
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨v₀,hv₀,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv₀
  apply Finset.mem_image.mpr
  refine ⟨r*i+s*j,Finset.mem_range.mpr ?_,?_⟩
  · exact Nat.add_lt_add (Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hi) hr)
      (Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hj) hs)
  · push_cast
    ring

/-- Bounded dilations change only the size of the sum support. The field
character self-energy bound is unchanged by each nonzero dilation. -/
theorem interval_dilated_mixed_l1_sq {p : ℕ} [Fact p.Prime]
    (a : ZMod p) (r s h k : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hrp : (r : ZMod p) ≠ 0) (hsp : (s : ZMod p) ≠ 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hh : (translatedEnergy (baseInterval p h) a : ℝ) ≤ C*(h : ℝ)^2)
    (hk : (translatedEnergy (baseInterval p k) a : ℝ) ≤ C*(k : ℝ)^2) :
    (∑ z : ZMod p, |(crossCharFiber
      (dilate (r : ZMod p) (intervalTranslate p a h))
      (dilate (s : ZMod p) (intervalTranslate p a k)) z : ℝ)|)^2 ≤
        C*h*k*(r*h+s*k) := by
  have hh' : energy (signedFunction (intervalTranslate p a h))
      (signedFunction (intervalTranslate p a h)) ≤ C*(h : ℝ)^2 := by
    rw [intervalTranslate,energy_signed_translate]
    exact hh
  have hk' : energy (signedFunction (intervalTranslate p a k))
      (signedFunction (intervalTranslate p a k)) ≤ C*(k : ℝ)^2 := by
    rw [intervalTranslate,energy_signed_translate]
    exact hk
  have he := energy_mixed_dilate_le (intervalTranslate p a h) (intervalTranslate p a k)
    (r : ZMod p) (s : ZMod p) hrp hsp C h k hC (Nat.cast_nonneg h) (Nat.cast_nonneg k) hh' hk'
  have hb := crossCharFiber_l1_sq_le
    (dilate (r : ZMod p) (intervalTranslate p a h))
    (dilate (s : ZMod p) (intervalTranslate p a k))
    (dilatedSumSupport p a r s h k) (dilated_sum_mem_support p a r s h k hr hs)
  have hc : ((dilatedSumSupport p a r s h k).card : ℝ) ≤
      (r : ℝ)*h+s*k := by exact_mod_cast dilatedSumSupport_card p a r s h k
  have hm := mul_le_mul hc he (energy_nonneg _ _) (by positivity : 0 ≤ (r : ℝ)*h+s*k)
  nlinarith


/-- A single translate simultaneously controls all dilations. The dependence
on the multipliers occurs only in the displayed sum-support factor. The
admissibility assertions here concern the undilated interval. -/
theorem exists_dilated_interval_fiber_control {ι : Type*}
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (L : ℕ) (hL : 4*L < p)
    (S : Finset ι) (length : ι → ℕ) (hlen : ∀ i ∈ S, length i ≤ L) :
    ∃ a : ZMod p,
      (∀ u∈intervalTranslate p a L, u ≠ 0) ∧
      (∀ u∈intervalTranslate p a L, ∀ v∈intervalTranslate p a L, u+v ≠ 0) ∧
      ∀ i∈S, ∀ j∈S, ∀ r s : ℕ, 0 < r → 0 < s →
        (r : ZMod p) ≠ 0 → (s : ZMod p) ≠ 0 →
        (∑ z : ZMod p, |(crossCharFiber
          (dilate (r : ZMod p) (intervalTranslate p a (length i)))
          (dilate (s : ZMod p) (intervalTranslate p a (length j))) z : ℝ)|)^2 ≤
          8*S.card*(length i)*(length j)*(r*(length i)+s*(length j)) := by
  obtain ⟨a,hzero,hopp,henergy⟩ :=
    exists_admissible_interval_translates p hp L hL S length hlen
  refine ⟨a,hzero,hopp,fun i hi j hj r s hr hs hrp hsp ↦ ?_⟩
  exact interval_dilated_mixed_l1_sq a r s (length i) (length j) hr hs hrp hsp
    (8*S.card) (by positivity) (henergy i hi) (henergy j hj)

end Erdos66DilatedCharacterFiber
