import Submission.IndexedCharacterEnergyExplore
import Submission.CharacterTranslateSelectionExplore

/-! Weighted character energy charged to the squared weights, rather than to
the number of labels. This is finite selection infrastructure, not a proof
of the original natural-number conjecture. -/
namespace Erdos66RealWeightedCharacterEnergy
open Erdos66CharacterEnergy Erdos66TranslatedCharacterEnergy
  Erdos66IndexedCharacterEnergy Erdos66SharedParameterKernel
  Erdos66CharacterTranslateSelection
open scoped Classical
set_option maxHeartbeats 2000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def realShiftSum {ι : Type*} (S : Finset ι) (b : ι → F)
    (c : ι → ℝ) (x : F) : ℝ := ∑ i∈S, c i*(quadraticChar F (x-b i) : ℝ)

lemma realShiftSum_energy_identity {ι : Type*} (hF : ringChar F ≠ 2)
    (S : Finset ι) (b : ι → F) (c : ι → ℝ) :
    (∑ x : F, (realShiftSum S b c x)^2) =
      (Fintype.card F : ℝ)*(∑ i∈S, ∑ j∈S, if b i=b j then c i*c j else 0)-
        (∑ i∈S, c i)^2 := by
  have he (x : F) : (realShiftSum S b c x)^2 =
      ∑ i∈S, ∑ j∈S, c i*c j*((quadraticChar F (x-b i) : ℝ)*(quadraticChar F (x-b j) : ℝ)) := by
    unfold realShiftSum
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
      (∑ x : F, ∑ j∈S, c i*c j*((quadraticChar F (x-b i) : ℝ)*(quadraticChar F (x-b j) : ℝ))) =
      ∑ j∈S, ((Fintype.card F : ℝ)*(if b i=b j then c i*c j else 0)-c i*c j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [←Finset.mul_sum]
    have hc : (∑ x : F, (quadraticChar F (x-b i) : ℝ)*(quadraticChar F (x-b j) : ℝ)) =
        if b i=b j then (Fintype.card F : ℝ)-1 else -1 := by
      exact_mod_cast quadraticChar_correlation hF (b i) (b j)
    rw [hc]
    split_ifs <;> ring
  simp_rw [hinner]
  simp only [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.sum_mul]
  ring

omit [Field F] [Fintype F] in
lemma collision_weight_le_two {ι : Type*} (S : Finset ι) (b : ι → F) (c : ι → ℝ)
    (hfiber : ∀ i∈S, (S.filter (fun j ↦ b i=b j)).card ≤ 2) :
    (∑ i∈S, ∑ j∈S, if b i=b j then c i*c j else 0) ≤ 2*∑ i∈S, (c i)^2 := by
  have hrow (i : ι) (hi : i∈S) :
      (∑ j∈S, if b i=b j then (c i)^2 else 0) ≤ 2*(c i)^2 := by
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfiber i hi) (sq_nonneg _)
  have hsum := Finset.sum_le_sum hrow
  rw [←Finset.mul_sum] at hsum
  have hswap : (∑ i∈S, ∑ j∈S, if b i=b j then (c j)^2 else 0) =
      ∑ i∈S, ∑ j∈S, if b i=b j then (c i)^2 else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [eq_comm]
  have hpoint (i j : ι) :
      2*(if b i=b j then c i*c j else 0) ≤
      (if b i=b j then (c i)^2 else 0)+(if b i=b j then (c j)^2 else 0) := by
    split_ifs <;> nlinarith [sq_nonneg (c i-c j)]
  have hh := Finset.sum_le_sum (s := S) (fun i _ ↦ Finset.sum_le_sum (s := S) (fun j _ ↦ hpoint i j))
  simp only [←Finset.mul_sum,Finset.sum_add_distrib] at hh
  rw [hswap] at hh
  linarith

lemma realShiftSum_energy_le {ι : Type*} (hF : ringChar F ≠ 2)
    (S : Finset ι) (b : ι → F) (c : ι → ℝ)
    (hfiber : ∀ i∈S, (S.filter (fun j ↦ b i=b j)).card ≤ 2) :
    (∑ x : F, (realShiftSum S b c x)^2) ≤
      2*(Fintype.card F : ℝ)*(∑ i∈S, (c i)^2) := by
  rw [realShiftSum_energy_identity hF]
  have hh := mul_le_mul_of_nonneg_left (collision_weight_le_two S b c hfiber)
    (Nat.cast_nonneg (α := ℝ) (Fintype.card F))
  nlinarith [sq_nonneg (∑ i∈S, c i)]

lemma real_sum_sq_comp_square_le_two (g : F → ℝ) :
    (∑ x : F, (g (x^2))^2) ≤ 2*∑ v : F, (g v)^2 := by
  rw [←Finset.sum_fiberwise (Finset.univ : Finset F) (fun x ↦ x^2) (fun x ↦ (g (x^2))^2)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  calc
    (∑ x∈Finset.univ.filter (fun x : F ↦ x^2=v), (g (x^2))^2) =
        ∑ _x∈Finset.univ.filter (fun x : F ↦ x^2=v), (g v)^2 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = ((Finset.univ.filter (fun x : F ↦ x^2=v)).card : ℝ)*(g v)^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast square_fiber_card_le_two v) (sq_nonneg _)

noncomputable def signedFiber {p : ℕ} [Fact p.Prime] (h : ℕ) (v : ℕ → ℝ)
    (a : ZMod p) (q : ℕ) : ℝ :=
  labelFiber h (fun i ↦ v i*(quadraticChar (ZMod p) (a+i) : ℝ)) q

noncomputable def signedEnergy {p : ℕ} [Fact p.Prime] (h : ℕ) (v : ℕ → ℝ)
    (a : ZMod p) : ℝ := ∑ q∈Finset.range (2*h), (signedFiber h v a q)^2

lemma signedFiber_as_shiftSum {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (h : ℕ) (v : ℕ → ℝ) (a : ZMod p) (q : ℕ) :
    signedFiber h v a q = realShiftSum (pairFiber h q)
      (fun ij ↦ ((ij.1 : ZMod p)-(q : ZMod p)/2)^2)
      (fun ij ↦ v ij.1*v ij.2) ((a+(q : ZMod p)/2)^2) := by
  unfold signedFiber labelFiber realShiftSum pairFiber
  rw [Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  by_cases hij : i+j=q
  · simp only [hij,if_true]
    have he : (j : ZMod p)=(q : ZMod p)-i := by rw [←hij]; push_cast; ring
    have hc := character_product_square
      (by simpa only [ZMod.ringChar_zmod_n] using hp) a (q : ZMod p) (i : ZMod p)
    rw [←he] at hc
    have hc' : (quadraticChar (ZMod p) (a+i) : ℝ)*(quadraticChar (ZMod p) (a+j) : ℝ) =
        (quadraticChar (ZMod p) ((a+(q : ZMod p)/2)^2-((i : ZMod p)-(q : ZMod p)/2)^2) : ℝ) := by
      exact_mod_cast hc
    rw [show v i*(quadraticChar (ZMod p) (a+i) : ℝ)*(v j*(quadraticChar (ZMod p) (a+j) : ℝ)) =
      (v i*v j)*((quadraticChar (ZMod p) (a+i) : ℝ)*(quadraticChar (ZMod p) (a+j) : ℝ)) by ring,hc']
  · simp [hij]

/-- The cost of a fixed signed fiber is its squared-weight pair mass. -/
theorem average_signed_fiber_energy {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (h q : ℕ) (hh : h ≤ p) (v : ℕ → ℝ) :
    (∑ a : ZMod p, (signedFiber h v a q)^2) ≤
      4*(p : ℝ)*(∑ ij∈pairFiber h q, (v ij.1*v ij.2)^2) := by
  simp_rw [signedFiber_as_shiftSum hp]
  have he := Equiv.sum_comp (Equiv.addRight ((q : ZMod p)/2))
    (fun a : ZMod p ↦ (realShiftSum (pairFiber h q)
      (fun ij ↦ ((ij.1 : ZMod p)-(q : ZMod p)/2)^2)
      (fun ij ↦ v ij.1*v ij.2) (a^2))^2)
  simp only [Equiv.coe_addRight] at he
  rw [he]
  have h₁ := real_sum_sq_comp_square_le_two (realShiftSum (pairFiber h q)
    (fun ij ↦ ((ij.1 : ZMod p)-(q : ZMod p)/2)^2) (fun ij ↦ v ij.1*v ij.2))
  have h₂ := realShiftSum_energy_le
    (by simpa only [ZMod.ringChar_zmod_n] using hp) (pairFiber h q)
    (fun ij ↦ ((ij.1 : ZMod p)-(q : ZMod p)/2)^2) (fun ij ↦ v ij.1*v ij.2)
    (fun ij hij ↦ indexed_square_fiber_le_two hp h q hh ij hij)
  rw [ZMod.card] at h₂
  nlinarith


lemma squared_weight_pair_mass (h : ℕ) (v : ℕ → ℝ) :
    (∑ q∈Finset.range (2*h), ∑ ij∈pairFiber h q, (v ij.1*v ij.2)^2) =
      (∑ i∈Finset.range h, (v i)^2)^2 := by
  have he := sum_labelFiber h (fun i ↦ (v i)^2) (fun _ ↦ 1)
  simp only [mul_one] at he
  have hf (q : ℕ) : (∑ ij∈pairFiber h q, (v ij.1*v ij.2)^2) =
      labelFiber h (fun i ↦ (v i)^2) q := by
    simp only [pairFiber,Finset.sum_filter,Finset.sum_product,labelFiber,mul_pow]
  simp_rw [hf]
  rw [he,pow_two,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

/-- The total cost is the square of the squared-weight mass. In particular
it can be much smaller than the unweighted number-of-labels estimate. -/
theorem average_signed_energy {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (h : ℕ) (hh : h ≤ p) (v : ℕ → ℝ) :
    (∑ a : ZMod p, signedEnergy h v a) ≤
      4*(p : ℝ)*(∑ i∈Finset.range h, (v i)^2)^2 := by
  unfold signedEnergy
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ q∈Finset.range (2*h), 4*(p : ℝ)*(∑ ij∈pairFiber h q, (v ij.1*v ij.2)^2) :=
      Finset.sum_le_sum (fun q _ ↦ average_signed_fiber_energy hp h q hh v)
    _ = _ := by rw [←Finset.mul_sum,squared_weight_pair_mass]

noncomputable def badTargets {p : ℕ} [Fact p.Prime] (h : ℕ) (v : ℕ → ℝ)
    (a : ZMod p) (E : ℝ) : Finset ℕ :=
  (Finset.range (2*h)).filter (fun q ↦ E < |signedFiber h v a q|)

lemma badTargets_mass {p : ℕ} [Fact p.Prime] (h : ℕ) (v : ℕ → ℝ)
    (a : ZMod p) (E : ℝ) (hE : 0 ≤ E) :
    ((badTargets h v a E).card : ℝ)*E^2 ≤ signedEnergy h v a := by
  calc
    _ = ∑ _q∈badTargets h v a E, E^2 := by simp
    _ ≤ ∑ q∈badTargets h v a E, (signedFiber h v a q)^2 := by
      apply Finset.sum_le_sum
      intro q hq
      have hh := (Finset.mem_filter.mp hq).2.le
      have hs := pow_le_pow_left₀ hE hh 2
      simpa only [sq_abs] using hs
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun q _ _ ↦ sq_nonneg _)

/-- One admissible translation controls every threshold via its total
weighted energy; the bound has no dependence on the number of fine targets. -/
theorem exists_admissible_weighted_translate (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (h : ℕ) (hh : 4*h<p) (v : ℕ → ℝ) :
    ∃ a : ZMod p, (∀ i<h, a+(i : ZMod p) ≠ 0) ∧
      (∀ q<2*h, 2*a+(q : ZMod p) ≠ 0) ∧
      signedEnergy h v a ≤ 8*(∑ i∈Finset.range h, (v i)^2)^2 ∧
      ∀ E : ℝ, 0 ≤ E → ((badTargets h v a E).card : ℝ)*E^2 ≤
        8*(∑ i∈Finset.range h, (v i)^2)^2 := by
  have hc : 2*(forbiddenInterval p h).card < Fintype.card (ZMod p) := by
    rw [ZMod.card]
    have := forbiddenInterval_card p h
    omega
  obtain ⟨a,ha,henergy⟩ := exists_small_outside (forbiddenInterval p h)
    (signedEnergy h v) (4*(∑ i∈Finset.range h, (v i)^2)^2) hc
    (fun a ↦ Finset.sum_nonneg (fun q _ ↦ sq_nonneg _))
    (by rw [ZMod.card]; nlinarith [average_signed_energy hp h (by omega) v])
  have henergy' : signedEnergy h v a ≤ 8*(∑ i∈Finset.range h, (v i)^2)^2 := by linarith
  have htwo : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)
  have hop (q : ℕ) (hq : q<2*h) : 2*a+(q : ZMod p) ≠ 0 := by
    intro he
    apply ha
    apply Finset.mem_image.mpr
    refine ⟨q,Finset.mem_range.mpr hq,?_⟩
    apply (div_eq_iff htwo).mpr
    linear_combination -he
  refine ⟨a,?_,hop,henergy',fun E hE ↦ (badTargets_mass h v a E hE).trans henergy'⟩
  intro i hi he
  have hh := hop (2*i) (by omega)
  apply hh
  push_cast
  linear_combination 2*he

end Erdos66RealWeightedCharacterEnergy
