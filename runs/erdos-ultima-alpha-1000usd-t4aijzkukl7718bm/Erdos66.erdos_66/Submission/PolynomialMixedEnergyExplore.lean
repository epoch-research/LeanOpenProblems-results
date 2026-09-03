import Submission.MixedEnergyExplore
import Submission.PrefixSignExplore

/-! Mixed-energy control for signed polynomials, obtained by embedding their
coefficient sequences in a sufficiently large cyclic group. -/
namespace Erdos66PolynomialMixedEnergy
open Polynomial Erdos66SignEnergy Erdos66PrefixSign

section Push
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def finitePush {ι : Type*} (S : Finset ι) (f : ι → G) (c : ι → ℝ) (z : G) : ℝ :=
  ∑ i ∈ S, if f i = z then c i else 0

lemma conv_finitePush {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (f : ι → G) (g : κ → G) (c : ι → ℝ) (d : κ → ℝ) (z : G) :
    Erdos66MixedEnergy.conv (finitePush S f c) (finitePush T g d) z =
      ∑ i ∈ S, ∑ j ∈ T, if f i + g j = z then c i * d j else 0 := by
  unfold Erdos66MixedEnergy.conv finitePush
  simp only [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [ite_mul, zero_mul]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  apply propext
  simp only [eq_sub_iff_add_eq, add_comm]

lemma finitePush_single {ι : Type*} (S : Finset ι) (f : ι → G) (c : ι → ℝ)
    (hf : Set.InjOn f S) (i : ι) (hi : i ∈ S) : finitePush S f c (f i) = c i := by
  classical
  unfold finitePush
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    exact if_neg (fun he ↦ hji (hf hj hi he))
  · exact fun h ↦ (h hi).elim

lemma finitePush_sq {ι : Type*} (S : Finset ι) (f : ι → G) (c : ι → ℝ)
    (hf : Set.InjOn f S) (z : G) :
    finitePush S f c z ^ 2 = finitePush S f (fun i ↦ c i ^ 2) z := by
  classical
  by_cases hz : ∃ i ∈ S, f i = z
  · obtain ⟨i, hi, rfl⟩ := hz
    rw [finitePush_single S f c hf i hi, finitePush_single S f _ hf i hi]
  · have hh (i : ι) (hi : i ∈ S) : f i ≠ z := fun h ↦ hz ⟨i, hi, h⟩
    have hzero : finitePush S f c z = 0 :=
      Finset.sum_eq_zero (fun i hi ↦ if_neg (hh i hi))
    have hzero' : finitePush S f (fun i ↦ c i ^ 2) z = 0 :=
      Finset.sum_eq_zero (fun i hi ↦ if_neg (hh i hi))
    rw [hzero, hzero']
    norm_num

lemma finitePush_energy {ι : Type*} (S : Finset ι) (f : ι → G) (c : ι → ℝ)
    (hf : Set.InjOn f S) : (∑ z : G, finitePush S f c z ^ 2) = ∑ i ∈ S, c i ^ 2 := by
  simp_rw [finitePush_sq S f c hf, finitePush]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Push

lemma polynomial_mixed_coeff {P Q : ℤ[X]} {h k : ℕ}
    (hP : SupportedBelow P h) (hQ : SupportedBelow Q k) (n : ℕ) :
    (P * Q).coeff n = ∑ i ∈ Finset.range h, ∑ j ∈ Finset.range k,
      if i + j = n then P.coeff i * Q.coeff j else 0 := by
  calc
    (P * Q).coeff n = (cutPoly P h * cutPoly Q k).coeff n := by
      rw [cutPoly_eq_self hP, cutPoly_eq_self hQ]
    _ = _ := by
      simp only [cutPoly, Finset.sum_mul_sum, finset_sum_coeff,
        monomial_mul_monomial, coeff_monomial]

noncomputable def polyPush (p h : ℕ) (P : ℤ[X]) : ZMod p → ℝ :=
  finitePush (Finset.range h) (fun i ↦ (i : ZMod p)) (fun i ↦ (P.coeff i : ℝ))

lemma conv_polyPush (p : ℕ) [NeZero p] {P Q : ℤ[X]} {h k : ℕ}
    (hP : SupportedBelow P h) (hQ : SupportedBelow Q k) :
    Erdos66MixedEnergy.conv (polyPush p h P) (polyPush p k Q) = polyPush p (h + k) (P * Q) := by
  funext z
  rw [polyPush, polyPush, conv_finitePush]
  unfold polyPush finitePush
  simp_rw [polynomial_mixed_coeff hP hQ, Int.cast_sum, Int.cast_ite, Int.cast_mul, Int.cast_zero]
  have hdist (n : ℕ) :
      (if (n : ZMod p) = z then
        ∑ i ∈ Finset.range h, ∑ j ∈ Finset.range k,
          (if i + j = n then (P.coeff i : ℝ) * Q.coeff j else 0) else 0) =
      ∑ i ∈ Finset.range h, ∑ j ∈ Finset.range k,
        if i + j = n then
          (if (n : ZMod p) = z then (P.coeff i : ℝ) * Q.coeff j else 0) else 0 := by
    by_cases hn : (n : ZMod p) = z <;> simp only [hn, if_true, if_false, ite_self, Finset.sum_const_zero]
  simp_rw [hdist]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_ite_eq]
  have hij : i + j ∈ Finset.range (h + k) := by
    simp only [Finset.mem_range] at hi hj ⊢
    omega
  rw [if_pos hij, Nat.cast_add]

lemma natCast_injOn_range (p L : ℕ) [NeZero p] (hL : L ≤ p) :
    Set.InjOn (fun i : ℕ ↦ (i : ZMod p)) (Finset.range L) := by
  intro i hi j hj hij
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  have hv := congrArg ZMod.val hij
  simpa only [ZMod.val_natCast_of_lt (by omega : i < p),
    ZMod.val_natCast_of_lt (by omega : j < p)] using hv

lemma polyPush_energy (p L : ℕ) [NeZero p] (P : ℤ[X]) (hL : L ≤ p) :
    (∑ z : ZMod p, polyPush p L P z ^ 2) =
      ((∑ i ∈ Finset.range L, (P.coeff i) ^ 2 : ℤ) : ℝ) := by
  rw [polyPush, finitePush_energy _ _ _ (natCast_injOn_range p L hL)]
  simp only [Int.cast_sum, Int.cast_pow]

lemma mixed_energy_polyPush (p : ℕ) [NeZero p] {P Q : ℤ[X]} {h k : ℕ}
    (hP : SupportedBelow P h) (hQ : SupportedBelow Q k) (hpk : h + k ≤ p) :
    Erdos66MixedEnergy.energy (polyPush p h P) (polyPush p k Q) =
      ((∑ i ∈ Finset.range (h + k), ((P * Q).coeff i) ^ 2 : ℤ) : ℝ) := by
  unfold Erdos66MixedEnergy.energy
  rw [conv_polyPush p hP hQ]
  exact polyPush_energy p (h + k) (P * Q) hpk

/-- Small self-convolution energies imply a small mixed-convolution energy. -/
theorem polynomial_mixed_energy_le {P Q : ℤ[X]} {h k : ℕ}
    (hP : SupportedBelow P h) (hQ : SupportedBelow Q k)
    (hPE : Erdos66SignEnergy.energy P h ≤ 2 * (h : ℤ) ^ 2)
    (hQE : Erdos66SignEnergy.energy Q k ≤ 2 * (k : ℤ) ^ 2) :
    (∑ i ∈ Finset.range (h + k), ((P * Q).coeff i) ^ 2) ≤ 2 * (h : ℤ) * k := by
  let p := 2 * h + 2 * k + 1
  haveI : NeZero p := ⟨by dsimp [p]; omega⟩
  have hselfP : Erdos66MixedEnergy.energy (polyPush p h P) (polyPush p h P) ≤ 2 * (h : ℝ) ^ 2 := by
    rw [mixed_energy_polyPush p hP hP (by dsimp [p]; omega)]
    have he : h + h = 2 * h := by omega
    rw [he, ← pow_two]
    exact_mod_cast hPE
  have hselfQ : Erdos66MixedEnergy.energy (polyPush p k Q) (polyPush p k Q) ≤ 2 * (k : ℝ) ^ 2 := by
    rw [mixed_energy_polyPush p hQ hQ (by dsimp [p]; omega)]
    have he : k + k = 2 * k := by omega
    rw [he, ← pow_two]
    exact_mod_cast hQE
  have hh := Erdos66MixedEnergy.mixed_energy_le (Nat.cast_nonneg h) (Nat.cast_nonneg k) hselfP hselfQ
  rw [mixed_energy_polyPush p hP hQ (by dsimp [p]; omega)] at hh
  exact_mod_cast hh

lemma polynomial_mixed_l1_sq {P Q : ℤ[X]} {h k : ℕ}
    (hP : SupportedBelow P h) (hQ : SupportedBelow Q k)
    (hPE : Erdos66SignEnergy.energy P h ≤ 2 * (h : ℤ) ^ 2)
    (hQE : Erdos66SignEnergy.energy Q k ≤ 2 * (k : ℤ) ^ 2) :
    (∑ i ∈ Finset.range (h + k), |(P * Q).coeff i|) ^ 2 ≤
      2 * (h : ℤ) * k * (h + k) := by
  have hh := sq_sum_le_card_mul_sum_sq (s := Finset.range (h + k))
    (f := fun i ↦ |(P * Q).coeff i|)
  simp only [Finset.card_range, sq_abs, Nat.cast_add] at hh
  have he := polynomial_mixed_energy_le hP hQ hPE hQE
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (h : ℤ) + k)
  nlinarith

/-- A single sign polynomial controls the mixed fibers of every two prefixes. -/
theorem exists_all_mixed_prefix_bounds (H : ℕ) :
    ∃ P : ℤ[X], SupportedBelow P H ∧
      (∀ i < H, P.coeff i = 1 ∨ P.coeff i = -1) ∧
      ∀ h ≤ H, ∀ k ≤ H,
        (∑ i ∈ Finset.range (h + k), |(cutPoly P h * cutPoly P k).coeff i|) ^ 2 ≤
          2 * (h : ℤ) * k * (h + k) := by
  obtain ⟨P, hP, hsign, hE⟩ := exists_all_prefix_energies H
  refine ⟨P, hP, hsign, ?_⟩
  intro h hh k hk
  exact polynomial_mixed_l1_sq (cutPoly_supported P h) (cutPoly_supported P k)
    ((hE h hh).trans (by omega)) ((hE k hk).trans (by omega))

end Erdos66PolynomialMixedEnergy
