import Submission.KloostermanCompletion

/-!
# Signed bilinear Kloosterman estimates

Additive orthogonality gives an exact centered spectral estimate. The two
weights remain arbitrary; no estimate for a growing-modulus prime progression
sum is asserted in this file.
-/
open Finset
open scoped Classical BigOperators ComplexConjugate
namespace Erdos821.Kloosterman

variable {F : Type*} [Field F] [Fintype F]

lemma sum_units_add_zero {A : Type*} [AddCommMonoid A] (f : F → A) :
    (∑ u : Fˣ, f u) + f 0 = ∑ x : F, f x := by
  have h : (∑ u : Fˣ, f u) = ∑ x ∈ (univ : Finset F).erase 0, f x := by
    calc
      _ = ∑ u : {x : F // x ≠ 0}, f u :=
        Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)
      _ = _ := (sum_subtype _ (by simp) f).symm
  rw [h, sum_erase_add _ _ (mem_univ 0)]

noncomputable def positiveTransform {I : Type*} [Fintype I]
    (ψ : AddChar F ℂ) (v : I → F) (w : I → ℂ) (t : F) : ℂ :=
  ∑ i : I, w i * ψ (t*v i)

lemma positiveTransform_correlation {I : Type*} [Fintype I]
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (v : I → F)
    (hv : Function.Injective v) (w z : I → ℂ) :
    (∑ t : F, positiveTransform ψ v w t * conj (positiveTransform ψ v z t)) =
      (Fintype.card F : ℂ) * ∑ i : I, w i*conj (z i) := by
  have hkernel (i j : I) : (∑ t : F, ψ (t*(v i-v j))) =
      if i=j then (Fintype.card F : ℂ) else 0 := by
    rw [AddChar.sum_mulShift _ hψ]
    by_cases h : i=j
    · simp [h]
    · simp [sub_ne_zero.mpr (fun he => h (hv he)), h]
  calc
    _ = ∑ t : F, ∑ i : I, ∑ j : I,
        (w i*conj (z j))*ψ (t*(v i-v j)) := by
      simp only [positiveTransform, map_sum, map_mul, conj_char, Finset.sum_mul_sum]
      apply sum_congr rfl
      intro t _
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      rw [show t*(v i-v j) = t*v i + -(t*v j) by ring, AddChar.map_add_eq_mul]
      ring
    _ = ∑ i : I, ∑ j : I, (w i*conj (z j))*∑ t : F, ψ (t*(v i-v j)) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
      simp only [mul_sum]
    _ = _ := by simp [hkernel, ← mul_sum, mul_comm]

/-- Parseval for any injectively indexed subset of the finite field. -/
theorem positiveTransform_energy {I : Type*} [Fintype I]
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (v : I → F)
    (hv : Function.Injective v) (w : I → ℂ) :
    (∑ t : F, ‖positiveTransform ψ v w t‖^2) =
      (Fintype.card F : ℝ) * ∑ i : I, ‖w i‖^2 := by
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_pow, Complex.mul_conj'] using
    positiveTransform_correlation ψ hψ v hv w w

noncomputable def centeredEnergy (w : F → ℂ) : ℝ :=
  (Fintype.card F : ℝ) * ∑ x : F, ‖w x‖^2 - ‖∑ x : F, w x‖^2

/-- The zero Fourier mode is removed exactly, rather than bounded. -/
theorem positiveTransform_units_energy (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (w : F → ℂ) :
    (∑ u : Fˣ, ‖positiveTransform ψ id w u‖^2) = centeredEnergy w := by
  have hh := sum_units_add_zero (fun t : F => ‖positiveTransform ψ id w t‖^2)
  rw [positiveTransform_energy ψ hψ id Function.injective_id w] at hh
  have hz : positiveTransform ψ id w 0 = ∑ x : F, w x := by
    simp [positiveTransform]
  rw [hz] at hh
  exact eq_sub_of_add_eq hh

lemma centeredEnergy_nonneg (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (w : F → ℂ) :
    0 ≤ centeredEnergy w := by
  rw [← positiveTransform_units_energy ψ hψ w]
  exact sum_nonneg fun _ _ => sq_nonneg _

lemma positiveTransform_inverse_units_energy (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (w : F → ℂ) :
    (∑ u : Fˣ, ‖positiveTransform ψ id w (u : F)⁻¹‖^2) = centeredEnergy w := by
  calc
    _ = ∑ u : Fˣ, ‖positiveTransform ψ id w u‖^2 := by
      apply Fintype.sum_equiv (Equiv.inv Fˣ)
      intro u
      simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val]
    _ = _ := positiveTransform_units_energy ψ hψ w

noncomputable def bilinearKloosterman (ψ : AddChar F ℂ) (α β : F → ℂ) : ℂ :=
  ∑ a : F, ∑ b : F, α a * β b * kloosterman ψ a b

/-- The signed sum factors into two Fourier transforms on the inverse graph. -/
lemma bilinearKloosterman_factorization (ψ : AddChar F ℂ) (α β : F → ℂ) :
    bilinearKloosterman ψ α β =
      ∑ u : Fˣ, positiveTransform ψ id α u * positiveTransform ψ id β (u : F)⁻¹ := by
  unfold bilinearKloosterman kloosterman
  simp only [mul_sum]
  conv_lhs =>
    enter [2, a]
    rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  simp only [positiveTransform, id_eq, Finset.sum_mul_sum, AddChar.map_add_eq_mul]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  rw [mul_comm (u : F) a, mul_comm (u : F)⁻¹ b]
  ring

lemma norm_sum_mul_sq_le {I : Type*} [Fintype I] (f g : I → ℂ) :
    ‖∑ i : I, f i*g i‖^2 ≤ (∑ i : I, ‖f i‖^2) * ∑ i : I, ‖g i‖^2 := by
  have hn : ‖∑ i : I, f i*g i‖ ≤ ∑ i : I, ‖f i‖*‖g i‖ := by
    simpa only [norm_mul] using norm_sum_le (univ : Finset I) (fun i => f i*g i)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (sum_mul_sq_le_sq_mul_sq univ (fun i => ‖f i‖) (fun i => ‖g i‖))

/-- A centered bilinear estimate. Taking absolute values of the individual
Kloosterman sums before summing would lose this cancellation. -/
theorem bilinearKloosterman_centered_bound (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (α β : F → ℂ) :
    ‖bilinearKloosterman ψ α β‖^2 ≤ centeredEnergy α * centeredEnergy β := by
  rw [bilinearKloosterman_factorization]
  have hh := norm_sum_mul_sq_le
    (fun u : Fˣ => positiveTransform ψ id α u)
    (fun u : Fˣ => positiveTransform ψ id β (u : F)⁻¹)
  rwa [positiveTransform_units_energy ψ hψ α,
    positiveTransform_inverse_units_energy ψ hψ β] at hh

lemma positiveTransform_wave (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (c t : F) :
    positiveTransform ψ id (fun a : F => ψ (-a*c)) t =
      if t=c then (Fintype.card F : ℂ) else 0 := by
  have he : positiveTransform ψ id (fun a : F => ψ (-a*c)) t =
      ∑ a : F, ψ (a*(t-c)) := by
    unfold positiveTransform
    apply sum_congr rfl
    intro a _
    rw [← AddChar.map_add_eq_mul]
    congr 1
    dsimp
    ring
  rw [he, AddChar.sum_mulShift _ hψ]
  by_cases h : t=c <;> simp [h, sub_eq_zero]

lemma centeredEnergy_wave (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (c : F) (hc : c ≠ 0) :
    centeredEnergy (fun a : F => ψ (-a*c)) = (Fintype.card F : ℝ)^2 := by
  have hsum : (∑ a : F, ψ (-a*c)) = 0 := by
    simpa [positiveTransform, Ne.symm hc] using positiveTransform_wave ψ hψ c 0
  unfold centeredEnergy
  rw [hsum]
  simp [AddChar.norm_apply, pow_two]

/-- Pure additive waves attain the centered spectral bound. Thus the bound
cannot be uniformly reduced for arbitrary complex coefficient sequences. -/
theorem bilinearKloosterman_waves (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (u₀ : Fˣ) :
    bilinearKloosterman ψ (fun a : F => ψ (-a*(u₀ : F)))
      (fun b : F => ψ (-b*(u₀ : F)⁻¹)) = (Fintype.card F : ℂ)^2 := by
  rw [bilinearKloosterman_factorization]
  have hterm (u : Fˣ) :
      positiveTransform ψ id (fun a : F => ψ (-a*(u₀ : F))) u *
        positiveTransform ψ id (fun b : F => ψ (-b*(u₀ : F)⁻¹)) (u : F)⁻¹ =
      if u=u₀ then (Fintype.card F : ℂ)^2 else 0 := by
    by_cases h : u=u₀
    · subst u
      rw [positiveTransform_wave ψ hψ, positiveTransform_wave ψ hψ]
      simp [pow_two]
    · have hv : (u : F) ≠ (u₀ : F) := fun he => h (Units.ext he)
      rw [positiveTransform_wave ψ hψ, if_neg hv]
      simp [h]
  simp_rw [hterm]
  simp

end Erdos821.Kloosterman
