import Submission.KloostermanIntervals

/-!
# Kloosterman sums on finite commutative rings and products

The ring definition uses inversion in the unit group. Additive characters
and sums are transported through ring equivalences before splitting into
prime factors; no unproved estimate for composite moduli is assumed.
-/
open Finset
open scoped Classical BigOperators
namespace Erdos821.Kloosterman

section FiniteRing
variable {R S : Type*} [CommRing R] [CommRing S] [Fintype R] [Fintype S]

noncomputable def ringKloosterman (ψ : AddChar R ℂ) (a b : R) : ℂ :=
  ∑ u : Rˣ, ψ (a*(u : R)+b*(↑(u⁻¹) : R))

lemma ringKloosterman_equiv (e : R ≃+* S) (ψ : AddChar S ℂ) (a b : R) :
    ringKloosterman (ψ.compAddMonoidHom e.toAddMonoidHom) a b =
      ringKloosterman ψ (e a) (e b) := by
  unfold ringKloosterman
  apply Fintype.sum_equiv (Units.mapEquiv e.toMulEquiv).toEquiv
  intro u
  change ψ (e (a*(u : R)+b*(↑(u⁻¹) : R))) =
    ψ (e a*(↑(Units.mapEquiv e.toMulEquiv u) : S)+
      e b*(↑((Units.mapEquiv e.toMulEquiv u)⁻¹) : S))
  simp only [← map_inv, Units.coe_mapEquiv, map_add, map_mul]
  rfl

lemma ringKloosterman_norm_le_card (ψ : AddChar R ℂ) (a b : R) :
    ‖ringKloosterman ψ a b‖ ≤ (Fintype.card R : ℝ) := by
  calc
    _ ≤ ∑ u : Rˣ, ‖ψ (a*(u : R)+b*(↑(u⁻¹) : R))‖ := norm_sum_le _ _
    _ = (Fintype.card Rˣ : ℝ) := by simp [AddChar.norm_apply]
    _ ≤ _ := by exact_mod_cast Fintype.card_le_of_injective (Units.val : Rˣ → R) Units.val_injective

omit [Fintype R] [Fintype S] in
lemma primitive_transport (e : R ≃+* S) (ψ : AddChar S ℂ) (hψ : ψ.IsPrimitive) :
    (ψ.compAddMonoidHom e.toAddMonoidHom).IsPrimitive := by
  intro a ha h
  apply hψ (show e a ≠ 0 from fun he => ha (e.injective (by simpa using he)))
  ext x
  have hx := congrArg (fun χ : AddChar R ℂ => χ (e.symm x)) h
  simpa [AddChar.mulShift_apply] using hx

end FiniteRing

section Field
variable {F : Type*} [Field F] [Fintype F]

lemma ringKloosterman_eq (ψ : AddChar F ℂ) (a b : F) :
    ringKloosterman ψ a b = kloosterman ψ a b := by
  simp only [ringKloosterman, kloosterman, Units.val_inv_eq_inv_val]

lemma ringKloosterman_fourth_field (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (a b : F) :
    ‖ringKloosterman ψ a b‖^4 ≤
      3*(Fintype.card F : ℝ)^3*(if b=0 then (Fintype.card F : ℝ) else 1) := by
  by_cases hb : b=0
  · rw [if_pos hb]
    have hh := pow_le_pow_left₀ (norm_nonneg _) (ringKloosterman_norm_le_card ψ a b) 4
    nlinarith only [hh, sq_nonneg ((Fintype.card F : ℝ)^2)]
  · rw [if_neg hb, mul_one, ringKloosterman_eq]
    exact kloosterman_norm_fourth_le_of_ne_zero ψ hψ a b (Or.inr hb)

end Field

section PiRing
variable {I : Type*} [Fintype I] (R : I → Type*) [∀ i, CommRing (R i)] [∀ i, Fintype (R i)]

noncomputable def coordinateChar (ψ : AddChar (∀ i, R i) ℂ) (i : I) : AddChar (R i) ℂ :=
  ψ.compAddMonoidHom (AddMonoidHom.single R i)

omit [Fintype I] [∀ i, Fintype (R i)] in
lemma coordinateChar_apply (ψ : AddChar (∀ i, R i) ℂ) (i : I) (x : R i) :
    coordinateChar R ψ i x = ψ (Pi.single i x) := rfl

omit [Fintype I] [∀ i, Fintype (R i)] in
lemma primitive_coordinate (ψ : AddChar (∀ i, R i) ℂ) (hψ : ψ.IsPrimitive) (i : I) :
    (coordinateChar R ψ i).IsPrimitive := by
  intro a ha h
  have hs : Pi.single i a ≠ (0 : ∀ i, R i) := by
    intro he
    have hi := congrFun he i
    apply ha
    simpa using hi
  apply hψ hs
  ext x
  have hx := congrArg (fun χ : AddChar (R i) ℂ => χ (x i)) h
  simpa only [AddChar.mulShift_apply, coordinateChar_apply, ← Pi.single_mul_left,
    AddChar.one_apply] using hx

omit [∀ i, Fintype (R i)] in
lemma character_pi_factorization (ψ : AddChar (∀ i, R i) ℂ) (x : ∀ i, R i) :
    ψ x = ∏ i : I, coordinateChar R ψ i (x i) := by
  have hmap (s : Finset I) : ψ (∑ i ∈ s, Pi.single i (x i)) =
      ∏ i ∈ s, ψ (Pi.single i (x i)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp only [sum_insert hi, prod_insert hi, AddChar.map_add_eq_mul, ih]
  calc
    _ = ψ (∑ i : I, Pi.single i (x i)) := by rw [univ_sum_single]
    _ = _ := hmap univ

/-- A Kloosterman sum on a finite product is the product of its coordinate
sums for the corresponding primitive coordinate characters. -/
theorem ringKloosterman_pi (ψ : AddChar (∀ i, R i) ℂ) (a b : ∀ i, R i) :
    ringKloosterman ψ a b = ∏ i : I, ringKloosterman (coordinateChar R ψ i) (a i) (b i) := by
  letI : DecidableEq (∀ i, R i) := fun a b => Classical.propDecidable (a=b)
  unfold ringKloosterman
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv MulEquiv.piUnits.toEquiv
  intro u
  rw [character_pi_factorization R]
  apply prod_congr rfl
  intro i _
  rfl

end PiRing
end Erdos821.Kloosterman
