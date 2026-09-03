import FormalConjecturesUtil

/-! A counterexample to a proposed coefficientwise obstruction modulo nine.
This does not prove or disprove Erdős 406: a genuine coefficient is bad. -/
set_option maxHeartbeats 0
namespace Erdos406FourthModNine
open Polynomial

noncomputable def F (A : Type*) [CommSemiring A] : A[X] :=
  X^7 + 7*X^6 + 3*X^5 + 8*X^4 + 8*X^3 + 3*X^2 + 7*X + 1

lemma monic_F : (F ℕ).Monic := by
  unfold F
  monicity <;> norm_num

lemma degree_F : (F ℕ).natDegree = 7 := by
  unfold F
  compute_degree!

lemma constant_F : (F ℕ).coeff 0 = 1 := by
  norm_num [F]

lemma fourth_mod_nine_identity :
    (F (ZMod 9))^4 =
      X^28+X^27+3*X^19+3*X^18+3*X^10+3*X^9+X+1 := by
  have hc (n : ℕ) : (n : (ZMod 9)[X]) = ((n % 9 : ℕ) : (ZMod 9)[X]) := by
    simpa only [C_eq_natCast] using
      congrArg (C : ZMod 9 → (ZMod 9)[X]) (ZMod.natCast_mod n 9).symm
  have h28 : (28 : (ZMod 9)[X]) = 1 := by
    simpa only [Nat.reduceMod, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using hc 28
  have h306 : (306 : (ZMod 9)[X]) = 0 := by
    simpa only [Nat.reduceMod, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using hc 306
  have h1656 : (1656 : (ZMod 9)[X]) = 0 := by
    simpa only [Nat.reduceMod, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using hc 1656
  have h4923 : (4923 : (ZMod 9)[X]) = 0 := by
    simpa only [Nat.reduceMod, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using hc 4923
  have h10548 : (10548 : (ZMod 9)[X]) = 0 := by
    simpa only [Nat.reduceMod, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using hc 10548
  have h23418 : (23418 : (ZMod 9)[X]) = 0 := by
    simpa only [Nat.reduceMod, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using hc 23418
  have h39348 : (39348 : (ZMod 9)[X]) = 0 := by
    simpa only [Nat.reduceMod, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using hc 39348
  have h63729 : (63729 : (ZMod 9)[X]) = 0 := by
    simpa only [Nat.reduceMod, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using hc 63729
  have h97068 : (97068 : (ZMod 9)[X]) = 3 := by
    simpa only [Nat.reduceMod, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using hc 97068
  have h125526 : (125526 : (ZMod 9)[X]) = 3 := by
    simpa only [Nat.reduceMod, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using hc 125526
  have h164880 : (164880 : (ZMod 9)[X]) = 0 := by
    simpa only [Nat.reduceMod, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using hc 164880
  have h191988 : (191988 : (ZMod 9)[X]) = 0 := by
    simpa only [Nat.reduceMod, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using hc 191988
  have h207756 : (207756 : (ZMod 9)[X]) = 0 := by
    simpa only [Nat.reduceMod, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using hc 207756
  have h222786 : (222786 : (ZMod 9)[X]) = 0 := by
    simpa only [Nat.reduceMod, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using hc 222786
  unfold F
  ring_nf
  simp only [h28, h306, h1656, h4923, h10548, h23418, h39348, h63729, h97068, h125526, h164880, h191988, h207756, h222786, mul_zero, mul_one, add_zero]


lemma map_F : (F ℕ).map (Nat.castRingHom (ZMod 9)) = F (ZMod 9) := by
  simp [F]

lemma coefficient_two : ((F ℕ)^4).coeff 2 = 306 := by
  conv_lhs => arg 1; unfold F; ring_nf
  norm_num [← C_ofNat, coeff_add, coeff_mul_C, coeff_X_pow, coeff_X, coeff_one]

lemma coefficient_two_bad : ¬ Nat.digits 3 (((F ℕ)^4).coeff 2) ⊆ [0,1] := by
  rw [coefficient_two]
  decide +kernel

lemma all_coefficients_mod_nine (j : ℕ) :
    ((F ℕ)^4).coeff j % 9 = 0 ∨ ((F ℕ)^4).coeff j % 9 = 1 ∨
      ((F ℕ)^4).coeff j % 9 = 3 ∨ ((F ℕ)^4).coeff j % 9 = 4 := by
  have hm : ((F ℕ)^4).map (Nat.castRingHom (ZMod 9)) =
      X^28+X^27+3*X^19+3*X^18+3*X^10+3*X^9+X+1 := by
    rw [Polynomial.map_pow, map_F, fourth_mod_nine_identity]
  have hc := congrArg (fun P : (ZMod 9)[X] => P.coeff j) hm
  simp only [coeff_map] at hc
  change (((F ℕ)^4).coeff j : ZMod 9) = _ at hc
  generalize hn : ((F ℕ)^4).coeff j = n at hc ⊢
  by_cases hj : j ≤ 28
  · interval_cases j <;>
      norm_num [← C_ofNat, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one] at hc
    all_goals
      first
      | exact Or.inl (by simpa using (ZMod.natCast_eq_natCast_iff' n 0 9).mp hc)
      | exact Or.inr (Or.inl (by simpa using (ZMod.natCast_eq_natCast_iff' n 1 9).mp hc))
      | exact Or.inr (Or.inr (Or.inl (by simpa using (ZMod.natCast_eq_natCast_iff' n 3 9).mp hc)))
  · have he : ∀ a ∈ ([0,1,9,10,18,19,27,28] : List ℕ), a ≠ j := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      omega
    simp only [coeff_add, ← C_ofNat, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one] at hc
    have he' : ∀ a ∈ ([0,1,9,10,18,19,27,28] : List ℕ), j ≠ a := by
      intro a ha
      exact Ne.symm (he a ha)
    simp [he, he'] at hc
    have hv := congrArg ZMod.val hc
    norm_num [ZMod.val_one, ZMod.val_ofNat] at hv
    omega

/-- The modulus-nine coefficient test does not exclude normalized nonconstant
polynomial fourth powers. This negates only the proposed local surrogate. -/
theorem normalized_mod_nine_fourth_power_obstruction_false :
    ¬ (∀ P : ℕ[X], P.Monic → P.coeff 0 = 1 → 0 < P.natDegree →
      ¬ (∀ j : ℕ, (P^4).coeff j % 9 = 0 ∨ (P^4).coeff j % 9 = 1 ∨
        (P^4).coeff j % 9 = 3 ∨ (P^4).coeff j % 9 = 4)) := by
  intro h
  exact h (F ℕ) monic_F constant_F (by rw [degree_F]; decide)
    all_coefficients_mod_nine

/-- The same example fails the whole-coefficient digit condition. In
particular, this theorem supplies no good-fourth-power construction. -/
theorem example_has_bad_full_coefficient :
    ¬ (∀ j : ℕ, Nat.digits 3 (((F ℕ)^4).coeff j) ⊆ [0,1]) := by
  intro h
  exact coefficient_two_bad (h 2)

#print axioms normalized_mod_nine_fourth_power_obstruction_false
#print axioms example_has_bad_full_coefficient

#print axioms fourth_mod_nine_identity
#print axioms coefficient_two_bad
#print axioms all_coefficients_mod_nine
end Erdos406FourthModNine
