import Submission.QuinticQuadraticMaximalResidue

/-! Rational quadratic fifth-power identities through (1,1,1,1,1).
The descent here concerns only this fixed-base construction. -/
namespace Erdos322Research.QuinticQuadraticPositiveBase
noncomputable section
open Polynomial
set_option maxHeartbeats 2000000
private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private def quad {R : Type*} [CommRing R] (a b : R) : R[X] :=
  1 + C b * X + C a * X^2

private theorem residue_coefficients (a b : Fin 5 → ZMod 11)
    (h : ∑ i, (quad (a i) (b i))^5 = 5) :
    (∀ i, a i = 0) ∧ (∀ i, b i = 0) := by
  have hd (i : Fin 5) : (quad (a i) (b i)).natDegree ≤ 2 := by
    dsimp only [quad]
    compute_degree
  have hz := QuinticQuadraticMaximalResidue.quadratic_constant _ hd h
  constructor
  · intro i
    have hc := Polynomial.coeff_eq_zero_of_natDegree_lt
      (show (quad (a i) (b i)).natDegree < 2 by rw [hz i]; decide)
    simpa [quad, coeff_one] using hc
  · intro i
    have hc := Polynomial.coeff_eq_zero_of_natDegree_lt
      (show (quad (a i) (b i)).natDegree < 1 by rw [hz i]; decide)
    simpa [quad, coeff_one] using hc

private theorem integer_first_divisibility (a b : Fin 5 → ℤ)
    (h : ∑ i, (quad (a i) (b i))^5 = 5) :
    (∀ i, 11 ∣ a i) ∧ (∀ i, 11 ∣ b i) := by
  have hm := congrArg (Polynomial.map (Int.castRingHom (ZMod 11))) h
  have hh : ∑ i, (quad ((a i : ℤ) : ZMod 11) ((b i : ℤ) : ZMod 11))^5 = 5 := by
    simpa [quad, Polynomial.map_sum] using hm
  obtain ⟨ha, hb⟩ := residue_coefficients _ _ hh
  constructor
  · intro i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (ha i)
  · intro i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (hb i)

private def remainderTerm (a b : ℤ) : ℤ[X] :=
  (1 + C a * X)^5 + 110 * (C b)^2 * X * (1 + C a * X)^3 +
    605 * (C b)^4 * X^2 * (1 + C a * X)

private theorem symmetrization (a b : ℤ) :
    (quad (11*a) (11*b))^5 + ((quad (11*a) (11*b))^5).comp (-X) =
      2 * (remainderTerm a b).comp (11*X^2) := by
  simp only [quad, remainderTerm, add_comp, mul_comp, pow_comp, one_comp,
    C_comp, X_comp, ofNat_comp, map_mul, map_ofNat]
  ring

private theorem comp_nonconstant_injective {R : Type*} [CommRing R] [IsDomain R]
    (p q s : R[X]) (hs : s.natDegree ≠ 0) (h : p.comp s = q.comp s) : p = q := by
  apply sub_eq_zero.mp
  have hh : (p-q).comp s = 0 := by simpa using sub_eq_zero.mpr h
  rcases (Polynomial.comp_eq_zero_iff.mp hh) with hz | hz
  · exact hz
  · exact False.elim (hs (by rw [hz.2, natDegree_C]))

private theorem integer_second_divisibility (a b : Fin 5 → ℤ)
    (h : ∑ i, (quad (11*a i) (11*b i))^5 = 5) :
    ∀ i, 11 ∣ a i := by
  let R : ℤ[X] := ∑ i, remainderTerm (a i) (b i)
  have hsym : 2 * R.comp (11*X^2) = 10 := by
    calc
      2 * R.comp (11*X^2) =
          ∑ i, ((quad (11*a i) (11*b i))^5 +
            ((quad (11*a i) (11*b i))^5).comp (-X)) := by
        simp only [R, sum_comp, Finset.mul_sum, symmetrization]
      _ = 10 := by rw [Finset.sum_add_distrib, ← sum_comp, h]; norm_num
  have hc : R.comp (11*X^2) = 5 := by
    have hn : (2 : ℤ[X]) ≠ 0 := by norm_num
    apply mul_left_cancel₀ hn
    linear_combination hsym
  have hR : R = 5 := by
    refine comp_nonconstant_injective R 5 (11*X^2) ?_ ?_
    · have hd : (11*X^2 : ℤ[X]).natDegree = 2 := by compute_degree; norm_num
      omega
    · simpa using hc
  have hm := congrArg (Polynomial.map (Int.castRingHom (ZMod 11))) hR
  have h110 : (110 : (ZMod 11)[X]) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C : ZMod 11 → (ZMod 11)[X]) (show (110 : ZMod 11) = 0 by decide)
  have h605 : (605 : (ZMod 11)[X]) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C : ZMod 11 → (ZMod 11)[X]) (show (605 : ZMod 11) = 0 by decide)
  have he : ∑ i, (quad (0 : ZMod 11) ((a i : ℤ) : ZMod 11))^5 = 5 := by
    simpa [R, remainderTerm, quad, Polynomial.map_sum, h110, h605] using hm
  have ha := (residue_coefficients _ _ he).2
  intro i
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (ha i)

private theorem integer_divisibility (a b : Fin 5 → ℤ)
    (h : ∑ i, (quad (a i) (b i))^5 = 5) :
    (∀ i, 121 ∣ a i) ∧ (∀ i, 11 ∣ b i) := by
  obtain ⟨ha, hb⟩ := integer_first_divisibility a b h
  choose a' ha' using ha
  choose b' hb' using hb
  have h' : ∑ i, (quad (11*a' i) (11*b' i))^5 = 5 := by
    simpa only [ha', hb'] using h
  have ha2 := integer_second_divisibility a' b' h'
  constructor
  · intro i
    obtain ⟨c, hc⟩ := ha2 i
    refine ⟨c, ?_⟩
    rw [ha', hc]
    ring
  · intro i
    exact ⟨b' i, hb' i⟩

private def size (a b : Fin 5 → ℤ) : ℕ :=
  (∑ i, (a i).natAbs) + ∑ i, (b i).natAbs

/-- There is no nonconstant integral quadratic fifth-power identity through
`(1,1,1,1,1)`. The linear and quadratic coefficients descend by different
powers of eleven. -/
theorem integer_coefficients_zero (a b : Fin 5 → ℤ)
    (h : ∑ i, (quad (a i) (b i))^5 = 5) :
    (∀ i, a i = 0) ∧ (∀ i, b i = 0) := by
  generalize hm : size a b = m
  induction m using Nat.strong_induction_on generalizing a b with
  | h m ih =>
    by_cases hm0 : m = 0
    · have ha (i : Fin 5) : (a i).natAbs ≤ size a b := by
        exact (Finset.single_le_sum (fun j _ => Nat.zero_le ((a j).natAbs))
          (Finset.mem_univ i)).trans (Nat.le_add_right _ _)
      have hb (i : Fin 5) : (b i).natAbs ≤ size a b := by
        exact (Finset.single_le_sum (fun j _ => Nat.zero_le ((b j).natAbs))
          (Finset.mem_univ i)).trans (Nat.le_add_left _ _)
      constructor
      · intro i
        apply Int.natAbs_eq_zero.mp
        have hi := ha i
        omega
      · intro i
        apply Int.natAbs_eq_zero.mp
        have hi := hb i
        omega
    · obtain ⟨ha, hb⟩ := integer_divisibility a b h
      choose a' ha' using ha
      choose b' hb' using hb
      have hs : size a b = 121*(∑ i, (a' i).natAbs) +
          11*(∑ i, (b' i).natAbs) := by
        simp only [size, ha', hb', Int.natAbs_mul, Finset.mul_sum]
        norm_num
      have hlt : size a' b' < m := by
        dsimp only [size]
        omega
      have hnew : ∑ i, (quad (a' i) (b' i))^5 = 5 := by
        refine comp_nonconstant_injective _ 5 (11*X) ?_ ?_
        · have hd : (11*X : ℤ[X]).natDegree = 1 := by compute_degree; norm_num
          omega
        · rw [sum_comp]
          have hp (i : Fin 5) : ((quad (a' i) (b' i))^5).comp (11*X) =
              (quad (a i) (b i))^5 := by
            rw [ha', hb']
            simp only [quad, pow_comp, add_comp, mul_comp, one_comp, C_comp,
              X_comp, map_mul, map_ofNat]
            ring
          simp_rw [hp]
          simpa using h
      obtain ⟨hza, hzb⟩ := ih (size a' b') hlt a' b' hnew rfl
      constructor
      · intro i
        rw [ha', hza, mul_zero]
      · intro i
        rw [hb', hzb, mul_zero]

/-- A rational quadratic curve through the all-one point cannot have constant
sum of five fifth powers. No symmetry of the five coordinates is assumed. -/
theorem rational_coefficients_zero (a b : Fin 5 → ℚ)
    (h : ∀ t : ℚ, ∑ i, (1 + b i*t + a i*t^2)^5 = 5) :
    (∀ i, a i = 0) ∧ (∀ i, b i = 0) := by
  obtain ⟨da, hda⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) a
  obtain ⟨db, hdb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) b
  choose A hA using hda
  choose B hB using hdb
  have hA' (i) : (A i : ℚ) = (da : ℤ)*a i := by
    simpa [Algebra.smul_def] using hA i
  have hB' (i) : (B i : ℚ) = (db : ℤ)*b i := by
    simpa [Algebra.smul_def] using hB i
  let d : ℤ := (da : ℤ)*(db : ℤ)
  let aa (i : Fin 5) : ℤ := (da : ℤ)*(db : ℤ)^2*A i
  let bb (i : Fin 5) : ℤ := (da : ℤ)*B i
  have haa (i) : (aa i : ℚ) = (d : ℚ)^2*a i := by
    simp only [aa, d, Int.cast_mul, Int.cast_pow, hA']
    ring
  have hbb (i) : (bb i : ℚ) = (d : ℚ)*b i := by
    simp only [bb, d, Int.cast_mul, hB']
    ring
  have heval (t : ℚ) : ∑ i, (1 + (bb i : ℚ)*t + (aa i : ℚ)*t^2)^5 = 5 := by
    convert h ((d : ℚ)*t) using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [haa, hbb]
    ring
  have hp : ∑ i, (quad (aa i) (bb i))^5 = 5 := by
    apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    apply Polynomial.funext
    intro t
    simpa [quad, Polynomial.map_sum, eval_finset_sum] using heval t
  obtain ⟨hza, hzb⟩ := integer_coefficients_zero aa bb hp
  have hd : (d : ℚ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (nonZeroDivisors.coe_ne_zero da)
      (nonZeroDivisors.coe_ne_zero db)
  constructor
  · intro i
    have hz : (d : ℚ)^2*a i = 0 := by rw [← haa, hza]; norm_num
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hd)
  · intro i
    have hz : (d : ℚ)*b i = 0 := by rw [← hbb, hzb]; norm_num
    exact (mul_eq_zero.mp hz).resolve_left hd

end
end Erdos322Research.QuinticQuadraticPositiveBase
