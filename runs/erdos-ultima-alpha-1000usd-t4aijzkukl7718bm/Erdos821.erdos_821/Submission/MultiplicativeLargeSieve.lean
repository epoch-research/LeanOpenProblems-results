import Submission.AdditiveLargeSieve

/-!
# Passing from additive sums to primitive Dirichlet characters

This file develops analytic upper bounds. It does not assert prime-count
lower bounds or settle Erdős 821.
-/

open scoped BigOperators
open Finset

namespace Erdos821.AnalyticSieve

lemma conductor_inv_eq {q : ℕ} (χ : DirichletCharacter ℂ q) :
    χ⁻¹.conductor = χ.conductor := by
  have hf {χ : DirichletCharacter ℂ q} {d : ℕ} (h : χ.FactorsThrough d) :
      χ⁻¹.FactorsThrough d := by
    obtain ⟨hd, ψ, hψ⟩ := h
    exact ⟨hd, ψ⁻¹, by rw [hψ, map_inv]⟩
  have heq : χ⁻¹.conductorSet = χ.conductorSet := by
    ext d
    constructor
    · intro h
      simpa only [inv_inv] using hf h
    · exact hf
  exact congrArg sInf heq

lemma primitive_inv {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    χ⁻¹.IsPrimitive := by
  change χ⁻¹.conductor = q
  rw [conductor_inv_eq]
  exact hχ

section FixedModulus

variable {q : ℕ} [NeZero q]

lemma conj_stdAddChar (x : ZMod q) :
    (starRingEnd ℂ) (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj]
  exact Circle.norm_coe _

lemma conj_gaussSum (χ : DirichletCharacter ℂ q) :
    (starRingEnd ℂ) (gaussSum χ ZMod.stdAddChar) =
      ∑ x : ZMod q, ZMod.stdAddChar x * χ⁻¹ (-x) := by
  simp only [gaussSum, map_sum, map_mul, conj_stdAddChar]
  have hc (x : ZMod q) : (starRingEnd ℂ) (χ x) = χ⁻¹ x := MulChar.star_apply' χ x
  simp only [hc]
  apply Fintype.sum_equiv (Equiv.neg (ZMod q))
  intro x
  simp only [Equiv.neg_apply, neg_neg, mul_comm]

/-- The usual squared norm of the Gauss sum, including the primitive
character of modulus one. -/
lemma primitive_gaussSum_norm_sq {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (q : ℝ) := by
  have hi := congrFun (ZMod.dft_dft (⇑χ)) (-1)
  rw [ZMod.dft_apply] at hi
  simp only [hχ.fourierTransform_eq_inv_mul_gaussSum, mul_neg_one, neg_neg,
    smul_eq_mul, map_one, mul_one] at hi
  have hh : (∑ x : ZMod q, ZMod.stdAddChar x * χ⁻¹ (-x)) *
      gaussSum χ ZMod.stdAddChar = (q : ℂ) := by
    simpa only [Finset.sum_mul, mul_assoc] using hi
  rw [← conj_gaussSum, mul_comm, Complex.mul_conj'] at hh
  exact_mod_cast hh

lemma unit_character_orthogonality (u v : (ZMod q)ˣ) :
    (∑ χ : DirichletCharacter ℂ q, χ u * (starRingEnd ℂ) (χ v)) =
      if u = v then (q.totient : ℂ) else 0 := by
  have hc (χ : DirichletCharacter ℂ q) : (starRingEnd ℂ) (χ v) = χ ((v : ZMod q)⁻¹) := by
    rw [show (starRingEnd ℂ) (χ v) = χ⁻¹ v from MulChar.star_apply' χ v,
      MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
  calc
    _ = ∑ χ : DirichletCharacter ℂ q, χ ((v : ZMod q)⁻¹) * χ u := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [hc, mul_comm]
    _ = if (v : ZMod q) = u then (q.totient : ℂ) else 0 :=
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ v.isUnit (u : ZMod q)
    _ = _ := by
      simp only [show ((v : ZMod q) = u) ↔ u = v from
        ⟨fun h => (Units.val_injective h).symm, fun h => congrArg Units.val h.symm⟩]

/-- Parseval for characters of the finite unit group. -/
lemma unit_character_parseval (b : (ZMod q)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, b u * χ u‖ ^ 2) =
      (q.totient : ℝ) * ∑ u : (ZMod q)ˣ, ‖b u‖ ^ 2 := by
  classical
  have hexpand (χ : DirichletCharacter ℂ q) :
      ((‖∑ u : (ZMod q)ˣ, b u * χ u‖ ^ 2 : ℝ) : ℂ) =
        ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
          (b u * (starRingEnd ℂ) (b v)) * (χ u * (starRingEnd ℂ) (χ v)) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [map_sum, map_mul, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    ring
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, hexpand, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_pow]
  rw [Finset.sum_comm]
  calc
    _ = ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
        (b u * (starRingEnd ℂ) (b v)) *
          (∑ χ : DirichletCharacter ℂ q, χ u * (starRingEnd ℂ) (χ v)) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      simp only [unit_character_orthogonality, mul_ite, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, Complex.mul_conj', ← Finset.sum_mul]
      ring

lemma sum_eq_sum_units (f : ZMod q → ℂ) (hf : ∀ x, ¬IsUnit x → f x = 0) :
    (∑ x : ZMod q, f x) = ∑ u : (ZMod q)ˣ, f u := by
  classical
  symm
  apply Finset.sum_bij_ne_zero (fun (u : (ZMod q)ˣ) _ _ => (u : ZMod q)) (fun _ _ _ => Finset.mem_univ _)
  · intro u hu hfu v hv hfv huv
    exact Units.val_injective huv
  · intro x hx hfx
    have hu : IsUnit x := by by_contra hn; exact hfx (hf x hn)
    exact ⟨hu.unit, Finset.mem_univ _, by simpa only [hu.unit_spec] using hfx, hu.unit_spec⟩
  · intro u hu hfu
    rfl

lemma stdAddChar_int_mul (n : ℤ) (u : ZMod q) :
    ZMod.stdAddChar ((n : ZMod q) * u) = wave n ((u.val : ℝ) / q) := by
  have hcast : (n : ZMod q) * u = ((n * u.val : ℤ) : ZMod q) := by
    simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [hcast, ZMod.stdAddChar_coe]
  unfold wave
  push_cast
  congr 1
  ring

noncomputable def characterSum (A : Finset ℤ) (a : ℤ → ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ A, a n * χ (n : ZMod q)

lemma primitive_characterSum_gauss {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (A : Finset ℤ) (a : ℤ → ℂ) :
    characterSum A a χ⁻¹ * gaussSum χ ZMod.stdAddChar =
      ∑ u : (ZMod q)ˣ, χ u * trigSum A a ((u.val.val : ℝ) / q) := by
  classical
  calc
    _ = ∑ n ∈ A, a n * gaussSum χ (ZMod.stdAddChar.mulShift (n : ZMod q)) := by
      simp only [characterSum, Finset.sum_mul, gaussSum_mulShift_of_isPrimitive _ hχ, mul_assoc]
    _ = ∑ u : ZMod q, χ u * (∑ n ∈ A, a n * ZMod.stdAddChar ((n : ZMod q) * u)) := by
      simp only [gaussSum, AddChar.mulShift_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = ∑ u : (ZMod q)ˣ, χ u * (∑ n ∈ A, a n * ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q))) :=
      sum_eq_sum_units _ (fun u hu => by rw [χ.map_nonunit hu, zero_mul])
    _ = _ := by simp only [stdAddChar_int_mul, trigSum]

lemma primitive_characterSum_norm_sq {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (A : Finset ℤ) (a : ℤ → ℂ) :
    (q : ℝ) * ‖characterSum A a χ‖ ^ 2 =
      ‖∑ u : (ZMod q)ˣ, χ⁻¹ u * trigSum A a ((u.val.val : ℝ) / q)‖ ^ 2 := by
  have h := congrArg (fun z : ℂ => ‖z‖ ^ 2) (primitive_characterSum_gauss (primitive_inv hχ) A a)
  simpa only [inv_inv, norm_mul, mul_pow, primitive_gaussSum_norm_sq (primitive_inv hχ), mul_comm] using h

lemma unit_character_inverse_parseval (b : (ZMod q)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, χ⁻¹ u * b u‖ ^ 2) =
      (q.totient : ℝ) * ∑ u : (ZMod q)ˣ, ‖b u‖ ^ 2 := by
  calc
    _ = ∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, b u * χ u‖ ^ 2 := by
      apply Fintype.sum_equiv (Equiv.inv (DirichletCharacter ℂ q))
      intro χ
      simp only [Equiv.inv_apply, mul_comm]
    _ = _ := unit_character_parseval b

/-- At one modulus, orthogonality bounds any family of primitive character
sums by additive sums at the reduced residue fractions. -/
lemma primitive_characterSum_family_bound (C : Finset (DirichletCharacter ℂ q))
    (hC : ∀ χ ∈ C, χ.IsPrimitive) (A : Finset ℤ) (a : ℤ → ℂ) :
    ((q : ℝ) / q.totient) * (∑ χ ∈ C, ‖characterSum A a χ‖ ^ 2) ≤
      ∑ u : (ZMod q)ˣ, ‖trigSum A a ((u.val.val : ℝ) / q)‖ ^ 2 := by
  classical
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have h : (q : ℝ) * (∑ χ ∈ C, ‖characterSum A a χ‖ ^ 2) ≤
      (q.totient : ℝ) * ∑ u : (ZMod q)ˣ, ‖trigSum A a ((u.val.val : ℝ) / q)‖ ^ 2 := by
    calc
      _ = ∑ χ ∈ C, ‖∑ u : (ZMod q)ˣ, χ⁻¹ u * trigSum A a ((u.val.val : ℝ) / q)‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun χ hχ => primitive_characterSum_norm_sq (hC χ hχ) A a)
      _ ≤ ∑ χ : DirichletCharacter ℂ q,
          ‖∑ u : (ZMod q)ˣ, χ⁻¹ u * trigSum A a ((u.val.val : ℝ) / q)‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (fun _ _ _ => sq_nonneg _)
      _ = _ := unit_character_inverse_parseval _
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hφ).mpr
  convert h using 1; ring

end FixedModulus

/-- A reduced residue with its positive modulus. -/
abbrev ReducedResidue := Σ q : ℕ+, (ZMod (q : ℕ))ˣ

def reducedFraction (z : ReducedResidue) : ℚ := mkRat (z.2.val.val : ℤ) z.1

lemma reducedResidue_coprime (z : ReducedResidue) :
    z.2.val.val.Coprime (z.1 : ℕ) := by
  apply (ZMod.isUnit_iff_coprime _ _).mp
  rw [ZMod.natCast_zmod_val]
  exact z.2.isUnit

lemma reducedFraction_den (z : ReducedResidue) :
    (reducedFraction z).den = (z.1 : ℕ) := by
  simp only [reducedFraction, Rat.den_mkRat, PNat.ne_zero, if_false, Int.natAbs_natCast,
    (reducedResidue_coprime z).symm.gcd_eq_one, Nat.div_one]

lemma reducedFraction_num (z : ReducedResidue) :
    (reducedFraction z).num = (z.2.val.val : ℤ) := by
  simp only [reducedFraction, Rat.num_mkRat, PNat.ne_zero, if_false, Int.natAbs_natCast,
    (reducedResidue_coprime z).symm.gcd_eq_one, Nat.cast_one, Int.ediv_one]

lemma reducedFraction_cast (z : ReducedResidue) :
    (reducedFraction z : ℝ) = (z.2.val.val : ℝ) / (z.1 : ℕ) := by
  rw [Rat.cast_def, reducedFraction_den, reducedFraction_num, Int.cast_natCast]

lemma reducedFraction_mem_unit_interval (z : ReducedResidue) :
    0 ≤ reducedFraction z ∧ reducedFraction z ≤ 1 := by
  have hq : (0 : ℚ) < (z.1 : ℕ) := by exact_mod_cast z.1.pos
  rw [reducedFraction, Rat.mkRat_eq_div]
  constructor
  · positivity
  · apply (div_le_one hq).mpr
    exact_mod_cast (ZMod.val_lt z.2.val).le

lemma reducedFraction_injective : Function.Injective reducedFraction := by
  rintro ⟨q, u⟩ ⟨r, v⟩ h
  have hd := congrArg Rat.den h
  rw [reducedFraction_den, reducedFraction_den] at hd
  have hqr : q = r := PNat.coe_inj.mp hd
  subst r
  have hn := congrArg Rat.num h
  rw [reducedFraction_num, reducedFraction_num] at hn
  have huv : u = v := by
    apply Units.val_injective
    apply ZMod.val_injective
    exact_mod_cast hn
  subst v
  rfl

lemma reducedResidue_additive_bound (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q)
    (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (A : Finset ℤ) (a : ℤ → ℂ) (N : ℝ) (hN : 0 ≤ N)
    (hA : ∀ n ∈ A, |(n : ℝ)| ≤ N) :
    (∑ q ∈ M, ∑ u : (ZMod (q : ℕ))ˣ,
      ‖trigSum A a ((u.val.val : ℝ) / (q : ℕ))‖ ^ 2) ≤
        (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * N + 1)) * ∑ n ∈ A, ‖a n‖ ^ 2 := by
  classical
  let F : Finset ReducedResidue := M.sigma (fun q => (Finset.univ : Finset (ZMod (q : ℕ))ˣ))
  let R := F.image reducedFraction
  have hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ 1 ∧ r.den ≤ Q := by
    intro r hr
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
    have hq : z.1 ∈ M := (Finset.mem_sigma.mp hz).1
    exact ⟨(reducedFraction_mem_unit_interval z).1, (reducedFraction_mem_unit_interval z).2,
      by rw [reducedFraction_den]; exact hM z.1 hq⟩
  have h := rational_large_sieve R Q hQ hR A a N hN hA
  have hsum : (∑ r ∈ R, ‖trigSum A a (r : ℝ)‖ ^ 2) =
      ∑ q ∈ M, ∑ u : (ZMod (q : ℕ))ˣ, ‖trigSum A a ((u.val.val : ℝ) / (q : ℕ))‖ ^ 2 := by
    rw [Finset.sum_image (fun _ _ _ _ heq => reducedFraction_injective heq)]
    simp only [F, Finset.sum_sigma, reducedFraction_cast]
  rwa [hsum] at h

/-- A multiplicative large sieve for arbitrary finite families of primitive
Dirichlet characters at positive moduli bounded by `Q`. -/
theorem multiplicative_large_sieve (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q)
    (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive)
    (A : Finset ℤ) (a : ℤ → ℂ) (N : ℝ) (hN : 0 ≤ N)
    (hA : ∀ n ∈ A, |(n : ℝ)| ≤ N) :
    (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient *
      (∑ χ ∈ C q, ‖characterSum A a χ‖ ^ 2)) ≤
        (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * N + 1)) * ∑ n ∈ A, ‖a n‖ ^ 2 := by
  calc
    _ ≤ ∑ q ∈ M, ∑ u : (ZMod (q : ℕ))ˣ,
        ‖trigSum A a ((u.val.val : ℝ) / (q : ℕ))‖ ^ 2 :=
      Finset.sum_le_sum (fun q hq => primitive_characterSum_family_bound (C q) (hC q hq) A a)
    _ ≤ _ := reducedResidue_additive_bound M Q hQ hM A a N hN hA

lemma weighted_sum_mul_sq_le {ι : Type*} (I : Finset ι) (w u v : ι → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i) :
    (∑ i ∈ I, w i * u i * v i) ^ 2 ≤
      (∑ i ∈ I, w i * (u i) ^ 2) * (∑ i ∈ I, w i * (v i) ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq I
    (fun i => Real.sqrt (w i) * u i) (fun i => Real.sqrt (w i) * v i)
  have hm : (∑ i ∈ I, (Real.sqrt (w i) * u i) * (Real.sqrt (w i) * v i)) =
      ∑ i ∈ I, w i * u i * v i := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = (Real.sqrt (w i)) ^ 2 * u i * v i := by ring
      _ = _ := by rw [Real.sq_sqrt (hw i hi)]
  have hs (f : ι → ℝ) : (∑ i ∈ I, (Real.sqrt (w i) * f i) ^ 2) =
      ∑ i ∈ I, w i * (f i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rwa [hm, hs u, hs v] at h

/-- A rectangular bilinear consequence of the multiplicative large sieve.
This does not include a hyperbolic cutoff `m*n <= X`. -/
theorem bilinear_characterSum_large_sieve (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q)
    (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive)
    (A B : Finset ℤ) (a b : ℤ → ℂ) (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hA : ∀ n ∈ A, |(n : ℝ)| ≤ X) (hB : ∀ n ∈ B, |(n : ℝ)| ≤ Y) :
    (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient *
      (∑ χ ∈ C q, ‖characterSum A a χ‖ * ‖characterSum B b χ‖)) ^ 2 ≤
        (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1)) *
        (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * Y + 1)) *
        (∑ n ∈ A, ‖a n‖ ^ 2) * (∑ n ∈ B, ‖b n‖ ^ 2) := by
  classical
  have hc := weighted_sum_mul_sq_le (M.sigma C)
    (fun z => ((z.1 : ℕ) : ℝ) / (z.1 : ℕ).totient)
    (fun z => ‖characterSum A a z.2‖) (fun z => ‖characterSum B b z.2‖)
    (fun z _ => by positivity)
  simp only [Finset.sum_sigma, ← Finset.mul_sum, mul_assoc] at hc
  have hleft := multiplicative_large_sieve M Q hQ hM C hC A a X hX hA
  have hright := multiplicative_large_sieve M Q hQ hM C hC B b Y hY hB
  have hp := mul_le_mul hleft hright (by positivity) (by positivity)
  have h := hc.trans hp
  convert h using 1; ring

lemma characterSum_mul_eq_rectangle {q : ℕ} (χ : DirichletCharacter ℂ q)
    (A B : Finset ℤ) (a b : ℤ → ℂ) :
    characterSum A a χ * characterSum B b χ =
      ∑ m ∈ A, ∑ n ∈ B, (a m * b n) * χ ((m * n : ℤ) : ZMod q) := by
  simp only [characterSum, Finset.sum_mul_sum, Int.cast_mul, map_mul]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  ring

#print axioms bilinear_characterSum_large_sieve

#print axioms primitive_characterSum_family_bound
#print axioms reducedFraction_injective
#print axioms reducedResidue_additive_bound
#print axioms multiplicative_large_sieve

#print axioms primitive_gaussSum_norm_sq
#print axioms unit_character_parseval

end Erdos821.AnalyticSieve
