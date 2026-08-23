import FormalConjectures.OddPrimeClassScratch
import FormalConjectures.TwoClassScratch
import FormalConjectures.Explicit8Scratch
import FormalConjectures.Explicit2Scratch

open Finset
noncomputable section

private lemma quadratic_ne_zero_on_unit {N : ℕ} (χ : DirichletCharacter ℂ N)
    (u : (ZMod N)ˣ) : χ (u : ZMod N) ≠ 0 := by
  simpa only [← MulChar.coe_equivToUnitHom] using (χ.toUnitHom u).ne_zero

private lemma primitive_ne_one {N : ℕ} [NeZero N] (hN1 : N ≠ 1)
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) : χ ≠ 1 := by
  intro h
  subst χ
  rw [DirichletCharacter.isPrimitive_def,
    DirichletCharacter.conductor_one (NeZero.ne N)] at hp
  exact hN1 hp.symm

private lemma two_char_eq_of_generators {e : ℕ} (he : 3 ≤ e)
    (χ ψ : DirichletCharacter ℂ (2^e))
    (hm : χ (-1) = ψ (-1)) (h5 : χ 5 = ψ 5) : χ = ψ := by
  apply MulChar.equivToUnitHom.injective
  apply MonoidHom.ext
  intro x
  obtain ⟨⟨b,k⟩, hx⟩ := twoGenMap_surjective he x
  subst x
  apply Units.ext
  simp only [MulChar.coe_equivToUnitHom, twoGenMap, Units.val_mul,
    Units.val_pow_eq_pow_val, map_mul, map_pow, fiveUnit_coe]
  have hm' : χ ((↑(-1 : (ZMod (2^e))ˣ)) : ZMod (2^e)) =
      ψ ((↑(-1 : (ZMod (2^e))ˣ)) : ZMod (2^e)) := by simpa using hm
  rw [hm', h5]

private lemma primitive_two_pow_exponent_le_three {e : ℕ} (he : 0 < e)
    (χ : DirichletCharacter ℂ (2^e)) (hq : χ.IsQuadratic)
    (hp : χ.IsPrimitive) : e ≤ 3 := by
  by_contra hn
  have he3 : 3 ≤ e := by omega
  have hf := quadratic_factorsThrough_eight he3 χ hq
  have hc : χ.conductor ≤ 8 := Nat.sInf_le hf
  rw [DirichletCharacter.isPrimitive_def] at hp
  rw [hp] at hc
  have hp16 : 16 ≤ 2^e := by
    have := pow_le_pow_right₀ (show 1 ≤ (2:ℕ) by omega) (show 4 ≤ e by omega)
    norm_num at this ⊢
    exact this
  omega

private lemma chi4C_quadratic : chi4C.IsQuadratic :=
  ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)
private lemma chi8C_quadratic : chi8C.IsQuadratic :=
  ZMod.isQuadratic_χ₈.comp (Int.castRingHom ℂ)
private lemma chi8'C_quadratic : chi8'C.IsQuadratic :=
  ZMod.isQuadratic_χ₈'.comp (Int.castRingHom ℂ)

private lemma chi4C_ne_one : chi4C ≠ 1 := by
  intro h
  have h3 : chi4C (3 : ZMod 4) = -1 := by
    have hz : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
    simpa [chi4C] using congrArg (fun z : ℤ ↦ (z : ℂ)) hz
  have heq := congrArg (fun η : DirichletCharacter ℂ 4 ↦ η (3 : ZMod 4)) h
  dsimp only at heq
  rw [h3] at heq
  have hu : IsUnit (3 : ZMod 4) := by native_decide
  rw [MulChar.one_apply hu] at heq
  change (-1 : ℂ) = 1 at heq
  norm_num at heq

private lemma level_two_eq_one (χ : DirichletCharacter ℂ 2) : χ = 1 := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := (ZMod 2)ˣ)
  apply (MulChar.eq_iff hg χ 1).2
  have hg1 : g = 1 := Subsingleton.elim _ _
  subst g
  simp

private lemma chi8C_gen_values : chi8C (-1) = 1 ∧ chi8C 5 = -1 := by
  constructor
  · have hz : ZMod.χ₈ (-1 : ZMod 8) = 1 := by decide
    simpa [chi8C] using congrArg (fun z : ℤ ↦ (z : ℂ)) hz
  · have hz : ZMod.χ₈ (5 : ZMod 8) = -1 := by decide
    simpa [chi8C] using congrArg (fun z : ℤ ↦ (z : ℂ)) hz

private lemma chi8'C_gen_values : chi8'C (-1) = -1 ∧ chi8'C 5 = -1 := by
  constructor
  · have hz : ZMod.χ₈' (-1 : ZMod 8) = -1 := by decide
    simpa [chi8'C] using congrArg (fun z : ℤ ↦ (z : ℂ)) hz
  · have hz : ZMod.χ₈' (5 : ZMod 8) = -1 := by decide
    simpa [chi8'C] using congrArg (fun z : ℤ ↦ (z : ℂ)) hz


private lemma factorsThrough_four_of_five_eq_one
    (χ : DirichletCharacter ℂ 8) (h5 : χ (5 : ZMod 8) = 1) :
    χ.FactorsThrough 4 := by
  have h4 : 4 ∣ 8 := by norm_num
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap h4]
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  obtain ⟨⟨b,k⟩, hbk⟩ := twoGenMap_surjective (e := 3) (by omega) x
  subst x
  have hfcast : (ZMod.cast (5 : ZMod 8) : ZMod 4) = 1 := by
    calc
      _ = (5 : ZMod 4) := by
        rw [← ZMod.castHom_apply]
        exact map_natCast (ZMod.castHom h4 (ZMod 4)) 5
      _ = 1 := by decide
  have hc0 := congrArg Units.val hx
  have hc : ((-1 : ZMod 4) ^ b.val) = 1 := by
    simpa [twoGenMap, ZMod.unitsMap_val, fiveUnit_coe,
      ZMod.cast_neg h4, ZMod.cast_one h4, hfcast] using hc0
  have hb : b.val = 0 := by
    have hbcase : b.val = 0 ∨ b.val = 1 := by omega
    rcases hbcase with hb | hb
    · exact hb
    · rw [hb] at hc
      exact ((show (-1 : ZMod 4) ≠ 1 by decide) hc).elim
  apply Units.ext
  simp only [MulChar.coe_toUnitHom, Units.val_one, twoGenMap,
    Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, fiveUnit_coe,
    hb, pow_zero, h5, one_pow, mul_one]

  exact map_one χ

lemma primitive_quadratic_two_pow_root_one {e : ℕ} (he : 0 < e)
    (χ : DirichletCharacter ℂ (2^e)) (hq : χ.IsQuadratic)
    (hp : χ.IsPrimitive) : χ.rootNumber = 1 := by
  have he3 := primitive_two_pow_exponent_le_three he χ hq hp
  have hecases : e = 1 ∨ e = 2 ∨ e = 3 := by omega
  let P : ℕ → Prop := fun n ↦ ∀ (_hn : NeZero n), ∀ ξ : DirichletCharacter ℂ n,
    ξ.IsQuadratic → ξ.IsPrimitive → @DirichletCharacter.rootNumber n _hn ξ = 1
  rcases hecases with he1 | he2 | he3eq
  · have hm : 2^e = 2 := by rw [he1]; norm_num
    have hl : P 2 := by
      intro hn ξ hξq hξp
      have hξ : ξ = 1 := level_two_eq_one ξ
      subst ξ
      rw [DirichletCharacter.isPrimitive_def,
        DirichletCharacter.conductor_one (by norm_num : (2:ℕ) ≠ 0)] at hξp
      norm_num at hξp
    exact (Eq.mpr (congrArg P hm) hl) inferInstance χ hq hp
  · have hm : 2^e = 4 := by rw [he2]; norm_num
    have hl : P 4 := by
      intro hn ξ hξq hξp
      letI : IsCyclic (ZMod 4)ˣ := ZMod.isCyclic_units_two_pow_iff 2 |>.mpr (by omega)
      have hξ1 : ξ ≠ 1 := primitive_ne_one (by norm_num) hξp
      have heq : ξ = chi4C :=
        quadratic_character_unique_of_isCyclic hξq chi4C_quadratic hξ1 chi4C_ne_one
      rw [heq]
      exact chi4C_rootNumber_one
    exact (Eq.mpr (congrArg P hm) hl) inferInstance χ hq hp
  · have hm : 2^e = 8 := by rw [he3eq]; norm_num
    have hl : P 8 := by
      intro hn ξ hξq hξp
      have h5ne : ξ (5 : ZMod 8) ≠ 1 := by
        intro h5
        have hf := factorsThrough_four_of_five_eq_one ξ h5
        have hc : ξ.conductor ≤ 4 := Nat.sInf_le hf
        rw [DirichletCharacter.isPrimitive_def] at hξp
        rw [hξp] at hc
        omega
      have h5nz : ξ (5 : ZMod 8) ≠ 0 := by
        let u : (ZMod 8)ˣ := ZMod.unitOfCoprime 5 (by norm_num)
        have hu : (u : ZMod 8) = 5 := by simp [u]
        simpa [hu] using quadratic_ne_zero_on_unit ξ u
      have h5m : ξ (5 : ZMod 8) = -1 := by
        rcases hξq (5 : ZMod 8) with h | h | h
        · exact (h5nz h).elim
        · exact (h5ne h).elim
        · exact h
      have hmz : ξ (-1 : ZMod 8) ≠ 0 := by
        let u : (ZMod 8)ˣ := -1
        simpa [u] using quadratic_ne_zero_on_unit ξ u
      rcases hξq (-1 : ZMod 8) with hm0 | hm1 | hmm
      · exact (hmz hm0).elim
      · have heq : ξ = chi8C := two_char_eq_of_generators (e:=3) (by omega)
          ξ chi8C (by simpa using hm1.trans chi8C_gen_values.1.symm) (by
            simpa using h5m.trans chi8C_gen_values.2.symm)
        rw [heq]
        exact chi8C_rootNumber_one
      · have heq : ξ = chi8'C := two_char_eq_of_generators (e:=3) (by omega)
          ξ chi8'C (by simpa using hmm.trans chi8'C_gen_values.1.symm) (by
            simpa using h5m.trans chi8'C_gen_values.2.symm)
        rw [heq]
        exact chi8'C_rootNumber_one
    exact (Eq.mpr (congrArg P hm) hl) inferInstance χ hq hp
