import FormalConjectures.PrimeSignScratch

open Finset
open scoped BigOperators
noncomputable section

private lemma quadratic_ne_zero_on_unit {N : ℕ} (χ : DirichletCharacter ℂ N)
    (u : (ZMod N)ˣ) : χ (u : ZMod N) ≠ 0 := by
  simpa only [← MulChar.coe_equivToUnitHom] using (χ.toUnitHom u).ne_zero

lemma quadratic_character_unique_of_isCyclic {N : ℕ} [IsCyclic (ZMod N)ˣ]
    {χ ψ : DirichletCharacter ℂ N} (hχq : χ.IsQuadratic) (hψq : ψ.IsQuadratic)
    (hχ1 : χ ≠ 1) (hψ1 : ψ ≠ 1) : χ = ψ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod N)ˣ)
  apply (MulChar.eq_iff hg χ ψ).2
  have hχg1 : χ (g : ZMod N) ≠ 1 := by
    intro he
    apply hχ1
    apply (MulChar.eq_iff hg χ 1).2
    simpa using he
  have hψg1 : ψ (g : ZMod N) ≠ 1 := by
    intro he
    apply hψ1
    apply (MulChar.eq_iff hg ψ 1).2
    simpa using he
  rcases hχq (g : ZMod N) with hχ0 | hχp | hχm
  · exact (quadratic_ne_zero_on_unit χ g hχ0).elim
  · exact (hχg1 hχp).elim
  · rcases hψq (g : ZMod N) with hψ0 | hψp | hψm
    · exact (quadratic_ne_zero_on_unit ψ g hψ0).elim
    · exact (hψg1 hψp).elim
    · rw [hχm, hψm]

private noncomputable def primeQuadratic (p : ℕ) [Fact p.Prime] :
    DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

private lemma primeQuadratic_quadratic (p : ℕ) [Fact p.Prime] :
    (primeQuadratic p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

private lemma primeQuadratic_ne_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    primeQuadratic p ≠ 1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    simpa [ZMod.ringChar_zmod_n] using hp2
  exact (MulChar.ringHomComp_ne_one_iff
    (Int.cast_injective : Function.Injective (fun z : ℤ ↦ (z : ℂ)))).mpr
      (quadraticChar_ne_one hchar)

private lemma changeLevel_quadratic {m n : ℕ} (h : m ∣ n)
    {χ : DirichletCharacter ℂ m} (hq : χ.IsQuadratic) :
    (DirichletCharacter.changeLevel h χ).IsQuadratic := by
  rw [MulChar.isQuadratic_iff_sq_eq_one] at hq ⊢
  rw [← map_pow, hq, map_one]

private lemma primitive_ne_one {N : ℕ} [NeZero N] (hN1 : N ≠ 1)
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) : χ ≠ 1 := by
  intro h
  subst χ
  rw [DirichletCharacter.isPrimitive_def,
    DirichletCharacter.conductor_one (NeZero.ne N)] at hp
  exact hN1 hp.symm

lemma primitive_quadratic_odd_prime_pow_level_one
    (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 0 < e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχq : χ.IsQuadratic)
    (hχp : χ.IsPrimitive) : e = 1 := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpow0 : p ^ e ≠ 0 := pow_ne_zero _ hp0
  letI : NeZero (p ^ e) := ⟨hpow0⟩
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hN1 : p ^ e ≠ 1 := by
    exact ne_of_gt (one_lt_pow₀ hp1 he.ne')
  have hχ1 := primitive_ne_one hN1 hχp
  have hd : p ∣ p ^ e := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    simp [pow_succ]
  let legLift : DirichletCharacter ℂ (p ^ e) :=
    DirichletCharacter.changeLevel hd (primeQuadratic p)
  have hlegq : legLift.IsQuadratic := changeLevel_quadratic hd (primeQuadratic_quadratic p)
  have hleg1 : legLift ≠ 1 := by
    intro hl
    apply primeQuadratic_ne_one hp2
    apply DirichletCharacter.changeLevel_injective hd
    simpa [legLift] using hl
  letI : IsCyclic (ZMod (p ^ e))ˣ :=
    ZMod.isCyclic_units_of_prime_pow p Fact.out hp2 e
  have heq : χ = legLift := quadratic_character_unique_of_isCyclic hχq hlegq hχ1 hleg1
  have hf : χ.FactorsThrough p := ⟨hd, primeQuadratic p, heq⟩
  have hc_le : χ.conductor ≤ p := Nat.sInf_le hf
  rw [DirichletCharacter.isPrimitive_def] at hχp
  rw [hχp] at hc_le
  have hpow_le : p ^ e ≤ p := hc_le
  by_contra he1
  have he2 : 2 ≤ e := (Nat.one_lt_iff_ne_zero_and_ne_one).2 ⟨he.ne', he1⟩
  have hp2le : p ^ 2 ≤ p ^ e := pow_le_pow_right₀ hp1.le he2
  nlinarith [show 2 ≤ p from hp1]

lemma primitive_quadratic_odd_prime_pow_root_one
    (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 0 < e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχq : χ.IsQuadratic)
    (hχp : χ.IsPrimitive) : χ.rootNumber = 1 := by
  have heq := primitive_quadratic_odd_prime_pow_level_one p e hp2 he χ hχq hχp
  have hmod : p ^ e = p := by rw [heq, pow_one]
  let P : ℕ → Prop := fun n ↦ ∀ (_hn : NeZero n), ∀ ξ : DirichletCharacter ℂ n,
    ξ.IsQuadratic → ξ.IsPrimitive → @DirichletCharacter.rootNumber n _hn ξ = 1
  have hlocal : P p := by
    intro hn ξ hξq hξp
    letI : NeZero p := hn
    letI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime Fact.out
    have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
    have hξ1 : ξ ≠ 1 := primitive_ne_one hp1 hξp
    have hEq : ξ = primeQuadratic p :=
      quadratic_character_unique_of_isCyclic hξq (primeQuadratic_quadratic p)
        hξ1 (primeQuadratic_ne_one hp2)
    rw [hEq]
    rcases (Fact.out : p.Prime).eq_two_or_odd with hp | hpodd
    · exact (hp2 hp).elim
    · have ho : Odd p := Nat.odd_iff.mpr hpodd
      obtain ⟨m, hm⟩ := ho
      exact PrimeSign.prime_quadratic_rootNumber_one p m (by
        simpa [primeQuadratic, two_mul] using hm)
  have hback : P (p ^ e) := Eq.mpr (congrArg P hmod) hlocal
  exact hback inferInstance χ hχq hχp

