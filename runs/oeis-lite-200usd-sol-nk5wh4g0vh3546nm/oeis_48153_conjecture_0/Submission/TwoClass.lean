import FormalConjectures.Util.ProblemImports

open Finset
open scoped BigOperators
noncomputable section

private lemma quadratic_ne_zero_on_unit {N : ℕ} (χ : DirichletCharacter ℂ N)
    (u : (ZMod N)ˣ) : χ (u : ZMod N) ≠ 0 := by
  simpa only [← MulChar.coe_equivToUnitHom] using (χ.toUnitHom u).ne_zero


def fiveUnit (e : ℕ) : (ZMod (2 ^ e))ˣ :=
  ZMod.unitOfCoprime 5 ((by norm_num : Nat.Coprime 5 2).pow_right e)

lemma fiveUnit_coe (e : ℕ) :
    ((fiveUnit e : (ZMod (2 ^ e))ˣ) : ZMod (2 ^ e)) = 5 := by
  simp [fiveUnit]

private lemma orderOf_fiveUnit {e : ℕ} (he : 2 ≤ e) :
    orderOf (fiveUnit e) = 2 ^ (e - 2) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [← orderOf_units, fiveUnit_coe]
  rw [add_comm 2 d]
  simpa [Nat.add_sub_cancel_left] using ZMod.orderOf_five d

def twoGenMap (e : ℕ) : Fin 2 × Fin (2 ^ (e-2)) → (ZMod (2^e))ˣ :=
  fun z ↦ (-1) ^ z.1.val * fiveUnit e ^ z.2.val

private lemma twoGenMap_injective {e : ℕ} (he : 3 ≤ e) :
    Function.Injective (twoGenMap e) := by
  rintro ⟨b,k⟩ ⟨b',k'⟩ h
  have h4 : 4 ∣ 2 ^ e := by
    rw [show 4 = 2^2 by norm_num]
    exact pow_dvd_pow 2 (by omega)
  have hc := congrArg (fun u : (ZMod (2^e))ˣ ↦
    ZMod.castHom h4 (ZMod 4) (u : ZMod (2^e))) h
  simp only [twoGenMap, Units.val_mul, Units.val_pow_eq_pow_val,
    map_mul, map_pow, map_neg, map_one, fiveUnit_coe] at hc
  simp only [map_ofNat] at hc
  have hfive : (5 : ZMod 4) = 1 := by decide
  simp only [hfive, one_pow] at hc
  norm_num at hc
  simp only [ZMod.cast_neg h4, ZMod.cast_one h4] at hc
  have hb : b = b' := by
    fin_cases b <;> fin_cases b'
    · rfl
    · exfalso
      apply (show (1 : ZMod 4) ≠ -1 by decide)
      simpa using hc
    · exfalso
      apply (show (-1 : ZMod 4) ≠ 1 by decide)
      simpa using hc
    · rfl
  subst b'
  have hpow : fiveUnit e ^ k.val = fiveUnit e ^ k'.val := mul_left_cancel h
  have hk : k.val = k'.val := by
    apply pow_injOn_Iio_orderOf (x := fiveUnit e)
    · rw [orderOf_fiveUnit (by omega)]
      exact k.isLt
    · rw [orderOf_fiveUnit (by omega)]
      exact k'.isLt
    · exact hpow
  exact Prod.ext rfl (Fin.ext hk)

private lemma card_twoGen_domain {e : ℕ} (he : 3 ≤ e) :
    Fintype.card (Fin 2 × Fin (2^(e-2))) = Fintype.card (ZMod (2^e))ˣ := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega)]
  norm_num
  have heq : e - 1 = (e - 2) + 1 := by omega
  rw [heq, pow_succ]
  ring

lemma twoGenMap_surjective {e : ℕ} (he : 3 ≤ e) :
    Function.Surjective (twoGenMap e) :=
  ((Fintype.bijective_iff_injective_and_card (twoGenMap e)).2
    ⟨twoGenMap_injective he, card_twoGen_domain he⟩).2

private lemma five_order_eight : orderOf (5 : ZMod 8) = 2 := by
  simpa using ZMod.orderOf_five 1

lemma quadratic_factorsThrough_eight {e : ℕ} (he : 3 ≤ e)
    (χ : DirichletCharacter ℂ (2^e)) (hχ : χ.IsQuadratic) :
    χ.FactorsThrough 8 := by
  have h8 : 8 ∣ 2^e := by
    rw [show 8 = 2^3 by norm_num]
    exact pow_dvd_pow 2 he
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap h8]
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  obtain ⟨⟨b,k⟩, hbk⟩ := twoGenMap_surjective he x
  subst x
  have hc0 := congrArg Units.val hx
  have hc' : ((-1 : ZMod 8) ^ b.val) *
      (ZMod.cast (5 : ZMod (2^e)) : ZMod 8) ^ k.val = 1 := by
    simpa [twoGenMap, ZMod.unitsMap_val, fiveUnit_coe,
      ZMod.cast_neg h8, ZMod.cast_one h8] using hc0
  have hf : (ZMod.cast (5 : ZMod (2^e)) : ZMod 8) = 5 := by
    rw [← ZMod.castHom_apply]
    exact map_natCast (ZMod.castHom h8 (ZMod 8)) 5
  have hc : ((-1 : ZMod 8) ^ b.val) * (5 : ZMod 8) ^ k.val = 1 := by
    rw [hf] at hc'
    exact hc'
  rw [← pow_mod_orderOf (5 : ZMod 8) k.val, five_order_eight] at hc
  have hbcase : b.val = 0 ∨ b.val = 1 := by omega
  have hkcase : k.val % 2 = 0 ∨ k.val % 2 = 1 := by
    have := Nat.mod_lt k.val (by norm_num : 0 < 2)
    omega
  have hb0 : b.val = 0 := by
    rcases hbcase with hb | hb
    · exact hb
    rcases hkcase with hk | hk
    · rw [hb, hk] at hc
      exact ((show (-1 : ZMod 8) ≠ 1 by decide) hc).elim
    · rw [hb, hk] at hc
      exact ((show (-5 : ZMod 8) ≠ 1 by decide) hc).elim
  have hk0 : k.val % 2 = 0 := by
    rcases hkcase with hk | hk
    · exact hk
    rw [hb0, hk] at hc
    exact ((show (5 : ZMod 8) ≠ 1 by decide) hc).elim
  have hke : Even k.val := Nat.even_iff.mpr hk0
  obtain ⟨t, ht⟩ := hke
  have hsquare : IsSquare (twoGenMap e (b,k)) := by
    refine ⟨fiveUnit e ^ t, ?_⟩
    simp only [twoGenMap, hb0, pow_zero, one_mul, pow_two, ht, pow_add]
  obtain ⟨y, hy⟩ := hsquare
  apply Units.ext
  simp only [MulChar.coe_toUnitHom, Units.val_one]
  rw [hy]
  change χ ((y : ZMod (2^e)) * (y : ZMod (2^e))) = 1
  rw [map_mul]
  rcases hχ (y : ZMod (2^e)) with hy0 | hy1 | hym
  · exact (quadratic_ne_zero_on_unit χ y hy0).elim
  · rw [hy1]; norm_num
  · rw [hym]; norm_num

