import FormalConjectures.TwoRootScratch
import FormalConjectures.GlobalSignScratch

open Finset
noncomputable section

private noncomputable def crtMulEquiv {m n : ℕ} (h : m.Coprime n) :
    ZMod (m*n) ≃* ZMod m × ZMod n where
  toFun := ZMod.chineseRemainder h
  invFun := (ZMod.chineseRemainder h).symm
  left_inv := (ZMod.chineseRemainder h).left_inv
  right_inv := (ZMod.chineseRemainder h).right_inv
  map_mul' := (ZMod.chineseRemainder h).map_mul

private noncomputable def crtUnits {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (crtMulEquiv h)).trans MulEquiv.prodUnits

private noncomputable def crtLeft {m n : ℕ} (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) : DirichletCharacter ℂ m :=
  MulChar.ofUnitHom (χ.toUnitHom.comp
    ((crtUnits h).symm.toMonoidHom.comp (MonoidHom.inl (ZMod m)ˣ (ZMod n)ˣ)))

private noncomputable def crtRight {m n : ℕ} (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) : DirichletCharacter ℂ n :=
  MulChar.ofUnitHom (χ.toUnitHom.comp
    ((crtUnits h).symm.toMonoidHom.comp (MonoidHom.inr (ZMod m)ˣ (ZMod n)ˣ)))

private lemma crtUnits_symm_mul {m n : ℕ} (h : m.Coprime n)
    (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) :
    (crtUnits h).symm (a,b) =
      (crtUnits h).symm (a,1) * (crtUnits h).symm (1,b) := by
  rw [← map_mul]
  simp

lemma eq_prodChar_crt {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) :
    χ = GlobalSign.prodChar (crtLeft h χ) (crtRight h χ) := by
  apply MulChar.equivToUnitHom.injective
  apply MonoidHom.ext
  intro u
  apply Units.ext
  change χ (u : ZMod (m*n)) = GlobalSign.prodChar (crtLeft h χ) (crtRight h χ) (u : ZMod (m*n))
  rw [GlobalSign.prodChar_apply h]
  let um := ZMod.unitsMap (dvd_mul_right m n) u
  let un := ZMod.unitsMap (dvd_mul_left n m) u
  have hmval : (ZMod.cast (u : ZMod (m*n)) : ZMod m) = (um : ZMod m) := by
    exact (ZMod.unitsMap_val _ _).symm
  have hnval : (ZMod.cast (u : ZMod (m*n)) : ZMod n) = (un : ZMod n) := by
    exact (ZMod.unitsMap_val _ _).symm
  rw [hmval, hnval]
  have hl : crtLeft h χ (um : ZMod m) = χ ((crtUnits h).symm (um,1) : ZMod (m*n)) := by
    simp [crtLeft]
  have hr : crtRight h χ (un : ZMod n) = χ ((crtUnits h).symm (1,un) : ZMod (m*n)) := by
    simp [crtRight]
  rw [hl, hr, ← map_mul]
  apply congrArg χ
  rw [← Units.val_mul, ← crtUnits_symm_mul]
  have hpair : crtUnits h u = (um,un) := by
    apply Prod.ext <;> apply Units.ext <;>
      simp [crtUnits, crtMulEquiv, ZMod.chineseRemainder, um, un,
        MulEquiv.prodUnits, ZMod.unitsMap_val]
  have hcu : (crtUnits h).symm (um,un) = u := by
    apply (crtUnits h).injective
    simpa using hpair.symm
  exact congrArg Units.val hcu.symm

private lemma prodChar_factorsThrough_left {m n d : ℕ}
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n)
    (hf : α.FactorsThrough d) :
    (GlobalSign.prodChar α β).FactorsThrough (d*n) := by
  obtain ⟨hd, α₀, ha⟩ := hf
  have hdn : d*n ∣ m*n := Nat.mul_dvd_mul_right hd n
  refine ⟨hdn, GlobalSign.prodChar α₀ β, ?_⟩
  subst α
  simp only [GlobalSign.prodChar, map_mul]
  apply congrArg₂ (· * ·)
  · exact (DirichletCharacter.changeLevel_trans α₀ hd (dvd_mul_right m n)).symm.trans
      (DirichletCharacter.changeLevel_trans α₀ (dvd_mul_right d n) hdn)
  · exact DirichletCharacter.changeLevel_trans β (dvd_mul_left n d) hdn

private lemma prodChar_factorsThrough_right {m n d : ℕ}
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n)
    (hf : β.FactorsThrough d) :
    (GlobalSign.prodChar α β).FactorsThrough (m*d) := by
  obtain ⟨hd, β₀, hb⟩ := hf
  have hmd : m*d ∣ m*n := Nat.mul_dvd_mul_left m hd
  refine ⟨hmd, GlobalSign.prodChar α β₀, ?_⟩
  subst β
  simp only [GlobalSign.prodChar, map_mul]
  apply congrArg₂ (· * ·)
  · exact DirichletCharacter.changeLevel_trans α (dvd_mul_right m d) hmd
  · exact (DirichletCharacter.changeLevel_trans β₀ hd (dvd_mul_left n m)).symm.trans
      (DirichletCharacter.changeLevel_trans β₀ (dvd_mul_left d m) hmd)


lemma crtLeft_primitive {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) (hp : χ.IsPrimitive) :
    (crtLeft h χ).IsPrimitive := by
  let α := crtLeft h χ
  let β := crtRight h χ
  have heq := eq_prodChar_crt h χ
  have hf := (α.factorsThrough_conductor)
  have hfg := prodChar_factorsThrough_left α β hf
  have hc : χ.conductor ≤ α.conductor * n := by
    rw [heq]
    exact Nat.sInf_le hfg
  rw [DirichletCharacter.isPrimitive_def] at hp ⊢
  rw [hp] at hc
  have hn : 0 < n := NeZero.pos n
  have hma : m ≤ α.conductor :=
    Nat.le_of_mul_le_mul_right (by simpa [mul_assoc, mul_comm, mul_left_comm] using hc)
      (NeZero.pos n)
  exact le_antisymm (Nat.le_of_dvd (NeZero.pos m) α.conductor_dvd_level) hma

lemma crtRight_primitive {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) (hp : χ.IsPrimitive) :
    (crtRight h χ).IsPrimitive := by
  let α := crtLeft h χ
  let β := crtRight h χ
  have heq := eq_prodChar_crt h χ
  have hf := β.factorsThrough_conductor
  have hfg := prodChar_factorsThrough_right α β hf
  have hc : χ.conductor ≤ m * β.conductor := by
    rw [heq]
    exact Nat.sInf_le hfg
  rw [DirichletCharacter.isPrimitive_def] at hp ⊢
  rw [hp] at hc
  have hnb : n ≤ β.conductor :=
    Nat.le_of_mul_le_mul_left (by simpa [mul_assoc, mul_comm, mul_left_comm] using hc)
      (NeZero.pos m)
  exact le_antisymm (Nat.le_of_dvd (NeZero.pos n) β.conductor_dvd_level) hnb

lemma crtLeft_quadratic {m n : ℕ} (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) (hq : χ.IsQuadratic) :
    (crtLeft h χ).IsQuadratic := by
  intro x
  by_cases hx : IsUnit x
  · let u := hx.unit
    have hux : (u : ZMod m) = x := hx.unit_spec
    have hv : crtLeft h χ x = χ ((crtUnits h).symm (u,1) : ZMod (m*n)) := by
      rw [← hux]
      simp [crtLeft]
    rw [hv]
    exact hq _
  · left
    exact MulChar.map_nonunit _ hx

lemma crtRight_quadratic {m n : ℕ} (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) (hq : χ.IsQuadratic) :
    (crtRight h χ).IsQuadratic := by
  intro x
  by_cases hx : IsUnit x
  · let u := hx.unit
    have hux : (u : ZMod n) = x := hx.unit_spec
    have hv : crtRight h χ x = χ ((crtUnits h).symm (1,u) : ZMod (m*n)) := by
      rw [← hux]
      simp [crtRight]
    rw [hv]
    exact hq _
  · left
    exact MulChar.map_nonunit _ hx
