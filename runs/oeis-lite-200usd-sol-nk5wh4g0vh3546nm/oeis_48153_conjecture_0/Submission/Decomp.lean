import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 1000000

open Finset
open scoped BigOperators

namespace Decomp

private lemma gcd_partition_sum {M : Type*} [AddCommMonoid M]
    (n : ℕ) (hn : 0 < n) (f : ℕ → M) :
    ∑ k ∈ range n, f k =
      ∑ d ∈ n.divisors, ∑ k ∈ range n with n.gcd k = d, f k := by
  exact (Finset.sum_fiberwise_of_maps_to (s := range n) (t := n.divisors)
    (g := fun k ↦ n.gcd k) (fun k hk ↦ by
      rw [Nat.mem_divisors]
      exact ⟨Nat.gcd_dvd_left _ _, hn.ne'⟩) f).symm

private lemma gcd_stratum_sum {M : Type*} [AddCommMonoid M]
    {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) (f : ℕ → M) :
    ∑ k ∈ range n with n.gcd k = d, f k =
      ∑ u ∈ range (n / d) with u.Coprime (n / d), f (d * u) := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  rcases hd with ⟨m, rfl⟩
  rw [Nat.mul_div_cancel_left m hdpos]
  symm
  apply Finset.sum_bij (fun u _ ↦ d * u)
  · intro u hu
    simp only [mem_filter, mem_range] at hu ⊢
    constructor
    · exact (Nat.mul_lt_mul_left hdpos).2 hu.1
    · rw [Nat.gcd_comm, Nat.gcd_mul_left, hu.2.gcd_eq_one, mul_one]
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hdpos hab
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    have hdk : d ∣ k := by
      rw [← hk.2]
      exact Nat.gcd_dvd_right _ _
    obtain ⟨u, rfl⟩ := hdk
    refine ⟨u, ?_, rfl⟩
    simp only [mem_filter, mem_range]
    constructor
    · exact (Nat.mul_lt_mul_left hdpos).1 hk.1
    · rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
      have hg := hk.2
      rw [Nat.gcd_mul_left] at hg
      exact Nat.eq_of_mul_eq_mul_left hdpos (by simpa using hg)
  · intro u hu
    rfl

private lemma gcd_quot_coprime {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    (d / d.gcd m).Coprime (m / d.gcd m) := by
  exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ hd)

private lemma gcd_factor_left {d m : ℕ} : d.gcd m * (d / d.gcd m) = d := by
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_left d m)

private lemma gcd_factor_right {d m : ℕ} : d.gcd m * (m / d.gcd m) = m := by
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_right d m)

private lemma square_mod_factor_raw {d m h a q u : ℕ}
    (hd : d = h*a) (hm : m = h*q) :
    (d * u) ^ 2 % (d * m) = h ^ 2 * a * (a * u ^ 2 % q) := by
  subst d
  subst m
  simp only [pow_two]
  rw [show (h * a * u) * (h * a * u) = (h * a) * (h * (a * u * u)) by ring]
  rw [Nat.mul_mod_mul_left]
  rw [Nat.mul_mod_mul_left]
  ring

private def dval (n r : ℕ) : ℤ :=
  if r % n = 0 then 0 else (n : ℤ) - 2 * (r % n : ℤ)

private lemma dval_mod (n r : ℕ) : dval n (r % n) = dval n r := by
  simp [dval, Nat.mod_mod]

private lemma dval_scale {c q r : ℕ} (hc : 0 < c) :
    dval (c*q) (c*r) = (c : ℤ) * dval q r := by
  unfold dval
  rw [Nat.mul_mod_mul_left]
  by_cases hr : r % q = 0
  · rw [if_pos (by simp [hr, hc.ne']), if_pos hr]
    ring
  · rw [if_neg (by simp [hr, hc.ne']), if_neg hr]
    simp only [Nat.cast_mul]
    rw [Int.mul_emod_mul_of_pos _ _ (by exact_mod_cast hc)]
    ring

private lemma stratum_dval {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) (u : ℕ) :
    let m := n / d
    let h := d.gcd m
    let a := d / h
    let q := m / h
    dval n ((d*u)^2) = (h^2*a : ℕ) * dval q (a*u^2) := by
  dsimp
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  have hmpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hd) hdpos
  have hnfac : n = d * (n/d) := (Nat.mul_div_cancel' hd).symm
  let h := d.gcd (n/d)
  let a := d/h
  let q := (n/d)/h
  change dval n ((d*u)^2) = ((h^2*a : ℕ) : ℤ) * dval q (a*u^2)
  have hh : 0 < h := Nat.gcd_pos_of_pos_left _ hdpos
  have ha : 0 < a := Nat.div_pos (Nat.gcd_le_left _ hdpos) hh
  have hc : 0 < h^2*a := mul_pos (pow_pos hh _) ha
  have hd' : d = h*a := (gcd_factor_left (d := d) (m := n/d)).symm
  have hm' : n/d = h*q := (gcd_factor_right (d := d) (m := n/d)).symm
  have hfac : n = (h^2*a)*q := by
    calc
      n = d * (n/d) := hnfac
      _ = (h*a) * (n/d) := congrArg (fun z ↦ z * (n/d)) hd'
      _ = (h*a) * (h*q) := congrArg (fun z ↦ (h*a) * z) hm'
      _ = (h^2*a)*q := by ring
  have hsquare : (d*u)^2 % n = h^2*a*(a*u^2 % q) := by
    rw [hnfac]
    exact square_mod_factor_raw hd' hm'
  rw [← dval_mod n ((d*u)^2), hsquare, hfac]
  rw [← Nat.mul_mod_mul_left (h^2*a) (a*u^2) q, dval_mod]
  exact dval_scale hc

private def unitValEquiv (m : ℕ) [NeZero m] :
    (ZMod m)ˣ ≃ ↥((range m).filter fun u ↦ u.Coprime m) where
  toFun x := ⟨x.val.val, by
    rw [mem_filter]
    exact ⟨mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime x⟩⟩
  invFun x := ZMod.unitOfCoprime x.1 (by simpa using (mem_filter.mp x.2).2)
  left_inv x := by
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]
  right_inv x := by
    apply Subtype.ext
    change ((ZMod.unitOfCoprime x.1 _ : (ZMod m)ˣ) : ZMod m).val = x.1
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast,
      Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp x.2).1)]

private lemma sum_coprime_eq_units {M : Type*} [AddCommMonoid M]
    (m : ℕ) [NeZero m] (f : ℕ → M) :
    ∑ u ∈ range m with u.Coprime m, f u =
      ∑ x : (ZMod m)ˣ, f x.val.val := by
  classical
  calc
    _ = ∑ y : ↥((range m).filter fun u ↦ u.Coprime m), f y.1 :=
      (Finset.sum_coe_sort ((range m).filter fun u ↦ u.Coprime m) f).symm
    _ = _ := by
      apply Fintype.sum_equiv (unitValEquiv m).symm
      intro y
      congr 1
      exact (congrArg Subtype.val ((unitValEquiv m).apply_symm_apply y)).symm

private noncomputable def kerEquivFiber {G H : Type*} [CommGroup G] [CommGroup H]
    [Fintype G] [Fintype H] (φ : G →* H) (hφ : Function.Surjective φ) (y : H) :
    ↥φ.ker ≃ {x : G // φ x = y} := by
  let x0 : G := Classical.choose (hφ y)
  have hx0 : φ x0 = y := Classical.choose_spec (hφ y)
  refine
    { toFun := fun k ↦ ⟨x0 * k.1, by
        have hk : φ k.1 = 1 := MonoidHom.mem_ker.mp k.2
        simp [hx0, hk]⟩
      invFun := fun x ↦ ⟨x0⁻¹ * x.1, ?_⟩
      left_inv := fun k ↦ by apply Subtype.ext; simp
      right_inv := fun x ↦ by apply Subtype.ext; simp }
  rw [MonoidHom.mem_ker, map_mul, map_inv, x.2, hx0]
  simp

private lemma sum_comp_surjective {G H : Type*} [CommGroup G] [CommGroup H]
    [Fintype G] [Fintype H] (φ : G →* H) (hφ : Function.Surjective φ)
    (f : H → ℤ) :
    ∑ x : G, f (φ x) = (Nat.card ↥φ.ker : ℤ) * ∑ y : H, f y := by
  classical
  rw [Finset.mul_sum]
  rw [← Finset.sum_fiberwise (Finset.univ : Finset G) φ (fun x ↦ f (φ x))]
  apply Finset.sum_congr rfl
  intro y _
  have hcard : #{x : G | φ x = y} = Nat.card ↥φ.ker := by
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    let e : ↥((Finset.univ : Finset G).filter fun x ↦ φ x = y) ≃
        {x : G // φ x = y} :=
      { toFun := fun x ↦ ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
        invFun := fun x ↦ ⟨x.1, by simp [x.2]⟩
        left_inv := fun x ↦ by apply Subtype.ext; rfl
        right_inv := fun x ↦ by apply Subtype.ext; rfl }
    exact Nat.card_congr (e.trans (kerEquivFiber φ hφ y).symm)
  calc
    ∑ x ∈ Finset.univ with φ x = y, f (φ x) =
        ∑ _x ∈ Finset.univ with φ _x = y, f y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = (#{x : G | φ x = y} : ℤ) * f y := by simp
    _ = (Nat.card ↥φ.ker : ℤ) * f y := by rw [hcard]



private lemma dval_eq_of_modEq {q r s : ℕ} (h : r ≡ s [MOD q]) :
    dval q r = dval q s := by
  change r % q = s % q at h
  have hi : (r : ℤ) % (q : ℤ) = (s : ℤ) % (q : ℤ) := by
    rw [← Int.natCast_emod, ← Int.natCast_emod, h]
  unfold dval
  rw [h, hi]

private noncomputable def unitExcess (q a : ℕ) : ℤ :=
  if hq : q = 0 then 0 else
    let _ : NeZero q := ⟨hq⟩
    ∑ v : (ZMod q)ˣ, dval q (a * v.val.val^2)

private lemma unitsMap_dval {m q a : ℕ} [NeZero m] [NeZero q]
    (hd : q ∣ m) (u : (ZMod m)ˣ) :
    dval q (a * u.val.val^2) =
      dval q (a * ((ZMod.unitsMap hd u).val.val)^2) := by
  apply dval_eq_of_modEq
  have hv : ((u.val.val : ℕ) : ZMod q) =
      (((ZMod.unitsMap hd u).val.val : ℕ) : ZMod q) := by
    calc
      ((u.val.val : ℕ) : ZMod q) = ZMod.cast u.val := by
        simpa using congrArg (fun z : ZMod m ↦ (ZMod.cast z : ZMod q))
          (ZMod.natCast_zmod_val u.val)
      _ = (ZMod.unitsMap hd u).val := (ZMod.unitsMap_val hd u).symm
      _ = (((ZMod.unitsMap hd u).val.val : ℕ) : ZMod q) :=
        (ZMod.natCast_zmod_val (ZMod.unitsMap hd u).val).symm
  have hs : ((a * u.val.val^2 : ℕ) : ZMod q) =
      ((a * ((ZMod.unitsMap hd u).val.val)^2 : ℕ) : ZMod q) := by
    push_cast
    rw [hv]
  exact (ZMod.natCast_eq_natCast_iff _ _ q).mp hs

private lemma sum_units_reduce {m q a : ℕ} [NeZero m] [NeZero q]
    (hd : q ∣ m) :
    ∑ u : (ZMod m)ˣ, dval q (a*u.val.val^2) =
      (Nat.card ↥(ZMod.unitsMap hd).ker : ℤ) * unitExcess q a := by
  calc
    _ = ∑ u : (ZMod m)ˣ,
        dval q (a*((ZMod.unitsMap hd u).val.val)^2) := by
      apply Finset.sum_congr rfl
      intro u _
      exact unitsMap_dval hd u
    _ = _ := by
      rw [show unitExcess q a = ∑ v : (ZMod q)ˣ,
          dval q (a*v.val.val^2) by simp [unitExcess, NeZero.ne q]]
      exact sum_comp_surjective (ZMod.unitsMap hd)
        (ZMod.unitsMap_surjective hd) (fun v ↦ dval q (a*v.val.val^2))

private def excess (n : ℕ) : ℤ := ∑ k ∈ range n, dval n (k^2)

private theorem excess_stratification (n : ℕ) (hn : 0 < n) :
    excess n = ∑ d ∈ n.divisors,
      let m := n/d
      let h := d.gcd m
      let a := d/h
      let q := m/h
      (h^2*a : ℕ) *
        ∑ u ∈ range m with u.Coprime m, dval q (a*u^2) := by
  rw [excess, gcd_partition_sum n hn]
  apply Finset.sum_congr rfl
  intro d hdmem
  have hd : d ∣ n := (Nat.mem_divisors.mp hdmem).1
  rw [gcd_stratum_sum hn hd]
  simp only [stratum_dval hn hd]
  rw [← Finset.mul_sum]

private theorem excess_unit_stratification (n : ℕ) (hn : 0 < n) :
    excess n = ∑ d ∈ n.divisors,
      let m := n/d
      let h := d.gcd m
      let a := d/h
      let q := m/h
      ((h^2*a : ℕ) : ℤ) *
        (Nat.card ↥(ZMod.unitsMap (show q ∣ m from
          ⟨h, by rw [mul_comm]; exact (gcd_factor_right (d := d) (m := m)).symm⟩)).ker : ℤ) *
        unitExcess q a := by
  rw [excess_stratification n hn]
  apply Finset.sum_congr rfl
  intro d hdmem
  have hd : d ∣ n := (Nat.mem_divisors.mp hdmem).1
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  let m := n/d
  have hmpos : 0 < m := Nat.div_pos (Nat.le_of_dvd hn hd) hdpos
  let h := d.gcd m
  let a := d/h
  let q := m/h
  have hh : 0 < h := Nat.gcd_pos_of_pos_left _ hdpos
  have hqpos : 0 < q := Nat.div_pos (Nat.gcd_le_right _ hmpos) hh
  let hdq : q ∣ m := ⟨h, by rw [mul_comm]; exact (gcd_factor_right (d := d) (m := m)).symm⟩
  letI : NeZero m := ⟨hmpos.ne'⟩
  letI : NeZero q := ⟨hqpos.ne'⟩
  dsimp only
  rw [sum_coprime_eq_units]
  rw [sum_units_reduce hdq]
  ring



-- Complex weighted first moment of a Dirichlet character.
private noncomputable def charMoment (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ r : ZMod q, (dval q r.val : ℂ) * χ r

private lemma sum_characters_square_inv (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∑ u : (ZMod q)ˣ, χ ((((u : ZMod q) ^ 2)⁻¹))) =
      if χ ^ 2 = 1 then (q.totient : ℂ) else 0 := by
  classical
  have mapinv {x : ZMod q} (hx : IsUnit x) : χ x⁻¹ = (χ x)⁻¹ := by
    obtain ⟨u, rfl⟩ := hx
    rw [ZMod.inv_coe_unit]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]
    simp

  by_cases hχ : χ ^ 2 = 1
  · rw [if_pos hχ]
    have hu (u : (ZMod q)ˣ) : χ ((((u : ZMod q) ^ 2)⁻¹)) = 1 := by
      rw [mapinv (u.isUnit.pow 2), map_pow]
      have he := DFunLike.congr_fun hχ (u : ZMod q)
      have he' : χ (u : ZMod q) ^ 2 = 1 := by
        simpa only [MulChar.pow_apply' _ two_ne_zero,
          MulChar.one_apply u.isUnit] using he
      rw [he', inv_one]
    simp_rw [hu]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ZMod.card_units_eq_totient]
  · rw [if_neg hχ]
    have hex : ∃ v : (ZMod q)ˣ, (χ ^ 2) (v : ZMod q) ≠ 1 := by
      by_contra hn
      push_neg at hn
      apply hχ
      ext x
      simpa using hn x
    let v := Classical.choose hex
    have hv : (χ ^ 2) (v : ZMod q) ≠ 1 := Classical.choose_spec hex
    have hvinv : χ (((v : ZMod q)^2)⁻¹) ≠ 1 := by
      rw [mapinv (v.isUnit.pow 2), map_pow, inv_ne_one]
      simpa only [MulChar.pow_apply' _ two_ne_zero] using hv
    let S := ∑ u : (ZMod q)ˣ, χ ((((u : ZMod q) ^ 2)⁻¹))
    have htrans : χ (((v : ZMod q)^2)⁻¹) * S = S := by
      dsimp only [S]
      calc
        χ (((v : ZMod q)^2)⁻¹) *
              (∑ u : (ZMod q)ˣ, χ (((u : ZMod q)^2)⁻¹)) =
            ∑ u : (ZMod q)ˣ, χ ((((v*u : (ZMod q)ˣ) : ZMod q)^2)⁻¹) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro u _
              rw [mapinv (v.isUnit.pow 2), mapinv (u.isUnit.pow 2),
                mapinv ((v*u).isUnit.pow 2)]
              simp only [map_pow, map_mul, Units.val_mul]
              ring
        _ = ∑ u : (ZMod q)ˣ, χ (((u : ZMod q)^2)⁻¹) :=
          Fintype.sum_bijective _ (Group.mulLeft_bijective v) _ _ (fun _ ↦ rfl)
    exact eq_zero_of_mul_eq_self_left hvinv htrans

private lemma unitExcess_character_expansion (q a : ℕ) [NeZero q]
    (hq : q ≠ 0) (ha : a.Coprime q) :
    ((unitExcess q a : ℤ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ q with χ ^ 2 = 1,
        χ ((a : ZMod q)⁻¹) * charMoment q χ := by
  classical
  have mapinv (χ : DirichletCharacter ℂ q) {x : ZMod q} (hx : IsUnit x) :
      χ x⁻¹ = (χ x)⁻¹ := by
    obtain ⟨u, rfl⟩ := hx
    rw [ZMod.inv_coe_unit]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]
    simp

  rw [unitExcess, dif_neg hq]
  push_cast
  -- Insert character orthogonality for the equality `r = a u²`.
  have htot : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)))
  apply (mul_left_cancel₀ htot)
  calc
    (q.totient : ℂ) * ∑ u : (ZMod q)ˣ,
        (dval q (a * u.val.val ^ 2) : ℂ)
      = ∑ u : (ZMod q)ˣ, ∑ r : ZMod q,
          (dval q r.val : ℂ) *
            (∑ χ : DirichletCharacter ℂ q,
              χ (((a : ZMod q) * (u : ZMod q)^2)⁻¹) * χ r) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          have hau : IsUnit ((a : ZMod q) * (u : ZMod q)^2) := by
            exact (ZMod.isUnit_iff_coprime a q).2 ha |>.mul (u.isUnit.pow 2)
          simp_rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hau]
          simp_rw [eq_comm]
          simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
            ↓reduceIte]
          rw [mul_comm]
          congr 2
          apply dval_eq_of_modEq
          rw [← ZMod.natCast_eq_natCast_iff]
          simp
    _ = ∑ χ : DirichletCharacter ℂ q,
          (∑ u : (ZMod q)ˣ, χ (((a : ZMod q) * (u : ZMod q)^2)⁻¹)) *
            charMoment q χ := by
          simp only [charMoment]
          calc
            (∑ u : (ZMod q)ˣ, ∑ r : ZMod q,
                (dval q r.val : ℂ) *
                  (∑ χ : DirichletCharacter ℂ q,
                    χ (((a : ZMod q) * (u : ZMod q)^2)⁻¹) * χ r)) =
              ∑ u : (ZMod q)ˣ, ∑ r : ZMod q,
                ∑ χ : DirichletCharacter ℂ q,
                  (dval q r.val : ℂ) *
                    (χ (((a : ZMod q) * (u : ZMod q)^2)⁻¹) * χ r) := by
                      apply Finset.sum_congr rfl
                      intro u _
                      apply Finset.sum_congr rfl
                      intro r _
                      rw [Finset.mul_sum]
            _ = ∑ u : (ZMod q)ˣ, ∑ χ : DirichletCharacter ℂ q,
                ∑ r : ZMod q, (dval q r.val : ℂ) *
                  (χ (((a : ZMod q) * (u : ZMod q)^2)⁻¹) * χ r) := by
                    apply Finset.sum_congr rfl
                    intro u _
                    exact Finset.sum_comm
            _ = ∑ χ : DirichletCharacter ℂ q, ∑ u : (ZMod q)ˣ,
                ∑ r : ZMod q, (dval q r.val : ℂ) *
                  (χ (((a : ZMod q) * (u : ZMod q)^2)⁻¹) * χ r) :=
                    Finset.sum_comm
            _ = ∑ χ : DirichletCharacter ℂ q,
                (∑ u : (ZMod q)ˣ, χ (((a : ZMod q) * (u : ZMod q)^2)⁻¹)) *
                  ∑ r : ZMod q, (dval q r.val : ℂ) * χ r := by
                    apply Finset.sum_congr rfl
                    intro χ _
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro u _
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro r _
                    ring
    _ = (q.totient : ℂ) * ∑ χ : DirichletCharacter ℂ q with χ ^ 2 = 1,
          χ ((a : ZMod q)⁻¹) * charMoment q χ := by
          have haunit : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
          have hfactor (χ : DirichletCharacter ℂ q) :
              (∑ u : (ZMod q)ˣ,
                χ (((a : ZMod q) * (u : ZMod q)^2)⁻¹)) =
                χ ((a : ZMod q)⁻¹) *
                  (∑ u : (ZMod q)ˣ, χ (((u : ZMod q)^2)⁻¹)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u _
            rw [mapinv χ (haunit.mul (u.isUnit.pow 2)), mapinv χ haunit,
              mapinv χ (u.isUnit.pow 2), map_mul]
            ring
          let F := fun χ : DirichletCharacter ℂ q ↦
            (∑ u : (ZMod q)ˣ,
              χ (((a : ZMod q) * (u : ZMod q)^2)⁻¹)) * charMoment q χ
          have hsupp : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
              F χ ≠ 0 → χ ^ 2 = 1 := by
            intro χ _ hn
            by_contra hc
            have hz := sum_characters_square_inv q χ
            rw [if_neg hc] at hz
            apply hn
            dsimp only [F]
            rw [hfactor χ, hz, mul_zero, zero_mul]
          calc
            (∑ χ : DirichletCharacter ℂ q,
                (∑ u : (ZMod q)ˣ,
                  χ (((a : ZMod q) * (u : ZMod q)^2)⁻¹)) * charMoment q χ) =
              ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) with χ ^ 2 = 1,
                F χ := by
                  change (∑ χ : DirichletCharacter ℂ q, F χ) = _
                  exact (Finset.sum_filter_of_ne hsupp).symm
            _ = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) with χ ^ 2 = 1,
                (q.totient : ℂ) *
                  (χ ((a : ZMod q)⁻¹) * charMoment q χ) := by
                    apply Finset.sum_congr rfl
                    intro χ hχ
                    have hc : χ ^ 2 = 1 := (Finset.mem_filter.mp hχ).2
                    dsimp only [F]
                    rw [hfactor χ, sum_characters_square_inv, if_pos hc]
                    ring
            _ = (q.totient : ℂ) *
                ∑ χ : DirichletCharacter ℂ q with χ ^ 2 = 1,
                  χ ((a : ZMod q)⁻¹) * charMoment q χ := by
                    rw [Finset.mul_sum]


end Decomp
