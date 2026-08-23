import FormalConjectures.Util.ProblemImports
open Nat Finset BigOperators Int

private def fallInt (X : ℕ) (d : ℕ) : ℤ :=
  ∏ i ∈ Finset.range d, ((X : ℤ) - i)

private lemma fallInt_eq (X d : ℕ) :
    fallInt X d = (d.factorial : ℤ) * (X.choose d : ℤ) := by
  rw [fallInt, ← Ring.choose_natCast (R := ℤ), ← nsmul_eq_mul,
    ← Ring.descPochhammer_eq_factorial_smul_choose, ← Polynomial.eval_eq_smeval]
  exact (descPochhammer_eval_eq_prod_range d (X : ℤ)).symm

private lemma fallInt_succ (X d : ℕ) :
    fallInt X (d + 1) = (X : ℤ) * ∏ i ∈ Finset.range d, ((X : ℤ) - (i + 1 : ℕ)) := by
  simp only [fallInt, Finset.prod_range_succ', Nat.cast_zero, sub_zero]
  ring


private lemma fallInt_tail_modEq (X Y d : ℕ) :
    (∏ i ∈ Finset.range d, ((X : ℤ) - (i + 1 : ℕ))) ≡
      (∏ i ∈ Finset.range d, ((Y : ℤ) - (i + 1 : ℕ))) [ZMOD ((Y : ℤ) - X)] := by
  apply Int.ModEq.prod
  intro i hi
  apply Int.ModEq.sub
  · exact Int.modEq_iff_dvd.mpr ⟨1, by ring⟩
  · rfl

private lemma factorial_choose_det_factor (X Y d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    ∃ z : ℤ,
      (d.factorial : ℤ) * e.factorial *
          ((X.choose d : ℤ) * Y.choose e - X.choose e * Y.choose d) =
        (X : ℤ) * Y * ((Y : ℤ) - X) * z := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  let UX : ℤ := ∏ i ∈ Finset.range d, ((X : ℤ) - (i + 1 : ℕ))
  let UY : ℤ := ∏ i ∈ Finset.range d, ((Y : ℤ) - (i + 1 : ℕ))
  let VX : ℤ := ∏ i ∈ Finset.range e, ((X : ℤ) - (i + 1 : ℕ))
  let VY : ℤ := ∏ i ∈ Finset.range e, ((Y : ℤ) - (i + 1 : ℕ))
  have hU : UX ≡ UY [ZMOD ((Y : ℤ) - X)] := fallInt_tail_modEq X Y d
  have hV : VX ≡ VY [ZMOD ((Y : ℤ) - X)] := fallInt_tail_modEq X Y e
  have hdiv : ((Y : ℤ) - X) ∣ UX * VY - VX * UY := by
    have h := hV.mul hU.symm
    rw [Int.modEq_iff_dvd] at h
    simpa [mul_comm] using h
  obtain ⟨z, hz⟩ := hdiv
  use z
  rw [show ((d + 1).factorial : ℤ) * (e + 1).factorial *
      ((X.choose (d + 1) : ℤ) * Y.choose (e + 1) -
       X.choose (e + 1) * Y.choose (d + 1)) =
      (((d + 1).factorial : ℤ) * X.choose (d + 1)) *
        (((e + 1).factorial : ℤ) * Y.choose (e + 1)) -
      (((e + 1).factorial : ℤ) * X.choose (e + 1)) *
        (((d + 1).factorial : ℤ) * Y.choose (d + 1)) by ring]
  rw [← fallInt_eq, ← fallInt_eq, ← fallInt_eq, ← fallInt_eq,
    fallInt_succ, fallInt_succ, fallInt_succ, fallInt_succ]
  dsimp [UX, UY, VX, VY] at hz ⊢
  linear_combination (X : ℤ) * Y * hz

private lemma factorial_vals_add_three_le {p d e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hd : 0 < d) (he : 0 < e) (hne : d ≠ e) :
    padicValNat p d.factorial + padicValNat p e.factorial + 3 ≤ d + e := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpd := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (Nat.ne_of_gt hd)
  have hpe := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (Nat.ne_of_gt he)
  have hp4 : 4 ≤ p - 1 := by omega
  have hd4 : 4 * padicValNat p d.factorial < d :=
    (Nat.mul_le_mul_right (padicValNat p d.factorial) hp4).trans_lt hpd
  have he4 : 4 * padicValNat p e.factorial < e :=
    (Nat.mul_le_mul_right (padicValNat p e.factorial) hp4).trans_lt hpe
  rcases lt_or_gt_of_ne hne with hde | hed <;> omega

lemma factorial_choose_det_level_dvd {p lev X Y d e : ℕ}
    (hX : p ^ lev ∣ X) (hY : p ^ lev ∣ Y) (hd : 0 < d) (he : 0 < e) :
    ((p : ℤ) ^ (3 * lev)) ∣
      (d.factorial : ℤ) * e.factorial *
        ((X.choose d : ℤ) * Y.choose e - X.choose e * Y.choose d) := by
  obtain ⟨z, hz⟩ := factorial_choose_det_factor X Y d e hd he
  obtain ⟨x, hx⟩ := hX
  obtain ⟨y, hy⟩ := hY
  have hxyz : ((p : ℤ) ^ (3 * lev)) ∣ (X : ℤ) * Y * ((Y : ℤ) - X) := by
    use (x : ℤ) * y * ((y : ℤ) - x)
    push_cast at hx hy ⊢
    rw [hx, hy]
    push_cast
    ring
  rw [hz]
  exact dvd_mul_of_dvd_left hxyz z


lemma factorial_choose_det_of_product_dvd {p L X Y d e : ℕ}
    (hprod : ((p : ℤ)^L) ∣ (X : ℤ) * Y * ((Y : ℤ)-X))
    (hd : 0 < d) (he : 0 < e) :
    ((p : ℤ)^L) ∣ (d.factorial : ℤ) * e.factorial *
      ((X.choose d : ℤ) * Y.choose e - X.choose e * Y.choose d) := by
  obtain ⟨z,hz⟩ := factorial_choose_det_factor X Y d e hd he
  rw [hz]
  exact dvd_mul_of_dvd_left hprod z


lemma paired_choose_term_dvd {p lev X Y d e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hX : p ^ lev ∣ X) (hY : p ^ lev ∣ Y) (hd : 0 < d) (he : 0 < e) (hne : d ≠ e) :
    ((p : ℤ) ^ (3 * (lev + 1))) ∣
      (p : ℤ) ^ (d + e) *
        ((X.choose d : ℤ) * Y.choose e - X.choose e * Y.choose d) := by
  letI : Fact p.Prime := ⟨hp⟩
  let det : ℤ := (X.choose d : ℤ) * Y.choose e - X.choose e * Y.choose d
  by_cases hdet : det = 0
  · simp [det, hdet]
  have hfac := factorial_choose_det_factor X Y d e hd he
  obtain ⟨z, hz⟩ := hfac
  obtain ⟨x, hx⟩ := hX
  obtain ⟨y, hy⟩ := hY
  have hxyz : ((p : ℤ) ^ (3 * lev)) ∣ (X : ℤ) * Y * ((Y : ℤ) - X) := by
    use (x : ℤ) * y * ((y : ℤ) - x)
    push_cast at hx hy ⊢
    rw [hx, hy]
    push_cast
    ring
  have hprod : ((p : ℤ) ^ (3 * lev)) ∣
      (d.factorial : ℤ) * e.factorial * det := by
    rw [hz]
    exact dvd_mul_of_dvd_left hxyz z
  have hvalprod : 3 * lev ≤ padicValInt p ((d.factorial : ℤ) * e.factorial * det) :=
    (padicValInt_dvd_iff (3 * lev) _).mp hprod |>.resolve_left (by
      exact mul_ne_zero (mul_ne_zero (by positivity) (by positivity)) hdet)
  have hvalsplit : padicValInt p ((d.factorial : ℤ) * e.factorial * det) =
      padicValNat p d.factorial + padicValNat p e.factorial + padicValInt p det := by
    rw [padicValInt.mul (mul_ne_zero (by positivity) (by positivity)) hdet,
      padicValInt.mul (by positivity) (by positivity), padicValInt.of_nat, padicValInt.of_nat]
  have hvfac := factorial_vals_add_three_le hp hp5 hd he hne
  have hgoalval : 3 * (lev + 1) ≤
      padicValInt p ((p : ℤ) ^ (d + e) * det) := by
    rw [padicValInt.mul (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)) hdet]
    change padicValNat p (p ^ (d + e)) + padicValInt p det ≥ 3 * (lev + 1)
    rw [padicValNat.prime_pow]
    rw [hvalsplit] at hvalprod
    omega
  exact (padicValInt_dvd_iff _ _).mpr (Or.inr hgoalval)
