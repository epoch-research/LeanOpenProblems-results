import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

namespace Wolst

/-- Extract a factor of `p` from a `ZMod N` element whose `val` is divisible by `p`. -/
lemma exists_p_mul {N : ℕ} [NeZero N] {p : ℕ} (x : ZMod N) (hx : p ∣ x.val) :
    ∃ w : ZMod N, x = p * w := by
  obtain ⟨m, hm⟩ := hx
  refine ⟨(m : ZMod N), ?_⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x, hm]
  push_cast
  ring

variable {p : ℕ} [Fact p.Prime]

/-- For `0 < i < p`, the cast of `i` is a unit in `ZMod (p^k)`. -/
lemma isUnit_cast {k : ℕ} (i : ℕ) (hi : 0 < i) (hip : i < p) :
    IsUnit ((i : ZMod (p ^ k))) := by
  rw [ZMod.isUnit_iff_coprime]
  have hpp : p.Prime := Fact.out
  have h1 : Nat.Coprime p i := (hpp.coprime_iff_not_dvd).mpr (fun h => by
    have := Nat.le_of_dvd hi h; omega)
  exact (h1.symm).pow_right k

/-- Bridge: a sum over `range p` of a function of casts equals the sum over all of `ZMod p`. -/
theorem sum_range_eq_univ {M : Type*} [AddCommMonoid M] (f : ZMod p → M) :
    ∑ i ∈ Finset.range p, f (i : ZMod p) = ∑ x : ZMod p, f x := by
  have : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  apply Finset.sum_nbij' (fun i => ((i : ℕ) : ZMod p)) ZMod.val
  · intro a _; exact Finset.mem_univ _
  · intro a _; rw [Finset.mem_range]; exact ZMod.val_lt a
  · intro a ha; rw [Finset.mem_range] at ha; exact ZMod.val_natCast_of_lt ha
  · intro a _; exact ZMod.natCast_zmod_val a
  · intro a _; rfl

/-- Sum of positive powers over `1..p-1` vanishes mod `p` (Fermat). -/
theorem sum_pow_Ico_eq_zero (m : ℕ) (hm1 : 1 ≤ m) (hm : m < p - 1) :
    ∑ i ∈ Finset.Ico 1 p, ((i : ZMod p))^m = 0 := by
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have key : ∑ x : ZMod p, x ^ m = 0 := by
    rw [FiniteField.sum_pow_lt_card_sub_one]; rw [hcard]; omega
  have h0 : ∑ i ∈ Finset.range p, ((i : ZMod p))^m = ∑ x : ZMod p, x ^ m :=
    sum_range_eq_univ (fun x => x ^ m)
  have hsplit : ∑ i ∈ Finset.range p, ((i : ZMod p))^m
      = ((0 : ZMod p))^m + ∑ i ∈ Finset.Ico 1 p, ((i : ZMod p))^m := by
    have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
    rw [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : (1:ℕ) ≤ p)]
    simp
  rw [h0] at hsplit
  rw [key] at hsplit
  have : ((0 : ZMod p))^m = 0 := by
    rw [zero_pow]; omega
  rw [this, zero_add] at hsplit
  exact hsplit.symm

noncomputable def proj : ZMod (p^5) →+* ZMod p :=
  ZMod.castHom (by exact dvd_pow_self p (by norm_num)) (ZMod p)
lemma proj_natCast (n : ℕ) : proj (p := p) (n : ZMod (p^5)) = (n : ZMod p) := by
  simp [proj]
lemma cast_ne_zero (i : ℕ) (hi : 0 < i) (hip : i < p) : ((i : ZMod p)) ≠ 0 := by
  have := isUnit_cast (k := 1) i hi hip
  rw [pow_one] at this; exact this.ne_zero
lemma cast_inv (i : ℕ) (hi : 0 < i) (hip : i < p) :
    proj (p := p) ((i : ZMod (p^5))⁻¹) = ((i : ZMod p))⁻¹ := by
  have hu : IsUnit ((i : ZMod (p^5))) := isUnit_cast i hi hip
  have h1 : (i : ZMod (p^5))⁻¹ * (i : ZMod (p^5)) = 1 := ZMod.inv_mul_of_unit _ hu
  have h2 := congrArg (proj (p := p)) h1
  rw [map_mul, map_one, proj_natCast] at h2
  have hne := cast_ne_zero i hi hip
  apply mul_left_cancel₀ hne
  rw [mul_inv_cancel₀ hne, mul_comm]; exact h2

theorem sum_inv_pow_Ico_eq_zero (m : ℕ) (hm1 : 1 ≤ m) (hm : m < p - 1) :
    ∑ i ∈ Finset.Ico 1 p, ((i : ZMod p)⁻¹)^m = 0 := by
  have hbij : Function.Bijective (fun x : ZMod p => x⁻¹) :=
    ⟨fun a b h => by simpa using congrArg (·⁻¹) h, fun y => ⟨y⁻¹, by simp⟩⟩
  have huniv : ∑ x : ZMod p, (x⁻¹)^m = ∑ x : ZMod p, x^m :=
    Fintype.sum_bijective _ hbij (fun x => (x⁻¹)^m) (fun x => x^m) (fun x => rfl)
  have hz : ∑ x : ZMod p, x^m = 0 := by
    rw [FiniteField.sum_pow_lt_card_sub_one]; rw [ZMod.card]; omega
  have h0 : ∑ i ∈ Finset.range p, ((i : ZMod p)⁻¹)^m = ∑ x : ZMod p, (x⁻¹)^m :=
    sum_range_eq_univ (fun x => (x⁻¹)^m)
  rw [huniv, hz] at h0
  have hmem : (0:ℕ) ∈ Finset.range p := Finset.mem_range.mpr (Fact.out (p:=p.Prime)).pos
  have herase : (Finset.range p).erase 0 = Finset.Ico 1 p := by
    rw [Finset.range_eq_Ico, Finset.Ico_erase_left]
    exact Finset.val_inj.mp rfl
  have hae := Finset.add_sum_erase (Finset.range p) (fun i => ((i : ZMod p)⁻¹)^m) hmem
  simp only [herase, Nat.cast_zero, inv_zero, zero_pow (show m ≠ 0 by omega), zero_add] at hae
  rw [h0] at hae
  exact hae

/-- If the projection to `ZMod p` vanishes, the element is `p` times something. -/
lemma dvd_p_of_proj_zero (x : ZMod (p^5)) (h : proj (p := p) x = 0) :
    ∃ z : ZMod (p^5), x = (p : ZMod (p^5)) * z := by
  apply exists_p_mul
  have : ((x.val : ZMod p)) = 0 := by
    rw [← proj_natCast, ZMod.natCast_zmod_val]; exact h
  exact (ZMod.natCast_eq_zero_iff _ _).mp this

/-- Inverse power sum in `ZMod (p^5)`. -/
noncomputable def S (m : ℕ) : ZMod (p^5) :=
  ∑ i ∈ Finset.Ico 1 p, ((i : ZMod (p^5))⁻¹)^m

lemma proj_S (m : ℕ) : proj (p := p) (S m) = ∑ i ∈ Finset.Ico 1 p, ((i : ZMod p)⁻¹)^m := by
  unfold S
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Ico] at hi
  rw [map_pow, cast_inv i (by omega) (by omega)]

/-- The inverse power sum `S m` is divisible by `p` when `1 ≤ m < p-1`. -/
lemma S_dvd_p (m : ℕ) (hm1 : 1 ≤ m) (hm : m < p - 1) :
    ∃ z : ZMod (p^5), S m = (p : ZMod (p^5)) * z := by
  apply dvd_p_of_proj_zero
  rw [proj_S]
  exact sum_inv_pow_Ico_eq_zero m hm1 hm

set_option linter.unusedSectionVars false

/-- Reflection `i ↦ p - i` on `Ico 1 p`. -/
theorem sum_reflect {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ i ∈ Finset.Ico 1 p, f (p - i) = ∑ i ∈ Finset.Ico 1 p, f i := by
  apply Finset.sum_nbij' (fun i => p - i) (fun i => p - i)
  · intro a ha; rw [Finset.mem_Ico] at *; omega
  · intro a ha; rw [Finset.mem_Ico] at *; omega
  · intro a ha; rw [Finset.mem_Ico] at ha; omega
  · intro a ha; rw [Finset.mem_Ico] at ha; omega
  · intro a ha; rfl

/-- The per-term pairing identity. -/
lemma pair_identity (I J a b : ZMod (p^5))
    (hI : a * I = 1) (hJ : b * J = 1) (hsum : I + J = (p:ZMod (p^5)))
    (hIu : IsUnit I) (hJu : IsUnit J) :
    2*a + (p:ZMod (p^5))*a^2 + 2*b + (p:ZMod (p^5))*b^2
      = (p:ZMod (p^5))^3 * (a^2 * b^2) := by
  have huI2J2 : IsUnit (I^2*J^2) := (hIu.pow 2).mul (hJu.pow 2)
  apply IsUnit.mul_right_cancel huI2J2
  set pc := (p:ZMod (p^5)) with hpc
  linear_combination
    (-I*J^2*a*b^2*pc^3 + I*J^2*a*pc + 2*I*J^2 - J^2*b^2*pc^3 + J^2*pc) * hI
    + (I^2*J*b*pc + 2*I^2*J + I^2*pc - J*b*pc^3 - pc^3) * hJ
    + (2*I*J + I*pc + J*pc + pc^2) * hsum

/-- `W2 = ∑ (i⁻¹ (p-i)⁻¹)²`. -/
noncomputable def W2 : ZMod (p^5) :=
  ∑ i ∈ Finset.Ico 1 p, ((i : ZMod (p^5))⁻¹ * ((p - i : ℕ) : ZMod (p^5))⁻¹)^2

lemma proj_W2_zero (hp7 : 7 ≤ p) : proj (p := p) (W2 (p := p)) = 0 := by
  unfold W2
  rw [map_sum]
  rw [← sum_inv_pow_Ico_eq_zero (p := p) 4 (by omega) (by omega)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Ico] at hi
  rw [map_pow, map_mul, cast_inv i (by omega) (by omega), cast_inv (p-i) (by omega) (by omega)]
  have hcast : ((p - i : ℕ) : ZMod p) = -(i : ZMod p) := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
  rw [hcast]
  rw [inv_neg]
  ring

/-- Fact (II): `2*(2 S₁ + p S₂) = p⁴ * z`. -/
theorem factII (hp7 : 7 ≤ p) : ∃ z : ZMod (p^5),
    2*(2 * S 1 + (p:ZMod (p^5)) * S 2) = (p:ZMod (p^5))^4 * z := by
  set R := ZMod (p^5)
  set term : ℕ → R := fun i => 2*((i:R)⁻¹) + (p:R)*((i:R)⁻¹)^2 with hterm
  have hsum_term : 2 * S 1 + (p:R) * S 2 = ∑ i ∈ Finset.Ico 1 p, term i := by
    unfold S
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; simp [hterm, pow_one]
  -- step 1: 2*(∑ term) = p^3 * W2
  have hrefl : ∑ i ∈ Finset.Ico 1 p, term (p - i) = ∑ i ∈ Finset.Ico 1 p, term i :=
    sum_reflect term
  have step1 : 2 * (∑ i ∈ Finset.Ico 1 p, term i) = (p:R)^3 * W2 (p := p) := by
    have e : 2 * (∑ i ∈ Finset.Ico 1 p, term i)
        = (∑ i ∈ Finset.Ico 1 p, term i) + (∑ i ∈ Finset.Ico 1 p, term (p - i)) := by
      rw [hrefl, two_mul]
    rw [e, ← Finset.sum_add_distrib]
    rw [show (p:R)^3 * W2 (p := p)
        = ∑ i ∈ Finset.Ico 1 p, (p:R)^3 * ((i:R)⁻¹ * ((p-i:ℕ):R)⁻¹)^2 from by
      rw [W2, Finset.mul_sum]]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hIu : IsUnit ((i:R)) := isUnit_cast i (by omega) (by omega)
    have hJu : IsUnit (((p-i:ℕ):R)) := isUnit_cast (p-i) (by omega) (by omega)
    have hI : (i:R)⁻¹ * (i:R) = 1 := ZMod.inv_mul_of_unit _ hIu
    have hJ : ((p-i:ℕ):R)⁻¹ * ((p-i:ℕ):R) = 1 := ZMod.inv_mul_of_unit _ hJu
    have hsum2 : (i:R) + ((p-i:ℕ):R) = (p:R) := by
      rw [← Nat.cast_add]; congr 1; omega
    have := pair_identity (p := p) (i:R) ((p-i:ℕ):R) ((i:R)⁻¹) (((p-i:ℕ):R)⁻¹)
      hI hJ hsum2 hIu hJu
    simp only [hterm]
    linear_combination this
  obtain ⟨w, hw⟩ := exists_p_mul (W2 (p := p)) (by
    have := proj_W2_zero (p := p) hp7
    have hval : ((W2 (p := p)).val : ZMod p) = 0 := by
      rw [← proj_natCast, ZMod.natCast_zmod_val]; exact this
    exact (ZMod.natCast_eq_zero_iff _ _).mp hval)
  refine ⟨w, ?_⟩
  rw [hsum_term, step1, hw]
  ring

/-- General pairing: if `term i + term (p-i) = pᵏ red i`, then `2 ∑ term = pᵏ ∑ red`. -/
lemma pairing_sum (k : ℕ) (term red : ℕ → ZMod (p^5))
    (hpt : ∀ i ∈ Finset.Ico 1 p, term i + term (p - i) = (p:ZMod (p^5))^k * red i) :
    2 * ∑ i ∈ Finset.Ico 1 p, term i
      = (p:ZMod (p^5))^k * ∑ i ∈ Finset.Ico 1 p, red i := by
  have hrefl := sum_reflect (p:=p) term
  rw [two_mul]
  nth_rewrite 2 [← hrefl]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi; exact hpt i hi

/-- `proj` of a sum of casts-with-inverses, reduced. Helper for divisibility. -/
lemma sum_dvd_p_of_proj_zero (g : ℕ → ZMod (p^5))
    (h : proj (p := p) (∑ i ∈ Finset.Ico 1 p, g i) = 0) :
    ∃ w : ZMod (p^5), (∑ i ∈ Finset.Ico 1 p, g i) = (p:ZMod (p^5)) * w :=
  dvd_p_of_proj_zero _ h

theorem S1_dvd_p2 (hp7 : 7 ≤ p) : ∃ z : ZMod (p^5), S 1 = (p:ZMod (p^5))^2 * z := by
  set R := ZMod (p^5)
  have key : 2 * ∑ i ∈ Finset.Ico 1 p, ((i:R)⁻¹)
      = (p:R)^1 * ∑ i ∈ Finset.Ico 1 p, ((i:R)⁻¹ * ((p-i:ℕ):R)⁻¹) := by
    apply pairing_sum 1
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hIu : IsUnit ((i:R)) := isUnit_cast i (by omega) (by omega)
    have hJu : IsUnit (((p-i:ℕ):R)) := isUnit_cast (p-i) (by omega) (by omega)
    have hI : (i:R)⁻¹ * (i:R) = 1 := ZMod.inv_mul_of_unit _ hIu
    have hJ : ((p-i:ℕ):R)⁻¹ * ((p-i:ℕ):R) = 1 := ZMod.inv_mul_of_unit _ hJu
    have hsum2 : (i:R) + ((p-i:ℕ):R) = (p:R) := by rw [← Nat.cast_add]; congr 1; omega
    apply IsUnit.mul_right_cancel (hIu.mul hJu)
    set pc := (p:R)
    set I := (i:R); set J := ((p-i:ℕ):R); set a := (i:R)⁻¹; set b := ((p-i:ℕ):R)⁻¹
    linear_combination (-J*b*pc+J)*hI + (I-pc)*hJ + hsum2
  obtain ⟨w, hw⟩ : ∃ w, (∑ i ∈ Finset.Ico 1 p, ((i:R)⁻¹*((p-i:ℕ):R)⁻¹)) = (p:R)*w := by
    apply dvd_p_of_proj_zero
    rw [map_sum]
    have hpt : (∑ i ∈ Finset.Ico 1 p, proj (p:=p) ((i:R)⁻¹*((p-i:ℕ):R)⁻¹))
        = -∑ i ∈ Finset.Ico 1 p, ((i:ZMod p)⁻¹)^2 := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Ico] at hi
      rw [map_mul, cast_inv i (by omega) (by omega), cast_inv (p-i) (by omega) (by omega)]
      have hh : ((p-i:ℕ):ZMod p) = -(i:ZMod p) := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
      rw [hh, inv_neg]; ring
    rw [hpt, sum_inv_pow_Ico_eq_zero (p:=p) 2 (by omega) (by omega), neg_zero]
  have h2u0 : IsUnit (((2:ℕ)):R) := isUnit_cast (k:=5) 2 (by norm_num) (by omega)
  have h2u : IsUnit (2:R) := by rwa [Nat.cast_ofNat] at h2u0
  have h2 : (2:R)⁻¹ * 2 = 1 := ZMod.inv_mul_of_unit _ h2u
  have hS1 : S 1 = ∑ i ∈ Finset.Ico 1 p, ((i:R)⁻¹) := by
    unfold S; apply Finset.sum_congr rfl; intro i _; rw [pow_one]
  refine ⟨(2:R)⁻¹ * w, ?_⟩
  have hkey2 : 2 * S 1 = (p:R)^2 * w := by rw [hS1, key, hw]; ring
  calc S 1 = (2:R)⁻¹ * 2 * S 1 := by rw [h2, one_mul]
    _ = (2:R)⁻¹ * (2 * S 1) := by ring
    _ = (2:R)⁻¹ * ((p:R)^2 * w) := by rw [hkey2]
    _ = (p:R)^2 * ((2:R)⁻¹ * w) := by ring

theorem S3_dvd_p2 (hp7 : 7 ≤ p) : ∃ z : ZMod (p^5), S 3 = (p:ZMod (p^5))^2 * z := by
  set R := ZMod (p^5)
  have key : 2 * ∑ i ∈ Finset.Ico 1 p, ((i:R)⁻¹)^3
      = (p:R)^1 * ∑ i ∈ Finset.Ico 1 p,
          (((p:R)^2 - 3*(i:R)*((p-i:ℕ):R)) * ((i:R)⁻¹*((p-i:ℕ):R)⁻¹)^3) := by
    apply pairing_sum 1
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hIu : IsUnit ((i:R)) := isUnit_cast i (by omega) (by omega)
    have hJu : IsUnit (((p-i:ℕ):R)) := isUnit_cast (p-i) (by omega) (by omega)
    have hI : (i:R)⁻¹ * (i:R) = 1 := ZMod.inv_mul_of_unit _ hIu
    have hJ : ((p-i:ℕ):R)⁻¹ * ((p-i:ℕ):R) = 1 := ZMod.inv_mul_of_unit _ hJu
    have hsum2 : (i:R) + ((p-i:ℕ):R) = (p:R) := by rw [← Nat.cast_add]; congr 1; omega
    apply IsUnit.mul_right_cancel ((hIu.mul hJu).pow 3)
    set pc := (p:R)
    set I := (i:R); set J := ((p-i:ℕ):R); set a := (i:R)⁻¹; set b := ((p-i:ℕ):R)⁻¹
    linear_combination
      (3*I^3*J^4*a^2*b^3*pc + 3*I^2*J^4*a*b^3*pc - I^2*J^3*a^2*b^3*pc^3 + I^2*J^3*a^2
        + 3*I*J^4*b^3*pc - I*J^3*a*b^3*pc^3 + I*J^3*a - J^3*b^3*pc^3 + J^3) * hI
      + (I^3*J^2*b^2 + I^3*J*b + I^3 + 3*I*J^3*b^2*pc + 3*I*J^2*b*pc + 3*I*J*pc
        - J^2*b^2*pc^3 - J*b*pc^3 - pc^3) * hJ
      + (I^2 - I*J + I*pc + J^2 + J*pc + pc^2) * hsum2
  obtain ⟨w, hw⟩ : ∃ w, (∑ i ∈ Finset.Ico 1 p,
      (((p:R)^2 - 3*(i:R)*((p-i:ℕ):R)) * ((i:R)⁻¹*((p-i:ℕ):R)⁻¹)^3)) = (p:R)*w := by
    apply dvd_p_of_proj_zero
    rw [map_sum]
    have hpt : (∑ i ∈ Finset.Ico 1 p, proj (p:=p)
          (((p:R)^2 - 3*(i:R)*((p-i:ℕ):R)) * ((i:R)⁻¹*((p-i:ℕ):R)⁻¹)^3))
        = ∑ i ∈ Finset.Ico 1 p, (-3 * ((i:ZMod p)⁻¹)^4) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Ico] at hi
      have e1 := cast_inv (p:=p) i (by omega) (by omega)
      have e2 := cast_inv (p:=p) (p-i) (by omega) (by omega)
      have hh : ((p-i:ℕ):ZMod p) = -(i:ZMod p) := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
      have hp0 : ((p:ℕ):ZMod p) = 0 := ZMod.natCast_self p
      have hi0 : (i:ZMod p) ≠ 0 := cast_ne_zero i (by omega) (by omega)
      simp only [map_mul, map_sub, map_pow, map_ofNat, map_natCast, e1, e2, hh, hp0]
      field_simp
      ring
    rw [hpt, ← Finset.mul_sum, sum_inv_pow_Ico_eq_zero (p:=p) 4 (by omega) (by omega), mul_zero]
  have h2u0 : IsUnit (((2:ℕ)):R) := isUnit_cast (k:=5) 2 (by norm_num) (by omega)
  have h2u : IsUnit (2:R) := by rwa [Nat.cast_ofNat] at h2u0
  have h2 : (2:R)⁻¹ * 2 = 1 := ZMod.inv_mul_of_unit _ h2u
  have hS3 : S 3 = ∑ i ∈ Finset.Ico 1 p, ((i:R)⁻¹)^3 := rfl
  refine ⟨(2:R)⁻¹ * w, ?_⟩
  have hkey2 : 2 * S 3 = (p:R)^2 * w := by rw [hS3, key, hw]; ring
  calc S 3 = (2:R)⁻¹ * 2 * S 3 := by rw [h2, one_mul]
    _ = (2:R)⁻¹ * (2 * S 3) := by ring
    _ = (2:R)⁻¹ * ((p:R)^2 * w) := by rw [hkey2]
    _ = (p:R)^2 * ((2:R)⁻¹ * w) := by ring

/-- Value of the binomial `((a+1)p-1).choose (p-1)` cast into `ZMod (p^5)` as a product. -/
theorem cval (a : ℕ) :
    ((((a+1)*p - 1).choose (p-1) : ℕ) : ZMod (p^5))
      = ∏ i ∈ Finset.Ico 1 p, (1 + (a:ZMod (p^5))*(p:ZMod (p^5)) * ((i:ZMod (p^5)))⁻¹) := by
  set R := ZMod (p^5)
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hnat : (p-1)! * (((a+1)*p - 1).choose (p-1)) = ∏ j ∈ Finset.Ico 1 p, (a*p + j) := by
    have h1 : (a*p+1).ascFactorial (p-1) = (p-1)! * (((a+1)*p-1)).choose (p-1) := by
      rw [Nat.ascFactorial_eq_factorial_mul_choose']; congr 2; rw [add_mul, one_mul]; omega
    rw [← h1, Nat.ascFactorial_eq_prod_range, Finset.prod_Ico_eq_prod_range]
    apply Finset.prod_congr rfl; intro i _; omega
  have cast_nat : ((p-1)! : R) * ((((a+1)*p - 1).choose (p-1)):R)
      = ∏ j ∈ Finset.Ico 1 p, ((a*p+j : ℕ):R) := by
    rw [← Nat.cast_mul, hnat, Nat.cast_prod]
  have hfact : ((p-1)! : R) = ∏ j ∈ Finset.Ico 1 p, (j:R) := by
    have h := prod_Ico_id_eq_factorial (p-1)
    rw [show (p-1)+1 = p from by omega] at h
    rw [← Nat.cast_prod, h]
  have hperfac : ∀ j ∈ Finset.Ico 1 p, ((a*p+j:ℕ):R)
      = (j:R)*(1+(a:R)*(p:R)*(j:R)⁻¹) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hju : IsUnit ((j:R)) := isUnit_cast j (by omega) (by omega)
    have hj1 : (j:R) * (j:R)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hju
    push_cast
    linear_combination -(a:R)*(p:R)*hj1
  have hprod : ∏ j ∈ Finset.Ico 1 p, ((a*p+j:ℕ):R)
      = (∏ j ∈ Finset.Ico 1 p, (j:R)) * ∏ j ∈ Finset.Ico 1 p, (1+(a:R)*(p:R)*(j:R)⁻¹) := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl hperfac
  have hunit : IsUnit (∏ j ∈ Finset.Ico 1 p, (j:R)) := by
    apply Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
    intro j hj; rw [Finset.mem_Ico] at hj; exact isUnit_cast j (by omega) (by omega)
  rw [hfact, hprod] at cast_nat
  exact (hunit.mul_right_inj).mp cast_nat

/-- Hockey-stick identity. -/
lemma hockey (n m : ℕ) : ∑ k ∈ Finset.range (m+1), (n+k).choose k = (n+m+1).choose m := by
  induction m with
  | zero => simp
  | succ d ih => rw [Finset.sum_range_succ, ih]; exact (Nat.choose_succ_succ (n+d+1) d).symm

/-- `S1 = 3 · (3p-1 choose p-1)`. -/
theorem S1_telescope (hp1 : 1 ≤ p) :
    (∑ k ∈ Finset.range (2*p+1), (p+k-1).choose k) = 3 * ((3*p-1).choose (p-1)) := by
  have hrw : ∑ k ∈ Finset.range (2*p+1), (p+k-1).choose k
      = ∑ k ∈ Finset.range (2*p+1), ((p-1)+k).choose k := by
    apply Finset.sum_congr rfl; intro k _; congr 1; omega
  rw [hrw, hockey (p-1) (2*p), show (p-1)+2*p+1 = 3*p from by omega]
  have hsym : (3*p).choose (2*p) = (3*p).choose p := by
    have h := Nat.choose_symm (show p ≤ 3*p from by omega)
    rw [show 3*p - p = 2*p from by omega] at h; exact h
  rw [hsym]
  have h := Nat.succ_mul_choose_eq (3*p-1) (p-1)
  rw [show (3*p-1).succ = 3*p from by omega, show (p-1).succ = p from by omega] at h
  have h2 : (3*p).choose p * p = (3 * ((3*p-1).choose (p-1))) * p := by rw [← h]; ring
  exact Nat.eq_of_mul_eq_mul_right hp1 h2

end Wolst
