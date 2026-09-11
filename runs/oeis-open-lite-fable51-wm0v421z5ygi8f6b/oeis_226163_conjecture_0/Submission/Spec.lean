import FormalConjectures.Util.ProblemImports

open Matrix Nat Int

/--
A226163: Determinant of the $(p_n-1)/2$-by-$(p_n-1)/2$ matrix with $(i,j)$-entry being the Legendre symbol
$$\left(\frac{i^2 - \left(\frac{p_n-1}{2}\right)! \cdot j}{p_n}\right)$$
where $p_n$ is the $n$-th prime.
The sequence is naturally indexed starting from $n=2$.
-/
noncomputable def A226163 (n : ℕ) : ℤ :=
  if h : n < 2 then 0 else

  -- p is the n-th prime, p_n. Mathlib's nth Nat.Prime is 0-indexed, so we use (n-1).
  -- Since n >= 2, p >= 3 is an an odd prime.
  let p : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Matrix dimension m = (p-1)/2.
  let m : ℕ := (p - 1) / 2

  -- The constant C = ((p-1)/2)! as an integer.
  let C : ℤ := m.factorial.cast

  -- The matrix M has entries in ℤ.
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    -- 1-based indices i' and j' for the formula: 1 <= i', j' <= m.
    let i' : ℤ := (i.val + 1).cast
    let j' : ℤ := (j.val + 1).cast

    -- Argument for the Legendre symbol: i'^2 - C * j'
    let arg : ℤ := i' * i' - C * j'

    -- jacobiSym is the Legendre symbol since p is prime.
    jacobiSym arg p

  M.det

open Polynomial


namespace SkewMix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix mixing columns of `A` (where `s j`) and `B` (where `¬ s j`). -/
def mix {F : Type*} (A B : Matrix n n F) (s : n → Prop) [DecidablePred s] : Matrix n n F :=
  Matrix.of fun i j => if s j then A i j else B i j

theorem det_diag_sign {F : Type*} [CommRing F] (s : n → Prop) [DecidablePred s] :
    (Matrix.diagonal fun i => if s i then (-1 : F) else 1).det =
      (-1) ^ (Finset.univ.filter s).card := by
  rw [Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

/-- Core lemma: `N' = R[s,s] ⊕ I` has zero determinant when `R` is skew and `|s|` is odd. -/
theorem det_block_skew_eq_zero {F : Type*} [CommRing F] (h2 : (2 : F) ≠ 0) [NoZeroDivisors F]
    (R : Matrix n n F) (hR : Rᵀ = -R) (s : n → Prop) [DecidablePred s]
    (hs : Odd (Finset.univ.filter s).card) :
    (Matrix.of fun i j => if s j then (if s i then R i j else 0) else (1 : Matrix n n F) i j).det
      = 0 := by
  set N' : Matrix n n F :=
    Matrix.of fun i j => if s j then (if s i then R i j else 0) else (1 : Matrix n n F) i j with hN'
  have hRij : ∀ i j, R j i = - R i j := by
    intro i j
    have := congrFun (congrFun hR i) j
    simpa [Matrix.transpose_apply] using this
  have hT : N'ᵀ = N' * Matrix.diagonal (fun i => if s i then (-1 : F) else 1) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    by_cases hi : s i <;> by_cases hj : s j
    · simp [hN', hi, hj, hRij i j]
    · simp only [hN', Matrix.of_apply, hi, hj, if_true, if_false, Matrix.one_apply, mul_one]
      rw [if_neg]; intro h; exact hj (h ▸ hi)
    · simp only [hN', Matrix.of_apply, hi, hj, if_true, if_false, Matrix.one_apply, mul_neg,
        mul_one]
      rw [if_neg]; · simp
      intro h; exact hi (h ▸ hj)
    · simp only [hN', Matrix.of_apply, hi, hj, if_false, Matrix.one_apply, mul_one, eq_comm]
  have h1 : N'.det = N'.det * (-1) := by
    conv_lhs => rw [← Matrix.det_transpose, hT, Matrix.det_mul, det_diag_sign, hs.neg_one_pow]
  have : N'.det * 2 = 0 := by linear_combination h1
  rcases _root_.mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd h h2

theorem det_mix_eq_zero_of_isUnit {F : Type*} [CommRing F] [NoZeroDivisors F] (h2 : (2 : F) ≠ 0)
    (A B : Matrix n n F) (hA : Aᵀ = -A) (hB : Bᵀ = B) (hAB : A * B = B * A)
    (hBu : IsUnit B.det) (s : n → Prop) [DecidablePred s]
    (hs : Odd (Finset.univ.filter s).card) :
    (mix A B s).det = 0 := by
  set R := B⁻¹ * A with hRdef
  have hBR : B * R = A := by
    rw [hRdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBu, Matrix.one_mul]
  have hcomm : B⁻¹ * A = A * B⁻¹ := by
    calc B⁻¹ * A = B⁻¹ * A * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv _ hBu, Matrix.mul_one]
      _ = B⁻¹ * (A * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * (B * A) * B⁻¹ := by rw [hAB]
      _ = (B⁻¹ * B) * A * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A * B⁻¹ := by rw [Matrix.nonsing_inv_mul _ hBu, Matrix.one_mul]
  have hR : Rᵀ = -R := by
    rw [hRdef, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hA, hB, Matrix.neg_mul, hcomm]
  -- N : columns of R where s, identity elsewhere
  set N : Matrix n n F := Matrix.of fun i j => if s j then R i j else (1 : Matrix n n F) i j with hN
  have hM : mix A B s = B * N := by
    ext i j
    by_cases h : s j
    · have := congrFun (congrFun hBR i) j
      simp only [Matrix.mul_apply] at this
      simp [mix, hN, h, Matrix.mul_apply, this]
    · simp [mix, hN, h, Matrix.mul_apply, Matrix.one_apply]
  set N' : Matrix n n F :=
    Matrix.of fun i j => if s j then (if s i then R i j else 0) else (1 : Matrix n n F) i j with hN'
  set E : Matrix n n F := Matrix.of fun i j => if (¬ s i ∧ s j) then R i j else 0 with hE
  have hNN' : N = N' * (1 + E) := by
    ext i j
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply,
      Finset.sum_eq_single i]
    · by_cases hi : s i <;> by_cases hj : s j <;> simp [hN, hN', hE, hi, hj]
    · intro k _ hk
      by_cases hk' : s k
      · simp [hE, hk']
      · simp [hN', hE, hk', Matrix.one_apply, Ne.symm hk]
    · simp
  have hdetN' : N'.det = 0 := det_block_skew_eq_zero h2 R hR s hs
  rw [hM, Matrix.det_mul, hNN', Matrix.det_mul, hdetN', zero_mul, mul_zero]




theorem det_mix_eq_zero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (A B : Matrix n n R) (hA : Aᵀ = -A) (hB : Bᵀ = B) (hAB : A * B = B * A)
    (s : n → Prop) [DecidablePred s] (hs : Odd (Finset.univ.filter s).card) :
    (mix A B s).det = 0 := by
  let P := R[X]
  let K := FractionRing P
  let f : P →+* K := algebraMap P K
  have hf : Function.Injective f := IsFractionRing.injective P K
  let AP : Matrix n n P := (C : R →+* P).mapMatrix A
  let BP : Matrix n n P := (C : R →+* P).mapMatrix B + (X : P) • (1 : Matrix n n P)
  have hBP : BP = charmatrix (-B) := by
    simp only [BP, charmatrix, Matrix.scalar_apply, map_neg, sub_neg_eq_add,
      Matrix.smul_one_eq_diagonal]
    abel
  have hdetBP : BP.det ≠ 0 := by
    rw [hBP]; exact (Matrix.charpoly_monic (-B)).ne_zero
  let AK : Matrix n n K := f.mapMatrix AP
  let BK : Matrix n n K := f.mapMatrix BP
  have h2K : (2 : K) ≠ 0 := by
    have : f 2 = 2 := map_ofNat f 2
    rw [← this, ← map_zero f]; exact hf.ne (two_ne_zero)
  have hAK : AKᵀ = -AK := by
    ext i j
    have := congrFun (congrFun hA i) j
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    simp [AK, AP, Matrix.transpose_apply, Matrix.neg_apply, this]
  have hBK : BKᵀ = BK := by
    ext i j
    have := congrFun (congrFun hB i) j
    simp only [Matrix.transpose_apply] at this
    simp only [BK, BP, RingHom.mapMatrix_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, this]
    congr 3
    simp [eq_comm]
  have hAPBP : AP * BP = BP * AP := by
    simp only [AP, BP, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul, ← map_mul, hAB]
  have hABK : AK * BK = BK * AK := by
    simp only [AK, BK, ← map_mul, hAPBP]
  have hBKu : IsUnit BK.det := by
    rw [isUnit_iff_ne_zero]
    show (f.mapMatrix BP).det ≠ 0
    rw [← RingHom.map_det]
    exact hf.ne_iff' (map_zero f) |>.mpr hdetBP
  have h0 := det_mix_eq_zero_of_isUnit h2K AK BK hAK hBK hABK hBKu s hs
  have hmixK : mix AK BK s = f.mapMatrix (mix AP BP s) := by
    ext i j
    simp only [mix, AK, BK, RingHom.mapMatrix_apply, Matrix.of_apply, Matrix.map_apply]
    split_ifs <;> rfl
  rw [hmixK, ← RingHom.map_det] at h0
  have hP : (mix AP BP s).det = 0 := hf (by rw [h0, map_zero])
  have hev : (Polynomial.evalRingHom (0 : R)).mapMatrix (mix AP BP s) = mix A B s := by
    ext i j
    simp only [mix, AP, BP, RingHom.mapMatrix_apply, Matrix.of_apply, Matrix.map_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, coe_evalRingHom]
    split_ifs <;> simp
  have := congrArg (Polynomial.evalRingHom (0 : R)) hP
  rw [RingHom.map_det, hev, map_zero] at this
  exact this

end SkewMix

namespace A226163Proof


variable {p m : ℕ}

/-- the element `i+1` of `ZMod p`, for `i : Fin m` -/
def a (p : ℕ) {m : ℕ} (i : Fin m) : ZMod p := ((i : ℕ) + 1 : ℕ)

variable (hpm : p = 2 * m + 1)
include hpm

omit hpm in
lemma prod_a : ∏ i : Fin m, a p i = ((m.factorial : ℕ) : ZMod p) := by
  rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]
  exact Fin.prod_univ_eq_prod_range (fun i => ((i + 1 : ℕ) : ZMod p)) m


lemma a_ne_zero (i : Fin m) : a p i ≠ 0 := by
  intro h
  rw [a, ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd (Nat.succ_pos _) h
  have := i.isLt
  omega

lemma a_inj {i j : Fin m} (h : a p i = a p j) : i = j := by
  rw [a, a, ZMod.natCast_eq_natCast_iff'] at h
  have hi := i.isLt; have hj := j.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  exact Fin.ext (by omega)

lemma a_add_ne_zero (i j : Fin m) : a p i + a p j ≠ 0 := by
  intro h
  rw [a, a, ← Nat.cast_add, ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd (by omega) h
  have := i.isLt; have := j.isLt
  omega

variable [hp : Fact p.Prime]

lemma a_sq_inj {i j : Fin m} (h : a p i ^ 2 = a p j ^ 2) : i = j := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact a_inj hpm h
  · exact absurd (by rw [h]; ring) (a_add_ne_zero hpm i j)

lemma exists_a {y : ZMod p} (hy : y ≠ 0) : ∃ i : Fin m, y = a p i ∨ y = -a p i := by
  have hv : y.val < p := ZMod.val_lt y
  have hv0 : y.val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
  by_cases hle : y.val ≤ m
  · refine ⟨⟨y.val - 1, by omega⟩, Or.inl ?_⟩
    rw [a]; simp only
    rw [Nat.sub_add_cancel (by omega), ZMod.natCast_zmod_val]
  · refine ⟨⟨p - 1 - y.val, by omega⟩, Or.inr ?_⟩
    rw [a]; simp only
    rw [show p - 1 - y.val + 1 = p - y.val by omega, Nat.cast_sub hv.le, ZMod.natCast_self,
      ZMod.natCast_zmod_val, zero_sub, neg_neg]

lemma sum_units_sq {M : Type*} [AddCommMonoid M] (F : ZMod p → M) :
    ∑ u : (ZMod p)ˣ, F ((u : ZMod p) ^ 2) =
      ∑ i : Fin m, F (a p i ^ 2) + ∑ i : Fin m, F (a p i ^ 2) := by
  let e : Fin m ⊕ Fin m → (ZMod p)ˣ :=
    Sum.elim (fun i => Units.mk0 _ (a_ne_zero hpm i)) (fun i => -Units.mk0 _ (a_ne_zero hpm i))
  have hinj : Function.Injective e := by
    rintro (i | i) (j | j) h <;> simp only [e, Sum.elim_inl, Sum.elim_inr] at h <;>
      have h' := congrArg Units.val h <;> simp only [Units.val_mk0, Units.val_neg] at h'
    · rw [a_inj hpm h']
    · exact absurd (by rw [h']; ring) (a_add_ne_zero hpm i j)
    · exact absurd (by rw [← h']; ring) (a_add_ne_zero hpm j i)
    · rw [a_inj hpm (neg_injective h')]
  have hsurj : Function.Surjective e := by
    intro u
    obtain ⟨i, h | h⟩ := exists_a hpm u.ne_zero
    · exact ⟨Sum.inl i, Units.ext (by simp [e, h])⟩
    · exact ⟨Sum.inr i, Units.ext (by simp [e, h])⟩
  let e' := Equiv.ofBijective e ⟨hinj, hsurj⟩
  rw [← Equiv.sum_comp e' (fun u => F ((u : ZMod p) ^ 2)), Fintype.sum_sum_type]
  simp [e', e]

lemma factorial_sq : ((m.factorial : ℕ) : ZMod p) ^ 2 = (-1) ^ (m + 1) := by
  have hw := ZMod.wilsons_lemma p
  have h1 : p - 1 = m + m := by omega
  rw [h1, ← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, Finset.prod_range_add] at hw
  have h2 : ∀ x ∈ Finset.range m,
      ((m + x + 1 : ℕ) : ZMod p) = - (((m - 1 - x) + 1 : ℕ) : ZMod p) := by
    intro x hx
    rw [Finset.mem_range] at hx
    have : (m + x + 1 : ℕ) + ((m - 1 - x) + 1 : ℕ) = p := by omega
    rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add, this, ZMod.natCast_self]
  rw [Finset.prod_congr rfl h2, Finset.prod_neg,
    Finset.prod_range_reflect (fun x => ((x + 1 : ℕ) : ZMod p)) m, Finset.card_range] at hw
  rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]
  have h3 : ((-1 : ZMod p) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  calc (∏ x ∈ Finset.range m, ((x + 1 : ℕ) : ZMod p)) ^ 2
      = ((∏ x ∈ Finset.range m, ((x + 1 : ℕ) : ZMod p)) *
          ((-1) ^ m * ∏ x ∈ Finset.range m, ((x + 1 : ℕ) : ZMod p))) * (-1) ^ m := by
        linear_combination (-(∏ x ∈ Finset.range m, ((x + 1 : ℕ) : ZMod p)) ^ 2) * h3
    _ = (-1) ^ (m + 1) := by rw [hw, pow_succ]; ring


local notation "ψ" => quadraticChar (ZMod p)

lemma psi_neg_one (hp3 : p % 4 = 3) : ψ (-1) = -1 := by
  rw [quadraticChar_neg_one (by rw [ZMod.ringChar_zmod_n]; omega), ZMod.card,
    ZMod.χ₄_nat_three_mod_four hp3]

/-- The key reindexing identity giving commutation of `Φ₊` and `Φ₋`. -/
lemma key_sum (x z : ZMod p) (hx : x ≠ 0) (hz : z ≠ 0) :
    ∑ l : Fin m, ψ ((x ^ 2 - a p l ^ 2) * (a p l ^ 2 + z ^ 2)) =
      ∑ l : Fin m, ψ ((x ^ 2 + a p l ^ 2) * (a p l ^ 2 - z ^ 2)) := by
  have h1 := sum_units_sq hpm (fun t => ψ ((x ^ 2 - t) * (t + z ^ 2)))
  have h2 := sum_units_sq hpm (fun t => ψ ((x ^ 2 + t) * (t - z ^ 2)))
  simp only at h1 h2
  have hU : ∑ u : (ZMod p)ˣ, ψ ((x ^ 2 - (u : ZMod p) ^ 2) * ((u : ZMod p) ^ 2 + z ^ 2)) =
      ∑ u : (ZMod p)ˣ, ψ ((x ^ 2 + (u : ZMod p) ^ 2) * ((u : ZMod p) ^ 2 - z ^ 2)) := by
    let w : (ZMod p)ˣ := Units.mk0 (x * z) (mul_ne_zero hx hz)
    let e : (ZMod p)ˣ ≃ (ZMod p)ˣ := (Equiv.inv _).trans (Equiv.mulLeft w)
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro u _
    have hu : (u : ZMod p) ≠ 0 := u.ne_zero
    have hcalc : (x ^ 2 - ((e u : (ZMod p)ˣ) : ZMod p) ^ 2) * (((e u : (ZMod p)ˣ) : ZMod p) ^ 2 + z ^ 2)
        = (x * z * (u : ZMod p)⁻¹ * (u : ZMod p)⁻¹) ^ 2 *
          ((x ^ 2 + (u : ZMod p) ^ 2) * ((u : ZMod p) ^ 2 - z ^ 2)) := by
      simp only [e, w, Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft, Units.val_mul,
        Units.val_inv_eq_inv_val, Units.val_mk0]
      field_simp
      try ring
    rw [hcalc, map_mul, quadraticChar_sq_one', one_mul]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hx hz) (inv_ne_zero hu)) (inv_ne_zero hu)
  have : ∑ l : Fin m, ψ ((x ^ 2 - a p l ^ 2) * (a p l ^ 2 + z ^ 2)) +
      ∑ l : Fin m, ψ ((x ^ 2 - a p l ^ 2) * (a p l ^ 2 + z ^ 2)) =
      ∑ l : Fin m, ψ ((x ^ 2 + a p l ^ 2) * (a p l ^ 2 - z ^ 2)) +
      ∑ l : Fin m, ψ ((x ^ 2 + a p l ^ 2) * (a p l ^ 2 - z ^ 2)) := by
    rw [← h1, ← h2, hU]
  linarith

theorem det_eq_zero_of_three (hp3 : p % 4 = 3) :
    (Matrix.of fun i j : Fin m =>
      ψ (a p i ^ 2 - ((m.factorial : ℕ) : ZMod p) * a p j)).det = 0 := by
  have hm : Odd m := by rw [Nat.odd_iff]; omega
  have hψneg : ψ (-1) = -1 := psi_neg_one hpm hp3
  set ε : ZMod p := ((m.factorial : ℕ) : ZMod p) with hε
  have hε2 : ε ^ 2 = 1 := by
    rw [hε, factorial_sq hpm]
    exact (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hm)).neg_one_pow
  have hε1 : ε = 1 ∨ ε = -1 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hε2.trans (one_pow 2).symm) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hψε : ((ψ ε : ℤ) : ZMod p) = ε := by
    rcases hε1 with h | h <;> simp [h, hψneg]
  have hψε2 : ψ ε * ψ ε = 1 := by
    rcases hε1 with h | h <;> simp [h, hψneg]
  have hψε1 : ψ ε = 1 ∨ ψ ε = -1 := by
    rcases hε1 with h | h
    · left; rw [h, map_one]
    · right; rw [h, hψneg]
  -- the squares `q j`
  have hσ : ∀ j : Fin m, ∃ k : Fin m, a p k ^ 2 = ((ψ (a p j) : ℤ) : ZMod p) * a p j := by
    intro j
    have hj := a_ne_zero hpm j
    have hsq : IsSquare (((ψ (a p j) : ℤ) : ZMod p) * a p j) := by
      rcases quadraticChar_dichotomy hj with h | h
      · rw [h]; simpa using (quadraticChar_one_iff_isSquare hj).mp h
      · rw [h]
        have hne : ((-1 : ℤ) : ZMod p) * a p j ≠ 0 := by simp [hj]
        rw [← quadraticChar_one_iff_isSquare hne]
        push_cast
        rw [map_mul, hψneg, h]; norm_num
    obtain ⟨y, hy⟩ := hsq
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [mul_zero, _root_.mul_eq_zero] at hy
      rcases hy with hy | hy
      · rcases quadraticChar_dichotomy hj with h | h <;> rw [h] at hy <;> simp at hy
      · exact hj hy
    obtain ⟨k, hk | hk⟩ := exists_a hpm hy0
    · exact ⟨k, by rw [hy, ← hk, sq]⟩
    · exact ⟨k, by rw [hy, hk, sq, neg_mul_neg]⟩
  choose σ hσ using hσ
  have hσinj : Function.Injective σ := by
    intro j j' h
    have h1 := hσ j
    rw [h, hσ j'] at h1
    have hj := a_ne_zero hpm j
    have hj' := a_ne_zero hpm j'
    rcases quadraticChar_dichotomy hj with h2 | h2 <;>
    rcases quadraticChar_dichotomy hj' with h3 | h3 <;> rw [h2, h3] at h1 <;>
      push_cast at h1
    · exact (a_inj hpm (by simpa using h1)).symm
    · exact absurd (by linear_combination -h1) (a_add_ne_zero hpm j j')
    · exact absurd (by linear_combination h1) (a_add_ne_zero hpm j j')
    · exact (a_inj hpm (neg_injective (by simpa using h1))).symm
  have hσbij := (Finite.injective_iff_bijective).mp hσinj
  let σe : Equiv.Perm (Fin m) := Equiv.ofBijective σ hσbij
  let Φp : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun i k => ψ (a p i ^ 2 - a p k ^ 2)
  let Φm : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun i k => ψ (a p i ^ 2 + a p k ^ 2)
  let s : Fin m → Prop := fun j => ψ ε * ψ (a p j) = 1
  let s' : Fin m → Prop := fun k => s (σe.symm k)
  have hΦp : Φpᵀ = -Φp := by
    ext i k
    simp only [Φp, Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply]
    rw [show a p k ^ 2 - a p i ^ 2 = (-1) * (a p i ^ 2 - a p k ^ 2) by ring, map_mul, hψneg]
    ring
  have hΦm : Φmᵀ = Φm := by
    ext i k
    simp only [Φm, Matrix.transpose_apply, Matrix.of_apply, add_comm]
  have hcomm : Φp * Φm = Φm * Φp := by
    ext i k
    simp only [Matrix.mul_apply, Φp, Φm, Matrix.of_apply, ← map_mul]
    exact key_sum hpm (a p i) (a p k) (a_ne_zero hpm i) (a_ne_zero hpm k)
  -- parity
  have hprod : ∏ j : Fin m, (ψ ε * ψ (a p j)) = 1 := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← map_prod, prod_a, ← hε, ← pow_succ]
    obtain ⟨k, hk⟩ := hm
    rw [hk, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul, sq, hψε2, one_pow]
  have hodd_s : Odd (Finset.univ.filter s).card := by
    have hprod' : ∏ j : Fin m, (ψ ε * ψ (a p j)) =
        ∏ j : Fin m, (if s j then (1 : ℤ) else -1) := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hs : s j
      · rw [if_pos hs]; exact hs
      · rw [if_neg hs]
        have hj := a_ne_zero hpm j
        change ¬ (ψ ε * ψ (a p j) = 1) at hs
        rcases hψε1 with h | h <;> rcases quadraticChar_dichotomy hj with h' | h' <;>
          rw [h, h'] at hs ⊢ <;> omega
    rw [hprod', Finset.prod_ite, Finset.prod_const_one, Finset.prod_const, one_mul,
      neg_one_pow_eq_one_iff_even (by decide)] at hprod
    have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ) s
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    rw [Nat.even_iff] at hprod
    rw [Nat.odd_iff] at hm ⊢
    omega
  have hodd : Odd (Finset.univ.filter s').card := by
    have : (Finset.univ.filter s).card = (Finset.univ.filter s').card := by
      apply Finset.card_equiv σe
      intro j
      simp [s']
    rw [← this]; exact hodd_s
  have hM : (Matrix.of fun i j : Fin m => ψ (a p i ^ 2 - ε * a p j)) =
      (SkewMix.mix Φp Φm s').submatrix id σe := by
    ext i j
    simp only [SkewMix.mix, Matrix.submatrix_apply, Matrix.of_apply, id, s', Φp, Φm,
      Equiv.symm_apply_apply]
    have hq : a p (σe j) ^ 2 = ((ψ (a p j) : ℤ) : ZMod p) * a p j := hσ j
    by_cases hs : s j
    · rw [if_pos hs, hq]
      have : ψ (a p j) = ψ ε := by
        have : ψ ε * (ψ ε * ψ (a p j)) = ψ ε * 1 := by rw [hs]
        rw [← mul_assoc, hψε2, one_mul, mul_one] at this
        exact this
      rw [this, hψε]
    · rw [if_neg hs, hq]
      have : ψ (a p j) = -ψ ε := by
        have hj := a_ne_zero hpm j
        change ¬ (ψ ε * ψ (a p j) = 1) at hs
        rcases hψε1 with h | h <;> rcases quadraticChar_dichotomy hj with h' | h' <;>
          rw [h, h'] at hs ⊢ <;> omega
      rw [this, Int.cast_neg, hψε]
      ring_nf
  rw [hM, Matrix.det_permute', SkewMix.det_mix_eq_zero Φp Φm hΦp hΦm hcomm s' hodd, mul_zero]


lemma psi_cast (x : ZMod p) : ((ψ x : ℤ) : ZMod p) = x ^ m := by
  have hp2 := hp.out.two_le
  rw [quadraticChar_eq_pow_of_char_ne_two' (by rw [ZMod.ringChar_zmod_n]; omega) x, ZMod.card]
  congr 1; omega

lemma one_ne_neg_one : (1 : ZMod p) ≠ -1 := by
  intro h
  have hp2 := hp.out.two_le
  have : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

lemma choose_ne_zero (k : ℕ) (hk : k ≤ m) : ((m.choose k : ℕ) : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have h2 : p ∣ m.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial hk]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _
  have := (Nat.Prime.dvd_factorial hp.out).mp h2
  omega

theorem det_ne_zero_of_one (hp1 : p % 4 = 1) :
    (Matrix.of fun i j : Fin m =>
      ψ (a p i ^ 2 - ((m.factorial : ℕ) : ZMod p) * a p j)).det ≠ 0 := by
  intro hdet
  have hp2 := hp.out.two_le
  have hm : Even m := by rw [Nat.even_iff]; omega
  have hm0 : 0 < m := by omega
  set ε : ZMod p := ((m.factorial : ℕ) : ZMod p) with hε
  have hε2 : ε ^ 2 = -1 := by
    rw [hε, factorial_sq hpm]; exact hm.add_one.neg_one_pow
  have hε0 : ε ≠ 0 := by
    intro h; rw [h] at hε2; simp at hε2
  have hne1 : (1 : ZMod p) ≠ -1 := one_ne_neg_one hpm
  -- the matrix over ZMod p
  set MK : Matrix (Fin m) (Fin m) (ZMod p) :=
    Matrix.of fun i j => (a p i ^ 2 - ε * a p j) ^ m with hMKdef
  have hMK : (Int.castRingHom (ZMod p)).mapMatrix
      (Matrix.of fun i j : Fin m => ψ (a p i ^ 2 - ε * a p j)) = MK := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hMKdef, eq_intCast]
    exact psi_cast hpm _
  have hdetK : MK.det = 0 := by
    rw [← hMK, ← RingHom.map_det, hdet, map_zero]
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetK
  -- moments
  set μ : ℕ → ZMod p := fun r => ∑ j, a p j ^ r * v j with hμ
  set c : ℕ → ZMod p := fun k => ((m.choose k : ℕ) : ZMod p) * (-ε) ^ (m - k) * μ (m - k) with hc
  have hexp : ∀ i : Fin m, ∑ k ∈ Finset.range (m + 1), (a p i ^ 2) ^ k * c k = 0 := by
    intro i
    have h := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, hMKdef, Matrix.of_apply, Pi.zero_apply] at h
    rw [← h]
    simp_rw [sub_eq_add_neg, add_pow, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    simp only [hc, hμ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [neg_mul_eq_neg_mul, mul_pow]
    ring
  have hX1 : ∀ i : Fin m, (a p i ^ 2) ^ m = 1 := by
    intro i
    rw [← pow_mul, show 2 * m = p - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one (a_ne_zero hpm i)
  set w : Fin m → ZMod p := fun k => c k + if (k : ℕ) = 0 then c m else 0 with hw
  have hVw : (Matrix.vandermonde fun i => a p i ^ 2) *ᵥ w = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply, hw]
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [Fin.sum_univ_eq_sum_range (fun k => (a p i ^ 2) ^ k * c k) m]
    rw [Finset.sum_eq_single (⟨0, hm0⟩ : Fin m)]
    · have := hexp i
      rw [Finset.sum_range_succ, hX1] at this
      simpa using this
    · intro k _ hk
      rw [if_neg]; · simp
      intro h; apply hk; exact Fin.ext h
    · simp
  have hw0 : w = 0 := Matrix.eq_zero_of_mulVec_eq_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr (fun i j h => a_sq_inj hpm h)) hVw
  have hμmid : ∀ r, 0 < r → r < m → μ r = 0 := by
    intro r hr0 hrm
    have hk := congrFun hw0 ⟨m - r, by omega⟩
    simp only [hw, Pi.zero_apply] at hk
    rw [if_neg (by show m - r ≠ 0; omega), add_zero, hc] at hk
    simp only at hk
    rw [show m - (m - r) = r by omega] at hk
    rcases _root_.mul_eq_zero.mp hk with h | h
    · exfalso
      rcases _root_.mul_eq_zero.mp h with h | h
      · exact choose_ne_zero hpm _ (Nat.sub_le m r) h
      · exact hε0 (neg_eq_zero.mp (pow_eq_zero_iff (by omega) |>.mp h))
    · exact h
  have hk0 := congrFun hw0 ⟨0, hm0⟩
  simp only [hw, Pi.zero_apply, if_true, hc] at hk0
  simp only [Nat.choose_zero_right, Nat.choose_self, Nat.sub_zero, Nat.sub_self, pow_zero,
    Nat.cast_one, one_mul, mul_one] at hk0
  -- polynomial step
  have hμm : μ m = -ε * μ 0 := by
    let g : Polynomial (ZMod p) := ∏ j : Fin m, (X - C (a p j))
    have hg_monic : g.Monic :=
      Polynomial.monic_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)
    have hg_deg : g.natDegree = m := by
      rw [Polynomial.natDegree_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)]
      simp
    have hg_eval : ∀ j : Fin m, g.eval (a p j) = 0 := by
      intro j
      simp only [g, Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp
    have hg0 : g.eval 0 = ε := by
      simp only [g, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, zero_sub]
      rw [Finset.prod_neg, prod_a, Finset.card_univ, Fintype.card_fin, hm.neg_one_pow, one_mul]
    have hcm : g.coeff m = 1 := by rw [← hg_deg]; exact hg_monic.coeff_natDegree
    have hc0 : g.coeff 0 = ε := by rw [Polynomial.coeff_zero_eq_eval_zero, hg0]
    have key : ∑ j, v j * g.eval (a p j) = ∑ r ∈ Finset.range (m + 1), g.coeff r * μ r := by
      simp_rw [Polynomial.eval_eq_sum_range, hg_deg, Finset.mul_sum, hμ]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [Finset.sum_range_succ, hcm,
      Finset.sum_eq_single 0 (fun r hr hr0 => by
        rw [hμmid r (Nat.pos_of_ne_zero hr0) (Finset.mem_range.mp hr), mul_zero])
        (fun h => absurd (Finset.mem_range.mpr hm0) h), hc0] at key
    simp only [hg_eval, mul_zero, Finset.sum_const_zero] at key
    linear_combination -key
  rw [hμm, hm.neg_pow] at hk0
  have hε_pow : ε ^ (m + 1) ≠ 1 := by
    intro h
    have : (ε ^ (m + 1)) ^ 2 = 1 := by rw [h, one_pow]
    rw [← pow_mul, mul_comm, pow_mul, hε2, hm.add_one.neg_one_pow] at this
    exact hne1 this.symm
  have hμ0 : μ 0 = 0 := by
    have : μ 0 * (1 - ε ^ (m + 1)) = 0 := by rw [pow_succ]; linear_combination hk0
    rcases _root_.mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h).symm hε_pow
  have hμall : ∀ r, r < m → μ r = 0 := by
    intro r hr
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h]; exact hμ0
    · exact hμmid r h hr
  have hVa : (Matrix.vandermonde (a p))ᵀ *ᵥ v = 0 := by
    ext r
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply,
      Pi.zero_apply]
    exact hμall r r.isLt
  exact hv0 (Matrix.eq_zero_of_mulVec_eq_zero (by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr (fun i j h => a_inj hpm h)) hVa)

end A226163Proof

/--
Conjecture: a(n) = 0 if and only if p_n ≡ 3 (mod 4).
-/
theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  have hn : ¬ n < 2 := by omega
  simp only [A226163, dif_neg hn]
  set p := Nat.nth Nat.Prime (n - 1) with hp_def
  have hp : p.Prime := Nat.prime_nth_prime (n - 1)
  have hp2 : 2 < p := by
    rw [hp_def, ← Nat.nth_prime_zero_eq_two]
    exact Nat.nth_strictMono Nat.infinite_setOf_prime (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  haveI : Fact p.Prime := ⟨hp⟩
  set m := (p - 1) / 2 with hm
  have hpm : p = 2 * m + 1 := by omega
  have hmat : (fun i j : Fin m => jacobiSym (((i.val + 1 : ℕ) : ℤ) * ((i.val + 1 : ℕ) : ℤ) -
      ((m.factorial : ℕ) : ℤ) * ((j.val + 1 : ℕ) : ℤ)) p) =
      Matrix.of fun i j : Fin m => quadraticChar (ZMod p)
        (A226163Proof.a p i ^ 2 - ((m.factorial : ℕ) : ZMod p) * A226163Proof.a p j) := by
    ext i j
    rw [Matrix.of_apply, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym, A226163Proof.a, A226163Proof.a]
    push_cast
    ring_nf
  rw [hmat]
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h | h
  · exact iff_of_false (A226163Proof.det_ne_zero_of_one hpm h) (by omega)
  · exact iff_of_true (A226163Proof.det_eq_zero_of_three hpm h) h

theorem oeis_226163_conjecture_0.disproof : ¬ (type_of% @oeis_226163_conjecture_0) := sorry
