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



open Matrix Polynomial

section CoreLemma

variable {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]

/-- If `K` is orthogonal, `D` is symmetric with `D * D = 1`, and
`det K * det D = -1`, then `det (K + D) = 0` (char ≠ 2). -/
theorem det_orth_add_symm_eq_zero (h2 : (2 : F) ≠ 0) (K D : Matrix n n F)
    (hK : Kᵀ * K = 1) (hDs : Dᵀ = D) (hD2 : D * D = 1)
    (hdet : K.det * D.det = -1) : (K + D).det = 0 := by
  have h1 : Kᵀ + D = Kᵀ * (1 + K * D) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hK, Matrix.one_mul]
  have h3 : (1 : Matrix n n F) + K * D = (D + K) * D := by
    rw [Matrix.add_mul, hD2]
  have key : (K + D).det = -(K + D).det := by
    calc (K + D).det = ((K + D)ᵀ).det := (Matrix.det_transpose _).symm
    _ = (Kᵀ + D).det := by rw [Matrix.transpose_add, hDs]
    _ = Kᵀ.det * (1 + K * D).det := by rw [h1, Matrix.det_mul]
    _ = Kᵀ.det * ((D + K).det * D.det) := by rw [h3, Matrix.det_mul]
    _ = (K.det * D.det) * (K + D).det := by
        rw [Matrix.det_transpose, _root_.add_comm D K]; ring
    _ = -(K + D).det := by rw [hdet]; ring
  have : (2 : F) * (K + D).det = 0 := by linear_combination key
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h h2
  · exact h

end CoreLemma

section MainLemma

variable {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]

/-- Over the fraction field, for invertible normal `W'`, symmetric `D'` with `D'*D'=1`,
`det D' = 1`, odd size: `det (W' - W'ᵀ * D') = 0`. -/
theorem det_sub_transpose_mul_symm_aux (h2 : (2 : F) ≠ 0) (hodd : Odd (Fintype.card n))
    (W D : Matrix n n F) (hW : W * Wᵀ = Wᵀ * W) (hdet : W.det ≠ 0)
    (hDs : Dᵀ = D) (hD2 : D * D = 1) (hDdet : D.det = 1) :
    (W - Wᵀ * D).det = 0 := by
  have hu : IsUnit W.det := isUnit_iff_ne_zero.mpr hdet
  have hut : IsUnit Wᵀ.det := by rwa [Matrix.det_transpose]
  -- inverses commute with transpose products
  have hcomm : W⁻¹ * Wᵀ = Wᵀ * W⁻¹ := by
    have h1 : W⁻¹ * (W * Wᵀ) * W⁻¹ = W⁻¹ * (Wᵀ * W) * W⁻¹ := by rw [hW]
    calc W⁻¹ * Wᵀ = W⁻¹ * Wᵀ * (W * W⁻¹) := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = W⁻¹ * (Wᵀ * W) * W⁻¹ := by noncomm_ring
    _ = W⁻¹ * (W * Wᵀ) * W⁻¹ := by rw [hW]
    _ = (W⁻¹ * W) * (Wᵀ * W⁻¹) := by noncomm_ring
    _ = Wᵀ * W⁻¹ := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  set K : Matrix n n F := -(W⁻¹ * Wᵀ) with hKdef
  have hKt : Kᵀ = -(W * (Wᵀ)⁻¹) := by
    rw [hKdef, Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv]
  have hKtK : Kᵀ * K = 1 := by
    rw [hKt, hKdef, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    calc W * (Wᵀ)⁻¹ * (W⁻¹ * Wᵀ) = W * (Wᵀ)⁻¹ * (Wᵀ * W⁻¹) := by rw [hcomm]
    _ = W * ((Wᵀ)⁻¹ * Wᵀ) * W⁻¹ := by noncomm_ring
    _ = W * W⁻¹ := by rw [Matrix.nonsing_inv_mul _ hut, Matrix.mul_one]
    _ = 1 := Matrix.mul_nonsing_inv _ hu
  have hKdet : K.det * D.det = -1 := by
    rw [hDdet, _root_.mul_one, hKdef, Matrix.det_neg, Matrix.det_mul, Matrix.det_nonsing_inv,
      Matrix.det_transpose, hodd.neg_one_pow, Ring.inverse_eq_inv]
    field_simp
  have hfact : W - Wᵀ * D = W * (1 + K * D) := by
    rw [Matrix.mul_add, Matrix.mul_one, hKdef, Matrix.neg_mul, Matrix.mul_neg,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul,
      sub_eq_add_neg]
  have h1KD : (1 : Matrix n n F) + K * D = (D + K) * D := by rw [Matrix.add_mul, hD2]
  rw [hfact, Matrix.det_mul, h1KD, Matrix.det_mul, _root_.add_comm D K,
    det_orth_add_symm_eq_zero h2 K D hKtK hDs hD2 hKdet]
  ring

end MainLemma

section PolyTrick

variable {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 800000 in
/-- Main lemma: for a normal matrix `W` of odd size over a field of characteristic zero,
and a symmetric `D` with `D * D = 1` and `det D = 1`, we have `det (W - Wᵀ * D) = 0`. -/
theorem det_normal_sub_transpose_mul_symm [CharZero F] (hodd : Odd (Fintype.card n))
    (W D : Matrix n n F) (hW : W * Wᵀ = Wᵀ * W)
    (hDs : Dᵀ = D) (hD2 : D * D = 1) (hDdet : D.det = 1) :
    (W - Wᵀ * D).det = 0 := by
  classical
  let 𝕂 := FractionRing (Polynomial F)
  let ψ : Polynomial F →+* 𝕂 := algebraMap (Polynomial F) 𝕂
  have hψ : Function.Injective ψ := IsFractionRing.injective (Polynomial F) 𝕂
  -- the perturbed matrix over F[X]
  set Wh : Matrix n n (Polynomial F) := W.map Polynomial.C + (Polynomial.X : Polynomial F) • 1
    with hWh
  set Dh : Matrix n n (Polynomial F) := D.map Polynomial.C with hDh
  -- Wh = charmatrix (-W), so det Wh ≠ 0
  have hWh_eq : Wh = Matrix.charmatrix (-W) := by
    rw [Matrix.charmatrix, hWh]
    ext i j
    by_cases h : i = j <;>
      simp [h, Matrix.scalar_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.diagonal_apply, RingHom.mapMatrix_apply, sub_eq_add_neg, _root_.add_comm]
  have hWh_det : Wh.det ≠ 0 := by
    rw [hWh_eq, ← Matrix.charpoly]
    exact (Matrix.charpoly_monic (-W)).ne_zero
  -- normality over F[X]
  have hWh_norm : Wh * Whᵀ = Whᵀ * Wh := by
    have hCW : (W.map Polynomial.C) * (Wᵀ.map Polynomial.C)
        = (Wᵀ.map Polynomial.C) * (W.map Polynomial.C) := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, hW]
    rw [hWh, Matrix.transpose_add, ← Matrix.transpose_map, Matrix.transpose_smul,
      Matrix.transpose_one]
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_add]
    rw [hCW]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    abel
  -- move to the fraction field
  set W' : Matrix n n 𝕂 := Wh.map ψ with hW'
  set D' : Matrix n n 𝕂 := Dh.map ψ with hD'
  have hmapmul : ∀ (A B : Matrix n n (Polynomial F)), (A * B).map ψ = A.map ψ * B.map ψ :=
    fun A B => Matrix.map_mul
  have hmapsub : ∀ (A B : Matrix n n (Polynomial F)), (A - B).map ψ = A.map ψ - B.map ψ :=
    fun A B => Matrix.map_sub ψ (fun a b => map_sub ψ a b) A B
  have hW'det : W'.det ≠ 0 := by
    rw [hW', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    intro h
    exact hWh_det (hψ (h.trans (map_zero ψ).symm))
  have hW'norm : W' * W'ᵀ = W'ᵀ * W' := by
    rw [hW', ← Matrix.transpose_map, ← hmapmul, ← hmapmul, hWh_norm]
  have hD's : D'ᵀ = D' := by
    rw [hD', hDh, Matrix.transpose_map.symm, Matrix.transpose_map.symm, hDs]
  have hD'2 : D' * D' = 1 := by
    rw [hD', ← hmapmul, hDh, ← Matrix.map_mul, hD2, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hD'det : D'.det = 1 := by
    rw [hD', ← RingHom.mapMatrix_apply, ← RingHom.map_det, hDh, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, hDdet]
    simp
  have h2 : (2 : 𝕂) ≠ 0 := by
    intro h
    have h2' : ψ (2 : Polynomial F) = 0 := by rw [map_ofNat]; exact_mod_cast h
    rw [← map_zero ψ] at h2'
    exact two_ne_zero (hψ h2')
  have hmain : (W' - W'ᵀ * D').det = 0 :=
    det_sub_transpose_mul_symm_aux h2 hodd W' D' hW'norm hW'det hD's hD'2 hD'det
  -- pull back to F[X]
  have hpull : (Wh - Whᵀ * Dh).det = 0 := by
    have h0 : ((Wh - Whᵀ * Dh).map ψ).det = 0 := by
      rw [hmapsub, hmapmul, Matrix.transpose_map]
      exact hmain
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h0
    exact hψ (h0.trans (map_zero ψ).symm)
  -- evaluate at X = 0
  have hfinal : (W - Wᵀ * D) = (Wh - Whᵀ * Dh).map (Polynomial.evalRingHom (0 : F)) := by
    have hWh0 : Wh.map (Polynomial.evalRingHom (0:F)) = W := by
      rw [hWh]
      ext i j
      by_cases h : i = j <;>
        simp [h, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
          smul_eq_mul]
    have hDh0 : Dh.map (Polynomial.evalRingHom (0:F)) = D := by
      rw [hDh]; ext i j; simp [Matrix.map_apply]
    have hmul0 : ∀ (A B : Matrix n n (Polynomial F)),
        (A * B).map (Polynomial.evalRingHom (0:F)) =
        A.map (Polynomial.evalRingHom (0:F)) * B.map (Polynomial.evalRingHom (0:F)) :=
      fun A B => Matrix.map_mul
    have hsub0 : ∀ (A B : Matrix n n (Polynomial F)),
        (A - B).map (Polynomial.evalRingHom (0:F)) =
        A.map (Polynomial.evalRingHom (0:F)) - B.map (Polynomial.evalRingHom (0:F)) :=
      fun A B => Matrix.map_sub _ (fun a b => map_sub _ a b) A B
    rw [hsub0, hmul0, hWh0, Matrix.transpose_map, hWh0, hDh0]
  rw [hfinal, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hpull, map_zero]

end PolyTrick

/-! ## Part 1 : the case `p % 4 = 3` -/

namespace OEIS226163

variable {p : ℕ} [hp : Fact p.Prime]

private lemma natCast_ne_zero_of_lt {k : ℕ} (h1 : k ≠ 0) (h2 : k < p) : ((k : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
  intro hdvd
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero h1) hdvd
  omega

private lemma natCast_inj_of_lt {a b : ℕ} (ha : a < p) (hb : b < p)
    (h : ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p)) : a = b := by
  have h1 := ZMod.val_cast_of_lt ha
  have h2 := ZMod.val_cast_of_lt hb
  rw [h] at h1
  omega

private lemma factorial_cast_ne_zero : ((((p-1)/2).factorial : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p, hp.out.dvd_factorial]
  have := hp.out.two_le
  omega

variable (p) in
/-- The subgroup of squares in `(ZMod p)ˣ`. -/
private def Sq : Subgroup (ZMod p)ˣ := (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range

noncomputable instance : Fintype ↥(Sq p) := Fintype.ofFinite _

private lemma mem_Sq_iff {x : (ZMod p)ˣ} : x ∈ Sq p ↔ ∃ u : (ZMod p)ˣ, u ^ 2 = x := by
  simp [Sq, MonoidHom.mem_range, powMonoidHom_apply]

/-- coercion of an element of `Sq p` to `ZMod p`. -/
private def cv (r : ↥(Sq p)) : ZMod p := ((r : (ZMod p)ˣ) : ZMod p)

private lemma cv_ne_zero (r : ↥(Sq p)) : cv r ≠ 0 := Units.ne_zero _

private lemma chi_cv_eq_one (r : ↥(Sq p)) : quadraticChar (ZMod p) (cv r) = 1 := by
  obtain ⟨u, hu⟩ := mem_Sq_iff.mp r.2
  have hval : cv r = (u : ZMod p) * (u : ZMod p) := by
    rw [cv, ← hu, ← Units.val_mul, sq]
  rw [hval]
  exact (quadraticChar_one_iff_isSquare
    (mul_ne_zero (Units.ne_zero u) (Units.ne_zero u))).mpr ⟨_, rfl⟩

private lemma chi_neg_one (hp3 : p % 4 = 3) : quadraticChar (ZMod p) (-1) = -1 :=
  quadraticChar_neg_one_iff_not_isSquare.mpr
    (by rw [ZMod.exists_sq_eq_neg_one_iff]; omega)

private lemma chi_neg (hp3 : p % 4 = 3) (x : ZMod p) :
    quadraticChar (ZMod p) (-x) = -quadraticChar (ZMod p) x := by
  rw [show -x = (-1) * x by ring, map_mul, chi_neg_one hp3]
  ring

variable (p) in
private noncomputable def u1 (i : Fin ((p-1)/2)) : (ZMod p)ˣ :=
  Units.mk0 ((i.1 + 1 : ℕ) : ZMod p) (by
    apply natCast_ne_zero_of_lt (by omega)
    have h2 := hp.out.two_le
    have := i.2
    omega)

private lemma u1_val (i : Fin ((p-1)/2)) : ((u1 p i : (ZMod p)ˣ) : ZMod p) = ((i.1 + 1 : ℕ) : ZMod p) :=
  rfl

variable (p) in
private noncomputable def Cu : (ZMod p)ˣ :=
  Units.mk0 ((((p-1)/2).factorial : ℕ) : ZMod p) factorial_cast_ne_zero

private lemma Cu_val : ((Cu p : (ZMod p)ˣ) : ZMod p) = ((((p-1)/2).factorial : ℕ) : ZMod p) := rfl

/-- The row parametrization of the squares by `1, ..., (p-1)/2`. -/
private lemma eR_bijective (hodd : p % 2 = 1) :
    Function.Bijective (fun i : Fin ((p-1)/2) =>
      (⟨u1 p i ^ 2, mem_Sq_iff.mpr ⟨u1 p i, rfl⟩⟩ : ↥(Sq p))) := by
  have h2 := hp.out.two_le
  constructor
  · intro i i' hii
    have hval : ((i.1 + 1 : ℕ) : ZMod p) ^ 2 = ((i'.1 + 1 : ℕ) : ZMod p) ^ 2 := by
      have := congrArg (fun x : ↥(Sq p) => ((x : (ZMod p)ˣ) : ZMod p)) hii
      simpa [Units.val_pow_eq_pow_val, u1_val] using this
    have hfact : (((i.1 + 1 : ℕ) : ZMod p) - ((i'.1 + 1 : ℕ) : ZMod p)) *
        (((i.1 + 1 : ℕ) : ZMod p) + ((i'.1 + 1 : ℕ) : ZMod p)) = 0 := by
      linear_combination hval
    have hi := i.2
    have hi' := i'.2
    rcases mul_eq_zero.mp hfact with hcase | hcase
    · have : ((i.1 + 1 : ℕ) : ZMod p) = ((i'.1 + 1 : ℕ) : ZMod p) := by
        linear_combination hcase
      have := natCast_inj_of_lt (by omega) (by omega) this
      exact Fin.ext (by omega)
    · exfalso
      have hzero : (((i.1 + 1) + (i'.1 + 1) : ℕ) : ZMod p) = 0 := by
        push_cast at hcase ⊢
        linear_combination hcase
      rw [CharP.cast_eq_zero_iff (ZMod p) p] at hzero
      have := Nat.le_of_dvd (by omega) hzero
      omega
  · rintro ⟨q, hq⟩
    obtain ⟨u, hu⟩ := mem_Sq_iff.mp hq
    set a := ((u : (ZMod p)ˣ) : ZMod p).val with ha
    have hu0 : ((u : (ZMod p)ˣ) : ZMod p) ≠ 0 := Units.ne_zero u
    have ha0 : a ≠ 0 := by
      rw [ha, Ne, ZMod.val_eq_zero]
      exact hu0
    have hap : a < p := ZMod.val_lt _
    have hcast : ((a : ℕ) : ZMod p) = ((u : (ZMod p)ˣ) : ZMod p) := ZMod.natCast_rightInverse _
    by_cases hle : a ≤ (p-1)/2
    · refine ⟨⟨a - 1, by omega⟩, ?_⟩
      have hu1 : u1 p ⟨a - 1, by omega⟩ = u := by
        apply Units.ext
        rw [u1_val]
        have : a - 1 + 1 = a := by omega
        rw [this, hcast]
      apply Subtype.ext
      show u1 p _ ^ 2 = q
      rw [hu1, hu]
    · refine ⟨⟨p - 1 - a, by omega⟩, ?_⟩
      have hu1 : u1 p ⟨p - 1 - a, by omega⟩ = -u := by
        apply Units.ext
        rw [u1_val]
        have hstep : p - 1 - a + 1 = p - a := by omega
        rw [hstep, Units.val_neg, ← hcast]
        push_cast [Nat.cast_sub (le_of_lt hap)]
        simp
      apply Subtype.ext
      show u1 p _ ^ 2 = q
      rw [hu1, ← hu]
      exact neg_sq u

open Classical in
variable (p) in
/-- the representative of `{x, -x}` that is a square. -/
private noncomputable def sqrep (x : (ZMod p)ˣ) : (ZMod p)ˣ :=
  if IsSquare ((x : (ZMod p)ˣ) : ZMod p) then x else -x

private lemma sqrep_val (hp3 : p % 4 = 3) (x : (ZMod p)ˣ) :
    ((sqrep p x : (ZMod p)ˣ) : ZMod p)
      = ((quadraticChar (ZMod p) ((x : (ZMod p)ˣ) : ZMod p) : ℤ) : ZMod p) * ((x : (ZMod p)ˣ) : ZMod p) := by
  rw [sqrep]
  split_ifs with h
  · rw [(quadraticChar_one_iff_isSquare (Units.ne_zero x)).mpr h]
    simp
  · rw [quadraticChar_neg_one_iff_not_isSquare.mpr h, Units.val_neg]
    push_cast
    ring

private lemma sqrep_mem (hp3 : p % 4 = 3) (x : (ZMod p)ˣ) : sqrep p x ∈ Sq p := by
  rw [sqrep]
  split_ifs with h
  · obtain ⟨y, hy⟩ := h
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, MulZeroClass.mul_zero] at hy
      exact Units.ne_zero x hy
    refine mem_Sq_iff.mpr ⟨Units.mk0 y hy0, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, sq, ← hy]
  · have hchi : quadraticChar (ZMod p) ((x : (ZMod p)ˣ) : ZMod p) = -1 :=
      quadraticChar_neg_one_iff_not_isSquare.mpr h
    have hsq : IsSquare (-((x : (ZMod p)ˣ) : ZMod p)) := by
      apply (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr (Units.ne_zero x))).mp
      rw [chi_neg hp3, hchi]
      ring
    obtain ⟨y, hy⟩ := hsq
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, MulZeroClass.mul_zero] at hy
      exact neg_ne_zero.mpr (Units.ne_zero x) hy
    refine mem_Sq_iff.mpr ⟨Units.mk0 y hy0, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, sq, ← hy, Units.val_neg]

/-- The column parametrization: `j ↦ ` square-representative of `m! * (j+1)`. -/
private lemma eC_bijective (hodd : p % 2 = 1) (hp3 : p % 4 = 3) :
    Function.Bijective (fun j : Fin ((p-1)/2) =>
      (⟨sqrep p (Cu p * u1 p j), sqrep_mem hp3 _⟩ : ↥(Sq p))) := by
  have h2 := hp.out.two_le
  constructor
  · intro j j' hjj
    -- from equality of sqrep values get w j = ± w j'
    have hval : ((sqrep p (Cu p * u1 p j) : (ZMod p)ˣ) : ZMod p)
        = ((sqrep p (Cu p * u1 p j') : (ZMod p)ˣ) : ZMod p) := by
      exact congrArg (fun x : ↥(Sq p) => ((x : (ZMod p)ˣ) : ZMod p)) hjj
    rw [sqrep_val hp3, sqrep_val hp3] at hval
    set w := ((Cu p * u1 p j : (ZMod p)ˣ) : ZMod p) with hw
    set w' := ((Cu p * u1 p j' : (ZMod p)ˣ) : ZMod p) with hw'
    have hw0 : w ≠ 0 := Units.ne_zero _
    have hw'0 : w' ≠ 0 := Units.ne_zero _
    have hcases : w = w' ∨ w = -w' := by
      rcases quadraticChar_dichotomy hw0 with h1 | h1 <;>
        rcases quadraticChar_dichotomy hw'0 with h2' | h2' <;>
          rw [h1, h2'] at hval <;> push_cast at hval <;>
          first
            | (left; linear_combination hval)
            | (left; linear_combination -hval)
            | (right; linear_combination hval)
            | (right; linear_combination -hval)
    -- cancel the unit Cu
    have hC0 : ((Cu p : (ZMod p)ˣ) : ZMod p) ≠ 0 := Units.ne_zero _
    have hju : w = ((Cu p : (ZMod p)ˣ) : ZMod p) * ((j.1 + 1 : ℕ) : ZMod p) := by
      rw [hw, Units.val_mul, u1_val]
    have hju' : w' = ((Cu p : (ZMod p)ˣ) : ZMod p) * ((j'.1 + 1 : ℕ) : ZMod p) := by
      rw [hw', Units.val_mul, u1_val]
    have hj := j.2
    have hj' := j'.2
    rcases hcases with hcase | hcase
    · rw [hju, hju'] at hcase
      have := mul_left_cancel₀ hC0 hcase
      have := natCast_inj_of_lt (by omega) (by omega) this
      exact Fin.ext (by omega)
    · exfalso
      rw [hju, hju'] at hcase
      have hsum : ((Cu p : (ZMod p)ˣ) : ZMod p) * ((((j.1 + 1) + (j'.1 + 1) : ℕ)) : ZMod p) = 0 := by
        push_cast at hcase ⊢
        linear_combination hcase
      rcases mul_eq_zero.mp hsum with h0 | h0
      · exact hC0 h0
      · rw [CharP.cast_eq_zero_iff (ZMod p) p] at h0
        have := Nat.le_of_dvd (by omega) h0
        omega
  · rintro ⟨q, hq⟩
    -- x = Cu⁻¹ * q
    set x : (ZMod p)ˣ := (Cu p)⁻¹ * q with hx
    set a := ((x : (ZMod p)ˣ) : ZMod p).val with ha
    have hx0 : ((x : (ZMod p)ˣ) : ZMod p) ≠ 0 := Units.ne_zero x
    have ha0 : a ≠ 0 := by
      rw [ha, Ne, ZMod.val_eq_zero]
      exact hx0
    have hap : a < p := ZMod.val_lt _
    have hcast : ((a : ℕ) : ZMod p) = ((x : (ZMod p)ˣ) : ZMod p) := ZMod.natCast_rightInverse _
    have hqsq : IsSquare ((q : (ZMod p)ˣ) : ZMod p) := by
      obtain ⟨u, hu⟩ := mem_Sq_iff.mp hq
      exact ⟨((u : (ZMod p)ˣ) : ZMod p), by rw [← hu, Units.val_pow_eq_pow_val, sq]⟩
    by_cases hle : a ≤ (p-1)/2
    · refine ⟨⟨a - 1, by omega⟩, ?_⟩
      have hu1 : u1 p ⟨a - 1, by omega⟩ = x := by
        apply Units.ext
        rw [u1_val]
        have : a - 1 + 1 = a := by omega
        rw [this, hcast]
      apply Subtype.ext
      show ((sqrep p (Cu p * u1 p _) : (ZMod p)ˣ)) = q
      rw [hu1, hx, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul, sqrep]
      rw [if_pos hqsq]
    · refine ⟨⟨p - 1 - a, by omega⟩, ?_⟩
      have hu1 : u1 p ⟨p - 1 - a, by omega⟩ = -x := by
        apply Units.ext
        rw [u1_val]
        have hstep : p - 1 - a + 1 = p - a := by omega
        rw [hstep, Units.val_neg, ← hcast]
        push_cast [Nat.cast_sub (le_of_lt hap)]
        simp
      apply Subtype.ext
      show ((sqrep p (Cu p * u1 p _) : (ZMod p)ˣ)) = q
      have hqval : ((q : (ZMod p)ˣ) : ZMod p) ≠ 0 := Units.ne_zero _
      have hchiq : quadraticChar (ZMod p) ((q : (ZMod p)ˣ) : ZMod p) = 1 :=
        (quadraticChar_one_iff_isSquare hqval).mpr hqsq
      have hnotsq : ¬ IsSquare (((-q : (ZMod p)ˣ) : ZMod p)) := by
        rw [Units.val_neg]
        intro hcon
        have := (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr hqval)).mpr hcon
        rw [chi_neg hp3, hchiq] at this
        norm_num at this
      rw [hu1, mul_neg, hx, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul, sqrep, if_neg hnotsq, neg_neg]

/-- determinant of a doubly-reindexed matrix vanishes if the original does. -/
private lemma det_submatrix_eq_zero {α β R : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [CommRing R] (N : Matrix β β R) (e f : α ≃ β)
    (h : N.det = 0) : (N.submatrix e f).det = 0 := by
  have heq : N.submatrix ⇑e ⇑f = (N.submatrix e e).submatrix id ⇑(f.trans e.symm) := by
    ext i j
    simp [Matrix.submatrix_apply]
  rw [heq, Matrix.det_permute', Matrix.det_submatrix_equiv_self, h, MulZeroClass.mul_zero]

private lemma cv_mul (x y : ↥(Sq p)) : cv (x * y) = cv x * cv y := by
  rw [cv, cv, cv]
  norm_cast

private lemma cv_inv (x : ↥(Sq p)) : cv x⁻¹ = (cv x)⁻¹ := by
  rw [cv, cv]
  norm_cast

/-- The `U` matrix entry function. -/
private noncomputable def uent (r q : ↥(Sq p)) : ℚ :=
  ((quadraticChar (ZMod p) (cv r - cv q) + quadraticChar (ZMod p) (cv r + cv q) : ℤ) : ℚ)

private lemma uent_shift (r r' q : ↥(Sq p)) : uent r (r * r' * q⁻¹) = uent q r' := by
  have hkey : ∀ s : ↥(Sq p), quadraticChar (ZMod p) (cv q - cv s) =
      quadraticChar (ZMod p) (cv r - cv (r * s * q⁻¹)) ∧
      quadraticChar (ZMod p) (cv q + cv s) =
      quadraticChar (ZMod p) (cv r + cv (r * s * q⁻¹)) := by
    intro s
    have hq0 : cv q ≠ 0 := cv_ne_zero q
    have h1 : cv r - cv (r * s * q⁻¹) = cv (r * q⁻¹) * (cv q - cv s) := by
      rw [cv_mul, cv_mul, cv_mul, cv_inv]
      field_simp
    have h2 : cv r + cv (r * s * q⁻¹) = cv (r * q⁻¹) * (cv q + cv s) := by
      rw [cv_mul, cv_mul, cv_mul, cv_inv]
      field_simp
    constructor
    · rw [h1, map_mul, chi_cv_eq_one (r * q⁻¹), _root_.one_mul]
    · rw [h2, map_mul, chi_cv_eq_one (r * q⁻¹), _root_.one_mul]
  obtain ⟨ha, hb⟩ := hkey r'
  rw [uent, uent, ← ha, ← hb]

private lemma uent_shift' (r r' q : ↥(Sq p)) : uent r' (r * r' * q⁻¹) = uent q r := by
  have : r * r' * q⁻¹ = r' * r * q⁻¹ := by rw [_root_.mul_comm r r']
  rw [this, uent_shift r' r q]

variable (p) in
private noncomputable def Umat : Matrix ↥(Sq p) ↥(Sq p) ℚ := Matrix.of uent

private lemma Umat_normal : Umat p * (Umat p)ᵀ = (Umat p)ᵀ * Umat p := by
  ext r r'
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Umat, Matrix.of_apply]
  let σ : ↥(Sq p) ≃ ↥(Sq p) := (Equiv.inv ↥(Sq p)).trans (Equiv.mulLeft (r * r'))
  have hσ : ∀ q, σ q = r * r' * q⁻¹ := fun q => rfl
  calc ∑ q, uent r q * uent r' q = ∑ q, uent r (σ q) * uent r' (σ q) :=
        (Equiv.sum_comp σ (fun q => uent r q * uent r' q)).symm
  _ = ∑ q, uent q r * uent q r' := by
      apply Finset.sum_congr rfl
      intro q _
      rw [hσ, uent_shift r r' q, uent_shift' r r' q, _root_.mul_comm]

set_option maxHeartbeats 1000000 in
private lemma part1 (hp3 : p % 4 = 3) :
    (Matrix.of fun i j : Fin ((p-1)/2) =>
      jacobiSym ((((i.1+1 : ℕ) : ℤ)) * (((i.1+1 : ℕ) : ℤ))
        - ((((p-1)/2).factorial : ℕ) : ℤ) * (((j.1+1 : ℕ) : ℤ))) p).det = 0 := by
  have hodd : p % 2 = 1 := by omega
  have h2p := hp.out.two_le
  set eR : Fin ((p-1)/2) ≃ ↥(Sq p) := Equiv.ofBijective _ (eR_bijective hodd) with heR
  set eC : Fin ((p-1)/2) ≃ ↥(Sq p) := Equiv.ofBijective _ (eC_bijective hodd hp3) with heC
  have heRval : ∀ i, cv (eR i) = ((i.1 + 1 : ℕ) : ZMod p) * ((i.1 + 1 : ℕ) : ZMod p) := by
    intro i
    show (((u1 p i ^ 2 : (ZMod p)ˣ)) : ZMod p) = _
    rw [Units.val_pow_eq_pow_val, u1_val, sq]
  set wv : ↥(Sq p) → ZMod p := fun q => ((Cu p * u1 p (eC.symm q) : (ZMod p)ˣ) : ZMod p) with hwv
  set η : ↥(Sq p) → ℤ := fun q => quadraticChar (ZMod p) (wv q) with hη
  have hwv0 : ∀ q, wv q ≠ 0 := fun q => Units.ne_zero _
  have hη2 : ∀ q, η q * η q = 1 := by
    intro q
    rcases quadraticChar_dichotomy (hwv0 q) with h | h <;> rw [hη] <;> simp only <;> rw [h] <;> norm_num
  have hcvq : ∀ q, cv q = ((η q : ℤ) : ZMod p) * wv q := by
    intro q
    have hval : cv (eC (eC.symm q)) = ((quadraticChar (ZMod p)
        (((Cu p * u1 p (eC.symm q) : (ZMod p)ˣ)) : ZMod p) : ℤ) : ZMod p) *
        (((Cu p * u1 p (eC.symm q) : (ZMod p)ˣ)) : ZMod p) := by
      show ((sqrep p (Cu p * u1 p (eC.symm q)) : (ZMod p)ˣ) : ZMod p) = _
      exact sqrep_val hp3 _
    rw [Equiv.apply_symm_apply] at hval
    exact hval
  have hwvq : ∀ q, wv q = ((η q : ℤ) : ZMod p) * cv q := by
    intro q
    rw [hcvq q, ← _root_.mul_assoc, ← Int.cast_mul, hη2 q]
    simp
  -- the matrices over ℚ
  set A : Matrix ↥(Sq p) ↥(Sq p) ℚ :=
    Matrix.of fun r q => ((quadraticChar (ZMod p) (cv r - cv q) : ℤ) : ℚ) with hA
  set B : Matrix ↥(Sq p) ↥(Sq p) ℚ :=
    Matrix.of fun r q => ((quadraticChar (ZMod p) (cv r + cv q) : ℤ) : ℚ) with hB
  set D : Matrix ↥(Sq p) ↥(Sq p) ℚ := Matrix.diagonal (fun q => ((η q : ℤ) : ℚ)) with hD
  set N : Matrix ↥(Sq p) ↥(Sq p) ℚ :=
    Matrix.of fun r q => ((quadraticChar (ZMod p) (cv r - wv q) : ℤ) : ℚ) with hN
  have hU : Umat p = A + B := by
    ext r q
    simp only [Umat, Matrix.of_apply, uent, Matrix.add_apply, hA, hB]
    push_cast
    ring
  have hAB : A - B = -(Umat p)ᵀ := by
    ext r q
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.transpose_apply, Umat, Matrix.of_apply,
      uent, hA, hB]
    have hswap : cv q - cv r = -(cv r - cv q) := by ring
    rw [hswap, chi_neg hp3, _root_.add_comm (cv q) (cv r)]
    push_cast
    ring
  have h2N : (2 : ℚ) • N = Umat p - (Umat p)ᵀ * D := by
    have hstep : (A + B) + (A - B) * D = Umat p - (Umat p)ᵀ * D := by
      rw [hAB, ← hU, Matrix.neg_mul, ← sub_eq_add_neg]
    rw [← hstep]
    ext r q
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, hN, hA, hB, hD,
      Matrix.of_apply, Matrix.mul_diagonal, smul_eq_mul]
    rcases quadraticChar_dichotomy (hwv0 q) with hcase | hcase
    · have hq1 : η q = 1 := by rw [hη]; simp only; exact hcase
      have hwvcv : wv q = cv q := by rw [hwvq q, hq1]; push_cast; ring
      rw [hwvcv, hq1]
      push_cast
      ring
    · have hq1 : η q = -1 := by rw [hη]; simp only; exact hcase
      have hwvcv : wv q = -cv q := by rw [hwvq q, hq1]; push_cast; ring
      have hplus : cv r - wv q = cv r + cv q := by rw [hwvcv]; ring
      rw [hplus, hq1]
      push_cast
      ring
  -- properties of D
  have hDt : Dᵀ = D := by rw [hD, Matrix.diagonal_transpose]
  have hDD : D * D = 1 := by
    rw [hD, Matrix.diagonal_mul_diagonal]
    have hfun : (fun q => ((η q : ℤ) : ℚ) * ((η q : ℤ) : ℚ)) = fun _ => (1:ℚ) := by
      funext q
      rw [← Int.cast_mul, hη2 q, Int.cast_one]
    rw [hfun, Matrix.diagonal_one]
  have hDdet : D.det = 1 := by
    rw [hD, Matrix.det_diagonal]
    have hcast : ∏ q, ((η q : ℤ) : ℚ) = ((∏ q, η q : ℤ) : ℚ) := by
      push_cast
      rfl
    rw [hcast]
    have hprod : ∏ q, η q = 1 := by
      have hcomp : ∏ q, η q = ∏ j, η (eC j) := (Equiv.prod_comp eC (fun q => η q)).symm
      have hηj : ∀ j, η (eC j) = quadraticChar (ZMod p)
          ((((p-1)/2).factorial : ℕ) * ((j.1+1 : ℕ) : ZMod p)) := by
        intro j
        rw [hη]
        simp only
        rw [hwv]
        simp only
        rw [Equiv.symm_apply_apply, Units.val_mul, Cu_val, u1_val]
      rw [hcomp]
      rw [Finset.prod_congr rfl (fun j _ => hηj j)]
      rw [← map_prod]
      have hprodval : (∏ j : Fin ((p-1)/2), ((((p-1)/2).factorial : ℕ) : ZMod p) * ((j.1+1 : ℕ) : ZMod p))
          = ((((p-1)/2).factorial : ℕ) : ZMod p) ^ ((p-1)/2 + 1) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        have : (∏ j : Fin ((p-1)/2), ((j.1+1 : ℕ) : ZMod p)) = ((((p-1)/2).factorial : ℕ) : ZMod p) := by
          rw [← Nat.cast_prod]
          congr 1
          rw [Fin.prod_univ_eq_prod_range (fun k => k + 1) ((p-1)/2)]
          exact Finset.prod_range_add_one_eq_factorial _
        rw [this, _root_.pow_succ]
      rw [hprodval, map_pow]
      rcases quadraticChar_dichotomy (factorial_cast_ne_zero (p := p)) with hone | hneg
      · rw [hone, _root_.one_pow]
      · rw [hneg]
        apply Even.neg_one_pow
        rw [Nat.even_add_one, Nat.not_even_iff_odd, Nat.odd_iff]
        omega
    rw [hprod, Int.cast_one]
  -- apply the main determinant lemma
  have hcard : Fintype.card ↥(Sq p) = (p-1)/2 := by
    have hc := Fintype.card_of_bijective (eR_bijective (p := p) hodd)
    rw [Fintype.card_fin] at hc
    exact hc.symm
  have hoddcard : Odd (Fintype.card ↥(Sq p)) := by
    rw [hcard, Nat.odd_iff]
    omega
  have hdetN : N.det = 0 := by
    have h0 : (Umat p - (Umat p)ᵀ * D).det = 0 :=
      det_normal_sub_transpose_mul_symm hoddcard (Umat p) D Umat_normal hDt hDD hDdet
    rw [← h2N, Matrix.det_smul] at h0
    have h2c : (2:ℚ) ^ Fintype.card ↥(Sq p) ≠ 0 := pow_ne_zero _ two_ne_zero
    exact (mul_eq_zero.mp h0).resolve_left h2c
  -- identify the original matrix with a submatrix of N
  have hMq : (Matrix.of fun i j : Fin ((p-1)/2) =>
      ((legendreSym p ((((i.1+1 : ℕ) : ℤ)) * (((i.1+1 : ℕ) : ℤ))
        - ((((p-1)/2).factorial : ℕ) : ℤ) * (((j.1+1 : ℕ) : ℤ))) : ℤ) : ℚ))
      = N.submatrix eR eC := by
    ext i j
    rw [Matrix.submatrix_apply, hN]
    simp only [Matrix.of_apply]
    congr 1
    show quadraticChar (ZMod p) _ = quadraticChar (ZMod p) (cv (eR i) - wv (eC j))
    congr 1
    have hwvj : wv (eC j) = ((((p-1)/2).factorial : ℕ) : ZMod p) * ((j.1+1 : ℕ) : ZMod p) := by
      rw [hwv]
      simp only
      rw [Equiv.symm_apply_apply, Units.val_mul, Cu_val, u1_val]
    rw [heRval i, hwvj]
    push_cast
    ring
  have hdetq : (Matrix.of fun i j : Fin ((p-1)/2) =>
      ((legendreSym p ((((i.1+1 : ℕ) : ℤ)) * (((i.1+1 : ℕ) : ℤ))
        - ((((p-1)/2).factorial : ℕ) : ℤ) * (((j.1+1 : ℕ) : ℤ))) : ℤ) : ℚ)).det = 0 := by
    rw [hMq]
    exact det_submatrix_eq_zero N eR eC hdetN
  -- back to ℤ
  have hfinal := RingHom.map_det (Int.castRingHom ℚ) (Matrix.of fun i j : Fin ((p-1)/2) =>
      jacobiSym ((((i.1+1 : ℕ) : ℤ)) * (((i.1+1 : ℕ) : ℤ))
        - ((((p-1)/2).factorial : ℕ) : ℤ) * (((j.1+1 : ℕ) : ℤ))) p)
  have hmm : (Int.castRingHom ℚ).mapMatrix (Matrix.of fun i j : Fin ((p-1)/2) =>
      jacobiSym ((((i.1+1 : ℕ) : ℤ)) * (((i.1+1 : ℕ) : ℤ))
        - ((((p-1)/2).factorial : ℕ) : ℤ) * (((j.1+1 : ℕ) : ℤ))) p)
      = (Matrix.of fun i j : Fin ((p-1)/2) =>
      ((legendreSym p ((((i.1+1 : ℕ) : ℤ)) * (((i.1+1 : ℕ) : ℤ))
        - ((((p-1)/2).factorial : ℕ) : ℤ) * (((j.1+1 : ℕ) : ℤ))) : ℤ) : ℚ)) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    simp only [Matrix.of_apply]
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    rfl
  rw [hmm, hdetq] at hfinal
  have : (((Matrix.of fun i j : Fin ((p-1)/2) =>
      jacobiSym ((((i.1+1 : ℕ) : ℤ)) * (((i.1+1 : ℕ) : ℤ))
        - ((((p-1)/2).factorial : ℕ) : ℤ) * (((j.1+1 : ℕ) : ℤ))) p).det : ℤ) : ℚ) = 0 := hfinal
  exact_mod_cast this

/-! ## Part 2 : the case `p % 4 = 1` -/

private lemma factorial_half_sq (hodd : p % 2 = 1) :
    ((((p-1)/2).factorial : ℕ) : ZMod p) ^ 2 * (-1 : ZMod p) ^ ((p-1)/2) = -1 := by
  have h2p := hp.out.two_le
  have hw : (((p-1).factorial : ℕ) : ZMod p) = -1 := ZMod.wilsons_lemma p
  have hsplit : (∏ k ∈ Finset.Ico 1 ((p-1)/2 + 1), (k : ZMod p)) *
      (∏ k ∈ Finset.Ico ((p-1)/2 + 1) p, (k : ZMod p)) = ∏ k ∈ Finset.Ico 1 p, (k : ZMod p) :=
    Finset.prod_Ico_consecutive _ (by omega) (by omega)
  have h1 : (∏ k ∈ Finset.Ico 1 ((p-1)/2 + 1), (k : ZMod p)) = ((((p-1)/2).factorial : ℕ) : ZMod p) := by
    rw [← Nat.cast_prod]
    congr 1
    exact Finset.prod_Ico_id_eq_factorial _
  have hfull : (∏ k ∈ Finset.Ico 1 p, (k : ZMod p)) = -1 := by
    rw [← Nat.cast_prod]
    have hico : Finset.Ico 1 p = Finset.Ico 1 ((p-1) + 1) := by congr 1; omega
    rw [hico, Finset.prod_Ico_id_eq_factorial]
    exact hw
  have h2 : (∏ k ∈ Finset.Ico ((p-1)/2 + 1) p, (k : ZMod p)) =
      ∏ k ∈ Finset.Ico 1 ((p-1)/2 + 1), (-(k : ZMod p)) := by
    apply Finset.prod_nbij' (fun k => p - k) (fun k => p - k)
    · intro k hk
      simp only [Finset.mem_Ico] at hk ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      have : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
        push_cast [Nat.cast_sub (by omega : k ≤ p)]
        simp
      rw [this, neg_neg]
  have h3 : (∏ k ∈ Finset.Ico 1 ((p-1)/2 + 1), (-(k : ZMod p))) =
      (-1 : ZMod p) ^ ((p-1)/2) * ((((p-1)/2).factorial : ℕ) : ZMod p) := by
    have : ∀ k ∈ Finset.Ico 1 ((p-1)/2 + 1), (-(k : ZMod p)) = (-1) * (k : ZMod p) :=
      fun k _ => by ring
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico]
    rw [h1]
    have hexp : (p-1)/2 + 1 - 1 = (p-1)/2 := by omega
    rw [hexp]
  rw [h1, h2, h3, hfull] at hsplit
  linear_combination hsplit

/-- Lagrange-interpolation coefficient extraction: for `f` of degree `< m`,
`∑ j, f(t j) / ∏_{k ≠ j} (t j - t k)` equals the coefficient of `X^(m-1)` in `f`. -/
private lemma sum_eval_div_prod {K : Type*} [Field K] {m : ℕ} (t : Fin m → K)
    (ht : Function.Injective t) (f : Polynomial K) (hdeg : f.degree < (m : ℕ)) :
    ∑ j, f.eval (t j) * (∏ k ∈ Finset.univ.erase j, (t j - t k))⁻¹ = f.coeff (m - 1) := by
  have hinj : Set.InjOn t ↑(Finset.univ : Finset (Fin m)) := Function.Injective.injOn ht
  have hcard : (Finset.univ : Finset (Fin m)).card = m := by simp
  have hf := Lagrange.eq_interpolate hinj (by rw [hcard]; exact hdeg)
  have hcoeff := congrArg (fun g => Polynomial.coeff g (m-1)) hf
  simp only [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul] at hcoeff
  rw [hcoeff]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hnd : (Lagrange.basis Finset.univ t j).natDegree = m - 1 := by
    rw [Lagrange.natDegree_basis hinj (Finset.mem_univ j), hcard]
  rw [← hnd, Polynomial.coeff_natDegree, Lagrange.leadingCoeff_basis hinj (Finset.mem_univ j)]

set_option maxHeartbeats 1600000 in
private lemma part2 (hp1 : p % 4 = 1) :
    (Matrix.of fun i j : Fin ((p-1)/2) =>
      jacobiSym ((((i.1+1 : ℕ) : ℤ)) * (((i.1+1 : ℕ) : ℤ))
        - ((((p-1)/2).factorial : ℕ) : ℤ) * (((j.1+1 : ℕ) : ℤ))) p).det ≠ 0 := by
  have h2p := hp.out.two_le
  have hp5 : 5 ≤ p := by omega
  intro hdet0
  set m : ℕ := (p-1)/2 with hm
  have hm2 : m % 2 = 0 := by omega
  have hm1 : 1 ≤ m := by omega
  have hmlt : m < p := by omega
  have h2m : 2 * m = p - 1 := by omega
  haveI : NeZero m := ⟨by omega⟩
  set C : ZMod p := ((m.factorial : ℕ) : ZMod p) with hCdef
  have hCne : C ≠ 0 := factorial_cast_ne_zero
  set a : Fin m → ZMod p := fun i => ((i.1 + 1 : ℕ) : ZMod p) with ha
  have ha_ne : ∀ i, a i ≠ 0 := by
    intro i
    have hi := i.2
    simp only [ha]
    exact natCast_ne_zero_of_lt (by omega) (by omega)
  have ha_inj : Function.Injective a := by
    intro i j hij
    simp only [ha] at hij
    have hi := i.2; have hj := j.2
    have := natCast_inj_of_lt (by omega : i.1 + 1 < p) (by omega : j.1 + 1 < p) hij
    exact Fin.ext (by omega)
  set x : Fin m → ZMod p := fun i => a i * a i with hx
  have hx_inj : Function.Injective x := by
    intro i j hij
    simp only [hx] at hij
    have hsumne : a i + a j ≠ 0 := by
      have hi := i.2; have hj := j.2
      have hrw : a i + a j = ((i.1 + j.1 + 2 : ℕ) : ZMod p) := by
        simp only [ha]; push_cast; ring
      rw [hrw]
      exact natCast_ne_zero_of_lt (by omega) (by omega)
    have hfac : (a i - a j) * (a i + a j) = 0 := by linear_combination hij
    rcases mul_eq_zero.mp hfac with h | h
    · exact ha_inj (by linear_combination h)
    · exact absurd h hsumne
  have hx1 : ∀ i, x i ^ m = 1 := by
    intro i
    have hh : x i ^ m = a i ^ (p - 1) := by
      simp only [hx]
      rw [← sq, ← _root_.pow_mul, h2m]
    rw [hh]
    exact ZMod.pow_card_sub_one_eq_one (ha_ne i)
  set t : Fin m → ZMod p := fun j => -(C * a j) with ht
  have ht_ne : ∀ j, t j ≠ 0 := by
    intro j
    simp only [ht, neg_ne_zero]
    exact mul_ne_zero hCne (ha_ne j)
  have ht_inj : Function.Injective t := by
    intro i j hij
    simp only [ht, neg_inj] at hij
    exact ha_inj (mul_left_cancel₀ hCne hij)
  -- cast the determinant hypothesis to `ZMod p`
  have hcast := RingHom.map_det (Int.castRingHom (ZMod p))
    (Matrix.of fun i j : Fin m =>
      jacobiSym ((((i.1+1 : ℕ) : ℤ)) * (((i.1+1 : ℕ) : ℤ))
        - ((m.factorial : ℕ) : ℤ) * (((j.1+1 : ℕ) : ℤ))) p)
  rw [hdet0, map_zero] at hcast
  have hMbar : ((Int.castRingHom (ZMod p)).mapMatrix (Matrix.of fun i j : Fin m =>
      jacobiSym ((((i.1+1 : ℕ) : ℤ)) * (((i.1+1 : ℕ) : ℤ))
        - ((m.factorial : ℕ) : ℤ) * (((j.1+1 : ℕ) : ℤ))) p))
      = Matrix.of (fun i j : Fin m => (x i + t j) ^ m) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Int.coe_castRingHom]
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    rw [legendreSym.eq_pow]
    rw [show p / 2 = m from by omega]
    congr 1
    simp only [hx, ht, ha, hCdef]
    push_cast
    ring
  rw [hMbar] at hcast
  -- the binomial-expansion factorisation
  set W : Matrix (Fin m) (Fin m) (ZMod p) :=
    Matrix.of (fun k j : Fin m => ((m.choose k.1 : ℕ) : ZMod p) * t j ^ (m - k.1)) with hW
  have hsplit : Matrix.of (fun i j : Fin m => (x i + t j) ^ m)
      = Matrix.vandermonde x * W + Matrix.of (fun _ _ : Fin m => (1 : ZMod p)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.vandermonde_apply, hW]
    rw [_root_.add_pow, Finset.sum_range_succ, Nat.sub_self, _root_.pow_zero, Nat.choose_self, Nat.cast_one,
      _root_.mul_one, _root_.mul_one, hx1 i]
    congr 1
    rw [Fin.sum_univ_eq_sum_range
      (fun k => x i ^ k * (((m.choose k : ℕ) : ZMod p) * t j ^ (m - k))) m]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- the explicit inverse-image vector
  set P : Fin m → ZMod p := fun j => ∏ k ∈ Finset.univ.erase j, (t j - t k) with hP
  set z : Fin m → ZMod p := fun j => (t j * P j)⁻¹ with hz
  have hLag : ∀ d : ℕ, d < m →
      (∑ j, t j ^ d * (∏ k ∈ Finset.univ.erase j, (t j - t k))⁻¹)
        = if d = m - 1 then 1 else 0 := by
    intro d hd
    have hdeg : (Polynomial.X ^ d : Polynomial (ZMod p)).degree < (m : ℕ) := by
      rw [Polynomial.degree_X_pow]
      exact_mod_cast hd
    have hres := sum_eval_div_prod t ht_inj (Polynomial.X ^ d) hdeg
    simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.coeff_X_pow] at hres
    rw [hres]
    by_cases hdm : d = m - 1
    · rw [if_pos hdm, if_pos hdm.symm]
    · rw [if_neg hdm, if_neg fun hh => hdm hh.symm]
  have hWz : W *ᵥ z = fun k : Fin m => if k = (0 : Fin m) then 1 else 0 := by
    funext k
    have hk2 := k.2
    have hterm : ∀ j, W k j * z j
        = ((m.choose k.1 : ℕ) : ZMod p) *
          (t j ^ (m - 1 - k.1) * (∏ k' ∈ Finset.univ.erase j, (t j - t k'))⁻¹) := by
      intro j
      simp only [hW, hz, hP, Matrix.of_apply]
      rw [_root_.mul_inv]
      have hpow : t j ^ (m - k.1) = t j * t j ^ (m - 1 - k.1) := by
        rw [← _root_.pow_succ']
        congr 1
        omega
      rw [hpow]
      have hinv : t j * (t j)⁻¹ = 1 := mul_inv_cancel₀ (ht_ne j)
      linear_combination (((m.choose k.1 : ℕ) : ZMod p) *
        (t j ^ (m - 1 - k.1) * (∏ k' ∈ Finset.univ.erase j, (t j - t k'))⁻¹)) * hinv
    show (∑ j, W k j * z j) = _
    rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum, hLag (m - 1 - k.1) (by omega)]
    by_cases hk0 : k = (0 : Fin m)
    · subst hk0
      simp
    · have hkne : k.1 ≠ 0 := fun hh => hk0 (Fin.ext hh)
      rw [if_neg (show ¬ (m - 1 - k.1 = m - 1) by omega), MulZeroClass.mul_zero, if_neg hk0]
  have hVWz : (Matrix.vandermonde x * W) *ᵥ z = fun _ : Fin m => (1 : ZMod p) := by
    rw [← Matrix.mulVec_mulVec, hWz]
    funext i
    show (∑ k, Matrix.vandermonde x i k * (if k = (0 : Fin m) then 1 else 0)) = 1
    rw [Finset.sum_eq_single (0 : Fin m)]
    · simp [Matrix.vandermonde_apply]
    · intro b _ hb
      rw [if_neg hb, MulZeroClass.mul_zero]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  have hVWz' : ∀ i, (∑ k, (Matrix.vandermonde x * W) i k * z k) = 1 := by
    intro i
    exact congrFun hVWz i
  set B : Matrix (Fin m) (Fin m) (ZMod p) := 1 + Matrix.vecMulVec z (fun _ => (1 : ZMod p)) with hB
  have hfact : Matrix.vandermonde x * W + Matrix.of (fun _ _ : Fin m => (1 : ZMod p))
      = (Matrix.vandermonde x * W) * B := by
    rw [hB, Matrix.mul_add, Matrix.mul_one]
    congr 1
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Matrix.vecMulVec_apply, _root_.mul_one]
    exact (hVWz' i).symm
  have hdetB : B.det = 1 + ∑ j, z j := by
    rw [hB, Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
    congr 1
    simp [dotProduct]
  have hdetVx : (Matrix.vandermonde x).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hx_inj
  have hchoose_ne : ∀ k : Fin m, ((m.choose k.1 : ℕ) : ZMod p) ≠ 0 := by
    intro k hzero
    have hle : k.1 ≤ m := le_of_lt k.2
    have hfacid : ((m.choose k.1 : ℕ) : ZMod p) * ((k.1.factorial : ℕ) : ZMod p)
        * (((m - k.1).factorial : ℕ) : ZMod p) = ((m.factorial : ℕ) : ZMod p) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul]
      congr 1
      exact Nat.choose_mul_factorial_mul_factorial hle
    rw [hzero, MulZeroClass.zero_mul, MulZeroClass.zero_mul] at hfacid
    rw [← hCdef] at hfacid
    exact hCne hfacid.symm
  have hdetW : W.det ≠ 0 := by
    have hWeq : W = Matrix.diagonal (fun k : Fin m => ((m.choose k.1 : ℕ) : ZMod p)) *
        (((Matrix.vandermonde t)ᵀ.submatrix (⇑(Fin.revPerm : Equiv.Perm (Fin m))) id) *
          Matrix.diagonal t) := by
      ext k j
      have hk2 := k.2
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
      simp only [hW, Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
        Matrix.vandermonde_apply, id_eq, Fin.revPerm_apply, Fin.val_rev]
      rw [show m - k.1 = m - (k.1 + 1) + 1 from by omega, _root_.pow_succ]
    rw [hWeq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
    refine mul_ne_zero ?_ (mul_ne_zero ?_ ?_)
    · exact Finset.prod_ne_zero_iff.mpr fun k _ => hchoose_ne k
    · rw [Matrix.det_permute (Fin.revPerm) ((Matrix.vandermonde t)ᵀ)]
      apply mul_ne_zero
      · rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m))) with hs | hs <;>
          rw [hs] <;> norm_num
      · rw [Matrix.det_transpose]
        exact Matrix.det_vandermonde_ne_zero_iff.mpr ht_inj
    · exact Finset.prod_ne_zero_iff.mpr fun j _ => ht_ne j
  -- computing `∑ z` via the auxiliary polynomial `Q`
  set Q : Polynomial (ZMod p) := ∏ j : Fin m, (Polynomial.X - Polynomial.C (t j)) with hQdef
  have hQmonic : Q.Monic := by
    rw [hQdef]
    exact monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C (t j)
  have hQdeg : Q.natDegree = m := by
    rw [hQdef, Polynomial.natDegree_prod _ _ fun j _ => Polynomial.X_sub_C_ne_zero (t j)]
    simp [Polynomial.natDegree_X_sub_C]
  set g : Polynomial (ZMod p) := Q /ₘ Polynomial.X with hgdef
  have hgdeg : g.natDegree = m - 1 := by
    rw [hgdef, Polynomial.natDegree_divByMonic Q Polynomial.monic_X, hQdeg, Polynomial.natDegree_X]
  have hQsplit : Polynomial.C (Q.eval 0) + Polynomial.X * g = Q := by
    rw [hgdef, ← Polynomial.modByMonic_X Q]
    exact Polynomial.modByMonic_add_div Q Polynomial.monic_X
  have hgcoeff : g.coeff (m - 1) = 1 := by
    have h1 : Q.coeff m = 1 := by
      have hh := hQmonic.coeff_natDegree
      rwa [hQdeg] at hh
    have h2 := congrArg (fun q => Polynomial.coeff q m) hQsplit
    simp only [Polynomial.coeff_add] at h2
    rw [Polynomial.coeff_C, if_neg (show ¬ m = 0 by omega), _root_.zero_add, h1] at h2
    rw [show m = (m - 1) + 1 from by omega, Polynomial.coeff_X_mul] at h2
    exact h2
  have hQeval0 : ∀ j, Q.eval (t j) = 0 := by
    intro j
    rw [hQdef, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp
  have hgeval : ∀ j, g.eval (t j) = -(Q.eval 0) * (t j)⁻¹ := by
    intro j
    have h0 := congrArg (Polynomial.eval (t j)) hQsplit
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] at h0
    rw [hQeval0 j] at h0
    have hinv : t j * (t j)⁻¹ = 1 := mul_inv_cancel₀ (ht_ne j)
    apply mul_left_cancel₀ (ht_ne j)
    linear_combination h0 + Q.eval 0 * hinv
  have hgdegree : g.degree < (m : ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    rw [hgdeg]
    exact_mod_cast (show m - 1 < m by omega)
  have hLagg := sum_eval_div_prod t ht_inj g hgdegree
  rw [hgcoeff] at hLagg
  have hSum : Q.eval 0 * (∑ j, z j) = -1 := by
    have hstep : (∑ j, g.eval (t j) * (∏ k ∈ Finset.univ.erase j, (t j - t k))⁻¹)
        = ∑ j, -(Q.eval 0) * z j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hgeval j]
      simp only [hz, hP]
      rw [_root_.mul_inv]
      ring
    rw [hstep, ← Finset.mul_sum] at hLagg
    linear_combination -hLagg
  have hQ0 : Q.eval 0 = C ^ (m + 1) := by
    rw [hQdef, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
    have h1 : ∀ j : Fin m, -(t j) = C * a j := by
      intro j
      simp only [ht, neg_neg]
    rw [Finset.prod_congr rfl fun j _ => h1 j, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    have h2 : (∏ j : Fin m, a j) = C := by
      simp only [ha, hCdef]
      rw [Fin.prod_univ_eq_prod_range (fun k => ((k + 1 : ℕ) : ZMod p)) m, ← Nat.cast_prod]
      congr 1
      exact Finset.prod_range_add_one_eq_factorial m
    rw [h2, _root_.pow_succ]
  have hC2 : C ^ 2 = -1 := by
    have hfs := factorial_half_sq (p := p) (by omega : p % 2 = 1)
    rw [← hm, ← hCdef] at hfs
    rwa [Even.neg_one_pow (Nat.even_iff.mpr hm2), _root_.mul_one] at hfs
  have hzsum : (1 : ZMod p) + ∑ j, z j ≠ 0 := by
    intro h0
    have hS : (∑ j, z j) = -1 := by linear_combination h0
    rw [hS, hQ0] at hSum
    have hQ1 : C ^ (m + 1) = 1 := by linear_combination -hSum
    have hsq : ((-1 : ZMod p)) ^ (m + 1) = 1 := by
      calc ((-1 : ZMod p)) ^ (m+1) = (C ^ 2) ^ (m+1) := by rw [hC2]
      _ = (C ^ (m+1)) ^ 2 := by rw [← _root_.pow_mul, ← _root_.pow_mul, Nat.mul_comm]
      _ = 1 := by rw [hQ1, _root_.one_pow]
    rw [Odd.neg_one_pow (Nat.odd_iff.mpr (by omega : (m + 1) % 2 = 1))] at hsq
    have h2z : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination -hsq
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2z
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hdetM : (Matrix.of fun i j : Fin m => (x i + t j) ^ m).det
      = (Matrix.vandermonde x).det * W.det * (1 + ∑ j, z j) := by
    rw [hsplit, hfact, Matrix.det_mul, Matrix.det_mul, hdetB]
  rw [hdetM] at hcast
  exact (mul_ne_zero (mul_ne_zero hdetVx hdetW) hzsum) hcast.symm

private lemma key (hodd : p % 2 = 1) :
    ((Matrix.of fun i j : Fin ((p-1)/2) =>
      jacobiSym ((((i.1+1 : ℕ) : ℤ)) * (((i.1+1 : ℕ) : ℤ))
        - ((((p-1)/2).factorial : ℕ) : ℤ) * (((j.1+1 : ℕ) : ℤ))) p).det = 0)
      ↔ p % 4 = 3 := by
  constructor
  · intro h
    by_contra h3
    have h2p := hp.out.two_le
    have h1 : p % 4 = 1 := by omega
    exact part2 h1 h
  · exact part1

end OEIS226163


/--
Conjecture: a(n) = 0 if and only if p_n ≡ 3 (mod 4).
-/
theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  have hpmem : (Nat.nth Nat.Prime (n-1)).Prime :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n-1)
  haveI : Fact (Nat.nth Nat.Prime (n-1)).Prime := ⟨hpmem⟩
  have hgt : 2 < Nat.nth Nat.Prime (n-1) := by
    have h0 : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime (n-1) :=
      (Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr (by omega)
    have h2 : 2 ≤ Nat.nth Nat.Prime 0 :=
      (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime 0).two_le
    omega
  have hodd : Nat.nth Nat.Prime (n-1) % 2 = 1 :=
    Nat.odd_iff.mp (hpmem.odd_of_ne_two (by omega))
  rw [show A226163 n = (Matrix.of fun i j : Fin ((Nat.nth Nat.Prime (n-1) - 1)/2) =>
      jacobiSym ((((i.1+1 : ℕ) : ℤ)) * (((i.1+1 : ℕ) : ℤ))
        - ((((Nat.nth Nat.Prime (n-1) - 1)/2).factorial : ℕ) : ℤ) * (((j.1+1 : ℕ) : ℤ)))
      (Nat.nth Nat.Prime (n-1))).det from by
    unfold A226163
    rw [dif_neg (by omega : ¬ n < 2)]
    rfl]
  exact OEIS226163.key hodd
