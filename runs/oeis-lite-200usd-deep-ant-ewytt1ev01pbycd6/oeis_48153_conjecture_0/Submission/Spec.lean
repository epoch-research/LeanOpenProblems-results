import FormalConjectures.Util.ProblemImports

/- ================= inlined from GaussGen.lean ================= -/
section

set_option maxHeartbeats 1000000
open Complex Finset AddChar Polynomial
open scoped Matrix

noncomputable section

namespace GaussGen

/-- The primitive `m`-th root of unity `ω = exp(2πi/m)`. -/
def ω (m : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)

variable (m : ℕ) [NeZero m]

theorem hm0 : m ≠ 0 := NeZero.ne m

theorem hmpos : 0 < m := Nat.pos_of_ne_zero (hm0 m)

theorem omega_primitiveRoot : IsPrimitiveRoot (ω m) m :=
  Complex.isPrimitiveRoot_exp m (hm0 m)

theorem omega_pow : (ω m) ^ m = 1 := (omega_primitiveRoot m).pow_eq_one

/-- The additive character `a ↦ ω^a` on `ZMod m`. -/
def psi : AddChar (ZMod m) ℂ := AddChar.zmodChar m (omega_pow m)

theorem psi_apply_natCast (k : ℕ) : psi m (k : ZMod m) = (ω m) ^ k :=
  AddChar.zmodChar_apply' (omega_pow m) k

/-- **Root-of-unity orthogonality.** -/
theorem orthogonality (n : ℕ) :
    ∑ k ∈ range m, (ω m) ^ (k * n) = if m ∣ n then (m : ℂ) else 0 := by
  set x : ℂ := (ω m) ^ n with hxdef
  have hsum : ∑ k ∈ range m, (ω m) ^ (k * n) = ∑ k ∈ range m, x ^ k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hxdef, ← pow_mul, Nat.mul_comm]
  rw [hsum]
  by_cases h : m ∣ n
  · have hx1 : x = 1 := by
      rw [hxdef, (omega_primitiveRoot m).pow_eq_one_iff_dvd n]; exact h
    simp [hx1, h, Finset.card_range]
  · have hxne : x ≠ 1 := by
      rw [hxdef]
      intro hc
      exact h (((omega_primitiveRoot m).pow_eq_one_iff_dvd n).mp hc)
    have hxp : x ^ m = 1 := by
      rw [hxdef, ← pow_mul, Nat.mul_comm, pow_mul, omega_pow, one_pow]
    rw [geom_sum_eq hxne m, hxp, sub_self, zero_div, if_neg h]

/-- Schur's matrix `A i j = ω^(i·j)`. -/
def A : Matrix (Fin m) (Fin m) ℂ := fun i j => (ω m) ^ (i.val * j.val)

/-- The trace of `A` is the exponential Gauss sum. -/
theorem trace_A : (A m).trace = ∑ k ∈ range m, (ω m) ^ (k ^ 2) := by
  rw [Matrix.trace]
  simp only [Matrix.diag, A]
  rw [← Fin.sum_univ_eq_sum_range (fun k => (ω m) ^ (k ^ 2)) m]
  apply Finset.sum_congr rfl
  intro i _
  rw [sq]

/-- The reversal permutation matrix `R i j = [i + j ≡ 0 mod m]`. -/
def R : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if m ∣ (i.val + j.val) then 1 else 0

/-- **Key identity `A² = m • R`.** -/
theorem A_sq : (A m) * (A m) = (m : ℂ) • (R m) := by
  ext i j
  rw [Matrix.mul_apply]
  have hrw : ∀ k : Fin m, (A m) i k * (A m) k j = (ω m) ^ (k.val * (i.val + j.val)) := by
    intro k
    simp only [A]
    rw [← pow_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun k _ => hrw k)]
  rw [Fin.sum_univ_eq_sum_range (fun k => (ω m) ^ (k * (i.val + j.val))) m]
  rw [orthogonality m (i.val + j.val)]
  simp only [Matrix.smul_apply, R, smul_eq_mul]
  by_cases h : m ∣ (i.val + j.val) <;> simp [h]

/-! ### structural lemmas -/

/-- `sqp m = √m` as a complex number. -/
def sqp : ℂ := (Real.sqrt m : ℂ)

theorem sqp_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast (hmpos m))

theorem sqp_ne : sqp m ≠ 0 := by
  simp only [sqp, ne_eq, Complex.ofReal_eq_zero]
  exact (sqp_pos m).ne'

theorem sqp_sq : (sqp m) ^ 2 = (m : ℂ) := by
  simp only [sqp]
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by exact_mod_cast Nat.zero_le m)]
  simp

theorem sqp_eq : sqp m = ((Real.sqrt m : ℝ) : ℂ) := rfl

/-- Divisibility of `i+k` by `m` expressed in `ZMod m`. -/
theorem R_dvd_iff (i k : Fin m) :
    m ∣ (i.val + k.val) ↔ ((i.val : ZMod m) + (k.val : ZMod m) = 0) := by
  rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]

/-- For each `i` there is a unique `k` with `m ∣ i + k`. -/
theorem R_unique (i : Fin m) : ∃! k : Fin m, ((i.val : ZMod m) + (k.val : ZMod m) = 0) := by
  refine ⟨⟨(-(i.val : ZMod m)).val, (-(i.val : ZMod m)).val_lt⟩, ?_, ?_⟩
  · simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
    ring
  · intro k hk
    apply Fin.ext
    have hk' : (k.val : ZMod m) = -(i.val : ZMod m) := by linear_combination hk
    have : (k.val : ZMod m) = (((-(i.val : ZMod m)).val : ℕ) : ZMod m) := by
      rw [ZMod.natCast_val, ZMod.cast_id', id_eq]; exact hk'
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mp this
    simpa [Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt (-(i.val : ZMod m)).val_lt] using
      h2.eq_of_lt_of_lt k.isLt (-(i.val : ZMod m)).val_lt

/-- `R` is an involution. -/
theorem R_involutive : (R m) * (R m) = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [R, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    obtain ⟨k₀, hk₀, hk₀uniq⟩ := R_unique m i
    rw [Finset.sum_eq_single k₀]
    · rw [if_pos rfl, if_pos ((R_dvd_iff m i k₀).mpr hk₀), if_pos]
      · ring
      · rw [R_dvd_iff]; rw [add_comm]; exact hk₀
    · intro k _ hk
      have : ¬ m ∣ (i.val + k.val) := by
        rw [R_dvd_iff]; intro h; exact hk (hk₀uniq k h)
      rw [if_neg this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases h1 : m ∣ (i.val + k.val)
    · by_cases h2 : m ∣ (k.val + j.val)
      · exfalso
        rw [R_dvd_iff] at h1
        rw [R_dvd_iff, add_comm] at h2
        have hij2 : (i.val : ZMod m) = (j.val : ZMod m) := by linear_combination h1 - h2
        have := (ZMod.natCast_eq_natCast_iff _ _ _).mp hij2
        exact hij (Fin.ext (this.eq_of_lt_of_lt i.isLt j.isLt))
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

/-! ### eigenvalue structure -/

theorem A_mul_A_sq :
    (A m * A m) * (A m * A m) = (m:ℂ)^2 • (1 : Matrix (Fin m) (Fin m) ℂ) := by
  rw [A_sq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, R_involutive, sq]

/-- Every eigenvalue `x` of `A` satisfies `x⁴ = m²`. -/
theorem eigen_pow4 (x : ℂ) (hx : x ∈ (A m).charpoly.roots) : x ^ 4 = (m:ℂ)^2 := by
  have hroot : (A m).charpoly.IsRoot x := Polynomial.isRoot_of_mem_roots hx
  have hdet : (Matrix.scalar (Fin m) x - A m).det = 0 := by
    have := Matrix.eval_charpoly (A m) x
    rwa [hroot, eq_comm] at this
  obtain ⟨v, hv, hMv⟩ := (Matrix.exists_mulVec_eq_zero_iff.mpr hdet)
  have hs : (Matrix.scalar (Fin m) x) *ᵥ v = x • v := by
    funext i
    rw [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    simp
  have key : (A m) *ᵥ v = x • v := by
    rw [Matrix.sub_mulVec, hs, sub_eq_zero] at hMv
    exact hMv.symm
  have key2 : (A m * A m) *ᵥ v = x ^ 2 • v := by
    rw [← Matrix.mulVec_mulVec, key, Matrix.mulVec_smul, key, smul_smul, sq]
  have key4 : ((A m * A m) * (A m * A m)) *ᵥ v = x ^ 4 • v := by
    rw [← Matrix.mulVec_mulVec, key2, Matrix.mulVec_smul, key2, smul_smul]
    congr 1; ring
  rw [A_mul_A_sq, Matrix.smul_mulVec, Matrix.one_mulVec] at key4
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have := congrFun key4 i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi this
  exact mul_right_cancel₀ hi this.symm

/-- Every root of the charpoly lies in the four–element set `S`. -/
theorem mem_S (x : ℂ) (hx : x ^ 4 = (m:ℂ)^2) :
    x = sqp m ∨ x = Complex.I * sqp m ∨ x = -sqp m ∨ x = -(Complex.I * sqp m) := by
  have hsp := sqp_sq m
  have h : (x^2 - (m:ℂ)) * (x^2 + (m:ℂ)) = 0 := by linear_combination hx
  rcases mul_eq_zero.mp h with h1 | h1
  · have hx2 : x^2 = (sqp m)^2 := by rw [hsp]; linear_combination h1
    have hf : (x - sqp m) * (x + sqp m) = 0 := by linear_combination hx2
    rcases mul_eq_zero.mp hf with h2 | h2
    · left; linear_combination h2
    · right; right; left; linear_combination h2
  · have hI : (Complex.I * sqp m)^2 = -(m:ℂ) := by
      rw [mul_pow, Complex.I_sq, hsp]; ring
    have hx2 : x^2 = (Complex.I * sqp m)^2 := by rw [hI]; linear_combination h1
    have hf : (x - Complex.I * sqp m) * (x + Complex.I * sqp m) = 0 := by linear_combination hx2
    rcases mul_eq_zero.mp hf with h2 | h2
    · right; left; linear_combination h2
    · right; right; right; linear_combination h2

theorem roots_card : (A m).charpoly.roots.card = m := by
  have h := Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits (A m).charpoly)
  rw [h, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

/-! ### multiplicity bookkeeping -/

/-- The four elements of `S` are pairwise distinct. -/
theorem S_pairwise :
    (sqp m ≠ Complex.I * sqp m) ∧ (sqp m ≠ -sqp m) ∧ (sqp m ≠ -(Complex.I * sqp m)) ∧
    (Complex.I * sqp m ≠ -sqp m) ∧ (Complex.I * sqp m ≠ -(Complex.I * sqp m)) ∧
    (-sqp m ≠ -(Complex.I * sqp m)) := by
  have hs := sqp_ne m
  have key : ∀ u u' : ℂ, u ≠ u' → u * sqp m ≠ u' * sqp m := by
    intro u u' huu h; exact huu (mul_right_cancel₀ hs h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using key 1 Complex.I (by norm_num [Complex.ext_iff])
  · simpa using key 1 (-1) (by norm_num [Complex.ext_iff])
  · simpa [neg_mul] using key 1 (-Complex.I) (by norm_num [Complex.ext_iff])
  · simpa using key Complex.I (-1) (by norm_num [Complex.ext_iff])
  · simpa [neg_mul] using key Complex.I (-Complex.I) (by norm_num [Complex.ext_iff])
  · simpa [neg_mul] using key (-1) (-Complex.I) (by norm_num [Complex.ext_iff])

/-- Multiplicities of the four eigenvalues. -/
def mA : ℕ := (A m).charpoly.roots.count (sqp m)
def mB : ℕ := (A m).charpoly.roots.count (Complex.I * sqp m)
def mC : ℕ := (A m).charpoly.roots.count (-sqp m)
def mD : ℕ := (A m).charpoly.roots.count (-(Complex.I * sqp m))

/-- The root multiset decomposes as replicates of the four eigenvalues. -/
theorem roots_decomp :
    (A m).charpoly.roots =
      Multiset.replicate (mA m) (sqp m) + Multiset.replicate (mB m) (Complex.I * sqp m)
        + Multiset.replicate (mC m) (-sqp m) + Multiset.replicate (mD m) (-(Complex.I * sqp m)) := by
  obtain ⟨n12, n13, n14, n23, n24, n34⟩ := S_pairwise m
  ext x
  simp only [Multiset.count_add, Multiset.count_replicate]
  by_cases hx : x ∈ (A m).charpoly.roots
  · rcases mem_S m x (eigen_pow4 m x hx) with h | h | h | h <;> subst h
    · rw [if_pos rfl, if_neg (fun h => n12 h.symm), if_neg (fun h => n13 h.symm),
        if_neg (fun h => n14 h.symm)]; simp [mA]
    · rw [if_neg n12, if_pos rfl, if_neg (fun h => n23 h.symm), if_neg (fun h => n24 h.symm)]
      simp [mB]
    · rw [if_neg n13, if_neg n23, if_pos rfl, if_neg (fun h => n34 h.symm)]; simp [mC]
    · rw [if_neg n14, if_neg n24, if_neg n34, if_pos rfl]; simp [mD]
  · rw [Multiset.count_eq_zero_of_notMem hx]
    have hz : ∀ (y : ℂ) (n : ℕ), n = (A m).charpoly.roots.count y → (if y = x then n else 0) = 0 := by
      intro y n hn; split_ifs with h
      · rw [hn, h]; exact Multiset.count_eq_zero_of_notMem hx
      · rfl
    rw [hz _ (mA m) rfl, hz _ (mB m) rfl, hz _ (mC m) rfl, hz _ (mD m) rfl]

/-- Sum of counts is `m`. -/
theorem card_eq : mA m + mB m + mC m + mD m = m := by
  have h := roots_card m
  rw [roots_decomp] at h
  simpa [Multiset.card_add, Multiset.card_replicate] using h

/-- Trace relation: the weighted sum of eigenvalues is the Gauss sum. -/
theorem sum_G :
    (mA m : ℂ) * sqp m + (mB m : ℂ) * (Complex.I * sqp m)
      + (mC m : ℂ) * (-sqp m) + (mD m : ℂ) * (-(Complex.I * sqp m))
    = ∑ k ∈ range m, (ω m) ^ (k ^ 2) := by
  have hsum : (A m).charpoly.roots.sum = ∑ k ∈ range m, (ω m) ^ (k ^ 2) := by
    rw [← Matrix.trace_eq_sum_roots_charpoly, trace_A]
  rw [← hsum, roots_decomp]
  simp only [Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul]

/-- Determinant relation: the product of eigenvalues is `det A`. -/
theorem prod_det :
    (sqp m) ^ (mA m) * (Complex.I * sqp m) ^ (mB m) * (-sqp m) ^ (mC m)
        * (-(Complex.I * sqp m)) ^ (mD m) = (A m).det := by
  rw [Matrix.det_eq_prod_roots_charpoly, roots_decomp]
  simp only [Multiset.prod_add, Multiset.prod_replicate]

/-! ### the trace-of-square bridge -/

theorem charmatrix_map_hom (B : Matrix (Fin m) (Fin m) ℂ) (f : ℂ[X] →ₐ[ℂ] ℂ[X]) :
    (Matrix.scalar (Fin m) X - B.map (C : ℂ →+* ℂ[X])).map f
      = Matrix.scalar (Fin m) (f X) - B.map (C : ℂ →+* ℂ[X]) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    map_sub, apply_ite f, map_zero]
  have hfC : f (C (B i j)) = C (B i j) := by
    rw [← Polynomial.algebraMap_eq]; exact AlgHom.commutes f _
  rw [hfC]

/-- **Key factorisation.**  `charpoly (A²)` is `∏ (X - λ²)` over the eigenvalues `λ` of `A`. -/
theorem charpoly_sq_factored :
    (A m * A m).charpoly
      = ((A m).charpoly.roots.map (fun lam => (X : ℂ[X]) - C (lam ^ 2))).prod := by
  set r := (A m).charpoly.roots with hr
  have hPfac : (A m).charpoly = (r.map (fun lam => (X : ℂ[X]) - C lam)).prod :=
    (IsAlgClosed.splits (A m).charpoly).eq_prod_roots_of_monic (A m).charpoly_monic
  have hPdet : (A m).charpoly = (Matrix.scalar (Fin m) X - (A m).map (C : ℂ →+* ℂ[X])).det := by
    rw [Matrix.charpoly, Matrix.charmatrix, RingHom.mapMatrix_apply]
  have hcard : Multiset.card r = m := roots_card m
  have hplus : (Matrix.scalar (Fin m) X + (A m).map (C : ℂ →+* ℂ[X])).det
      = (r.map (fun lam => (X : ℂ[X]) + C lam)).prod := by
    have hψ : (Polynomial.aeval (-(X : ℂ[X]))) (A m).charpoly
        = (r.map (fun lam => (-(X : ℂ[X]) - C lam))).prod := by
      rw [hPfac, map_multiset_prod, Multiset.map_map]
      apply congrArg Multiset.prod
      apply Multiset.map_congr rfl
      intro lam _
      simp only [Function.comp_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
        Polynomial.algebraMap_eq]
    have hψdet : (Polynomial.aeval (-(X : ℂ[X]))) (A m).charpoly
        = (Matrix.scalar (Fin m) (-(X : ℂ[X])) - (A m).map (C : ℂ →+* ℂ[X])).det := by
      rw [hPdet, AlgHom.map_det, AlgHom.mapMatrix_apply, charmatrix_map_hom]
      simp [Polynomial.aeval_X]
    rw [hψ] at hψdet
    have hneg : Matrix.scalar (Fin m) (-(X : ℂ[X])) - (A m).map (C : ℂ →+* ℂ[X])
        = -(Matrix.scalar (Fin m) X + (A m).map (C : ℂ →+* ℂ[X])) := by
      rw [map_neg]; abel
    rw [hneg, Matrix.det_neg, Fintype.card_fin] at hψdet
    have hprodneg : (r.map (fun lam => (-(X : ℂ[X]) - C lam))).prod
        = (-1 : ℂ[X]) ^ m * (r.map (fun lam => (X : ℂ[X]) + C lam)).prod := by
      have hfun : (fun lam : ℂ => (-(X : ℂ[X]) - C lam))
          = (fun lam : ℂ => (-1 : ℂ[X]) * ((X : ℂ[X]) + C lam)) := by funext lam; ring
      rw [hfun, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard]
    rw [hprodneg] at hψdet
    exact mul_left_cancel₀ (pow_ne_zero m (by norm_num : (-1 : ℂ[X]) ≠ 0)) hψdet.symm
  apply Polynomial.expand_injective (n := 2) (by norm_num)
  rw [Matrix.charpoly, Matrix.charmatrix, RingHom.mapMatrix_apply, AlgHom.map_det,
    AlgHom.mapMatrix_apply, charmatrix_map_hom]
  simp only [Polynomial.expand_X]
  have hfactor : Matrix.scalar (Fin m) (X ^ 2) - (A m * A m).map (C : ℂ →+* ℂ[X])
      = (Matrix.scalar (Fin m) X - (A m).map (C : ℂ →+* ℂ[X]))
          * (Matrix.scalar (Fin m) X + (A m).map (C : ℂ →+* ℂ[X])) := by
    have hc : Matrix.scalar (Fin m) X * (A m).map (C : ℂ →+* ℂ[X])
        = (A m).map (C : ℂ →+* ℂ[X]) * Matrix.scalar (Fin m) X :=
      (Matrix.scalar_commute X (fun r => Commute.all _ _) _).eq
    have hexp : (Matrix.scalar (Fin m) X - (A m).map (C : ℂ →+* ℂ[X]))
        * (Matrix.scalar (Fin m) X + (A m).map (C : ℂ →+* ℂ[X]))
        = Matrix.scalar (Fin m) X * Matrix.scalar (Fin m) X
            - (A m).map (C : ℂ →+* ℂ[X]) * (A m).map (C : ℂ →+* ℂ[X]) := by
      rw [sub_mul, mul_add, mul_add, hc]; abel
    rw [hexp]
    congr 1
    · rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
      simp [sq, Matrix.scalar_apply]
    · rw [← Matrix.map_mul]
  rw [hfactor, Matrix.det_mul, ← hPdet, hplus]
  rw [hPfac, map_multiset_prod, Multiset.map_map, ← Multiset.prod_map_mul]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro lam _
  simp only [Function.comp_apply, map_sub, Polynomial.expand_X, Polynomial.expand_C]
  rw [map_pow]; ring

/-- The bridge equation:  `(mA + mC) - (mB + mD) = trace(A²)/m`, in the form
`m·((mA+mC) - (mB+mD)) = trace(A*A)`. -/
theorem sum_sq_rel :
    ((mA m : ℂ) + mC m) - (mB m + mD m) = (1 / m) * (A m * A m).trace := by
  have hroots2 : (A m * A m).charpoly.roots
      = (A m).charpoly.roots.map (fun lam => lam ^ 2) := by
    rw [charpoly_sq_factored]
    have hcomp : (fun lam : ℂ => (X : ℂ[X]) - C (lam ^ 2))
        = (fun mu : ℂ => (X : ℂ[X]) - C mu) ∘ (fun lam => lam ^ 2) := rfl
    rw [hcomp, ← Multiset.map_map, Polynomial.roots_multiset_prod_X_sub_C]
  have htr : (A m * A m).trace = ((A m).charpoly.roots.map (fun lam => lam ^ 2)).sum := by
    rw [Matrix.trace_eq_sum_roots_charpoly, hroots2]
  rw [roots_decomp] at htr
  simp only [Multiset.map_add, Multiset.map_replicate, Multiset.sum_add, Multiset.sum_replicate,
    nsmul_eq_mul] at htr
  have e2 : (Complex.I * sqp m) ^ 2 = -(m : ℂ) := by rw [mul_pow, Complex.I_sq, sqp_sq]; ring
  have e3 : (-sqp m) ^ 2 = (m : ℂ) := by rw [neg_pow]; simp [sqp_sq]
  have e4 : (-(Complex.I * sqp m)) ^ 2 = -(m : ℂ) := by rw [neg_pow]; simp [e2]
  rw [sqp_sq, e2, e3, e4] at htr
  have hm0c : (m : ℂ) ≠ 0 := by exact_mod_cast hm0 m
  rw [htr]; field_simp; ring

/-! ### Vandermonde determinant phase -/

theorem omega_pow_eq (k : ℕ) :
    (ω m) ^ k = Complex.exp (↑k * (2 * ↑Real.pi * Complex.I / ↑m)) := by
  rw [ω, ← Complex.exp_nat_mul]

theorem A_eq_vandermonde :
    A m = Matrix.vandermonde (fun i : Fin m => (ω m) ^ (i.val)) := by
  ext i j
  show (ω m) ^ (i.val * j.val) = Matrix.vandermonde (fun i : Fin m => (ω m) ^ (i.val)) i j
  rw [Matrix.vandermonde_apply, ← pow_mul]

theorem det_A_eq_prod :
    (A m).det
      = ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, ((ω m) ^ (j.val) - (ω m) ^ (i.val)) := by
  rw [A_eq_vandermonde, Matrix.det_vandermonde]

/-- The determinant as a product of the eigenvalues, simplified to `√m^m · Iᴱ`. -/
theorem prod_det_simp :
    (A m).det = (sqp m) ^ m * Complex.I ^ (mB m + 2 * (mC m) + 3 * (mD m)) := by
  have key : (A m).det
      = (sqp m) ^ (mA m + mB m + mC m + mD m)
          * Complex.I ^ (mB m + 2 * (mC m) + 3 * (mD m)) := by
    rw [← prod_det]
    have hI2 : (-1 : ℂ) = Complex.I ^ 2 := Complex.I_sq.symm
    have hB : (Complex.I * sqp m) ^ (mB m) = Complex.I ^ (mB m) * (sqp m) ^ (mB m) :=
      mul_pow _ _ _
    have hC : (-sqp m) ^ (mC m) = Complex.I ^ (2 * mC m) * (sqp m) ^ (mC m) := by
      rw [neg_eq_neg_one_mul, mul_pow, hI2, ← pow_mul]
    have hD : (-(Complex.I * sqp m)) ^ (mD m)
        = Complex.I ^ (2 * mD m) * (Complex.I ^ (mD m) * (sqp m) ^ (mD m)) := by
      rw [neg_eq_neg_one_mul, mul_pow, hI2, ← pow_mul, mul_pow]
    rw [hB, hC, hD]
    ring
  rw [key, card_eq m]

/-- For `a < b`, the Vandermonde factor factorises into modulus and phase. -/
theorem vand_factor (a b : ℕ) :
    (ω m) ^ b - (ω m) ^ a
      = (2 * Complex.I * (Real.sin (Real.pi * ((b : ℝ) - a) / m) : ℂ))
          * Complex.exp (Complex.I * ((Real.pi * ((a : ℝ) + b) / m : ℝ) : ℂ)) := by
  have hpc : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hm0 m)
  have key : ∀ z : ℂ, 2 * Complex.I * Complex.sin z
      = Complex.exp (z * Complex.I) - Complex.exp (-z * Complex.I) := by
    intro z
    rw [Complex.sin]
    linear_combination (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * Complex.I_sq
  rw [Complex.ofReal_sin, key, sub_mul, ← Complex.exp_add, ← Complex.exp_add,
      omega_pow_eq m b, omega_pow_eq m a]
  congr 1
  · congr 1; push_cast; field_simp; ring
  · congr 1; push_cast; field_simp; ring

/-- For `a < b < m`, the sine of the phase argument is positive. -/
theorem vand_sin_pos (a b : ℕ) (hab : a < b) (hb : b < m) :
    0 < Real.sin (Real.pi * ((b : ℝ) - a) / m) := by
  have hpr : (0 : ℝ) < m := by exact_mod_cast (hmpos m)
  have hd : (0 : ℝ) < (b : ℝ) - a := by
    have : (a : ℝ) < b := by exact_mod_cast hab
    linarith
  have hdp : (b : ℝ) - a < m := by
    have h1 : (b : ℝ) < m := by exact_mod_cast hb
    have h2 : (0 : ℝ) ≤ a := by positivity
    linarith
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [div_lt_iff₀ hpr]
    nlinarith [Real.pi_pos]

/-- `2·∑_{i<m} i = m(m-1)`. -/
theorem sum_fin_val_two : 2 * (∑ i : Fin m, (i.val)) = m * (m - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => k) m]
  rw [Nat.mul_comm]
  exact Finset.sum_range_id_mul_two m

/-- The phase index sum before simplification. -/
theorem Snat_pre :
    (∑ i : Fin m, ∑ j ∈ Finset.Ioi i, (i.val + j.val))
      = (∑ i : Fin m, (i.val)) * (m - 1) := by
  have hswap : (∑ i : Fin m, ∑ j ∈ Finset.Ioi i, j.val)
      = ∑ j : Fin m, ∑ _i ∈ Finset.Iio j, j.val := by
    apply Finset.sum_comm'
    intro i j
    simp only [Finset.mem_univ, true_and, and_true, Finset.mem_Ioi, Finset.mem_Iio]
  have inner : ∀ i : Fin m, (∑ j ∈ Finset.Ioi i, (i.val + j.val))
      = i.val * (Finset.Ioi i).card + ∑ j ∈ Finset.Ioi i, j.val := by
    intro i
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm]
  simp only [inner]
  rw [Finset.sum_add_distrib, hswap]
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Fin.card_Ioi, Fin.card_Iio]
  rw [← Finset.sum_add_distrib]
  have hterm : ∀ i : Fin m, i.val * (m - 1 - i.val) + i.val * i.val = i.val * (m - 1) := by
    intro i; have := i.isLt; rw [← Nat.mul_add]; congr 1; omega
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_mul]

/-- The double sum of `π(i+j)/m` equals `π(m-1)²/2` (real number). -/
theorem phase_real_sum :
    (∑ i : Fin m, ∑ j ∈ Finset.Ioi i, Real.pi * ((i.val : ℝ) + j.val) / m)
      = Real.pi * ((m : ℝ) - 1) ^ 2 / 2 := by
  have hpr : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hm0 m)
  have hcast : (∑ i : Fin m, ∑ j ∈ Finset.Ioi i, ((i.val : ℝ) + j.val))
      = ((∑ i : Fin m, ∑ j ∈ Finset.Ioi i, (i.val + j.val) : ℕ) : ℝ) := by
    push_cast; rfl
  have hfactor : (∑ i : Fin m, ∑ j ∈ Finset.Ioi i, Real.pi * ((i.val : ℝ) + j.val) / m)
      = (Real.pi / m) * (∑ i : Fin m, ∑ j ∈ Finset.Ioi i, ((i.val : ℝ) + j.val)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hfactor, hcast, Snat_pre m]
  -- now need: (π/m) * ((Σ i.val)*(m-1) : ℕ cast) = π (m-1)²/2
  have h2 : 2 * ((∑ i : Fin m, (i.val)) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
    have := sum_fin_val_two m
    have hcast2 : ((2 * (∑ i : Fin m, (i.val)) : ℕ) : ℝ) = ((m * (m - 1) : ℕ) : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
    push_cast at hcast2
    -- m ≥ 1 so (m-1 : ℕ) casts fine
    have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (hmpos m), Nat.cast_one]
    rw [hm1] at hcast2
    linarith [hcast2]
  have hprod : (((∑ i : Fin m, (i.val)) * (m - 1) : ℕ) : ℝ)
      = ((∑ i : Fin m, (i.val)) : ℝ) * ((m : ℝ) - 1) := by
    have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (hmpos m), Nat.cast_one]
    rw [Nat.cast_mul, hm1, Nat.cast_sum]
  rw [hprod]
  field_simp
  nlinarith [h2]

/-! ### The squared modulus of the Gauss sum via character orthogonality -/

theorem psi_primitive : AddChar.IsPrimitive (psi m) :=
  AddChar.zmodChar_primitive_of_primitive_root m (omega_primitiveRoot m)

theorem G_zmod :
    ∑ k ∈ range m, (ω m) ^ (k ^ 2) = ∑ a : ZMod m, psi m (a ^ 2) := by
  apply Finset.sum_nbij' (fun k : ℕ => (k : ZMod m)) (fun a : ZMod m => a.val)
  · intro a _; exact Finset.mem_univ _
  · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro k hk; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hk)
  · intro a _; exact ZMod.natCast_rightInverse a
  · intro k _
    have : ((k : ZMod m)) ^ 2 = ((k ^ 2 : ℕ) : ZMod m) := by push_cast; ring
    rw [this, psi_apply_natCast]

/-- `conj (ψ a) = ψ (-a)`. -/
theorem conj_psi (a : ZMod m) : (starRingEnd ℂ) (psi m a) = psi m (-a) := by
  have hR : 0 < ringChar (ZMod m) := by
    rw [ZMod.ringChar_zmod_n]; exact hmpos m
  rw [AddChar.starComp_apply hR]
  rfl

/-- **The squared modulus of the Gauss sum**, expressed via the "double points" `2d = 0`. -/
theorem G_conj_G :
    (∑ k ∈ range m, (ω m) ^ (k ^ 2)) * (starRingEnd ℂ) (∑ k ∈ range m, (ω m) ^ (k ^ 2))
      = (m : ℂ) * ∑ d : ZMod m, (if (2 : ZMod m) * d = 0 then psi m (d ^ 2) else 0) := by
  rw [G_zmod, map_sum]
  -- conj of each term
  have hconj : ∀ b : ZMod m, (starRingEnd ℂ) (psi m (b ^ 2)) = psi m (-(b ^ 2)) := by
    intro b; exact conj_psi m (b ^ 2)
  rw [Finset.sum_congr rfl (fun b _ => hconj b)]
  -- expand product of sums
  rw [Finset.sum_mul_sum]
  -- combine characters: psi(a²)*psi(-(b²)) = psi(a²-b²)
  have hcomb : ∀ a b : ZMod m, psi m (a ^ 2) * psi m (-(b ^ 2)) = psi m (a ^ 2 - b ^ 2) := by
    intro a b; rw [← AddChar.map_add_eq_mul]; congr 1; ring
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hcomb a b))]
  -- swap to make `a` the inner sum, then reindex a = b + d
  rw [Finset.sum_comm]
  have hreindex : ∀ b : ZMod m,
      (∑ a : ZMod m, psi m (a ^ 2 - b ^ 2)) = ∑ d : ZMod m, psi m (2 * b * d + d ^ 2) := by
    intro b
    rw [← Equiv.sum_comp (Equiv.addLeft b) (fun a => psi m (a ^ 2 - b ^ 2))]
    apply Finset.sum_congr rfl
    intro d _
    simp only [Equiv.coe_addLeft]
    congr 1; ring
  rw [Finset.sum_congr rfl (fun b _ => hreindex b)]
  -- swap back: sum over d outer
  rw [Finset.sum_comm]
  -- factor psi(d²) and use sum_mulShift
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  have hsplit : ∀ b : ZMod m, psi m (2 * b * d + d ^ 2) = psi m (b * (2 * d)) * psi m (d ^ 2) := by
    intro b; rw [← AddChar.map_add_eq_mul]; congr 1; ring
  rw [Finset.sum_congr rfl (fun b _ => hsplit b), ← Finset.sum_mul]
  rw [AddChar.sum_mulShift (2 * d) (psi_primitive m), ZMod.card]
  split_ifs with h
  · ring
  · ring

/-- The determinant of `A` as a nonnegative real modulus times a power of `I` times a phase. -/
theorem det_A_modphase :
    (A m).det
      = (↑(∏ i : Fin m, ∏ j ∈ Finset.Ioi i,
            2 * Real.sin (Real.pi * ((j.val : ℝ) - i.val) / m)) : ℂ)
          * Complex.I ^ (∑ i : Fin m, (Finset.Ioi i).card)
          * Complex.exp (Complex.I * ((Real.pi * ((m : ℝ) - 1) ^ 2 / 2 : ℝ) : ℂ)) := by
  rw [det_A_eq_prod]
  have hfac : ∀ i : Fin m, ∀ j ∈ Finset.Ioi i,
      (ω m) ^ (j.val) - (ω m) ^ (i.val)
        = (↑(2 * Real.sin (Real.pi * ((j.val : ℝ) - i.val) / m)) : ℂ) * Complex.I
            * Complex.exp (Complex.I * (↑(Real.pi * ((i.val : ℝ) + j.val) / m) : ℂ)) := by
    intro i j _
    rw [vand_factor m i.val j.val]
    push_cast
    ring
  rw [Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (hfac i))]
  conv_lhs => simp only [Finset.prod_mul_distrib]
  have hX : (∏ i : Fin m, ∏ j ∈ Finset.Ioi i,
        (↑(2 * Real.sin (Real.pi * ((j.val : ℝ) - i.val) / m)) : ℂ))
      = (↑(∏ i : Fin m, ∏ j ∈ Finset.Ioi i,
            2 * Real.sin (Real.pi * ((j.val : ℝ) - i.val) / m)) : ℂ) := by
    push_cast; rfl
  have hI : (∏ i : Fin m, ∏ _j ∈ Finset.Ioi i, Complex.I)
      = Complex.I ^ (∑ i : Fin m, (Finset.Ioi i).card) := by
    simp only [Finset.prod_const]
    rw [Finset.prod_pow_eq_pow_sum]
  have hE : (∏ i : Fin m, ∏ j ∈ Finset.Ioi i,
        Complex.exp (Complex.I * (↑(Real.pi * ((i.val : ℝ) + j.val) / m) : ℂ)))
      = Complex.exp (Complex.I * ((Real.pi * ((m : ℝ) - 1) ^ 2 / 2 : ℝ) : ℂ)) := by
    simp only [← Complex.exp_sum]
    congr 1
    rw [← phase_real_sum m]
    simp only [Complex.ofReal_sum, Finset.mul_sum]
  rw [hX, hI, hE]

/-- `N = ∑ card (Ioi i) = m(m-1)/2`. -/
theorem N_value : (∑ i : Fin m, (Finset.Ioi i).card) = m * (m - 1) / 2 := by
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun k => m - 1 - k) m]
  have hrefl : (∑ k ∈ Finset.range m, (m - 1 - k)) = ∑ k ∈ Finset.range m, k :=
    Finset.sum_range_reflect (fun k => k) m
  rw [hrefl, Finset.sum_range_id]

/-! ### Trace of R, and the double-point sum -/

/-- `2 * d = 0` in `ZMod m` iff `m ∣ 2 * d.val`. -/
theorem two_mul_eq_zero_iff (d : ZMod m) : (2 : ZMod m) * d = 0 ↔ m ∣ (2 * d.val) := by
  have hd : ((2 * d.val : ℕ) : ZMod m) = (2 : ZMod m) * d := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [← hd, ZMod.natCast_eq_zero_iff]

/-- For `m` odd, `2 d = 0 → d = 0`. -/
theorem two_mul_eq_zero_odd (hodd : m % 2 = 1) (d : ZMod m) (h : (2 : ZMod m) * d = 0) :
    d = 0 := by
  rw [two_mul_eq_zero_iff] at h
  have hcop : Nat.Coprime m 2 := by
    rw [Nat.coprime_two_right]; exact Nat.odd_iff.mpr hodd
  have hdvd : m ∣ d.val := Nat.Coprime.dvd_of_dvd_mul_left hcop h
  have hv0 : d.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt d)
  exact (ZMod.val_eq_zero d).mp hv0

/-- Arithmetic helper: for `m = 2s`, `s ≥ 1`, `a < 2s`, `m ∣ 2a ↔ a = 0 ∨ a = s`. -/
theorem two_dvd_helper (s a : ℕ) (hs1 : 1 ≤ s) (ha : a < 2 * s) :
    2 * s ∣ 2 * a ↔ a = 0 ∨ a = s := by
  constructor
  · intro h
    have hsa : s ∣ a := (mul_dvd_mul_iff_left (by norm_num : (2:ℕ) ≠ 0)).mp h
    obtain ⟨t, rfl⟩ := hsa
    have ht2 : t < 2 := by
      by_contra hc
      push_neg at hc
      have : 2 * s ≤ s * t := by nlinarith
      omega
    interval_cases t <;> simp
  · rintro (rfl | rfl) <;> simp

/-- For `m` odd, the sum of the double-point indicator equals `1`. -/
theorem Sd_odd (hodd : m % 2 = 1) :
    (∑ d : ZMod m, if (2 : ZMod m) * d = 0 then psi m (d ^ 2) else 0) = 1 := by
  rw [Finset.sum_eq_single (0 : ZMod m)]
  · rw [if_pos (by ring)]
    simp
  · intro d _ hd
    rw [if_neg]
    intro hc
    exact hd (two_mul_eq_zero_odd m hodd d hc)
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The value `ω^{(m/2)²} = (-1)^{m/2}`. -/
theorem psi_c_sq (heven : m % 2 = 0) :
    psi m (((m / 2 : ℕ) : ZMod m) ^ 2) = (-1) ^ (m / 2) := by
  obtain ⟨s, hs⟩ : ∃ s, m = 2 * s := ⟨m / 2, by omega⟩
  have hs2 : m / 2 = s := by omega
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h, Nat.mul_zero] at hs; exact absurd hs (hm0 m)
    · exact h
  rw [hs2]
  have hcast : (((s : ℕ) : ZMod m) ^ 2) = ((s ^ 2 : ℕ) : ZMod m) := by push_cast; ring
  rw [hcast, psi_apply_natCast, omega_pow_eq]
  have hm : (m : ℂ) = 2 * s := by rw [hs]; push_cast; ring
  rw [hm]
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
  have hkey : (↑(s ^ 2) : ℂ) * (2 * ↑Real.pi * Complex.I / (2 * ↑s))
      = (↑s) * (↑Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [hkey, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-- For `m` even, the sum of the double-point indicator equals `1 + (-1)^{m/2}`. -/
theorem Sd_even (heven : m % 2 = 0) :
    (∑ d : ZMod m, if (2 : ZMod m) * d = 0 then psi m (d ^ 2) else 0)
      = 1 + (-1) ^ (m / 2) := by
  obtain ⟨s, hs⟩ : ∃ s, m = 2 * s := ⟨m / 2, by omega⟩
  have hs2 : m / 2 = s := by omega
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h, Nat.mul_zero] at hs; exact absurd hs (hm0 m)
    · exact h
  set c : ZMod m := ((s : ℕ) : ZMod m) with hc
  have hcval : c.val = s := by rw [hc, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hcne : c ≠ 0 := by
    intro h
    rw [h, ZMod.val_zero] at hcval
    omega
  have hmem : ∀ d : ZMod m, ((2 : ZMod m) * d = 0) ↔ (d = 0 ∨ d = c) := by
    intro d
    rw [two_mul_eq_zero_iff]
    have hval : d.val < 2 * s := by rw [← hs]; exact ZMod.val_lt d
    have hiff : (m ∣ 2 * d.val) ↔ (d.val = 0 ∨ d.val = s) :=
      hs.symm ▸ two_dvd_helper s d.val hspos hval
    rw [hiff]
    constructor
    · rintro (h | h)
      · left; exact (ZMod.val_eq_zero d).mp h
      · right; rw [← ZMod.natCast_zmod_val d, h]
    · rintro (rfl | rfl)
      · left; simp
      · right; exact hcval
  have hfilter : (Finset.univ.filter (fun d : ZMod m => (2 : ZMod m) * d = 0)) = {0, c} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact hmem d
  rw [← Finset.sum_filter, hfilter, Finset.sum_pair (by
    intro h; exact hcne h.symm)]
  have h0 : psi m ((0 : ZMod m) ^ 2) = 1 := by simp
  rw [h0]
  congr 1
  rw [hc, ← hs2]
  exact psi_c_sq m heven

/-- Trace of `R` for `m` odd. -/
theorem trace_R_odd (hodd : m % 2 = 1) : (R m).trace = 1 := by
  rw [Matrix.trace]
  simp only [Matrix.diag, R]
  rw [Finset.sum_eq_single (0 : Fin m)]
  · rw [if_pos (by simp)]
  · intro i _ hi
    rw [if_neg]
    intro hdvd
    apply hi
    have hcop : Nat.Coprime m 2 := by
      rw [Nat.coprime_two_right]; exact Nat.odd_iff.mpr hodd
    have h2 : m ∣ 2 * i.val := by rw [two_mul]; exact hdvd
    have : m ∣ i.val := Nat.Coprime.dvd_of_dvd_mul_left hcop h2
    exact Fin.ext (Nat.eq_zero_of_dvd_of_lt this i.isLt)
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Trace of `R` for `m` even. -/
theorem trace_R_even (heven : m % 2 = 0) : (R m).trace = 2 := by
  obtain ⟨s, hs⟩ : ∃ s, m = 2 * s := ⟨m / 2, by omega⟩
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h, Nat.mul_zero] at hs; exact absurd hs (hm0 m)
    · exact h
  have hsm : s < m := by omega
  rw [Matrix.trace]
  simp only [Matrix.diag, R]
  rw [Finset.sum_boole]
  have hfilter : (Finset.univ.filter (fun i : Fin m => m ∣ (i.val + i.val)))
      = {0, ⟨s, hsm⟩} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    have hval : i.val < 2 * s := by rw [← hs]; exact i.isLt
    have hiff : (m ∣ (i.val + i.val)) ↔ (i.val = 0 ∨ i.val = s) := by
      rw [show i.val + i.val = 2 * i.val from by ring]
      exact hs.symm ▸ two_dvd_helper s i.val hspos hval
    rw [hiff]
    constructor
    · rintro (h | h)
      · left; exact Fin.ext h
      · right; exact Fin.ext h
    · rintro (rfl | rfl)
      · left; rfl
      · right; rfl
  rw [hfilter, Finset.card_pair (by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero] at hv
    omega)]
  norm_num

/-! ### Phase factors -/

/-- For `m` odd, the accumulated Vandermonde phase is `1`. -/
theorem phase_odd (hodd : m % 2 = 1) :
    Complex.exp (Complex.I * ((Real.pi * ((m : ℝ) - 1) ^ 2 / 2 : ℝ) : ℂ)) = 1 := by
  obtain ⟨q, hq⟩ : ∃ q, m = 2 * q + 1 := ⟨m / 2, by omega⟩
  have hmr : ((m : ℝ) - 1) = 2 * q := by rw [hq]; push_cast; ring
  have harg : Complex.I * ((Real.pi * ((m : ℝ) - 1) ^ 2 / 2 : ℝ) : ℂ)
      = (↑(q ^ 2) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [hmr]; push_cast; ring
  rw [harg, Complex.exp_nat_mul_two_pi_mul_I]

/-- For `m` even, the accumulated Vandermonde phase is `I`. -/
theorem phase_even (heven : m % 2 = 0) :
    Complex.exp (Complex.I * ((Real.pi * ((m : ℝ) - 1) ^ 2 / 2 : ℝ) : ℂ)) = Complex.I := by
  obtain ⟨s, hs⟩ : ∃ s, m = 2 * s := ⟨m / 2, by omega⟩
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h, Nat.mul_zero] at hs; exact absurd hs (hm0 m)
    · exact h
  set k : ℕ := s * (s - 1) with hk
  have hmr : ((m : ℝ) - 1) = 2 * s - 1 := by rw [hs]; push_cast; ring
  have harg : Complex.I * ((Real.pi * ((m : ℝ) - 1) ^ 2 / 2 : ℝ) : ℂ)
      = (↑k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + (Real.pi : ℂ) / 2 * Complex.I := by
    rw [hmr, hk]
    have hsk : ((s - 1 : ℕ) : ℂ) = (s : ℂ) - 1 := by
      rw [Nat.cast_sub hspos, Nat.cast_one]
    push_cast
    rw [hsk]
    ring
  rw [harg, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, one_mul,
    Complex.exp_mul_I, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  ring

/-! ### Assembling the main value -/

/-- The powers `I⁰,…,I³` are distinct. -/
theorem I_pow_inj (a b : ℕ) (ha : a < 4) (hb : b < 4)
    (h : Complex.I ^ a = Complex.I ^ b) : a = b := by
  have e2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have e3 : Complex.I ^ 3 = -Complex.I := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, Complex.I_sq, pow_one]; ring
  interval_cases a <;> interval_cases b <;>
    first
      | rfl
      | (simp only [pow_zero, pow_one, e2, e3] at h; norm_num [Complex.ext_iff] at h)

/-- The real modulus `∏∏ 2 sin` is positive. -/
theorem Rsin_pos :
    0 < ∏ i : Fin m, ∏ j ∈ Finset.Ioi i,
        2 * Real.sin (Real.pi * ((j.val : ℝ) - i.val) / m) := by
  apply Finset.prod_pos; intro i _
  apply Finset.prod_pos; intro j hj
  have hij : i < j := Finset.mem_Ioi.mp hj
  have hs := vand_sin_pos m i.val j.val hij j.isLt
  linarith

/-- `‖phase‖ = 1`. -/
theorem norm_phase :
    ‖Complex.exp (Complex.I * ((Real.pi * ((m : ℝ) - 1) ^ 2 / 2 : ℝ) : ℂ))‖ = 1 := by
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

/-- The phase-modulus equality `↑(∏∏2sin) = √m ^ m`. -/
theorem Rsin_eq :
    ((∏ i : Fin m, ∏ j ∈ Finset.Ioi i,
        2 * Real.sin (Real.pi * ((j.val : ℝ) - i.val) / m) : ℝ) : ℂ) = (sqp m) ^ m := by
  set Rs : ℝ := ∏ i : Fin m, ∏ j ∈ Finset.Ioi i,
      2 * Real.sin (Real.pi * ((j.val : ℝ) - i.val) / m) with hRs
  have hRpos : 0 < Rs := Rsin_pos m
  have hn1 : ‖(A m).det‖ = |Rs| := by
    rw [det_A_modphase m]
    rw [norm_mul, norm_mul, norm_phase m, mul_one, Complex.norm_pow, Complex.norm_I, one_pow,
      mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hn2 : ‖(A m).det‖ = (Real.sqrt m) ^ m := by
    rw [prod_det_simp m]
    rw [norm_mul, Complex.norm_pow, Complex.norm_pow, Complex.norm_I, one_pow, mul_one, sqp_eq,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg (m : ℝ))]
  have hRabs : |Rs| = (Real.sqrt m) ^ m := by rw [← hn1, hn2]
  rw [abs_of_pos hRpos] at hRabs
  rw [sqp_eq, ← Complex.ofReal_pow]
  exact_mod_cast hRabs

theorem int_bound_two {x : ℤ} (h : x ^ 2 ≤ 2) : -1 ≤ x ∧ x ≤ 1 := by
  constructor <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]

/-- **Main quadratic Gauss sum evaluation.**
For `m ≡ 1, 2, 3 (mod 4)` the value is determined exactly.  For `m ≡ 0 (mod 4)` the
linear-algebra data (trace, determinant phase, squared modulus) determine the value only up
to sign; the correct sign (`+`) is Gauss's classical hard case and is left as a disjunction. -/
theorem gauss_sum_value :
    (m % 4 = 1 → (∑ k ∈ range m, (ω m) ^ (k ^ 2)) = (Real.sqrt m : ℂ)) ∧
    (m % 4 = 2 → (∑ k ∈ range m, (ω m) ^ (k ^ 2)) = 0) ∧
    (m % 4 = 3 → (∑ k ∈ range m, (ω m) ^ (k ^ 2)) = Complex.I * (Real.sqrt m : ℂ)) ∧
    (m % 4 = 0 → (∑ k ∈ range m, (ω m) ^ (k ^ 2)) = (1 + Complex.I) * (Real.sqrt m : ℂ)
      ∨ (∑ k ∈ range m, (ω m) ^ (k ^ 2)) = -((1 + Complex.I) * (Real.sqrt m : ℂ))) := by
  set G := ∑ k ∈ range m, (ω m) ^ (k ^ 2) with hGdef
  set a : ℂ := (mA m : ℂ) - (mC m) with ha
  set b : ℂ := (mB m : ℂ) - (mD m) with hb
  have hG : G = sqp m * (a + Complex.I * b) := by
    rw [hGdef, ← sum_G m, ha, hb]; ring
  -- squared modulus  `|G|² = m (a²+b²)`
  have hGGbar : G * (starRingEnd ℂ) G = (m : ℂ) * (a ^ 2 + b ^ 2) := by
    have hca : (starRingEnd ℂ) a = a := by rw [ha]; simp
    have hcb : (starRingEnd ℂ) b = b := by rw [hb]; simp
    have hcsqp : (starRingEnd ℂ) (sqp m) = sqp m := by rw [sqp]; exact Complex.conj_ofReal _
    have hconjG : (starRingEnd ℂ) G = sqp m * (a - Complex.I * b) := by
      rw [hG, map_mul, map_add, map_mul, hca, hcb, hcsqp, Complex.conj_I]; ring
    have hs2 : sqp m * sqp m = (m : ℂ) := by rw [← sq]; exact sqp_sq m
    have hinner : (a + Complex.I * b) * (a - Complex.I * b) = a ^ 2 + b ^ 2 := by
      linear_combination (-(b ^ 2)) * Complex.I_sq
    rw [hconjG, hG]
    calc sqp m * (a + Complex.I * b) * (sqp m * (a - Complex.I * b))
        = (sqp m * sqp m) * ((a + Complex.I * b) * (a - Complex.I * b)) := by ring
      _ = (m : ℂ) * (a ^ 2 + b ^ 2) := by rw [hs2, hinner]
  have hm0c : (m : ℂ) ≠ 0 := by exact_mod_cast hm0 m
  have hab_sq : a ^ 2 + b ^ 2
      = ∑ d : ZMod m, (if (2 : ZMod m) * d = 0 then psi m (d ^ 2) else 0) := by
    apply mul_left_cancel₀ hm0c
    rw [← hGGbar]; exact G_conj_G m
  -- trace relation
  have htr : (mA m : ℂ) + mC m - (mB m + mD m) = (R m).trace := by
    rw [sum_sq_rel m, A_sq, Matrix.trace_smul, smul_eq_mul, one_div,
      inv_mul_cancel_left₀ hm0c]
  -- phase relation
  have hdet1 := det_A_modphase m
  have hdet2 := prod_det_simp m
  rw [Rsin_eq m] at hdet1
  have hN := N_value m
  set N := ∑ i : Fin m, (Finset.Ioi i).card with hNdef
  set E := mB m + 2 * mC m + 3 * mD m with hEdef
  set x : ℤ := (mA m : ℤ) - mC m with hx
  set y : ℤ := (mB m : ℤ) - mD m with hy
  have hax : a = (x : ℂ) := by rw [ha, hx]; push_cast; ring
  have hby : b = (y : ℂ) := by rw [hb, hy]; push_cast; ring
  have hcardℤ : (mA m : ℤ) + mB m + mC m + mD m = m := by
    have h := card_eq m; exact_mod_cast (by omega : (mA m : ℤ) + mB m + mC m + mD m = m)
  have hEz : (E : ℤ) = 2 * (mB m + mD m) + (mA m + mC m) - x - y := by
    rw [hEdef, hx, hy]; push_cast; ring
  have hN2 : 2 * N = m * (m - 1) := by
    rw [hN]
    have hdvd : 2 ∣ m * (m - 1) := by
      rcases Nat.even_or_odd m with he | ho
      · exact Dvd.dvd.mul_right (even_iff_two_dvd.mp he) _
      · have : 2 ∣ (m - 1) := by
          rcases ho with ⟨t, ht⟩; exact ⟨t, by omega⟩
        exact Dvd.dvd.mul_left this _
    rw [Nat.mul_div_cancel' hdvd]
  have hIphase : Complex.I ^ N * Complex.exp (Complex.I * ((Real.pi * ((m:ℝ)-1)^2/2 : ℝ):ℂ))
      = Complex.I ^ E := by
    have h := hdet1.symm.trans hdet2
    have hsqpm : (sqp m) ^ m ≠ 0 := pow_ne_zero m (sqp_ne m)
    apply mul_left_cancel₀ hsqpm
    linear_combination h
  clear hGGbar hdet1 hdet2 hN hm0c
  refine ⟨fun h4 => ?_, fun h4 => ?_, fun h4 => ?_, fun h4 => ?_⟩
  · -- m ≡ 1 (mod 4):  √m
    have hodd : m % 2 = 1 := by omega
    obtain ⟨j, hj⟩ : ∃ j, m = 4 * j + 1 := ⟨m / 4, by omega⟩
    have hm1 : m - 1 = 4 * j := by omega
    have hNval : 2 * N = 16 * (j * j) + 4 * j := by rw [hN2, hm1, hj]; ring
    have hxy : x ^ 2 + y ^ 2 = 1 := by
      have hcx : ((x ^ 2 + y ^ 2 : ℤ) : ℂ) = 1 := by
        push_cast; rw [← hax, ← hby, hab_sq, Sd_odd m hodd]
      exact_mod_cast hcx
    have htr1 : (mA m : ℤ) + mC m - (mB m + mD m) = 1 := by
      have ht := htr; rw [trace_R_odd m hodd] at ht
      have hc : (((mA m : ℤ) + mC m - (mB m + mD m) : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by
        push_cast; push_cast at ht; linear_combination ht
      exact_mod_cast hc
    have hmod : E % 4 = N % 4 := by
      apply I_pow_inj _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
      rw [← Complex.I_pow_eq_pow_mod, ← Complex.I_pow_eq_pow_mod, ← hIphase,
        phase_odd m hodd, mul_one]
    obtain ⟨hxr1, hxr2⟩ := int_bound_two (show x ^ 2 ≤ 2 by linarith [sq_nonneg y, hxy])
    obtain ⟨hyr1, hyr2⟩ := int_bound_two (show y ^ 2 ≤ 2 by linarith [sq_nonneg x, hxy])
    have hy0 : y = 0 := by omega
    have hx2 : x ^ 2 = 1 := by rw [hy0] at hxy; simpa using hxy
    have hxeq : x = 1 := by
      have hne : x ≠ 0 := by intro h; rw [h] at hx2; norm_num at hx2
      have hxne : x = 1 ∨ x = -1 := by omega
      rcases hxne with h | h
      · exact h
      · exfalso; omega
    have hae : a = 1 := by rw [hax, hxeq]; norm_num
    have hbe : b = 0 := by rw [hby, hy0]; norm_num
    rw [hG, hae, hbe, sqp_eq]; ring
  · -- m ≡ 2 (mod 4):  0
    have heven : m % 2 = 0 := by omega
    have hxy : x ^ 2 + y ^ 2 = 0 := by
      have hcx : ((x ^ 2 + y ^ 2 : ℤ) : ℂ) = 0 := by
        push_cast; rw [← hax, ← hby, hab_sq, Sd_even m heven]
        have hodd2 : Odd (m / 2) := by rw [Nat.odd_iff]; omega
        rw [Odd.neg_one_pow hodd2]; norm_num
      exact_mod_cast hcx
    have hx0 : x = 0 := by
      have hx2 : x ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg y, hxy]) (sq_nonneg x)
      exact sq_eq_zero_iff.mp hx2
    have hy0 : y = 0 := by
      have hy2 : y ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg x, hxy]) (sq_nonneg y)
      exact sq_eq_zero_iff.mp hy2
    have hae : a = 0 := by rw [hax, hx0]; norm_num
    have hbe : b = 0 := by rw [hby, hy0]; norm_num
    rw [hG, hae, hbe]; ring
  · -- m ≡ 3 (mod 4):  I√m
    have hodd : m % 2 = 1 := by omega
    obtain ⟨j, hj⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hm1 : m - 1 = 4 * j + 2 := by omega
    have hNval : 2 * N = 16 * (j * j) + 20 * j + 6 := by rw [hN2, hm1, hj]; ring
    have hxy : x ^ 2 + y ^ 2 = 1 := by
      have hcx : ((x ^ 2 + y ^ 2 : ℤ) : ℂ) = 1 := by
        push_cast; rw [← hax, ← hby, hab_sq, Sd_odd m hodd]
      exact_mod_cast hcx
    have htr1 : (mA m : ℤ) + mC m - (mB m + mD m) = 1 := by
      have ht := htr; rw [trace_R_odd m hodd] at ht
      have hc : (((mA m : ℤ) + mC m - (mB m + mD m) : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by
        push_cast; push_cast at ht; linear_combination ht
      exact_mod_cast hc
    have hmod : E % 4 = N % 4 := by
      apply I_pow_inj _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
      rw [← Complex.I_pow_eq_pow_mod, ← Complex.I_pow_eq_pow_mod, ← hIphase,
        phase_odd m hodd, mul_one]
    obtain ⟨hxr1, hxr2⟩ := int_bound_two (show x ^ 2 ≤ 2 by linarith [sq_nonneg y, hxy])
    obtain ⟨hyr1, hyr2⟩ := int_bound_two (show y ^ 2 ≤ 2 by linarith [sq_nonneg x, hxy])
    have hx0 : x = 0 := by omega
    have hy2 : y ^ 2 = 1 := by rw [hx0] at hxy; simpa using hxy
    have hyeq : y = 1 := by
      have hne : y ≠ 0 := by intro h; rw [h] at hy2; norm_num at hy2
      have hyne : y = 1 ∨ y = -1 := by omega
      rcases hyne with h | h
      · exact h
      · exfalso; omega
    have hae : a = 0 := by rw [hax, hx0]; norm_num
    have hbe : b = 1 := by rw [hby, hyeq]; norm_num
    rw [hG, hae, hbe, sqp_eq]; ring
  · -- m ≡ 0 (mod 4):  ±(1+I)√m
    have hmp : 0 < m := hmpos m
    have heven : m % 2 = 0 := by omega
    obtain ⟨j, hj⟩ : ∃ j, m = 4 * j := ⟨m / 4, by omega⟩
    have hj1 : 1 ≤ j := by omega
    have hm1 : m - 1 = 4 * j - 1 := by omega
    have hNval : 2 * N + 4 * j = 16 * (j * j) := by
      rw [hN2, hj]; zify [show (1:ℕ) ≤ 4 * j by omega]; ring
    have hxy : x ^ 2 + y ^ 2 = 2 := by
      have hcx : ((x ^ 2 + y ^ 2 : ℤ) : ℂ) = 2 := by
        push_cast; rw [← hax, ← hby, hab_sq, Sd_even m heven]
        have heo : Even (m / 2) := by rw [Nat.even_iff]; omega
        rw [Even.neg_one_pow heo]; norm_num
      exact_mod_cast hcx
    have htr2 : (mA m : ℤ) + mC m - (mB m + mD m) = 2 := by
      have ht := htr; rw [trace_R_even m heven] at ht
      have hc : (((mA m : ℤ) + mC m - (mB m + mD m) : ℤ) : ℂ) = ((2 : ℤ) : ℂ) := by
        push_cast; push_cast at ht; linear_combination ht
      exact_mod_cast hc
    have hmod : E % 4 = (N + 1) % 4 := by
      apply I_pow_inj _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
      rw [← Complex.I_pow_eq_pow_mod, ← Complex.I_pow_eq_pow_mod, ← hIphase,
        phase_even m heven, pow_succ]
    obtain ⟨hxr1, hxr2⟩ := int_bound_two (show x ^ 2 ≤ 2 by linarith [sq_nonneg y, hxy])
    obtain ⟨hyr1, hyr2⟩ := int_bound_two (show y ^ 2 ≤ 2 by linarith [sq_nonneg x, hxy])
    have hxpar : x % 2 = 1 := by omega
    have hypar : y % 2 = 1 := by omega
    have hkey : (x = 1 ∧ y = 1) ∨ (x = -1 ∧ y = -1) := by
      have hx1 : x = 1 ∨ x = -1 := by omega
      have hy1 : y = 1 ∨ y = -1 := by omega
      rcases hx1 with h | h <;> rcases hy1 with g | g
      · exact Or.inl ⟨h, g⟩
      · exfalso; omega
      · exfalso; omega
      · exact Or.inr ⟨h, g⟩
    rcases hkey with ⟨hxe, hye⟩ | ⟨hxe, hye⟩
    · left
      have hae : a = 1 := by rw [hax, hxe]; norm_num
      have hbe : b = 1 := by rw [hby, hye]; norm_num
      rw [hG, hae, hbe, sqp_eq]; ring
    · right
      have hae : a = -1 := by rw [hax, hxe]; norm_num
      have hbe : b = -1 := by rw [hby, hye]; norm_num
      rw [hG, hae, hbe, sqp_eq]; ring

/-- The classical quadratic Gauss sum `S t m = ∑_{k<m} exp(2πi t k²/m)`. -/
def S (t m : ℕ) : ℂ :=
  ∑ k ∈ range m, Complex.exp (2 * Real.pi * Complex.I * t * k ^ 2 / m)

/-- For `t = 1` the Gauss sum equals the power sum `∑ ω^(k²)`. -/
theorem S_one_eq : S 1 m = ∑ k ∈ range m, (ω m) ^ (k ^ 2) := by
  unfold S
  apply Finset.sum_congr rfl
  intro k _
  rw [ω, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **Main quadratic Gauss sum evaluation, phrased for `S 1 m`.** -/
theorem S_value :
    (m % 4 = 1 → S 1 m = (Real.sqrt m : ℂ)) ∧
    (m % 4 = 2 → S 1 m = 0) ∧
    (m % 4 = 3 → S 1 m = Complex.I * (Real.sqrt m : ℂ)) ∧
    (m % 4 = 0 → S 1 m = (1 + Complex.I) * (Real.sqrt m : ℂ)
      ∨ S 1 m = -((1 + Complex.I) * (Real.sqrt m : ℂ))) := by
  rw [S_one_eq]
  exact gauss_sum_value m

end GaussGen

end
end

/- ================= inlined from Analytic.lean ================= -/
section

set_option maxHeartbeats 1000000

open Complex Filter Topology Real HurwitzZeta
open scoped ComplexOrder LSeries.notation

/-! ## Target 2 helper lemmas (odd Hurwitz-zeta special value). -/

/-- `x : ℝ` with `0 < x < 1` is not an integer (as a complex number). -/
lemma mem_integerComplement_of_mem_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (x : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.integerComplement.mem_iff]
  rintro ⟨n, hn⟩
  have hnx : (n : ℝ) = x := by exact_mod_cast hn
  have h1 : (0 : ℝ) < n := by rw [hnx]; exact hx0
  have h2 : (n : ℝ) < 1 := by rw [hnx]; exact hx1
  have : 0 < n := by exact_mod_cast h1
  have : n < 1 := by exact_mod_cast h2
  omega

/-- The complex summand is the coercion of the real difference. -/
lemma summand_eq_ofReal {x : ℝ} (n : ℕ) :
    1 / ((n : ℂ) + x) - 1 / ((n : ℂ) + 1 - x)
      = ((1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1 - x) : ℝ) : ℂ) := by
  push_cast
  ring

lemma denom_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) :
    ((n : ℝ)) ^ 2 ≤ ((n : ℝ) + x) * ((n : ℝ) + 1 - x) := by
  have : ((n : ℝ) + x) * ((n : ℝ) + 1 - x) = (n : ℝ) ^ 2 + n + x * (1 - x) := by ring
  rw [this]
  nlinarith [mul_pos hx0 (by linarith : (0:ℝ) < 1 - x), Nat.cast_nonneg (α := ℝ) n]

lemma abs_r_le {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {n : ℕ} (hn : 1 ≤ n) :
    |1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1 - x)| ≤ |1 - 2 * x| * (1 / (n : ℝ) ^ 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hd1 : (0 : ℝ) < (n : ℝ) + x := by linarith
  have hd2 : (0 : ℝ) < (n : ℝ) + 1 - x := by linarith
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have heq : 1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + 1 - x)
      = (1 - 2 * x) / (((n : ℝ) + x) * ((n : ℝ) + 1 - x)) := by
    field_simp; ring
  rw [heq, abs_div, abs_of_pos (by positivity : (0:ℝ) < ((n : ℝ) + x) * ((n : ℝ) + 1 - x)),
    mul_one_div]
  gcongr
  exact denom_bound hx0 hx1 n

lemma summable_diff {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + x) - 1 / ((n : ℂ) + 1 - x)) := by
  apply Summable.of_norm_bounded_eventually_nat (g := fun n => |1 - 2 * x| * (1 / (n : ℝ) ^ 2))
  · exact (summable_one_div_nat_pow.mpr (le_refl 2)).mul_left _
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [summand_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]
    exact abs_r_le hx0 hx1 hn

lemma summable_norm_diff {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Summable (fun n : ℕ => ‖1 / ((n : ℂ) + x) - 1 / ((n : ℂ) + 1 - x)‖) :=
  (summable_norm_iff.mpr (summable_diff hx0 hx1))

/-- Telescoping identity for the partial sums of the difference series. -/
lemma telescope {x : ℝ} (hz : (x : ℂ) ∈ Complex.integerComplement) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), (1 / ((n : ℂ) + x) - 1 / ((n : ℂ) + 1 - x))
      = 1 / (x : ℂ)
        + (∑ m ∈ Finset.range M, (1 / ((x : ℂ) - (m + 1)) + 1 / ((x : ℂ) + (m + 1))))
        - 1 / ((M : ℂ) + 1 - x) := by
  induction M with
  | zero =>
    rw [Finset.sum_range_one]
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero]
    ring
  | succ M ih =>
    have hx0 : (x : ℂ) ≠ 0 := Complex.integerComplement.ne_zero hz
    have hA : (x : ℂ) + ((M : ℂ) + 1) ≠ 0 := by
      simpa using Complex.integerComplement_add_ne_zero hz (M + 1 : ℤ)
    have hB : (x : ℂ) - ((M : ℂ) + 1) ≠ 0 := by
      simpa [sub_eq_add_neg] using Complex.integerComplement_add_ne_zero hz (-(M + 1) : ℤ)
    have hC : (M : ℂ) + 1 - x ≠ 0 := by
      intro h; apply hB; rw [sub_eq_zero] at h ⊢; exact h.symm
    have hD : (M : ℂ) + 1 + x ≠ 0 := by
      rw [add_comm ((M : ℂ) + 1) x]; exact hA
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    push_cast
    field_simp
    ring

/-- The boundary term tends to `0`. -/
lemma tendsto_boundary {x : ℝ} :
    Tendsto (fun M : ℕ => 1 / ((M : ℂ) + 1 - x)) atTop (𝓝 0) := by
  simp only [one_div]
  apply tendsto_inv₀_cobounded.comp
  rw [← tendsto_norm_atTop_iff_cobounded]
  apply tendsto_atTop_mono (f := fun M : ℕ => (M : ℝ) - ‖(x : ℂ) - 1‖)
  · intro M
    have : (M : ℂ) + 1 - x = (M : ℂ) - ((x : ℂ) - 1) := by ring
    rw [this]
    calc (M : ℝ) - ‖(x : ℂ) - 1‖ = ‖(M : ℂ)‖ - ‖(x : ℂ) - 1‖ := by rw [Complex.norm_natCast]
      _ ≤ ‖(M : ℂ) - ((x : ℂ) - 1)‖ := norm_sub_norm_le _ _
  · exact tendsto_atTop_add_const_right atTop (-‖(x : ℂ) - 1‖) tendsto_natCast_atTop_atTop

lemma hasSum_cot_diff {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + x) - 1 / ((n : ℂ) + 1 - x))
      ((π : ℂ) * Complex.cot ((π : ℂ) * (x : ℂ))) := by
  have hz := mem_integerComplement_of_mem_Ioo hx0 hx1
  have hsumc : Summable (fun n : ℕ => 1 / ((x : ℂ) - (n + 1)) + 1 / ((x : ℂ) + (n + 1))) :=
    Summable_cotTerm hz
  have htcot : HasSum (fun n : ℕ => 1 / ((x : ℂ) - (n + 1)) + 1 / ((x : ℂ) + (n + 1)))
      ((π : ℂ) * Complex.cot ((π : ℂ) * (x : ℂ)) - 1 / (x : ℂ)) := by
    rw [cot_series_rep' hz]; exact hsumc.hasSum
  have hpc := htcot.tendsto_sum_nat
  have hpd : Tendsto
      (fun M : ℕ => ∑ n ∈ Finset.range (M + 1), (1 / ((n : ℂ) + x) - 1 / ((n : ℂ) + 1 - x)))
      atTop (𝓝 ((π : ℂ) * Complex.cot ((π : ℂ) * (x : ℂ)))) := by
    have hfun : (fun M : ℕ => ∑ n ∈ Finset.range (M + 1),
          (1 / ((n : ℂ) + x) - 1 / ((n : ℂ) + 1 - x)))
        = fun M : ℕ => 1 / (x : ℂ)
            + (∑ m ∈ Finset.range M, (1 / ((x : ℂ) - (m + 1)) + 1 / ((x : ℂ) + (m + 1))))
            - 1 / ((M : ℂ) + 1 - x) := funext (telescope hz)
    rw [hfun]
    have hlim : (π : ℂ) * Complex.cot ((π : ℂ) * (x : ℂ))
        = 1 / (x : ℂ) + ((π : ℂ) * Complex.cot ((π : ℂ) * (x : ℂ)) - 1 / (x : ℂ)) - 0 := by ring
    rw [hlim]
    exact (tendsto_const_nhds.add hpc).sub tendsto_boundary
  rw [hasSum_iff_tendsto_nat_of_summable_norm (summable_norm_diff hx0 hx1)]
  exact (tendsto_add_atTop_iff_nat 1).mp hpd

/-- One-sided difference bound for `t ↦ t^(-s)` via Bernoulli's inequality. -/
lemma diff_rpow_le {u v s : ℝ} (hu : 0 < u) (huv : u ≤ v) (hs : 1 ≤ s) :
    u ^ (-s) - v ^ (-s) ≤ s * (v - u) * u ^ (-s - 1) := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hr : 0 < u / v := div_pos hu hv
  have hb : 1 + s * (u / v - 1) ≤ (u / v) ^ s := by
    have h := one_add_mul_self_le_rpow_one_add (s := u / v - 1) (by linarith [hr.le]) hs
    simpa using h
  -- v^(-s) = u^(-s) * (u/v)^s
  have hsplit : v ^ (-s) = u ^ (-s) * (u / v) ^ s := by
    rw [Real.div_rpow hu.le hv.le, Real.rpow_neg hu.le, Real.rpow_neg hv.le]
    field_simp
  have hune : (0:ℝ) ≤ u ^ (-s) := (Real.rpow_pos_of_pos hu _).le
  have step1 : u ^ (-s) - v ^ (-s) ≤ u ^ (-s) * (s * (1 - u / v)) := by
    rw [hsplit]
    have : u ^ (-s) - u ^ (-s) * (u / v) ^ s = u ^ (-s) * (1 - (u / v) ^ s) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ hune
    linarith [hb]
  have hfrac : 1 - u / v = (v - u) / v := by field_simp
  have step2 : u ^ (-s) * (s * (1 - u / v)) ≤ u ^ (-s) * (s * ((v - u) / u)) := by
    rw [hfrac]
    apply mul_le_mul_of_nonneg_left _ hune
    apply mul_le_mul_of_nonneg_left _ (by linarith : (0:ℝ) ≤ s)
    apply div_le_div_of_nonneg_left (by linarith) hu huv
  have hpow : u ^ (-s) * (s * ((v - u) / u)) = s * (v - u) * u ^ (-s - 1) := by
    rw [Real.rpow_sub hu, Real.rpow_neg hu.le, Real.rpow_one]
    field_simp
  linarith [step1, step2, hpow.le, hpow.ge]

/-- Rewrite the complex `s`-summand as the coercion of a real expression (for `s` real). -/
lemma F_eq_ofReal {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (s : ℝ) (n : ℕ) :
    (1 / ((n : ℂ) + x) ^ (s : ℂ) - 1 / ((n : ℂ) + 1 - x) ^ (s : ℂ)) / 2
      = ((( ((n : ℝ) + x) ^ (-s) - ((n : ℝ) + 1 - x) ^ (-s)) / 2 : ℝ) : ℂ) := by
  have hp1 : (0 : ℝ) ≤ (n : ℝ) + x := add_nonneg (Nat.cast_nonneg n) hx0.le
  have hp2 : (0 : ℝ) ≤ (n : ℝ) + 1 - x := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have h1 : ((n : ℂ) + x) = (((n : ℝ) + x : ℝ) : ℂ) := by push_cast; ring
  have h2 : ((n : ℂ) + 1 - x) = (((n : ℝ) + 1 - x : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, ← Complex.ofReal_cpow hp1, ← Complex.ofReal_cpow hp2]
  rw [Real.rpow_neg hp1, Real.rpow_neg hp2]
  push_cast
  ring

/-- Uniform bound for the real difference of `rpow`s, for `n ≥ 1`. -/
lemma F_abs_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    {n : ℕ} (hn : 1 ≤ n) :
    |((n : ℝ) + x) ^ (-s) - ((n : ℝ) + 1 - x) ^ (-s)| ≤ 2 * |1 - 2 * x| * (1 / (n : ℝ) ^ 2) := by
  have hw : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hwpos : (0 : ℝ) < (n : ℝ) := by linarith
  -- the pointwise bound for `u ≤ v`
  have core : ∀ u v : ℝ, 1 ≤ u → (n : ℝ) ≤ u → u ≤ v → v - u = |1 - 2 * x| →
      u ^ (-s) - v ^ (-s) ≤ 2 * |1 - 2 * x| * (1 / (n : ℝ) ^ 2) := by
    intro u v hu1 hwu huv hvu
    have hu : (0 : ℝ) < u := by linarith
    have hpb : u ^ (-s - 1) ≤ 1 / (n : ℝ) ^ 2 := by
      have e1 : u ^ (-s - 1) ≤ u ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
      have e2 : u ^ (-2 : ℝ) ≤ (n : ℝ) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hwpos hwu (by norm_num)
      have e3 : (n : ℝ) ^ (-2 : ℝ) = 1 / (n : ℝ) ^ 2 := by
        rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hwpos.le, Real.rpow_two, one_div]
      linarith [e1, e2, e3.le, e3.ge]
    have h1 := diff_rpow_le hu huv hs1
    have hrn : (0 : ℝ) ≤ u ^ (-s - 1) := (Real.rpow_pos_of_pos hu _).le
    calc u ^ (-s) - v ^ (-s) ≤ s * (v - u) * u ^ (-s - 1) := h1
      _ = s * |1 - 2 * x| * u ^ (-s - 1) := by rw [hvu]
      _ ≤ 2 * |1 - 2 * x| * (1 / (n : ℝ) ^ 2) := by
          apply mul_le_mul _ hpb hrn (by positivity)
          apply mul_le_mul hs2 le_rfl (abs_nonneg _) (by norm_num)
  rcases le_total x (1 / 2) with hx | hx
  · have huv : (n : ℝ) + x ≤ (n : ℝ) + 1 - x := by linarith
    have hnn : 0 ≤ ((n : ℝ) + x) ^ (-s) - ((n : ℝ) + 1 - x) ^ (-s) := by
      have := Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < (n:ℝ)+x) huv (by linarith : -s ≤ 0)
      linarith
    rw [abs_of_nonneg hnn]
    exact core _ _ (by linarith) (by linarith) huv (by rw [abs_of_nonneg (by linarith)]; ring)
  · have huv : (n : ℝ) + 1 - x ≤ (n : ℝ) + x := by linarith
    have hnn : 0 ≤ ((n : ℝ) + 1 - x) ^ (-s) - ((n : ℝ) + x) ^ (-s) := by
      have := Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < (n:ℝ)+1-x) huv (by linarith : -s ≤ 0)
      linarith
    rw [abs_sub_comm, abs_of_nonneg hnn]
    exact core _ _ (by linarith) (by linarith) huv (by rw [abs_of_nonpos (by linarith)]; ring)

/-- Bound for the `n = 0` term. -/
lemma F0_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    |x ^ (-s) - (1 - x) ^ (-s)| ≤ x ^ (-2 : ℝ) + (1 - x) ^ (-2 : ℝ) := by
  have hxx : (0 : ℝ) < 1 - x := by linarith
  calc |x ^ (-s) - (1 - x) ^ (-s)| ≤ |x ^ (-s)| + |(1 - x) ^ (-s)| := abs_sub _ _
    _ = x ^ (-s) + (1 - x) ^ (-s) := by
        rw [abs_of_nonneg (Real.rpow_nonneg hx0.le _), abs_of_nonneg (Real.rpow_nonneg hxx.le _)]
    _ ≤ x ^ (-2 : ℝ) + (1 - x) ^ (-2 : ℝ) := by
        apply add_le_add
        · exact Real.rpow_le_rpow_of_exponent_ge hx0 (by linarith) (by linarith)
        · exact Real.rpow_le_rpow_of_exponent_ge hxx (by linarith) (by linarith)

/-- **Special value.** For `0 < x < 1`, the odd Hurwitz zeta value at `1` is `(π/2) cot(π x)`. -/
lemma hurwitzZetaOdd_ofReal_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    hurwitzZetaOdd (x : UnitAddCircle) 1 = (π : ℂ) / 2 * Complex.cot ((π : ℂ) * (x : ℂ)) := by
  classical
  set f : ℝ → ℕ → ℂ :=
    fun s n => (1 / ((n : ℂ) + x) ^ (s : ℂ) - 1 / ((n : ℂ) + 1 - x) ^ (s : ℂ)) / 2 with hf_def
  set g : ℕ → ℂ := fun n => (1 / ((n : ℂ) + x) - 1 / ((n : ℂ) + 1 - x)) / 2 with hg_def
  set B0 : ℝ := x ^ (-2 : ℝ) + (1 - x) ^ (-2 : ℝ) with hB0_def
  set bnd : ℕ → ℝ :=
    fun n => 2 * |1 - 2 * x| * (1 / (n : ℝ) ^ 2) + (if n = 0 then B0 else 0) with hbnd_def
  -- Summability of the bound
  have hbnd_summable : Summable bnd := by
    apply Summable.add
    · exact (summable_one_div_nat_pow.mpr (le_refl 2)).mul_left _
    · apply summable_of_ne_finset_zero (s := {0})
      intro n hn
      simp only [Finset.mem_singleton] at hn
      simp [hn]
  -- Termwise limits
  have hab : ∀ n, Tendsto (fun s : ℝ => f s n) (𝓝[>] (1 : ℝ)) (𝓝 (g n)) := by
    intro n
    have hcast : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
      have : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝 1) (𝓝 ((1 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    have hA : ((n : ℂ) + x) ≠ 0 := by
      rw [show ((n : ℂ) + x) = (((n : ℝ) + x : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_ne_zero.mpr (by positivity)
    have hB : ((n : ℂ) + 1 - x) ≠ 0 := by
      rw [show ((n : ℂ) + 1 - x) = (((n : ℝ) + 1 - x : ℝ) : ℂ) by push_cast; ring]
      refine Complex.ofReal_ne_zero.mpr ?_
      have : (0 : ℝ) < (n : ℝ) + 1 - x := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      linarith
    have tA : Tendsto (fun s : ℝ => ((n : ℂ) + x) ^ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 ((n : ℂ) + x)) := by
      have := hcast.const_cpow (a := (n : ℂ) + x) (Or.inl hA)
      simpa using this
    have tB : Tendsto (fun s : ℝ => ((n : ℂ) + 1 - x) ^ (s : ℂ)) (𝓝[>] (1 : ℝ))
        (𝓝 ((n : ℂ) + 1 - x)) := by
      have := hcast.const_cpow (a := (n : ℂ) + 1 - x) (Or.inl hB)
      simpa using this
    have hcA : Tendsto (fun _ : ℝ => (1 : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := tendsto_const_nhds
    have hcB : Tendsto (fun _ : ℝ => (1 : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := tendsto_const_nhds
    have := ((hcA.div tA hA).sub (hcB.div tB hB)).div_const 2
    simpa [hf_def, hg_def] using this
  -- Uniform bound
  have hbound_ev : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), ∀ n, ‖f s n‖ ≤ bnd n := by
    have h2 : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), s < 2 :=
      (isOpen_Iio.eventually_mem (show (1 : ℝ) ∈ Set.Iio 2 by norm_num)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, h2] with s hs1 hs2 n
    have hs1' : (1 : ℝ) ≤ s := le_of_lt hs1
    have hs2' : s ≤ 2 := le_of_lt hs2
    simp only [hf_def]
    rw [F_eq_ofReal hx0 hx1 s n, Complex.norm_real, Real.norm_eq_abs, abs_div,
      show |(2 : ℝ)| = 2 by norm_num]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [hbnd_def]
      simp only [Nat.cast_zero, if_pos rfl]
      have : |((0 : ℝ) + x) ^ (-s) - ((0 : ℝ) + 1 - x) ^ (-s)| / 2 ≤ B0 := by
        rw [show ((0 : ℝ) + x) = x by ring, show ((0 : ℝ) + 1 - x) = 1 - x by ring]
        have := F0_bound hx0 hx1 hs1' hs2'
        rw [hB0_def]; linarith [abs_nonneg (x ^ (-s) - (1 - x) ^ (-s))]
      simpa using this
    · have hn1 : 1 ≤ n := hn
      have hb := F_abs_bound hx0 hx1 hs1' hs2' hn1
      rw [hbnd_def]
      have hne : n ≠ 0 := by omega
      simp only [if_neg hne, add_zero]
      have hnp : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      have habs : (0 : ℝ) ≤ |1 - 2 * x| := abs_nonneg _
      have : |((n : ℝ) + x) ^ (-s) - ((n : ℝ) + 1 - x) ^ (-s)| / 2
          ≤ 2 * |1 - 2 * x| * (1 / (n : ℝ) ^ 2) := by
        have h2b : |((n : ℝ) + x) ^ (-s) - ((n : ℝ) + 1 - x) ^ (-s)| / 2
            ≤ (2 * |1 - 2 * x| * (1 / (n : ℝ) ^ 2)) / 2 := by
          apply div_le_div_of_nonneg_right hb (by norm_num)
        have h3b : (2 * |1 - 2 * x| * (1 / (n : ℝ) ^ 2)) / 2 ≤ 2 * |1 - 2 * x| * (1 / (n : ℝ) ^ 2) := by
          have : (0 : ℝ) ≤ 2 * |1 - 2 * x| * (1 / (n : ℝ) ^ 2) := by positivity
          linarith
        linarith
      exact this
  -- Tannery's theorem
  have htan : Tendsto (fun s : ℝ => ∑' n, f s n) (𝓝[>] (1 : ℝ)) (𝓝 (∑' n, g n)) :=
    tendsto_tsum_of_dominated_convergence hbnd_summable hab hbound_ev
  -- Sum of `g`
  have hg_sum : ∑' n, g n = (π : ℂ) / 2 * Complex.cot ((π : ℂ) * (x : ℂ)) := by
    have h := (hasSum_cot_diff hx0 hx1).div_const 2
    have : (fun n : ℕ => (1 / ((n : ℂ) + x) - 1 / ((n : ℂ) + 1 - x)) / 2) = g := by
      rw [hg_def]
    rw [this] at h
    rw [h.tsum_eq]; ring
  -- On `s > 1`, the tsum is `hurwitzZetaOdd`
  have hf_eq : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      ∑' n, f s n = hurwitzZetaOdd (x : UnitAddCircle) (s : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (1 : ℝ) < s := hs
    have hsc : 1 < ((s : ℂ)).re := by simpa using hs'
    have := hasSum_nat_hurwitzZetaOdd_of_mem_Icc (a := x) ⟨hx0.le, hx1.le⟩ hsc
    simp only [hf_def]
    exact this.tsum_eq
  -- Combine: limit is `hurwitzZetaOdd ↑x 1`
  have hcont : Tendsto (fun s : ℝ => hurwitzZetaOdd (x : UnitAddCircle) (s : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (hurwitzZetaOdd (x : UnitAddCircle) 1)) := by
    have hc : ContinuousAt (hurwitzZetaOdd (x : UnitAddCircle)) (1 : ℂ) :=
      (differentiable_hurwitzZetaOdd _).continuous.continuousAt
    have hcast : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
      have : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝 1) (𝓝 ((1 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    exact hc.tendsto.comp hcast
  have htan' : Tendsto (fun s : ℝ => hurwitzZetaOdd (x : UnitAddCircle) (s : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (∑' n, g n)) := by
    apply htan.congr'
    filter_upwards [hf_eq] with s hs using hs
  have := tendsto_nhds_unique hcont htan'
  rw [this, hg_sum]


/-! ## Main theorems. -/

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

open ArithmeticFunction in
/-- For `1 < re s`, the L-series of `zetaMul χ` equals `ζ(s) · L(χ,s)`. -/
private lemma LSeries_zetaMul_eq (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * LFunction χ s = LSeries (χ.zetaMul ·) s := by
  rw [zetaMul, ← coe_mul, LSeries_convolution']
  · congr 1
    · simp_rw [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
    · rw [χ.LFunction_eq_LSeries hs]
      exact LSeries_congr (fun {n} hn => χ.apply_eq_toArithmeticFunction_apply hn) s
  · exact LSeriesSummable_zeta_iff.mpr hs
  · exact (LSeriesSummable_congr _ fun h ↦ (χ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
      ZMod.LSeriesSummable_of_one_lt_re χ hs

/-- For real `σ > 1`, `L(χ, σ)` is a positive real number (when `χ² = 1`). -/
private lemma LFunction_pos_of_real {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1)
    {σ : ℝ} (hσ : 1 < σ) : 0 < LFunction χ (σ : ℂ) := by
  have hσc : 1 < ((σ : ℂ)).re := by simpa using hσ
  -- abscissa bound
  have habs : LSeries.abscissaOfAbsConv (χ.zetaMul ·) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      χ.LSeriesSummable_zetaMul (by simpa using hy)
  have habs' : LSeries.abscissaOfAbsConv (χ.zetaMul ·) < (σ : ℝ) :=
    lt_of_le_of_lt habs (by exact_mod_cast hσ)
  -- positivity of the LSeries of zetaMul
  have hP : (0 : ℂ) < LSeries (χ.zetaMul ·) σ := by
    refine LSeries.positive (fun n => zetaMul_nonneg hχ n) ?_ habs'
    have : χ.zetaMul 1 = 1 := χ.isMultiplicative_zetaMul.map_one
    rw [this]; exact one_pos
  -- positivity of riemannZeta σ
  have hZ : (0 : ℂ) < riemannZeta (σ : ℂ) := by
    rw [← LSeries_one_eq_riemannZeta hσc]
    refine LSeries.positive (a := (1 : ℕ → ℂ)) (fun n => ?_) ?_ ?_
    · simp
    · simp
    · rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hσ
  -- combine: L = P / Z, positive / positive
  have hmul : riemannZeta (σ : ℂ) * LFunction χ (σ : ℂ) = LSeries (χ.zetaMul ·) σ :=
    LSeries_zetaMul_eq χ hσc
  -- Z and P are positive reals
  have hZr : riemannZeta (σ : ℂ) = ((riemannZeta (σ : ℂ)).re : ℂ) :=
    eq_re_of_ofReal_le (by simpa using hZ.le)
  have hPr : LSeries (χ.zetaMul ·) σ = ((LSeries (χ.zetaMul ·) σ).re : ℂ) :=
    eq_re_of_ofReal_le (by simpa using hP.le)
  set Zr := (riemannZeta (σ : ℂ)).re with hZrdef
  set Pr := (LSeries (χ.zetaMul ·) σ).re with hPrdef
  have hZrpos : 0 < Zr := by have := (pos_iff.mp hZ).1; simpa [hZrdef] using this
  have hPrpos : 0 < Pr := by have := (pos_iff.mp hP).1; simpa [hPrdef] using this
  have hLeq : LFunction χ (σ : ℂ) = ((Pr / Zr : ℝ) : ℂ) := by
    have hZne : (Zr : ℂ) ≠ 0 := by
      simp only [ne_eq, ofReal_eq_zero]; exact hZrpos.ne'
    rw [hZr, hPr] at hmul
    push_cast at hmul ⊢
    field_simp
    linear_combination hmul
  rw [hLeq]
  rw [zero_lt_real]
  positivity

/-- **Target 1.** If `χ` is a nontrivial quadratic character, then `L(χ, 1)` is a positive
real number. -/
theorem LFunction_one_pos (hχ : χ ^ 2 = 1) (hχ1 : χ ≠ 1) :
    0 < (DirichletCharacter.LFunction χ 1).re ∧ (DirichletCharacter.LFunction χ 1).im = 0 := by
  -- Continuity at 1
  have hcont : ContinuousAt (LFunction χ) (1 : ℂ) :=
    (differentiable_LFunction hχ1).continuous.continuousAt
  -- ofReal tends to 1 from the right
  have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) := by
    have : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝 1) (𝓝 ((1 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun σ : ℝ => LFunction χ (σ : ℂ)) (𝓝[>] 1) (𝓝 (LFunction χ 1)) :=
    hcont.tendsto.comp hmap
  -- each value for σ > 1 is a positive real
  have hpos : ∀ᶠ σ : ℝ in 𝓝[>] 1, (0 : ℂ) < LFunction χ (σ : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact LFunction_pos_of_real hχ hσ
  -- limit gives im = 0 and re ≥ 0
  have him : (LFunction χ 1).im = 0 := by
    have h1 : Tendsto (fun σ : ℝ => (LFunction χ (σ : ℂ)).im) (𝓝[>] 1)
        (𝓝 (LFunction χ 1).im) := (Complex.continuous_im.tendsto _).comp hg
    have hle : (LFunction χ 1).im ≤ 0 :=
      le_of_tendsto h1 (by filter_upwards [hpos] with σ hσ using ((pos_iff.mp hσ).2).symm.le)
    have hge : 0 ≤ (LFunction χ 1).im :=
      ge_of_tendsto h1 (by filter_upwards [hpos] with σ hσ using ((pos_iff.mp hσ).2).le)
    exact le_antisymm hle hge
  have hre : 0 ≤ (LFunction χ 1).re := by
    have h1 : Tendsto (fun σ : ℝ => (LFunction χ (σ : ℂ)).re) (𝓝[>] 1)
        (𝓝 (LFunction χ 1).re) := (Complex.continuous_re.tendsto _).comp hg
    exact ge_of_tendsto h1 (by filter_upwards [hpos] with σ hσ using (pos_iff.mp hσ).1.le)
  -- combine with nonvanishing
  have hne : LFunction χ 1 ≠ 0 := LFunction_apply_one_ne_zero hχ1
  refine ⟨hre.lt_of_ne ?_, him⟩
  intro h
  exact hne (Complex.ext h.symm him)


/-- **Target 2.** cot-sum formula for `L(χ,1)` of an odd character. -/
theorem LFunction_one_eq_cot_sum {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hodd : χ (-1) = -1) :
    DirichletCharacter.LFunction χ 1
      = (π / (2 * N)) * ∑ a ∈ Finset.Ico 1 N, χ (a : ZMod N) * Complex.cot (π * a / N) := by
  -- Basic facts about N
  have hN : N ≠ 1 := by
    rintro rfl
    rw [show (-1 : ZMod 1) = 1 from Subsingleton.elim _ _, map_one] at hodd
    exact absurd hodd (by norm_num)
  have hN1 : 1 < N := lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) (Ne.symm hN)
  haveI : Fact (1 < N) := Fact.mk hN1
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hNre : (0 : ℝ) < N := by exact_mod_cast hN1.trans_le' (by norm_num)
  -- χ is odd as a function
  have hΦ : Function.Odd (χ : ZMod N → ℂ) := by
    intro a
    rw [show (-a) = (-1) * a by ring, map_mul, hodd, neg_one_mul]
  -- χ 0 = 0
  have hχ0 : χ (0 : ZMod N) = 0 := MulChar.map_zero χ
  -- unfold to ZMod.LFunction and apply the odd formula
  have hL : DirichletCharacter.LFunction χ 1 = ZMod.LFunction (χ : ZMod N → ℂ) 1 := rfl
  rw [hL, ZMod.LFunction_def_odd hΦ, Complex.cpow_neg_one]
  -- reindex the sum over ZMod N to Finset.range N
  have reindex : (∑ j : ZMod N, χ j * hurwitzZetaOdd (ZMod.toAddCircle j) 1)
      = ∑ a ∈ Finset.range N,
          χ (a : ZMod N) * hurwitzZetaOdd (ZMod.toAddCircle (a : ZMod N)) 1 := by
    apply Finset.sum_nbij' (i := ZMod.val) (j := (Nat.cast : ℕ → ZMod N))
    · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
    · intro a _; exact Finset.mem_univ _
    · intro a _; exact ZMod.natCast_zmod_val a
    · intro a ha; exact ZMod.val_cast_of_lt (Finset.mem_range.mp ha)
    · intro a _; rw [ZMod.natCast_zmod_val]
  rw [reindex]
  -- drop the a = 0 term (χ 0 = 0)
  set G : ℕ → ℂ :=
    fun a => χ (a : ZMod N) * hurwitzZetaOdd (ZMod.toAddCircle (a : ZMod N)) 1 with hG_def
  have hF0 : G 0 = 0 := by simp only [hG_def, Nat.cast_zero, hχ0, zero_mul]
  have hsplit : ∑ a ∈ Finset.range N, G a = ∑ a ∈ Finset.Ico 1 N, G a := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive G (Nat.zero_le 1) hN1.le]
    have h01 : ∑ a ∈ Finset.Ico 0 1, G a = 0 := by
      rw [Nat.Ico_zero_eq_range, Finset.sum_range_one]; exact hF0
    rw [h01, zero_add]
  rw [hsplit]
  -- compute each Hurwitz zeta value
  have hterm : ∀ a ∈ Finset.Ico 1 N,
      G a = χ (a : ZMod N) * ((π : ℂ) / 2 * Complex.cot ((π : ℂ) * a / N)) := by
    intro a ha
    rw [Finset.mem_Ico] at ha
    obtain ⟨ha1, ha2⟩ := ha
    have hare : (0 : ℝ) < a := by exact_mod_cast ha1
    have hx0 : (0 : ℝ) < (a : ℝ) / (N : ℝ) := div_pos hare hNre
    have hx1 : (a : ℝ) / (N : ℝ) < 1 := (div_lt_one hNre).mpr (by exact_mod_cast ha2)
    rw [hG_def]
    simp only
    rw [ZMod.toAddCircle_natCast, hurwitzZetaOdd_ofReal_one hx0 hx1]
    push_cast
    rw [← mul_div_assoc]
  rw [Finset.sum_congr rfl hterm, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  field_simp


end DirichletCharacter
end

/- ================= inlined from Common.lean ================= -/
section

open Complex Finset

noncomputable section

/-- OEIS A048153: `∑_{k<n} k² mod n`. -/
def A048153 (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, k ^ 2 % n

/-- Number of `k < n` with `n ∣ k²`. -/
def Zc (n : ℕ) : ℕ := ((Finset.range n).filter (fun k => k ^ 2 % n = 0)).card

/-- Real cotangent. -/
noncomputable def rcot (x : ℝ) : ℝ := Real.cos x / Real.sin x

/-- The quadratic Gauss sum `S t m = ∑_{k<m} exp(2πi t k²/m)` (from `GaussGen`). -/
abbrev S (t m : ℕ) : ℂ := GaussGen.S t m

/-- The per-divisor sum `P m = ∑_{s unit mod m, 1≤s<m} cot(πs/m)·Im S(s,m)`. -/
noncomputable def P (m : ℕ) : ℝ :=
  ∑ s ∈ (Finset.Ico 1 m).filter (fun s => Nat.Coprime s m),
    rcot (Real.pi * (s : ℝ) / (m : ℝ)) * (S s m).im
end
end

/- ================= inlined from OddTwist.lean ================= -/
section

open Complex Finset

noncomputable section

namespace OddTwist

/-- The integer-twisted quadratic Gauss sum. -/
def Sz (s : ℤ) (n : ℕ) : ℂ :=
  ∑ k ∈ range n, Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * (k : ℂ) ^ 2 / (n : ℂ))

theorem S_eq_Sz (t n : ℕ) : S t n = Sz (t : ℤ) n := by
  unfold Sz
  show GaussGen.S t n = _
  unfold GaussGen.S
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring_nf

/-- Periodicity of a single term in the modulus argument. -/
theorem expterm_periodic (s : ℤ) (n : ℕ) (hn : n ≠ 0) (a b : ℤ) (h : (n : ℤ) ∣ (a - b)) :
    Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * (a : ℂ) ^ 2 / (n : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * (b : ℂ) ^ 2 / (n : ℂ)) := by
  obtain ⟨d, hd⟩ := h
  set c : ℤ := s * d * (a + b) with hc
  have key : (s : ℤ) * (a ^ 2 - b ^ 2) = (n : ℤ) * c := by
    have hfac : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    rw [hfac, hd, hc]; ring
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hcast : (s : ℂ) * ((a : ℂ) ^ 2 - (b : ℂ) ^ 2) = (n : ℂ) * (c : ℂ) := by
    exact_mod_cast key
  have hdiv : (s : ℂ) * ((a : ℂ) ^ 2 - (b : ℂ) ^ 2) / (n : ℂ) = (c : ℂ) := by
    rw [hcast]; field_simp
  have goal_eq : (2 * Real.pi * Complex.I * (s : ℂ) * (a : ℂ) ^ 2 / (n : ℂ))
      = (2 * Real.pi * Complex.I * (s : ℂ) * (b : ℂ) ^ 2 / (n : ℂ))
        + (c : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [← hdiv]; field_simp; ring
  rw [goal_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Factorization of a single CRT term. -/
theorem exp_factor (s : ℤ) (m₁ m₂ : ℕ) (hm1 : m₁ ≠ 0) (hm2 : m₂ ≠ 0) (x y : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)
        * (((m₂ * x + m₁ * y : ℕ) : ℂ)) ^ 2 / ((m₁ * m₂ : ℕ) : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * ((s * m₂ : ℤ) : ℂ) * (x : ℂ) ^ 2 / (m₁ : ℂ))
        * Complex.exp (2 * Real.pi * Complex.I * ((s * m₁ : ℤ) : ℂ) * (y : ℂ) ^ 2 / (m₂ : ℂ)) := by
  have hm1' : (m₁ : ℂ) ≠ 0 := by exact_mod_cast hm1
  have hm2' : (m₂ : ℂ) ≠ 0 := by exact_mod_cast hm2
  have hEq : (2 * Real.pi * Complex.I * (s : ℂ)
        * (((m₂ * x + m₁ * y : ℕ) : ℂ)) ^ 2 / ((m₁ * m₂ : ℕ) : ℂ))
      = (2 * Real.pi * Complex.I * ((s * m₂ : ℤ) : ℂ) * (x : ℂ) ^ 2 / (m₁ : ℂ))
        + (2 * Real.pi * Complex.I * ((s * m₁ : ℤ) : ℂ) * (y : ℂ) ^ 2 / (m₂ : ℂ))
        + (((2 * s * (x : ℤ) * (y : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
    ring
  rw [hEq, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `Sz` as a sum over `ZMod n`. -/
theorem Sz_zmod (s : ℤ) (n : ℕ) [NeZero n] :
    Sz s n = ∑ a : ZMod n,
      Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * ((a.val : ℕ) : ℂ) ^ 2 / (n : ℂ)) := by
  unfold Sz
  apply Finset.sum_nbij' (fun k : ℕ => (k : ZMod n)) (fun a : ZMod n => a.val)
  · intro a _; exact Finset.mem_univ _
  · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro k hk; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hk)
  · intro a _; exact ZMod.natCast_rightInverse a
  · intro k hk
    have : ((k : ZMod n).val : ℂ) = (k : ℂ) := by
      rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hk)]
    rw [this]

/-- Multiplication by a unit is a bijection of `ZMod n`. -/
def unitMulEquiv {n : ℕ} (u : (ZMod n)ˣ) : ZMod n ≃ ZMod n where
  toFun x := (u : ZMod n) * x
  invFun x := ((u⁻¹ : (ZMod n)ˣ) : ZMod n) * x
  left_inv x := by
    show ((u⁻¹ : (ZMod n)ˣ) : ZMod n) * ((u : ZMod n) * x) = x
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  right_inv x := by
    show (u : ZMod n) * (((u⁻¹ : (ZMod n)ˣ) : ZMod n) * x) = x
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

/-- **Block 1 — CRT multiplicativity of the Gauss sum.** -/
theorem block1 (s : ℤ) (m₁ m₂ : ℕ) (hm1 : m₁ ≠ 0) (hm2 : m₂ ≠ 0) (h : m₁.Coprime m₂) :
    Sz s (m₁ * m₂) = Sz (s * m₂) m₁ * Sz (s * m₁) m₂ := by
  haveI : NeZero m₁ := ⟨hm1⟩
  haveI : NeZero m₂ := ⟨hm2⟩
  haveI : NeZero (m₁ * m₂) := ⟨Nat.mul_ne_zero hm1 hm2⟩
  have hc1 : m₂.Coprime m₁ := h.symm
  set u₁ : (ZMod m₁)ˣ := ZMod.unitOfCoprime m₂ hc1 with hu1
  set u₂ : (ZMod m₂)ˣ := ZMod.unitOfCoprime m₁ h with hu2
  set e := ZMod.chineseRemainder h with he
  set Φ : ZMod m₁ × ZMod m₂ ≃ ZMod (m₁ * m₂) :=
    ((unitMulEquiv u₁).prodCongr (unitMulEquiv u₂)).trans e.toEquiv.symm with hΦ
  set g : ZMod (m₁ * m₂) → ℂ :=
    fun a => Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * ((a.val : ℕ) : ℂ) ^ 2
      / ((m₁ * m₂ : ℕ) : ℂ)) with hg
  rw [Sz_zmod s (m₁ * m₂)]
  show (∑ a, g a) = _
  rw [← Equiv.sum_comp Φ g]
  -- term identity
  have hterm : ∀ (x : ZMod m₁) (y : ZMod m₂),
      g (Φ (x, y))
        = Complex.exp (2 * Real.pi * Complex.I * ((s * m₂ : ℤ) : ℂ) * ((x.val : ℕ) : ℂ) ^ 2
            / (m₁ : ℂ))
          * Complex.exp (2 * Real.pi * Complex.I * ((s * m₁ : ℤ) : ℂ) * ((y.val : ℕ) : ℂ) ^ 2
            / (m₂ : ℂ)) := by
    intro x y
    -- CRT value of Φ (x,y)
    have he_eval : e (((m₂ * x.val + m₁ * y.val : ℕ) : ZMod (m₁ * m₂)))
        = ((↑u₁ : ZMod m₁) * x, (↑u₂ : ZMod m₂) * y) := by
      rw [map_natCast]
      refine Prod.ext ?_ ?_
      · show ((m₂ * x.val + m₁ * y.val : ℕ) : ZMod m₁) = (↑u₁ : ZMod m₁) * x
        push_cast
        rw [ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_rightInverse x, hu1,
          ZMod.coe_unitOfCoprime]
      · show ((m₂ * x.val + m₁ * y.val : ℕ) : ZMod m₂) = (↑u₂ : ZMod m₂) * y
        push_cast
        rw [ZMod.natCast_self, zero_mul, zero_add, ZMod.natCast_rightInverse y, hu2,
          ZMod.coe_unitOfCoprime]
    have hΦ_apply : Φ (x, y) = e.symm ((↑u₁ : ZMod m₁) * x, (↑u₂ : ZMod m₂) * y) := by
      simp only [hΦ, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map]
      rfl
    have hΦval : Φ (x, y) = ((m₂ * x.val + m₁ * y.val : ℕ) : ZMod (m₁ * m₂)) := by
      rw [hΦ_apply, ← he_eval, e.symm_apply_apply]
    -- divisibility for periodicity
    have hdvd : ((m₁ * m₂ : ℕ) : ℤ)
        ∣ (((Φ (x, y)).val : ℕ) : ℤ) - ((m₂ * x.val + m₁ * y.val : ℕ) : ℤ) := by
      have hvaleq : (Φ (x, y)).val = (m₂ * x.val + m₁ * y.val) % (m₁ * m₂) := by
        rw [hΦval, ZMod.val_natCast]
      rw [hvaleq]
      refine ⟨-(((m₂ * x.val + m₁ * y.val) / (m₁ * m₂) : ℕ) : ℤ), ?_⟩
      have hnm : (m₁ * m₂) * ((m₂ * x.val + m₁ * y.val) / (m₁ * m₂))
          + (m₂ * x.val + m₁ * y.val) % (m₁ * m₂) = (m₂ * x.val + m₁ * y.val) :=
        Nat.div_add_mod _ _
      have hc : ((m₂ * x.val + m₁ * y.val : ℕ) : ℤ)
          = ((m₁ * m₂ : ℕ) : ℤ) * (((m₂ * x.val + m₁ * y.val) / (m₁ * m₂) : ℕ) : ℤ)
            + (((m₂ * x.val + m₁ * y.val) % (m₁ * m₂) : ℕ) : ℤ) := by exact_mod_cast hnm.symm
      linarith [hc]
    -- rewrite g via periodicity then factor
    rw [hg]
    simp only []
    have hc1' : (((Φ (x, y)).val : ℕ) : ℂ) = ((((Φ (x, y)).val : ℕ) : ℤ) : ℂ) := by push_cast; ring
    have hc2' : ((m₂ * x.val + m₁ * y.val : ℕ) : ℂ) = (((m₂ * x.val + m₁ * y.val : ℕ) : ℤ) : ℂ) := by
      push_cast; ring
    rw [hc1', expterm_periodic s (m₁ * m₂) (Nat.mul_ne_zero hm1 hm2)
      (((Φ (x, y)).val : ℕ) : ℤ) ((m₂ * x.val + m₁ * y.val : ℕ) : ℤ) hdvd, ← hc2']
    exact exp_factor s m₁ m₂ hm1 hm2 x.val y.val
  rw [Fintype.sum_prod_type]
  rw [Sz_zmod (s * m₂) m₁, Sz_zmod (s * m₁) m₂, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  exact hterm x y

/-- Periodicity of a linear exponential term. -/
theorem exp_lin_periodic (p : ℕ) (hp : p ≠ 0) (j k : ℤ) (h : (p : ℤ) ∣ (j - k)) :
    Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / (p : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (p : ℂ)) := by
  obtain ⟨d, hd⟩ := h
  have hne : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hcast : (j : ℂ) - (k : ℂ) = (p : ℂ) * (d : ℂ) := by exact_mod_cast hd
  have hdiv : ((j : ℂ) - (k : ℂ)) / (p : ℂ) = (d : ℂ) := by rw [hcast]; field_simp
  have goal_eq : 2 * Real.pi * Complex.I * (j : ℂ) / (p : ℂ)
      = 2 * Real.pi * Complex.I * (k : ℂ) / (p : ℂ) + (d : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [← hdiv]; field_simp; ring
  rw [goal_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `psi` as an exponential. -/
theorem psi_eq_exp (p : ℕ) [NeZero p] (c : ZMod p) :
    GaussGen.psi p c = Complex.exp (2 * Real.pi * Complex.I * ((c.val : ℕ) : ℂ) / (p : ℂ)) := by
  conv_lhs => rw [← ZMod.natCast_rightInverse c, GaussGen.psi_apply_natCast]
  rw [GaussGen.ω, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- Term identity linking the exponential Gauss sum term with `psi`. -/
theorem psi_term (p : ℕ) [NeZero p] (s : ℤ) (a : ZMod p) :
    Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * ((a.val : ℕ) : ℂ) ^ 2 / (p : ℂ))
      = GaussGen.psi p ((s : ZMod p) * a ^ 2) := by
  rw [psi_eq_exp]
  have hL : Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * ((a.val : ℕ) : ℂ) ^ 2 / (p : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * (((s * (a.val : ℤ) ^ 2 : ℤ)) : ℂ) / (p : ℂ)) := by
    push_cast; ring_nf
  rw [hL]
  have hR : (((s : ZMod p) * a ^ 2).val : ℂ) = ((((s : ZMod p) * a ^ 2).val : ℤ) : ℂ) := by
    push_cast; ring
  rw [hR]
  apply exp_lin_periodic p (NeZero.ne p)
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_
  push_cast
  rw [ZMod.natCast_rightInverse a, ZMod.natCast_rightInverse ((s : ZMod p) * a ^ 2)]
  ring

/-- The `ℂ`-valued quadratic character. -/
def chiC (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- Generalized: `∑ ψ(a²) = gaussSum χ ψ` for a nontrivial additive character. -/
theorem sumsq_eq_gaussSum (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1) :
    ∑ a : ZMod p, ψ (a ^ 2) = gaussSum (chiC p) ψ := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have h2 : ∑ a : ZMod p, ψ (a ^ 2)
      = ∑ j : ZMod p, ((#{i : ZMod p | i ^ 2 = j}.toFinset : ℤ) : ℂ) * ψ j := by
    rw [← Finset.sum_fiberwise' Finset.univ (fun k : ZMod p => k ^ 2) ψ]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_const]
    have hset : {i : ZMod p | i ^ 2 = j}.toFinset
        = Finset.univ.filter (fun i : ZMod p => i ^ 2 = j) := by ext i; simp
    rw [hset, nsmul_eq_mul]
    push_cast; ring
  rw [h2]
  have h3 : ∀ j : ZMod p, ((#{i : ZMod p | i ^ 2 = j}.toFinset : ℤ) : ℂ) = chiC p j + 1 := by
    intro j
    rw [quadraticChar_card_sqrts hF j]
    have : chiC p j = ((quadraticChar (ZMod p) j : ℤ) : ℂ) := by
      simp [chiC, MulChar.ringHomComp_apply]
    rw [this]; push_cast; ring
  simp_rw [h3]
  have h4 : ∑ j : ZMod p, (chiC p j + 1) * ψ j
      = (∑ j : ZMod p, chiC p j * ψ j) + ∑ j : ZMod p, ψ j := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; ring
  rw [h4, AddChar.sum_eq_zero_of_ne_one hψ, add_zero]
  rfl

/-- **Block 2 — prime base case.** -/
theorem block2 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (s : ℤ) (hgcd : s.gcd (p : ℤ) = 1) :
    Sz s p = ((jacobiSym s p : ℤ) : ℂ) * Sz 1 p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hŝ0 : (s : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdvd
    have hpg : p ∣ s.gcd (p : ℤ) := Int.dvd_gcd hdvd (dvd_refl _)
    rw [hgcd] at hpg
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp hpg)
  have hSzs : Sz s p = ∑ a : ZMod p, (GaussGen.psi p).mulShift (s : ZMod p) (a ^ 2) := by
    rw [Sz_zmod s p]
    apply Finset.sum_congr rfl
    intro a _
    rw [AddChar.mulShift_apply]
    exact psi_term p s a
  have hSz1 : Sz 1 p = ∑ a : ZMod p, GaussGen.psi p (a ^ 2) := by
    rw [Sz_zmod 1 p]
    apply Finset.sum_congr rfl
    intro a _
    rw [psi_term p 1 a]
    congr 1
    push_cast; ring
  have hpsine : (GaussGen.psi p) ≠ 1 := by
    rw [← AddChar.mulShift_one (GaussGen.psi p)]
    exact GaussGen.psi_primitive p one_ne_zero
  have hg1 : (∑ a : ZMod p, GaussGen.psi p (a ^ 2)) = gaussSum (chiC p) (GaussGen.psi p) :=
    sumsq_eq_gaussSum p hp2 (GaussGen.psi p) hpsine
  have hgs : (∑ a : ZMod p, (GaussGen.psi p).mulShift (s : ZMod p) (a ^ 2))
      = gaussSum (chiC p) ((GaussGen.psi p).mulShift (s : ZMod p)) :=
    sumsq_eq_gaussSum p hp2 _ (GaussGen.psi_primitive p hŝ0)
  have huŝ : IsUnit (s : ZMod p) := isUnit_iff_ne_zero.mpr hŝ0
  have hûval : (↑huŝ.unit : ZMod p) = (s : ZMod p) := huŝ.unit_spec
  have hmulshift := gaussSum_mulShift (chiC p) (GaussGen.psi p) huŝ.unit
  rw [hûval] at hmulshift
  rw [← hgs, ← hSzs, ← hg1, ← hSz1] at hmulshift
  have hchi_jac : chiC p (s : ZMod p) = ((jacobiSym s p : ℤ) : ℂ) := by
    have h1 : chiC p (s : ZMod p) = ((quadraticChar (ZMod p) (s : ZMod p) : ℤ) : ℂ) := by
      simp [chiC, MulChar.ringHomComp_apply]
    rw [h1, show quadraticChar (ZMod p) (s : ZMod p) = legendreSym p s from rfl,
      jacobiSym.legendreSym.to_jacobiSym]
  rw [hchi_jac] at hmulshift
  have hJsq : ((jacobiSym s p : ℤ) : ℂ) ^ 2 = 1 := by
    rw [← Int.cast_pow, jacobiSym.sq_one hgcd, Int.cast_one]
  calc Sz s p = ((jacobiSym s p : ℤ) : ℂ) ^ 2 * Sz s p := by rw [hJsq, one_mul]
    _ = ((jacobiSym s p : ℤ) : ℂ) * (((jacobiSym s p : ℤ) : ℂ) * Sz s p) := by ring
    _ = ((jacobiSym s p : ℤ) : ℂ) * Sz 1 p := by rw [hmulshift]

/-- `exp(2πi t/p) = 1` iff `p ∣ t`. -/
theorem exp_dvd_iff (p : ℕ) (hp : p ≠ 0) (t : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) / (p : ℂ)) = 1 ↔ (p : ℤ) ∣ t := by
  have hpne : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    field_simp at hn
    exact_mod_cast hn
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    have hcast : (t : ℂ) = (p : ℂ) * (d : ℂ) := by exact_mod_cast hd
    rw [hcast]; field_simp

/-- Geometric sum / root-of-unity orthogonality. -/
theorem geom_sum_p (p : ℕ) (hp : p ≠ 0) (t : ℤ) :
    ∑ c ∈ range p, Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (c : ℂ) / (p : ℂ))
      = if (p : ℤ) ∣ t then (p : ℂ) else 0 := by
  have hx : ∀ c : ℕ, Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (c : ℂ) / (p : ℂ))
      = (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) / (p : ℂ))) ^ c := by
    intro c; rw [← Complex.exp_nat_mul]; congr 1; ring
  simp_rw [hx]
  by_cases hdvd : (p : ℤ) ∣ t
  · rw [if_pos hdvd]
    have hx1 : Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) / (p : ℂ)) = 1 :=
      (exp_dvd_iff p hp t).mpr hdvd
    rw [hx1]; simp
  · rw [if_neg hdvd]
    have hxne : Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) / (p : ℂ)) ≠ 1 := by
      intro hcontra
      exact hdvd ((exp_dvd_iff p hp t).mp hcontra)
    have hxp : (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) / (p : ℂ))) ^ p = 1 := by
      rw [← Complex.exp_nat_mul]
      have hpne : (p : ℂ) ≠ 0 := by exact_mod_cast hp
      have : (p : ℂ) * (2 * Real.pi * Complex.I * (t : ℂ) / (p : ℂ)) = (t : ℂ) * (2 * Real.pi * Complex.I) := by
        field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [geom_sum_eq hxne p, hxp, sub_self, zero_div]

/-- **Block 3 — prime-power descent.** -/
theorem block3 (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k) (s : ℤ)
    (hgcd : s.gcd (p : ℤ) = 1) :
    Sz s (p ^ k) = (p : ℂ) * Sz s (p ^ (k - 2)) := by
  have hp0 : p ≠ 0 := hp.pos.ne'
  have hNpos : 0 < p ^ (k - 1) := pow_pos hp.pos _
  have hk1 : p ^ (k - 1) = p ^ (k - 2) * p := by
    rw [← pow_succ]; congr 1; omega
  have hk2 : p ^ k = p ^ (k - 2) * p ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hpk1eq : p ^ k = p ^ (k - 1) * p := by
    rw [← pow_succ]; congr 1; omega
  set A : ℕ → ℂ := fun b =>
    Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * ((b : ℕ) : ℂ) ^ 2 / ((p ^ k : ℕ) : ℂ)) with hA
  -- Step 1: base-`p^(k-1)` reindexing
  have hreindex : Sz s (p ^ k)
      = ∑ x ∈ (range (p ^ (k - 1)) ×ˢ range p), A (x.1 + p ^ (k - 1) * x.2) := by
    rw [Sz]
    apply Finset.sum_nbij' (fun a => (a % p ^ (k - 1), a / p ^ (k - 1)))
      (fun x => x.1 + p ^ (k - 1) * x.2)
    · intro a ha
      rw [Finset.mem_range] at ha
      rw [Finset.mem_product]
      refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ hNpos), Finset.mem_range.mpr ?_⟩
      rw [Nat.div_lt_iff_lt_mul hNpos, mul_comm, ← hpk1eq]; exact ha
    · intro x hx
      rw [Finset.mem_product] at hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [Finset.mem_range] at hx1 hx2 ⊢
      rw [hpk1eq]
      calc x.1 + p ^ (k - 1) * x.2 < p ^ (k - 1) * (x.2 + 1) := by
            rw [Nat.mul_add_one]; omega
        _ ≤ p ^ (k - 1) * p := Nat.mul_le_mul (le_refl _) (by omega)
    · intro a _; exact Nat.mod_add_div a (p ^ (k - 1))
    · intro x hx
      rw [Finset.mem_product] at hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [Finset.mem_range] at hx1 hx2
      refine Prod.ext ?_ ?_
      · show (x.1 + p ^ (k - 1) * x.2) % p ^ (k - 1) = x.1
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx1]
      · show (x.1 + p ^ (k - 1) * x.2) / p ^ (k - 1) = x.2
        rw [Nat.add_mul_div_left _ _ hNpos, Nat.div_eq_of_lt hx1, zero_add]
    · intro a _
      have hma : a % p ^ (k - 1) + p ^ (k - 1) * (a / p ^ (k - 1)) = a := Nat.mod_add_div a _
      rw [hma]
  rw [hreindex, Finset.sum_product]
  dsimp only
  -- Step 2: factor each term
  have hterm3 : ∀ (b c : ℕ), A (b + p ^ (k - 1) * c)
      = A b * Complex.exp (2 * Real.pi * Complex.I * ((2 * s * (b : ℤ) : ℤ) : ℂ) * (c : ℂ) / (p : ℂ)) := by
    intro b c
    simp only [hA]
    have hkey : 2 * Real.pi * Complex.I * (s : ℂ) * (((b + p ^ (k - 1) * c : ℕ)) : ℂ) ^ 2
          / ((p ^ k : ℕ) : ℂ)
        = 2 * Real.pi * Complex.I * (s : ℂ) * ((b : ℕ) : ℂ) ^ 2 / ((p ^ k : ℕ) : ℂ)
          + 2 * Real.pi * Complex.I * ((2 * s * (b : ℤ) : ℤ) : ℂ) * (c : ℂ) / (p : ℂ)
          + ((s * (p ^ (k - 2) : ℕ) * (c : ℤ) ^ 2 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      have hpne : (p : ℂ) ≠ 0 := by exact_mod_cast hp0
      have hMne : ((p ^ (k - 2) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hp0
      rw [hk1, hk2]
      push_cast
      field_simp
      ring
    rw [hkey, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp_rw [hterm3]
  -- Step 3: inner geometric sum
  have step : ∑ b ∈ range (p ^ (k - 1)),
        ∑ c ∈ range p, A b
          * Complex.exp (2 * Real.pi * Complex.I * ((2 * s * (b : ℤ) : ℤ) : ℂ) * (c : ℂ) / (p : ℂ))
      = ∑ b ∈ range (p ^ (k - 1)), A b * (if (p : ℤ) ∣ (2 * s * (b : ℤ)) then (p : ℂ) else 0) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.mul_sum, geom_sum_p p hp0 (2 * s * (b : ℤ))]
  rw [step]
  -- Step 4: condition `p ∣ 2sb ↔ p ∣ b`
  have hcop : IsCoprime (p : ℤ) (2 * s) := by
    have h2 : IsCoprime (p : ℤ) 2 := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hodd : Odd p := hp.odd_of_ne_two hp2
      have : Nat.Coprime p 2 := Nat.coprime_two_right.mpr hodd
      simpa [Int.gcd] using this
    have hs : IsCoprime (p : ℤ) s := by
      rw [Int.isCoprime_iff_gcd_eq_one]; rw [Int.gcd_comm]; exact hgcd
    exact h2.mul_right hs
  have hcond : ∀ b : ℕ, ((p : ℤ) ∣ (2 * s * (b : ℤ))) ↔ p ∣ b := by
    intro b
    constructor
    · intro hd
      have : (p : ℤ) ∣ (b : ℤ) := hcop.dvd_of_dvd_mul_left hd
      exact_mod_cast this
    · intro hd
      have : (p : ℤ) ∣ (b : ℤ) := by exact_mod_cast hd
      exact Dvd.dvd.mul_left this (2 * s)
  have step2 : ∑ b ∈ range (p ^ (k - 1)), A b * (if (p : ℤ) ∣ (2 * s * (b : ℤ)) then (p : ℂ) else 0)
      = (p : ℂ) * ∑ b ∈ (range (p ^ (k - 1))).filter (fun b => p ∣ b), A b := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    simp only [hcond b]
    split_ifs with h
    · ring
    · ring
  rw [step2]
  -- Step 5: reindex the filtered sum via `b = p * b'`
  congr 1
  rw [Sz]
  apply Finset.sum_nbij' (fun b => b / p) (fun b' => p * b')
  · intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨hb1, hdvd⟩ := hb
    rw [Finset.mem_range] at hb1 ⊢
    rw [Nat.div_lt_iff_lt_mul hp.pos, ← hk1]; exact hb1
  · intro b' hb'
    rw [Finset.mem_range] at hb'
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, Dvd.intro _ rfl⟩
    rw [hk1, mul_comm (p ^ (k - 2)) p]; exact (Nat.mul_lt_mul_left hp.pos).mpr hb'
  · intro b hb
    rw [Finset.mem_filter] at hb
    exact Nat.mul_div_cancel' hb.2
  · intro b' _; exact Nat.mul_div_cancel_left b' hp.pos
  · intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨_, hdvd⟩ := hb
    simp only [hA]
    congr 1
    have hbb : (b : ℂ) = (p : ℂ) * ((b / p : ℕ) : ℂ) := by
      have := Nat.mul_div_cancel' hdvd
      exact_mod_cast this.symm
    have hpne : (p : ℂ) ≠ 0 := by exact_mod_cast hp0
    have hMne : ((p ^ (k - 2) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hp0
    rw [hbb, show ((p ^ k : ℕ) : ℂ) = ((p ^ (k - 2) : ℕ) : ℂ) * (p : ℂ) ^ 2 by push_cast [hk2]; ring]
    field_simp

theorem Sz_one_val (s : ℤ) : Sz s 1 = 1 := by
  rw [Sz, Finset.sum_range_one]; simp

/-- **Prime-power case.** -/
theorem primepow (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (s : ℤ) (hgcd : s.gcd (p : ℤ) = 1) :
    ∀ k, Sz s (p ^ k) = ((jacobiSym s (p ^ k) : ℤ) : ℂ) * Sz 1 (p ^ k) := by
  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.pos.ne'
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    rcases k with _ | _ | k
    · simp only [pow_zero]
      rw [Sz_one_val s, Sz_one_val 1, jacobiSym.one_right]; norm_num
    · rw [pow_one]; exact block2 p hp2 s hgcd
    · have hk2 : 2 ≤ k + 2 := by omega
      have hb3s := block3 p (k + 2) hp hp2 hk2 s hgcd
      have hb31 := block3 p (k + 2) hp hp2 hk2 1
        (Int.isCoprime_iff_gcd_eq_one.mp isCoprime_one_left)
      simp only [Nat.add_sub_cancel] at hb3s hb31
      have hIH := IH k (by omega)
      have hJ : (jacobiSym s (p ^ (k + 2)) : ℤ) = jacobiSym s (p ^ k) := by
        rw [jacobiSym.pow_right, jacobiSym.pow_right, pow_add, jacobiSym.sq_one hgcd, mul_one]
      calc Sz s (p ^ (k + 2)) = (p : ℂ) * Sz s (p ^ k) := hb3s
        _ = (p : ℂ) * (((jacobiSym s (p ^ k) : ℤ) : ℂ) * Sz 1 (p ^ k)) := by rw [hIH]
        _ = ((jacobiSym s (p ^ k) : ℤ) : ℂ) * ((p : ℂ) * Sz 1 (p ^ k)) := by ring
        _ = ((jacobiSym s (p ^ k) : ℤ) : ℂ) * Sz 1 (p ^ (k + 2)) := by rw [← hb31]
        _ = ((jacobiSym s (p ^ (k + 2)) : ℤ) : ℂ) * Sz 1 (p ^ (k + 2)) := by rw [hJ]

/-- **Global induction over odd moduli.** -/
theorem aux : ∀ m : ℕ, Odd m → ∀ s : ℤ, s.gcd (m : ℤ) = 1 →
    Sz s m = ((jacobiSym s m : ℤ) : ℂ) * Sz 1 m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro hodd s hgcd
    rcases eq_or_ne m 1 with hm1 | hm1
    · subst hm1
      rw [Sz_one_val s, Sz_one_val 1, jacobiSym.one_right]; norm_num
    · have hm0 : m ≠ 0 := by rintro rfl; rw [Nat.odd_iff] at hodd; omega
      have hm1lt : 1 < m := by omega
      set p := m.minFac with hp_def
      have hp : p.Prime := Nat.minFac_prime hm1
      haveI : Fact p.Prime := ⟨hp⟩
      have hp0 : p ≠ 0 := hp.pos.ne'
      have hpdvd : p ∣ m := Nat.minFac_dvd m
      have hp2 : p ≠ 2 := by
        rintro hpe
        rw [hpe] at hpdvd
        rw [Nat.odd_iff] at hodd; omega
      set K := m.factorization p with hK_def
      have hK1 : 1 ≤ K := (Nat.Prime.dvd_iff_one_le_factorization hp hm0).mp hpdvd
      obtain ⟨pk, m', hpk_def, hm'_def, hmeq, hcopPm'⟩ :
          ∃ pk m', pk = p ^ K ∧ m' = m / pk ∧ pk * m' = m ∧ Nat.Coprime p m' :=
        ⟨p ^ K, m / p ^ K, rfl, rfl, Nat.ordProj_mul_ordCompl_eq_self m p,
          Nat.coprime_ordCompl hp hm0⟩
      have hpk0 : pk ≠ 0 := by rw [hpk_def]; exact pow_ne_zero _ hp0
      have hm'0 : m' ≠ 0 := by rintro h0; rw [h0, mul_zero] at hmeq; exact hm0 hmeq.symm
      have hcoppk : Nat.Coprime pk m' := by rw [hpk_def]; exact hcopPm'.pow_left K
      have hm'dvd : m' ∣ m := ⟨pk, by rw [← hmeq]; ring⟩
      have hm'lt : m' < m := by
        have hpklt : 1 < pk := by
          rw [hpk_def]
          have := hp.one_lt
          have h2 := Nat.le_self_pow (show K ≠ 0 by omega) p
          omega
        rw [hm'_def]; exact Nat.div_lt_self (Nat.pos_of_ne_zero hm0) hpklt
      have hm'odd : Odd m' := by
        have hop : Odd (pk * m') := by rw [hmeq]; exact hodd
        exact (Nat.odd_mul.mp hop).2
      haveI : NeZero pk := ⟨hpk0⟩
      haveI : NeZero m' := ⟨hm'0⟩
      -- coprimality on the `s` side
      have hcopI : IsCoprime s (m : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
      have hmeqZ : (m : ℤ) = (pk : ℤ) * (m' : ℤ) := by rw [← hmeq]; push_cast; ring
      have hcopI' : IsCoprime s ((pk : ℤ) * (m' : ℤ)) := hmeqZ ▸ hcopI
      have hs_pk : IsCoprime s (pk : ℤ) := hcopI'.of_mul_right_left
      have hs_m' : IsCoprime s (m' : ℤ) := hcopI'.of_mul_right_right
      have hppk : (p : ℤ) ∣ (pk : ℤ) := by
        rw [hpk_def]; exact_mod_cast dvd_pow_self p (show K ≠ 0 by omega)
      have hs_p : IsCoprime s (p : ℤ) := hs_pk.of_isCoprime_of_dvd_right hppk
      have hm'_p : IsCoprime (m' : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.mpr hcopPm'.symm
      have hpk_m' : IsCoprime (pk : ℤ) (m' : ℤ) := Nat.isCoprime_iff_coprime.mpr hcoppk
      have gcd_sm'_p : (s * (m' : ℤ)).gcd (p : ℤ) = 1 :=
        Int.isCoprime_iff_gcd_eq_one.mp (hs_p.mul_left hm'_p)
      have gcd_m'_p : (m' : ℤ).gcd (p : ℤ) = 1 :=
        Int.isCoprime_iff_gcd_eq_one.mp hm'_p
      have gcd_spk_m' : (s * (pk : ℤ)).gcd (m' : ℤ) = 1 :=
        Int.isCoprime_iff_gcd_eq_one.mp (hs_m'.mul_left hpk_m')
      have gcd_pk_m' : (pk : ℤ).gcd (m' : ℤ) = 1 :=
        Int.isCoprime_iff_gcd_eq_one.mp hpk_m'
      -- the four multiplicative pieces
      have pp_sm' : Sz (s * (m' : ℤ)) pk
          = ((jacobiSym (s * (m' : ℤ)) pk : ℤ) : ℂ) * Sz 1 pk := by
        rw [hpk_def]; exact primepow p hp2 (s * (m' : ℤ)) gcd_sm'_p K
      have pp_m' : Sz (m' : ℤ) pk = ((jacobiSym (m' : ℤ) pk : ℤ) : ℂ) * Sz 1 pk := by
        rw [hpk_def]; exact primepow p hp2 (m' : ℤ) gcd_m'_p K
      have ih_spk : Sz (s * (pk : ℤ)) m'
          = ((jacobiSym (s * (pk : ℤ)) m' : ℤ) : ℂ) * Sz 1 m' :=
        IH m' hm'lt hm'odd (s * (pk : ℤ)) gcd_spk_m'
      have ih_pk : Sz (pk : ℤ) m' = ((jacobiSym (pk : ℤ) m' : ℤ) : ℂ) * Sz 1 m' :=
        IH m' hm'lt hm'odd (pk : ℤ) gcd_pk_m'
      -- CRT factorization of `Sz s m` and `Sz 1 m`
      have e1 : Sz s m = Sz (s * (m' : ℤ)) pk * Sz (s * (pk : ℤ)) m' := by
        rw [← hmeq]; exact block1 s pk m' hpk0 hm'0 hcoppk
      have e2 : Sz 1 m = Sz (m' : ℤ) pk * Sz (pk : ℤ) m' := by
        rw [← hmeq]
        have hb := block1 1 pk m' hpk0 hm'0 hcoppk
        simpa using hb
      have HS : Sz s m
          = ((jacobiSym s pk : ℤ) : ℂ) * ((jacobiSym (m' : ℤ) pk : ℤ) : ℂ) * Sz 1 pk
            * (((jacobiSym s m' : ℤ) : ℂ) * ((jacobiSym (pk : ℤ) m' : ℤ) : ℂ) * Sz 1 m') := by
        rw [e1, pp_sm', ih_spk, jacobiSym.mul_left s (m' : ℤ) pk,
          jacobiSym.mul_left s (pk : ℤ) m']
        push_cast
        ring
      have H1 : Sz 1 m
          = ((jacobiSym (m' : ℤ) pk : ℤ) : ℂ) * Sz 1 pk
            * (((jacobiSym (pk : ℤ) m' : ℤ) : ℂ) * Sz 1 m') := by
        rw [e2, pp_m', ih_pk]
      have hJm : ((jacobiSym s m : ℤ) : ℂ)
          = ((jacobiSym s pk : ℤ) : ℂ) * ((jacobiSym s m' : ℤ) : ℂ) := by
        rw [show m = pk * m' from hmeq.symm, jacobiSym.mul_right]
        push_cast; ring
      rw [HS, H1, hJm]
      ring

end OddTwist

/-- **Twist relation for odd modulus.** -/
theorem odd_twist_thm (m : ℕ) [NeZero m] (hoddm : m % 2 = 1) (s : ℕ)
    (hs : Nat.Coprime s m) :
    S s m = ((jacobiSym (s : ℤ) m : ℤ) : ℂ) * S 1 m := by
  have hodd : Odd m := Nat.odd_iff.mpr hoddm
  have hgcd : (s : ℤ).gcd (m : ℤ) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (Nat.isCoprime_iff_coprime.mpr hs)
  rw [OddTwist.S_eq_Sz s m, OddTwist.S_eq_Sz 1 m, Nat.cast_one]
  exact OddTwist.aux m hodd (s : ℤ) hgcd
end
end

/- ================= inlined from Reduce.lean ================= -/
section

open Complex Finset

noncomputable section

/-- For `0 < t < n`, `ω^t ≠ 1`. -/
lemma pow_ne_one (n : ℕ) [NeZero n] {t : ℕ} (ht : 0 < t) (htn : t < n) :
    (GaussGen.ω n) ^ t ≠ 1 := by
  intro h
  rw [(GaussGen.omega_primitiveRoot n).pow_eq_one_iff_dvd t] at h
  exact absurd (Nat.le_of_dvd ht h) (not_le.mpr htn)

/-- The Gauss sum as a power sum of `ω`. -/
lemma S_eq_pow (t m : ℕ) : S t m = ∑ k ∈ Finset.range m, (GaussGen.ω m) ^ (t * k ^ 2) := by
  show GaussGen.S t m = _
  unfold GaussGen.S
  apply Finset.sum_congr rfl
  intro k _
  rw [GaussGen.ω, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **Step 1.** `i·cot(πt/n)` as roots of unity. -/
lemma icot_omega (n : ℕ) [NeZero n] {t : ℕ} (ht : 0 < t) (htn : t < n) :
    Complex.I * (↑(rcot (Real.pi * (t : ℝ) / (n : ℝ))) : ℂ)
      = ((GaussGen.ω n) ^ t + 1) / (1 - (GaussGen.ω n) ^ t) := by
  have hz1 : (GaussGen.ω n) ^ t ≠ 1 := pow_ne_one n ht htn
  have hden : (1 : ℂ) - (GaussGen.ω n) ^ t ≠ 0 := by
    intro h; apply hz1; linear_combination -h
  have hcot : (↑(rcot (Real.pi * (t : ℝ) / (n : ℝ))) : ℂ)
      = Complex.cot (↑(Real.pi * (t : ℝ) / (n : ℝ))) := by
    rw [rcot, ← Real.cot_eq_cos_div_sin, Complex.ofReal_cot]
  have hexp : Complex.exp (2 * Complex.I * (↑(Real.pi * (t : ℝ) / (n : ℝ)))) = (GaussGen.ω n) ^ t := by
    rw [GaussGen.ω, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hcot, Complex.cot_eq_exp_ratio, hexp]
  field_simp

/-- Sum of `ω^(t·j)` over `t ∈ [1,n)`. -/
lemma Gsum (n : ℕ) [NeZero n] (hn : 1 ≤ n) (j : ℕ) :
    ∑ t ∈ Finset.Ico 1 n, (GaussGen.ω n) ^ (t * j) = (if n ∣ j then (n : ℂ) else 0) - 1 := by
  have hins : (Finset.range n) = insert 0 (Finset.Ico 1 n) := by
    ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
  have h0 : (0 : ℕ) ∉ Finset.Ico 1 n := by simp
  have h := GaussGen.orthogonality n j
  rw [hins, Finset.sum_insert h0] at h
  simp only [Nat.zero_mul, pow_zero] at h
  linear_combination h

/-- **Step 2 pairing.** `∑_{t∈[1,n)} 1/(ω^t - 1) = -(n-1)/2`. -/
lemma F0_eval (n : ℕ) [NeZero n] (hn : 1 ≤ n) :
    ∑ t ∈ Finset.Ico 1 n, (1 / ((GaussGen.ω n) ^ t - 1)) = -((n : ℂ) - 1) / 2 := by
  have hre : ∑ t ∈ Finset.Ico 1 n, (1 / ((GaussGen.ω n) ^ t - 1))
           = ∑ t ∈ Finset.Ico 1 n, (1 / ((GaussGen.ω n) ^ (n - t) - 1)) := by
    apply Finset.sum_nbij' (fun t => n - t) (fun t => n - t)
    · intro a ha; rw [Finset.mem_Ico] at *; omega
    · intro a ha; rw [Finset.mem_Ico] at *; omega
    · intro a ha; rw [Finset.mem_Ico] at ha; omega
    · intro a ha; rw [Finset.mem_Ico] at ha; omega
    · intro a ha; rw [Finset.mem_Ico] at ha
      rw [show n - (n - a) = a from by omega]
  have hpt : ∀ t ∈ Finset.Ico 1 n,
      (1 / ((GaussGen.ω n) ^ t - 1)) + (1 / ((GaussGen.ω n) ^ (n - t) - 1)) = -1 := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    have hz1 : (GaussGen.ω n) ^ t ≠ 1 := pow_ne_one n ht.1 ht.2
    have hmul : (GaussGen.ω n) ^ t * (GaussGen.ω n) ^ (n - t) = 1 := by
      rw [← pow_add, show t + (n - t) = n from by omega, GaussGen.omega_pow]
    have hw1 : (GaussGen.ω n) ^ (n - t) ≠ 1 := by
      intro h; rw [h, mul_one] at hmul; exact hz1 hmul
    have hd1 : (GaussGen.ω n) ^ t - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hd2 : (GaussGen.ω n) ^ (n - t) - 1 ≠ 0 := sub_ne_zero.mpr hw1
    rw [div_add_div _ _ hd1 hd2, div_eq_iff (mul_ne_zero hd1 hd2)]
    linear_combination hmul
  have hpair : ∑ t ∈ Finset.Ico 1 n,
      ((1 / ((GaussGen.ω n) ^ t - 1)) + (1 / ((GaussGen.ω n) ^ (n - t) - 1)))
        = ∑ _t ∈ Finset.Ico 1 n, (-1 : ℂ) := Finset.sum_congr rfl hpt
  rw [Finset.sum_add_distrib, ← hre, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hpair
  rw [Nat.cast_sub hn, Nat.cast_one] at hpair
  linear_combination hpair / 2

/-- **Step 2 telescoping.** -/
lemma Fsum_eval (n : ℕ) [NeZero n] (hn : 1 ≤ n) (ρ : ℕ) (hρ : ρ < n) :
    ∑ t ∈ Finset.Ico 1 n, (GaussGen.ω n) ^ (t * ρ) / ((GaussGen.ω n) ^ t - 1)
      = (∑ j ∈ Finset.range ρ, ((if n ∣ j then (n : ℂ) else 0) - 1)) + (-((n : ℂ) - 1) / 2) := by
  have step : ∀ t ∈ Finset.Ico 1 n,
      (GaussGen.ω n) ^ (t * ρ) / ((GaussGen.ω n) ^ t - 1)
        = (∑ j ∈ Finset.range ρ, (GaussGen.ω n) ^ (t * j)) + 1 / ((GaussGen.ω n) ^ t - 1) := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    have hz1 : (GaussGen.ω n) ^ t ≠ 1 := pow_ne_one n ht.1 ht.2
    have hne : (GaussGen.ω n) ^ t - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hgeo : ∑ j ∈ Finset.range ρ, (GaussGen.ω n) ^ (t * j)
        = ((GaussGen.ω n) ^ (t * ρ) - 1) / ((GaussGen.ω n) ^ t - 1) := by
      have hc : ∑ j ∈ Finset.range ρ, (GaussGen.ω n) ^ (t * j)
           = ∑ j ∈ Finset.range ρ, ((GaussGen.ω n) ^ t) ^ j := by
        apply Finset.sum_congr rfl; intro j _; rw [← pow_mul]
      rw [hc, geom_sum_eq hz1 ρ, ← pow_mul]
    rw [hgeo]
    field_simp
    ring
  have hswap : ∑ t ∈ Finset.Ico 1 n, ∑ j ∈ Finset.range ρ, (GaussGen.ω n) ^ (t * j)
             = ∑ j ∈ Finset.range ρ, ((if n ∣ j then (n : ℂ) else 0) - 1) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact Gsum n hn j
  rw [Finset.sum_congr rfl step, Finset.sum_add_distrib, hswap, F0_eval n hn]

/-- **Step 2 (closed form).** The sawtooth finite Fourier identity. -/
lemma T_closed (n : ℕ) [NeZero n] (hn : 1 ≤ n) (r : ℕ) :
    ∑ t ∈ Finset.Ico 1 n,
        (Complex.I * (↑(rcot (Real.pi * (t : ℝ) / (n : ℝ))) : ℂ)) * (GaussGen.ω n) ^ (t * r)
      = Complex.ofReal (if r % n = 0 then (0 : ℝ) else 2 * ((r % n : ℕ) : ℝ) - (n : ℝ)) := by
  -- reduce the exponent modulo n
  have hpow : ∀ t : ℕ, (GaussGen.ω n) ^ (t * r) = (GaussGen.ω n) ^ (t * (r % n)) := by
    intro t
    have e1 : t * r = n * (t * (r / n)) + t * (r % n) := by
      have h := Nat.div_add_mod r n
      calc t * r = t * (n * (r / n) + r % n) := by rw [h]
        _ = n * (t * (r / n)) + t * (r % n) := by ring
    rw [e1, pow_add, pow_mul, GaussGen.omega_pow, one_pow, one_mul]
  -- rewrite each summand
  have hsum : ∑ t ∈ Finset.Ico 1 n,
        (Complex.I * (↑(rcot (Real.pi * (t : ℝ) / (n : ℝ))) : ℂ)) * (GaussGen.ω n) ^ (t * r)
      = ∑ t ∈ Finset.Ico 1 n,
        ((-1) * (GaussGen.ω n) ^ (t * (r % n))
          + (-2) * ((GaussGen.ω n) ^ (t * (r % n)) / ((GaussGen.ω n) ^ t - 1))) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_Ico] at ht
    rw [icot_omega n ht.1 ht.2, hpow t]
    have hz1 : (GaussGen.ω n) ^ t ≠ 1 := pow_ne_one n ht.1 ht.2
    have hd1 : (GaussGen.ω n) ^ t - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hd2 : (1 : ℂ) - (GaussGen.ω n) ^ t ≠ 0 := by
      intro h; apply hz1; linear_combination -h
    field_simp
    ring
  rw [hsum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  set ρ := r % n with hρdef
  have hρn : ρ < n := Nat.mod_lt r (by omega)
  rw [Gsum n hn ρ, Fsum_eval n hn ρ hρn]
  -- evaluate the range-ρ sum
  have hJ : ∑ j ∈ Finset.range ρ, ((if n ∣ j then (n : ℂ) else 0) - 1)
      = (if ρ = 0 then (0 : ℂ) else (n : ℂ)) - ρ := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    congr 1
    have hind : ∀ j ∈ Finset.range ρ,
        (if n ∣ j then (n : ℂ) else 0) = (if j = 0 then (n : ℂ) else 0) := by
      intro j hj
      rw [Finset.mem_range] at hj
      by_cases hj0 : j = 0
      · simp [hj0]
      · have hnd : ¬ n ∣ j := fun hd => hj0 (Nat.eq_zero_of_dvd_of_lt hd (by omega))
        rw [if_neg hnd, if_neg hj0]
    rw [Finset.sum_congr rfl hind, Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    by_cases hρ0 : ρ = 0
    · rw [if_pos hρ0]; simp [hρ0]
    · rw [if_neg hρ0, if_pos (by omega)]
  rw [hJ]
  by_cases hρ0 : ρ = 0
  · rw [hρ0]
    rw [if_pos (dvd_zero n), if_pos (rfl : (0 : ℕ) = 0), if_pos (rfl : (0 : ℕ) = 0)]
    push_cast
    ring
  · rw [if_neg hρ0]
    have hnd : ¬ n ∣ ρ := fun hd => hρ0 (Nat.eq_zero_of_dvd_of_lt hd hρn)
    rw [if_neg hnd, if_neg hρ0]
    push_cast
    ring

/-- Periodic block sum: `∑_{k<d·m} f = d·∑_{k<m} f` for `f k = ω_m^(s·k²)`. -/
lemma block_sum (m : ℕ) [NeZero m] (d s : ℕ) :
    ∑ k ∈ Finset.range (d * m), (GaussGen.ω m) ^ (s * k ^ 2)
      = (d : ℂ) * ∑ k ∈ Finset.range m, (GaussGen.ω m) ^ (s * k ^ 2) := by
  induction d with
  | zero => simp
  | succ e ih =>
    rw [add_mul, one_mul, Finset.sum_range_add, ih]
    have hper : ∀ i, (GaussGen.ω m) ^ (s * (e * m + i) ^ 2) = (GaussGen.ω m) ^ (s * i ^ 2) := by
      intro i
      have hexp : s * (e * m + i) ^ 2 = s * i ^ 2 + m * (s * (e * e * m + 2 * e * i)) := by ring
      rw [hexp, pow_add, pow_mul (GaussGen.ω m) m (s * (e * e * m + 2 * e * i)),
        GaussGen.omega_pow, one_pow, mul_one]
    rw [Finset.sum_congr rfl (fun i _ => hper i)]
    push_cast
    ring

/-- **Step 4 scaling.** `S ((n/m)·s) n = (n/m)·S s m` when `m ∣ n`. -/
lemma S_scale (n : ℕ) (hn : 1 ≤ n) {m : ℕ} (hm1 : 1 ≤ m) (hmn : m ∣ n) (s : ℕ) :
    S ((n / m) * s) n = ((n / m : ℕ) : ℂ) * S s m := by
  haveI : NeZero m := ⟨by omega⟩
  set d := n / m with hddef
  have hdpos : 0 < d := by
    rw [hddef]; exact Nat.div_pos (Nat.le_of_dvd (by omega) hmn) (by omega)
  have hnmd : d * m = n := Nat.div_mul_cancel hmn
  have hstep : S (d * s) n = ∑ k ∈ Finset.range n, (GaussGen.ω m) ^ (s * k ^ 2) := by
    rw [S_eq_pow]
    apply Finset.sum_congr rfl
    intro k _
    rw [GaussGen.ω, GaussGen.ω, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show 0 < m by omega).ne'
    have hnc : (n : ℂ) = (d : ℂ) * (m : ℂ) := by exact_mod_cast hnmd.symm
    rw [hnc]
    push_cast
    field_simp
  rw [hstep, ← hnmd, block_sum m d s, S_eq_pow s m]

/-- **Master reduction identity.** -/
theorem master (n : ℕ) (hn : 1 ≤ n) :
    2 * (A048153 n : ℝ) - (n : ℝ) * ((n : ℝ) - (Zc n : ℝ)) =
      - ∑ m ∈ n.divisors.filter (fun m => 1 < m), ((n / m : ℕ) : ℝ) * P m := by
  haveI : NeZero n := ⟨by omega⟩
  -- Step 3 (real): evaluate the real sum coming from the closed form.
  have hRHSreal : ∑ k ∈ Finset.range n,
        (if (k ^ 2) % n = 0 then (0 : ℝ) else 2 * (((k ^ 2) % n : ℕ) : ℝ) - (n : ℝ))
      = 2 * (A048153 n : ℝ) - (n : ℝ) * ((n : ℝ) - (Zc n : ℝ)) := by
    have hpt : ∀ k ∈ Finset.range n,
        (if (k ^ 2) % n = 0 then (0 : ℝ) else 2 * (((k ^ 2) % n : ℕ) : ℝ) - (n : ℝ))
          = 2 * (((k ^ 2) % n : ℕ) : ℝ) - (n : ℝ) * (if (k ^ 2) % n = 0 then (0 : ℝ) else 1) := by
      intro k _
      by_cases h : (k ^ 2) % n = 0
      · rw [if_pos h, if_pos h, h]; push_cast; ring
      · rw [if_neg h, if_neg h]; ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    congr 1
    · congr 1
      rw [← Nat.cast_sum]
      rfl
    · congr 1
      have hcard : ∀ k ∈ Finset.range n, (if (k ^ 2) % n = 0 then (0 : ℝ) else 1)
          = 1 - (if (k ^ 2) % n = 0 then (1 : ℝ) else 0) := by
        intro k _; by_cases h : (k ^ 2) % n = 0 <;> simp [h]
      rw [Finset.sum_congr rfl hcard, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_one, Finset.sum_boole]
      rfl
  -- Step 3 (complex): the double-sum identity, folded and cast.
  have hEq : ∑ t ∈ Finset.Ico 1 n,
        (Complex.I * (↑(rcot (Real.pi * (t : ℝ) / (n : ℝ))) : ℂ)) * (S t n)
      = Complex.ofReal (2 * (A048153 n : ℝ) - (n : ℝ) * ((n : ℝ) - (Zc n : ℝ))) := by
    have e1 : ∑ t ∈ Finset.Ico 1 n,
          (Complex.I * (↑(rcot (Real.pi * (t : ℝ) / (n : ℝ))) : ℂ)) * (S t n)
        = ∑ t ∈ Finset.Ico 1 n, ∑ k ∈ Finset.range n,
          (Complex.I * (↑(rcot (Real.pi * (t : ℝ) / (n : ℝ))) : ℂ)) * (GaussGen.ω n) ^ (t * k ^ 2) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [S_eq_pow t n, Finset.mul_sum]
    rw [e1, Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.range n) => T_closed n hn (k ^ 2))]
    rw [← Complex.ofReal_sum, hRHSreal]
  -- Step 3: take real parts to get (⋆).
  have hX : 2 * (A048153 n : ℝ) - (n : ℝ) * ((n : ℝ) - (Zc n : ℝ))
      = -∑ t ∈ Finset.Ico 1 n, rcot (Real.pi * (t : ℝ) / (n : ℝ)) * (S t n).im := by
    have hre : (∑ t ∈ Finset.Ico 1 n,
        (Complex.I * (↑(rcot (Real.pi * (t : ℝ) / (n : ℝ))) : ℂ)) * (S t n)).re
        = 2 * (A048153 n : ℝ) - (n : ℝ) * ((n : ℝ) - (Zc n : ℝ)) := by
      rw [hEq, Complex.ofReal_re]
    rw [Complex.re_sum] at hre
    have hterm : ∀ t ∈ Finset.Ico 1 n,
        ((Complex.I * (↑(rcot (Real.pi * (t : ℝ) / (n : ℝ))) : ℂ)) * (S t n)).re
          = -(rcot (Real.pi * (t : ℝ) / (n : ℝ)) * (S t n).im) := by
      intro t _
      rw [show (Complex.I * (↑(rcot (Real.pi * (t : ℝ) / (n : ℝ))) : ℂ)) * (S t n)
            = (↑(rcot (Real.pi * (t : ℝ) / (n : ℝ))) : ℂ) * (Complex.I * (S t n)) from by ring,
          Complex.re_ofReal_mul, Complex.I_mul_re]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib] at hre
    linarith [hre]
  -- Step 4: reindex by gcd.
  have hStep4 : ∑ t ∈ Finset.Ico 1 n, rcot (Real.pi * (t : ℝ) / (n : ℝ)) * (S t n).im
      = ∑ m ∈ n.divisors.filter (fun m => 1 < m), ((n / m : ℕ) : ℝ) * P m := by
    set D := n.divisors.filter (fun m => 1 < m) with hDdef
    have hstep : ∀ m ∈ D, ((n / m : ℕ) : ℝ) * P m
        = ∑ s ∈ (Finset.Ico 1 m).filter (fun s => Nat.Coprime s m),
            ((n / m : ℕ) : ℝ) * (rcot (Real.pi * (s : ℝ) / (m : ℝ)) * (S s m).im) := by
      intro m _
      rw [P, Finset.mul_sum]
    have hR : ∑ m ∈ D, ((n / m : ℕ) : ℝ) * P m
        = ∑ x ∈ D.sigma (fun m => (Finset.Ico 1 m).filter (fun s => Nat.Coprime s m)),
            ((n / x.1 : ℕ) : ℝ) * (rcot (Real.pi * (x.2 : ℝ) / (x.1 : ℝ)) * (S x.2 x.1).im) := by
      rw [Finset.sum_congr rfl hstep, Finset.sum_sigma']
    rw [hR]
    refine Finset.sum_bij'
      (fun t _ => (⟨n / Nat.gcd t n, t / Nat.gcd t n⟩ : Σ _ : ℕ, ℕ))
      (fun x _ => (n / x.1) * x.2) ?_ ?_ ?_ ?_ ?_
    · -- hi
      intro t ht
      rw [Finset.mem_Ico] at ht
      have htpos : 0 < t := ht.1
      have hd_dvd_t : Nat.gcd t n ∣ t := Nat.gcd_dvd_left t n
      have hd_dvd_n : Nat.gcd t n ∣ n := Nat.gcd_dvd_right t n
      have hd_pos : 0 < Nat.gcd t n := Nat.gcd_pos_iff.mpr (Or.inl htpos)
      have hd_lt_n : Nat.gcd t n < n := lt_of_le_of_lt (Nat.le_of_dvd htpos hd_dvd_t) ht.2
      rw [Finset.mem_sigma]
      refine ⟨?_, ?_⟩
      · rw [hDdef, Finset.mem_filter, Nat.mem_divisors]
        refine ⟨⟨⟨Nat.gcd t n, (Nat.div_mul_cancel hd_dvd_n).symm⟩, by omega⟩, ?_⟩
        have hge1 : 1 ≤ n / Nat.gcd t n :=
          (Nat.one_le_div_iff hd_pos).mpr (Nat.le_of_dvd (by omega) hd_dvd_n)
        rcases eq_or_lt_of_le hge1 with heq | hlt
        · exfalso
          have hgn : Nat.gcd t n = n := by
            have h := Nat.mul_div_cancel' hd_dvd_n
            rw [← heq, mul_one] at h; omega
          omega
        · exact hlt
      · simp only [Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact (Nat.one_le_div_iff hd_pos).mpr (Nat.le_of_dvd htpos hd_dvd_t)
        · exact Nat.div_lt_div_of_lt_of_dvd hd_dvd_n ht.2
        · exact Nat.coprime_div_gcd_div_gcd hd_pos
    · -- hj
      intro x hx
      obtain ⟨m, s⟩ := x
      rw [Finset.mem_sigma] at hx
      obtain ⟨hmD, hsC⟩ := hx
      rw [hDdef, Finset.mem_filter, Nat.mem_divisors] at hmD
      obtain ⟨⟨hmn, _⟩, hm1⟩ := hmD
      simp only [Finset.mem_filter, Finset.mem_Ico] at hsC
      obtain ⟨⟨hs1, hsm⟩, _⟩ := hsC
      rw [Finset.mem_Ico]
      have hdd_pos : 0 < n / m := Nat.div_pos (Nat.le_of_dvd (by omega) hmn) (by omega)
      have hdd_m : (n / m) * m = n := Nat.div_mul_cancel hmn
      have hspos : 0 < s := by omega
      refine ⟨Nat.mul_pos hdd_pos hspos, ?_⟩
      calc (n / m) * s < (n / m) * m := (Nat.mul_lt_mul_left hdd_pos).mpr hsm
        _ = n := hdd_m
    · -- left_inv
      intro t ht
      rw [Finset.mem_Ico] at ht
      have hd_dvd_t : Nat.gcd t n ∣ t := Nat.gcd_dvd_left t n
      have hd_dvd_n : Nat.gcd t n ∣ n := Nat.gcd_dvd_right t n
      show (n / (n / Nat.gcd t n)) * (t / Nat.gcd t n) = t
      rw [Nat.div_div_self hd_dvd_n (by omega), Nat.mul_div_cancel' hd_dvd_t]
    · -- right_inv
      intro x hx
      obtain ⟨m, s⟩ := x
      rw [Finset.mem_sigma] at hx
      obtain ⟨hmD, hsC⟩ := hx
      rw [hDdef, Finset.mem_filter, Nat.mem_divisors] at hmD
      obtain ⟨⟨hmn, _⟩, hm1⟩ := hmD
      simp only [Finset.mem_filter, Finset.mem_Ico] at hsC
      obtain ⟨⟨hs1, hsm⟩, hcop⟩ := hsC
      set dd := n / m with hdddef
      have hdd_pos : 0 < dd := Nat.div_pos (Nat.le_of_dvd (by omega) hmn) (by omega)
      have hdd_m : dd * m = n := Nat.div_mul_cancel hmn
      have hgcd : Nat.gcd (dd * s) n = dd := by
        rw [← hdd_m, Nat.gcd_mul_left, show Nat.gcd s m = 1 from hcop, mul_one]
      show (⟨n / Nat.gcd (dd * s) n, (dd * s) / Nat.gcd (dd * s) n⟩ : Σ _ : ℕ, ℕ) = ⟨m, s⟩
      rw [hgcd]
      have h1 : n / dd = m := by rw [hdddef, Nat.div_div_self hmn (by omega)]
      have h2 : (dd * s) / dd = s := Nat.mul_div_cancel_left s hdd_pos
      rw [h1, h2]
    · -- h : summand equality
      intro t ht
      rw [Finset.mem_Ico] at ht
      have htpos : 0 < t := ht.1
      have hd_dvd_t : Nat.gcd t n ∣ t := Nat.gcd_dvd_left t n
      have hd_dvd_n : Nat.gcd t n ∣ n := Nat.gcd_dvd_right t n
      have hd_pos : 0 < Nat.gcd t n := Nat.gcd_pos_iff.mpr (Or.inl htpos)
      set d := Nat.gcd t n with hddef
      set m := n / d with hmdef
      set s := t / d with hsdef
      have hm_dvd_n : m ∣ n := ⟨d, by rw [hmdef]; exact (Nat.div_mul_cancel hd_dvd_n).symm⟩
      have hm1 : 1 ≤ m := by
        rw [hmdef]; exact (Nat.one_le_div_iff hd_pos).mpr (Nat.le_of_dvd (by omega) hd_dvd_n)
      have hts : (n / m) * s = t := by
        rw [show n / m = d from by rw [hmdef, Nat.div_div_self hd_dvd_n (by omega)], hsdef]
        exact Nat.mul_div_cancel' hd_dvd_t
      have harg : Real.pi * (t : ℝ) / (n : ℝ) = Real.pi * (s : ℝ) / (m : ℝ) := by
        have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd_pos.ne'
        have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show 0 < m by omega).ne'
        have ht_ds : d * s = t := by rw [hsdef]; exact Nat.mul_div_cancel' hd_dvd_t
        have hn_dm : d * m = n := by rw [hmdef]; exact Nat.mul_div_cancel' hd_dvd_n
        have htc : (t : ℝ) = (d : ℝ) * s := by exact_mod_cast ht_ds.symm
        have hnc : (n : ℝ) = (d : ℝ) * m := by exact_mod_cast hn_dm.symm
        rw [htc, hnc]; field_simp
      have hSeq : S t n = ((n / m : ℕ) : ℂ) * S s m := by
        rw [← hts]; exact S_scale n hn hm1 hm_dvd_n s
      have hSim : (S t n).im = ((n / m : ℕ) : ℝ) * (S s m).im := by
        rw [hSeq, Complex.mul_im]
        simp [Complex.natCast_im, Complex.natCast_re]
      rw [harg, hSim]
      ring
  rw [hX, hStep4]

end
end

/- ================= inlined from PosP.lean ================= -/
section

open Complex Finset
open scoped NumberTheorySymbols

noncomputable section

/-! ## Helper lemmas for the positivity of `P m`. -/

/-- Complex cotangent of a real argument is the real cotangent (`rcot`). -/
private lemma complex_cot_ofReal (x : ℝ) : Complex.cot (x : ℂ) = ((rcot x : ℝ) : ℂ) := by
  rw [rcot, ← Real.cot_eq_cos_div_sin, Complex.ofReal_cot]

/-- The Jacobi–symbol Dirichlet character mod `m`. -/
def jChar (m : ℕ) [NeZero m] : DirichletCharacter ℂ m where
  toFun := fun a => ((J((a.val : ℤ) | m) : ℤ) : ℂ)
  map_one' := by
    have hcong : ((( (1 : ZMod m).val : ℤ)) : ZMod m) = ((1 : ℤ) : ZMod m) := by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]; push_cast; ring
    have hmod : ((1 : ZMod m).val : ℤ) % (m : ℤ) = (1 : ℤ) % (m : ℤ) :=
      (ZMod.intCast_eq_intCast_iff' _ _ _).1 hcong
    rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]; simp
  map_mul' := fun a b => by
    show ((J(((a * b).val : ℤ) | m) : ℤ) : ℂ)
      = ((J((a.val : ℤ) | m) : ℤ) : ℂ) * ((J((b.val : ℤ) | m) : ℤ) : ℂ)
    rw [ZMod.val_mul]
    have h1 : ((a.val * b.val % m : ℕ) : ℤ) % (m : ℤ) = ((a.val * b.val : ℕ) : ℤ) % (m : ℤ) := by
      push_cast [Int.natCast_mod]
      exact Int.emod_emod_of_dvd _ dvd_rfl
    rw [jacobiSym.mod_left' h1]
    push_cast
    rw [jacobiSym.mul_left]
    push_cast
    ring
  map_nonunit' := fun a ha => by
    show ((J((a.val : ℤ) | m) : ℤ) : ℂ) = 0
    have hcop : ¬ (a.val).Coprime m := by
      intro hc
      exact ha (by rw [← ZMod.natCast_zmod_val a]; exact (ZMod.isUnit_iff_coprime _ _).2 hc)
    have : J((a.val : ℤ) | m) = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
      exact hcop
    rw [this]; simp

@[simp] lemma jChar_apply (m : ℕ) [NeZero m] (a : ZMod m) :
    jChar m a = ((J((a.val : ℤ) | m) : ℤ) : ℂ) := rfl

lemma jChar_natCast_apply (m : ℕ) [NeZero m] (s : ℕ) (hs : s < m) :
    jChar m (s : ZMod m) = ((J((s : ℤ) | m) : ℤ) : ℂ) := by
  rw [jChar_apply, ZMod.val_natCast_of_lt hs]

/-- Values of `jChar` are real. -/
lemma jChar_im (m : ℕ) [NeZero m] (a : ZMod m) : (jChar m a).im = 0 := by
  rw [jChar_apply]; simp

/-- `jChar` squares to the trivial character. -/
lemma jChar_sq (m : ℕ) [NeZero m] : (jChar m) ^ 2 = 1 := by
  ext a
  rw [MulChar.pow_apply_coe, jChar_apply, MulChar.one_apply_coe]
  have hcop : (a : ZMod m).val.Coprime m := by
    have := a.isUnit
    rw [← ZMod.natCast_zmod_val (a : ZMod m)] at this
    exact (ZMod.isUnit_iff_coprime _ _).1 this
  have hj : J(((a : ZMod m).val : ℤ) | m) ^ 2 = 1 := by
    apply jacobiSym.sq_one
    rw [Int.gcd_natCast_natCast]; exact hcop
  rw [← Int.cast_pow, hj]; simp

lemma jChar_neg_one (m : ℕ) [NeZero m] (hodd : m % 2 = 1) :
    jChar m (-1) = ((ZMod.χ₄ m : ℤ) : ℂ) := by
  rw [jChar_apply]
  have hcong : (((( -1 : ZMod m).val : ℤ)) : ZMod m) = ((-1 : ℤ) : ZMod m) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]; push_cast; ring
  have hmod : ((( -1 : ZMod m).val : ℤ)) % (m : ℤ) = (-1 : ℤ) % (m : ℤ) :=
    (ZMod.intCast_eq_intCast_iff' _ _ _).1 hcong
  rw [jacobiSym.mod_left' hmod, jacobiSym.at_neg_one (Nat.odd_iff.2 hodd)]

/-- **The key assembly lemma.**  Given an odd, real, nontrivial quadratic Dirichlet character
`χ` mod `m` whose values encode the imaginary parts of the Gauss sums, `P m ≥ 0`. -/
private lemma P_nonneg_of_char (m : ℕ) [NeZero m] (hm : 1 < m)
    (χ : DirichletCharacter ℂ m)
    (hsq : χ ^ 2 = 1) (hne : χ ≠ 1) (hodd : χ (-1) = -1)
    (hreal : ∀ a : ZMod m, (χ a).im = 0)
    (htwist : ∀ s : ℕ, s < m → Nat.Coprime s m →
      (S s m).im = Real.sqrt m * (χ (s : ZMod m)).re) :
    0 ≤ P m := by
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  have hsqrtne : Real.sqrt m ≠ 0 := hsqrt.ne'
  -- The cotangent sum equals `P m / √m`.
  have hT : (∑ a ∈ Finset.Ico 1 m, χ (a : ZMod m) * Complex.cot (↑Real.pi * ↑a / ↑m))
      = ((P m / Real.sqrt m : ℝ) : ℂ) := by
    -- rewrite each summand as the coercion of a real number
    have hterm : ∀ a ∈ Finset.Ico 1 m,
        χ (a : ZMod m) * Complex.cot (↑Real.pi * ↑a / ↑m)
          = (((χ (a : ZMod m)).re * rcot (Real.pi * a / m) : ℝ) : ℂ) := by
      intro a _
      have hcot : Complex.cot (↑Real.pi * ↑a / ↑m) = ((rcot (Real.pi * a / m) : ℝ) : ℂ) := by
        rw [show (↑Real.pi * ↑a / ↑m : ℂ) = ((Real.pi * a / m : ℝ) : ℂ) by push_cast; ring,
          complex_cot_ofReal]
      have hcx : χ (a : ZMod m) = (((χ (a : ZMod m)).re : ℝ) : ℂ) := by
        conv_lhs => rw [← Complex.re_add_im (χ (a : ZMod m)), hreal]
        simp
      rw [hcot]
      conv_lhs => rw [hcx]
      rw [← Complex.ofReal_mul]
    rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum]
    congr 1
    -- now a purely real computation
    rw [P]
    -- drop the non-coprime terms
    have hsub : ∑ a ∈ (Finset.Ico 1 m).filter (fun s => Nat.Coprime s m),
          (χ (a : ZMod m)).re * rcot (Real.pi * a / m)
        = ∑ a ∈ Finset.Ico 1 m, (χ (a : ZMod m)).re * rcot (Real.pi * a / m) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a ha hna
      have hncop : ¬ Nat.Coprime a m := by
        simp only [Finset.mem_filter, ha, true_and, not_and] at hna
        exact hna
      have : χ (a : ZMod m) = 0 := by
        apply MulChar.map_nonunit
        rw [ZMod.isUnit_iff_coprime]
        exact hncop
      rw [this]; simp
    rw [← hsub]
    -- on the coprime set, replace the character value by the Gauss sum imaginary part
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mem_filter, Finset.mem_Ico] at ha
    obtain ⟨⟨ha1, ha2⟩, hcop⟩ := ha
    have := htwist a ha2 hcop
    -- (χ a).re = (S a m).im / √m
    have hre : (χ (a : ZMod m)).re = (S a m).im / Real.sqrt m := by
      field_simp
      linarith [this]
    rw [hre]
    ring
  -- Apply the cot-sum formula for the L-function.
  have hcot := DirichletCharacter.LFunction_one_eq_cot_sum (χ := χ) hodd
  rw [hT] at hcot
  -- Rewrite as coercion of a single real number.
  set R : ℝ := (Real.pi / (2 * (m : ℝ))) * (P m / Real.sqrt m) with hRdef
  have hcast : ((R : ℝ) : ℂ)
      = (↑Real.pi / (2 * ↑m)) * ((P m / Real.sqrt m : ℝ) : ℂ) := by
    rw [hRdef]; push_cast; ring
  rw [← hcast] at hcot
  -- positivity of the L-function's real part
  have hpos := DirichletCharacter.LFunction_one_pos hsq hne
  have hRe : (DirichletCharacter.LFunction χ 1).re = R := by rw [hcot]; simp
  have hRpos : 0 < R := hRe ▸ hpos.1
  -- unwind to `P m`
  have hcpos : 0 < Real.pi / (2 * (m : ℝ)) := by positivity
  have hquot : 0 < P m / Real.sqrt m := by
    by_contra h
    push_neg at h
    have : R ≤ 0 := by
      rw [hRdef]; exact mul_nonpos_of_nonneg_of_nonpos hcpos.le h
    linarith [hRpos]
  have hP : 0 < P m := by
    have := mul_pos hquot hsqrt
    rwa [div_mul_cancel₀ _ hsqrtne] at this
  exact hP.le

/-! ### The Gauss-sum twist relations (number theory). -/

/-- **Odd twist relation.**  For odd `m` and `s` coprime to `m`,
`S s m = J(s | m) · S 1 m`. -/
private lemma odd_twist (m : ℕ) [NeZero m] (hoddm : m % 2 = 1) (s : ℕ)
    (hs : Nat.Coprime s m) :
    S s m = ((J((s : ℤ) | m) : ℤ) : ℂ) * S 1 m :=
  odd_twist_thm m hoddm s hs

/-! ### Dyadic Gauss sums. -/

/-- Normalized exponential `epow x = exp(2πi x)`. -/
private def epow (x : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

private lemma epow_zero : epow 0 = 1 := by
  rw [epow, mul_zero, Complex.exp_zero]

private lemma epow_add (x y : ℂ) : epow (x + y) = epow x * epow y := by
  rw [epow, epow, epow, mul_add, Complex.exp_add]

private lemma epow_int (n : ℤ) : epow (n : ℂ) = 1 := by
  rw [epow, show (2 * Real.pi * Complex.I * (n : ℂ)) = (n : ℂ) * (2 * Real.pi * Complex.I) by ring,
    Complex.exp_int_mul_two_pi_mul_I]

private lemma epow_add_int (x : ℂ) (n : ℤ) : epow (x + n) = epow x := by
  rw [epow_add, epow_int, mul_one]

/-- `Sz` in terms of `epow`. -/
private lemma Sz_epow (s : ℤ) (n : ℕ) :
    OddTwist.Sz s n = ∑ k ∈ Finset.range n, epow ((s : ℂ) * (k : ℂ) ^ 2 / (n : ℂ)) := by
  rw [OddTwist.Sz]
  apply Finset.sum_congr rfl
  intro k _
  rw [epow]
  congr 1
  ring

/-- Periodicity of `epow (a/d)` in `a` modulo `d`. -/
private lemma epow_div_period (a : ℤ) (d : ℕ) (hd : d ≠ 0) :
    epow ((a : ℂ) / (d : ℂ)) = epow (((a % (d : ℤ) : ℤ) : ℂ) / (d : ℂ)) := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  set q : ℤ := a / (d : ℤ) with hq
  set r : ℤ := a % (d : ℤ) with hr
  have hdecomp : a = (d : ℤ) * q + r := by rw [hq, hr, Int.ediv_add_emod]
  have hc : (a : ℂ) = (d : ℂ) * (q : ℂ) + (r : ℂ) := by exact_mod_cast hdecomp
  have : (a : ℂ) / (d : ℂ) = (r : ℂ) / (d : ℂ) + (q : ℂ) := by
    rw [hc]; field_simp; ring
  rw [this, epow_add_int]

/-- Base case at modulus 4. -/
private lemma Sz_four (a : ℤ) : OddTwist.Sz a 4 = 2 + 2 * epow ((a : ℂ) / 4) := by
  rw [Sz_epow]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  push_cast
  have h0 : epow ((a : ℂ) * (0 : ℂ) ^ 2 / 4) = 1 := by
    rw [show ((a : ℂ) * (0 : ℂ) ^ 2 / 4) = 0 by ring, epow_zero]
  have h1 : epow ((a : ℂ) * (1 : ℂ) ^ 2 / 4) = epow ((a : ℂ) / 4) := by ring_nf
  have h2 : epow ((a : ℂ) * (2 : ℂ) ^ 2 / 4) = 1 := by
    rw [show ((a : ℂ) * (2 : ℂ) ^ 2 / 4) = ((a : ℤ) : ℂ) by push_cast; ring, epow_int]
  have h3 : epow ((a : ℂ) * (3 : ℂ) ^ 2 / 4) = epow ((a : ℂ) / 4) := by
    rw [show ((a : ℂ) * (3 : ℂ) ^ 2 / 4) = (a : ℂ) / 4 + ((2 * a : ℤ) : ℂ) by push_cast; ring,
      epow_add_int]
  rw [h0, h1, h2, h3]; ring

/-- Base case at modulus 8. -/
private lemma Sz_eight (a : ℤ) :
    OddTwist.Sz a 8 = 2 + 2 * epow ((a : ℂ) / 2) + 4 * epow ((a : ℂ) / 8) := by
  rw [Sz_epow]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  push_cast
  have h0 : epow ((a : ℂ) * (0 : ℂ) ^ 2 / 8) = 1 := by
    rw [show ((a : ℂ) * (0 : ℂ) ^ 2 / 8) = 0 by ring, epow_zero]
  have h1 : epow ((a : ℂ) * (1 : ℂ) ^ 2 / 8) = epow ((a : ℂ) / 8) := by ring_nf
  have h2 : epow ((a : ℂ) * (2 : ℂ) ^ 2 / 8) = epow ((a : ℂ) / 2) := by
    rw [show ((a : ℂ) * (2 : ℂ) ^ 2 / 8) = (a : ℂ) / 2 by ring]
  have h3 : epow ((a : ℂ) * (3 : ℂ) ^ 2 / 8) = epow ((a : ℂ) / 8) := by
    rw [show ((a : ℂ) * (3 : ℂ) ^ 2 / 8) = (a : ℂ) / 8 + ((a : ℤ) : ℂ) by push_cast; ring,
      epow_add_int]
  have h4 : epow ((a : ℂ) * (4 : ℂ) ^ 2 / 8) = 1 := by
    rw [show ((a : ℂ) * (4 : ℂ) ^ 2 / 8) = ((2 * a : ℤ) : ℂ) by push_cast; ring, epow_int]
  have h5 : epow ((a : ℂ) * (5 : ℂ) ^ 2 / 8) = epow ((a : ℂ) / 8) := by
    rw [show ((a : ℂ) * (5 : ℂ) ^ 2 / 8) = (a : ℂ) / 8 + ((3 * a : ℤ) : ℂ) by push_cast; ring,
      epow_add_int]
  have h6 : epow ((a : ℂ) * (6 : ℂ) ^ 2 / 8) = epow ((a : ℂ) / 2) := by
    rw [show ((a : ℂ) * (6 : ℂ) ^ 2 / 8) = (a : ℂ) / 2 + ((4 * a : ℤ) : ℂ) by push_cast; ring,
      epow_add_int]
  have h7 : epow ((a : ℂ) * (7 : ℂ) ^ 2 / 8) = epow ((a : ℂ) / 8) := by
    rw [show ((a : ℂ) * (7 : ℂ) ^ 2 / 8) = (a : ℂ) / 8 + ((6 * a : ℤ) : ℂ) by push_cast; ring,
      epow_add_int]
  rw [h0, h1, h2, h3, h4, h5, h6, h7]; ring

private lemma epow_int_pow (x : ℂ) (n : ℕ) : epow x ^ n = epow ((n : ℂ) * x) := by
  rw [epow, epow, ← Complex.exp_nat_mul]; congr 1; ring

/-- `epow (1/2) = -1`. -/
private lemma epow_half_one : epow (((1 : ℤ) : ℂ) / 2) = -1 := by
  rw [epow, show (2 * Real.pi * Complex.I * (((1 : ℤ) : ℂ) / 2)) = (Real.pi : ℂ) * Complex.I by
    push_cast; ring, Complex.exp_pi_mul_I]

/-- `epow (a/2) = -1` for odd `a`. -/
private lemma epow_half_odd (a : ℤ) (ha : a % 2 = 1) : epow ((a : ℂ) / 2) = -1 := by
  obtain ⟨t, rfl⟩ : ∃ t, a = 2 * t + 1 := ⟨a / 2, by omega⟩
  rw [show ((2 * t + 1 : ℤ) : ℂ) / 2 = ((1 : ℤ) : ℂ) / 2 + ((t : ℤ) : ℂ) by push_cast; ring,
    epow_add_int, epow_half_one]

/-- `epow (1/4) = I`. -/
private lemma epow_quarter_one : epow (((1 : ℤ) : ℂ) / 4) = Complex.I := by
  rw [epow, show (2 * Real.pi * Complex.I * (((1 : ℤ) : ℂ) / 4)) = ((Real.pi : ℂ) / 2) * Complex.I by
    push_cast; ring, Complex.exp_pi_div_two_mul_I]

/-- `epow (3/4) = -I`. -/
private lemma epow_quarter_three : epow (((3 : ℤ) : ℂ) / 4) = -Complex.I := by
  rw [show ((3 : ℤ) : ℂ) / 4 = ((-1 : ℤ) : ℂ) / 4 + ((1 : ℤ) : ℂ) by push_cast; ring, epow_add_int,
    epow, show (2 * Real.pi * Complex.I * (((-1 : ℤ) : ℂ) / 4)) = -((Real.pi : ℂ) / 2 * Complex.I) by
      push_cast; ring, Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]

/-- `epow (a/4)` in terms of `χ₄` for odd `a`. -/
private lemma epow_quarter (a : ℤ) (ha : a % 2 = 1) :
    epow ((a : ℂ) / 4) = Complex.I * ((ZMod.χ₄ (a : ZMod 4) : ℤ) : ℂ) := by
  have hcases : a % 4 = 1 ∨ a % 4 = 3 := by omega
  rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, epow_div_period a 4 (by norm_num)]
  simp only [Nat.cast_ofNat]
  rcases hcases with h | h
  · rw [h, epow_quarter_one, ZMod.χ₄_int_one_mod_four h]; push_cast; ring
  · rw [h, epow_quarter_three, ZMod.χ₄_int_three_mod_four h]; push_cast; ring

/-- `epow (1/8) = (√2/2)(1 + I)`. -/
private lemma epow_eighth_one :
    epow (((1 : ℤ) : ℂ) / 8) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + Complex.I) := by
  rw [epow, show (2 * Real.pi * Complex.I * (((1 : ℤ) : ℂ) / 8)) = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast; ring

/-- `zeta² = I` where `zeta = (√2/2)(1+I)`. -/
private lemma zeta_sq : (((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + Complex.I)) ^ 2 = Complex.I := by
  have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc2 : ((Real.sqrt 2 / 2 : ℝ) : ℂ) ^ 2 = 1 / 2 := by
    rw [← Complex.ofReal_pow, show (Real.sqrt 2 / 2) ^ 2 = 1 / 2 by rw [div_pow, hsqrt2]; norm_num]
    norm_num
  rw [mul_pow, hc2, add_sq, one_pow, mul_one, Complex.I_sq]; ring

/-- `epow (a/8)` in terms of `χ₈`, `χ₈'` for odd `a`. -/
private lemma epow_eighth (a : ℤ) (ha : a % 2 = 1) :
    epow ((a : ℂ) / 8) =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (((ZMod.χ₈ (a : ZMod 8) : ℤ) : ℂ) +
        Complex.I * ((ZMod.χ₈' (a : ZMod 8) : ℤ) : ℂ)) := by
  have hcases : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
  have hζ := epow_eighth_one
  have hz2 := zeta_sq
  set c : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ) with hc
  rw [show (8 : ℂ) = ((8 : ℕ) : ℂ) by norm_num, epow_div_period a 8 (by norm_num)]
  simp only [Nat.cast_ofNat]
  have hpow : ∀ n : ℕ, epow (((n : ℕ) : ℂ) / 8) = (c * (1 + Complex.I)) ^ n := by
    intro n
    rw [show ((n : ℕ) : ℂ) / 8 = ((n : ℕ) : ℂ) * (((1 : ℤ) : ℂ) / 8) by push_cast; ring,
      ← epow_int_pow, hζ]
  -- character values
  rw [ZMod.χ₈_int_eq_if_mod_eight a, ZMod.χ₈'_int_eq_if_mod_eight a]
  rcases hcases with h | h | h | h
  · rw [h, show ((1 : ℤ) : ℂ) / 8 = ((1 : ℕ) : ℂ) / 8 by norm_num, hpow 1]
    simp only [ha]; norm_num
  · rw [h, show ((3 : ℤ) : ℂ) / 8 = ((3 : ℕ) : ℂ) / 8 by norm_num, hpow 3,
      show (c * (1 + Complex.I)) ^ 3 = (c * (1 + Complex.I)) ^ 2 * (c * (1 + Complex.I)) by ring, hz2]
    simp only [ha]; norm_num
    push_cast
    linear_combination c * Complex.I_sq
  · rw [h, show ((5 : ℤ) : ℂ) / 8 = ((5 : ℕ) : ℂ) / 8 by norm_num, hpow 5,
      show (c * (1 + Complex.I)) ^ 5 = ((c * (1 + Complex.I)) ^ 2) ^ 2 * (c * (1 + Complex.I)) by ring,
      hz2, Complex.I_sq]
    simp only [ha]; norm_num
    push_cast; ring
  · rw [h, show ((7 : ℤ) : ℂ) / 8 = ((7 : ℕ) : ℂ) / 8 by norm_num, hpow 7,
      show (c * (1 + Complex.I)) ^ 7 = ((c * (1 + Complex.I)) ^ 2) ^ 3 * (c * (1 + Complex.I)) by ring,
      hz2, show (Complex.I) ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq]; ring]
    simp only [ha]; norm_num
    push_cast
    linear_combination (-c) * Complex.I_sq

/-- Pairing decomposition of a sum over `range (2M)`. -/
private lemma sum_range_two_mul (f : ℕ → ℂ) (M : ℕ) :
    ∑ b ∈ Finset.range (2 * M), f b = ∑ j ∈ Finset.range M, (f (2 * j) + f (2 * j + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    ring

/-- **Descent** for dyadic Gauss sums: `Sz a (4M) = 2 · Sz a M` for odd `a` and `4 ∣ M`. -/
private lemma Sz_descent (a : ℤ) (M : ℕ) (hM : 4 ∣ M) (hM0 : M ≠ 0) (ha : a % 2 = 1) :
    OddTwist.Sz a (4 * M) = 2 * OddTwist.Sz a M := by
  obtain ⟨t, hMt⟩ : ∃ t, M = 4 * t := hM
  have ht0 : t ≠ 0 := by rintro rfl; simp [hMt] at hM0
  have hMc : (M : ℂ) = 4 * (t : ℂ) := by exact_mod_cast hMt
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  have hMcne : (M : ℂ) ≠ 0 := by exact_mod_cast hM0
  -- the two summand families
  set g4 : ℕ → ℂ := fun k => epow ((a : ℂ) * (k : ℂ) ^ 2 / ((4 * M : ℕ) : ℂ)) with hg4
  set gM : ℕ → ℂ := fun k => epow ((a : ℂ) * (k : ℂ) ^ 2 / ((M : ℕ) : ℂ)) with hgM
  -- shift by 2M leaves g4 invariant
  have hshift2M : ∀ i : ℕ, g4 (2 * M + i) = g4 i := by
    intro i
    simp only [hg4]
    rw [show (a : ℂ) * ((2 * M + i : ℕ) : ℂ) ^ 2 / ((4 * M : ℕ) : ℂ)
        = (a : ℂ) * ((i : ℕ) : ℂ) ^ 2 / ((4 * M : ℕ) : ℂ)
          + ((a * ((i : ℤ) + 4 * (t : ℤ)) : ℤ) : ℂ) by
      push_cast; rw [hMc]; field_simp; ring, epow_add_int]
  -- shift by M negates g4 on odd inputs
  have hshiftM : ∀ b : ℕ, b % 2 = 1 → g4 (b + M) = - g4 b := by
    intro b hb
    simp only [hg4]
    rw [show (a : ℂ) * ((b + M : ℕ) : ℂ) ^ 2 / ((4 * M : ℕ) : ℂ)
        = (a : ℂ) * ((b : ℕ) : ℂ) ^ 2 / ((4 * M : ℕ) : ℂ) + ((a * (b : ℤ) : ℤ) : ℂ) / 2
          + ((a * (t : ℤ) : ℤ) : ℂ) by
      push_cast; rw [hMc]; field_simp; ring, epow_add_int, epow_add,
      epow_half_odd (a * (b : ℤ)) (by
        have hbz : (b : ℤ) % 2 = 1 := by exact_mod_cast hb
        exact Int.odd_iff.1 ((Int.odd_iff.2 ha).mul (Int.odd_iff.2 hbz)))]
    ring
  -- even shift: g4 (2j) = gM j
  have heven : ∀ j : ℕ, g4 (2 * j) = gM j := by
    intro j
    simp only [hg4, hgM]
    congr 1
    push_cast
    rw [hMc]; field_simp; ring
  rw [Sz_epow a (4 * M), Sz_epow a M]
  show (∑ k ∈ Finset.range (4 * M), g4 k) = 2 * ∑ k ∈ Finset.range M, gM k
  -- c-split: sum over range (4M) = 2 * sum over range (2M)
  have hc : (∑ k ∈ Finset.range (4 * M), g4 k) = 2 * ∑ b ∈ Finset.range (2 * M), g4 b := by
    rw [show 4 * M = 2 * M + 2 * M by ring, Finset.sum_range_add]
    have : (∑ i ∈ Finset.range (2 * M), g4 (2 * M + i)) = ∑ i ∈ Finset.range (2 * M), g4 i :=
      Finset.sum_congr rfl (fun i _ => hshift2M i)
    rw [this]; ring
  rw [hc, sum_range_two_mul g4 M, Finset.sum_add_distrib]
  -- even part = Sz a M, odd part = 0
  have hevensum : (∑ j ∈ Finset.range M, g4 (2 * j)) = ∑ k ∈ Finset.range M, gM k :=
    Finset.sum_congr rfl (fun j _ => heven j)
  have hoddsum : (∑ j ∈ Finset.range M, g4 (2 * j + 1)) = 0 := by
    rw [show M = 2 * t + 2 * t by omega, Finset.sum_range_add]
    have hkey : (∑ i ∈ Finset.range (2 * t), g4 (2 * (2 * t + i) + 1))
        = ∑ i ∈ Finset.range (2 * t), (- g4 (2 * i + 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      have : 2 * (2 * t + i) + 1 = (2 * i + 1) + M := by omega
      rw [this, hshiftM (2 * i + 1) (by omega)]
    rw [hkey, Finset.sum_neg_distrib]
    ring
  rw [hevensum, hoddsum]
  ring

/-- Closed form of the dyadic Gauss sum at modulus 4, odd `a`. -/
private lemma Sz_four_char (a : ℤ) (ha : a % 2 = 1) :
    OddTwist.Sz a 4 = 2 * (1 + Complex.I * ((ZMod.χ₄ (a : ZMod 4) : ℤ) : ℂ)) := by
  rw [Sz_four, epow_quarter a ha]; ring

/-- Closed form of the dyadic Gauss sum at modulus 8, odd `a`. -/
private lemma Sz_eight_char (a : ℤ) (ha : a % 2 = 1) :
    OddTwist.Sz a 8 = 2 * (Real.sqrt 2 : ℂ) *
      (((ZMod.χ₈ (a : ZMod 8) : ℤ) : ℂ) + Complex.I * ((ZMod.χ₈' (a : ZMod 8) : ℤ) : ℂ)) := by
  rw [Sz_eight, epow_half_odd a ha, epow_eighth a ha]
  push_cast
  ring

private lemma sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Closed form for even exponent: `Sz a (2^(2f)) = √(2^(2f))·(1 + I·χ₄ a)`. -/
private lemma Sz_pow_even (a : ℤ) (ha : a % 2 = 1) : ∀ f : ℕ, 1 ≤ f →
    OddTwist.Sz a (2 ^ (2 * f)) = (Real.sqrt ((2 : ℝ) ^ (2 * f)) : ℂ) *
      (1 + Complex.I * ((ZMod.χ₄ (a : ZMod 4) : ℤ) : ℂ)) := by
  intro f
  induction f with
  | zero => intro h; omega
  | succ f ih =>
    intro _
    rcases Nat.eq_zero_or_pos f with hf0 | hf0
    · subst hf0
      rw [show 2 * (0 + 1) = 2 by ring, show (2 : ℕ) ^ 2 = 4 by norm_num, Sz_four_char a ha,
        show (2 : ℝ) ^ (2 * (0 + 1)) = 4 by norm_num, sqrt_four]
      push_cast; ring
    · have hIH := ih (by omega)
      have hdvd : (4 : ℕ) ∣ 2 ^ (2 * f) := by
        rw [show (4 : ℕ) = 2 ^ 2 from rfl]; exact pow_dvd_pow 2 (by omega)
      have hne : (2 : ℕ) ^ (2 * f) ≠ 0 := pow_ne_zero _ (by norm_num)
      have hmul : 2 ^ (2 * (f + 1)) = 4 * 2 ^ (2 * f) := by
        rw [show 2 * (f + 1) = 2 + 2 * f by ring, pow_add]; norm_num
      have hsqrt : Real.sqrt ((2 : ℝ) ^ (2 * (f + 1))) = 2 * Real.sqrt ((2 : ℝ) ^ (2 * f)) := by
        rw [show (2 : ℝ) ^ (2 * (f + 1)) = (2 : ℝ) ^ (2 * f) * 4 by
          rw [show 2 * (f + 1) = 2 * f + 2 by ring, pow_add]; norm_num,
          Real.sqrt_mul (by positivity), sqrt_four]; ring
      rw [hmul, Sz_descent a (2 ^ (2 * f)) hdvd hne ha, hIH, hsqrt]
      push_cast; ring

/-- Closed form for odd exponent: `Sz a (2^(2f+1)) = √(2^(2f+1))·(χ₈ a + I·χ₈' a)`. -/
private lemma Sz_pow_odd (a : ℤ) (ha : a % 2 = 1) : ∀ f : ℕ, 1 ≤ f →
    OddTwist.Sz a (2 ^ (2 * f + 1)) = (Real.sqrt ((2 : ℝ) ^ (2 * f + 1)) : ℂ) *
      (((ZMod.χ₈ (a : ZMod 8) : ℤ) : ℂ) + Complex.I * ((ZMod.χ₈' (a : ZMod 8) : ℤ) : ℂ)) := by
  intro f
  induction f with
  | zero => intro h; omega
  | succ f ih =>
    intro _
    rcases Nat.eq_zero_or_pos f with hf0 | hf0
    · subst hf0
      rw [show 2 * (0 + 1) + 1 = 3 by ring, show (2 : ℕ) ^ 3 = 8 by norm_num, Sz_eight_char a ha,
        show (2 : ℝ) ^ (2 * (0 + 1) + 1) = 8 by norm_num,
        show Real.sqrt 8 = 2 * Real.sqrt 2 by
          rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num), sqrt_four]]
      push_cast; ring
    · have hIH := ih (by omega)
      have hdvd : (4 : ℕ) ∣ 2 ^ (2 * f + 1) := by
        rw [show (4 : ℕ) = 2 ^ 2 from rfl]; exact pow_dvd_pow 2 (by omega)
      have hne : (2 : ℕ) ^ (2 * f + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      have hmul : 2 ^ (2 * (f + 1) + 1) = 4 * 2 ^ (2 * f + 1) := by
        rw [show 2 * (f + 1) + 1 = 2 + (2 * f + 1) by ring, pow_add]; norm_num
      have hsqrt : Real.sqrt ((2 : ℝ) ^ (2 * (f + 1) + 1))
          = 2 * Real.sqrt ((2 : ℝ) ^ (2 * f + 1)) := by
        rw [show (2 : ℝ) ^ (2 * (f + 1) + 1) = (2 : ℝ) ^ (2 * f + 1) * 4 by
          rw [show 2 * (f + 1) + 1 = (2 * f + 1) + 2 by ring, pow_add]; norm_num,
          Real.sqrt_mul (by positivity), sqrt_four]; ring
      rw [hmul, Sz_descent a (2 ^ (2 * f + 1)) hdvd hne ha, hIH, hsqrt]
      push_cast; ring

/-- Combined character: dyadic part `D` (mod `d`) times the Jacobi character mod `m₀`. -/
private def combChar (m d m₀ : ℕ) [NeZero m] [NeZero m₀] (hd : d ∣ m) (hm₀ : m₀ ∣ m)
    (D : MulChar (ZMod d) ℤ)
    (hsplit : ∀ x : ZMod m, ¬ IsUnit x →
      ¬ IsUnit ((ZMod.castHom hd (ZMod d)) x) ∨ ¬ IsUnit ((ZMod.castHom hm₀ (ZMod m₀)) x)) :
    DirichletCharacter ℂ m where
  toFun x := ((D ((ZMod.castHom hd (ZMod d)) x) : ℤ) : ℂ)
    * jChar m₀ ((ZMod.castHom hm₀ (ZMod m₀)) x)
  map_one' := by
    simp only [map_one, MulChar.map_one]
    norm_num
  map_mul' x y := by
    simp only [map_mul]
    push_cast
    ring
  map_nonunit' x hx := by
    rcases hsplit x hx with h | h
    · rw [D.map_nonunit h]; simp
    · rw [(jChar m₀).map_nonunit h]; ring

private lemma combChar_apply (m d m₀ : ℕ) [NeZero m] [NeZero m₀] (hd : d ∣ m) (hm₀ : m₀ ∣ m)
    (D : MulChar (ZMod d) ℤ) (hsplit) (x : ZMod m) :
    combChar m d m₀ hd hm₀ D hsplit x
      = ((D ((ZMod.castHom hd (ZMod d)) x) : ℤ) : ℂ)
        * jChar m₀ ((ZMod.castHom hm₀ (ZMod m₀)) x) := rfl

private lemma combChar_natCast (m d m₀ : ℕ) [NeZero m] [NeZero m₀] (hd : d ∣ m) (hm₀ : m₀ ∣ m)
    (D : MulChar (ZMod d) ℤ) (hsplit) (s : ℕ) :
    combChar m d m₀ hd hm₀ D hsplit (s : ZMod m)
      = ((D (s : ZMod d) : ℤ) : ℂ) * jChar m₀ (s : ZMod m₀) := by
  rw [combChar_apply, map_natCast (ZMod.castHom hd (ZMod d)) s,
    map_natCast (ZMod.castHom hm₀ (ZMod m₀)) s]

private lemma combChar_im (m d m₀ : ℕ) [NeZero m] [NeZero m₀] (hd : d ∣ m) (hm₀ : m₀ ∣ m)
    (D : MulChar (ZMod d) ℤ) (hsplit) (x : ZMod m) :
    (combChar m d m₀ hd hm₀ D hsplit x).im = 0 := by
  rw [combChar_apply]
  simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, jChar_im (m₀)]
  ring

private lemma combChar_isquad (m d m₀ : ℕ) [NeZero m] [NeZero m₀] (hd : d ∣ m) (hm₀ : m₀ ∣ m)
    (D : MulChar (ZMod d) ℤ) (hDq : D.IsQuadratic) (hsplit) :
    (combChar m d m₀ hd hm₀ D hsplit).IsQuadratic := by
  intro x
  rw [combChar_apply, jChar_apply]
  have hDv := hDq ((ZMod.castHom hd (ZMod d)) x)
  have hJv := jacobiSym.trichotomy (((ZMod.castHom hm₀ (ZMod m₀)) x).val : ℤ) m₀
  rcases hDv with h | h | h <;> rcases hJv with hj | hj | hj <;>
    rw [h, hj] <;> simp

private lemma re_intCast_mul (a b : ℤ) : (((a : ℤ) : ℂ) * ((b : ℤ) : ℂ)).re = (a : ℝ) * (b : ℝ) := by
  simp [Complex.mul_re]

private lemma chi8_sq_odd (b : ℤ) (hb : b % 2 = 1) : ZMod.χ₈ ((b : ZMod 8)) ^ 2 = 1 := by
  rw [ZMod.χ₈_int_eq_if_mod_eight, if_neg (by omega)]
  split <;> norm_num

private lemma chi8_mul_chi8'_odd (b : ℤ) (hb : b % 2 = 1) :
    ZMod.χ₈ (b : ZMod 8) * ZMod.χ₈' (b : ZMod 8) = ZMod.χ₄ (b : ZMod 4) := by
  have h2 := chi8_sq_odd b hb
  rw [ZMod.χ₈'_int_eq_χ₄_mul_χ₈,
    show ZMod.χ₈ (b : ZMod 8) * (ZMod.χ₄ (b : ZMod 4) * ZMod.χ₈ (b : ZMod 8))
        = ZMod.χ₄ (b : ZMod 4) * ZMod.χ₈ (b : ZMod 8) ^ 2 by ring, h2, mul_one]

/-- **Existence of the even quadratic character** for `4 ∣ m`. -/
private lemma exists_even_char (m : ℕ) [NeZero m] (h4 : m % 4 = 0) (hm : 1 < m) :
    ∃ χ : DirichletCharacter ℂ m, χ ^ 2 = 1 ∧ χ ≠ 1 ∧ χ (-1) = -1 ∧
      (∀ a : ZMod m, (χ a).im = 0) ∧
      (∀ s : ℕ, s < m → Nat.Coprime s m →
        (S s m).im = Real.sqrt m * (χ (s : ZMod m)).re) := by
  have hm0 : m ≠ 0 := NeZero.ne m
  obtain ⟨e, m₀, hm00, hm0odd, he2, hcop, hm₀dvd, h2edvd, hme⟩ :
      ∃ e m₀, m₀ ≠ 0 ∧ m₀ % 2 = 1 ∧ 2 ≤ e ∧ Nat.Coprime (2 ^ e) m₀ ∧ m₀ ∣ m ∧ 2 ^ e ∣ m
        ∧ 2 ^ e * m₀ = m := by
    refine ⟨m.factorization 2, ordCompl[2] m, (Nat.ordCompl_pos 2 hm0).ne', ?_, ?_, ?_,
      Nat.ordCompl_dvd m 2, Nat.ordProj_dvd m 2, Nat.ordProj_mul_ordCompl_eq_self m 2⟩
    · have : ¬ 2 ∣ ordCompl[2] m := Nat.not_dvd_ordCompl Nat.prime_two hm0
      omega
    · have h4dvd : (2 : ℕ) ^ 2 ∣ m := by
        rw [show (2 : ℕ) ^ 2 = 4 from rfl]; exact Nat.dvd_of_mod_eq_zero h4
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm0).1 h4dvd
    · exact (Nat.coprime_ordCompl Nat.prime_two hm0).pow_left _
  haveI : NeZero m₀ := ⟨hm00⟩
  have hm0odd' : Odd m₀ := Nat.odd_iff.2 hm0odd
  have hd4 : (4 : ℕ) ∣ m := Nat.dvd_of_mod_eq_zero h4
  -- jChar value at a natural
  have hjChar_val : ∀ s : ℕ, jChar m₀ (s : ZMod m₀) = ((J((s : ℤ) | m₀) : ℤ) : ℂ) := by
    intro s
    rw [jChar_apply]
    have hmod : ((s : ZMod m₀).val : ℤ) % (m₀ : ℤ) = (s : ℤ) % (m₀ : ℤ) := by
      rw [ZMod.val_natCast, Int.natCast_mod, Int.emod_emod_of_dvd _ dvd_rfl]
    rw [jacobiSym.mod_left' hmod]
  -- √m factorization
  have hRm : Real.sqrt (m : ℝ) = Real.sqrt ((2 : ℝ) ^ e) * Real.sqrt (m₀ : ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    rw [← hme]; push_cast; ring
  -- coprimality of s with m₀
  have hcop_sm₀ : ∀ s : ℕ, Nat.Coprime s m → Nat.Coprime s m₀ :=
    fun s hs => hs.coprime_dvd_right hm₀dvd
  have hs_odd : ∀ s : ℕ, Nat.Coprime s m → s % 2 = 1 := by
    intro s hs
    have h2m : (2 : ℕ) ∣ m := dvd_trans (by norm_num) hd4
    have : Nat.Coprime s 2 := hs.coprime_dvd_right h2m
    exact Nat.odd_iff.1 (Nat.coprime_two_right.1 this)
  -- factorization of the Gauss sum
  have hSfact : ∀ s : ℕ, Nat.Coprime s m →
      S s m = OddTwist.Sz ((s : ℤ) * (m₀ : ℤ)) (2 ^ e)
        * (((J((s : ℤ) * ((2 ^ e : ℕ) : ℤ) | m₀) : ℤ) : ℂ) * S 1 m₀) := by
    intro s hs
    have hgcd : ((s : ℤ) * ((2 ^ e : ℕ) : ℤ)).gcd ((m₀ : ℕ) : ℤ) = 1 := by
      have hc : Nat.Coprime (s * 2 ^ e) m₀ := Nat.Coprime.mul (hcop_sm₀ s hs) hcop
      have hh := Int.isCoprime_iff_gcd_eq_one.mp (Nat.isCoprime_iff_coprime.mpr hc)
      rw [show ((s : ℤ) * ((2 ^ e : ℕ) : ℤ)) = ((s * 2 ^ e : ℕ) : ℤ) by push_cast; ring, hh]
    rw [OddTwist.S_eq_Sz, ← hme, OddTwist.block1 (s : ℤ) (2 ^ e) m₀ (by positivity) hm00 hcop,
      OddTwist.aux m₀ hm0odd' ((s : ℤ) * ((2 ^ e : ℕ) : ℤ)) hgcd]
    have hSz1 : OddTwist.Sz (1 : ℤ) m₀ = S 1 m₀ := by
      have := OddTwist.S_eq_Sz 1 m₀; rw [Nat.cast_one] at this; rw [this]
    rw [hSz1]
  -- the generic split lemma for combChar
  have hsplit_gen : ∀ (d : ℕ) (hdd : d ∣ m), d ≠ 0 → 2 ∣ d →
      ∀ x : ZMod m, ¬ IsUnit x →
        ¬ IsUnit ((ZMod.castHom hdd (ZMod d)) x)
          ∨ ¬ IsUnit ((ZMod.castHom hm₀dvd (ZMod m₀)) x) := by
    intro d hdd hd0 hd2 x hx
    haveI : NeZero d := ⟨hd0⟩
    have hcast_d : (ZMod.castHom hdd (ZMod d)) x = ((x.val : ℕ) : ZMod d) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val x]
      rw [map_natCast]
    have hcast_m₀ : (ZMod.castHom hm₀dvd (ZMod m₀)) x = ((x.val : ℕ) : ZMod m₀) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val x]
      rw [map_natCast]
    have hxc : ¬ Nat.Coprime x.val m := by
      intro hc
      exact hx (by rw [← ZMod.natCast_zmod_val x]; exact (ZMod.isUnit_iff_coprime _ _).2 hc)
    by_cases hev : 2 ∣ x.val
    · left
      rw [hcast_d, ZMod.isUnit_iff_coprime]
      intro hcop'
      have : (2 : ℕ) ∣ Nat.gcd x.val d := Nat.dvd_gcd hev hd2
      rw [hcop'] at this; norm_num at this
    · right
      rw [hcast_m₀, ZMod.isUnit_iff_coprime]
      intro hcop'
      have hodd2 : Nat.Coprime x.val 2 := Nat.coprime_two_right.2 (Nat.odd_iff.2 (by omega))
      have hcop2e : Nat.Coprime x.val (2 ^ e) := hodd2.pow_right e
      have hfull : Nat.Coprime x.val (2 ^ e * m₀) := hcop2e.mul_right hcop'
      rw [hme] at hfull
      exact hxc hfull
  -- helper: cast of -1 through the ring homs
  have hcnm : (ZMod.castHom hm₀dvd (ZMod m₀)) (-1) = -1 := by rw [map_neg, map_one]
  rcases Nat.even_or_odd' e with ⟨f, hf | hf⟩
  · -- e = 2f (even)
    subst hf
    have hf1 : 1 ≤ f := by omega
    have hcn4 : (ZMod.castHom hd4 (ZMod 4)) (-1) = -1 := by rw [map_neg, map_one]
    -- J of the square part is 1
    have hgcd2f : ((2 ^ f : ℕ) : ℤ).gcd ((m₀ : ℕ) : ℤ) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp
        (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_two_left.2 hm0odd').pow_left f))
    have hJ2 : (J(((2 ^ (2 * f) : ℕ) : ℤ) | m₀) : ℤ) = 1 := by
      rw [show ((2 ^ (2 * f) : ℕ) : ℤ) = (((2 ^ f : ℕ) : ℤ)) ^ 2 by push_cast; ring,
        jacobiSym.pow_left]
      exact jacobiSym.sq_one hgcd2f
    have hJc : ∀ s : ℕ, (J((s : ℤ) * ((2 ^ (2 * f) : ℕ) : ℤ) | m₀) : ℤ) = J((s : ℤ) | m₀) := by
      intro s; rw [jacobiSym.mul_left, hJ2, mul_one]
    rcases (show m₀ % 4 = 1 ∨ m₀ % 4 = 3 by omega) with hm4 | hm4
    · -- branch 1: D = χ₄
      set hsp4 := hsplit_gen 4 hd4 (by norm_num) (by norm_num) with hsp4_def
      set χ := combChar m 4 m₀ hd4 hm₀dvd ZMod.χ₄ hsp4 with hχ_def
      have hneg : χ (-1) = -1 := by
        rw [hχ_def, combChar_apply, hcn4, hcnm, jChar_neg_one m₀ hm0odd,
          show ZMod.χ₄ (-1 : ZMod 4) = -1 from by decide, ZMod.χ₄_nat_one_mod_four hm4]
        norm_num
      refine ⟨χ, ?_, ?_, hneg, fun a => combChar_im m 4 m₀ hd4 hm₀dvd ZMod.χ₄ hsp4 a, ?_⟩
      · rw [hχ_def]
        exact (combChar_isquad m 4 m₀ hd4 hm₀dvd ZMod.χ₄ ZMod.isQuadratic_χ₄ hsp4).sq_eq_one
      · intro hc
        rw [hc, MulChar.one_apply (isUnit_one.neg)] at hneg; norm_num at hneg
      · intro s hsm hcop
        have hsodd := hs_odd s hcop
        have ha : ((s : ℤ) * (m₀ : ℤ)) % 2 = 1 :=
          Int.odd_iff.1 ((Int.odd_iff.2 (by exact_mod_cast hsodd)).mul
            (Int.odd_iff.2 (by exact_mod_cast hm0odd)))
        have hSval1 : S 1 m₀ = ((Real.sqrt (m₀ : ℝ)) : ℂ) := (GaussGen.S_value m₀).1 hm4
        have hIdR : (J((s : ℤ) * ((2 ^ (2 * f) : ℕ) : ℤ) | m₀) : ℤ)
            * (ZMod.χ₄ (((s : ℤ) * (m₀ : ℤ)) : ZMod 4))
            = (ZMod.χ₄ (s : ZMod 4)) * (J((s : ℤ) | m₀)) := by
          rw [hJc s, show (((s : ℤ) * (m₀ : ℤ)) : ZMod 4) = ((s : ℤ) : ZMod 4) * ((m₀ : ℤ) : ZMod 4)
              by push_cast; ring, map_mul,
            ZMod.χ₄_int_one_mod_four (by exact_mod_cast hm4 : ((m₀ : ℤ)) % 4 = 1), Int.cast_natCast]
          ring
        have hIdRr : ((J((s : ℤ) * ((2 ^ (2 * f) : ℕ) : ℤ) | m₀) : ℤ) : ℝ)
            * ((ZMod.χ₄ (((s : ℤ) * (m₀ : ℤ)) : ZMod 4) : ℤ) : ℝ)
            = ((ZMod.χ₄ (s : ZMod 4) : ℤ) : ℝ) * ((J((s : ℤ) | m₀) : ℤ) : ℝ) := by
          exact_mod_cast hIdR
        have hχre : (χ (s : ZMod m)).re
            = ((ZMod.χ₄ (s : ZMod 4) : ℤ) : ℝ) * ((J((s : ℤ) | m₀) : ℤ) : ℝ) := by
          rw [hχ_def, combChar_natCast m 4 m₀ hd4 hm₀dvd ZMod.χ₄ hsp4 s, hjChar_val s, re_intCast_mul]
        rw [hSfact s hcop, Sz_pow_even ((s : ℤ) * (m₀ : ℤ)) ha f hf1, hSval1, hχre, hRm]
        simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.one_re,
          Complex.one_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.intCast_re, Complex.intCast_im]
        rw [Int.cast_mul]
        linear_combination (Real.sqrt ((2 : ℝ) ^ (2 * f)) * Real.sqrt (m₀ : ℝ)) * hIdRr
    · -- branch 2: D = 1 (trivial), m₀ % 4 = 3
      have hq1 : (1 : MulChar (ZMod 4) ℤ).IsQuadratic := by
        intro a
        by_cases h : IsUnit a
        · exact Or.inr (Or.inl (MulChar.one_apply h))
        · exact Or.inl (MulChar.map_nonunit 1 h)
      set hsp4 := hsplit_gen 4 hd4 (by norm_num) (by norm_num) with hsp4_def
      set χ := combChar m 4 m₀ hd4 hm₀dvd (1 : MulChar (ZMod 4) ℤ) hsp4 with hχ_def
      have hneg : χ (-1) = -1 := by
        rw [hχ_def, combChar_apply, hcn4, hcnm, jChar_neg_one m₀ hm0odd,
          MulChar.one_apply (isUnit_one.neg), ZMod.χ₄_nat_three_mod_four hm4]
        norm_num
      refine ⟨χ, ?_, ?_, hneg, fun a => combChar_im m 4 m₀ hd4 hm₀dvd _ hsp4 a, ?_⟩
      · rw [hχ_def]
        exact (combChar_isquad m 4 m₀ hd4 hm₀dvd (1 : MulChar (ZMod 4) ℤ) hq1 hsp4).sq_eq_one
      · intro hc
        rw [hc, MulChar.one_apply (isUnit_one.neg)] at hneg; norm_num at hneg
      · intro s hsm hcop
        have hsodd := hs_odd s hcop
        have ha : ((s : ℤ) * (m₀ : ℤ)) % 2 = 1 :=
          Int.odd_iff.1 ((Int.odd_iff.2 (by exact_mod_cast hsodd)).mul
            (Int.odd_iff.2 (by exact_mod_cast hm0odd)))
        have hSval1 : S 1 m₀ = Complex.I * ((Real.sqrt (m₀ : ℝ)) : ℂ) :=
          (GaussGen.S_value m₀).2.2.1 hm4
        have hunit_s : IsUnit ((s : ℕ) : ZMod 4) :=
          (ZMod.isUnit_iff_coprime s 4).2 (hcop.coprime_dvd_right hd4)
        have hone_s : (1 : MulChar (ZMod 4) ℤ) ((s : ℕ) : ZMod 4) = 1 :=
          MulChar.one_apply hunit_s
        have hJcr : ((J((s : ℤ) * ((2 ^ (2 * f) : ℕ) : ℤ) | m₀) : ℤ) : ℝ)
            = ((J((s : ℤ) | m₀) : ℤ) : ℝ) := by exact_mod_cast hJc s
        have hχre : (χ (s : ZMod m)).re = ((J((s : ℤ) | m₀) : ℤ) : ℝ) := by
          rw [hχ_def, combChar_natCast m 4 m₀ hd4 hm₀dvd (1 : MulChar (ZMod 4) ℤ) hsp4 s,
            hjChar_val s, hone_s]
          simp [Complex.mul_re]
        rw [hSfact s hcop, Sz_pow_even ((s : ℤ) * (m₀ : ℤ)) ha f hf1, hSval1, hχre, hRm]
        simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.one_re,
          Complex.one_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.intCast_re, Complex.intCast_im]
        linear_combination (Real.sqrt ((2 : ℝ) ^ (2 * f)) * Real.sqrt (m₀ : ℝ)) * hJcr
  · -- e = 2f+1 (odd)
    subst hf
    have hf1 : 1 ≤ f := by omega
    have hd8 : (8 : ℕ) ∣ m := by
      have h3 : (2 : ℕ) ^ 3 ∣ 2 ^ (2 * f + 1) := pow_dvd_pow 2 (by omega)
      exact dvd_trans (by norm_num) (dvd_trans h3 h2edvd)
    have hcn8 : (ZMod.castHom hd8 (ZMod 8)) (-1) = -1 := by rw [map_neg, map_one]
    have hgcd2f : ((2 ^ f : ℕ) : ℤ).gcd ((m₀ : ℕ) : ℤ) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp
        (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_two_left.2 hm0odd').pow_left f))
    have hJ2 : (J(((2 ^ (2 * f + 1) : ℕ) : ℤ) | m₀) : ℤ) = ZMod.χ₈ ((m₀ : ℤ) : ZMod 8) := by
      rw [show ((2 ^ (2 * f + 1) : ℕ) : ℤ) = 2 * (((2 ^ f : ℕ) : ℤ)) ^ 2 by push_cast; ring,
        jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.sq_one hgcd2f, mul_one,
        jacobiSym.at_two hm0odd', Int.cast_natCast]
    have hJc : ∀ s : ℕ, (J((s : ℤ) * ((2 ^ (2 * f + 1) : ℕ) : ℤ) | m₀) : ℤ)
        = J((s : ℤ) | m₀) * ZMod.χ₈ ((m₀ : ℤ) : ZMod 8) := by
      intro s; rw [jacobiSym.mul_left, hJ2]
    rcases (show m₀ % 4 = 1 ∨ m₀ % 4 = 3 by omega) with hm4 | hm4
    · -- sub-branch A: m₀ % 4 = 1, D = χ₈'
      set hsp8 := hsplit_gen 8 hd8 (by norm_num) (by norm_num) with hsp8_def
      set χ := combChar m 8 m₀ hd8 hm₀dvd ZMod.χ₈' hsp8 with hχ_def
      have hneg : χ (-1) = -1 := by
        rw [hχ_def, combChar_apply, hcn8, hcnm, jChar_neg_one m₀ hm0odd,
          show ZMod.χ₈' (-1 : ZMod 8) = -1 from by decide, ZMod.χ₄_nat_one_mod_four hm4]
        norm_num
      refine ⟨χ, ?_, ?_, hneg, fun a => combChar_im m 8 m₀ hd8 hm₀dvd _ hsp8 a, ?_⟩
      · rw [hχ_def]
        exact (combChar_isquad m 8 m₀ hd8 hm₀dvd ZMod.χ₈' ZMod.isQuadratic_χ₈' hsp8).sq_eq_one
      · intro hc
        rw [hc, MulChar.one_apply (isUnit_one.neg)] at hneg; norm_num at hneg
      · intro s hsm hcop
        have hsodd := hs_odd s hcop
        have ha : ((s : ℤ) * (m₀ : ℤ)) % 2 = 1 :=
          Int.odd_iff.1 ((Int.odd_iff.2 (by exact_mod_cast hsodd)).mul
            (Int.odd_iff.2 (by exact_mod_cast hm0odd)))
        have hSval1 : S 1 m₀ = ((Real.sqrt (m₀ : ℝ)) : ℂ) := (GaussGen.S_value m₀).1 hm4
        have hmm : ZMod.χ₈ ((m₀ : ℤ) : ZMod 8) * ZMod.χ₈' ((m₀ : ℤ) : ZMod 8) = 1 := by
          rw [chi8_mul_chi8'_odd (m₀ : ℤ) (by exact_mod_cast hm0odd),
            ZMod.χ₄_int_one_mod_four (by exact_mod_cast hm4)]
        have hId : (J((s : ℤ) * ((2 ^ (2 * f + 1) : ℕ) : ℤ) | m₀) : ℤ)
            * ZMod.χ₈' (((s : ℤ) * (m₀ : ℤ)) : ZMod 8)
            = ZMod.χ₈' (s : ZMod 8) * J((s : ℤ) | m₀) := by
          rw [hJc s, show (((s : ℤ) * (m₀ : ℤ)) : ZMod 8)
              = ((s : ℤ) : ZMod 8) * ((m₀ : ℤ) : ZMod 8) by push_cast; ring, map_mul,
            show (J((s : ℤ) | m₀) * ZMod.χ₈ ((m₀ : ℤ) : ZMod 8))
                * (ZMod.χ₈' ((s : ℤ) : ZMod 8) * ZMod.χ₈' ((m₀ : ℤ) : ZMod 8))
              = (ZMod.χ₈ ((m₀ : ℤ) : ZMod 8) * ZMod.χ₈' ((m₀ : ℤ) : ZMod 8))
                * (ZMod.χ₈' ((s : ℤ) : ZMod 8) * J((s : ℤ) | m₀)) by ring,
            hmm, one_mul, Int.cast_natCast]
        have hIdRr : ((J((s : ℤ) * ((2 ^ (2 * f + 1) : ℕ) : ℤ) | m₀) : ℤ) : ℝ)
            * ((ZMod.χ₈' (((s : ℤ) * (m₀ : ℤ)) : ZMod 8) : ℤ) : ℝ)
            = ((ZMod.χ₈' (s : ZMod 8) : ℤ) : ℝ) * ((J((s : ℤ) | m₀) : ℤ) : ℝ) := by
          exact_mod_cast hId
        have hχre : (χ (s : ZMod m)).re
            = ((ZMod.χ₈' (s : ZMod 8) : ℤ) : ℝ) * ((J((s : ℤ) | m₀) : ℤ) : ℝ) := by
          rw [hχ_def, combChar_natCast m 8 m₀ hd8 hm₀dvd ZMod.χ₈' hsp8 s, hjChar_val s,
            re_intCast_mul]
        rw [hSfact s hcop, Sz_pow_odd ((s : ℤ) * (m₀ : ℤ)) ha f hf1, hSval1, hχre, hRm]
        simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.one_re,
          Complex.one_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.intCast_re, Complex.intCast_im]
        rw [Int.cast_mul]
        linear_combination (Real.sqrt ((2 : ℝ) ^ (2 * f + 1)) * Real.sqrt (m₀ : ℝ)) * hIdRr
    · -- sub-branch B: m₀ % 4 = 3, D = χ₈
      set hsp8 := hsplit_gen 8 hd8 (by norm_num) (by norm_num) with hsp8_def
      set χ := combChar m 8 m₀ hd8 hm₀dvd ZMod.χ₈ hsp8 with hχ_def
      have hneg : χ (-1) = -1 := by
        rw [hχ_def, combChar_apply, hcn8, hcnm, jChar_neg_one m₀ hm0odd,
          show ZMod.χ₈ (-1 : ZMod 8) = 1 from by decide, ZMod.χ₄_nat_three_mod_four hm4]
        norm_num
      refine ⟨χ, ?_, ?_, hneg, fun a => combChar_im m 8 m₀ hd8 hm₀dvd _ hsp8 a, ?_⟩
      · rw [hχ_def]
        exact (combChar_isquad m 8 m₀ hd8 hm₀dvd ZMod.χ₈ ZMod.isQuadratic_χ₈ hsp8).sq_eq_one
      · intro hc
        rw [hc, MulChar.one_apply (isUnit_one.neg)] at hneg; norm_num at hneg
      · intro s hsm hcop
        have hsodd := hs_odd s hcop
        have ha : ((s : ℤ) * (m₀ : ℤ)) % 2 = 1 :=
          Int.odd_iff.1 ((Int.odd_iff.2 (by exact_mod_cast hsodd)).mul
            (Int.odd_iff.2 (by exact_mod_cast hm0odd)))
        have hSval1 : S 1 m₀ = Complex.I * ((Real.sqrt (m₀ : ℝ)) : ℂ) :=
          (GaussGen.S_value m₀).2.2.1 hm4
        have hmm : ZMod.χ₈ ((m₀ : ℤ) : ZMod 8) ^ 2 = 1 :=
          chi8_sq_odd (m₀ : ℤ) (by exact_mod_cast hm0odd)
        have hId : (J((s : ℤ) * ((2 ^ (2 * f + 1) : ℕ) : ℤ) | m₀) : ℤ)
            * ZMod.χ₈ (((s : ℤ) * (m₀ : ℤ)) : ZMod 8)
            = ZMod.χ₈ (s : ZMod 8) * J((s : ℤ) | m₀) := by
          rw [hJc s, show (((s : ℤ) * (m₀ : ℤ)) : ZMod 8)
              = ((s : ℤ) : ZMod 8) * ((m₀ : ℤ) : ZMod 8) by push_cast; ring, map_mul,
            show (J((s : ℤ) | m₀) * ZMod.χ₈ ((m₀ : ℤ) : ZMod 8))
                * (ZMod.χ₈ ((s : ℤ) : ZMod 8) * ZMod.χ₈ ((m₀ : ℤ) : ZMod 8))
              = ZMod.χ₈ ((m₀ : ℤ) : ZMod 8) ^ 2
                * (ZMod.χ₈ ((s : ℤ) : ZMod 8) * J((s : ℤ) | m₀)) by ring,
            hmm, one_mul, Int.cast_natCast]
        have hIdRr : ((J((s : ℤ) * ((2 ^ (2 * f + 1) : ℕ) : ℤ) | m₀) : ℤ) : ℝ)
            * ((ZMod.χ₈ (((s : ℤ) * (m₀ : ℤ)) : ZMod 8) : ℤ) : ℝ)
            = ((ZMod.χ₈ (s : ZMod 8) : ℤ) : ℝ) * ((J((s : ℤ) | m₀) : ℤ) : ℝ) := by
          exact_mod_cast hId
        have hχre : (χ (s : ZMod m)).re
            = ((ZMod.χ₈ (s : ZMod 8) : ℤ) : ℝ) * ((J((s : ℤ) | m₀) : ℤ) : ℝ) := by
          rw [hχ_def, combChar_natCast m 8 m₀ hd8 hm₀dvd ZMod.χ₈ hsp8 s, hjChar_val s,
            re_intCast_mul]
        rw [hSfact s hcop, Sz_pow_odd ((s : ℤ) * (m₀ : ℤ)) ha f hf1, hSval1, hχre, hRm]
        simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.one_re,
          Complex.one_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.intCast_re, Complex.intCast_im]
        rw [Int.cast_mul]
        linear_combination (Real.sqrt ((2 : ℝ) ^ (2 * f + 1)) * Real.sqrt (m₀ : ℝ)) * hIdRr

/-- For `m ≡ 2 (mod 4)`, the Gauss sum vanishes on units, so its imaginary part is `0`. -/
private lemma imS_eq_zero_two (m : ℕ) [NeZero m] (h2 : m % 4 = 2) (s : ℕ)
    (hs : Nat.Coprime s m) : (S s m).im = 0 := by
  obtain ⟨n, hn⟩ : ∃ n, m = 2 * n := ⟨m / 2, by omega⟩
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso; rw [h, Nat.mul_zero] at hn; exact (NeZero.ne m) hn
    · exact h
  have hsodd : Odd s := by
    rcases Nat.even_or_odd s with he | ho
    · exfalso
      have h2s : (2 : ℕ) ∣ s := he.two_dvd
      have h2m : (2 : ℕ) ∣ m := ⟨n, hn⟩
      have hd : (2 : ℕ) ∣ Nat.gcd s m := Nat.dvd_gcd h2s h2m
      rw [hs] at hd; exact absurd hd (by norm_num)
    · exact ho
  have hnodd : Odd n := Nat.odd_iff.2 (by omega)
  set f : ℕ → ℂ := fun k => Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * (k : ℂ) ^ 2 / (m : ℂ))
    with hf
  have hSsum : S s m = ∑ k ∈ Finset.range m, f k := rfl
  have hmc : (m : ℂ) = 2 * (n : ℂ) := by rw [hn]; push_cast; ring
  have hpair : ∀ i : ℕ, f i + f (i + n) = 0 := by
    intro i
    have hexpX : Complex.exp ((↑(s * n) : ℂ) * (Real.pi * Complex.I)
        + (↑(s * i) : ℂ) * (2 * Real.pi * Complex.I)) = -1 := by
      rw [Complex.exp_add, Complex.exp_nat_mul, Complex.exp_nat_mul, Complex.exp_pi_mul_I,
        Complex.exp_two_pi_mul_I, one_pow, mul_one, Odd.neg_one_pow (hsodd.mul hnodd)]
    have hfin : f (i + n)
        = f i * Complex.exp ((↑(s * n) : ℂ) * (Real.pi * Complex.I)
          + (↑(s * i) : ℂ) * (2 * Real.pi * Complex.I)) := by
      simp only [hf]
      rw [← Complex.exp_add]
      congr 1
      rw [hmc]
      have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
      field_simp
      push_cast
      ring
    rw [hfin, hexpX]; ring
  have hzero : S s m = 0 := by
    rw [hSsum, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive f (Nat.zero_le n) (by omega : n ≤ m)]
    have hsecond : ∑ i ∈ Finset.Ico n m, f i = ∑ i ∈ Finset.range n, f (n + i) := by
      rw [Finset.sum_Ico_eq_sum_range]
      rw [show m - n = n by omega]
    rw [Nat.Ico_zero_eq_range, hsecond, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    rw [add_comm n i]; exact hpair i
  rw [hzero]; simp

/-- For `m ≡ 1 (mod 4)`, the Gauss sum is real, so its imaginary part vanishes. -/
private lemma imS_eq_zero_one (m : ℕ) [NeZero m] (h1 : m % 4 = 1) (s : ℕ)
    (hs : Nat.Coprime s m) : (S s m).im = 0 := by
  have hoddm : m % 2 = 1 := by omega
  rw [odd_twist m hoddm s hs]
  have hS1 : S 1 m = ((Real.sqrt m : ℝ) : ℂ) := (GaussGen.S_value m).1 h1
  rw [hS1]
  simp [Complex.mul_im]

/-- For `m ≡ 3 (mod 4)` the twist relation gives the imaginary part in terms of `jChar`. -/
private lemma htwist_three (m : ℕ) [NeZero m] (h3 : m % 4 = 3) (s : ℕ) (hsm : s < m)
    (hs : Nat.Coprime s m) :
    (S s m).im = Real.sqrt m * (jChar m (s : ZMod m)).re := by
  have hoddm : m % 2 = 1 := by omega
  rw [odd_twist m hoddm s hs]
  have hS1 : S 1 m = Complex.I * ((Real.sqrt m : ℝ) : ℂ) := (GaussGen.S_value m).2.2.1 h3
  rw [hS1, jChar_natCast_apply m s hsm]
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.intCast_re,
    Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Positivity of the per-divisor sum.** -/
theorem P_nonneg (m : ℕ) (hm : 1 < m) : 0 ≤ P m := by
  haveI : NeZero m := ⟨by omega⟩
  rcases (by omega : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3) with h0 | h1 | h2 | h3
  · -- 4 ∣ m
    obtain ⟨χ, hsq, hne, hodd, hreal, htw⟩ := exists_even_char m h0 hm
    exact P_nonneg_of_char m hm χ hsq hne hodd hreal htw
  · -- m ≡ 1 (mod 4): P m = 0
    have hP0 : P m = 0 := by
      rw [P]
      apply Finset.sum_eq_zero
      intro s hs
      rw [Finset.mem_filter, Finset.mem_Ico] at hs
      obtain ⟨⟨_, _⟩, hcop⟩ := hs
      rw [imS_eq_zero_one m h1 s hcop]; ring
    exact hP0.ge
  · -- m ≡ 2 (mod 4): P m = 0
    have hP0 : P m = 0 := by
      rw [P]
      apply Finset.sum_eq_zero
      intro s hs
      rw [Finset.mem_filter, Finset.mem_Ico] at hs
      obtain ⟨⟨_, _⟩, hcop⟩ := hs
      rw [imS_eq_zero_two m h2 s hcop]; ring
    exact hP0.ge
  · -- m ≡ 3 (mod 4)
    have hoddchar : jChar m (-1) = -1 := by
      rw [jChar_neg_one m (by omega : m % 2 = 1), ZMod.χ₄_nat_three_mod_four h3]; simp
    have hne : jChar m ≠ 1 := by
      intro h
      rw [h, MulChar.one_apply (isUnit_one.neg)] at hoddchar
      norm_num at hoddchar
    exact P_nonneg_of_char m hm (jChar m) (jChar_sq m) hne hoddchar (jChar_im m)
      (fun s hsm hcop => htwist_three m h3 s hsm hcop)

end

end

/- ================= inlined from Final.lean ================= -/
section

open Finset

noncomputable section

/-- `k = 0` gives `0² % n = 0`, so `Zc n ≥ 1` for `n ≥ 1`. -/
private lemma one_le_Zc (n : ℕ) (hn : 1 ≤ n) : 1 ≤ Zc n := by
  unfold Zc
  refine Finset.card_pos.mpr ⟨0, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, by simp⟩

/-- `Zc n ≤ n`. -/
private lemma Zc_le (n : ℕ) : Zc n ≤ n := by
  unfold Zc
  calc ((Finset.range n).filter (fun k => k ^ 2 % n = 0)).card
      ≤ (Finset.range n).card := Finset.card_filter_le _ _
    _ = n := Finset.card_range n

/-- The deep inequality `2 * A048153 n ≤ n * (n - Zc n)`, from `master` and `P_nonneg`. -/
private lemma deep (n : ℕ) (hn : 1 ≤ n) : 2 * A048153 n ≤ n * (n - Zc n) := by
  have hmaster := master n hn
  have hsum_nonneg : 0 ≤
      ∑ m ∈ n.divisors.filter (fun m => 1 < m), ((n / m : ℕ) : ℝ) * P m := by
    apply Finset.sum_nonneg
    intro m hm
    rw [Finset.mem_filter] at hm
    have := P_nonneg m hm.2
    positivity
  -- real inequality
  have hZ : Zc n ≤ n := Zc_le n
  have hreal : 2 * (A048153 n : ℝ) ≤ (n : ℝ) * ((n : ℝ) - (Zc n : ℝ)) := by
    nlinarith [hmaster, hsum_nonneg]
  -- rewrite RHS as a cast of a ℕ product
  have hcast : (n : ℝ) * ((n : ℝ) - (Zc n : ℝ)) = ((n * (n - Zc n) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hZ]
    ring
  rw [hcast] at hreal
  have : ((2 * A048153 n : ℕ) : ℝ) ≤ ((n * (n - Zc n) : ℕ) : ℝ) := by push_cast; push_cast at hreal; linarith
  exact_mod_cast this

/-- **The conjecture (OEIS A048153).** -/
theorem oeis_48153_conjecture_0 (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  have hd := deep n h
  have hz1 := one_le_Zc n h
  have hzn := Zc_le n
  have hnn : n * (n - Zc n) ≤ n * (n - 1) := Nat.mul_le_mul_left _ (by omega)
  have e : n * (n - 1) + n = n ^ 2 := by
    have h1 : n - 1 + 1 = n := by omega
    calc n * (n - 1) + n = n * (n - 1) + n * 1 := by ring
      _ = n * (n - 1 + 1) := by rw [← Nat.mul_add]
      _ = n * n := by rw [h1]
      _ = n ^ 2 := by ring
  omega
end
end
