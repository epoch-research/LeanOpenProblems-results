import FormalConjectures.Util.ProblemImports

open Matrix Finset BigOperators

namespace Crux

noncomputable section

variable {m : ℕ}

/-- Stub for the DetF result (to be replaced by the real `Eval.detF`). -/
theorem detF_stub (m : ℕ) (hmodd : Odd m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    (Matrix.vandermonde (fun a : Fin (2 * m) => ζ ^ (a : ℕ))).det
      = (-1 : ℂ) ^ ((m + 1) / 2) * (2 * m : ℂ) ^ m := sorry

/-- Index type: `Fin m × Fin 2`, identifying with `ZMod (2m)` via `(k,c) ↦ k + m*c`. -/
abbrev Ix (m : ℕ) := Fin m × Fin 2

/-- The exponent of an index. -/
def ex (x : Ix m) : ℕ := (x.1 : ℕ) + m * (x.2 : ℕ)

/-- The DFT matrix `W (x) (y) = ζ ^ (ex x * ex y)`. -/
def W (ζ : ℂ) : Matrix (Ix m) (Ix m) ℂ := fun x y => ζ ^ (ex x * ex y)

/-- `ex` as a bijection `Ix m ≃ Fin (2*m)`. -/
def exEquiv (m : ℕ) : Ix m ≃ Fin (2 * m) where
  toFun x := ⟨ex x, by
    rcases x with ⟨k, c⟩
    simp only [ex]
    have hk := k.isLt
    have hc := c.isLt
    have : m * (c : ℕ) ≤ m * 1 := Nat.mul_le_mul_left _ (by omega)
    omega⟩
  invFun y := (⟨(y : ℕ) % m, by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; exact absurd y.isLt (by simp)
      · exact Nat.mod_lt _ h⟩, ⟨(y : ℕ) / m, by
      have hy := y.isLt
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at hy
      · rw [Nat.div_lt_iff_lt_mul h]; omega⟩)
  left_inv := by
    rintro ⟨k, c⟩
    have hk := k.isLt
    have hmpos : 0 < m := by omega
    ext
    · show ((ex (k, c)) % m) = (k : ℕ)
      simp only [ex]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
    · show ((ex (k, c)) / m) = (c : ℕ)
      simp only [ex]
      rw [Nat.add_mul_div_left _ _ hmpos, Nat.div_eq_of_lt hk, zero_add]
  right_inv := by
    intro y
    have hy := y.isLt
    have hmpos : 0 < m := by omega
    apply Fin.ext
    show ex ((⟨(y:ℕ) % m, _⟩ : Fin m), (⟨(y:ℕ) / m, _⟩ : Fin 2)) = (y : ℕ)
    simp only [ex]
    exact Nat.mod_add_div _ _

/-- `W` is the reindexed Vandermonde DFT matrix. -/
theorem W_eq_submatrix (ζ : ℂ) :
    (W ζ : Matrix (Ix m) (Ix m) ℂ)
      = (Matrix.vandermonde (fun a : Fin (2 * m) => ζ ^ (a : ℕ))).submatrix (exEquiv m) (exEquiv m) := by
  ext x y
  simp only [W, Matrix.submatrix_apply, Matrix.vandermonde_apply]
  rw [← pow_mul]
  rfl

/-- Determinant of `W` via `detF`. -/
theorem det_W (hmodd : Odd m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    (W ζ : Matrix (Ix m) (Ix m) ℂ).det = (-1 : ℂ) ^ ((m + 1) / 2) * (2 * m : ℂ) ^ m := by
  rw [W_eq_submatrix, Matrix.det_submatrix_equiv_self, detF_stub m hmodd ζ hζ]

/-- The conjugate DFT matrix using `ζ⁻¹`. -/
def Wc (ζ : ℂ) : Matrix (Ix m) (Ix m) ℂ := fun x y => (ζ⁻¹) ^ (ex x * ex y)

/-- Orthogonality: `W * Wc = (2m) • 1`. -/
theorem W_mul_Wc (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    (W ζ : Matrix (Ix m) (Ix m) ℂ) * Wc ζ = (2 * m : ℂ) • (1 : Matrix (Ix m) (Ix m) ℂ) := by
  ext x y
  have hmpos : 0 < m := x.1.pos
  have hζne : ζ ≠ 0 := by
    intro h; subst h
    have := hζ.pow_eq_one
    rw [zero_pow (by omega : 2 * m ≠ 0)] at this
    exact zero_ne_one this
  rw [Matrix.mul_apply]
  -- term z = r ^ (ex z) with r = ζ^(ex x) * (ζ^(ex y))⁻¹
  set r : ℂ := ζ ^ (ex x) * (ζ ^ (ex y))⁻¹ with hr
  have hterm : ∀ z : Ix m, (W ζ x z) * (Wc ζ z y) = r ^ (ex z) := by
    intro z
    simp only [W, Wc, hr]
    rw [mul_pow, inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (ex z) (ex y)]
  rw [Finset.sum_congr rfl (fun z _ => hterm z)]
  -- reindex sum over Ix to Fin (2m)
  have hreindex : (∑ z : Ix m, r ^ (ex z)) = ∑ w : Fin (2 * m), r ^ (w : ℕ) := by
    rw [← Equiv.sum_comp (exEquiv m) (fun w : Fin (2 * m) => r ^ (w : ℕ))]
    rfl
  rw [hreindex]
  -- evaluate the geometric sum
  have hpow2m : ∀ e : ℕ, (ζ ^ e) ^ (2 * m) = 1 := by
    intro e
    rw [← pow_mul, mul_comm e (2 * m), pow_mul, hζ.pow_eq_one, one_pow]
  have hr2m : r ^ (2 * m) = 1 := by
    rw [hr, mul_pow, inv_pow, hpow2m, hpow2m, inv_one, mul_one]
  rw [Matrix.smul_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    have hr1 : r = 1 := by rw [hr]; rw [mul_inv_cancel₀ (pow_ne_zero _ hζne)]
    simp only [hr1, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, if_true, smul_eq_mul]
    push_cast; ring
  · -- r ≠ 1, geometric sum = 0
    have hr1 : r ≠ 1 := by
      rw [hr]
      intro h
      rw [mul_inv_eq_one₀ (pow_ne_zero _ hζne)] at h
      apply hxy
      -- ζ^(ex x) = ζ^(ex y), ex < 2m, primitive ⟹ ex x = ex y ⟹ x = y
      have hexeq : ex x = ex y := by
        have hxlt : ex x < 2 * m := (exEquiv m x).isLt
        have hylt : ex y < 2 * m := (exEquiv m y).isLt
        have := hζ.pow_inj (by exact hxlt) (by exact hylt) h
        exact this
      exact (exEquiv m).injective (Fin.ext hexeq)
    have hsum : (∑ w : Fin (2 * m), r ^ (w : ℕ)) = 0 := by
      have := geom_sum_eq hr1 (2 * m)
      rw [Fin.sum_univ_eq_sum_range (fun i => r ^ i) (2 * m), this, hr2m]
      simp
    rw [hsum]
    simp only [if_neg hxy, smul_eq_mul, mul_zero]

/-- The "other element" of `Fin 2`. -/
def flip2 (c : Fin 2) : Fin 2 := c + 1

@[simp] theorem flip2_flip2 (c : Fin 2) : flip2 (flip2 c) = c := by
  fin_cases c <;> rfl

theorem flip2_ne (c : Fin 2) : flip2 c ≠ c := by fin_cases c <;> decide

theorem eq_flip2_of_ne {c d : Fin 2} (h : c ≠ d) : c = flip2 d := by
  fin_cases c <;> fin_cases d <;> simp_all <;> decide

/-- Reindexing `Ix m` by a transversal selector `a`: `(k,c) ↦ inl k` if `c = a k`, else `inr k`. -/
def eR (a : Fin m → Fin 2) : Ix m ≃ (Fin m ⊕ Fin m) where
  toFun x := if x.2 = a x.1 then Sum.inl x.1 else Sum.inr x.1
  invFun s := s.elim (fun k => (k, a k)) (fun k => (k, flip2 (a k)))
  left_inv := by
    rintro ⟨k, c⟩
    by_cases h : c = a k
    · simp [h]
    · simp only [h, if_false, Sum.elim_inr]
      rw [eq_flip2_of_ne h]
  right_inv := by
    rintro (k | k)
    · simp
    · simp only [Sum.elim_inr]
      rw [if_neg (flip2_ne (a k))]

@[simp] theorem eR_symm_inl (a : Fin m → Fin 2) (k : Fin m) :
    (eR a).symm (Sum.inl k) = (k, a k) := rfl

@[simp] theorem eR_symm_inr (a : Fin m → Fin 2) (k : Fin m) :
    (eR a).symm (Sum.inr k) = (k, flip2 (a k)) := rfl

@[simp] theorem eR_apply (a : Fin m → Fin 2) (x : Ix m) :
    (eR a) x = if x.2 = a x.1 then Sum.inl x.1 else Sum.inr x.1 := rfl

/-- Standard equiv `(Fin m ⊕ Fin m) ≃ (Fin m × Fin 2)`. -/
def esum (m : ℕ) : (Fin m ⊕ Fin m) ≃ (Fin m × Fin 2) where
  toFun s := s.elim (fun k => (k, 0)) (fun k => (k, 1))
  invFun x := if x.2 = 0 then Sum.inl x.1 else Sum.inr x.1
  left_inv := by rintro (k | k) <;> simp
  right_inv := by
    rintro ⟨k, c⟩; fin_cases c <;> simp

@[simp] theorem esum_inl (k : Fin m) : esum m (Sum.inl k) = (k, 0) := rfl
@[simp] theorem esum_inr (k : Fin m) : esum m (Sum.inr k) = (k, 1) := rfl

/-- The reindex permutation `τ = (eR b).symm.trans (eR a)` on `Fin m ⊕ Fin m`. -/
def tauPerm (a b : Fin m → Fin 2) : Equiv.Perm (Fin m ⊕ Fin m) :=
  (eR b).symm.trans (eR a)

/-- The fiberwise permutation on `Fin 2` for each `k`. -/
def sigPerm (a b : Fin m → Fin 2) (k : Fin m) : Equiv.Perm (Fin 2) :=
  if a k = b k then 1 else Equiv.swap 0 1

theorem tau_conj (a b : Fin m → Fin 2) :
    ∀ s : Fin m ⊕ Fin m,
      esum m (tauPerm a b s) = (Equiv.prodCongrRight (sigPerm a b)) (esum m s) := by
  rintro (k | k)
  · show esum m ((eR a) ((eR b).symm (Sum.inl k)))
        = (Equiv.prodCongrRight (sigPerm a b)) (esum m (Sum.inl k))
    rw [eR_symm_inl, eR_apply, esum_inl, Equiv.prodCongrRight_apply]
    by_cases h : a k = b k
    · rw [if_pos h.symm, esum_inl, sigPerm, if_pos h]
      simp
    · rw [if_neg (fun hh => h hh.symm), esum_inr, sigPerm, if_neg h, Equiv.swap_apply_left]
  · show esum m ((eR a) ((eR b).symm (Sum.inr k)))
        = (Equiv.prodCongrRight (sigPerm a b)) (esum m (Sum.inr k))
    rw [eR_symm_inr, eR_apply, esum_inr, Equiv.prodCongrRight_apply]
    by_cases h : a k = b k
    · rw [if_neg (by rw [h]; exact flip2_ne (b k)), esum_inr, sigPerm, if_pos h]
      simp
    · rw [if_pos (eq_flip2_of_ne h).symm, esum_inl, sigPerm, if_neg h,
        Equiv.swap_apply_right]

theorem sign_tau (a b : Fin m → Fin 2) :
    Equiv.Perm.sign (tauPerm a b) = ∏ k, (if a k = b k then (1 : ℤˣ) else -1) := by
  rw [Equiv.Perm.sign_eq_sign_of_equiv (tauPerm a b) (Equiv.prodCongrRight (sigPerm a b)) (esum m)
        (tau_conj a b),
    Equiv.Perm.sign_prodCongrRight]
  apply Finset.prod_congr rfl
  intro k _
  simp only [sigPerm]
  by_cases h : a k = b k
  · simp [h]
  · simp [h, Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]

/-- The `m × m` minor of `W` selecting rows `(k, a k)` and columns `(j, b j)`. -/
def D (a b : Fin m → Fin 2) (ζ : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun k j => ζ ^ (ex (k, a k) * ex (j, b j))

theorem eRb_eq (a b : Fin m → Fin 2) (s : Fin m ⊕ Fin m) :
    (eR b).symm s = (eR a).symm (tauPerm a b s) := by
  show (eR b).symm s = (eR a).symm ((eR a) ((eR b).symm s))
  rw [Equiv.symm_apply_apply]

/-- The reindexed full matrix `M = W.submatrix (eR a).symm (eR b).symm` has
determinant `sign(tau) * det W`. -/
theorem det_Msub (a b : Fin m → Fin 2) (ζ : ℂ) :
    ((W ζ).submatrix (eR a).symm (eR b).symm).det
      = ((Equiv.Perm.sign (tauPerm a b) : ℂ)) * (W ζ : Matrix (Ix m) (Ix m) ℂ).det := by
  have h1 : (W ζ).submatrix (eR a).symm (eR b).symm
      = ((W ζ).submatrix (eR a).symm (eR a).symm).submatrix id (tauPerm a b) := by
    rw [Matrix.submatrix_submatrix]
    congr 1
    funext s
    exact (eRb_eq a b s)
  rw [h1, Matrix.det_permute', Matrix.det_submatrix_equiv_self]

/-- `M = W.submatrix (eR a).symm (eR b).symm`. -/
def Msub (a b : Fin m → Fin 2) (ζ : ℂ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
  (W ζ).submatrix (eR a).symm (eR b).symm

/-- `N = Wc.submatrix (eR b).symm (eR a).symm`. -/
def Nsub (a b : Fin m → Fin 2) (ζ : ℂ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
  (Wc ζ).submatrix (eR b).symm (eR a).symm

theorem Msub_mul_Nsub (a b : Fin m → Fin 2) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    Msub a b ζ * Nsub a b ζ = (2 * m : ℂ) • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ) := by
  rw [Msub, Nsub, Matrix.submatrix_mul_equiv (W ζ) (Wc ζ) (eR a).symm (eR b).symm (eR a).symm,
    W_mul_Wc ζ hζ]
  rw [show ((2 * m : ℂ) • (1 : Matrix (Ix m) (Ix m) ℂ)).submatrix (eR a).symm (eR a).symm
        = (2 * m : ℂ) • ((1 : Matrix (Ix m) (Ix m) ℂ).submatrix (eR a).symm (eR a).symm) from
      ext fun i => congrFun rfl, Matrix.submatrix_one_equiv]

/-- Block decomposition of `Msub`. -/
theorem Msub_fromBlocks (a b : Fin m → Fin 2) (ζ : ℂ) :
    Msub a b ζ = fromBlocks (D a b ζ)
      (fun k j => ζ ^ (ex (k, a k) * ex (j, flip2 (b j))))
      (fun k j => ζ ^ (ex (k, flip2 (a k)) * ex (j, b j)))
      (fun k j => ζ ^ (ex (k, flip2 (a k)) * ex (j, flip2 (b j)))) := by
  ext s t
  rcases s with k | k <;> rcases t with j | j <;>
    simp [Msub, W, D, eR_symm_inl, eR_symm_inr]

/-- Block decomposition of `Nsub`. -/
theorem Nsub_fromBlocks (a b : Fin m → Fin 2) (ζ : ℂ) :
    Nsub a b ζ = fromBlocks
      (fun k j => (ζ⁻¹) ^ (ex (k, b k) * ex (j, a j)))
      (fun k j => (ζ⁻¹) ^ (ex (k, b k) * ex (j, flip2 (a j))))
      (fun k j => (ζ⁻¹) ^ (ex (k, flip2 (b k)) * ex (j, a j)))
      (fun k j => (ζ⁻¹) ^ (ex (k, flip2 (b k)) * ex (j, flip2 (a j)))) := by
  ext s t
  rcases s with k | k <;> rcases t with j | j <;>
    simp [Nsub, Wc, eR_symm_inl, eR_symm_inr]

theorem zeta_pow_m (ζ : ℂ) (hm : 0 < m) (hζ : IsPrimitiveRoot ζ (2 * m)) : ζ ^ m = -1 := by
  have h2 : (ζ ^ m) * (ζ ^ m) = 1 := by
    rw [← pow_add, show m + m = 2 * m by ring, hζ.pow_eq_one]
  rcases mul_self_eq_one_iff.1 h2 with h | h
  · exfalso
    rw [hζ.pow_eq_one_iff_dvd] at h
    have := Nat.le_of_dvd hm h
    omega
  · exact h

/-- Entry-level identity expressing the flipped exponent in terms of the original. -/
theorem entry_flip (ζ : ℂ) (hmodd : Odd m) (hζ : IsPrimitiveRoot ζ (2 * m)) (k j : Fin m)
    (c d : Fin 2) :
    ζ ^ (ex (k, flip2 c) * ex (j, flip2 d))
      = (-1) * ((-1) ^ (ex (k, c)) * (-1) ^ (ex (j, d))) * ζ ^ (ex (k, c) * ex (j, d)) := by
  have hm : 0 < m := k.pos
  have hzm : ζ ^ m = -1 := zeta_pow_m ζ hm hζ
  have hmm : (-1 : ℂ) ^ m = -1 := Odd.neg_one_pow hmodd
  have g1 : ζ ^ (((k : ℕ) + m) * ((j : ℕ) + m))
      = ζ ^ ((k : ℕ) * (j : ℕ)) * ((-1) ^ (k : ℕ) * (-1) ^ (j : ℕ) * (-1) ^ m) := by
    rw [show ((k : ℕ) + m) * ((j : ℕ) + m) = (k : ℕ) * (j : ℕ) + m * (k : ℕ) + (m * (j : ℕ) + m * m) by ring,
      pow_add, pow_add, pow_add]
    simp only [pow_mul, hzm]; ring
  have g2 : ζ ^ (((k : ℕ) + m) * (j : ℕ))
      = ζ ^ ((k : ℕ) * (j : ℕ)) * (-1) ^ (j : ℕ) := by
    rw [show ((k : ℕ) + m) * (j : ℕ) = (k : ℕ) * (j : ℕ) + m * (j : ℕ) by ring, pow_add]
    simp only [pow_mul, hzm]
  have g3 : ζ ^ ((k : ℕ) * ((j : ℕ) + m))
      = ζ ^ ((k : ℕ) * (j : ℕ)) * (-1) ^ (k : ℕ) := by
    rw [show (k : ℕ) * ((j : ℕ) + m) = (k : ℕ) * (j : ℕ) + m * (k : ℕ) by ring, pow_add]
    simp only [pow_mul, hzm]
  have hk2 : ((-1 : ℂ)) ^ ((k : ℕ) * 2) = 1 := by rw [mul_comm, pow_mul]; norm_num
  have hj2 : ((-1 : ℂ)) ^ ((j : ℕ) * 2) = 1 := by rw [mul_comm, pow_mul]; norm_num
  fin_cases c <;> fin_cases d <;>
    simp only [ex, flip2, Fin.val_add, Fin.val_zero, Fin.val_one, Fin.isValue, Nat.reduceMod,
      Nat.reduceAdd, mul_one, mul_zero, add_zero] <;>
    simp only [g1, g2, g3, pow_add, hmm] <;>
    ring_nf <;>
    simp only [hk2, hj2, mul_one, one_mul]

/-- The `(2,2)` block of `Nsub`, which is `conj` of a flipped `D`. -/
def Tpr (a b : Fin m → Fin 2) (ζ : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun k j => (ζ⁻¹) ^ (ex (k, flip2 (b k)) * ex (j, flip2 (a j)))

/-- Schur-complement scalar identity:
`det(Msub) * det(Tpr) = det(D a b) * (2m)^m`. -/
theorem schur_scalar (a b : Fin m → Fin 2) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m))
    (hP : IsUnit (D a b ζ).det) :
    (Msub a b ζ).det * (Tpr a b ζ).det = (D a b ζ).det * (2 * m : ℂ) ^ m := by
  -- name the blocks
  set P := D a b ζ with hPdef
  set Q : Matrix (Fin m) (Fin m) ℂ := (fun k j => ζ ^ (ex (k, a k) * ex (j, flip2 (b j)))) with hQ
  set R : Matrix (Fin m) (Fin m) ℂ := (fun k j => ζ ^ (ex (k, flip2 (a k)) * ex (j, b j))) with hR
  set T : Matrix (Fin m) (Fin m) ℂ := (fun k j => ζ ^ (ex (k, flip2 (a k)) * ex (j, flip2 (b j)))) with hT
  set P' : Matrix (Fin m) (Fin m) ℂ := (fun k j => (ζ⁻¹) ^ (ex (k, b k) * ex (j, a j))) with hP'
  set Q' : Matrix (Fin m) (Fin m) ℂ := (fun k j => (ζ⁻¹) ^ (ex (k, b k) * ex (j, flip2 (a j)))) with hQ'
  set R' : Matrix (Fin m) (Fin m) ℂ := (fun k j => (ζ⁻¹) ^ (ex (k, flip2 (b k)) * ex (j, a j))) with hR'
  -- the (2,2) block of N is Tpr
  have hTpr : (Tpr a b ζ) = (fun k j => (ζ⁻¹) ^ (ex (k, flip2 (b k)) * ex (j, flip2 (a j)))) := rfl
  -- block equations from Msub * Nsub = (2m)•1
  have hmul := Msub_mul_Nsub a b ζ hζ
  rw [Msub_fromBlocks, Nsub_fromBlocks, Matrix.fromBlocks_multiply,
    show ((2 * m : ℂ) • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ))
        = fromBlocks ((2 * m : ℂ) • 1) 0 0 ((2 * m : ℂ) • 1) by
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]; simp] at hmul
  rw [Matrix.fromBlocks_inj] at hmul
  obtain ⟨_, eq12, _, eq22⟩ := hmul
  -- eq12 : P * Q' + Q * (Tpr) = 0 ; eq22 : R * Q' + T * (Tpr) = (2m)•1
  change P * Q' + Q * (Tpr a b ζ) = 0 at eq12
  change R * Q' + T * (Tpr a b ζ) = (2 * m : ℂ) • 1 at eq22
  -- invertibility of P
  letI := Matrix.invertibleOfIsUnitDet P hP
  -- Schur complement
  have hdetM : (fromBlocks P Q R T).det = P.det * (T - R * (⅟ P) * Q).det :=
    Matrix.det_fromBlocks₁₁ P Q R T
  have hSchur : (T - R * (⅟ P) * Q) * (Tpr a b ζ) = (2 * m : ℂ) • 1 := by
    have hQmulT : Q * (Tpr a b ζ) = - (P * Q') := by
      have := eq12
      linear_combination (norm := module) this
    have key : R * (⅟ P) * Q * (Tpr a b ζ) = - (R * Q') := by
      rw [mul_assoc, mul_assoc, hQmulT, mul_neg, ← mul_assoc, invOf_mul_self,
        Matrix.one_mul, mul_neg]
    rw [sub_mul, key, sub_neg_eq_add, add_comm]
    exact eq22
  -- determinants
  have hMsub_det : (Msub a b ζ).det = (fromBlocks P Q R T).det := by rw [Msub_fromBlocks]
  rw [hMsub_det, hdetM]
  have hdetS : (T - R * (⅟ P) * Q).det * (Tpr a b ζ).det = (2 * m : ℂ) ^ m := by
    have := congrArg Matrix.det hSchur
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
    exact this
  rw [mul_assoc, hdetS]

/-- Determinant of the doubly-flipped `D` in terms of `D a b`. -/
theorem det_DF (a b : Fin m → Fin 2) (ζ : ℂ) (hmodd : Odd m) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    (D (fun k => flip2 (b k)) (fun j => flip2 (a j)) ζ).det
      = (-1) ^ (m + (∑ k, ex (k, b k)) + (∑ j, ex (j, a j))) * (D a b ζ).det := by
  have hDF : D (fun k => flip2 (b k)) (fun j => flip2 (a j)) ζ
      = (-1 : ℂ) • (Matrix.diagonal (fun k => (-1 : ℂ) ^ (ex (k, b k))) * D b a ζ
          * Matrix.diagonal (fun j => (-1 : ℂ) ^ (ex (j, a j)))) := by
    ext k j
    rw [Matrix.smul_apply,
      show (Matrix.diagonal (fun k => (-1 : ℂ) ^ (ex (k, b k))) * D b a ζ
            * Matrix.diagonal (fun j => (-1 : ℂ) ^ (ex (j, a j)))) k j
          = (-1 : ℂ) ^ (ex (k, b k)) * (D b a ζ) k j * (-1 : ℂ) ^ (ex (j, a j)) from by
        rw [Matrix.mul_diagonal, Matrix.diagonal_mul]]
    simp only [D, smul_eq_mul]
    rw [entry_flip ζ hmodd hζ k j (b k) (a j)]
    ring
  rw [hDF, Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_diagonal,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  have htr : (D b a ζ).det = (D a b ζ).det := by
    rw [show D b a ζ = (D a b ζ)ᵀ by ext k j; simp only [D, Matrix.transpose_apply, mul_comm],
      Matrix.det_transpose]
  rw [htr, pow_add, pow_add]
  ring

/-- Determinant of `Tpr` in terms of `conj (det (D a b))`. -/
theorem det_Tpr (a b : Fin m → Fin 2) (ζ : ℂ) (hmodd : Odd m) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    (Tpr a b ζ).det
      = (-1) ^ (m + (∑ k, ex (k, b k)) + (∑ j, ex (j, a j)))
          * (starRingEnd ℂ) ((D a b ζ).det) := by
  have hm : 0 < m := hmodd.pos
  have hconj : (starRingEnd ℂ) ζ = ζ⁻¹ := by
    have hn : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one (by omega)
    rw [← Complex.inv_eq_conj hn]
  -- Tpr is the entrywise conjugate of the flipped D
  have hmap : Tpr a b ζ = ((starRingEnd ℂ).mapMatrix (D (fun k => flip2 (b k)) (fun j => flip2 (a j)) ζ)) := by
    ext k j
    simp only [Tpr, RingHom.mapMatrix_apply, Matrix.map_apply, D]
    rw [map_pow, hconj]
  rw [hmap, ← RingHom.map_det, det_DF a b ζ hmodd hζ, map_mul]
  congr 1
  rw [map_pow]
  norm_num

/-- Sign cancellation: `sign(tau) * (-1)^(Sa+Sb) = 1`. -/
theorem sign_cancel (a b : Fin m → Fin 2) (hmodd : Odd m) :
    ((Equiv.Perm.sign (tauPerm a b) : ℂ)) * (-1) ^ ((∑ j, ex (j, a j)) + (∑ k, ex (k, b k))) = 1 := by
  have hmm : (-1 : ℂ) ^ m = -1 := Odd.neg_one_pow hmodd
  rw [show ((∑ j, ex (j, a j)) + (∑ k, ex (k, b k))) = ∑ k, (ex (k, a k) + ex (k, b k)) by
        rw [Finset.sum_add_distrib], ← Finset.prod_pow_eq_pow_sum, sign_tau]
  push_cast
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro k _
  have hsum : ex (k, a k) + ex (k, b k) = 2 * (k : ℕ) + m * ((a k).val + (b k).val) := by
    simp only [ex]; ring
  rw [hsum, pow_add, pow_mul, pow_mul, hmm]
  by_cases h : a k = b k
  · rw [if_pos h]
    have hv : (a k).val + (b k).val = 2 * (a k).val := by rw [h]; ring
    rw [hv, pow_mul]; norm_num
  · rw [if_neg h]
    have hv : (a k).val + (b k).val = 1 := by
      have hne : (a k).val ≠ (b k).val := fun hh => h (Fin.val_injective hh)
      have h1 := (a k).isLt
      have h2 := (b k).isLt
      omega
    rw [hv]; norm_num

/-- **The crux identity.** For any selectors `a b`, with `ζ` a primitive `2m`-th root of unity
and `m` odd, `conj (det (D a b)) = (-1)^((m-1)/2) * det (D a b)`. -/
theorem crux (a b : Fin m → Fin 2) (hmodd : Odd m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    (starRingEnd ℂ) ((D a b ζ).det) = (-1) ^ ((m - 1) / 2) * (D a b ζ).det := by
  by_cases hD : (D a b ζ).det = 0
  · rw [hD]; simp
  set Sa : ℕ := ∑ j, ex (j, a j) with hSa
  set Sb : ℕ := ∑ k, ex (k, b k) with hSb
  have hPunit : IsUnit (D a b ζ).det := isUnit_iff_ne_zero.2 hD
  have hsc := schur_scalar a b ζ hζ hPunit
  have hMsub : (Msub a b ζ).det = (Equiv.Perm.sign (tauPerm a b) : ℂ) * (W ζ).det :=
    det_Msub a b ζ
  rw [hMsub, det_W hmodd ζ hζ, det_Tpr a b ζ hmodd hζ] at hsc
  -- hsc : (s * ((-1)^((m+1)/2) * (2m)^m)) * ((-1)^(m+Sb+Sa) * conj detD) = detD * (2m)^m
  have hm : 0 < m := hmodd.pos
  have hpw : (2 * m : ℂ) ^ m ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 (by omega)))
  set s : ℂ := (Equiv.Perm.sign (tauPerm a b) : ℂ) with hs
  set detD : ℂ := (D a b ζ).det with hdetD
  -- cancel (2m)^m
  have hcancel : s * (-1) ^ ((m + 1) / 2) * ((-1) ^ (m + Sb + Sa) * (starRingEnd ℂ) detD) = detD := by
    have key : (2 * m : ℂ) ^ m * (s * (-1) ^ ((m + 1) / 2) * ((-1) ^ (m + Sb + Sa) * (starRingEnd ℂ) detD))
        = (2 * m : ℂ) ^ m * detD := by
      linear_combination hsc
    exact mul_left_cancel₀ hpw key
  -- compute the coefficient
  have hexp : (-1 : ℂ) ^ ((m + 1) / 2 + m) = (-1) ^ ((m - 1) / 2) := by
    obtain ⟨t, ht⟩ := hmodd
    subst ht
    rw [show (2 * t + 1 + 1) / 2 = t + 1 by omega, show (2 * t + 1 - 1) / 2 = t by omega,
      show (t + 1) + (2 * t + 1) = t + 2 * (t + 1) by ring, pow_add, pow_mul]
    norm_num
  have hsg := sign_cancel a b hmodd
  rw [← hSa, ← hSb, ← hs] at hsg
  have hcoef : s * (-1) ^ ((m + 1) / 2) * (-1) ^ (m + Sb + Sa) = (-1) ^ ((m - 1) / 2) := by
    rw [show m + Sb + Sa = (Sa + Sb) + m by ring, pow_add,
      show s * (-1) ^ ((m + 1) / 2) * ((-1) ^ (Sa + Sb) * (-1) ^ m)
        = (-1) ^ ((m + 1) / 2) * (-1) ^ m * (s * (-1) ^ (Sa + Sb)) by ring,
      hsg, mul_one, ← pow_add, hexp]
  rw [show s * (-1) ^ ((m + 1) / 2) * ((-1) ^ (m + Sb + Sa) * (starRingEnd ℂ) detD)
      = (s * (-1) ^ ((m + 1) / 2) * (-1) ^ (m + Sb + Sa)) * (starRingEnd ℂ) detD by ring,
    hcoef] at hcancel
  -- hcancel : (-1)^((m-1)/2) * conj detD = detD
  have hpm1 : ((-1 : ℂ) ^ ((m - 1) / 2)) * ((-1 : ℂ) ^ ((m - 1) / 2)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  calc (starRingEnd ℂ) detD
      = ((-1 : ℂ) ^ ((m - 1) / 2) * (-1) ^ ((m - 1) / 2)) * (starRingEnd ℂ) detD := by
          rw [hpm1, one_mul]
    _ = (-1) ^ ((m - 1) / 2) * ((-1) ^ ((m - 1) / 2) * (starRingEnd ℂ) detD) := by ring
    _ = (-1) ^ ((m - 1) / 2) * detD := by rw [hcancel]

end

end Crux
