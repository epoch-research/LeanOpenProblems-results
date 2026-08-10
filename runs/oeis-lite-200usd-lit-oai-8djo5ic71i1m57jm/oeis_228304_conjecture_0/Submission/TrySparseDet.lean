import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

-- paste sign lemmas
lemma sign_revPerm_units (n : ℕ) :
    Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) = (-1 : ℤˣ) ^ (n * (n - 1) / 2) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  simp only [Fin.revPerm_apply]
  have hinner : ∀ x : Fin n, (∏ y ∈ Iio x, if x < y then (1 : ℤˣ) else -1) = ∏ _y ∈ Iio x, (-1 : ℤˣ) := by
    intro x
    apply Finset.prod_congr rfl
    intro y hy
    rw [if_neg]
    exact not_lt_of_gt (by simpa using hy)
  simp [hinner, Fin.card_Iio, Finset.prod_const]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [show (∑ i : Fin n, (i : ℕ)) = ∑ i ∈ range n, i by
    simpa using (Fin.sum_univ_eq_sum_range (fun x => x) n)]
  rw [Finset.sum_range_id]

lemma sparse_hankel_det_zmod (p m : ℕ) (hp : p = 2*m + 1) (s : ℕ → ZMod p) (t : ZMod p)
    (hzero : ∀ n, p ≤ n → s n = 0) (htop : s (p-1) = t) :
    Matrix.det (fun i j : Fin p => s (i.val + j.val)) = ((-1 : ZMod p) ^ m) * t ^ p := by
  classical
  let M : Matrix (Fin p) (Fin p) (ZMod p) := fun i j => s (i.val + j.val)
  let B : Matrix (Fin p) (Fin p) (ZMod p) := M.submatrix id (Fin.revPerm : Equiv.Perm (Fin p))
  have htri : B.BlockTriangular id := by
    intro i j hij
    dsimp [B, M]
    apply hzero
    have hjlt : (j : ℕ) < i := by simpa using hij
    have hi_lt : (i : ℕ) < p := i.2
    have hj_lt : (j : ℕ) < p := j.2
    omega
  have hdiag : ∀ i : Fin p, B i i = t := by
    intro i
    dsimp [B, M]
    have hsum : i.val + (p - (i.val + 1)) = p - 1 := by omega
    rw [hsum, htop]
  have hdetB : B.det = t ^ p := by
    rw [Matrix.det_of_upperTriangular htri]
    simp [hdiag]
  have hperm : B.det = (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin p)) : ZMod p) * M.det := by
    simpa [B] using (Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin p)) M)
  have hsign : (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin p)) : ZMod p) = (-1 : ZMod p) ^ m := by
    have hsint := congrArg (fun z : ℤ => (z : ZMod p)) (by
      have hs := sign_revPerm_units p
      -- use odd corollary inline
      subst p
      rw [sign_revPerm_units]
      have hexp : (2 * m + 1) * (2 * m + 1 - 1) / 2 = m * (2*m+1) := by
        rw [show 2 * m + 1 - 1 = 2*m by omega]
        rw [show (2*m+1) * (2*m) = 2 * (m * (2*m+1)) by ring]
        rw [Nat.mul_div_right _ (by norm_num : 0 < 2)]
      rw [hexp]
      have hpow_units : (-1 : ℤˣ) ^ (m * (2*m+1)) = (-1 : ℤˣ) ^ m := by
        apply neg_one_pow_congr
        rw [Nat.even_mul]
        have hodd : Odd (2*m+1) := ⟨m, rfl⟩
        constructor
        · intro h
          exact h.resolve_right ((Nat.not_even_iff_odd).2 hodd)
        · intro hm
          exact Or.inl hm
      rw [hpow_units]
      simp : ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin p)) : ℤˣ) : ℤ) = (-1 : ℤ) ^ m)
    simpa using hsint
  have ht : t ^ p = ((-1 : ZMod p) ^ m) * M.det := by
    rw [← hdetB, hperm, hsign]
  have hsquare : ((-1 : ZMod p) ^ m) * ((-1 : ZMod p) ^ m) = 1 := by
    rw [← pow_add]
    have heven : Even (m+m) := ⟨m, by omega⟩
    simpa using (Even.neg_one_pow (α := ZMod p) heven)
  rw [ht, ← mul_assoc, hsquare, one_mul]
