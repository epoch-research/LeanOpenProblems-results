import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

/--
A228304: The sequence $a(n)$ is defined by the alternating sum of fourth powers of binomial coefficients.
$$a(n) = \sum_{k=0}^n \binom{n}{k}^4 (-1)^k$$
-/
def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 4)

/--
A228304 c(n) sequence:
$$c(n) = \sum_{k=0}^n (-1)^k \binom{n}{k}^2 \binom{2k}{k} \binom{2(n-k)}{n-k}$$
-/
def c (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 2) * (choose (2 * k) k : ℤ) * (choose (2 * (n - k)) (n - k) : ℤ)


lemma sign_revPerm (n : ℕ) :
    (Fin.revPerm : Equiv.Perm (Fin n)).sign = (-1 : ℤˣ) ^ (∑ j : Fin n, (j : ℕ)) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro j _
  have : ∀ i ∈ Finset.Iio j, (if (Fin.revPerm i) < (Fin.revPerm j) then (1:ℤˣ) else -1) = -1 := by
    intro i hi
    rw [Finset.mem_Iio] at hi
    rw [if_neg]
    simp only [Fin.revPerm_apply]
    rw [not_lt]
    exact (Fin.rev_le_rev).2 (le_of_lt hi)
  rw [Finset.prod_congr rfl this, Finset.prod_const, Fin.card_Iio]

lemma sign_rev_odd {p : ℕ} (t : ℕ) (hp : p = 2 * t + 1) :
    (Fin.revPerm : Equiv.Perm (Fin p)).sign = (-1 : ℤˣ) ^ t := by
  rw [sign_revPerm]
  have hsum : ∑ j : Fin p, (j : ℕ) = t + 2 * (t * t) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => k) p, Finset.sum_range_id, hp]
    rw [Nat.add_sub_cancel]
    have : (2 * t + 1) * (2 * t) = 2 * (t + 2 * (t * t)) := by ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hsum, pow_add, pow_mul]
  norm_num

lemma antitri_det {p : ℕ} (M : Matrix (Fin p) (Fin p) (ZMod p))
    (hz : ∀ i j : Fin p, p ≤ (i : ℕ) + (j : ℕ) → M i j = 0) :
    M.det = (Fin.revPerm : Equiv.Perm (Fin p)).sign * ∏ i : Fin p, M i i.rev := by
  set N : Matrix (Fin p) (Fin p) (ZMod p) := M.submatrix id Fin.revPerm with hN
  have hperm : N.det = (Fin.revPerm : Equiv.Perm (Fin p)).sign * M.det :=
    Matrix.det_permute' Fin.revPerm M
  have htri : N.BlockTriangular id := by
    intro i j hji
    simp only [id_eq] at hji
    rw [hN, Matrix.submatrix_apply, id_eq, Fin.revPerm_apply]
    apply hz
    rw [Fin.val_rev]
    omega
  have hdiag : N.det = ∏ i : Fin p, M i i.rev := by
    rw [Matrix.det_of_upperTriangular htri]
    apply Finset.prod_congr rfl
    intro i _
    rw [hN, Matrix.submatrix_apply, id_eq, Fin.revPerm_apply]
  rw [hdiag] at hperm
  -- hperm : ∏ M i i.rev = sign * M.det
  have hs := Int.units_mul_self (Fin.revPerm : Equiv.Perm (Fin p)).sign
  have hone : (↑↑(Fin.revPerm : Equiv.Perm (Fin p)).sign : ZMod p) *
      ↑↑(Fin.revPerm : Equiv.Perm (Fin p)).sign = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, hs, Units.val_one, Int.cast_one]
  rw [hperm, ← mul_assoc, hone, one_mul]

section NT
variable {p : ℕ} [Fact p.Prime]

lemma lucas_cast (n k : ℕ) :
    ((n.choose k : ℕ) : ZMod p)
      = ((n % p).choose (k % p) : ZMod p) * ((n / p).choose (k / p) : ZMod p) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := p)
  rw [← ZMod.natCast_eq_natCast_iff] at h
  push_cast at h
  exact h

lemma L_lowk (m k : ℕ) (hm : m < p) (hk : k < p) :
    ((Nat.choose (p + m) k : ℕ) : ZMod p) = ((Nat.choose m k : ℕ) : ZMod p) := by
  rw [lucas_cast]
  have h1 : (p + m) % p = m := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hm]
  have h2 : (p + m) / p = 1 := by
    rw [Nat.add_div_left _ (Nat.pos_of_ne_zero (by rintro rfl; exact absurd hm (by simp))), Nat.div_eq_of_lt hm]
  have h3 : k % p = k := Nat.mod_eq_of_lt hk
  have h4 : k / p = 0 := Nat.div_eq_of_lt hk
  rw [h1, h2, h3, h4]
  simp

lemma L_highk (m k : ℕ) (hm : m < p) (hk : k < p) :
    ((Nat.choose (p + m) (p + k) : ℕ) : ZMod p) = ((Nat.choose m k : ℕ) : ZMod p) := by
  rw [lucas_cast]
  have h1 : (p + m) % p = m := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hm]
  have h2 : (p + m) / p = 1 := by
    rw [Nat.add_div_left _ (Nat.pos_of_ne_zero (by rintro rfl; exact absurd hm (by simp))), Nat.div_eq_of_lt hm]
  have h3 : (p + k) % p = k := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hk]
  have h4 : (p + k) / p = 1 := by
    rw [Nat.add_div_left _ (Nat.pos_of_ne_zero (by rintro rfl; exact absurd hk (by simp))), Nat.div_eq_of_lt hk]
  rw [h1, h2, h3, h4]
  simp

lemma L_cb0 (k : ℕ) (h1 : p ≤ 2 * k) (h2 : k < p) :
    ((Nat.choose (2 * k) k : ℕ) : ZMod p) = 0 := by
  have hppos : 0 < p := (Fact.out : p.Prime).pos
  rw [lucas_cast]
  obtain ⟨d, hd, hdlt⟩ : ∃ d, 2 * k = d + p ∧ d < p := ⟨2 * k - p, by omega, by omega⟩
  rw [hd]
  have e1 : (d + p) % p = d := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hdlt]
  have e2 : (d + p) / p = 1 := by rw [Nat.add_div_right _ hppos, Nat.div_eq_of_lt hdlt]
  rw [e1, e2, Nat.mod_eq_of_lt h2, Nat.div_eq_of_lt h2]
  have hlt : d < k := by omega
  rw [Nat.choose_eq_zero_of_lt hlt]
  simp

open Polynomial in
lemma coeff_Xp_mul (Q : (ZMod p)[X]) (d : ℕ) :
    (((X : (ZMod p)[X]) ^ p + 1) * Q).coeff d
      = (if p ≤ d then Q.coeff (d - p) else 0) + Q.coeff d := by
  rw [add_mul, one_mul, Polynomial.coeff_add, mul_comm ((X : (ZMod p)[X]) ^ p) Q,
    Polynomial.coeff_mul_X_pow']

open Polynomial in
lemma L_cent (j : ℕ) (hj : j < p) :
    ((Nat.choose (2 * (p + j)) (p + j) : ℕ) : ZMod p)
      = 2 * ((Nat.choose (2 * j) j : ℕ) : ZMod p) := by
  have hp1 : ((X : (ZMod p)[X]) + 1) ^ p = X ^ p + 1 := by
    rw [add_pow_char]; simp
  have key : ((X : (ZMod p)[X]) + 1) ^ (2 * (p + j))
      = (X ^ p + 1) * ((X ^ p + 1) * (X + 1) ^ (2 * j)) := by
    rw [show 2 * (p + j) = (p + p) + 2 * j by ring, pow_add, pow_add, hp1]
    ring
  rw [← coeff_X_add_one_pow (ZMod p) (2 * (p + j)) (p + j), key]
  simp only [coeff_Xp_mul, Polynomial.coeff_X_add_one_pow]
  have hj1 : ¬ (p ≤ j) := by omega
  have hj2 : p ≤ p + j := by omega
  have hj3 : Nat.choose (2 * j) (p + j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp only [Nat.add_sub_cancel_left, if_pos hj2, if_neg hj1, hj3]
  push_cast
  ring

lemma L_pm1 : ∀ k, k < p → ((Nat.choose (p - 1) k : ℕ) : ZMod p) = (-1) ^ k := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro k
  induction k with
  | zero => intro _; simp
  | succ n ih =>
    intro hk
    have hpascal : Nat.choose p (n + 1)
        = Nat.choose (p - 1) n + Nat.choose (p - 1) (n + 1) := by
      have hp1 : (p - 1) + 1 = p := by
        have := (Fact.out : p.Prime).one_lt; omega
      calc Nat.choose p (n + 1) = Nat.choose ((p - 1) + 1) (n + 1) := by rw [hp1]
        _ = Nat.choose (p - 1) n + Nat.choose (p - 1) (n + 1) := Nat.choose_succ_succ' (p - 1) n
    have hdvd : ((Nat.choose p (n + 1) : ℕ) : ZMod p) = 0 := by
      rw [CharP.cast_eq_zero_iff (ZMod p) p]
      exact (Fact.out : p.Prime).dvd_choose_self (by omega) hk
    have hcast : (0 : ZMod p)
        = ((Nat.choose (p - 1) n : ℕ) : ZMod p) + ((Nat.choose (p - 1) (n + 1) : ℕ) : ZMod p) := by
      rw [← hdvd, hpascal]; push_cast; ring
    have ihn := ih (by omega)
    have hneg : ((Nat.choose (p - 1) (n + 1) : ℕ) : ZMod p)
        = -((Nat.choose (p - 1) n : ℕ) : ZMod p) := by
      linear_combination -hcast
    rw [hneg, ihn]; ring

end NT

lemma alt_sum_odd {R : Type*} [CommRing R] (t : ℕ) :
    ∑ k ∈ range (2 * t + 1), (-1 : R) ^ k = 1 := by
  induction t with
  | zero => simp
  | succ s ih =>
    have heq : 2 * (s + 1) + 1 = (2 * s + 1) + 1 + 1 := by ring
    rw [heq, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (-1 : R) ^ (2 * s + 1) = -1 := by rw [pow_succ, pow_mul]; simp
    have h2 : (-1 : R) ^ (2 * s + 1 + 1) = 1 := by rw [pow_succ, pow_succ, pow_mul]; simp
    rw [h1, h2]; ring

section NT2
variable {p : ℕ} [Fact p.Prime]

lemma a_cast (n : ℕ) :
    ((a n : ℤ) : ZMod p)
      = ∑ k ∈ range (n + 1), (-1 : ZMod p) ^ k * ((Nat.choose n k : ℕ) : ZMod p) ^ 4 := by
  rw [a]
  push_cast
  rfl

lemma a_pm1 (t : ℕ) (hp : p = 2 * t + 1) :
    ((a (p - 1) : ℤ) : ZMod p) = 1 := by
  have hpm1 : p - 1 = 2 * t := by omega
  rw [a_cast]
  have : (p - 1) + 1 = p := by omega
  rw [this]
  have hterm : ∀ k ∈ range p, (-1 : ZMod p) ^ k * ((Nat.choose (p - 1) k : ℕ) : ZMod p) ^ 4
      = (-1 : ZMod p) ^ k := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [L_pm1 k hk]
    have h4 : ((-1 : ZMod p) ^ k) ^ 4 = 1 := by
      rw [← pow_mul]; exact Even.neg_one_pow ⟨k * 2, by ring⟩
    rw [h4, mul_one]
  rw [Finset.sum_congr rfl hterm]
  have := alt_sum_odd (R := ZMod p) t
  rw [← hp] at this
  exact this

lemma a_zero (t m : ℕ) (hp : p = 2 * t + 1) (hm : m < p - 1) :
    ((a (p + m) : ℤ) : ZMod p) = 0 := by
  have hmp : m < p := by omega
  have hsign : (-1 : ZMod p) ^ p = -1 := Odd.neg_one_pow ⟨t, by omega⟩
  rw [a_cast]
  set f : ℕ → ZMod p := fun k => (-1 : ZMod p) ^ k * ((Nat.choose (p + m) k : ℕ) : ZMod p) ^ 4
    with hf
  have e1 : ∑ k ∈ range (p + m + 1), f k
      = ∑ k ∈ Finset.Ico 0 (m + 1), f k + ∑ k ∈ Finset.Ico (m + 1) (p + m + 1), f k := by
    have h0 : (0 : ℕ) ≤ m + 1 := by omega
    have hb : m + 1 ≤ p + m + 1 := by omega
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive f h0 hb]
  have e2 : ∑ k ∈ Finset.Ico (m + 1) (p + m + 1), f k
      = ∑ k ∈ Finset.Ico (m + 1) p, f k + ∑ k ∈ Finset.Ico p (p + m + 1), f k := by
    have h3 : m + 1 ≤ p := by omega
    have h4 : p ≤ p + m + 1 := by omega
    rw [← Finset.sum_Ico_consecutive f h3 h4]
  have emid : ∑ k ∈ Finset.Ico (m + 1) p, f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [hf]
    simp only
    rw [L_lowk m k hmp (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have eshift : ∑ k ∈ Finset.Ico p (p + m + 1), f k = ∑ k ∈ range (m + 1), f (p + k) := by
    have hb : p + m + 1 - p = m + 1 := by omega
    rw [Finset.sum_Ico_eq_sum_range, hb]
  have eIco0 : ∑ k ∈ Finset.Ico 0 (m + 1), f k = ∑ k ∈ range (m + 1), f k := by
    rw [Finset.range_eq_Ico]
  rw [e1, e2, emid, eshift, eIco0, zero_add, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_range] at hk
  have hkp : k < p := by omega
  rw [hf]
  simp only
  rw [L_lowk m k hmp hkp, L_highk m k hmp hkp]
  rw [pow_add, hsign]
  ring

lemma c_cast (n : ℕ) :
    ((c n : ℤ) : ZMod p)
      = ∑ k ∈ range (n + 1), (-1 : ZMod p) ^ k * ((Nat.choose n k : ℕ) : ZMod p) ^ 2
          * ((Nat.choose (2 * k) k : ℕ) : ZMod p)
          * ((Nat.choose (2 * (n - k)) (n - k) : ℕ) : ZMod p) := by
  rw [c]
  push_cast
  rfl

lemma c_zero (t m : ℕ) (hp : p = 2 * t + 1) (hm : m < p - 1) :
    ((c (p + m) : ℤ) : ZMod p) = 0 := by
  have hmp : m < p := by omega
  have hsign : (-1 : ZMod p) ^ p = -1 := Odd.neg_one_pow ⟨t, by omega⟩
  rw [c_cast]
  set f : ℕ → ZMod p := fun k => (-1 : ZMod p) ^ k * ((Nat.choose (p + m) k : ℕ) : ZMod p) ^ 2
      * ((Nat.choose (2 * k) k : ℕ) : ZMod p)
      * ((Nat.choose (2 * (p + m - k)) (p + m - k) : ℕ) : ZMod p) with hf
  have e1 : ∑ k ∈ range (p + m + 1), f k
      = ∑ k ∈ Finset.Ico 0 (m + 1), f k + ∑ k ∈ Finset.Ico (m + 1) (p + m + 1), f k := by
    have h0 : (0 : ℕ) ≤ m + 1 := by omega
    have hb : m + 1 ≤ p + m + 1 := by omega
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive f h0 hb]
  have e2 : ∑ k ∈ Finset.Ico (m + 1) (p + m + 1), f k
      = ∑ k ∈ Finset.Ico (m + 1) p, f k + ∑ k ∈ Finset.Ico p (p + m + 1), f k := by
    have h3 : m + 1 ≤ p := by omega
    have h4 : p ≤ p + m + 1 := by omega
    rw [← Finset.sum_Ico_consecutive f h3 h4]
  have emid : ∑ k ∈ Finset.Ico (m + 1) p, f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [hf]
    simp only
    rw [L_lowk m k hmp (by omega), Nat.choose_eq_zero_of_lt (show m < k by omega)]
    simp
  have eshift : ∑ k ∈ Finset.Ico p (p + m + 1), f k = ∑ k ∈ range (m + 1), f (p + k) := by
    have hb : p + m + 1 - p = m + 1 := by omega
    rw [Finset.sum_Ico_eq_sum_range, hb]
  have eIco0 : ∑ k ∈ Finset.Ico 0 (m + 1), f k = ∑ k ∈ range (m + 1), f k := by
    rw [Finset.range_eq_Ico]
  rw [e1, e2, emid, eshift, eIco0, zero_add, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_range] at hk
  have hkp : k < p := by omega
  have hmk : m - k < p := by omega
  rw [hf]
  simp only
  -- rewrite the nat-subtraction arguments
  have hs1 : p + m - k = p + (m - k) := by omega
  have hs2 : p + m - (p + k) = m - k := by omega
  rw [hs1, hs2]
  rw [L_lowk m k hmp hkp, L_highk m k hmp hkp, L_cent (m - k) hmk, L_cent k hkp]
  rw [pow_add, hsign]
  ring

lemma c_pm1 (t : ℕ) (hp : p = 2 * t + 1) :
    ((c (p - 1) : ℤ) : ZMod p) = (-1 : ZMod p) ^ t := by
  rw [c_cast, show (p - 1) + 1 = p from by omega]
  have htmem : t ∈ range p := Finset.mem_range.mpr (by omega)
  have hother : ∀ k ∈ range p, k ≠ t →
      (-1 : ZMod p) ^ k * ((Nat.choose (p - 1) k : ℕ) : ZMod p) ^ 2
        * ((Nat.choose (2 * k) k : ℕ) : ZMod p)
        * ((Nat.choose (2 * (p - 1 - k)) (p - 1 - k) : ℕ) : ZMod p) = 0 := by
    intro k hk hkt
    rw [Finset.mem_range] at hk
    rcases lt_or_gt_of_ne hkt with hlt | hgt
    · -- k < t : the second central binomial vanishes
      rw [L_cb0 (p - 1 - k) (by omega) (by omega)]
      ring
    · -- k > t : the first central binomial vanishes
      rw [L_cb0 k (by omega) hk]
      ring
  rw [Finset.sum_eq_single_of_mem t htmem hother]
  -- goal : term at t = (-1)^t
  rw [show p - 1 - t = t from by omega, show 2 * t = p - 1 from by omega]
  rw [L_pm1 t (by omega)]
  have hpow : (-1 : ZMod p) ^ t * ((-1 : ZMod p) ^ t) ^ 2 * (-1 : ZMod p) ^ t * (-1 : ZMod p) ^ t
      = ((-1 : ZMod p) ^ t) ^ 5 := by ring
  rw [hpow, ← pow_mul, show t * 5 = t + 2 * (2 * t) from by ring, pow_add, pow_mul]
  simp

lemma hankel_det (t : ℕ) (hpt : p = 2 * t + 1) (s : ℕ → ℤ) (d : ZMod p)
    (hz : ∀ i j : Fin p, p ≤ (i : ℕ) + (j : ℕ) → ((s ((i : ℕ) + (j : ℕ)) : ℤ) : ZMod p) = 0)
    (hd : ∀ i : Fin p, ((s ((i : ℕ) + ((i.rev : Fin p) : ℕ)) : ℤ) : ZMod p) = d) :
    ((Matrix.det (fun i j : Fin p => s ((i : ℕ) + (j : ℕ))) : ℤ) : ZMod p)
      = (-1 : ZMod p) ^ t * d ^ p := by
  set M : Matrix (Fin p) (Fin p) (ZMod p) :=
    (Int.castRingHom (ZMod p)).mapMatrix (fun i j : Fin p => s ((i : ℕ) + (j : ℕ))) with hM
  have hcast : ((Matrix.det (fun i j : Fin p => s ((i : ℕ) + (j : ℕ))) : ℤ) : ZMod p) = M.det := by
    rw [hM, ← RingHom.map_det]; rfl
  rw [hcast]
  have hMz : ∀ i j : Fin p, p ≤ (i : ℕ) + (j : ℕ) → M i j = 0 := by
    intro i j hij
    rw [hM]; simp only [RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]
    exact hz i j hij
  rw [antitri_det M hMz]
  have hprod : ∏ i : Fin p, M i i.rev = d ^ p := by
    have : ∀ i : Fin p, M i i.rev = d := by
      intro i
      rw [hM]; simp only [RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]
      exact hd i
    rw [Finset.prod_congr rfl (fun i _ => this i), Finset.prod_const]
    congr 1
    simp
  rw [hprod, sign_rev_odd t hpt]
  congr 1
  push_cast
  ring

end NT2

/--
A228304 Conjecture: Let p be any odd prime, and let A(p) be the p X p determinant with (i,j)-entry equal to a(i+j) for all i,j = 0,...,p-1. Then A(p) == (-1)^{(p-1)/2} (mod p). Similarly, if c(n) = sum_{k=0}^n (-1)^k*C(n,k)^2*C(2k,k)*C(2(n-k),n-k) and C(p) is the p X p determinant with (i,j)-entry equal to c(i+j) for all i,j = 0,...,p-1, then we have C(p) == 1 (mod p).
-/
theorem oeis_228304_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) :
    let N := Fin p
    let half_minus_one := (p - 1) / 2
    -- A(p) is the p x p matrix with entries a(i+j)
    let A : Matrix N N ℤ := fun i j => a (i.val + j.val)
    -- C(p) is the p x p matrix with entries c(i+j)
    let C : Matrix N N ℤ := fun i j => c (i.val + j.val)
    (Matrix.det A ≡ (-1 : ℤ) ^ half_minus_one [ZMOD p]) ∧ (Matrix.det C ≡ 1 [ZMOD p]) := by
  intro N half_minus_one A C
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, hpt⟩ : ∃ t, p = 2 * t + 1 := (hp.odd_of_ne_two h_odd)
  have hht : half_minus_one = t := by simp only [half_minus_one]; omega
  -- A part
  have hAz : ∀ i j : Fin p, p ≤ (i : ℕ) + (j : ℕ) → ((a ((i : ℕ) + (j : ℕ)) : ℤ) : ZMod p) = 0 := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hm : (i : ℕ) + (j : ℕ) - p < p - 1 := by omega
    have heq : (i : ℕ) + (j : ℕ) = p + ((i : ℕ) + (j : ℕ) - p) := by omega
    rw [heq]
    exact a_zero t ((i : ℕ) + (j : ℕ) - p) hpt hm
  have hAd : ∀ i : Fin p, ((a ((i : ℕ) + ((i.rev : Fin p) : ℕ)) : ℤ) : ZMod p) = 1 := by
    intro i
    have hi := i.isLt
    have heq : (i : ℕ) + ((i.rev : Fin p) : ℕ) = p - 1 := by rw [Fin.val_rev]; omega
    rw [heq]
    exact a_pm1 t hpt
  have hAdet := hankel_det t hpt a 1 hAz hAd
  -- C part
  have hCz : ∀ i j : Fin p, p ≤ (i : ℕ) + (j : ℕ) → ((c ((i : ℕ) + (j : ℕ)) : ℤ) : ZMod p) = 0 := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hm : (i : ℕ) + (j : ℕ) - p < p - 1 := by omega
    have heq : (i : ℕ) + (j : ℕ) = p + ((i : ℕ) + (j : ℕ) - p) := by omega
    rw [heq]
    exact c_zero t ((i : ℕ) + (j : ℕ) - p) hpt hm
  have hCd : ∀ i : Fin p, ((c ((i : ℕ) + ((i.rev : Fin p) : ℕ)) : ℤ) : ZMod p) = (-1 : ZMod p) ^ t := by
    intro i
    have hi := i.isLt
    have heq : (i : ℕ) + ((i.rev : Fin p) : ℕ) = p - 1 := by rw [Fin.val_rev]; omega
    rw [heq]
    exact c_pm1 t hpt
  have hCdet := hankel_det t hpt c ((-1 : ZMod p) ^ t) hCz hCd
  constructor
  · -- det A ≡ (-1)^((p-1)/2) [ZMOD p]
    rw [← ZMod.intCast_eq_intCast_iff]
    rw [hht]
    show ((Matrix.det (fun i j : Fin p => a ((i : ℕ) + (j : ℕ))) : ℤ) : ZMod p)
        = (((-1 : ℤ) ^ t : ℤ) : ZMod p)
    rw [hAdet]
    push_cast
    ring
  · -- det C ≡ 1 [ZMOD p]
    rw [← ZMod.intCast_eq_intCast_iff]
    show ((Matrix.det (fun i j : Fin p => c ((i : ℕ) + (j : ℕ))) : ℤ) : ZMod p)
        = ((1 : ℤ) : ZMod p)
    rw [hCdet]
    rw [ZMod.pow_card]
    rw [← pow_add, show t + t = 2 * t from by ring, pow_mul]
    simp
