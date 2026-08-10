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



lemma sign_revPerm (n : ℕ) : (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) = (-1 : ℤ) ^ (n * (n - 1) / 2) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  simp only [Fin.revPerm_apply, Units.coe_prod]
  trans ∏ x : Fin n, (-1 : ℤ) ^ (x : ℕ)
  · apply Finset.prod_congr rfl
    intro x hx
    trans ∏ i ∈ Finset.Iio x, (-1 : ℤ)
    · apply Finset.prod_congr rfl
      intro i hi
      have hix : i < x := by simpa using hi
      have : ¬ x < i := not_lt.mpr (le_of_lt hix)
      simp [this]
    · rw [Finset.prod_const]
      simp
  · trans (-1 : ℤ) ^ (∑ x : Fin n, (x : ℕ))
    · simpa using (Finset.prod_pow_eq_pow_sum Finset.univ (fun x : Fin n => (x : ℕ)) (-1 : ℤ))
    · congr 1
      rw [Finset.sum_fin_eq_sum_range]
      trans ∑ x ∈ Finset.range n, x
      · apply Finset.sum_congr rfl
        intro x hx
        simp [Finset.mem_range.mp hx]
      · exact Finset.sum_range_id n


lemma det_of_antidiagonal_mod {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (d : R)
    (hzero : ∀ i j : Fin n, n ≤ i.val + j.val → M i j = 0)
    (hdiag : ∀ i j : Fin n, i.val + j.val = n - 1 → M i j = d) :
    M.det = (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : R) * d ^ n) := by
  let B : Matrix (Fin n) (Fin n) R := M.submatrix (Fin.revPerm : Equiv.Perm (Fin n)) id
  have htri : Bᵀ.BlockTriangular id := by
    intro i j hij
    dsimp [B]
    apply hzero
    have hlt : j.val < i.val := by simpa using hij
    have hle : j.val + 1 ≤ i.val := Nat.succ_le_of_lt hlt
    rw [Fin.val_rev]
    omega
  have hBdet : B.det = d ^ n := by
    calc
      B.det = Bᵀ.det := by rw [Matrix.det_transpose]
      _ = ∏ i, Bᵀ i i := Matrix.det_of_upperTriangular htri
      _ = ∏ i : Fin n, d := by
        apply Finset.prod_congr rfl
        intro i hi
        dsimp [B]
        apply hdiag
        rw [Fin.val_rev]
        omega
      _ = d ^ n := by simp
  have hperm : B.det = (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : R) * M.det) := by
    simpa [B] using (Matrix.det_permute (Fin.revPerm : Equiv.Perm (Fin n)) M)
  have hsgn_sq : (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : R) *
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : R)) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with hs | hs <;>
      simp [hs]
  calc
    M.det = 1 * M.det := by simp
    _ = (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : R) *
        ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : R)) * M.det := by rw [hsgn_sq]
    _ = (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : R) * B.det) := by rw [hperm]; ring
    _ = (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : R) * d ^ n) := by rw [hBdet]

lemma zmod_nat_ne_zero_of_pos_lt {p k : ℕ} (hk0 : 0 < k) (hkp : k < p) : (k : ZMod p) ≠ 0 := by
  intro h
  exact Nat.not_dvd_of_pos_of_lt hk0 hkp ((ZMod.natCast_eq_zero_iff k p).mp h)

lemma choose_cast_lucas (p n k : ℕ) [Fact p.Prime] :
    ((Nat.choose n k : ℕ) : ZMod p) =
      ((Nat.choose (n % p) (k % p) * Nat.choose (n / p) (k / p) : ℕ) : ZMod p) := by
  rw [ZMod.natCast_eq_natCast_iff]
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat

lemma choose_p_sub_one_cast (p k : ℕ) [Fact p.Prime] (hk : k < p) :
    ((Nat.choose (p - 1) k : ℕ) : ZMod p) = (-1 : ZMod p) ^ k := by
  induction k with
  | zero => simp
  | succ k IH =>
    have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
    have hklt : k < p := lt_trans (Nat.lt_succ_self k) hk
    have hksuccpos : 0 < k + 1 := Nat.succ_pos k
    have hne : ((k + 1 : ℕ) : ZMod p) ≠ 0 := zmod_nat_ne_zero_of_pos_lt hksuccpos hk
    apply mul_right_cancel₀ hne
    change ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod p) * ((k + 1 : ℕ) : ZMod p) =
      (-1 : ZMod p) ^ (k + 1) * ((k + 1 : ℕ) : ZMod p)
    calc
      ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod p) * (((k + 1 : ℕ) : ZMod p))
          = ((Nat.choose (p - 1) (k + 1) * (k + 1) : ℕ) : ZMod p) := by norm_num [Nat.cast_mul]
      _ = ((Nat.choose (p - 1) k * ((p - 1) - k) : ℕ) : ZMod p) := by rw [Nat.choose_succ_right_eq]
      _ = ((Nat.choose (p - 1) k : ℕ) : ZMod p) * (((p - 1) - k : ℕ) : ZMod p) := by norm_num [Nat.cast_mul]
      _ = (-1 : ZMod p) ^ k * (-(k + 1 : ZMod p)) := by
        congr 1
        · exact IH hklt
        · have hsub : (p - 1) - k = p - (k + 1) := by omega
          rw [hsub]
          have : ((p - (k + 1) : ℕ) : ZMod p) = -(k + 1 : ZMod p) := by
            rw [eq_neg_iff_add_eq_zero]
            have hcastsucc : (((k + 1 : ℕ) : ZMod p)) = (k : ZMod p) + 1 := by norm_num
            rw [← hcastsucc]
            have hle : k + 1 ≤ p := le_of_lt hk
            rw [← Nat.cast_add, Nat.sub_add_cancel hle, ZMod.natCast_self]
          exact this
      _ = (-1 : ZMod p) ^ (k + 1) * (((k + 1 : ℕ) : ZMod p)) := by
        rw [pow_succ]
        norm_num [Nat.cast_add]
        ring

lemma choose_p_add_small_cast (p r k : ℕ) [Fact p.Prime] (hr : r < p) (hk : k < p) :
    ((Nat.choose (p + r) k : ℕ) : ZMod p) = ((Nat.choose r k : ℕ) : ZMod p) := by
  rw [choose_cast_lucas]
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  have hmodn : (p + r) % p = r := by
    rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
  have hdivn : (p + r) / p = 1 := by
    rw [Nat.add_comm]
    simpa [Nat.div_eq_of_lt hr] using (Nat.add_mul_div_left r 1 hp0 : (r + p * 1) / p = r / p + 1)
  have hmodk : k % p = k := Nat.mod_eq_of_lt hk
  have hdivk : k / p = 0 := Nat.div_eq_of_lt hk
  rw [hmodn, hdivn, hmodk, hdivk]
  simp

lemma choose_p_add_p_add_cast (p r l : ℕ) [Fact p.Prime] (hr : r < p) (hl : l < p) :
    ((Nat.choose (p + r) (p + l) : ℕ) : ZMod p) = ((Nat.choose r l : ℕ) : ZMod p) := by
  rw [choose_cast_lucas]
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  have hmodn : (p + r) % p = r := by
    rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
  have hdivn : (p + r) / p = 1 := by
    rw [Nat.add_comm]
    simpa [Nat.div_eq_of_lt hr] using (Nat.add_mul_div_left r 1 hp0 : (r + p * 1) / p = r / p + 1)
  have hmodk : (p + l) % p = l := by
    rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hl]
  have hdivk : (p + l) / p = 1 := by
    rw [Nat.add_comm]
    simpa [Nat.div_eq_of_lt hl] using (Nat.add_mul_div_left l 1 hp0 : (l + p * 1) / p = l / p + 1)
  rw [hmodn, hdivn, hmodk, hdivk]
  simp

lemma choose_p_add_middle_cast (p r k : ℕ) [Fact p.Prime] (hr : r < p) (hrk : r < k) (hkp : k < p) :
    ((Nat.choose (p + r) k : ℕ) : ZMod p) = 0 := by
  rw [choose_p_add_small_cast p r k hr hkp]
  rw [Nat.choose_eq_zero_of_lt hrk]
  simp

lemma neg_one_pow_add_p_eq_neg (p l : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    (-1 : ZMod p) ^ (p + l) = - ((-1 : ZMod p) ^ l) := by
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hpodd
  rw [pow_add]
  have hpown : (-1 : ZMod p) ^ p = -1 := hodd.neg_one_pow
  rw [hpown]
  ring

lemma int_cast_a_term (p n k : ℕ) :
    ((((-1 : ℤ) ^ k) * ((Nat.choose n k : ℤ) ^ 4) : ℤ) : ZMod p) =
      (-1 : ZMod p) ^ k * (((Nat.choose n k : ℕ) : ZMod p) ^ 4) := by
  norm_num

lemma int_cast_c_term (p n k : ℕ) :
    ((((-1 : ℤ) ^ k) * ((Nat.choose n k : ℤ) ^ 2) * (Nat.choose (2 * k) k : ℤ) *
        (Nat.choose (2 * (n - k)) (n - k) : ℤ) : ℤ) : ZMod p) =
      (-1 : ZMod p) ^ k * (((Nat.choose n k : ℕ) : ZMod p) ^ 2) *
        ((Nat.choose (2 * k) k : ℕ) : ZMod p) *
        ((Nat.choose (2 * (n - k)) (n - k) : ℕ) : ZMod p) := by
  norm_num

lemma a_p_add_pair_term (p r l : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    (hr : r < p) (hl : l < p) :
    ((((-1 : ℤ) ^ (p + l)) * ((Nat.choose (p + r) (p + l) : ℤ) ^ 4) : ℤ) : ZMod p) =
      - ((((-1 : ℤ) ^ l) * ((Nat.choose (p + r) l : ℤ) ^ 4) : ℤ) : ZMod p) := by
  rw [int_cast_a_term, int_cast_a_term]
  rw [choose_p_add_p_add_cast p r l hr hl, choose_p_add_small_cast p r l hr hl]
  rw [neg_one_pow_add_p_eq_neg p l hpodd]
  ring

lemma a_p_add_middle_term_zero (p r k : ℕ) [Fact p.Prime]
    (hr : r < p) (hrk : r < k) (hkp : k < p) :
    ((((-1 : ℤ) ^ k) * ((Nat.choose (p + r) k : ℤ) ^ 4) : ℤ) : ZMod p) = 0 := by
  rw [int_cast_a_term]
  rw [choose_p_add_middle_cast p r k hr hrk hkp]
  ring

lemma a_p_add_cast (p r : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) (hr : r + 1 < p) :
    (a (p + r) : ZMod p) = 0 := by
  let f : ℕ → ZMod p := fun k => ((((-1 : ℤ) ^ k) * ((Nat.choose (p + r) k : ℤ) ^ 4) : ℤ) : ZMod p)
  have hrp : r < p := by omega
  have hr1le : r + 1 ≤ p := le_of_lt hr
  unfold a
  rw [Int.cast_sum]
  change (∑ k ∈ Finset.range (p + r + 1), f k) = 0
  have hlen : p + r + 1 = p + (r + 1) := by omega
  rw [hlen]
  rw [Finset.sum_range_add f p (r + 1)]
  have hp_split : (r + 1) + (p - (r + 1)) = p := by omega
  have hsplit_sum : (∑ x ∈ Finset.range p, f x) =
      (∑ x ∈ Finset.range (r + 1), f x) +
        (∑ x ∈ Finset.range (p - (r + 1)), f (r + 1 + x)) := by
    simpa [hp_split] using (Finset.sum_range_add f (r + 1) (p - (r + 1)))
  rw [hsplit_sum]
  have hmid : (∑ x ∈ Finset.range (p - (r + 1)), f (r + 1 + x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    dsimp [f]
    apply a_p_add_middle_term_zero p r (r + 1 + x) (by omega) (by omega)
    have hxlt : x < p - (r + 1) := by simpa using hx
    omega
  have hhigh : (∑ x ∈ Finset.range (r + 1), f (p + x)) = - (∑ x ∈ Finset.range (r + 1), f x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hxlt : x < p := by
      have : x < r + 1 := by simpa using hx
      omega
    dsimp [f]
    exact a_p_add_pair_term p r x hpodd (by omega) hxlt
  rw [hmid, hhigh]
  abel


lemma a_p_sub_one_cast (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    (a (p - 1) : ZMod p) = 1 := by
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hpodd
  unfold a
  have hlen : p - 1 + 1 = p := Nat.sub_one_add_one hp0.ne'
  rw [hlen]
  rw [Int.cast_sum]

  trans (∑ k ∈ range p, ((-1 : ZMod p) ^ k))
  · apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < p := by simpa using hk
    rw [int_cast_a_term, choose_p_sub_one_cast p k hklt]
    have hpow4 : (((-1 : ZMod p) ^ k) ^ 4) = 1 := by
      rw [← pow_mul]
      exact Even.neg_one_pow (show Even (k * 4) from ⟨2 * k, by ring⟩)
    rw [hpow4, mul_one]
  · rw [neg_one_geom_sum]
    simp [Nat.not_even_iff_odd.mpr hodd]

lemma choose_two_mul_cast_eq_zero_of_large (p t : ℕ) [Fact p.Prime]
    (htp : t < p) (hlt : p ≤ 2 * t) :
    ((Nat.choose (2 * t) t : ℕ) : ZMod p) = 0 := by
  rw [choose_cast_lucas]
  have htdiv : t / p = 0 := Nat.div_eq_of_lt htp
  have htdig : t % p = t := Nat.mod_eq_of_lt htp
  have h2div : (2 * t) / p = 1 := by
    have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
    have hlt2 : 2 * t < 2 * p := by nlinarith [htp]
    have hle : 2 * t < (1 + 1) * p := by omega
    exact Nat.div_eq_of_lt_le (by simpa using hlt) hle
  have h2mod : (2 * t) % p = 2 * t - p := by
    have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
    have hlt2 : 2 * t < 2 * p := by nlinarith [htp]
    have hlt2' : 2 * t < p * 2 := by simpa [Nat.mul_comm] using hlt2
    rw [Nat.mod_eq_sub_mod hlt]
    exact Nat.mod_eq_of_lt (by omega)
  rw [htdiv, htdig, h2div, h2mod]
  have : 2 * t - p < t := by omega
  rw [Nat.choose_eq_zero_of_lt this]
  simp

lemma choose_two_mul_p_add_cast (p t : ℕ) [Fact p.Prime] (htp : t < p) :
    ((Nat.choose (2 * (p + t)) (p + t) : ℕ) : ZMod p) =
      (2 : ZMod p) * ((Nat.choose (2 * t) t : ℕ) : ZMod p) := by
  by_cases hlt : p ≤ 2 * t
  · rw [choose_two_mul_cast_eq_zero_of_large p t htp hlt]
    rw [choose_cast_lucas]
    have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
    have hp2 : 2 * (p + t) = 2 * p + 2 * t := by ring
    have hmodk : (p + t) % p = t := by
      rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt htp]
    have hdivk : (p + t) / p = 1 := by
      rw [Nat.add_comm]
      simpa [Nat.div_eq_of_lt htp] using (Nat.add_mul_div_left t 1 hp0 : (t + p * 1) / p = t / p + 1)
    have hmodn : (2 * (p + t)) % p = (2 * t) % p := by
      rw [hp2]
      simp [Nat.add_mod, Nat.mul_mod]
    have hdivn : (2 * (p + t)) / p = 2 + (2 * t) / p := by

      rw [hp2]
      simpa [Nat.mul_comm, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.add_mul_div_left (2 * t) 2 hp0)
    rw [hmodk, hdivk, hmodn, hdivn]
    have htdiv : t / p = 0 := Nat.div_eq_of_lt htp
    have htdig : t % p = t := Nat.mod_eq_of_lt htp
    have h2div : (2 * t) / p = 1 := by
      have hlt2 : 2 * t < 2 * p := by nlinarith [htp]
      exact Nat.div_eq_of_lt_le (by simpa using hlt) (by omega)
    have h2modlt : (2 * t) % p < t := by
      have h2mod : (2 * t) % p = 2 * t - p := by
        rw [Nat.mod_eq_sub_mod hlt]
        exact Nat.mod_eq_of_lt (by omega)
      rw [h2mod]
      omega
    rw [h2div]
    rw [Nat.choose_eq_zero_of_lt h2modlt]
    norm_num [Nat.cast_mul, Nat.mul_comm]
  · have h2ltp : 2 * t < p := lt_of_not_ge hlt
    rw [choose_cast_lucas]
    have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
    have hp2 : 2 * (p + t) = 2 * p + 2 * t := by ring
    have hmodk : (p + t) % p = t := by
      rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt htp]
    have hdivk : (p + t) / p = 1 := by
      rw [Nat.add_comm]
      simpa [Nat.div_eq_of_lt htp] using (Nat.add_mul_div_left t 1 hp0 : (t + p * 1) / p = t / p + 1)
    have hmodn : (2 * (p + t)) % p = 2 * t := by
      rw [hp2]
      simp [Nat.add_mod, Nat.mod_eq_of_lt h2ltp]
    have hdivn : (2 * (p + t)) / p = 2 := by
      rw [hp2]
      rw [show 2 * p = p * 2 by ring]
      simpa [Nat.div_eq_of_lt h2ltp] using (Nat.mul_add_div hp0 2 (2 * t))
    rw [hmodk, hdivk, hmodn, hdivn]
    norm_num [Nat.cast_mul, Nat.mul_comm]


lemma c_p_add_middle_term_zero (p r k : ℕ) [Fact p.Prime]
    (hr : r < p) (hrk : r < k) (hkp : k < p) :
    ((((-1 : ℤ) ^ k) * ((Nat.choose (p + r) k : ℤ) ^ 2) * (Nat.choose (2 * k) k : ℤ) *
        (Nat.choose (2 * ((p + r) - k)) ((p + r) - k) : ℤ) : ℤ) : ZMod p) = 0 := by
  rw [int_cast_c_term]
  rw [choose_p_add_middle_cast p r k hr hrk hkp]
  ring

lemma c_p_add_pair_term (p r l : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    (hr : r < p) (hlr : l ≤ r) :
    ((((-1 : ℤ) ^ (p + l)) * ((Nat.choose (p + r) (p + l) : ℤ) ^ 2) *
        (Nat.choose (2 * (p + l)) (p + l) : ℤ) *
        (Nat.choose (2 * ((p + r) - (p + l))) ((p + r) - (p + l)) : ℤ) : ℤ) : ZMod p) =
      - ((((-1 : ℤ) ^ l) * ((Nat.choose (p + r) l : ℤ) ^ 2) *
        (Nat.choose (2 * l) l : ℤ) *
        (Nat.choose (2 * ((p + r) - l)) ((p + r) - l) : ℤ) : ℤ) : ZMod p) := by
  have hlp : l < p := by omega
  have hrlp : r - l < p := by omega
  rw [int_cast_c_term, int_cast_c_term]
  rw [choose_p_add_p_add_cast p r l hr hlp, choose_p_add_small_cast p r l hr hlp]
  have hsub1 : (p + r) - (p + l) = r - l := by omega
  have hsub2 : (p + r) - l = p + (r - l) := by omega
  rw [hsub1, hsub2]
  rw [choose_two_mul_p_add_cast p l hlp]
  rw [choose_two_mul_p_add_cast p (r - l) hrlp]
  rw [neg_one_pow_add_p_eq_neg p l hpodd]
  ring

lemma c_p_add_cast (p r : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) (hr : r + 1 < p) :
    (c (p + r) : ZMod p) = 0 := by
  let f : ℕ → ZMod p := fun k => ((((-1 : ℤ) ^ k) * ((Nat.choose (p + r) k : ℤ) ^ 2) *
        (Nat.choose (2 * k) k : ℤ) * (Nat.choose (2 * ((p + r) - k)) ((p + r) - k) : ℤ) : ℤ) : ZMod p)
  unfold c
  rw [Int.cast_sum]
  change (∑ k ∈ Finset.range (p + r + 1), f k) = 0
  have hlen : p + r + 1 = p + (r + 1) := by omega
  rw [hlen]
  rw [Finset.sum_range_add f p (r + 1)]
  have hp_split : (r + 1) + (p - (r + 1)) = p := by omega
  have hsplit_sum : (∑ x ∈ Finset.range p, f x) =
      (∑ x ∈ Finset.range (r + 1), f x) +
        (∑ x ∈ Finset.range (p - (r + 1)), f (r + 1 + x)) := by
    simpa [hp_split] using (Finset.sum_range_add f (r + 1) (p - (r + 1)))
  rw [hsplit_sum]
  have hmid : (∑ x ∈ Finset.range (p - (r + 1)), f (r + 1 + x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    dsimp [f]
    apply c_p_add_middle_term_zero p r (r + 1 + x) (by omega) (by omega)
    have hxlt : x < p - (r + 1) := by simpa using hx
    omega
  have hhigh : (∑ x ∈ Finset.range (r + 1), f (p + x)) = - (∑ x ∈ Finset.range (r + 1), f x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hxle : x ≤ r := by
      have : x < r + 1 := by simpa using hx
      omega
    dsimp [f]
    exact c_p_add_pair_term p r x hpodd (by omega) hxle
  rw [hmid, hhigh]
  abel

lemma c_p_sub_one_cast (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    let m := (p - 1) / 2
    (c (p - 1) : ZMod p) = (-1 : ZMod p) ^ m := by
  intro m
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hpodd
  have h2m : 2 * m = p - 1 := by
    subst m
    rcases hodd with ⟨q, hq⟩
    rw [hq]
    simp
  have hmp : m < p := by omega
  unfold c
  have hlen : p - 1 + 1 = p := Nat.sub_one_add_one hp0.ne'
  rw [hlen]
  rw [Int.cast_sum]
  trans (∑ k ∈ range p, if k = m then (-1 : ZMod p) ^ m else 0)
  · apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < p := by simpa using hk
    by_cases hkm : k = m
    · subst k
      simp only [if_true]
      rw [int_cast_c_term]
      have hnmk : p - 1 - m = m := by omega
      rw [hnmk, h2m]
      rw [choose_p_sub_one_cast p m hmp]
      have s2 : (((-1 : ZMod p) ^ m) ^ 2) = 1 := by
        rw [← pow_mul]
        exact Even.neg_one_pow (show Even (m * 2) from ⟨m, by ring⟩)
      rw [s2]
      simpa [pow_two] using s2
    · simp only [hkm, if_false]
      rw [int_cast_c_term]
      rcases lt_or_gt_of_ne hkm with hlt | hgt
      · -- k < m: the right central binomial coefficient vanishes
        let t := p - 1 - k
        have htltp : t < p := by dsimp [t]; omega
        have hlarge : p ≤ 2 * t := by dsimp [t]; omega
        have hz : ((Nat.choose (2 * t) t : ℕ) : ZMod p) = 0 :=
          choose_two_mul_cast_eq_zero_of_large p t htltp hlarge
        have htdef : t = p - 1 - k := rfl
        rw [← htdef]
        rw [hz]
        ring
      · -- m < k: the left central binomial coefficient vanishes
        have hlarge : p ≤ 2 * k := by omega
        have hz : ((Nat.choose (2 * k) k : ℕ) : ZMod p) = 0 :=
          choose_two_mul_cast_eq_zero_of_large p k hklt hlarge
        rw [hz]
        ring
  · rw [Finset.sum_eq_single_of_mem m (by simpa using hmp)]
    · simp
    · intro b hb hbm
      simp [hbm]

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
  letI : Fact p.Prime := ⟨hp⟩
  dsimp only
  let A : Matrix (Fin p) (Fin p) ℤ := fun i j => a (i.val + j.val)
  let C : Matrix (Fin p) (Fin p) ℤ := fun i j => c (i.val + j.val)
  let Az : Matrix (Fin p) (Fin p) (ZMod p) := fun i j => (a (i.val + j.val) : ZMod p)
  let Cz : Matrix (Fin p) (Fin p) (ZMod p) := fun i j => (c (i.val + j.val) : ZMod p)
  have hp_pos : 0 < p := hp.pos
  have hp_odd : Odd p := hp.odd_of_ne_two h_odd
  have hA_zero : ∀ i j : Fin p, p ≤ i.val + j.val → Az i j = 0 := by
    intro i j hij
    dsimp [Az]
    let r := i.val + j.val - p
    have hsum_le : i.val + j.val ≤ 2 * p - 2 := by omega
    have hr : r + 1 < p := by dsimp [r]; omega
    have hsum : p + r = i.val + j.val := by dsimp [r]; omega
    rw [← hsum]
    exact a_p_add_cast p r h_odd hr
  have hA_diag : ∀ i j : Fin p, i.val + j.val = p - 1 → Az i j = (1 : ZMod p) := by
    intro i j hij
    dsimp [Az]
    rw [hij]
    exact a_p_sub_one_cast p h_odd
  have hC_zero : ∀ i j : Fin p, p ≤ i.val + j.val → Cz i j = 0 := by
    intro i j hij
    dsimp [Cz]
    let r := i.val + j.val - p
    have hsum_le : i.val + j.val ≤ 2 * p - 2 := by omega
    have hr : r + 1 < p := by dsimp [r]; omega
    have hsum : p + r = i.val + j.val := by dsimp [r]; omega
    rw [← hsum]
    exact c_p_add_cast p r h_odd hr
  have hC_diag : ∀ i j : Fin p, i.val + j.val = p - 1 → Cz i j = ((-1 : ZMod p) ^ ((p - 1) / 2)) := by
    intro i j hij
    dsimp [Cz]
    rw [hij]
    exact c_p_sub_one_cast p h_odd
  have hsign_exp : (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin p)) : ℤ) : ZMod p)) =
      (-1 : ZMod p) ^ ((p - 1) / 2) := by
    rw [sign_revPerm]
    norm_num
    rcases hp_odd with ⟨m, hm⟩
    have hmhalf : (p - 1) / 2 = m := by
      rw [hm]
      simp
    have hexp : p * (p - 1) / 2 = p * m := by
      rw [hm]
      have hsub : 2 * m + 1 - 1 = 2 * m := by omega
      rw [hsub]
      rw [show (2 * m + 1) * (2 * m) = ((2 * m + 1) * m) * 2 by ring]
      rw [Nat.mul_comm ((2 * m + 1) * m) 2]
      exact Nat.mul_div_right ((2 * m + 1) * m) (by norm_num : 0 < 2)
    rw [hexp, hmhalf, pow_mul]
    have hpown : (-1 : ZMod p) ^ p = -1 := (show Odd p from ⟨m, hm⟩).neg_one_pow
    rw [hpown]
  have hdetAz : Az.det = (-1 : ZMod p) ^ ((p - 1) / 2) := by
    have h := det_of_antidiagonal_mod Az (1 : ZMod p) hA_zero hA_diag
    rw [h, hsign_exp]
    simp
  have hdetCz : Cz.det = (1 : ZMod p) := by
    have h := det_of_antidiagonal_mod Cz ((-1 : ZMod p) ^ ((p - 1) / 2)) hC_zero hC_diag
    rw [h, hsign_exp]
    rcases hp_odd with ⟨m, hm⟩
    have hmhalf : (p - 1) / 2 = m := by
      rw [hm]
      simp
    rw [hmhalf]
    have hpown : (-1 : ZMod p) ^ p = -1 := (show Odd p from ⟨m, hm⟩).neg_one_pow
    rw [← pow_mul, mul_comm m p, pow_mul, hpown]
    have : ((-1 : ZMod p) ^ m) * ((-1 : ZMod p) ^ m) = 1 := by
      rw [← pow_add, ← two_mul]
      exact Even.neg_one_pow ⟨m, by ring⟩
    exact this
  have hmapA : ((Matrix.det A : ℤ) : ZMod p) = Az.det := by
    simpa [A, Az] using (Int.castRingHom (ZMod p)).map_det A
  have hmapC : ((Matrix.det C : ℤ) : ZMod p) = Cz.det := by
    simpa [C, Cz] using (Int.castRingHom (ZMod p)).map_det C
  constructor
  · rw [← ZMod.intCast_eq_intCast_iff]
    calc
      ((Matrix.det A : ℤ) : ZMod p) = Az.det := hmapA
      _ = (-1 : ZMod p) ^ ((p - 1) / 2) := hdetAz
      _ = (((-1 : ℤ) ^ ((p - 1) / 2) : ℤ) : ZMod p) := by norm_num
  · rw [← ZMod.intCast_eq_intCast_iff]
    calc
      ((Matrix.det C : ℤ) : ZMod p) = Cz.det := hmapC
      _ = 1 := hdetCz
      _ = ((1 : ℤ) : ZMod p) := by norm_num
