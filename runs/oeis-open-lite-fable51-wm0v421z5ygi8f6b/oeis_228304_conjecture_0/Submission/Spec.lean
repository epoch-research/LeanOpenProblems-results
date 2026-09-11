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


theorem sign_revPerm_eq (n : ℕ) :
    Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) = (-1) ^ (n.choose 2) := by
  induction n with
  | zero =>
    have : (Fin.revPerm : Equiv.Perm (Fin 0)) = 1 := Subsingleton.elim _ _
    rw [this]; simp
  | succ n ih =>
    have key : (Fin.revPerm : Equiv.Perm (Fin (n+1))) =
        finRotate (n+1) * (Fin.revPerm : Equiv.Perm (Fin n)).extendDomain
          (finSuccAboveEquiv (Fin.last n)) := by
      ext i : 1
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [Equiv.Perm.mul_apply, Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp),
          finRotate_last, Fin.revPerm_apply, Fin.rev_last]
      · have h1 : ∀ k : Fin n, ((finSuccAboveEquiv (Fin.last n)) k : Fin (n+1)) = Fin.castSucc k := by
          intro k
          rw [finSuccAboveEquiv_apply]
          exact congrFun Fin.succAbove_last k
        rw [Equiv.Perm.mul_apply, ← h1, Equiv.Perm.extendDomain_apply_image, h1, h1,
          Fin.revPerm_apply, Fin.revPerm_apply, Fin.rev_castSucc]
        simp
    rw [key, Equiv.Perm.sign_mul, sign_finRotate, Equiv.Perm.sign_extendDomain, ih]
    have : (n+1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    rw [this, pow_add]

theorem det_antidiag {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j : Fin n, n ≤ i.val + j.val → M i j = 0) :
    M.det = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : R) * ∏ i, M i (Fin.rev i) := by
  have h1 : (M.submatrix id Fin.revPerm).det =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : R) * M.det :=
    Matrix.det_permute' _ _
  have h2 : (M.submatrix id Fin.revPerm).det = ∏ i, M i (Fin.rev i) := by
    rw [Matrix.det_of_upperTriangular]
    · rfl
    · intro i j hij
      apply h
      change j < i at hij
      show n ≤ (i : ℕ) + (Fin.rev j : ℕ)
      rw [Fin.val_rev]
      have := Fin.lt_def.mp hij
      omega
  have h3 : ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : R) *
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : R) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  calc M.det = (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : R) *
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : R)) * M.det := by rw [h3, one_mul]
    _ = _ := by rw [mul_assoc, ← h1, h2]

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem lucas_zmod (n k : ℕ) :
    ((n.choose k : ℕ) : ZMod p) = ((n % p).choose (k % p) : ℕ) * ((n / p).choose (k / p) : ℕ) := by
  have h := (ZMod.intCast_eq_intCast_iff _ _ p).mpr
    (Choose.choose_modEq_choose_mod_mul_choose_div (n := n) (k := k) (p := p))
  push_cast at h
  exact_mod_cast h

theorem choose_p_add_lt (m k : ℕ) (hm : m < p) (hk : k < p) :
    (((p + m).choose k : ℕ) : ZMod p) = (m.choose k : ℕ) := by
  rw [lucas_zmod]
  have h1 : (p + m) % p = m := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hm]
  have h2 : (p + m) / p = 1 := by
    rw [Nat.add_div_left _ hp.out.pos, Nat.div_eq_of_lt hm]
  rw [h1, h2, Nat.mod_eq_of_lt hk, Nat.div_eq_of_lt hk]; simp

theorem choose_p_add_p_add (m k : ℕ) (hm : m < p) (hk : k < p) :
    (((p + m).choose (p + k) : ℕ) : ZMod p) = (m.choose k : ℕ) := by
  rw [lucas_zmod]
  have h1 : (p + m) % p = m := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hm]
  have h2 : (p + m) / p = 1 := by
    rw [Nat.add_div_left _ hp.out.pos, Nat.div_eq_of_lt hm]
  have h3 : (p + k) % p = k := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hk]
  have h4 : (p + k) / p = 1 := by
    rw [Nat.add_div_left _ hp.out.pos, Nat.div_eq_of_lt hk]
  rw [h1, h2, h3, h4]; simp

theorem central_zero (k : ℕ) (hk : k < p) (h2k : p ≤ 2 * k) :
    (((2 * k).choose k : ℕ) : ZMod p) = 0 := by
  rw [ZMod.natCast_eq_zero_iff, two_mul]
  exact hp.out.dvd_choose_add hk hk (by omega)

theorem central_p_add (r : ℕ) (hr : r < p) :
    (((2 * (p + r)).choose (p + r) : ℕ) : ZMod p) = 2 * ((2 * r).choose r : ℕ) := by
  have hpr1 : (p + r) % p = r := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hr]
  have hpr2 : (p + r) / p = 1 := by
    rw [Nat.add_div_left _ hp.out.pos, Nat.div_eq_of_lt hr]
  rcases Nat.lt_or_ge (2 * r) p with h | h
  · rw [lucas_zmod]
    have e : 2 * (p + r) = 2 * r + p * 2 := by ring
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h, Nat.add_mul_div_left _ _ hp.out.pos,
      Nat.div_eq_of_lt h, hpr1, hpr2]
    simp [mul_comm]
  · rw [lucas_zmod, central_zero r hr h]
    have e : 2 * (p + r) = (2 * r - p) + p * 3 := by omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega), Nat.add_mul_div_left _ _ hp.out.pos,
      Nat.div_eq_of_lt (by omega), hpr1, hpr2, Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem choose_p_sub_one (k : ℕ) (hk : k ≤ p - 1) :
    (((p - 1).choose k : ℕ) : ZMod p) = (-1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (p - 1).choose k + (p - 1).choose (k + 1) = p.choose (k + 1) := by
      rw [← Nat.choose_succ_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hp.out.pos]
    have h2 : ((p.choose (k + 1) : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact hp.out.dvd_choose_self (Nat.succ_ne_zero k) (by omega)
    have h3 := congrArg (fun x : ℕ => (x : ZMod p)) h1
    simp only [Nat.cast_add] at h3
    rw [h2, ih (by omega)] at h3
    rw [pow_succ]
    linear_combination h3

theorem a_cast (n : ℕ) : ((a n : ℤ) : ZMod p) =
    ∑ k ∈ range (n + 1), (-1 : ZMod p) ^ k * ((n.choose k : ℕ) : ZMod p) ^ 4 := by
  unfold a; push_cast; rfl

theorem c_cast (n : ℕ) : ((c n : ℤ) : ZMod p) =
    ∑ k ∈ range (n + 1), (-1 : ZMod p) ^ k * ((n.choose k : ℕ) : ZMod p) ^ 2 *
      (((2 * k).choose k : ℕ) : ZMod p) * (((2 * (n - k)).choose (n - k) : ℕ) : ZMod p) := by
  unfold c; push_cast; rfl

theorem a_vanish (hodd : Odd p) (m : ℕ) (hm : m + 1 < p) : ((a (p + m) : ℤ) : ZMod p) = 0 := by
  rw [a_cast, show p + m + 1 = p + (m + 1) by ring, Finset.sum_range_add]
  have e1 : ∀ k ∈ range p, (-1 : ZMod p) ^ k * (((p + m).choose k : ℕ) : ZMod p) ^ 4
      = (-1) ^ k * ((m.choose k : ℕ) : ZMod p) ^ 4 := by
    intro k hk
    rw [choose_p_add_lt m k (by omega) (mem_range.mp hk)]
  have e2 : ∀ k ∈ range (m + 1), (-1 : ZMod p) ^ (p + k) * (((p + m).choose (p + k) : ℕ) : ZMod p) ^ 4
      = -((-1) ^ k * ((m.choose k : ℕ) : ZMod p) ^ 4) := by
    intro k hk
    have := mem_range.mp hk
    rw [choose_p_add_p_add m k (by omega) (by omega), pow_add, hodd.neg_one_pow]
    ring
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_neg_distrib]
  have e3 : ∑ k ∈ range p, (-1 : ZMod p) ^ k * ((m.choose k : ℕ) : ZMod p) ^ 4
      = ∑ k ∈ range (m + 1), (-1 : ZMod p) ^ k * ((m.choose k : ℕ) : ZMod p) ^ 4 := by
    refine (Finset.sum_subset (Finset.range_subset_range.mpr (by omega : m + 1 ≤ p)) ?_).symm
    intro k hk hk'
    simp only [mem_range] at hk hk'
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [e3, add_neg_cancel]

theorem c_vanish (hodd : Odd p) (m : ℕ) (hm : m + 1 < p) : ((c (p + m) : ℤ) : ZMod p) = 0 := by
  rw [c_cast, show p + m + 1 = p + (m + 1) by ring, Finset.sum_range_add]
  set g : ℕ → ZMod p := fun k => (-1) ^ k * ((m.choose k : ℕ) : ZMod p) ^ 2 *
      (((2 * k).choose k : ℕ) : ZMod p) * (2 * (((2 * (m - k)).choose (m - k) : ℕ) : ZMod p)) with hg
  have e1 : ∀ k ∈ range p, (-1 : ZMod p) ^ k * (((p + m).choose k : ℕ) : ZMod p) ^ 2 *
      (((2 * k).choose k : ℕ) : ZMod p) * (((2 * (p + m - k)).choose (p + m - k) : ℕ) : ZMod p)
      = g k := by
    intro k hk
    simp only [hg]
    rw [choose_p_add_lt m k (by omega) (mem_range.mp hk)]
    rcases Nat.lt_or_ge m k with h | h
    · rw [Nat.choose_eq_zero_of_lt h]; simp
    · rw [show p + m - k = p + (m - k) by omega, central_p_add (m - k) (by omega)]
  have e2 : ∀ k ∈ range (m + 1), (-1 : ZMod p) ^ (p + k) * (((p + m).choose (p + k) : ℕ) : ZMod p) ^ 2 *
      (((2 * (p + k)).choose (p + k) : ℕ) : ZMod p) *
      (((2 * (p + m - (p + k))).choose (p + m - (p + k)) : ℕ) : ZMod p)
      = -(g k) := by
    intro k hk
    have := mem_range.mp hk
    simp only [hg]
    rw [choose_p_add_p_add m k (by omega) (by omega), central_p_add k (by omega),
      show p + m - (p + k) = m - k by omega, pow_add, hodd.neg_one_pow]
    ring
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_neg_distrib]
  have e3 : ∑ k ∈ range p, g k = ∑ k ∈ range (m + 1), g k := by
    refine (Finset.sum_subset (Finset.range_subset_range.mpr (by omega : m + 1 ≤ p)) ?_).symm
    intro k hk hk'
    simp only [mem_range] at hk hk'
    simp only [hg]
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [e3, add_neg_cancel]

theorem a_diag (hodd : Odd p) : ((a (p - 1) : ℤ) : ZMod p) = 1 := by
  rw [a_cast, Nat.sub_add_cancel hp.out.pos]
  have h4 : ∀ k : ℕ, ((-1 : ZMod p) ^ k) ^ 4 = 1 := by
    intro k; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [Finset.sum_congr rfl (fun k hk => by
    rw [choose_p_sub_one k (by have := mem_range.mp hk; omega), h4, mul_one])]
  rw [neg_one_geom_sum, if_neg (Nat.not_even_iff_odd.mpr hodd)]

theorem c_diag (hodd : Odd p) : ((c (p - 1) : ℤ) : ZMod p) = (-1) ^ ((p - 1) / 2) := by
  rw [c_cast, Nat.sub_add_cancel hp.out.pos]
  obtain ⟨h, hh⟩ := hodd
  have hp1 : (p - 1) / 2 = h := by omega
  rw [Finset.sum_eq_single h]
  · rw [choose_p_sub_one h (by omega), show p - 1 - h = h by omega, show 2 * h = p - 1 by omega,
      choose_p_sub_one h (by omega), hp1]
    have h2 : ((-1 : ZMod p) ^ h) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    linear_combination (((-1 : ZMod p) ^ h) ^ 3 + (-1) ^ h) * h2
  · intro k hk hkh
    have hk' := mem_range.mp hk
    rcases Nat.lt_or_ge k h with hlt | hge
    · rw [show 2 * (p - 1 - k) = 2 * (p - 1 - k) from rfl, central_zero (p - 1 - k) (by omega) (by omega)]
      simp
    · rw [central_zero k (by omega) (by omega)]
      simp
  · intro habs
    exact absurd (mem_range.mpr (by omega)) habs

end

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
  intro N h A C
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two h_odd
  have hsign : (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin p)) : ℤ)) : ZMod p) = (-1) ^ h := by
    rw [sign_revPerm_eq]
    push_cast
    have h2 : 2 ∣ p - 1 := by obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩
    rw [Nat.choose_two_right, Nat.mul_div_assoc _ h2, pow_mul, hodd.neg_one_pow]
  have hdiag : ∀ i : Fin p, (i : ℕ) + (Fin.rev i : ℕ) = p - 1 := by
    intro i; rw [Fin.val_rev]; omega
  have hvan : ∀ (f : ℕ → ℤ), (∀ m, m + 1 < p → ((f (p + m) : ℤ) : ZMod p) = 0) →
      ∀ i j : Fin p, p ≤ i.val + j.val → ((f (i.val + j.val) : ℤ) : ZMod p) = 0 := by
    intro f hf i j hij
    have := hf (i.val + j.val - p) (by omega)
    rwa [show p + (i.val + j.val - p) = i.val + j.val by omega] at this
  constructor
  · rw [← ZMod.intCast_eq_intCast_iff]
    have hmap : ((A.det : ℤ) : ZMod p) = (A.map (Int.cast : ℤ → ZMod p)).det :=
      RingHom.map_det (Int.castRingHom (ZMod p)) A
    rw [hmap, det_antidiag (A.map (Int.cast : ℤ → ZMod p))
      (fun i j hij => hvan a (a_vanish hodd) i j hij), hsign]
    have hprod : ∏ i : Fin p, (A.map (Int.cast : ℤ → ZMod p)) i (Fin.rev i)
        = ((a (p - 1) : ℤ) : ZMod p) ^ p := by
      calc ∏ i : Fin p, (A.map (Int.cast : ℤ → ZMod p)) i (Fin.rev i)
          = ∏ _i : Fin p, ((a (p - 1) : ℤ) : ZMod p) := by
            refine Finset.prod_congr rfl (fun i _ => ?_)
            show ((a ((i : ℕ) + (Fin.rev i : ℕ)) : ℤ) : ZMod p) = _
            rw [hdiag i]
        _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hprod, ZMod.pow_card, a_diag hodd, mul_one]
    push_cast
    rfl
  · rw [← ZMod.intCast_eq_intCast_iff]
    have hmap : ((C.det : ℤ) : ZMod p) = (C.map (Int.cast : ℤ → ZMod p)).det :=
      RingHom.map_det (Int.castRingHom (ZMod p)) C
    rw [hmap, det_antidiag (C.map (Int.cast : ℤ → ZMod p))
      (fun i j hij => hvan c (c_vanish hodd) i j hij), hsign]
    have hprod : ∏ i : Fin p, (C.map (Int.cast : ℤ → ZMod p)) i (Fin.rev i)
        = ((c (p - 1) : ℤ) : ZMod p) ^ p := by
      calc ∏ i : Fin p, (C.map (Int.cast : ℤ → ZMod p)) i (Fin.rev i)
          = ∏ _i : Fin p, ((c (p - 1) : ℤ) : ZMod p) := by
            refine Finset.prod_congr rfl (fun i _ => ?_)
            show ((c ((i : ℕ) + (Fin.rev i : ℕ)) : ℤ) : ZMod p) = _
            rw [hdiag i]
        _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hprod, ZMod.pow_card, c_diag hodd, ← sq, ← pow_mul, mul_comm, pow_mul]
    push_cast
    norm_num

theorem oeis_228304_conjecture_0.disproof : ¬ (type_of% @oeis_228304_conjecture_0) := sorry