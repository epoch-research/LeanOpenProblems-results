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

namespace OEIS228304

/- ### Powers of `-1` -/

private lemma neg_one_pow_congr {M : Type*} [Monoid M] [HasDistribNeg M] {s t : ℕ}
    (h : s % 2 = t % 2) : (-1 : M) ^ s = (-1 : M) ^ t := by
  conv_lhs => rw [← Nat.div_add_mod s 2]
  conv_rhs => rw [← Nat.div_add_mod t 2]
  rw [pow_add, pow_add, pow_mul, pow_mul, neg_one_sq, one_pow, one_pow, h]

private lemma neg_one_pow_mul_self {R : Type*} [Monoid R] [HasDistribNeg R] (k : ℕ) :
    (-1 : R) ^ k * (-1 : R) ^ k = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/- ### The sign of the reversal permutation -/

private lemma revPerm_succ (n : ℕ) :
    (Fin.revPerm : Equiv.Perm (Fin (n + 1))) =
      finRotate (n + 1) *
        (finSuccEquivLast.symm.permCongr
          (Equiv.optionCongr (Fin.revPerm : Equiv.Perm (Fin n)))) := by
  apply Equiv.ext
  intro i
  induction i using Fin.lastCases with
  | last =>
    simp [Equiv.Perm.mul_apply, Equiv.permCongr_apply, Fin.rev_last]
  | cast j =>
    simp [Equiv.Perm.mul_apply, Equiv.permCongr_apply, Fin.rev_castSucc,
      Fin.coeSucc_eq_succ]

private lemma sign_revPerm (n : ℕ) :
    Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) = (-1) ^ (n / 2) := by
  induction n with
  | zero =>
    have h : (Fin.revPerm : Equiv.Perm (Fin 0)) = 1 := by
      apply Equiv.ext; intro i; exact i.elim0
    simp [h]
  | succ n ih =>
    rw [revPerm_succ, map_mul, sign_finRotate, Equiv.Perm.sign_permCongr,
      Equiv.optionCongr_sign, ih]
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [show (m + m) / 2 = m from by omega, show (m + m + 1) / 2 = m from by omega,
        Even.neg_one_pow ⟨m, rfl⟩, one_mul]
    · rw [show (2 * m + 1) / 2 = m from by omega,
        show (2 * m + 1 + 1) / 2 = m + 1 from by omega,
        Odd.neg_one_pow ⟨m, rfl⟩, pow_succ]
      exact mul_comm _ _

/- ### Determinants of anti-triangular matrices -/

private lemma det_antitriangular {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j : Fin n, n ≤ (i : ℕ) + (j : ℕ) → M i j = 0) :
    M.det = (-1 : R) ^ (n / 2) * ∏ i : Fin n, M i i.rev := by
  have htri : (M.submatrix id (Fin.revPerm : Equiv.Perm (Fin n))).BlockTriangular id := by
    intro i j hij
    have hj : (j : ℕ) < (i : ℕ) := hij
    have hi := i.isLt
    have hjlt := j.isLt
    show M i j.rev = 0
    refine h i j.rev ?_
    rw [Fin.val_rev]
    omega
  have hperm := Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin n)) M
  have hdiag := Matrix.det_of_upperTriangular htri
  rw [hdiag, sign_revPerm] at hperm
  have hprod : ∏ i : Fin n, (M.submatrix id (Fin.revPerm : Equiv.Perm (Fin n))) i i
      = ∏ i : Fin n, M i i.rev := by
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [Matrix.submatrix_apply]
  rw [hprod] at hperm
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Int.cast_pow,
    Int.cast_neg, Int.cast_one] at hperm
  calc M.det = ((-1 : R) ^ (n / 2) * (-1 : R) ^ (n / 2)) * M.det := by
        rw [neg_one_pow_mul_self, one_mul]
    _ = (-1 : R) ^ (n / 2) * ((-1 : R) ^ (n / 2) * M.det) := by rw [mul_assoc]
    _ = (-1 : R) ^ (n / 2) * ∏ i : Fin n, M i i.rev := by rw [← hperm]

/- ### Binomial coefficients modulo `p` -/

section ModP

variable {p : ℕ} [Fact p.Prime]

private lemma cast_lucas (n k : ℕ) :
    ((n.choose k : ℕ) : ZMod p) =
      (((n % p).choose (k % p) : ℕ) : ZMod p) * (((n / p).choose (k / p) : ℕ) : ZMod p) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := n) (k := k) (p := p)
  have h2 := (ZMod.intCast_eq_intCast_iff _ _ _).mpr h
  push_cast at h2
  exact h2

private lemma choose_add_left {r k : ℕ} (hr : r < p) (hk : k < p) :
    (((p + r).choose k : ℕ) : ZMod p) = ((r.choose k : ℕ) : ZMod p) := by
  have hppos : 0 < p := (Fact.out : p.Prime).pos
  have h1 : (p + r) % p = r := by
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt hr
  have h2 : (p + r) / p = 1 := by
    rw [Nat.add_div_left _ hppos, Nat.div_eq_of_lt hr]
  rw [cast_lucas (p + r) k, h1, h2, Nat.mod_eq_of_lt hk, Nat.div_eq_of_lt hk]
  simp

private lemma choose_add_add {r j : ℕ} (hr : r < p) (hj : j < p) :
    (((p + r).choose (p + j) : ℕ) : ZMod p) = ((r.choose j : ℕ) : ZMod p) := by
  have hppos : 0 < p := (Fact.out : p.Prime).pos
  have h1 : (p + r) % p = r := by
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt hr
  have h2 : (p + r) / p = 1 := by
    rw [Nat.add_div_left _ hppos, Nat.div_eq_of_lt hr]
  have h3 : (p + j) % p = j := by
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt hj
  have h4 : (p + j) / p = 1 := by
    rw [Nat.add_div_left _ hppos, Nat.div_eq_of_lt hj]
  rw [cast_lucas (p + r) (p + j), h1, h2, h3, h4]
  simp

private lemma central_add {t : ℕ} (ht : t < p) :
    (((2 * (p + t)).choose (p + t) : ℕ) : ZMod p) = 2 * (((2 * t).choose t : ℕ) : ZMod p) := by
  have hppos : 0 < p := (Fact.out : p.Prime).pos
  have hpt_mod : (p + t) % p = t := by
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt ht
  have hpt_div : (p + t) / p = 1 := by
    rw [Nat.add_div_left _ hppos, Nat.div_eq_of_lt ht]
  rcases lt_or_ge (2 * t) p with h2t | h2t
  · have hmod : (2 * (p + t)) % p = 2 * t := by
      have e : 2 * (p + t) = 2 * t + p * 2 := by ring
      rw [e, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt h2t
    have hdiv : (2 * (p + t)) / p = 2 := by
      have e : 2 * (p + t) = 2 * t + p * 2 := by ring
      rw [e, Nat.add_mul_div_left _ _ hppos, Nat.div_eq_of_lt h2t]
    rw [cast_lucas (2 * (p + t)) (p + t), hmod, hdiv, hpt_mod, hpt_div,
      Nat.choose_one_right]
    push_cast
    ring
  · obtain ⟨u, hu⟩ : ∃ u, 2 * t = p + u := ⟨2 * t - p, by omega⟩
    have hut : u < t := by omega
    have hup : u < p := by omega
    have hmod : (2 * (p + t)) % p = u := by
      have e : 2 * (p + t) = u + p * 3 := by omega
      rw [e, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hup
    have hdiv : (2 * (p + t)) / p = 3 := by
      have e : 2 * (p + t) = u + p * 3 := by omega
      rw [e, Nat.add_mul_div_left _ _ hppos, Nat.div_eq_of_lt hup]
    have hmod2 : (2 * t) % p = u := by
      rw [hu, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt hup
    have hdiv2 : (2 * t) / p = 1 := by
      rw [hu, Nat.add_div_left _ hppos, Nat.div_eq_of_lt hup]
    rw [cast_lucas (2 * (p + t)) (p + t), hmod, hdiv, hpt_mod, hpt_div,
      cast_lucas (2 * t) t, hmod2, hdiv2, Nat.mod_eq_of_lt ht, Nat.div_eq_of_lt ht,
      Nat.choose_eq_zero_of_lt hut]
    simp

private lemma choose_p_sub_one_cast : ∀ {k : ℕ}, k < p →
    (((p - 1).choose k : ℕ) : ZMod p) = (-1 : ZMod p) ^ k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : k < p := by omega
    have hkey : (((p - 1).choose (k + 1) : ℕ) : ZMod p) * ((k : ZMod p) + 1)
        = (((p - 1).choose k : ℕ) : ZMod p) * (((p - 1 - k : ℕ)) : ZMod p) := by
      have key := Nat.choose_succ_right_eq (p - 1) k
      exact_mod_cast congrArg (fun m : ℕ => (m : ZMod p)) key
    have hsub : (((p - 1 - k : ℕ)) : ZMod p) = -((k : ZMod p) + 1) := by
      have hadd : ((p - 1 - k) + (k + 1) : ℕ) = p := by omega
      have h2 := congrArg (fun m : ℕ => (m : ZMod p)) hadd
      simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at h2
      linear_combination h2
    rw [hsub, ih hk'] at hkey
    have hne : ((k : ZMod p) + 1) ≠ 0 := by
      intro h0
      have hlt : k + 1 < p := hk
      have hv := ZMod.val_cast_of_lt hlt
      have hcast : ((k + 1 : ℕ) : ZMod p) = (k : ZMod p) + 1 := by push_cast; ring
      rw [hcast, h0, ZMod.val_zero] at hv
      omega
    have hfin : (((p - 1).choose (k + 1) : ℕ) : ZMod p) * ((k : ZMod p) + 1)
        = (-1 : ZMod p) ^ (k + 1) * ((k : ZMod p) + 1) := by
      rw [hkey]; ring
    exact mul_right_cancel₀ hne hfin

private lemma central_cast_eq_zero {k : ℕ} (h1 : p ≤ 2 * k) (h2 : k < p) :
    (((2 * k).choose k : ℕ) : ZMod p) = 0 := by
  have hdvd : p ∣ (k + k).choose k :=
    (Fact.out : p.Prime).dvd_choose_add h2 h2 (by omega)
  rw [two_mul]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr hdvd

/- ### The sequences `a` and `c` modulo `p` -/

private lemma cast_a (n : ℕ) :
    ((a n : ℤ) : ZMod p) =
      ∑ k ∈ range (n + 1), (-1 : ZMod p) ^ k * ((n.choose k : ℕ) : ZMod p) ^ 4 := by
  unfold a
  push_cast
  rfl

private lemma cast_c (n : ℕ) :
    ((c n : ℤ) : ZMod p) =
      ∑ k ∈ range (n + 1), (-1 : ZMod p) ^ k * ((n.choose k : ℕ) : ZMod p) ^ 2
        * (((2 * k).choose k : ℕ) : ZMod p) * (((2 * (n - k)).choose (n - k) : ℕ) : ZMod p) := by
  unfold c
  push_cast
  rfl

private lemma cast_a_add (hodd : Odd p) {r : ℕ} (hr : r < p) :
    ((a (p + r) : ℤ) : ZMod p) = 0 := by
  rw [cast_a, show p + r + 1 = p + (r + 1) from by omega, Finset.sum_range_add]
  have h1 : ∀ k ∈ range p,
      (-1 : ZMod p) ^ k * (((p + r).choose k : ℕ) : ZMod p) ^ 4
        = (-1 : ZMod p) ^ k * ((r.choose k : ℕ) : ZMod p) ^ 4 := by
    intro k hk
    rw [choose_add_left hr (mem_range.mp hk)]
  have h2 : ∀ k ∈ range (r + 1),
      (-1 : ZMod p) ^ (p + k) * (((p + r).choose (p + k) : ℕ) : ZMod p) ^ 4
        = -((-1 : ZMod p) ^ k * ((r.choose k : ℕ) : ZMod p) ^ 4) := by
    intro k hk
    have hkp : k < p := by
      have := mem_range.mp hk; omega
    rw [choose_add_add hr hkp, pow_add, hodd.neg_one_pow]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_neg_distrib]
  have h3 : ∑ k ∈ range (r + 1), (-1 : ZMod p) ^ k * ((r.choose k : ℕ) : ZMod p) ^ 4
      = ∑ k ∈ range p, (-1 : ZMod p) ^ k * ((r.choose k : ℕ) : ZMod p) ^ 4 := by
    have hsubset : range (r + 1) ⊆ range p := by
      apply Finset.range_subset_range.mpr
      omega
    refine Finset.sum_subset hsubset ?_
    intro k hk hnk
    have hrk : r < k := by
      have h4 := mem_range.mp hk
      have h5 : ¬(k < r + 1) := fun hcon => hnk (mem_range.mpr hcon)
      omega
    rw [Nat.choose_eq_zero_of_lt hrk]
    simp
  rw [h3, add_neg_cancel]

private lemma cast_c_add (hodd : Odd p) {r : ℕ} (hr : r < p) :
    ((c (p + r) : ℤ) : ZMod p) = 0 := by
  rw [cast_c, show p + r + 1 = p + (r + 1) from by omega, Finset.sum_range_add]
  have h1 : ∀ k ∈ range p,
      (-1 : ZMod p) ^ k * (((p + r).choose k : ℕ) : ZMod p) ^ 2
          * (((2 * k).choose k : ℕ) : ZMod p)
          * (((2 * (p + r - k)).choose (p + r - k) : ℕ) : ZMod p)
        = 2 * ((-1 : ZMod p) ^ k * ((r.choose k : ℕ) : ZMod p) ^ 2
          * (((2 * k).choose k : ℕ) : ZMod p)
          * (((2 * (r - k)).choose (r - k) : ℕ) : ZMod p)) := by
    intro k hk
    have hkp : k < p := mem_range.mp hk
    rw [choose_add_left hr hkp]
    by_cases hkr : k ≤ r
    · rw [show p + r - k = p + (r - k) from by omega, central_add (show r - k < p by omega)]
      ring
    · rw [Nat.choose_eq_zero_of_lt (show r < k by omega)]
      push_cast
      ring
  have h2 : ∀ k ∈ range (r + 1),
      (-1 : ZMod p) ^ (p + k) * (((p + r).choose (p + k) : ℕ) : ZMod p) ^ 2
          * (((2 * (p + k)).choose (p + k) : ℕ) : ZMod p)
          * (((2 * (p + r - (p + k))).choose (p + r - (p + k)) : ℕ) : ZMod p)
        = -(2 * ((-1 : ZMod p) ^ k * ((r.choose k : ℕ) : ZMod p) ^ 2
          * (((2 * k).choose k : ℕ) : ZMod p)
          * (((2 * (r - k)).choose (r - k) : ℕ) : ZMod p))) := by
    intro k hk
    have hkr : k ≤ r := by
      have := mem_range.mp hk; omega
    have hkp : k < p := by omega
    rw [show p + r - (p + k) = r - k from by omega, choose_add_add hr hkp,
      central_add hkp, pow_add, hodd.neg_one_pow]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_neg_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have h3 : ∑ k ∈ range (r + 1),
        (-1 : ZMod p) ^ k * ((r.choose k : ℕ) : ZMod p) ^ 2
          * (((2 * k).choose k : ℕ) : ZMod p)
          * (((2 * (r - k)).choose (r - k) : ℕ) : ZMod p)
      = ∑ k ∈ range p,
        (-1 : ZMod p) ^ k * ((r.choose k : ℕ) : ZMod p) ^ 2
          * (((2 * k).choose k : ℕ) : ZMod p)
          * (((2 * (r - k)).choose (r - k) : ℕ) : ZMod p) := by
    have hsubset : range (r + 1) ⊆ range p := by
      apply Finset.range_subset_range.mpr
      omega
    refine Finset.sum_subset hsubset ?_
    intro k hk hnk
    have hrk : r < k := by
      have h4 := mem_range.mp hk
      have h5 : ¬(k < r + 1) := fun hcon => hnk (mem_range.mpr hcon)
      omega
    rw [Nat.choose_eq_zero_of_lt hrk]
    push_cast
    ring
  rw [h3, add_neg_cancel]

private lemma cast_a_sub_one (hodd : Odd p) : ((a (p - 1) : ℤ) : ZMod p) = 1 := by
  have hppos : 0 < p := (Fact.out : p.Prime).pos
  rw [cast_a, show p - 1 + 1 = p from by omega]
  have h1 : ∀ k ∈ range p,
      (-1 : ZMod p) ^ k * (((p - 1).choose k : ℕ) : ZMod p) ^ 4 = (-1 : ZMod p) ^ k := by
    intro k hk
    rw [choose_p_sub_one_cast (mem_range.mp hk), ← pow_mul,
      neg_one_pow_congr (show k * 4 % 2 = 0 % 2 by omega), pow_zero, mul_one]
  rw [Finset.sum_congr rfl h1, neg_one_geom_sum, if_neg (Nat.not_even_iff_odd.mpr hodd)]

private lemma cast_c_sub_one (hodd : Odd p) :
    ((c (p - 1) : ℤ) : ZMod p) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
  obtain ⟨m, hm⟩ := hodd
  have hm2 : (p - 1) / 2 = m := by omega
  rw [cast_c, show p - 1 + 1 = p from by omega, hm2]
  have hmem : m ∈ range p := mem_range.mpr (by omega)
  have hzero : ∀ k ∈ range p, k ≠ m →
      (-1 : ZMod p) ^ k * (((p - 1).choose k : ℕ) : ZMod p) ^ 2
          * (((2 * k).choose k : ℕ) : ZMod p)
          * (((2 * (p - 1 - k)).choose (p - 1 - k) : ℕ) : ZMod p) = 0 := by
    intro k hk hkm
    have hkp : k < p := mem_range.mp hk
    rcases lt_or_gt_of_ne hkm with hlt | hgt
    · rw [central_cast_eq_zero (show p ≤ 2 * (p - 1 - k) by omega)
        (show p - 1 - k < p by omega), mul_zero]
    · rw [central_cast_eq_zero (show p ≤ 2 * k by omega) hkp]
      ring
  rw [Finset.sum_eq_single_of_mem m hmem hzero,
    show p - 1 - m = m from by omega, show 2 * m = p - 1 from by omega,
    choose_p_sub_one_cast (show m < p by omega)]
  rcases Nat.even_or_odd m with he | ho
  · rw [he.neg_one_pow]; norm_num
  · rw [ho.neg_one_pow]; norm_num

/- ### The Hankel determinant modulo `p` -/

private lemma det_hankel {p : ℕ} [Fact p.Prime] (hodd : Odd p) (f : ℕ → ℤ)
    (hvan : ∀ r : ℕ, r < p → ((f (p + r) : ℤ) : ZMod p) = 0) :
    (((Matrix.of fun i j : Fin p => f ((i : ℕ) + (j : ℕ))).det : ℤ) : ZMod p)
      = (-1 : ZMod p) ^ ((p - 1) / 2) * ((f (p - 1) : ℤ) : ZMod p) := by
  have hodd2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hppos : 0 < p := (Fact.out : p.Prime).pos
  rw [Int.cast_det]
  have hvan' : ∀ i j : Fin p, p ≤ (i : ℕ) + (j : ℕ) →
      ((Matrix.of fun i j : Fin p => f ((i : ℕ) + (j : ℕ))).map
        (fun x : ℤ => (x : ZMod p))) i j = 0 := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    show ((f ((i : ℕ) + (j : ℕ)) : ℤ) : ZMod p) = 0
    rw [show (i : ℕ) + (j : ℕ) = p + ((i : ℕ) + (j : ℕ) - p) from by omega]
    exact hvan _ (by omega)
  rw [det_antitriangular _ hvan']
  have hentry : ∀ i : Fin p,
      ((Matrix.of fun i j : Fin p => f ((i : ℕ) + (j : ℕ))).map
        (fun x : ℤ => (x : ZMod p))) i i.rev = ((f (p - 1) : ℤ) : ZMod p) := by
    intro i
    show ((f ((i : ℕ) + ((i.rev : Fin p) : ℕ)) : ℤ) : ZMod p) = _
    rw [show (i : ℕ) + ((i.rev : Fin p) : ℕ) = p - 1 from by
      have := i.isLt; rw [Fin.val_rev]; omega]
  rw [Finset.prod_congr rfl (fun i _ => hentry i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ZMod.pow_card, show p / 2 = (p - 1) / 2 from by omega]

end ModP

end OEIS228304

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
  have hodd : Odd p := hp.odd_of_ne_two h_odd
  constructor
  · show (Matrix.of fun i j : Fin p => a ((i : ℕ) + (j : ℕ))).det
      ≡ (-1 : ℤ) ^ ((p - 1) / 2) [ZMOD (p : ℤ)]
    rw [← ZMod.intCast_eq_intCast_iff]
    have h := OEIS228304.det_hankel hodd a (fun r hr => OEIS228304.cast_a_add hodd hr)
    rw [OEIS228304.cast_a_sub_one hodd, mul_one] at h
    rw [h]
    push_cast
    rfl
  · show (Matrix.of fun i j : Fin p => c ((i : ℕ) + (j : ℕ))).det
      ≡ 1 [ZMOD (p : ℤ)]
    rw [← ZMod.intCast_eq_intCast_iff]
    have h := OEIS228304.det_hankel hodd c (fun r hr => OEIS228304.cast_c_add hodd hr)
    rw [OEIS228304.cast_c_sub_one hodd, OEIS228304.neg_one_pow_mul_self] at h
    rw [h]
    push_cast
    rfl
