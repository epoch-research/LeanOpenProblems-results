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

lemma lucas (p n k : ℕ) [Fact p.Prime] :
    (n.choose k : ZMod p) = (n % p).choose (k % p) * ((n / p).choose (k / p) : ZMod p) := by
  have h := (Choose.choose_modEq_choose_mod_mul_choose_div (n := n) (k := k) (p := p))
  simpa using (ZMod.intCast_eq_intCast_iff _ _ _).mpr h

lemma choose_low (p r k : ℕ) [Fact p.Prime] (hr : r < p) (hk : k < p) :
    ((p + r).choose k : ZMod p) = (r.choose k : ZMod p) := by
  rw [lucas]
  simp [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hk,
    Nat.div_eq_of_lt hk]

lemma choose_high (p r k : ℕ) [Fact p.Prime] (hr : r < p) (hk : k < p) :
    ((p + r).choose (p + k) : ZMod p) = (r.choose k : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [lucas]
  simp [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hk,
    Nat.add_div_left, Nat.div_eq_of_lt hr, Nat.div_eq_of_lt hk, hp]

lemma central_zero (p k : ℕ) [Fact p.Prime] (hk : k < p) (h : p ≤ 2*k) :
    ((2*k).choose k : ZMod p) = 0 := by
  exact (ZMod.natCast_eq_zero_iff _ _).mpr ((Fact.out : p.Prime).dvd_choose hk (by omega) h)

lemma central_shift (p k : ℕ) [Fact p.Prime] (hk : k < p) :
    ((2*(p+k)).choose (p+k) : ZMod p) = 2 * ((2*k).choose k : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  by_cases h : 2*k < p
  · rw [lucas]
    have hmod : 2*(p+k) % p = 2*k := by
      rw [mul_add, mul_comm 2 p, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt h]
    have hdiv : 2*(p+k) / p = 2 := by
      rw [mul_add, mul_comm 2 p, Nat.mul_add_div hp, Nat.div_eq_of_lt h]
    have hmod' : (p+k) % p = k := by simp [Nat.mod_eq_of_lt hk]
    have hdiv' : (p+k) / p = 1 := by simp [Nat.add_div_left, hp, Nat.div_eq_of_lt hk]
    rw [hmod, hdiv, hmod', hdiv']; norm_num; ring
  · rw [central_zero p k hk (by omega), mul_zero, lucas]
    have hmod : 2*(p+k) % p = 2*k-p := by
      rw [mul_add, mul_comm 2 p, Nat.mul_add_mod_self_left, Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have hmod' : (p+k) % p = k := by simp [Nat.mod_eq_of_lt hk]
    rw [hmod, hmod', Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma choose_pred (p k : ℕ) [Fact p.Prime] (hk : k < p) :
    ((p-1).choose k : ZMod p) = (-1 : ZMod p)^k := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  induction k with
  | zero => simp
  | succ k ih =>
    have hz : (p.choose (k+1) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr ((Fact.out : p.Prime).dvd_choose_self (by omega) hk)
    have he : p = (p-1)+1 := by omega
    have hchoose : p.choose (k+1) = (p-1).choose k + (p-1).choose (k+1) := by
      conv_lhs => rw [he]
      exact Nat.choose_succ_succ' _ _
    rw [hchoose] at hz
    push_cast at hz
    rw [ih (by omega)] at hz
    rw [pow_succ]
    linear_combination hz



lemma sum_cancel (p r : ℕ) (hr : r < p) (f : ℕ → ZMod p)
    (hz : ∀ k, r < k → k < p → f k = 0)
    (hc : ∀ k, k ≤ r → f (p+k) = - f k) :
    ∑ k ∈ range (p+r+1), f k = 0 := by
  have hs : ∑ k ∈ range p, f k = ∑ k ∈ range (r+1), f k := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k hk hk'
    apply hz <;> simp only [mem_range] at hk hk' <;> omega
  rw [show p+r+1=p+(r+1) by omega, Finset.sum_range_add, hs]
  have he : ∑ k ∈ range (r+1), f (p+k) = -(∑ k ∈ range (r+1), f k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    exact hc k (by simpa only [mem_range, Nat.lt_succ_iff] using hk)
  rw [he, add_neg_cancel]

lemma a_zero (p r : ℕ) [Fact p.Prime] (ho : Odd p) (hr : r < p) :
    (a (p+r) : ZMod p) = 0 := by
  simp only [a, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast]
  apply sum_cancel p r hr
  · intro k hkr hkp
    rw [choose_low p r k hr hkp, Nat.choose_eq_zero_of_lt hkr]
    simp
  · intro k hk
    rw [choose_high p r k hr (by omega), choose_low p r k hr (by omega),
      pow_add, ho.neg_one_pow]
    ring

lemma c_zero (p r : ℕ) [Fact p.Prime] (ho : Odd p) (hr : r < p) :
    (c (p+r) : ZMod p) = 0 := by
  simp only [c, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast]
  apply sum_cancel p r hr
  · intro k hkr hkp
    rw [choose_low p r k hr hkp, Nat.choose_eq_zero_of_lt hkr]
    simp
  · intro k hk
    have hk' : k < p := by omega
    have hnk : p+r-k = p+(r-k) := by omega
    have hnk' : p+r-(p+k) = r-k := by omega
    rw [choose_high p r k hr hk', choose_low p r k hr hk', hnk, hnk',
      central_shift p k hk', central_shift p (r-k) (by omega),
      pow_add, ho.neg_one_pow]
    ring

lemma sign_sq {R : Type*} [CommRing R] (k : ℕ) : ((-1 : R)^k)^2 = 1 := by
  rw [← pow_mul, mul_comm k 2, pow_mul, neg_one_sq, one_pow]

lemma a_pred (p : ℕ) [Fact p.Prime] (ho : Odd p) : (a (p-1) : ZMod p) = 1 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  simp only [a, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast]
  rw [show p-1+1=p by omega]
  calc
    _ = ∑ k ∈ range p, (-1 : ZMod p)^k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [choose_pred p k (mem_range.mp hk)]
      have he : ((-1 : ZMod p)^k)^4 = 1 := by
        rw [show 4=2*2 by rfl, pow_mul, sign_sq, one_pow]
      rw [he, mul_one]
    _ = 1 := by rw [neg_one_geom_sum, if_neg (Nat.not_even_iff_odd.mpr ho)]

lemma c_pred (p : ℕ) [Fact p.Prime] (ho : Odd p) :
    (c (p-1) : ZMod p) = (-1 : ZMod p)^((p-1)/2) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨m, hm⟩ := ho
  have hhalf : (p-1)/2 = m := by omega
  have heven : p-1 = 2*m := by omega
  simp only [c, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast]
  rw [hhalf]
  rw [Finset.sum_eq_single m]
  · have hm' : m < p := by omega
    rw [show p-1-m=m by omega, ← heven, choose_pred p m hm', sign_sq, mul_one]
    calc
      _ = (-1 : ZMod p)^m * ((-1 : ZMod p)^m)^2 := by ring
      _ = _ := by rw [sign_sq, mul_one]
  · intro k hk hkm
    have hk' : k < p := by simp only [mem_range] at hk; omega
    by_cases h : m < k
    · rw [central_zero p k hk' (by omega)]
      ring
    · rw [central_zero p (p-1-k) (by omega) (by omega)]
      ring
  · intro hm'
    exfalso
    apply hm'
    simp only [mem_range]
    omega

lemma sign_rev (p : ℕ) (hp : Odd p) :
    Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin p)) = (-1)^((p-1)/2) := by
  classical
  obtain ⟨m, hm⟩ := hp
  have hpos : 0 < p := by omega
  have hp2 : (p-1)/2 < p := by omega
  have hmid : p-1 = 2*((p-1)/2) := by omega
  have hfix : Function.fixedPoints (Fin.revPerm : Equiv.Perm (Fin p)) =
      {⟨(p-1)/2, hp2⟩} := by
    ext i
    change i.rev = i ↔ i = ⟨(p-1)/2, hp2⟩
    simp only [Fin.ext_iff, Fin.val_rev]
    omega
  rw [Equiv.Perm.sign_of_pow_two_eq_one (by ext i; simp [pow_two, Fin.revPerm])]
  simp [hfix]

lemma det_hankel (p : ℕ) (hp : Odd p) (f : ℕ → ZMod p)
    (hz : ∀ n, p ≤ n → n ≤ 2*p-2 → f n = 0) :
    (Matrix.det (fun i j : Fin p => f (i.val+j.val))) =
      (-1 : ZMod p)^((p-1)/2) * (f (p-1))^p := by
  classical
  let M : Matrix (Fin p) (Fin p) (ZMod p) := fun i j => f (i.val+j.val)
  let B := M.submatrix id Fin.revPerm
  have hb : B.BlockTriangular id := by
    intro i j hij
    dsimp at hij
    dsimp [B, M, Fin.revPerm]
    apply hz <;> omega
  have hd : B.det = (f (p-1))^p := by
    rw [Matrix.det_of_upperTriangular hb]
    have he : ∀ i : Fin p, B i i = f (p-1) := by
      intro i
      dsimp [B, M, Fin.revPerm]
      congr 1
      omega
    simp_rw [he]
    simp
  have hd' : B.det = (-1 : ZMod p)^((p-1)/2) * M.det := by
    dsimp [B]
    rw [Matrix.det_permute', sign_rev p hp]
    simp
  change M.det = _
  rw [hd'] at hd
  calc
    M.det = (-1 : ZMod p)^((p-1)/2) *
        ((-1 : ZMod p)^((p-1)/2) * M.det) := by rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
    _ = _ := by rw [hd]
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
  letI : Fact p.Prime := ⟨hp⟩
  have ho : Odd p := hp.odd_of_ne_two h_odd
  have ha : ∀ n, p ≤ n → n ≤ 2*p-2 → (a n : ZMod p) = 0 := by
    intro n hn hn'
    have he : n = p+(n-p) := by omega
    rw [he]
    exact OEIS228304.a_zero p (n-p) ho (by have hp2 := hp.two_le; omega)
  have hc : ∀ n, p ≤ n → n ≤ 2*p-2 → (c n : ZMod p) = 0 := by
    intro n hn hn'
    have he : n = p+(n-p) := by omega
    rw [he]
    exact OEIS228304.c_zero p (n-p) ho (by have hp2 := hp.two_le; omega)
  dsimp only
  constructor
  · apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
    rw [Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_det]
    change (Matrix.det (fun i j : Fin p => (a (i.val+j.val) : ZMod p))) = _
    rw [OEIS228304.det_hankel p ho _ ha, OEIS228304.a_pred p ho, one_pow, mul_one]
  · apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
    rw [Int.cast_one, Int.cast_det]
    change (Matrix.det (fun i j : Fin p => (c (i.val+j.val) : ZMod p))) = _
    rw [OEIS228304.det_hankel p ho _ hc, ZMod.pow_card, OEIS228304.c_pred p ho,
      ← pow_two, OEIS228304.sign_sq]

theorem oeis_228304_conjecture_0.disproof : ¬ (type_of% @oeis_228304_conjecture_0) := sorry
