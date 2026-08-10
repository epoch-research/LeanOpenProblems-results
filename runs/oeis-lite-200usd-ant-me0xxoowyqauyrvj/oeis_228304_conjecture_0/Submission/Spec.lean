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

open Equiv Equiv.Perm

/-- For `n ≥ 2`, the combinatorial sign `signAux` agrees with `Equiv.Perm.sign` on `Perm (Fin n)`.
-/
lemma signAux_eq_sign {n : ℕ} (hn : 2 ≤ n) (f : Perm (Fin n)) :
    Equiv.Perm.signAux f = Equiv.Perm.sign f := by
  have hsurj : Function.Surjective
      (MonoidHom.mk' (Equiv.Perm.signAux) Equiv.Perm.signAux_mul : Perm (Fin n) →* ℤˣ) := by
    intro u
    rcases Int.units_eq_one_or u with h | h
    · exact ⟨1, by simp [h, Equiv.Perm.signAux_one]⟩
    · refine ⟨Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩, ?_⟩
      show Equiv.Perm.signAux _ = u
      rw [h, Equiv.Perm.signAux_swap]
      simp [Fin.ext_iff]
  have hh := Equiv.Perm.eq_sign_of_surjective_hom hsurj
  exact DFunLike.congr_fun hh f

/-- The sign of the reversal permutation of `Fin n` is `(-1)^(n(n-1)/2)`. -/
lemma sign_revPerm {n : ℕ} (hn : 2 ≤ n) :
    Equiv.Perm.sign (Fin.revPerm : Perm (Fin n)) = (-1) ^ (n * (n - 1) / 2) := by
  rw [← signAux_eq_sign hn]
  unfold Equiv.Perm.signAux
  rw [Finset.prod_congr rfl (g := fun _ => (-1 : ℤˣ)) ?_]
  · rw [Finset.prod_const]
    congr 1
    rw [Equiv.Perm.finPairsLT, Finset.card_sigma]
    simp only [Finset.card_attachFin, Finset.card_range]
    rw [Fin.sum_univ_eq_sum_range (fun i => i) n]
    rw [← Finset.sum_range_id_mul_two n] at *
    omega
  · intro x hx
    rw [Equiv.Perm.mem_finPairsLT] at hx
    have : (Fin.revPerm : Perm (Fin n)) x.1 ≤ (Fin.revPerm : Perm (Fin n)) x.2 := by
      simp only [Fin.revPerm_apply]
      exact Fin.rev_le_rev.mpr (le_of_lt hx)
    rw [if_pos this]

variable {p : ℕ} [Fact p.Prime]

/-- Single-step Lucas in `ZMod p`. -/
lemma lucas_zmod (n k : ℕ) :
    (n.choose k : ZMod p)
      = ((n % p).choose (k % p) : ZMod p) * ((n / p).choose (k / p) : ZMod p) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := n) (k := k) (p := p)
  have h2 := (ZMod.intCast_eq_intCast_iff _ _ _).mpr h
  push_cast at h2
  exact_mod_cast h2

/-- `choose (p+m) k ≡ choose m k` for `k < p`, `m < p`. -/
lemma choose_low (m k : ℕ) (hm : m < p) (hk : k < p) :
    ((p+m).choose k : ZMod p) = (m.choose k : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [lucas_zmod]
  have e1 : (p+m) % p = m := by rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt hm
  have e2 : (p+m) / p = 1 := by
    rw [Nat.add_comm, Nat.add_div_right _ hp, Nat.div_eq_of_lt hm]
  have e3 : k % p = k := Nat.mod_eq_of_lt hk
  have e4 : k / p = 0 := Nat.div_eq_of_lt hk
  rw [e1, e2, e3, e4]
  simp

/-- `choose (p+m) (p+j) ≡ choose m j` for `j < p`, `m < p`. -/
lemma choose_high (m j : ℕ) (hm : m < p) (hj : j < p) :
    ((p+m).choose (p+j) : ZMod p) = (m.choose j : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [lucas_zmod]
  have e1 : (p+m) % p = m := by rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt hm
  have e2 : (p+m) / p = 1 := by
    rw [Nat.add_comm, Nat.add_div_right _ hp, Nat.div_eq_of_lt hm]
  have e3 : (p+j) % p = j := by rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt hj
  have e4 : (p+j) / p = 1 := by
    rw [Nat.add_comm, Nat.add_div_right _ hp, Nat.div_eq_of_lt hj]
  rw [e1, e2, e3, e4]
  simp

/-- Central binomial vanishes: `p ∣ choose (2k) k` for `p/2 < k < p`. -/
lemma ZV (k : ℕ) (h1 : p ≤ 2*k) (h2 : k < p) : ((2*k).choose k : ZMod p) = 0 := by
  rw [lucas_zmod]
  have hk_mod : k % p = k := Nat.mod_eq_of_lt h2
  have hk_div : k / p = 0 := Nat.div_eq_of_lt h2
  have e_mod : (2*k) % p = 2*k - p := by
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega : 2*k - p < p)]
  rw [hk_mod, hk_div, e_mod, Nat.choose_eq_zero_of_lt (by omega : 2*k - p < k)]
  simp

/-- `choose (2(p+r)) (p+r) ≡ 2 * choose (2r) r` for `r < p`. -/
lemma CB (r : ℕ) (hr : r < p) :
    ((2*(p+r)).choose (p+r) : ZMod p) = 2 * ((2*r).choose r : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [lucas_zmod]
  have hpr_mod : (p+r) % p = r := by rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt hr
  have hpr_div : (p+r) / p = 1 := by
    rw [Nat.add_comm, Nat.add_div_right _ hp, Nat.div_eq_of_lt hr]
  rw [hpr_mod, hpr_div]
  rcases lt_or_ge (2*r) p with h | h
  · have e_mod : (2*(p+r)) % p = 2*r := by
      have h3 : 2*(p+r) = 2*r + p*2 := by ring
      rw [h3, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
    have e_div : (2*(p+r)) / p = 2 := by
      have h3 : 2*(p+r) = 2*r + p*2 := by ring
      rw [h3, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt h]
    rw [e_mod, e_div]
    have : (Nat.choose 2 1 : ZMod p) = 2 := by norm_num
    rw [this]; ring
  · have e_mod : (2*(p+r)) % p = 2*r - p := by
      have h3 : 2*(p+r) = (2*r - p) + p*3 := by omega
      rw [h3, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : 2*r - p < p)]
    have e_div : (2*(p+r)) / p = 3 := by
      have h3 : 2*(p+r) = (2*r - p) + p*3 := by omega
      rw [h3, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega : 2*r - p < p)]
    rw [e_mod, e_div, Nat.choose_eq_zero_of_lt (by omega : 2*r - p < r), Nat.cast_zero,
      zero_mul, ZV r h hr, mul_zero]

/-- `choose (p-1) k ≡ (-1)^k` for `k < p`. -/
lemma PM : ∀ k, k < p → ((p-1).choose k : ZMod p) = (-1)^k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : k < p := by omega
    have hpp : (p-1)+1 = p := by have := (Fact.out : p.Prime).two_le; omega
    have pascal : (p.choose (k+1) : ZMod p)
        = ((p-1).choose k : ZMod p) + ((p-1).choose (k+1) : ZMod p) := by
      have hcss := Nat.choose_succ_succ' (p-1) k
      rw [hpp] at hcss
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) hcss
    have hzero : (p.choose (k+1) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact (Fact.out : p.Prime).dvd_choose_self (by omega) hk
    rw [hzero] at pascal
    have hneg : ((p-1).choose (k+1) : ZMod p) = -((p-1).choose k : ZMod p) := by
      linear_combination -pascal
    rw [hneg, ih hk', pow_succ]
    ring

/-- `a(p-1) ≡ 1 (mod p)`. -/
lemma a_value (hodd : Odd p) : ((a (p-1) : ℤ) : ZMod p) = 1 := by
  have hp2 := (Fact.out : p.Prime).two_le
  have hne : ¬ Even p := Nat.not_even_iff_odd.mpr hodd
  simp only [a]
  rw [show (p-1)+1 = p from by omega]
  push_cast
  rw [Finset.sum_congr rfl (g := fun k => ((-1:ZMod p))^k) (fun k hk => ?_)]
  · rw [neg_one_geom_sum, if_neg hne]
  · rw [Finset.mem_range] at hk
    rw [PM k hk]
    have h4 : ((-1:ZMod p)^k)^4 = 1 := by
      rw [← pow_mul]; exact Even.neg_one_pow ⟨2*k, by ring⟩
    rw [h4, mul_one]

/-- `c(p-1) ≡ (-1)^((p-1)/2) (mod p)`. -/
lemma c_value (hodd : Odd p) : ((c (p-1) : ℤ) : ZMod p) = (-1)^((p-1)/2) := by
  have hp2 := (Fact.out : p.Prime).two_le
  obtain ⟨t, ht⟩ := hodd
  set q := (p-1)/2 with hq
  have hq2 : 2 * q = p - 1 := by omega
  have hqp : q < p := by omega
  simp only [c]
  rw [show (p-1)+1 = p from by omega]
  push_cast
  rw [Finset.sum_eq_single q]
  · rw [PM q hqp]
    have hpk : p - 1 - q = q := by omega
    rw [hpk]
    rw [show 2 * q = p - 1 from hq2, PM q hqp]
    have ha2 : ((-1:ZMod p)^q)^2 = 1 := by
      rw [← pow_mul]; exact Even.neg_one_pow ⟨q, by ring⟩
    linear_combination (((-1:ZMod p)^q)^3 + (-1:ZMod p)^q) * ha2
  · intro k hkrange hkq
    rw [Finset.mem_range] at hkrange
    rcases lt_or_gt_of_ne hkq with hlt | hgt
    · have hzv : ((2 * (p - 1 - k)).choose (p - 1 - k) : ZMod p) = 0 :=
        ZV (p - 1 - k) (by omega) (by omega)
      rw [hzv]; ring
    · have hzv : ((2 * k).choose k : ZMod p) = 0 := ZV k (by omega) hkrange
      rw [hzv]; ring
  · intro hq_not
    rw [Finset.mem_range] at hq_not
    exact absurd hqp hq_not

/-- `a(p+m) ≡ 0 (mod p)` for `m+1 < p`. -/
lemma a_vanish (hodd : Odd p) (m : ℕ) (hm : m + 1 < p) : ((a (p+m) : ℤ) : ZMod p) = 0 := by
  have hmp : m < p := by omega
  simp only [a]
  rw [show (p+m)+1 = p + (m+1) from by ring]
  push_cast
  rw [Finset.sum_range_add]
  have part1 : (∑ x ∈ Finset.range p, (-1:ZMod p)^x * (↑((p+m).choose x))^4)
      = ∑ x ∈ Finset.range (m+1), (-1:ZMod p)^x * (↑(m.choose x))^4 := by
    have step1 : (∑ x ∈ Finset.range p, (-1:ZMod p)^x * (↑((p+m).choose x))^4)
        = ∑ x ∈ Finset.range p, (-1:ZMod p)^x * (↑(m.choose x))^4 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_range] at hx
      rw [choose_low m x hmp hx]
    rw [step1]
    symm
    have hsub : Finset.range (m+1) ⊆ Finset.range p := by
      intro y hy; rw [Finset.mem_range] at hy ⊢; omega
    apply Finset.sum_subset hsub
    intro x _ hxnot
    simp only [Finset.mem_range, not_lt] at hxnot
    rw [Nat.choose_eq_zero_of_lt (by omega : m < x)]
    simp
  have part2 : (∑ x ∈ Finset.range (m+1), (-1:ZMod p)^(p+x) * (↑((p+m).choose (p+x)))^4)
      = ∑ x ∈ Finset.range (m+1), -((-1:ZMod p)^x * (↑(m.choose x))^4) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    rw [choose_high m x hmp (by omega), pow_add, Odd.neg_one_pow hodd]
    ring
  rw [part1, part2, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro x _
  ring

/-- `c(p+m) ≡ 0 (mod p)` for `m+1 < p`. -/
lemma c_vanish (hodd : Odd p) (m : ℕ) (hm : m + 1 < p) : ((c (p+m) : ℤ) : ZMod p) = 0 := by
  have hmp : m < p := by omega
  simp only [c]
  rw [show (p+m)+1 = p + (m+1) from by ring]
  push_cast
  rw [Finset.sum_range_add]
  have part1 : (∑ x ∈ Finset.range p, (-1:ZMod p)^x * (↑((p+m).choose x))^2
        * (↑((2*x).choose x)) * (↑((2*(p+m-x)).choose (p+m-x))))
      = ∑ x ∈ Finset.range (m+1), (-1:ZMod p)^x * (↑(m.choose x))^2
        * (↑((2*x).choose x)) * (2 * ↑((2*(m-x)).choose (m-x))) := by
    have step1 : (∑ x ∈ Finset.range p, (-1:ZMod p)^x * (↑((p+m).choose x))^2
          * (↑((2*x).choose x)) * (↑((2*(p+m-x)).choose (p+m-x))))
        = ∑ x ∈ Finset.range p, (-1:ZMod p)^x * (↑(m.choose x))^2
          * (↑((2*x).choose x)) * (↑((2*(p+m-x)).choose (p+m-x))) := by
      apply Finset.sum_congr rfl
      intro x hx; rw [Finset.mem_range] at hx
      rw [choose_low m x hmp hx]
    rw [step1]
    have hsub : Finset.range (m+1) ⊆ Finset.range p := by
      intro y hy; rw [Finset.mem_range] at hy ⊢; omega
    rw [← Finset.sum_subset hsub ?_]
    · apply Finset.sum_congr rfl
      intro x hx; rw [Finset.mem_range] at hx
      rw [show p+m-x = p+(m-x) from by omega, CB (m-x) (by omega)]
    · intro x _ hxnot
      simp only [Finset.mem_range, not_lt] at hxnot
      rw [Nat.choose_eq_zero_of_lt (by omega : m < x)]; simp
  have part2 : (∑ x ∈ Finset.range (m+1), (-1:ZMod p)^(p+x) * (↑((p+m).choose (p+x)))^2
        * (↑((2*(p+x)).choose (p+x))) * (↑((2*(p+m-(p+x))).choose (p+m-(p+x)))))
      = ∑ x ∈ Finset.range (m+1), -((-1:ZMod p)^x * (↑(m.choose x))^2
        * (↑((2*x).choose x)) * (2 * ↑((2*(m-x)).choose (m-x)))) := by
    apply Finset.sum_congr rfl
    intro x hx; rw [Finset.mem_range] at hx
    rw [choose_high m x hmp (by omega), CB x (by omega), pow_add, Odd.neg_one_pow hodd,
      show p+m-(p+x) = m-x from by omega]
    ring
  rw [part1, part2, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro x _; ring

/-- Determinant of the anti-triangular Hankel matrix over `ZMod p`. -/
lemma det_formula (hodd : Odd p) (g : ℕ → ZMod p)
    (hvanish : ∀ n, p ≤ n → n ≤ 2*p-2 → g n = 0) :
    Matrix.det (fun i j : Fin p => g (i.val + j.val))
      = (-1:ZMod p)^((p-1)/2) * g (p-1) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  set M : Matrix (Fin p) (Fin p) (ZMod p) := fun i j => g (i.val + j.val) with hM
  have hperm := Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin p)) M
  have hBT : (M.submatrix id (Fin.revPerm : Equiv.Perm (Fin p))).BlockTriangular id := by
    intro i j hij
    simp only [Matrix.submatrix_apply, id_eq, hM, Fin.revPerm_apply]
    apply hvanish
    · have hr : (Fin.rev j).val = p - 1 - j.val := by rw [Fin.val_rev]; omega
      rw [hr]; have := i.isLt; have := j.isLt; have : j.val < i.val := hij; omega
    · have hr : (Fin.rev j).val = p - 1 - j.val := by rw [Fin.val_rev]; omega
      rw [hr]; have := i.isLt; have := j.isLt; omega
  have hdetB : (M.submatrix id (Fin.revPerm : Equiv.Perm (Fin p))).det = g (p-1) ^ p := by
    rw [Matrix.det_of_upperTriangular hBT]
    have hpc : (∏ i : Fin p, (M.submatrix id (Fin.revPerm : Equiv.Perm (Fin p))) i i)
        = ∏ _i : Fin p, g (p-1) := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [Matrix.submatrix_apply, id_eq, hM, Fin.revPerm_apply]
      congr 1
      have hr : (Fin.rev i).val = p - 1 - i.val := by rw [Fin.val_rev]; omega
      rw [hr]; have := i.isLt; omega
    rw [hpc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hdetB, ZMod.pow_card] at hperm
  have hs : ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin p)) : ℤ) : ZMod p)
      = (-1:ZMod p)^((p-1)/2) := by
    rw [sign_revPerm hp2]
    have h2d : 2 ∣ (p-1) := by obtain ⟨t, ht⟩ := hodd; omega
    push_cast
    rw [Nat.mul_div_assoc p h2d, pow_mul, Odd.neg_one_pow hodd]
  rw [hs] at hperm
  have hw2 : ((-1:ZMod p)^((p-1)/2)) * ((-1:ZMod p)^((p-1)/2)) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨(p-1)/2, by ring⟩
  rw [hperm, ← mul_assoc, hw2, one_mul]

end OEIS228304

open OEIS228304

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
  have hp2 : 2 ≤ p := hp.two_le
  have hgA : ∀ n, p ≤ n → n ≤ 2*p-2 → (fun m => ((a m : ℤ) : ZMod p)) n = 0 := by
    intro n h1 h2
    obtain ⟨m, rfl⟩ : ∃ m, n = p + m := ⟨n - p, by omega⟩
    exact a_vanish hodd m (by omega)
  have hgC : ∀ n, p ≤ n → n ≤ 2*p-2 → (fun m => ((c m : ℤ) : ZMod p)) n = 0 := by
    intro n h1 h2
    obtain ⟨m, rfl⟩ : ∃ m, n = p + m := ⟨n - p, by omega⟩
    exact c_vanish hodd m (by omega)
  constructor
  · apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    rw [Int.cast_det]
    have hmat : (A.map (fun x => (x : ZMod p)))
        = (fun i j : Fin p => (fun m => ((a m : ℤ) : ZMod p)) (i.val + j.val)) := by
      funext i j; simp [Matrix.map_apply, A]
    rw [hmat, det_formula hodd _ hgA, a_value hodd, mul_one]
    push_cast
    rfl
  · apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    rw [Int.cast_det]
    have hmat : (C.map (fun x => (x : ZMod p)))
        = (fun i j : Fin p => (fun m => ((c m : ℤ) : ZMod p)) (i.val + j.val)) := by
      funext i j; simp [Matrix.map_apply, C]
    rw [hmat, det_formula hodd _ hgC, c_value hodd]
    rw [← pow_add]
    rw [Even.neg_one_pow ⟨(p-1)/2, by ring⟩]
    push_cast
    rfl
