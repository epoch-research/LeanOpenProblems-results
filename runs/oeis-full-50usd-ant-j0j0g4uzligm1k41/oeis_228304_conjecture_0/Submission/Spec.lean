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

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

/-- Single-step Lucas in `ZMod p`. -/
theorem luc (n k : ℕ) :
    (Nat.choose n k : ZMod p)
      = (Nat.choose (n % p) (k % p) : ZMod p) * (Nat.choose (n / p) (k / p) : ZMod p) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := p)
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  push_cast at this
  exact this

/-- `choose (p-1) k ≡ (-1)^k`. -/
theorem choose_pred (k : ℕ) (hk : k ≤ p - 1) :
    (Nat.choose (p - 1) k : ZMod p) = (-1) ^ k := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  induction k with
  | zero => simp
  | succ k ih =>
    have hkp : k + 1 < p := by omega
    have hk' : k ≤ p - 1 := by omega
    -- Pascal: p.choose (k+1) = (p-1).choose k + (p-1).choose (k+1)
    have hpas : Nat.choose p (k + 1)
        = Nat.choose (p - 1) k + Nat.choose (p - 1) (k + 1) := by
      have : p = (p - 1) + 1 := by omega
      rw [this, Nat.choose_succ_succ]
      simp
    have hdvd : (Nat.choose p (k + 1) : ZMod p) = 0 := by
      have : p ∣ Nat.choose p (k + 1) :=
        Nat.Prime.dvd_choose_self hp.out (by omega) hkp
      exact (ZMod.natCast_eq_zero_iff _ _).mpr this
    have hcast : (Nat.choose p (k + 1) : ZMod p)
        = (Nat.choose (p - 1) k : ZMod p) + (Nat.choose (p - 1) (k + 1) : ZMod p) := by
      rw [hpas]; push_cast; ring
    rw [hdvd] at hcast
    have : (Nat.choose (p - 1) (k + 1) : ZMod p) = - (Nat.choose (p - 1) k : ZMod p) :=
      eq_neg_of_add_eq_zero_right hcast.symm
    rw [this, ih hk', pow_succ]
    ring

/-- central binomial vanishes: `p ≤ 2k`, `k < p` ⟹ `choose (2k) k ≡ 0`. -/
theorem central_zero (k : ℕ) (hk : k < p) (h2 : p ≤ 2 * k) :
    (Nat.choose (2 * k) k : ZMod p) = 0 := by
  have hk0 : k % p = k := Nat.mod_eq_of_lt hk
  have hkd : k / p = 0 := Nat.div_eq_of_lt hk
  have hmod : (2 * k) % p = 2 * k - p := by
    conv_lhs => rw [show 2 * k = p + (2 * k - p) from by omega]
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hlt : (2 * k) % p < k := by omega
  rw [luc, hk0, hkd]
  rw [Nat.choose_eq_zero_of_lt hlt]
  simp

/-- helper: `(p + r) % p = r` and `(p + r) / p = 1` for `r < p`. -/
theorem pr_mod (r : ℕ) (h : r < p) : (p + r) % p = r := by
  rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt h

theorem pr_div (r : ℕ) (h : r < p) : (p + r) / p = 1 := by
  have hp0 : 0 < p := hp.out.pos
  rw [Nat.add_comm, Nat.add_div_right _ hp0, Nat.div_eq_of_lt h]

/-- shifted central binomial, small case `2r < p`: `choose (2(p+r)) (p+r) ≡ 2·choose (2r) r`. -/
theorem central_shift_small (r : ℕ) (h2r : 2 * r < p) :
    (Nat.choose (2 * (p + r)) (p + r) : ZMod p) = 2 * (Nat.choose (2 * r) r : ZMod p) := by
  have hp0 : 0 < p := hp.out.pos
  have hr : r < p := by omega
  have hm : (2 * (p + r)) % p = 2 * r := by
    have e : 2 * (p + r) = p + (p + 2 * r) := by ring
    rw [e, Nat.add_mod_left, Nat.add_mod_left]; exact Nat.mod_eq_of_lt h2r
  have hd : (2 * (p + r)) / p = 2 := by
    have e : 2 * (p + r) = 2 * r + p * 2 := by ring
    rw [e, Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt h2r]
  rw [luc, hm, hd, pr_mod r hr, pr_div r hr]
  -- choose 2 1 = 2
  norm_num [Nat.choose]
  ring

/-- shifted central binomial, large case `p ≤ 2r`, `r < p`: `choose (2(p+r)) (p+r) ≡ 0`. -/
theorem central_shift_zero (r : ℕ) (hr : r < p) (h2r : p ≤ 2 * r) :
    (Nat.choose (2 * (p + r)) (p + r) : ZMod p) = 0 := by
  have hp0 : 0 < p := hp.out.pos
  have hm : (2 * (p + r)) % p = 2 * r - p := by
    have e : 2 * (p + r) = (2 * r - p) + p * 3 := by omega
    rw [e, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [luc, hm, pr_mod r hr]
  rw [Nat.choose_eq_zero_of_lt (by omega : 2 * r - p < r)]
  simp

/-- The determinant of an anti-triangular Hankel matrix. -/
theorem hankel_antitri {R : Type*} [CommRing R] :
    ∀ (d : ℕ) (s : ℕ → R) (v : R), s d = v →
      (∀ x, d < x → x ≤ 2 * d → s x = 0) →
      Matrix.det (fun i j : Fin (d + 1) => s (i.val + j.val))
        = (-1) ^ (Nat.choose (d + 1) 2) * v ^ (d + 1) := by
  intro d
  induction d with
  | zero =>
    intro s v hv _
    rw [Matrix.det_fin_one]
    simp [hv]
  | succ d ih =>
    intro s v hv hvan
    set A : Matrix (Fin (d + 2)) (Fin (d + 2)) R := fun i j => s (i.val + j.val) with hA
    have hlast : (Fin.last (d + 1)).val = d + 1 := rfl
    rw [Matrix.det_succ_row A (Fin.last (d + 1))]
    -- only the j = 0 term survives
    rw [Finset.sum_eq_single (0 : Fin (d + 2))]
    · -- evaluate the j = 0 term
      have hval : A (Fin.last (d + 1)) 0 = v := by
        simp only [hA, hlast]; rw [show (0 : Fin (d + 2)).val = 0 from rfl, Nat.add_zero, hv]
      -- the minor equals the Hankel matrix of the shifted sequence
      have hminor : A.submatrix (Fin.last (d + 1)).succAbove ((0 : Fin (d + 2)).succAbove)
          = (fun i' j' : Fin (d + 1) => (fun x => s (x + 1)) (i'.val + j'.val)) := by
        rw [Fin.succAbove_last, Fin.succAbove_zero]
        ext i' j'
        simp only [Matrix.submatrix_apply, hA, Fin.val_castSucc, Fin.val_succ]
        congr 1
      rw [hminor]
      have ht1 : (fun x => s (x + 1)) d = v := by simpa using hv
      have ht2 : ∀ x, d < x → x ≤ 2 * d → (fun x => s (x + 1)) x = 0 := by
        intro x hx1 hx2
        simp only
        exact hvan (x + 1) (by omega) (by omega)
      rw [ih (fun x => s (x + 1)) v ht1 ht2, hval, hlast]
      -- exponent arithmetic
      have hch : Nat.choose (d + 2) 2 = (d + 1) + Nat.choose (d + 1) 2 := by
        rw [Nat.choose_succ_succ (d + 1) 1]
        simp [Nat.choose_one_right]
      rw [hch]
      rw [show (0 : Fin (d + 2)).val = 0 from rfl, Nat.add_zero]
      rw [pow_add, pow_succ, pow_succ]
      ring
    · -- terms j ≠ 0 vanish
      intro j _ hj
      have hjlt : j.val < d + 2 := j.isLt
      have hjpos : 1 ≤ j.val := by
        rcases Nat.eq_zero_or_pos j.val with h | h
        · exact absurd (Fin.ext h) hj
        · exact h
      have : A (Fin.last (d + 1)) j = 0 := by
        simp only [hA, hlast]
        apply hvan
        · omega
        · have : j.val ≤ d + 1 := by omega
          omega
      rw [this]; ring
    · intro h; exact absurd (Finset.mem_univ _) h

/-- `choose (p+m) k ≡ choose m (k % p)` for `m < p`, `k < 2p`. -/
theorem choose_shift (m k : ℕ) (hm : m < p) (hk : k < 2 * p) :
    (Nat.choose (p + m) k : ZMod p) = (Nat.choose m (k % p) : ZMod p) := by
  have hp0 : 0 < p := hp.out.pos
  have hd : k / p < 2 := (Nat.div_lt_iff_lt_mul hp0).mpr hk
  have hone : Nat.choose 1 (k / p) = 1 := by
    interval_cases h : (k / p) <;> simp
  rw [luc, pr_mod m hm, pr_div m hm, hone]
  simp

/-- `(-1)^a` only depends on `a mod 2`. -/
theorem negpow_mod2 {R : Type*} [Monoid R] [HasDistribNeg R] (a : ℕ) :
    (-1 : R) ^ a = (-1) ^ (a % 2) := by
  conv_lhs => rw [← Nat.div_add_mod a 2]
  rw [pow_add, pow_mul]
  simp

/-- Determinant of the Hankel matrix mod `p`, via `hankel_antitri`. -/
theorem det_hankel (d : ℕ) [Fact (d + 1).Prime] (s : ℕ → ℤ) (v : ZMod (d + 1))
    (hv : ((s d : ℤ) : ZMod (d + 1)) = v)
    (hvan : ∀ x, d < x → x ≤ 2 * d → ((s x : ℤ) : ZMod (d + 1)) = 0) :
    ((Matrix.det (fun i j : Fin (d + 1) => s (i.val + j.val)) : ℤ) : ZMod (d + 1))
      = (-1) ^ (Nat.choose (d + 1) 2) * v ^ (d + 1) := by
  have hmap : ((Matrix.det (fun i j : Fin (d + 1) => s (i.val + j.val)) : ℤ) : ZMod (d + 1))
      = Matrix.det (fun i j : Fin (d + 1) => ((s (i.val + j.val) : ℤ) : ZMod (d + 1))) := by
    have h := RingHom.map_det (Int.castRingHom (ZMod (d + 1)))
      (fun i j : Fin (d + 1) => s (i.val + j.val))
    simpa using h
  rw [hmap]
  exact hankel_antitri d (fun x => ((s x : ℤ) : ZMod (d + 1))) v hv hvan

/-- Geometric sum of `(-1)^k`. -/
theorem geomNegOne {R : Type*} [CommRing R] (m : ℕ) :
    (∑ k ∈ range m, (-1 : R) ^ k) = if Even m then 0 else 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases he : Even m
    · rw [if_pos he, he.neg_one_pow, if_neg (by simp [Nat.even_add_one, he]), zero_add]
    · rw [if_neg he, (Nat.not_even_iff_odd.mp he).neg_one_pow,
        if_pos (by simp [Nat.even_add_one, he])]
      ring

theorem a_pred (hodd : Odd p) : ((a (p - 1) : ℤ) : ZMod p) = 1 := by
  have hp1 : p - 1 + 1 = p := by have := hp.out.one_lt; omega
  have hcast : ((a (p - 1) : ℤ) : ZMod p)
      = ∑ k ∈ range (p - 1 + 1), ((-1 : ZMod p) ^ k * (Nat.choose (p - 1) k : ZMod p) ^ 4) := by
    rw [a]; push_cast; rfl
  rw [hcast]
  have hcongr : (∑ k ∈ range (p - 1 + 1), ((-1 : ZMod p) ^ k * (Nat.choose (p - 1) k : ZMod p) ^ 4))
      = ∑ k ∈ range (p - 1 + 1), ((-1 : ZMod p) ^ k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [choose_pred k (by omega), ← pow_mul,
      show (-1 : ZMod p) ^ (k * 4) = 1 from Even.neg_one_pow ⟨2 * k, by ring⟩]
    ring
  rw [hcongr, hp1, geomNegOne]
  rw [if_neg (Nat.not_even_iff_odd.mpr hodd)]

theorem a_van (m : ℕ) (hm : m ≤ p - 2) (hodd : Odd p) :
    ((a (p + m) : ℤ) : ZMod p) = 0 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hcast : ((a (p + m) : ℤ) : ZMod p)
      = ∑ k ∈ range (p + m + 1), (-1 : ZMod p) ^ k * (Nat.choose (p + m) k : ZMod p) ^ 4 := by
    rw [a]; push_cast; rfl
  rw [hcast]
  -- Lucas reduction
  have hshift : (∑ k ∈ range (p + m + 1), (-1 : ZMod p) ^ k * (Nat.choose (p + m) k : ZMod p) ^ 4)
      = ∑ k ∈ range (p + m + 1), (-1 : ZMod p) ^ k * (Nat.choose m (k % p) : ZMod p) ^ 4 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [choose_shift m k (by omega) (by omega)]
  rw [hshift]
  -- split the range at p
  rw [show p + m + 1 = p + (m + 1) from by ring, Finset.sum_range_add]
  -- first part: reduce range p to range (m+1)
  have hfirst : (∑ x ∈ range p, (-1 : ZMod p) ^ x * (Nat.choose m (x % p) : ZMod p) ^ 4)
      = ∑ x ∈ range (m + 1), (-1 : ZMod p) ^ x * (Nat.choose m x : ZMod p) ^ 4 := by
    rw [← Finset.sum_subset (by
      intro x hx; rw [Finset.mem_range] at hx ⊢; omega : range (m + 1) ⊆ range p)]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_range] at hx
      rw [Nat.mod_eq_of_lt (by omega)]
    · intro x hx hxn
      rw [Finset.mem_range] at hx hxn
      rw [Nat.mod_eq_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
      simp
  -- second part: equals -(first part)
  have hsecond : (∑ x ∈ range (m + 1), (-1 : ZMod p) ^ (p + x) * (Nat.choose m ((p + x) % p) : ZMod p) ^ 4)
      = - ∑ x ∈ range (m + 1), (-1 : ZMod p) ^ x * (Nat.choose m x : ZMod p) ^ 4 := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    rw [pr_mod x (by omega), pow_add, Odd.neg_one_pow hodd]
    ring
  rw [hfirst, hsecond]
  ring

/-- The key central-binomial cancellation. -/
theorem cancel (j r : ℕ) (hj : j < p) (hr : r < p) :
    (Nat.choose (2 * j) j : ZMod p) * (Nat.choose (2 * (p + r)) (p + r) : ZMod p)
      = (Nat.choose (2 * (p + j)) (p + j) : ZMod p) * (Nat.choose (2 * r) r : ZMod p) := by
  rcases lt_or_ge (2 * j) p with hjs | hjl
  · rcases lt_or_ge (2 * r) p with hrs | hrl
    · rw [central_shift_small r hrs, central_shift_small j hjs]; ring
    · rw [central_shift_zero r hr hrl, central_zero r hr hrl]; ring
  · rw [central_zero j hj hjl, central_shift_zero j hj hjl]; ring

theorem c_van (m : ℕ) (hm : m ≤ p - 2) (hodd : Odd p) :
    ((c (p + m) : ℤ) : ZMod p) = 0 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hcast : ((c (p + m) : ℤ) : ZMod p)
      = ∑ k ∈ range (p + m + 1), (-1 : ZMod p) ^ k * (Nat.choose (p + m) k : ZMod p) ^ 2
          * (Nat.choose (2 * k) k : ZMod p)
          * (Nat.choose (2 * (p + m - k)) (p + m - k) : ZMod p) := by
    rw [c]; push_cast; rfl
  rw [hcast]
  -- Lucas reduction on the squared binomial
  have hshift : (∑ k ∈ range (p + m + 1), (-1 : ZMod p) ^ k * (Nat.choose (p + m) k : ZMod p) ^ 2
          * (Nat.choose (2 * k) k : ZMod p)
          * (Nat.choose (2 * (p + m - k)) (p + m - k) : ZMod p))
      = ∑ k ∈ range (p + m + 1), (-1 : ZMod p) ^ k * (Nat.choose m (k % p) : ZMod p) ^ 2
          * (Nat.choose (2 * k) k : ZMod p)
          * (Nat.choose (2 * (p + m - k)) (p + m - k) : ZMod p) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [choose_shift m k (by omega) (by omega)]
  rw [hshift]
  rw [show p + m + 1 = p + (m + 1) from by ring, Finset.sum_range_add]
  -- reduce the first sum (range p) to range (m+1)
  have hfirst : (∑ x ∈ range p, (-1 : ZMod p) ^ x * (Nat.choose m (x % p) : ZMod p) ^ 2
          * (Nat.choose (2 * x) x : ZMod p)
          * (Nat.choose (2 * (p + m - x)) (p + m - x) : ZMod p))
      = ∑ j ∈ range (m + 1), (-1 : ZMod p) ^ j * (Nat.choose m j : ZMod p) ^ 2
          * (Nat.choose (2 * j) j : ZMod p)
          * (Nat.choose (2 * (p + m - j)) (p + m - j) : ZMod p) := by
    rw [← Finset.sum_subset (by
      intro x hx; rw [Finset.mem_range] at hx ⊢; omega : range (m + 1) ⊆ range p)]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_range] at hx
      rw [Nat.mod_eq_of_lt (by omega)]
    · intro x hx hxn
      rw [Finset.mem_range] at hx hxn
      rw [Nat.mod_eq_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
      simp
  rw [hfirst, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  have e1 : p + m - (p + j) = m - j := by omega
  have e2 : (p + j) % p = j := pr_mod j (by omega)
  have e3 : p + m - j = p + (m - j) := by omega
  rw [e2, e1, e3, pow_add, Odd.neg_one_pow hodd]
  have hc := cancel (p := p) j (m - j) (by omega) (by omega)
  linear_combination ((-1 : ZMod p) ^ j * (Nat.choose m j : ZMod p) ^ 2) * hc

theorem c_pred (hodd : Odd p) : ((c (p - 1) : ℤ) : ZMod p) = (-1) ^ ((p - 1) / 2) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  obtain ⟨q, hq⟩ := hodd
  set t := (p - 1) / 2 with ht
  have htval : t = q := by omega
  have h2t : 2 * t = p - 1 := by omega
  have hsubt : p - 1 - t = t := by omega
  have htp : t < p := by omega
  have hp1 : p - 1 + 1 = p := by omega
  have hcast : ((c (p - 1) : ℤ) : ZMod p)
      = ∑ k ∈ range (p - 1 + 1), (-1 : ZMod p) ^ k * (Nat.choose (p - 1) k : ZMod p) ^ 2
          * (Nat.choose (2 * k) k : ZMod p) * (Nat.choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) := by
    rw [c]; push_cast; rfl
  rw [hcast, hp1]
  rw [Finset.sum_eq_single t]
  · -- value at k = t
    rw [h2t, hsubt, h2t]
    rw [choose_pred t (by omega)]
    have hu : (-1 : ZMod p) ^ t * (-1) ^ t = 1 := by
      rw [← pow_add]; exact Even.neg_one_pow ⟨t, by ring⟩
    linear_combination (((-1 : ZMod p) ^ t) ^ 3 + (-1 : ZMod p) ^ t) * hu
  · -- terms k ≠ t vanish
    intro k hk hkt
    rw [Finset.mem_range] at hk
    rcases lt_or_gt_of_ne hkt with hlt | hgt
    · -- k < t : the factor choose (2(p-1-k)) (p-1-k) vanishes
      rw [central_zero (p - 1 - k) (by omega) (by omega)]
      ring
    · -- k > t : the factor choose (2k) k vanishes
      rw [central_zero k hk (by omega)]
      ring
  · intro h; exact absurd (Finset.mem_range.mpr htp) h

/-- `(-1)^(choose p 2) = (-1)^((p-1)/2)`. -/
theorem exp_eq (hodd : Odd p) :
    (-1 : ZMod p) ^ (Nat.choose p 2) = (-1) ^ ((p - 1) / 2) := by
  rw [negpow_mod2 (Nat.choose p 2), negpow_mod2 ((p - 1) / 2)]
  congr 1
  rw [Nat.choose_two_right]
  obtain ⟨q, rfl⟩ := hodd
  have h1 : (2 * q + 1) * (2 * q + 1 - 1) / 2 = q + 2 * (q * q) := by
    rw [show 2 * q + 1 - 1 = 2 * q from by omega,
        show (2 * q + 1) * (2 * q) = 2 * (q + 2 * (q * q)) from by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
  rw [h1]
  omega

end

/--
A228304 Conjecture: Let p be any odd prime, and let A(p) be the p X p determinant with (i,j)-entry equal to a(i+j) for all i,j = 0,...,p-1. Then A(p) == (-1)^{(p-1)/2} (mod p). Similarly, if c(n) = sum_{k=0}^n (-1)^k*C(n,k)^2*C(2k,k)*C(2(n-k),n-k) and C(p) is the p X p determinant with (i,j)-entry equal to c(i+j) for all i,j = 0,...,p-1, then we have C(p) == 1 (mod p).
-/
theorem oeis_228304_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) :
    let N := Fin p
    let half_minus_one := (p - 1) / 2
    let A : Matrix N N ℤ := fun i j => a (i.val + j.val)
    let C : Matrix N N ℤ := fun i j => c (i.val + j.val)
    (Matrix.det A ≡ (-1 : ℤ) ^ half_minus_one [ZMOD p]) ∧ (Matrix.det C ≡ 1 [ZMOD p]) := by
  intro N half_minus_one A C
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two h_odd
  obtain ⟨d, rfl⟩ : ∃ d, p = d + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  -- vanishing facts as a single helper
  have hvan_a : ∀ x, d < x → x ≤ 2 * d → ((a x : ℤ) : ZMod (d + 1)) = 0 := by
    intro x hx1 hx2
    have := a_van (p := d + 1) (x - (d + 1)) (by omega) hodd
    rwa [show d + 1 + (x - (d + 1)) = x from by omega] at this
  have hvan_c : ∀ x, d < x → x ≤ 2 * d → ((c x : ℤ) : ZMod (d + 1)) = 0 := by
    intro x hx1 hx2
    have := c_van (p := d + 1) (x - (d + 1)) (by omega) hodd
    rwa [show d + 1 + (x - (d + 1)) = x from by omega] at this
  have hv_a := a_pred (p := d + 1) hodd
  have hv_c := c_pred (p := d + 1) hodd
  refine ⟨?_, ?_⟩
  · -- det A
    rw [← ZMod.intCast_eq_intCast_iff]
    show ((Matrix.det (fun i j : Fin (d + 1) => a (i.val + j.val)) : ℤ) : ZMod (d + 1)) = _
    rw [det_hankel d a 1 hv_a hvan_a, exp_eq hodd]
    push_cast
    simp [half_minus_one]
  · -- det C
    rw [← ZMod.intCast_eq_intCast_iff]
    show ((Matrix.det (fun i j : Fin (d + 1) => c (i.val + j.val)) : ℤ) : ZMod (d + 1)) = _
    rw [det_hankel d c _ hv_c hvan_c, exp_eq hodd]
    -- goal: (-1)^((d+1-1)/2) * ((-1)^((d+1-1)/2))^(d+1) = ((1:ℤ):ZMod (d+1))
    set t := (d + 1 - 1) / 2 with ht
    rw [← pow_mul, ← pow_add]
    have hde : Even d := by
      rw [← Nat.not_even_iff_odd, Nat.even_add_one] at hodd
      exact not_not.mp hodd
    have heven : Even (t + t * (d + 1)) := by
      have : t + t * (d + 1) = t * (d + 2) := by ring
      rw [this]
      exact (hde.add (by norm_num : Even 2)).mul_left t
    rw [heven.neg_one_pow]
    simp

