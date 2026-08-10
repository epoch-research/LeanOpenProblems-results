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

def aZ (p n : ℕ) : ZMod p :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 4)

def cZ (p n : ℕ) : ZMod p :=
  Finset.sum (range (n + 1)) fun k =>
    ((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 2) * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p)

lemma cast_a_eq_aZ (p n : ℕ) : ((a n : ℤ) : ZMod p) = aZ p n := by
  simp [a, aZ, map_sum, Nat.cast_sum]

lemma cast_c_eq_cZ (p n : ℕ) : ((c n : ℤ) : ZMod p) = cZ p n := by
  simp [c, cZ, map_sum, Nat.cast_sum]

lemma choose_p_sub_one_zmod (p k : ℕ) (hp : Nat.Prime p) (hk : k < p) :
    ((Nat.choose (p - 1) k : ℕ) : ZMod p) = (-1 : ZMod p) ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k < p := Nat.lt_trans (Nat.lt_succ_self k) hk
      have hk1_ne : ((k+1 : ℕ) : ZMod p) ≠ 0 := by
        intro hzero
        have hdvd : p ∣ k + 1 := (ZMod.natCast_eq_zero_iff (k+1) p).mp hzero
        have hle := Nat.le_of_dvd (Nat.succ_pos _) hdvd
        omega
      have hnat := Nat.choose_succ_right_eq (p - 1) k
      have hcast : ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod p) * ((k+1 : ℕ) : ZMod p)
          = ((Nat.choose (p - 1) k : ℕ) : ZMod p) * (((p - 1) - k : ℕ) : ZMod p) := by
        have h := congrArg (fun n : ℕ => (n : ZMod p)) hnat
        simpa [Nat.cast_mul] using h
      have hpk : (((p - 1) - k : ℕ) : ZMod p) = - ((k+1 : ℕ) : ZMod p) := by
        have : (p - 1 - k) + (k + 1) = p := by omega
        apply eq_neg_iff_add_eq_zero.mpr
        rw [← Nat.cast_add, this]
        simp
      apply (mul_right_injective₀ hk1_ne) ?_
      change ((k+1 : ℕ) : ZMod p) * ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod p)
          = ((k+1 : ℕ) : ZMod p) * ((-1 : ZMod p) ^ (k + 1))
      rw [show ((k+1 : ℕ) : ZMod p) * ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod p)
            = ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod p) * ((k+1 : ℕ) : ZMod p) by ring,
          hcast, hpk, ih hk']
      ring

lemma sum_neg_one_range_odd {R : Type*} [Ring R] (m : ℕ) :
    (∑ k ∈ range (2*m+1), (-1 : R)^k) = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2*(m+1)+1 = (2*m+1)+2 by ring]
      rw [Finset.sum_range_add]
      simp [ih, pow_add]

lemma aZ_top (p m : ℕ) (hp : Nat.Prime p) (hp_eq : p = 2*m+1) :
    aZ p (p-1) = 1 := by
  subst p
  unfold aZ
  rw [show 2*m+1 - 1 + 1 = 2*m+1 by omega]
  trans ∑ k ∈ range (2*m+1), (-1 : ZMod (2*m+1)) ^ k
  · apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < 2*m+1 := by simpa using hk
    rw [choose_p_sub_one_zmod (2*m+1) k hp hklt]
    have h4 : (((-1 : ZMod (2*m+1)) ^ k) ^ 4) = 1 := by
      rw [← pow_mul]
      have he : Even (k * 4) := ⟨2*k, by omega⟩
      simpa using (Even.neg_one_pow (α := ZMod (2*m+1)) he)
    simp [h4]
  · exact sum_neg_one_range_odd (R := ZMod (2*m+1)) m



lemma choose_p_add_cast_zmod (p r k : ℕ) (hp : Nat.Prime p) (hr : r < p) (hk : k ≤ p + r) :
    ((Nat.choose (p + r) k : ℕ) : ZMod p) =
      if k < p then ((Nat.choose r k : ℕ) : ZMod p) else ((Nat.choose r (k - p) : ℕ) : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmod := (Choose.choose_modEq_choose_mod_mul_choose_div (n := p + r) (k := k) (p := p))
  have hz : (((Nat.choose (p + r) k : ℕ) : ℤ) : ZMod p) =
      (((Nat.choose ((p + r) % p) (k % p) * Nat.choose ((p + r) / p) (k / p) : ℕ) : ℤ) : ZMod p) := by
    exact (ZMod.intCast_eq_intCast_iff _ _ p).2 hmod
  have hp_pos : 0 < p := hp.pos
  have hpr_mod : (p + r) % p = r := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hr]
  have hpr_div : (p + r) / p = 1 := by
    rw [Nat.add_comm, Nat.add_div_right _ hp_pos]
    simp [Nat.div_eq_of_lt hr]
  by_cases hkp : k < p
  · have hk_mod : k % p = k := Nat.mod_eq_of_lt hkp
    have hk_div : k / p = 0 := Nat.div_eq_of_lt hkp
    simpa [hkp, hpr_mod, hpr_div, hk_mod, hk_div, Nat.cast_mul] using hz
  · have hkp_le : p ≤ k := Nat.le_of_not_gt hkp
    have hk_lt_2p : k < 2 * p := by omega
    have hk_div : k / p = 1 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · exact hk_lt_2p
    have hk_mod : k % p = k - p := by
      rw [Nat.mod_eq_sub_mod hkp_le]
      rw [Nat.mod_eq_of_lt]
      omega
    simpa [hkp, hpr_mod, hpr_div, hk_mod, hk_div, Nat.cast_mul] using hz

lemma aZ_p_add_eq_zero (p r : ℕ) (hp : Nat.Prime p) (hpodd : p ≠ 2) (hr : r < p) :
    aZ p (p + r) = 0 := by
  classical
  have hp_pos : 0 < p := hp.pos
  have hp_odd_nat : Odd p := hp.odd_of_ne_two hpodd
  have hnegp : (-1 : ZMod p) ^ p = -1 := by
    rcases hp_odd_nat with ⟨m, hm⟩
    rw [hm]
    simp [pow_succ, pow_mul]
  have hsplit := Finset.sum_range_add (fun k => ((-1 : ZMod p) ^ k) * ((choose (p + r) k : ZMod p) ^ 4)) p (r+1)
  unfold aZ
  rw [show p + r + 1 = p + (r + 1) by omega]
  rw [hsplit]
  -- lower sum equals S, upper sum equals -S
  let f : ℕ → ZMod p := fun k => ((-1 : ZMod p) ^ k) * ((choose r k : ZMod p) ^ 4)
  have hlower : (∑ x ∈ range p, ((-1 : ZMod p) ^ x) * ((choose (p + r) x : ZMod p) ^ 4)) = ∑ x ∈ range p, f x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxlt : x < p := by simpa using hx
    have hch := choose_p_add_cast_zmod p r x hp hr (by omega)
    simp [f, hxlt, hch]
  have hupper : (∑ x ∈ range (r + 1), ((-1 : ZMod p) ^ (p + x)) * ((choose (p + r) (p + x) : ZMod p) ^ 4)) = - (∑ x ∈ range (r + 1), f x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hxle : x ≤ r := by simpa [Finset.mem_range] using hx
    have hch := choose_p_add_cast_zmod p r (p+x) hp hr (by omega)
    have hnlt : ¬ p + x < p := by omega
    have hsub : p + x - p = x := by omega
    simp [f, hch, hnlt, hsub, pow_add, hnegp]
  rw [hlower, hupper]
  have htail : (∑ x ∈ range p, f x) = ∑ x ∈ range (r+1), f x := by
    symm
    rw [← Finset.sum_range_add_sum_Ico (f := f) (m := r+1) (n := p) (by omega)]
    suffices (∑ k ∈ Ico (r + 1) p, f k) = 0 by simp [this]
    apply Finset.sum_eq_zero
    intro x hx
    have hxr : r < x := by
      have hx' : r + 1 ≤ x ∧ x < p := by simpa [Finset.mem_Ico] using hx
      omega
    simp [f, Nat.choose_eq_zero_of_lt hxr]
  rw [htail]
  abel

lemma central_small_cast_zmod (p s : ℕ) (hp : Nat.Prime p) (hs : s < p) :
    ((Nat.choose (2*s) s : ℕ) : ZMod p) =
      if 2*s < p then ((Nat.choose (2*s) s : ℕ) : ZMod p) else 0 := by
  by_cases h : 2*s < p
  · simp [h]
  · simp [h]
    haveI : Fact p.Prime := ⟨hp⟩
    have hmod := (Choose.choose_modEq_choose_mod_mul_choose_div (n := 2*s) (k := s) (p := p))
    have hz : (((Nat.choose (2*s) s : ℕ) : ℤ) : ZMod p) =
        (((Nat.choose ((2*s) % p) (s % p) * Nat.choose ((2*s) / p) (s / p) : ℕ) : ℤ) : ZMod p) := by
      exact (ZMod.intCast_eq_intCast_iff _ _ p).2 hmod
    have hp_pos : 0 < p := hp.pos
    have hs_mod : s % p = s := Nat.mod_eq_of_lt hs
    have hs_div : s / p = 0 := Nat.div_eq_of_lt hs
    have hle : p ≤ 2*s := Nat.le_of_not_gt h
    have hlt2 : 2*s < 2*p := by omega
    have h2mod : (2*s) % p = 2*s - p := by
      rw [Nat.mod_eq_sub_mod hle]
      rw [Nat.mod_eq_of_lt]
      omega
    have hzero : Nat.choose (2*s - p) s = 0 := by
      apply Nat.choose_eq_zero_of_lt
      omega
    simpa [hs_mod, hs_div, h2mod, hzero, Nat.cast_mul] using hz

lemma central_p_add_cast_zmod (p s : ℕ) (hp : Nat.Prime p) (hs : s < p) :
    ((Nat.choose (2*(p+s)) (p+s) : ℕ) : ZMod p) =
      if 2*s < p then (2 : ZMod p) * ((Nat.choose (2*s) s : ℕ) : ZMod p) else 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmod := (Choose.choose_modEq_choose_mod_mul_choose_div (n := 2*(p+s)) (k := p+s) (p := p))
  have hz : (((Nat.choose (2*(p+s)) (p+s) : ℕ) : ℤ) : ZMod p) =
      (((Nat.choose ((2*(p+s)) % p) ((p+s) % p) * Nat.choose ((2*(p+s)) / p) ((p+s) / p) : ℕ) : ℤ) : ZMod p) := by
    exact (ZMod.intCast_eq_intCast_iff _ _ p).2 hmod
  have hp_pos : 0 < p := hp.pos
  have hk_mod : (p+s) % p = s := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hs]
  have hk_div : (p+s) / p = 1 := by
    rw [Nat.add_comm, Nat.add_div_right _ hp_pos]
    simp [Nat.div_eq_of_lt hs]
  by_cases h : 2*s < p
  · have hn_mod : (2*(p+s)) % p = 2*s := by
      have hcalc : 2*(p+s) = 2*s + p*2 := by ring
      rw [hcalc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
    have hn_div : (2*(p+s)) / p = 2 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · have : 2*(p+s) < (2+1)*p := by omega
        exact this
    calc
      ((Nat.choose (2*(p+s)) (p+s) : ℕ) : ZMod p)
          = ((Nat.choose (2*s) s : ℕ) : ZMod p) * (2 : ZMod p) := by
              simpa [h, hk_mod, hk_div, hn_mod, hn_div, Nat.cast_mul] using hz
      _ = (if 2*s < p then (2 : ZMod p) * ((Nat.choose (2*s) s : ℕ) : ZMod p) else 0) := by
            have h' : s*2 < p := by omega
            simp [h, h', mul_comm]
  · have hle : p ≤ 2*s := Nat.le_of_not_gt h
    have hn_mod : (2*(p+s)) % p = 2*s - p := by
      have hcalc : 2*(p+s) = 2*s + p*2 := by ring
      rw [hcalc, Nat.add_mul_mod_self_left, Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt]
      omega
    have hn_div : (2*(p+s)) / p = 3 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · have : 2*(p+s) < (3+1)*p := by omega
        exact this
    have hzero : Nat.choose (2*s - p) s = 0 := by
      apply Nat.choose_eq_zero_of_lt
      omega
    simpa [h, hk_mod, hk_div, hn_mod, hn_div, hzero, Nat.cast_mul] using hz

lemma central_pair_eq_zmod (p x s : ℕ) (hp : Nat.Prime p) (hx : x < p) (hs : s < p) :
    ((Nat.choose (2*x) x : ℕ) : ZMod p) * ((Nat.choose (2*(p+s)) (p+s) : ℕ) : ZMod p)
      = ((Nat.choose (2*(p+x)) (p+x) : ℕ) : ZMod p) * ((Nat.choose (2*s) s : ℕ) : ZMod p) := by
  by_cases hx2 : 2*x < p
  · by_cases hs2 : 2*s < p
    · have hpx := central_p_add_cast_zmod p x hp hx
      have hps := central_p_add_cast_zmod p s hp hs
      simp [hx2, hs2] at hpx hps
      rw [hpx, hps]
      ring
    · have hs0 := central_small_cast_zmod p s hp hs
      have hps := central_p_add_cast_zmod p s hp hs
      simp [hs2] at hs0 hps
      rw [hs0, hps]
      ring
  · by_cases hs2 : 2*s < p
    · have hx0 := central_small_cast_zmod p x hp hx
      have hpx := central_p_add_cast_zmod p x hp hx
      simp [hx2] at hx0 hpx
      rw [hx0, hpx]
      ring
    · have hx0 := central_small_cast_zmod p x hp hx
      have hpx := central_p_add_cast_zmod p x hp hx
      have hs0 := central_small_cast_zmod p s hp hs
      have hps := central_p_add_cast_zmod p s hp hs
      simp [hx2, hs2] at hx0 hpx hs0 hps
      rw [hx0, hpx, hs0, hps]

lemma cZ_p_add_eq_zero (p r : ℕ) (hp : Nat.Prime p) (hpodd : p ≠ 2) (hr : r < p) :
    cZ p (p + r) = 0 := by
  classical
  have hp_odd_nat : Odd p := hp.odd_of_ne_two hpodd
  have hnegp : (-1 : ZMod p) ^ p = -1 := by
    rcases hp_odd_nat with ⟨m, hm⟩
    rw [hm]
    simp [pow_succ, pow_mul]
  let T : ℕ → ℕ → ZMod p := fun n k =>
    ((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 2) * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p)
  unfold cZ
  rw [show p + r + 1 = p + (r + 1) by omega]
  rw [Finset.sum_range_add (fun k => T (p+r) k) p (r+1)]
  let f : ℕ → ZMod p := fun k =>
    ((-1 : ZMod p) ^ k) * ((choose r k : ZMod p) ^ 2) * (choose (2*k) k : ZMod p) * (choose (2*(p+(r-k))) (p+(r-k)) : ZMod p)
  have hlower : (∑ x ∈ range p, T (p+r) x) = ∑ x ∈ range p, f x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxlt : x < p := by simpa using hx
    have hch := choose_p_add_cast_zmod p r x hp hr (by omega)
    by_cases hxr : x ≤ r
    · have hsub : p + r - x = p + (r - x) := by omega
      simp [T, f, hxlt, hch, hsub]
    · have hz : Nat.choose r x = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hxr)
      simp [T, f, hxlt, hch, hz]
  have hupper : (∑ x ∈ range (r + 1), T (p+r) (p+x)) = - (∑ x ∈ range (r + 1), f x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hxle : x ≤ r := by simpa [Finset.mem_range] using hx
    have hch := choose_p_add_cast_zmod p r (p+x) hp hr (by omega)
    have hnlt : ¬ p + x < p := by omega
    have hsub1 : p + x - p = x := by omega
    have hsub2 : p + r - (p + x) = r - x := by omega
    have hcentral := central_pair_eq_zmod p x (r-x) hp (by omega) (by omega)
    simp [T, f, hch, hnlt, hsub1, hsub2, pow_add, hnegp]
    calc
      (-1 : ZMod p) ^ x * ↑(r.choose x) ^ 2 * ↑((2 * (p + x)).choose (p + x)) * ↑((2 * (r - x)).choose (r - x))
          = ((-1 : ZMod p) ^ x * ↑(r.choose x) ^ 2) * (↑((2 * (p + x)).choose (p + x)) * ↑((2 * (r - x)).choose (r - x))) := by ring
      _ = ((-1 : ZMod p) ^ x * ↑(r.choose x) ^ 2) * (↑((2 * x).choose x) * ↑((2 * (p + (r - x))).choose (p + (r - x)))) := by rw [← hcentral]
      _ = (-1 : ZMod p) ^ x * ↑(r.choose x) ^ 2 * ↑((2 * x).choose x) * ↑((2 * (p + (r - x))).choose (p + (r - x))) := by ring
  rw [hlower, hupper]
  have htail : (∑ x ∈ range p, f x) = ∑ x ∈ range (r+1), f x := by
    symm
    rw [← Finset.sum_range_add_sum_Ico (f := f) (m := r+1) (n := p) (by omega)]
    suffices (∑ k ∈ Ico (r + 1) p, f k) = 0 by simp [this]
    apply Finset.sum_eq_zero
    intro x hx
    have hxr : r < x := by
      have hx' : r + 1 ≤ x ∧ x < p := by simpa [Finset.mem_Ico] using hx
      omega
    simp [f, Nat.choose_eq_zero_of_lt hxr]
  rw [htail]
  abel

lemma cZ_top (p m : ℕ) (hp : Nat.Prime p) (hp_eq : p = 2*m+1) :
    cZ p (p-1) = (-1 : ZMod p) ^ m := by
  subst p
  unfold cZ
  rw [show 2*m+1 - 1 + 1 = 2*m+1 by omega]
  let term : ℕ → ZMod (2*m+1) := fun k =>
    (-1 : ZMod (2*m+1)) ^ k * ((choose (2*m+1-1) k : ZMod (2*m+1)) ^ 2) *
      (choose (2*k) k : ZMod (2*m+1)) *
      (choose (2*(2*m+1-1-k)) (2*m+1-1-k) : ZMod (2*m+1))
  change (∑ k ∈ range (2*m+1), term k) = (-1 : ZMod (2*m+1)) ^ m
  have hsum : (∑ k ∈ range (2*m+1), term k) = term m := by
    apply Finset.sum_eq_single
    · intro k hk hkm
      have hklt : k < 2*m+1 := by simpa using hk
      by_cases hlt : k < m
      · have hslt : 2*m - k < 2*m+1 := by omega
        have hsmall := central_small_cast_zmod (2*m+1) (2*m-k) hp hslt
        have hnsmall : ¬ 2*(2*m-k) < 2*m+1 := by omega
        simp [hnsmall] at hsmall
        dsimp [term]
        rw [hsmall]
        ring
      · have hgt : m < k := by omega
        have hsmall := central_small_cast_zmod (2*m+1) k hp hklt
        have hnsmall : ¬ 2*k < 2*m+1 := by omega
        simp [hnsmall] at hsmall
        dsimp [term]
        rw [hsmall]
        ring
    · intro hmnot
      exfalso
      apply hmnot
      simp
      omega
  rw [hsum]
  dsimp [term]
  have hchoose := choose_p_sub_one_zmod (2*m+1) m hp (by omega)
  have hcent : ((Nat.choose (2*m) m : ℕ) : ZMod (2*m+1)) = (-1 : ZMod (2*m+1)) ^ m := by
    simpa [show 2*m+1-1 = 2*m by omega] using hchoose
  have hchoose_sq : (((Nat.choose (2*m) m : ℕ) : ZMod (2*m+1)) ^ 2) = 1 := by
    rw [hcent, ← pow_mul]
    have he : Even (m*2) := ⟨m, by omega⟩
    simpa using (Even.neg_one_pow (α := ZMod (2*m+1)) he)
  have hlast : 2*m - m = m := by omega
  rw [hlast, hchoose_sq, hcent]
  ring_nf
  apply neg_one_pow_congr
  rw [Nat.even_mul]
  constructor
  · intro h
    exact h.resolve_right (by norm_num : ¬ Even 3)
  · intro hm
    exact Or.inl hm


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
    (hzero : ∀ r, r < p → s (p + r) = 0) (htop : s (p-1) = t) :
    Matrix.det (fun i j : Fin p => s (i.val + j.val)) = ((-1 : ZMod p) ^ m) * t ^ p := by
  classical
  let M : Matrix (Fin p) (Fin p) (ZMod p) := fun i j => s (i.val + j.val)
  let B : Matrix (Fin p) (Fin p) (ZMod p) := M.submatrix id (Fin.revPerm : Equiv.Perm (Fin p))
  have htri : B.BlockTriangular id := by
    intro i j hij
    dsimp [B, M]
    have hjlt : (j : ℕ) < i := by simpa using hij
    have hi_lt : (i : ℕ) < p := i.2
    have hj_lt : (j : ℕ) < p := j.2
    have hsum : i.val + (p - (j.val + 1)) = p + (i.val - (j.val + 1)) := by omega
    rw [hsum]
    apply hzero
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
  classical
  let m := (p - 1) / 2
  have hpodd : Odd p := hp.odd_of_ne_two h_odd
  have hp_eq : p = 2*m + 1 := by
    rcases hpodd with ⟨q, hq⟩
    have hqm : q = m := by
      dsimp [m]
      omega
    omega
  dsimp
  constructor
  · have hdet_z : (((Matrix.det (fun i j : Fin p => a (i.val + j.val)) : ℤ) : ZMod p)) = ((-1 : ZMod p) ^ m) := by
      change (Int.castRingHom (ZMod p)) (Matrix.det (fun i j : Fin p => a (i.val + j.val))) = _
      rw [RingHom.map_det (Int.castRingHom (ZMod p))]
      have hs := sparse_hankel_det_zmod p m hp_eq (fun n => ((a n : ℤ) : ZMod p)) 1
        (by
          intro r hr
          change ((a (p + r) : ℤ) : ZMod p) = 0
          rw [cast_a_eq_aZ]
          exact aZ_p_add_eq_zero p r hp h_odd hr)
        (by
          change ((a (p - 1) : ℤ) : ZMod p) = 1
          rw [cast_a_eq_aZ]
          exact aZ_top p m hp hp_eq)
      simpa [RingHom.mapMatrix_apply] using hs
    exact (ZMod.intCast_eq_intCast_iff _ _ p).1 (by simpa [m] using hdet_z)
  · have hdet_z : (((Matrix.det (fun i j : Fin p => c (i.val + j.val)) : ℤ) : ZMod p)) = (1 : ZMod p) := by
      change (Int.castRingHom (ZMod p)) (Matrix.det (fun i j : Fin p => c (i.val + j.val))) = _
      rw [RingHom.map_det (Int.castRingHom (ZMod p))]
      have hs := sparse_hankel_det_zmod p m hp_eq (fun n => ((c n : ℤ) : ZMod p)) ((-1 : ZMod p) ^ m)
        (by
          intro r hr
          change ((c (p + r) : ℤ) : ZMod p) = 0
          rw [cast_c_eq_cZ]
          exact cZ_p_add_eq_zero p r hp h_odd hr)
        (by
          change ((c (p - 1) : ℤ) : ZMod p) = (-1 : ZMod p) ^ m
          rw [cast_c_eq_cZ]
          exact cZ_top p m hp hp_eq)
      have hp_odd_pow : ((-1 : ZMod p) ^ m) ^ p = ((-1 : ZMod p) ^ m) := by
        rw [← pow_mul]
        apply neg_one_pow_congr
        rw [Nat.even_mul]
        have hpodd' : Odd p := hp.odd_of_ne_two h_odd
        constructor
        · intro h
          exact h.resolve_right ((Nat.not_even_iff_odd).2 hpodd')
        · intro hm
          exact Or.inl hm
      have hsquare : ((-1 : ZMod p) ^ m) * ((-1 : ZMod p) ^ m) = 1 := by
        rw [← pow_add]
        have he : Even (m+m) := ⟨m, by omega⟩
        simpa using (Even.neg_one_pow (α := ZMod p) he)
      simpa [RingHom.mapMatrix_apply, hp_odd_pow, hsquare] using hs
    exact (ZMod.intCast_eq_intCast_iff _ _ p).1 (by simpa using hdet_z)
