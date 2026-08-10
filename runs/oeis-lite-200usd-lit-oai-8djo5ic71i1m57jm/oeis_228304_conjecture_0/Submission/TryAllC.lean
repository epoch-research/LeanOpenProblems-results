import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix



def aZ (p n : ℕ) : ZMod p :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 4)

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



def cZ (p n : ℕ) : ZMod p :=
  Finset.sum (range (n + 1)) fun k =>
    ((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 2) * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p)

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