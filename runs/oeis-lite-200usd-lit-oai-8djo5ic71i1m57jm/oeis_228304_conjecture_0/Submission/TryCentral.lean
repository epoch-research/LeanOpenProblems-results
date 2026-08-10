import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

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
