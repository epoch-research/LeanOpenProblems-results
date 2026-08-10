import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix



def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 4)

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
