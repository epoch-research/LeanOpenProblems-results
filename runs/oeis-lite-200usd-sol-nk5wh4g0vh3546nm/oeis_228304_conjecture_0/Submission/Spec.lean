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

lemma neg_one_pow_sub_of_odd {n k : ℕ} (hn : Odd n) (hk : k ≤ n) :
    (-1 : ℤ) ^ (n - k) = - ((-1 : ℤ) ^ k) := by
  rcases Nat.even_or_odd k with hk' | hk'
  · have hs : Odd (n - k) := by
      obtain ⟨u, hu⟩ := hn
      obtain ⟨v, hv⟩ := hk'
      exact ⟨u - v, by omega⟩
    rw [(neg_one_pow_eq_one_iff_even (R := ℤ) (by norm_num)).2 hk',
      (neg_one_pow_eq_neg_one_iff_odd (R := ℤ) (by norm_num)).2 hs]
  · have hs : Even (n - k) := by
      obtain ⟨u, hu⟩ := hn
      obtain ⟨v, hv⟩ := hk'
      exact ⟨u - v, by omega⟩
    rw [(neg_one_pow_eq_neg_one_iff_odd (R := ℤ) (by norm_num)).2 hk',
      (neg_one_pow_eq_one_iff_even (R := ℤ) (by norm_num)).2 hs]
    norm_num

lemma a_odd {n : ℕ} (hn : Odd n) : a n = 0 := by
  classical
  apply Finset.sum_involution (s := range (n + 1))
    (g := fun k _ => n - k)
  · intro k hk
    have hkn : k ≤ n := by simpa using hk
    rw [neg_one_pow_sub_of_odd hn hkn, Nat.choose_symm hkn]
    ring
  · intro k hk hne
    have hkn : k ≤ n := by simpa using hk
    intro hfix
    have : Even n := ⟨k, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hn) this
  · intro k hk
    have hkn : k ≤ n := by simpa using hk
    simp only [mem_range]
    omega
  · intro k hk
    have hkn : k ≤ n := by simpa using hk
    omega

lemma c_odd {n : ℕ} (hn : Odd n) : c n = 0 := by
  classical
  apply Finset.sum_involution (s := range (n + 1))
    (g := fun k _ => n - k)
  · intro k hk
    have hkn : k ≤ n := by simpa using hk
    rw [neg_one_pow_sub_of_odd hn hkn, Nat.choose_symm hkn]
    have hsub : n - (n - k) = k := by omega
    rw [hsub]
    ring
  · intro k hk hne
    have hkn : k ≤ n := by simpa using hk
    intro hfix
    have : Even n := ⟨k, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hn) this
  · intro k hk
    have hkn : k ≤ n := by simpa using hk
    simp only [mem_range]

    omega
  · intro k hk
    have hkn : k ≤ n := by simpa using hk
    omega

lemma choose_add_prime_left {p s k : ℕ} (hp : Nat.Prime p) (hs : s < p) (hk : k ≤ s) :
    ((choose (p + s) k : ℕ) : ZMod p) = choose s k := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := p + s) (k := k) (p := p)
  rw [← ZMod.intCast_eq_intCast_iff] at h
  norm_num [Nat.add_mod, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt (hk.trans_lt hs),
    Nat.add_div (Nat.pos_of_ne_zero hp.ne_zero), Nat.div_eq_of_lt hs,
    Nat.div_eq_of_lt (hk.trans_lt hs)] at h ⊢
  exact h

lemma choose_add_prime_both {p s k : ℕ} (hp : Nat.Prime p) (hs : s < p) (hk : k ≤ s) :
    ((choose (p + s) (p + k) : ℕ) : ZMod p) = choose s k := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := p + s) (k := p + k) (p := p)
  rw [← ZMod.intCast_eq_intCast_iff] at h
  norm_num [Nat.add_mod, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt (hk.trans_lt hs),
    Nat.add_div (Nat.pos_of_ne_zero hp.ne_zero), Nat.div_eq_of_lt hs,
    Nat.div_eq_of_lt (hk.trans_lt hs), Nat.div_self hp.pos,
    if_neg (not_le.mpr hs), if_neg (not_le.mpr (hk.trans_lt hs))] at h ⊢
  exact h

lemma choose_add_prime_middle {p s k : ℕ} (hp : Nat.Prime p) (hs : s < p)
    (hsk : s < k) (hkp : k < p) : ((choose (p + s) k : ℕ) : ZMod p) = 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := p + s) (k := k) (p := p)
  rw [← ZMod.intCast_eq_intCast_iff] at h
  norm_num [Nat.add_mod, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hkp,
    Nat.add_div (Nat.pos_of_ne_zero hp.ne_zero), Nat.div_eq_of_lt hs,
    Nat.div_eq_of_lt hkp, Nat.choose_eq_zero_of_lt hsk] at h ⊢
  exact h


lemma neg_one_pow_prime {R : Type*} [Ring R] {p : ℕ} (hp : Odd p)
    (hne : (-1 : R) ≠ 1) : (-1 : R) ^ p = -1 := by
  exact (neg_one_pow_eq_neg_one_iff_odd (R := R) hne).2 hp

lemma a_add_prime_odd (p s : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hs : s < p) : ((a (p + s) : ℤ) : ZMod p) = 0 := by
  classical
  have hpodd : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left hp2)
  have hp1 : p ≠ 1 := hp.ne_one
  have hpgt2 : 2 < p := by have := hp.two_le; omega
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Nontrivial (ZMod p) := ZMod.nontrivial_iff.mpr hp1
  letI : Fact (2 < p) := ⟨hpgt2⟩
  let f : ℕ → ZMod p := fun k => (-1) ^ k * (choose (p + s) k : ZMod p) ^ 4
  have ha : ((a (p + s) : ℤ) : ZMod p) = ∑ k ∈ range (p + s + 1), f k := by
    simp [a, f]
  rw [ha]
  let g : ℕ → ℕ := fun k => if k ≤ s then p + k else if p ≤ k then k - p else k
  apply Finset.sum_involution (fun k _ => g k)
  · intro k hk
    have hbound : k ≤ p + s := by simpa using hk
    simp only [f, g]
    by_cases hks : k ≤ s
    · simp only [hks, ↓reduceIte]
      rw [choose_add_prime_left hp hs hks, choose_add_prime_both hp hs hks, pow_add,
        neg_one_pow_prime (R := ZMod p) hpodd ZMod.neg_one_ne_one]
      ring
    · simp only [hks, ↓reduceIte]
      by_cases hpk : p ≤ k
      · simp only [hpk, ↓reduceIte]
        have hl : k - p ≤ s := by omega
        have hkform : k = p + (k - p) := by omega
        rw [hkform, choose_add_prime_both hp hs hl, Nat.add_sub_cancel_left,
          choose_add_prime_left hp hs hl, pow_add,
          neg_one_pow_prime (R := ZMod p) hpodd ZMod.neg_one_ne_one]
        ring
      · simp only [hpk, ↓reduceIte]
        have hsp : s < k := by omega
        have hkp : k < p := by omega
        rw [choose_add_prime_middle hp hs hsp hkp]
        simp
  · intro k hk
    simp only [f, g]
    by_cases hks : k ≤ s
    · simp only [hks, ↓reduceIte]
      omega
    · by_cases hpk : p ≤ k
      · simp only [hks, hpk, ↓reduceIte]
        omega
      · simp only [hks, hpk, ↓reduceIte]
        intro hzero
        have hsp : s < k := by omega
        have hkp : k < p := by omega
        rw [choose_add_prime_middle hp hs hsp hkp] at hzero
        simp at hzero
  · intro k hk
    have hbound : k ≤ p + s := by simpa using hk
    simp only [g]
    by_cases hks : k ≤ s
    · simp only [hks, ↓reduceIte, mem_range]
      omega
    · by_cases hpk : p ≤ k
      · simp only [hks, hpk, ↓reduceIte, mem_range]
        omega
      · simp only [hks, hpk, ↓reduceIte]
        exact hk
  · intro k hk
    have hbound : k ≤ p + s := by simpa using hk
    simp only [g]
    by_cases hks : k ≤ s
    · have hps : ¬ p + k ≤ s := by omega
      have hpp : p ≤ p + k := by omega
      simp [hks, hps, hpp]
    · by_cases hpk : p ≤ k
      · have hl : k - p ≤ s := by omega
        simp [hks, hpk, hl]
      · simp [hks, hpk]


lemma central_add_prime (p r : ℕ) (hp : Nat.Prime p) (hr : r < p) :
    ((choose (2 * (p + r)) (p + r) : ℕ) : ZMod p) =
      2 * (choose (2 * r) r : ZMod p) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hbig := Choose.choose_modEq_choose_mod_mul_choose_div
    (n := 2 * (p + r)) (k := p + r) (p := p)
  have hsmall := Choose.choose_modEq_choose_mod_mul_choose_div
    (n := 2 * r) (k := r) (p := p)
  rw [← ZMod.intCast_eq_intCast_iff] at hbig hsmall
  by_cases h : 2 * r < p
  · have hn : 2 * (p + r) = 2 * r + p * 2 := by omega
    have hk : p + r = r + p * 1 := by omega
    have hm : 2 * (p + r) % p = 2 * r := by
      rw [hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
    have hd : 2 * (p + r) / p = 2 := by
      rw [hn, Nat.add_mul_div_left _ _ hp.pos, Nat.div_eq_of_lt h]
    have hkm : (p + r) % p = r := by
      rw [hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    have hkd : (p + r) / p = 1 := by
      rw [hk, Nat.add_mul_div_left _ _ hp.pos, Nat.div_eq_of_lt hr]
    rw [hm, hd, hkm, hkd] at hbig
    simpa [mul_comm] using hbig
  · have hl : 2 * r - p < r := by omega
    have hn : 2 * (p + r) = (2 * r - p) + p * 3 := by omega
    have hn' : 2 * r = (2 * r - p) + p * 1 := by omega
    have hk : p + r = r + p * 1 := by omega
    have hlp : 2 * r - p < p := by omega
    have hm : 2 * (p + r) % p = 2 * r - p := by
      rw [hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlp]
    have hd : 2 * (p + r) / p = 3 := by
      rw [hn, Nat.add_mul_div_left _ _ hp.pos, Nat.div_eq_of_lt hlp]
    have hsm : 2 * r % p = 2 * r - p := by
      calc
        2 * r % p = ((2 * r - p) + p * 1) % p := congrArg (fun x => x % p) hn'
        _ = (2 * r - p) % p := Nat.add_mul_mod_self_left _ _ _
        _ = 2 * r - p := Nat.mod_eq_of_lt hlp
    have hsd : 2 * r / p = 1 := by
      calc
        2 * r / p = ((2 * r - p) + p * 1) / p := congrArg (fun x => x / p) hn'
        _ = (2 * r - p) / p + 1 := Nat.add_mul_div_left _ _ hp.pos
        _ = 1 := by rw [Nat.div_eq_of_lt hlp]
    have hkm : (p + r) % p = r := by
      rw [hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    have hkd : (p + r) / p = 1 := by
      rw [hk, Nat.add_mul_div_left _ _ hp.pos, Nat.div_eq_of_lt hr]
    rw [hm, hd, hkm, hkd] at hbig
    rw [hsm, hsd, Nat.mod_eq_of_lt hr, Nat.div_eq_of_lt hr] at hsmall
    have hz : choose (2 * r - p) r = 0 := Nat.choose_eq_zero_of_lt hl
    simp [hz] at hbig hsmall
    simp [hbig, hsmall]

lemma c_add_prime_odd (p s : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hs : s < p) : ((c (p + s) : ℤ) : ZMod p) = 0 := by
  classical
  have hpodd : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left hp2)
  have hpgt2 : 2 < p := by have := hp.two_le; omega
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Nontrivial (ZMod p) := ZMod.nontrivial_iff.mpr hp.ne_one
  letI : Fact (2 < p) := ⟨hpgt2⟩
  let f : ℕ → ZMod p := fun k =>
    (-1) ^ k * (choose (p + s) k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) *
      (choose (2 * ((p + s) - k)) ((p + s) - k) : ZMod p)
  have hc : ((c (p + s) : ℤ) : ZMod p) = ∑ k ∈ range (p + s + 1), f k := by
    simp [c, f]
  rw [hc]
  let g : ℕ → ℕ := fun k => if k ≤ s then p + k else if p ≤ k then k - p else k
  apply Finset.sum_involution (fun k _ => g k)
  · intro k hk
    have hbound : k ≤ p + s := by simpa using hk
    simp only [f, g]
    by_cases hks : k ≤ s
    · simp only [hks, ↓reduceIte]
      have hsub : p + s - k = p + (s - k) := by omega
      have hsub' : p + s - (p + k) = s - k := by omega
      rw [choose_add_prime_left hp hs hks, choose_add_prime_both hp hs hks,
        hsub, hsub', central_add_prime p (s - k) hp (by omega),
        central_add_prime p k hp (hks.trans_lt hs), pow_add,
        neg_one_pow_prime (R := ZMod p) hpodd ZMod.neg_one_ne_one]
      ring
    · simp only [hks, ↓reduceIte]
      by_cases hpk : p ≤ k
      · simp only [hpk, ↓reduceIte]
        have hl : k - p ≤ s := by omega
        have hkform : k = p + (k - p) := by omega
        have hsub : p + s - (p + (k - p)) = s - (k - p) := by omega
        have hsub' : p + s - (k - p) = p + (s - (k - p)) := by omega
        rw [hkform, choose_add_prime_both hp hs hl, Nat.add_sub_cancel_left,
          choose_add_prime_left hp hs hl, hsub, hsub',
          central_add_prime p (k - p) hp (hl.trans_lt hs),
          central_add_prime p (s - (k - p)) hp (by omega), pow_add,
          neg_one_pow_prime (R := ZMod p) hpodd ZMod.neg_one_ne_one]
        ring
      · simp only [hpk, ↓reduceIte]
        have hsp : s < k := by omega
        have hkp : k < p := by omega
        rw [choose_add_prime_middle hp hs hsp hkp]
        simp
  · intro k hk
    simp only [f, g]
    by_cases hks : k ≤ s
    · simp only [hks, ↓reduceIte]
      omega
    · by_cases hpk : p ≤ k
      · simp only [hks, hpk, ↓reduceIte]
        omega
      · simp only [hks, hpk, ↓reduceIte]
        intro hzero
        have hsp : s < k := by omega
        have hkp : k < p := by omega
        rw [choose_add_prime_middle hp hs hsp hkp] at hzero
        simp at hzero
  · intro k hk
    have hbound : k ≤ p + s := by simpa using hk
    simp only [g]
    by_cases hks : k ≤ s
    · simp only [hks, ↓reduceIte, mem_range]
      omega
    · by_cases hpk : p ≤ k
      · simp only [hks, hpk, ↓reduceIte, mem_range]
        omega
      · simp only [hks, hpk, ↓reduceIte]
        exact hk
  · intro k hk
    have hbound : k ≤ p + s := by simpa using hk
    simp only [g]
    by_cases hks : k ≤ s
    · have hps : ¬ p + k ≤ s := by omega
      have hpp : p ≤ p + k := by omega
      simp [hks, hps, hpp]
    · by_cases hpk : p ≤ k
      · have hl : k - p ≤ s := by omega
        simp [hks, hpk, hl]
      · simp [hks, hpk]

lemma choose_prime_pred (p k : ℕ) (hp : Nat.Prime p) (hk : k < p) :
    (choose (p - 1) k : ZMod p) = (-1 : ZMod p) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k < p := by omega
      have hkp : k + 1 ≠ 0 := by omega
      have hd := hp.dvd_choose_self hkp hk
      obtain ⟨q, hq⟩ := hd
      have hpform : p = (p - 1) + 1 := by omega
      have hpascal : choose p (k + 1) = choose (p - 1) k + choose (p - 1) (k + 1) := by
        conv_lhs => rw [hpform]
        exact Nat.choose_succ_succ (p - 1) k
      have hz : (choose p (k + 1) : ZMod p) = 0 := by
        rw [hq]
        simp
      rw [hpascal, Nat.cast_add] at hz
      rw [pow_succ, ← ih hk']
      linear_combination hz

lemma central_zero (p r : ℕ) (hp : Nat.Prime p) (hr : r < p) (hpr : p ≤ 2 * r) :
    (choose (2 * r) r : ZMod p) = 0 := by
  have hd : p ∣ choose (2 * r) r := hp.dvd_choose hr (by omega) hpr
  obtain ⟨q, hq⟩ := hd
  rw [hq]
  simp

lemma a_prime_pred (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    ((a (p - 1) : ℤ) : ZMod p) = 1 := by
  classical
  have hodd : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left hp2)
  simp only [a, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]
  have hrange : p - 1 + 1 = p := by have := hp.pos; omega
  rw [hrange]
  have hchoose : ∀ k ∈ range p, (choose (p - 1) k : ZMod p) = (-1 : ZMod p) ^ k := by
    intro k hk
    exact choose_prime_pred p k hp (by simpa using hk)
  have heq : (∑ k ∈ range p, (-1 : ZMod p) ^ k * (choose (p - 1) k : ZMod p) ^ 4) =
      ∑ k ∈ range p, (-1 : ZMod p) ^ k := by
    apply sum_congr rfl
    intro k hk
    rw [hchoose k hk]
    rw [← pow_mul, show k * 4 = 4 * k by omega, pow_mul]
    norm_num
  rw [heq]
  have hsum := Fin.sum_neg_one_pow (ZMod p) p
  rw [if_neg (Nat.not_even_iff_odd.mpr hodd)] at hsum
  rw [Fin.sum_univ_eq_sum_range] at hsum
  simpa using hsum

lemma c_prime_pred_aux (p m : ℕ) (hp : Nat.Prime p) (hpm : p = 2 * m + 1) :
    ((c (p - 1) : ℤ) : ZMod p) = (-1 : ZMod p) ^ m := by
  classical
  simp only [c, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]
  have hrange : p - 1 + 1 = p := by omega
  rw [hrange]
  let f : ℕ → ZMod p := fun k =>
    (-1) ^ k * (choose (p - 1) k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) *
      (choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p)
  change (∑ k ∈ range p, f k) = _
  have hsingle : (∑ k ∈ range p, f k) = f m := by
    apply Finset.sum_eq_single m
    · intro k hk hkm
      dsimp only [f]
      have hkp : k < p := by simpa using hk
      rcases lt_or_gt_of_ne hkm with hkm' | hmk
      · have hrlt : p - 1 - k < p := by omega
        have hpr : p ≤ 2 * (p - 1 - k) := by omega
        rw [central_zero p (p - 1 - k) hp hrlt hpr]
        simp
      · have hpr : p ≤ 2 * k := by omega
        rw [central_zero p k hp hkp hpr]
        simp
    · intro hmnot
      exfalso
      apply hmnot
      simp only [mem_range]
      omega
  rw [hsingle]
  dsimp only [f]
  have hmp : m < p := by omega
  rw [choose_prime_pred p m hp hmp]
  have hsub : p - 1 - m = m := by omega
  have htwo : 2 * m = p - 1 := by omega
  rw [hsub, htwo, choose_prime_pred p m hp hmp]
  rw [← pow_mul, show m * 2 = 2 * m by omega, pow_mul]
  norm_num
  rw [← pow_add, show m + m = 2 * m by omega, pow_mul]
  norm_num

lemma c_prime_pred (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    ((c (p - 1) : ℤ) : ZMod p) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
  have hodd : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left hp2)
  obtain ⟨m, hm⟩ := hodd
  have hdiv : (p - 1) / 2 = m := by omega
  rw [hdiv]
  apply c_prime_pred_aux p m hp
  omega

lemma sign_revPerm_odd (m : ℕ) :
    Equiv.Perm.sign (@Fin.revPerm (2 * m + 1)) = (-1 : ℤˣ) ^ m := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  have hinner (j : Fin (2 * m + 1)) :
      (∏ i ∈ Finset.Iio j,
        (if (@Fin.revPerm (2 * m + 1)) i < (@Fin.revPerm (2 * m + 1)) j then 1 else -1)) =
        (-1 : ℤˣ) ^ j.val := by
    have hn : ∀ i ∈ Finset.Iio j,
        ¬(@Fin.revPerm (2 * m + 1)) i < (@Fin.revPerm (2 * m + 1)) j := by
      intro i hi
      rw [Fin.revPerm_apply, Fin.revPerm_apply, Fin.rev_lt_rev]
      exact not_lt_of_ge (le_of_lt (Finset.mem_Iio.mp hi))
    calc
      _ = ∏ _i ∈ Finset.Iio j, (-1 : ℤˣ) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [if_neg (hn i hi)]
      _ = (-1 : ℤˣ) ^ j.val := by simp [Fin.card_Iio]
  simp_rw [hinner]
  have hprod := Finset.prod_pow_eq_pow_sum Finset.univ
    (fun x : Fin (2 * m + 1) => x.val) (-1 : ℤˣ)
  rw [hprod]
  have hsum : (∑ x : Fin (2 * m + 1), x.val) = (2 * m + 1) * (2 * m) / 2 := by
    calc
      (∑ x : Fin (2 * m + 1), x.val) = ∑ k ∈ range (2 * m + 1), k :=
        Fin.sum_univ_eq_sum_range (fun k : ℕ => k) (2 * m + 1)
      _ = (2 * m + 1) * ((2 * m + 1) - 1) / 2 := Finset.sum_range_id _
      _ = (2 * m + 1) * (2 * m) / 2 := by
        rw [show (2 * m + 1) - 1 = 2 * m by omega]
  rw [hsum]
  have he : (2 * m + 1) * (2 * m) / 2 = (2 * m + 1) * m := by
    rw [show (2 * m + 1) * (2 * m) = ((2 * m + 1) * m) * 2 by ring,
      Nat.mul_div_cancel _ (by omega)]
  rw [he, pow_mul]
  norm_num

lemma det_antiTriangular_odd {R : Type*} [CommRing R] (m : ℕ)
    (M : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) R) (x : R)
    (hzero : ∀ i j, 2 * m < i.val + j.val → M i j = 0)
    (hanti : ∀ i, M i i.rev = x) :
    M.det = (-1 : R) ^ m * x ^ (2 * m + 1) := by
  classical
  let N : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) R :=
    M.submatrix (@Fin.revPerm (2 * m + 1)) id
  have hN : N.BlockTriangular OrderDual.toDual := by
    intro i j hij
    change M i.rev j = 0
    apply hzero
    have hij' : i < j := hij
    have hrev : i.rev.val + i.val = 2 * m := Fin.rev_add_cast i
    omega
  have hdiag : ∀ i, N i i = x := by
    intro i
    change M i.rev i = x
    simpa using hanti i.rev
  have hdetN : N.det = x ^ (2 * m + 1) := by
    rw [Matrix.det_of_lowerTriangular N hN]
    simp_rw [hdiag]
    simp
  have hback : N.submatrix (@Fin.revPerm (2 * m + 1)) id = M := by
    ext i j
    simp [N, Matrix.submatrix]
  have hperm := Matrix.det_permute (@Fin.revPerm (2 * m + 1)) N
  rw [hback, hdetN, sign_revPerm_odd m] at hperm
  simpa using hperm


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
  dsimp
  have hpodd : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left h_odd)
  obtain ⟨m, hm⟩ := hpodd
  have hhalf : (p - 1) / 2 = m := by omega
  have hpform : p = 2 * m + 1 := by omega
  subst p
  have hp2 : 2 * m + 1 ≠ 2 := h_odd
  constructor
  · rw [← ZMod.intCast_eq_intCast_iff]
    rw [hhalf]
    let A : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℤ :=
      fun i j => a (i.val + j.val)
    let AZ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) (ZMod (2 * m + 1)) :=
      A.map (Int.castRingHom (ZMod (2 * m + 1)))
    have hAZ : AZ.det = (-1 : ZMod (2 * m + 1)) ^ m := by
      have hdet := det_antiTriangular_odd m AZ (1 : ZMod (2 * m + 1))
      have hz : ∀ i j, 2 * m < i.val + j.val → AZ i j = 0 := by
        intro i j hij
        change ((a (i.val + j.val) : ℤ) : ZMod (2 * m + 1)) = 0
        let s := i.val + j.val - (2 * m + 1)
        have hs : s < 2 * m + 1 := by
          dsimp only [s]
          omega
        have heq : i.val + j.val = (2 * m + 1) + s := by
          dsimp only [s]
          omega
        rw [heq]
        exact a_add_prime_odd (2 * m + 1) s hp hp2 hs
      have ha : ∀ i, AZ i i.rev = (1 : ZMod (2 * m + 1)) := by
        intro i
        change ((a (i.val + i.rev.val) : ℤ) : ZMod (2 * m + 1)) = 1
        rw [Fin.add_rev_cast]
        exact a_prime_pred (2 * m + 1) hp hp2
      simpa using hdet hz ha
    change (Int.castRingHom (ZMod (2 * m + 1))) A.det = _
    rw [RingHom.map_det]
    change AZ.det = _
    simpa using hAZ
  · rw [← ZMod.intCast_eq_intCast_iff]
    let C : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℤ :=
      fun i j => c (i.val + j.val)
    let CZ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) (ZMod (2 * m + 1)) :=
      C.map (Int.castRingHom (ZMod (2 * m + 1)))
    have hCZ : CZ.det = 1 := by
      have hdet := det_antiTriangular_odd m CZ ((-1 : ZMod (2 * m + 1)) ^ m)
      have hz : ∀ i j, 2 * m < i.val + j.val → CZ i j = 0 := by
        intro i j hij
        change ((c (i.val + j.val) : ℤ) : ZMod (2 * m + 1)) = 0
        let s := i.val + j.val - (2 * m + 1)
        have hs : s < 2 * m + 1 := by
          dsimp only [s]
          omega
        have heq : i.val + j.val = (2 * m + 1) + s := by
          dsimp only [s]
          omega
        rw [heq]
        exact c_add_prime_odd (2 * m + 1) s hp hp2 hs
      have hc : ∀ i, CZ i i.rev = (-1 : ZMod (2 * m + 1)) ^ m := by
        intro i
        change ((c (i.val + i.rev.val) : ℤ) : ZMod (2 * m + 1)) = _
        rw [Fin.add_rev_cast]
        have he := c_prime_pred (2 * m + 1) hp hp2
        have hd : (2 * m + 1 - 1) / 2 = m := by omega
        simpa [hd] using he
      have hd := hdet hz hc
      rw [hd]
      rw [← pow_mul]
      have he : m * (2 * m + 1) = m + 2 * (m * m) := by ring
      rw [he, pow_add]
      norm_num [pow_mul]
      rw [← pow_add, show m + m = 2 * m by omega, pow_mul]
      norm_num
    change (Int.castRingHom (ZMod (2 * m + 1))) C.det = 1
    rw [RingHom.map_det]
    exact hCZ
