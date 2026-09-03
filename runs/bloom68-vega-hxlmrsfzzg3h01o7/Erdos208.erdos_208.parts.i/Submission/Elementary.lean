import FormalConjecturesUtil

/-!
# An elementary squarefree-in-short-interval bound

This file proves an unconditional cubic-scale baseline, not the all-ε
squarefree-gap conjecture.  The proof uses only finite counting: small square
divisors are bounded by a telescoping reciprocal-square sum, and large square
divisors are counted in fibers of the complementary factor.
-/

open Finset

namespace ElementarySquarefree

/-- A length-`L` interval contains at most `L / k + 1` multiples of `k`.
The division in this statement is natural-number division. -/
theorem card_multiples_Ioc_le (x L k : ℕ) :
    ((Ioc x (x + L)).filter (fun n => k ∣ n)).card ≤ L / k + 1 := by
  let s := (Ioc x (x + L)).filter (fun n => k ∣ n)
  change s.card ≤ L / k + 1
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    have ha : a ∈ s := s.min'_mem hs
    have hax : x < a := (mem_Ioc.mp (mem_filter.mp ha).1).1
    have hka : k ∣ a := (mem_filter.mp ha).2
    have hc : s.card ≤ (range (L / k + 1)).card := by
      apply card_le_card_of_injOn (fun n => (n - a) / k)
      · intro n hn
        have hnL : n ≤ x + L := (mem_Ioc.mp (mem_filter.mp hn).1).2
        have hd : n - a ≤ L := by omega
        exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hd))
      · intro n hn n' hn' he
        have han : a ≤ n := s.min'_le n hn
        have han' : a ≤ n' := s.min'_le n' hn'
        have hkn : k ∣ n := (mem_filter.mp (show n ∈ s from hn)).2
        have hkn' : k ∣ n' := (mem_filter.mp (show n' ∈ s from hn')).2
        have hk : k ∣ n - a := Nat.dvd_sub hkn hka
        have hk' : k ∣ n' - a := Nat.dvd_sub hkn' hka
        have he' := congrArg (fun q => q * k) he
        dsimp only at he'
        rw [Nat.div_mul_cancel hk, Nat.div_mul_cancel hk'] at he'
        omega
    simpa only [card_range] using hc
  · have : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    simp [this]

private theorem reciprocal_step (a : ℚ) (ha : 0 < a) :
    1 / (a + 1) ^ 2 ≤ 1 / a - 1 / (a + 1) := by
  have ha1 : 0 < a + 1 := by linarith
  have he : 1 / a - 1 / (a + 1) = 1 / (a * (a + 1)) := by
    field_simp
    ring
  rw [he]
  exact one_div_le_one_div_of_le (mul_pos ha ha1) (by nlinarith)

private theorem sum_reciprocal_sq_le_aux (h : ℕ) (hh : 2 ≤ h) :
    (∑ d ∈ Icc 2 h, (1 : ℚ) / (d : ℚ) ^ 2) ≤ 3 / 4 - 1 / (h : ℚ) := by
  induction h, hh using Nat.le_induction with
  | base => norm_num
  | succ h hh ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hhQ : (0 : ℚ) < h := by exact_mod_cast (show 0 < h by omega)
    have hs := reciprocal_step (h : ℚ) hhQ
    push_cast
    linarith

/-- The elementary finite bound `∑_{d=2}^h 1/d² ≤ 3/4`. -/
theorem sum_reciprocal_sq_le (h : ℕ) :
    (∑ d ∈ Icc 2 h, (1 : ℚ) / (d : ℚ) ^ 2) ≤ 3 / 4 := by
  by_cases hh : 2 ≤ h
  · have hb := sum_reciprocal_sq_le_aux h hh
    have hn : (0 : ℚ) ≤ 1 / (h : ℚ) := by positivity
    linarith
  · rw [Icc_eq_empty_of_lt (by omega)]
    norm_num

/-- Numbers in the interval divisible by a square with base between `2` and `h`. -/
def smallBad (x h : ℕ) : Finset ℕ :=
  (Icc 2 h).biUnion fun d => (Ioc x (x + 8 * h)).filter (fun n => d ^ 2 ∣ n)

/-- The union bound for small square divisors removes at most `7*h` numbers. -/
theorem card_smallBad_le (x h : ℕ) : (smallBad x h).card ≤ 7 * h := by
  have h_each (d : ℕ) :
      (((Ioc x (x + 8 * h)).filter (fun n => d ^ 2 ∣ n)).card : ℚ) ≤
        8 * (h : ℚ) * (1 / (d : ℚ) ^ 2) + 1 := by
    have hc := card_multiples_Ioc_le x (8 * h) (d ^ 2)
    have hcQ :
        (((Ioc x (x + 8 * h)).filter (fun n => d ^ 2 ∣ n)).card : ℚ) ≤
          ((8 * h / d ^ 2 : ℕ) : ℚ) + 1 := by exact_mod_cast hc
    have hd : ((8 * h / d ^ 2 : ℕ) : ℚ) ≤ (8 * h : ℚ) / (d : ℚ) ^ 2 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
        (Nat.cast_div_le (α := ℚ) (m := 8 * h) (n := d ^ 2))
    calc
      _ ≤ ((8 * h / d ^ 2 : ℕ) : ℚ) + 1 := hcQ
      _ ≤ (8 * h : ℚ) / (d : ℚ) ^ 2 + 1 := by linarith
      _ = _ := by ring
  have hc : ((Icc 2 h).card : ℚ) ≤ h := by
    exact_mod_cast (show (Icc 2 h).card ≤ h by rw [Nat.card_Icc]; omega)
  have hs : ((smallBad x h).card : ℚ) ≤ 7 * (h : ℚ) := by
    calc
      _ ≤ ∑ d ∈ Icc 2 h,
          (((Ioc x (x + 8 * h)).filter (fun n => d ^ 2 ∣ n)).card : ℚ) := by
        exact_mod_cast (card_biUnion_le (s := Icc 2 h)
          (t := fun d => (Ioc x (x + 8 * h)).filter (fun n => d ^ 2 ∣ n)))
      _ ≤ ∑ d ∈ Icc 2 h, (8 * (h : ℚ) * (1 / (d : ℚ) ^ 2) + 1) :=
        sum_le_sum fun d _ => h_each d
      _ = 8 * (h : ℚ) * (∑ d ∈ Icc 2 h, (1 : ℚ) / (d : ℚ) ^ 2) +
          (Icc 2 h).card := by
        rw [sum_add_distrib, ← mul_sum]
        simp
      _ ≤ 8 * (h : ℚ) * (3 / 4) + h :=
        add_le_add (mul_le_mul_of_nonneg_left (sum_reciprocal_sq_le h) (by positivity)) hc
      _ = 7 * (h : ℚ) := by ring
  exact_mod_cast hs

/-- Possible bases of large square divisors for a fixed complementary factor. -/
def largeBases (x h m : ℕ) : Finset ℕ :=
  (Ioc h (x + 8 * h)).filter (fun d => x < m * d ^ 2 ∧ m * d ^ 2 ≤ x + 8 * h)

/-- Each positive complementary-factor fiber has at most four possible bases. -/
theorem card_largeBases_le (x h m : ℕ) (hm : 0 < m) :
    (largeBases x h m).card ≤ 4 := by
  let s := largeBases x h m
  change s.card ≤ 4
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    have ha : a ∈ s := s.min'_mem hs
    have hha : h < a := (mem_Ioc.mp (mem_filter.mp ha).1).1
    have hxa : x < m * a ^ 2 := (mem_filter.mp ha).2.1
    have hsub : s ⊆ Icc a (a + 3) := by
      intro d hd
      refine mem_Icc.mpr ⟨s.min'_le d hd, ?_⟩
      have hdx : m * d ^ 2 ≤ x + 8 * h := (mem_filter.mp hd).2.2
      by_contra hnot
      have h4 : a + 4 ≤ d := by omega
      have hsq := Nat.pow_le_pow_left h4 2
      have hsep : a ^ 2 + (8 * h + 1) ≤ d ^ 2 := by nlinarith
      have hmul := Nat.mul_le_mul_left m hsep
      have hpos := Nat.le_mul_of_pos_left (8 * h + 1) hm
      nlinarith
    have hc := card_le_card hsub
    rw [Nat.card_Icc] at hc
    omega
  · have : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    simp [this]

/-- A large-square representation has a small complementary factor. -/
theorem large_factor_le (x h m d : ℕ) (hh : 0 < h)
    (hbound : 8 * (x + 8 * h) ≤ h ^ 3) (hd : h < d)
    (hn : m * d ^ 2 ≤ x + 8 * h) : m ≤ h / 8 := by
  have hs : (8 * m) * h ^ 2 ≤ h * h ^ 2 := by
    calc
      (8 * m) * h ^ 2 ≤ (8 * m) * d ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_of_lt hd) 2)
      _ = 8 * (m * d ^ 2) := by ring
      _ ≤ 8 * (x + 8 * h) := Nat.mul_le_mul_left 8 hn
      _ ≤ h ^ 3 := hbound
      _ = h * h ^ 2 := by ring
  have hb : 8 * m ≤ h := Nat.le_of_mul_le_mul_right hs (pow_pos hh 2)
  exact (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)

/-- The union of the large-square fibers. -/
def largeBad (x h : ℕ) : Finset ℕ :=
  (Icc 1 (h / 8)).biUnion fun m => (largeBases x h m).image (fun d => m * d ^ 2)

/-- The tail union has at most four entries for each of `h / 8` complementary factors. -/
theorem card_largeBad_le (x h : ℕ) : (largeBad x h).card ≤ 4 * (h / 8) := by
  have hc := card_biUnion_le_card_mul (Icc 1 (h / 8))
    (fun m => (largeBases x h m).image (fun d => m * d ^ 2)) 4 (by
      intro m hm
      exact card_image_le.trans (card_largeBases_le x h m (by
        have := (mem_Icc.mp hm).1
        omega)))
  simpa only [Nat.card_Icc, Nat.add_sub_cancel, mul_comm] using hc

/-- Every nonsquarefree number in the interval is counted by one of the two unions. -/
theorem nonsquarefree_mem_union (x h n : ℕ) (hh : 0 < h)
    (hbound : 8 * (x + 8 * h) ≤ h ^ 3)
    (hn : n ∈ Ioc x (x + 8 * h)) (hns : ¬ Squarefree n) :
    n ∈ smallBad x h ∪ largeBad x h := by
  classical
  rw [Nat.squarefree_iff_prime_squarefree] at hns
  push_neg at hns
  obtain ⟨p, hp, hpdvd⟩ := hns
  have hpsq : p ^ 2 ∣ n := by simpa only [pow_two] using hpdvd
  by_cases hph : p ≤ h
  · apply mem_union_left
    apply mem_biUnion.mpr
    exact ⟨p, mem_Icc.mpr ⟨hp.two_le, hph⟩, mem_filter.mpr ⟨hn, hpsq⟩⟩
  · have hhp : h < p := by omega
    obtain ⟨m, hnm⟩ := hpsq
    have hmn : m * p ^ 2 = n := by simpa only [mul_comm] using hnm.symm
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le x) (mem_Ioc.mp hn).1
    have hm : 0 < m := by
      by_contra hm
      have hm0 : m = 0 := by omega
      simp only [hm0, zero_mul] at hmn
      omega
    have hupper : m * p ^ 2 ≤ x + 8 * h := by
      rw [hmn]
      exact (mem_Ioc.mp hn).2
    have hpX : p ≤ x + 8 * h :=
      (Nat.le_self_pow (by decide) p).trans
        ((Nat.le_mul_of_pos_left (p ^ 2) hm).trans hupper)
    have hmB : m ∈ Icc 1 (h / 8) :=
      mem_Icc.mpr ⟨hm, large_factor_le x h m p hh hbound hhp hupper⟩
    have hpB : p ∈ largeBases x h m := by
      apply mem_filter.mpr
      refine ⟨mem_Ioc.mpr ⟨hhp, hpX⟩, ?_⟩
      simpa only [hmn] using mem_Ioc.mp hn
    apply mem_union_right
    apply mem_biUnion.mpr
    exact ⟨m, hmB, mem_image.mpr ⟨p, hpB, hmn⟩⟩

/-- Quantitative finite sieve bound for the nonsquarefree members of the interval. -/
theorem card_nonsquarefree_le (x h : ℕ) (hh : 0 < h)
    (hbound : 8 * (x + 8 * h) ≤ h ^ 3) :
    ((Ioc x (x + 8 * h)).filter (fun n => ¬ Squarefree n)).card ≤
      7 * h + 4 * (h / 8) := by
  calc
    _ ≤ (smallBad x h ∪ largeBad x h).card := by
      apply card_le_card
      intro n hn
      exact nonsquarefree_mem_union x h n hh hbound
        (mem_filter.mp hn).1 (mem_filter.mp hn).2
    _ ≤ (smallBad x h).card + (largeBad x h).card := card_union_le _ _
    _ ≤ 7 * h + 4 * (h / 8) := Nat.add_le_add (card_smallBad_le x h) (card_largeBad_le x h)

/-- An unconditional elementary short-interval theorem for squarefree natural numbers.

The hypothesis is cubic in `h`; this is an `O(x^(1/3))`-scale baseline and does
not establish the all-ε squarefree-gap conjecture. -/
theorem exists_squarefree_in_short_interval (x h : ℕ) (hh : 0 < h)
    (hbound : 8 * (x + 8 * h) ≤ h ^ 3) :
    ∃ n : ℕ, x < n ∧ n ≤ x + 8 * h ∧ Squarefree n := by
  classical
  by_contra he
  have hall : (Ioc x (x + 8 * h)).filter (fun n => ¬ Squarefree n) =
      Ioc x (x + 8 * h) := by
    apply filter_eq_self.mpr
    intro n hn hsq
    exact he ⟨n, (mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2, hsq⟩
  have hc := card_nonsquarefree_le x h hh hbound
  rw [hall, Nat.card_Ioc, Nat.add_sub_cancel_left] at hc
  have hd := Nat.mul_div_le h 8
  omega

end ElementarySquarefree
