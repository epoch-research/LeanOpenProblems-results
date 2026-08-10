import FormalConjectures.Util.ProblemImports

open Rat Nat Finset

theorem pvn_add_one_le {p j : ℕ} [Fact p.Prime] (hj : 1 ≤ j) :
    padicValNat p j + 1 ≤ j := by
  have hp : 1 < p := (Fact.out (p := p.Prime)).one_lt
  have hdvd : p ^ padicValNat p j ∣ j := pow_padicValNat_dvd
  have hle : p ^ padicValNat p j ≤ j := Nat.le_of_dvd (by omega) hdvd
  have hlt : padicValNat p j < p ^ padicValNat p j := Nat.lt_pow_self hp
  omega

theorem three_pow_ge {k : ℕ} (hk : 1 ≤ k) : k + 2 ≤ 3 ^ k := by
  induction k with
  | zero => omega
  | succ d hd =>
    rcases Nat.lt_or_ge d 1 with h | h
    · interval_cases d <;> norm_num
    · have hd1 : 1 ≤ d := by omega
      have := hd hd1
      have : 3 ^ (d+1) = 3 * 3 ^ d := by ring
      omega

theorem pvn_add_two_le {p j : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) (hj : 2 ≤ j) :
    padicValNat p j + 2 ≤ j := by
  set k := padicValNat p j with hk
  have hdvd : p ^ k ∣ j := pow_padicValNat_dvd
  have hle : p ^ k ≤ j := Nat.le_of_dvd (by omega) hdvd
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · omega
  · have h3 : (3:ℕ) ^ k ≤ p ^ k := Nat.pow_le_pow_left hp3 k
    have := three_pow_ge hk1
    omega

theorem choose_nat_id (m i : ℕ) (hi : i ≤ m) :
    (m+1).choose i * (m+1-i) = (m+1) * m.choose i := by
  have h1 := Nat.add_one_mul_choose_eq m i
  have h2 := Nat.choose_succ_right_eq (m+1) i
  -- h1 : (m+1) * m.choose i = (m+1).choose (i+1) * (i+1)
  -- h2 : (m+1).choose (i+1) * (i+1) = (m+1).choose i * ((m+1) - i)
  omega

theorem choose_cast_id (m i : ℕ) (hi : i ≤ m) :
    (((m+1).choose i : ℕ) : ℚ) * (((m+1-i : ℕ)) : ℚ)
      = (((m.choose i : ℕ)) : ℚ) * ((m+1 : ℕ) : ℚ) := by
  have := choose_nat_id m i hi
  exact_mod_cast (this.trans (Nat.mul_comm _ _))

/-- The p-adic valuation of a Faulhaber term. -/
theorem term_val_eq {p : ℕ} [Fact p.Prime] (m i : ℕ) (hi : i ≤ m) (hb : bernoulli i ≠ 0) :
    padicValRat p (bernoulli i * (((m+1).choose i : ℕ) : ℚ) * ((p:ℕ) : ℚ)^(m+1-i) / ((m+1 : ℕ) : ℚ))
    = padicValRat p (bernoulli i) + (padicValNat p (m.choose i) : ℤ)
      + ((m+1-i : ℕ) : ℤ) - (padicValNat p (m+1-i) : ℤ) := by
  have hp1 : 1 < p := (Fact.out (p := p.Prime)).one_lt
  have hpQ : ((p:ℕ):ℚ) ≠ 0 := by exact_mod_cast (Fact.out (p := p.Prime)).ne_zero
  have hC' : ((m.choose i : ℕ) : ℚ) ≠ 0 := by
    have : 0 < m.choose i := Nat.choose_pos hi
    positivity
  have hd1 : ((m+1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hposj : 0 < m+1-i := by omega
  have hd2 : (((m+1-i : ℕ)) : ℚ) ≠ 0 := by positivity
  have hpowne : ((p:ℕ):ℚ)^(m+1-i) ≠ 0 := pow_ne_zero _ hpQ
  -- rewrite the term
  have hterm : bernoulli i * (((m+1).choose i : ℕ) : ℚ) * ((p:ℕ) : ℚ)^(m+1-i) / ((m+1 : ℕ) : ℚ)
      = bernoulli i * (((m.choose i : ℕ)) : ℚ) * ((p:ℕ) : ℚ)^(m+1-i) / (((m+1-i : ℕ)) : ℚ) := by
    rw [div_eq_div_iff hd1 hd2]
    have key := choose_cast_id m i hi
    linear_combination (bernoulli i * ((p:ℕ):ℚ)^(m+1-i)) * key
  rw [hterm]
  rw [padicValRat.div (by positivity) hd2, padicValRat.mul (by positivity) hpowne,
      padicValRat.mul hb hC']
  rw [padicValRat.pow hpQ, padicValRat.self hp1, mul_one]
  rw [padicValRat.of_nat, padicValRat.of_nat]


/-- The p-adic valuation of a Faulhaber term with a general base `b`. -/
theorem term_val_base {p : ℕ} [Fact p.Prime] (b m i : ℕ) (hb0 : b ≠ 0) (hi : i ≤ m)
    (hb : bernoulli i ≠ 0) :
    padicValRat p (bernoulli i * (((m+1).choose i : ℕ) : ℚ) * ((b:ℕ) : ℚ)^(m+1-i) / ((m+1 : ℕ) : ℚ))
    = padicValRat p (bernoulli i) + (padicValNat p (m.choose i) : ℤ)
      + ((m+1-i : ℕ) : ℤ) * (padicValNat p b : ℤ) - (padicValNat p (m+1-i) : ℤ) := by
  have hbQ : ((b:ℕ):ℚ) ≠ 0 := by exact_mod_cast hb0
  have hC' : ((m.choose i : ℕ) : ℚ) ≠ 0 := by
    have : 0 < m.choose i := Nat.choose_pos hi
    positivity
  have hd1 : ((m+1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hposj : 0 < m+1-i := by omega
  have hd2 : (((m+1-i : ℕ)) : ℚ) ≠ 0 := by positivity
  have hpowne : ((b:ℕ):ℚ)^(m+1-i) ≠ 0 := pow_ne_zero _ hbQ
  have hterm : bernoulli i * (((m+1).choose i : ℕ) : ℚ) * ((b:ℕ) : ℚ)^(m+1-i) / ((m+1 : ℕ) : ℚ)
      = bernoulli i * (((m.choose i : ℕ)) : ℚ) * ((b:ℕ) : ℚ)^(m+1-i) / (((m+1-i : ℕ)) : ℚ) := by
    rw [div_eq_div_iff hd1 hd2]
    have key := choose_cast_id m i hi
    linear_combination (bernoulli i * ((b:ℕ):ℚ)^(m+1-i)) * key
  rw [hterm]
  rw [padicValRat.div (by positivity) hd2, padicValRat.mul (by positivity) hpowne,
      padicValRat.mul hb hC']
  rw [padicValRat.pow hbQ]
  rw [padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat]

/-- Helper: lower bound on p-adic valuation of a finite sum, allowing zero terms. -/
theorem padic_sum_ge {p : ℕ} [Fact p.Prime] {ι : Type*} (S : Finset ι) (F : ι → ℚ) (c : ℤ)
    (h : ∀ i ∈ S, F i = 0 ∨ c ≤ padicValRat p (F i)) :
    (∑ i ∈ S, F i) = 0 ∨ c ≤ padicValRat p (∑ i ∈ S, F i) := by
  classical
  induction S using Finset.induction with
  | empty => left; simp
  | insert s S' hs ih =>
    rw [Finset.sum_insert hs]
    have hFs := h s (Finset.mem_insert_self s S')
    have ihres := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    rcases hFs with hFs0 | hFsc
    · rw [hFs0, zero_add]; exact ihres
    · rcases ihres with hsum0 | hsumc
      · rw [hsum0, add_zero]; right; exact hFsc
      · by_cases hz : F s + ∑ i ∈ S', F i = 0
        · left; exact hz
        · right
          refine le_trans (le_min hFsc hsumc) (padicValRat.min_le_padicValRat_add hz)

/-- The last Faulhaber term (i = m) equals `bernoulli m * p`. -/
theorem faulhaber_last (p m : ℕ) :
    bernoulli m * (((m+1).choose m : ℕ) : ℚ) * ((p:ℕ) : ℚ)^(m+1-m) / ((m+1 : ℕ) : ℚ)
      = bernoulli m * ((p:ℕ) : ℚ) := by
  have hcm : (m+1).choose m = m+1 := Nat.choose_succ_self_right m
  have hsub : m+1-m = 1 := by omega
  rw [hcm, hsub, pow_one]
  have : ((m+1 : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp

/-- The Faulhaber equation with the top term split off. -/
theorem faulhaber_split (p m : ℕ) :
    ((∑ k ∈ Finset.range p, (k : ℚ)^m) : ℚ)
      = (∑ i ∈ Finset.range m,
          bernoulli i * (((m+1).choose i : ℕ) : ℚ) * ((p:ℕ) : ℚ)^(m+1-i) / ((m+1 : ℕ) : ℚ))
        + bernoulli m * ((p:ℕ) : ℚ) := by
  have hF := sum_range_pow p m
  rw [Finset.sum_range_succ] at hF
  simp only [show ((m:ℚ)+1) = ((m+1:ℕ):ℚ) from by push_cast; ring] at hF
  rw [hF, faulhaber_last]

theorem sum_range_zmod (p : ℕ) [NeZero p] (f : ZMod p → ZMod p) :
    (∑ k ∈ range p, f (k : ZMod p)) = ∑ x : ZMod p, f x := by
  refine Finset.sum_nbij' (fun k => (k : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact mem_univ _
  · intro a _; simp [ZMod.val_lt]
  · intro a ha; exact ZMod.val_cast_of_lt (mem_range.mp ha)
  · intro a _; simp [ZMod.natCast_val, ZMod.cast_id]
  · intro a _; rfl

theorem univ_sum_pow_zmod (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : 1 ≤ m) :
    (∑ x : ZMod p, x ^ m) = if (p - 1) ∣ m then -1 else 0 := by
  classical
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  let emb : (ZMod p)ˣ ↪ ZMod p := ⟨fun x => x, Units.val_injective⟩
  have hmap : univ.map emb = univ \ {0} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, emb] using isUnit_iff_ne_zero
  calc ∑ x : ZMod p, x ^ m
      = ∑ x ∈ univ \ {(0 : ZMod p)}, x ^ m := by
        rw [← Finset.sum_sdiff ({0} : Finset (ZMod p)).subset_univ, Finset.sum_singleton,
          zero_pow (by omega), add_zero]
    _ = ∑ x : (ZMod p)ˣ, ((x : ZMod p)) ^ m := by
        rw [← hmap, univ.sum_map emb]; rfl
    _ = if (p - 1) ∣ m then -1 else 0 := by
        rw [FiniteField.sum_pow_units (ZMod p) m, hcard]

theorem range_sum_pow_zmod (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ range p, (k : ZMod p) ^ m) = if (p - 1) ∣ m then -1 else 0 := by
  rw [sum_range_zmod p (fun x => x ^ m)]
  exact univ_sum_pow_zmod p m hm

/-- von Staudt–Clausen lower bound: for odd primes, `bernoulli` is `p`-integral up to one.
This version is needed first by strong induction. -/
theorem vSC_lower' {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) :
    ∀ m, (-1 : ℤ) ≤ padicValRat p (bernoulli m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    by_cases hbm : bernoulli m = 0
    · rw [hbm]; simp
    · have hpQ : ((p:ℕ):ℚ) ≠ 0 := by exact_mod_cast (Fact.out (p := p.Prime)).ne_zero
      have hp1 : 1 < p := (Fact.out (p := p.Prime)).one_lt
      -- Tail sum has nonnegative valuation
      set F : ℕ → ℚ := fun i =>
        bernoulli i * (((m+1).choose i : ℕ) : ℚ) * ((p:ℕ) : ℚ)^(m+1-i) / ((m+1 : ℕ) : ℚ) with hFdef
      have htail : (∑ i ∈ Finset.range m, F i) = 0
          ∨ (0 : ℤ) ≤ padicValRat p (∑ i ∈ Finset.range m, F i) := by
        apply padic_sum_ge
        intro i hi
        have hilt : i < m := Finset.mem_range.mp hi
        by_cases hbi : bernoulli i = 0
        · left; simp [hFdef, hbi]
        · right
          rw [hFdef]
          rw [term_val_eq m i (le_of_lt hilt) hbi]
          have hIHi : (-1 : ℤ) ≤ padicValRat p (bernoulli i) := IH i hilt
          have hpvn := pvn_add_one_le (p := p) (j := m+1-i) (by omega)
          have hnn : (0 : ℤ) ≤ (padicValNat p (m.choose i) : ℤ) := by positivity
          have : ((m+1-i : ℕ) : ℤ) - (padicValNat p (m+1-i) : ℤ) ≥ 1 := by
            have : (padicValNat p (m+1-i) : ℤ) + 1 ≤ ((m+1-i : ℕ) : ℤ) := by exact_mod_cast hpvn
            omega
          omega
      have htailnn : (0 : ℤ) ≤ padicValRat p (∑ i ∈ Finset.range m, F i) := by
        rcases htail with h0 | h0
        · rw [h0]; simp
        · exact h0
      -- The integer sum on the left has nonnegative valuation
      have hintnn : (0 : ℤ) ≤ padicValRat p (∑ k ∈ Finset.range p, (k : ℚ)^m) := by
        have : (∑ k ∈ Finset.range p, (k : ℚ)^m) = ((∑ k ∈ Finset.range p, k^m : ℕ) : ℚ) := by
          push_cast; rfl
        rw [this]
        rw [padicValRat.of_nat]
        positivity
      -- bernoulli m * p = int - tail
      have hsplit := faulhaber_split p m
      have hbmp : bernoulli m * ((p:ℕ):ℚ)
          = (∑ k ∈ Finset.range p, (k : ℚ)^m) + (-(∑ i ∈ Finset.range m, F i)) := by
        rw [hsplit]; ring
      have hbmp_ne : bernoulli m * ((p:ℕ):ℚ) ≠ 0 := mul_ne_zero hbm hpQ
      have hval : (0 : ℤ) ≤ padicValRat p (bernoulli m * ((p:ℕ):ℚ)) := by
        rw [hbmp]
        have hne : (∑ k ∈ Finset.range p, (k : ℚ)^m) + (-(∑ i ∈ Finset.range m, F i)) ≠ 0 := by
          rw [← hbmp]; exact hbmp_ne
        refine le_trans (le_min hintnn ?_) (padicValRat.min_le_padicValRat_add hne)
        rw [padicValRat.neg]; exact htailnn
      -- conclude
      rw [padicValRat.mul hbm hpQ, padicValRat.self hp1] at hval
      omega


/-- Abbreviation for the Faulhaber tail sum. -/
noncomputable def ftail (p m : ℕ) : ℚ :=
  ∑ i ∈ Finset.range m, bernoulli i * (((m+1).choose i : ℕ) : ℚ) * ((p:ℕ) : ℚ)^(m+1-i) / ((m+1 : ℕ) : ℚ)

/-- The Faulhaber tail sum has p-adic valuation ≥ 1 (for odd primes). -/
theorem faulhaber_tail_pos {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) (m : ℕ) :
    ftail p m = 0 ∨ (1 : ℤ) ≤ padicValRat p (ftail p m) := by
  unfold ftail
  apply padic_sum_ge
  intro i hi
  have hilt : i < m := Finset.mem_range.mp hi
  by_cases hbi : bernoulli i = 0
  · left; simp [hbi]
  · right
    rw [term_val_eq m i (le_of_lt hilt) hbi]
    have hIHi : (-1 : ℤ) ≤ padicValRat p (bernoulli i) := vSC_lower' hp3 i
    have hpvn := pvn_add_two_le (p := p) (j := m+1-i) hp3 (by omega)
    have hnn : (0 : ℤ) ≤ (padicValNat p (m.choose i) : ℤ) := by positivity
    have hge : ((m+1-i : ℕ) : ℤ) - (padicValNat p (m+1-i) : ℤ) ≥ 2 := by
      have : (padicValNat p (m+1-i) : ℤ) + 2 ≤ ((m+1-i : ℕ) : ℤ) := by exact_mod_cast hpvn
      omega
    omega

/-- The integer power sum cast to ℚ. -/
theorem powsum_val_eq {p : ℕ} [Fact p.Prime] (m : ℕ) (hm : 1 ≤ m) :
    padicValRat p (∑ k ∈ Finset.range p, (k : ℚ)^m)
      = (padicValNat p (∑ k ∈ Finset.range p, k^m) : ℤ) := by
  have : (∑ k ∈ Finset.range p, (k : ℚ)^m) = ((∑ k ∈ Finset.range p, k^m : ℕ) : ℚ) := by
    push_cast; rfl
  rw [this, padicValRat.of_nat]

theorem powsum_nat_ne_zero (p : ℕ) (hp3 : 3 ≤ p) (m : ℕ) :
    (∑ k ∈ Finset.range p, k^m : ℕ) ≠ 0 := by
  have hpos : (1:ℕ)^m ≤ ∑ k ∈ Finset.range p, k^m :=
    Finset.single_le_sum (f := fun k => k^m) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))
  simp only [one_pow] at hpos
  omega

theorem powsum_ne_zero (p : ℕ) (hp3 : 3 ≤ p) (m : ℕ) :
    (∑ k ∈ Finset.range p, (k : ℚ)^m) ≠ 0 := by
  have h1 : (∑ k ∈ Finset.range p, (k : ℚ)^m) = ((∑ k ∈ Finset.range p, k^m : ℕ) : ℚ) := by
    push_cast; rfl
  rw [h1]
  exact_mod_cast powsum_nat_ne_zero p hp3 m

/-- Divisibility of the integer power sum by `p`. -/
theorem powsum_dvd_iff {p : ℕ} [Fact p.Prime] (m : ℕ) (hm : 1 ≤ m) :
    (p ∣ (∑ k ∈ Finset.range p, k^m)) ↔ ¬ ((p-1) ∣ m) := by
  have hcast : ((∑ k ∈ Finset.range p, k^m : ℕ) : ZMod p) = ∑ k ∈ Finset.range p, (k : ZMod p)^m := by
    push_cast; rfl
  rw [← ZMod.natCast_eq_zero_iff]
  rw [hcast, range_sum_pow_zmod p m hm]
  by_cases hd : (p-1) ∣ m
  · have hne : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    rw [if_pos hd]; simp [hne, hd]
  · rw [if_neg hd]; simp [hd]


theorem bmp_eq (p m : ℕ) :
    bernoulli m * ((p:ℕ):ℚ)
      = (∑ k ∈ Finset.range p, (k : ℚ)^m) + (-(ftail p m)) := by
  unfold ftail; rw [faulhaber_split p m]; ring

/-- von Staudt–Clausen value when `(p-1) ∣ m`: valuation is exactly `-1`. -/
theorem vSC_val_neg {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) (m : ℕ) (hm : 1 ≤ m)
    (hd : (p-1) ∣ m) : padicValRat p (bernoulli m) = -1 ∧ bernoulli m ≠ 0 := by
  have hpQ : ((p:ℕ):ℚ) ≠ 0 := by exact_mod_cast (Fact.out (p := p.Prime)).ne_zero
  have hp1 : 1 < p := (Fact.out (p := p.Prime)).one_lt
  set Sp := ∑ k ∈ Finset.range p, (k : ℚ)^m with hSp
  have hSpne : Sp ≠ 0 := powsum_ne_zero p hp3 m
  -- valuation of Sp is 0
  have hS0 : padicValRat p Sp = 0 := by
    rw [hSp, powsum_val_eq m hm]
    have hnd : ¬ p ∣ (∑ k ∈ Finset.range p, k^m) := by
      rw [powsum_dvd_iff m hm]; exact not_not.mpr hd
    rw [padicValNat.eq_zero_of_not_dvd hnd]; rfl
  have htail := faulhaber_tail_pos hp3 m
  -- bernoulli m ≠ 0
  have hbm : bernoulli m ≠ 0 := by
    intro h0
    have hb := bmp_eq p m
    rw [h0, zero_mul] at hb
    have heq : Sp = ftail p m := by linarith [hb]
    rcases htail with hT0 | hTpos
    · rw [hT0] at heq; exact hSpne heq
    · have hv : padicValRat p Sp = padicValRat p (ftail p m) := by rw [heq]
      rw [hS0] at hv
      omega
  -- valuation of bernoulli m * p
  have key : padicValRat p (bernoulli m * ((p:ℕ):ℚ)) = 0 := by
    rw [bmp_eq p m]
    rcases htail with hT0 | hTpos
    · rw [hT0]; simp only [neg_zero, add_zero]; exact hS0
    · have hTne : ftail p m ≠ 0 := by
        intro h; rw [h] at hTpos; simp at hTpos
      have hnegne : -(ftail p m) ≠ 0 := neg_ne_zero.mpr hTne
      have hsum_ne : Sp + (-(ftail p m)) ≠ 0 := by
        rw [← bmp_eq p m]; exact mul_ne_zero hbm hpQ
      have hlt : padicValRat p Sp < padicValRat p (-(ftail p m)) := by
        rw [padicValRat.neg, hS0]; omega
      rw [padicValRat.add_eq_of_lt hsum_ne hSpne hnegne hlt, hS0]
  rw [padicValRat.mul hbm hpQ, padicValRat.self hp1] at key
  exact ⟨by omega, hbm⟩

/-- Helper: numerator and denominator of a reduced rational can't share the prime `p`. -/
theorem num_den_not_both {p : ℕ} [Fact p.Prime] (q : ℚ) (hpD : p ∣ q.den) :
    ¬ (p : ℤ) ∣ q.num := by
  have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced
  intro hpN
  have hpNa : p ∣ q.num.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hpN
    simpa using this
  have h1 : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hpNa hpD
  have h2 : p = 1 := Nat.dvd_one.mp (hcop ▸ h1)
  have := (Fact.out (p := p.Prime)).one_lt
  omega

/-- von Staudt–Clausen value when `¬ (p-1) ∣ m`: valuation is `≥ 0`. -/
theorem vSC_val_nonneg {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) (m : ℕ) (hm : 1 ≤ m)
    (hd : ¬ (p-1) ∣ m) : 0 ≤ padicValRat p (bernoulli m) := by
  by_cases hbm : bernoulli m = 0
  · rw [hbm]; simp
  · have hpQ : ((p:ℕ):ℚ) ≠ 0 := by exact_mod_cast (Fact.out (p := p.Prime)).ne_zero
    have hp1 : 1 < p := (Fact.out (p := p.Prime)).one_lt
    set Sp := ∑ k ∈ Finset.range p, (k : ℚ)^m with hSp
    have hSpne : Sp ≠ 0 := powsum_ne_zero p hp3 m
    have hS1 : (1:ℤ) ≤ padicValRat p Sp := by
      rw [hSp, powsum_val_eq m hm]
      have hdvd : p ∣ (∑ k ∈ Finset.range p, k^m) := by
        rw [powsum_dvd_iff m hm]; exact hd
      have hsumne : (∑ k ∈ Finset.range p, k^m) ≠ 0 := powsum_nat_ne_zero p hp3 m
      have : 1 ≤ padicValNat p (∑ k ∈ Finset.range p, k^m) :=
        one_le_padicValNat_of_dvd hsumne hdvd
      exact_mod_cast this
    have htail := faulhaber_tail_pos hp3 m
    have key : (1:ℤ) ≤ padicValRat p (bernoulli m * ((p:ℕ):ℚ)) := by
      rw [bmp_eq p m]
      rcases htail with hT0 | hTpos
      · rw [hT0]; simp only [neg_zero, add_zero]; exact hS1
      · have hnegge : (1:ℤ) ≤ padicValRat p (-(ftail p m)) := by
          rw [padicValRat.neg]; exact hTpos
        have hsum_ne : Sp + (-(ftail p m)) ≠ 0 := by
          rw [← bmp_eq p m]; exact mul_ne_zero hbm hpQ
        exact le_trans (le_min hS1 hnegge) (padicValRat.min_le_padicValRat_add hsum_ne)
    rw [padicValRat.mul hbm hpQ, padicValRat.self hp1] at key
    omega

/-- Integer-form von Staudt–Clausen facts about the denominator and numerator. -/
theorem vSC_den_pos {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) (m : ℕ) (hm : 1 ≤ m)
    (hd : (p-1) ∣ m) :
    padicValNat p (bernoulli m).den = 1 ∧ ¬ (p : ℤ) ∣ (bernoulli m).num := by
  have hval := (vSC_val_neg hp3 m hm hd).1
  rw [padicValRat_def] at hval
  -- hval : (↑(padicValInt p N) - ↑(padicValNat p D) : ℤ) = -1
  set a := padicValInt p (bernoulli m).num with ha
  set b := padicValNat p (bernoulli m).den with hb
  have hba : b = a + 1 := by omega
  have hpD : p ∣ (bernoulli m).den := dvd_of_one_le_padicValNat (by omega : 1 ≤ b)
  have hNa : ¬ (p : ℤ) ∣ (bernoulli m).num := num_den_not_both _ hpD
  have ha0 : a = 0 := by
    rw [ha]; exact padicValInt.eq_zero_of_not_dvd hNa
  exact ⟨by omega, hNa⟩

theorem vSC_den_zero {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) (m : ℕ) (hm : 1 ≤ m)
    (hd : ¬ (p-1) ∣ m) : ¬ p ∣ (bernoulli m).den := by
  intro hpD
  have hval := vSC_val_nonneg hp3 m hm hd
  rw [padicValRat_def] at hval
  have hNa : ¬ (p : ℤ) ∣ (bernoulli m).num := num_den_not_both _ hpD
  have ha0 : padicValInt p (bernoulli m).num = 0 := padicValInt.eq_zero_of_not_dvd hNa
  have hb1 : 1 ≤ padicValNat p (bernoulli m).den :=
    one_le_padicValNat_of_dvd (Rat.den_pos _).ne' hpD
  rw [ha0] at hval
  omega

/-- The Faulhaber tail with base `b` divisible by `p` has p-adic valuation ≥ 1. -/
theorem faulhaber_tail_base_pos {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) (b m : ℕ)
    (hb : 1 ≤ padicValNat p b) :
    ftail b m = 0 ∨ (1 : ℤ) ≤ padicValRat p (ftail b m) := by
  have hb0 : b ≠ 0 := by
    intro h; rw [h] at hb; simp [padicValNat.zero] at hb
  unfold ftail
  apply padic_sum_ge
  intro i hi
  have hilt : i < m := Finset.mem_range.mp hi
  by_cases hbi : bernoulli i = 0
  · left; simp [hbi]
  · right
    rw [term_val_base b m i hb0 (le_of_lt hilt) hbi]
    have hIHi : (-1 : ℤ) ≤ padicValRat p (bernoulli i) := vSC_lower' hp3 i
    have hpvn := pvn_add_two_le (p := p) (j := m+1-i) hp3 (by omega)
    have hnn : (0 : ℤ) ≤ (padicValNat p (m.choose i) : ℤ) := by positivity
    have hge2 : ((m+1-i : ℕ) : ℤ) - (padicValNat p (m+1-i) : ℤ) ≥ 2 := by
      have : (padicValNat p (m+1-i) : ℤ) + 2 ≤ ((m+1-i : ℕ) : ℤ) := by exact_mod_cast hpvn
      omega
    have hbge : (1 : ℤ) ≤ (padicValNat p b : ℤ) := by exact_mod_cast hb
    have hmul : ((m+1-i : ℕ) : ℤ) ≤ ((m+1-i : ℕ) : ℤ) * (padicValNat p b : ℤ) := by
      nlinarith [hge2, hbge, Int.natCast_nonneg (m+1-i)]
    omega

/-- Divisibility characterized by prime powers (nat version). -/
theorem nat_dvd_iff_prime_pow (k c : ℕ) (hk : k ≠ 0) :
    k ∣ c ↔ ∀ p, p.Prime → p ^ (k.factorization p) ∣ c := by
  constructor
  · intro hkc p _
    exact dvd_trans (Nat.ordProj_dvd k p) hkc
  · intro h
    by_cases hc : c = 0
    · simp [hc]
    · rw [← Nat.factorization_le_iff_dvd hk hc]
      intro p
      by_cases hp : p.Prime
      · rw [← Nat.Prime.pow_dvd_iff_le_factorization hp hc]
        exact h p hp
      · rw [Nat.factorization_eq_zero_of_not_prime k hp]
        exact Nat.zero_le _

/-- Divisibility characterized by prime powers (int version). -/
theorem int_dvd_iff_prime_pow (k : ℕ) (z : ℤ) (hk : k ≠ 0) :
    (k : ℤ) ∣ z ↔ ∀ p : ℕ, p.Prime → ((p : ℤ) ^ (k.factorization p) ∣ z) := by
  rw [Int.ofNat_dvd_left, nat_dvd_iff_prime_pow k z.natAbs hk]
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro _
  rw [← Nat.cast_pow, Int.ofNat_dvd_left]

/-- Grouping: sum of `(k mod p)^m` over a multiple of `p` of terms. -/
theorem nsum_zmod (p t m : ℕ) [NeZero p] :
    (∑ k ∈ Finset.range (p*t), (k : ZMod p)^m) = (t : ZMod p) * (∑ x : ZMod p, x^m) := by
  induction t with
  | zero => simp
  | succ d hd =>
    have hmul : p * (d+1) = p*d + p := by ring
    rw [hmul, Finset.sum_range_add]
    rw [hd]
    have hblock : (∑ k ∈ Finset.range p, ((p*d+k : ℕ) : ZMod p)^m)
        = ∑ x : ZMod p, x^m := by
      have : (∑ k ∈ Finset.range p, ((p*d+k : ℕ) : ZMod p)^m)
          = ∑ k ∈ Finset.range p, ((k : ℕ) : ZMod p)^m := by
        apply Finset.sum_congr rfl
        intro k _
        congr 1
        push_cast
        simp [ZMod.natCast_self]
      rw [this, sum_range_zmod p (fun x => x^m)]
    rw [hblock]
    push_cast
    ring

/-- If `p ∣ n` and (`p ∣ n/p` or `(p-1) ∤ m`), then `p` divides the power sum. -/
theorem nsum_dvd_of {p n m : ℕ} [Fact p.Prime] (hpn : p ∣ n) (hm : 1 ≤ m)
    (hcond : p ∣ (n/p) ∨ ¬ (p-1) ∣ m) :
    p ∣ (∑ k ∈ Finset.range n, k^m) := by
  rw [← ZMod.natCast_eq_zero_iff]
  have hcast : ((∑ k ∈ Finset.range n, k^m : ℕ) : ZMod p) = ∑ k ∈ Finset.range n, (k : ZMod p)^m := by
    push_cast; rfl
  rw [hcast]
  have hn : n = p * (n/p) := (Nat.mul_div_cancel' hpn).symm
  rw [hn, nsum_zmod p (n/p) m, univ_sum_pow_zmod p m hm]
  rcases hcond with hc | hc
  · have : ((n/p : ℕ) : ZMod p) = 0 := by rw [ZMod.natCast_eq_zero_iff]; exact hc
    rw [this, zero_mul]
  · rw [if_neg hc, mul_zero]

/-- From a valuation bound, conclude divisibility by `p²`. -/
theorem int_sq_dvd_of_val {p : ℕ} [Fact p.Prime] (z : ℤ) (hz : z ≠ 0)
    (hv : 2 ≤ padicValInt p z) : (p : ℤ)^2 ∣ z := by
  have hzn : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hp := (Fact.out : p.Prime)
  have h2 : p^2 ∣ z.natAbs := by
    rw [Nat.Prime.pow_dvd_iff_le_factorization hp hzn, Nat.factorization_def _ hp]
    exact hv
  have h3 : ((p^2 : ℕ):ℤ) ∣ z := by rw [Int.ofNat_dvd_left]; exact h2
  simpa using h3

/-- The local magic identity: when `p ‖ n` and `(p-1) ∣ m`, `p² ∣ D·S - N·n`. -/
theorem magic_local {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) (n m : ℕ) (hm : 1 ≤ m)
    (hpn : 1 ≤ padicValNat p n) (hd : (p-1) ∣ m) :
    (p : ℤ)^2 ∣ (((bernoulli m).den : ℤ) * (∑ k ∈ Finset.range n, (k : ℤ)^m)
      - (bernoulli m).num * n) := by
  set D : ℕ := (bernoulli m).den with hDdef
  set N : ℤ := (bernoulli m).num with hNdef
  have hD0 : D ≠ 0 := by rw [hDdef]; exact (Rat.den_pos (bernoulli m)).ne'
  have hDQ : ((D:ℕ):ℚ) ≠ 0 := by exact_mod_cast hD0
  -- rational identity
  have hBeq : (bernoulli m) = (N : ℚ) / (D : ℚ) := by
    rw [hNdef, hDdef]; exact (Rat.num_div_den (bernoulli m)).symm
  have hDN : (D:ℚ) * bernoulli m = (N:ℚ) := by rw [hBeq]; field_simp
  have hsplit := faulhaber_split n m
  -- hsplit : ∑_{k<n}(k:ℚ)^m = ftail n m + bernoulli m * n
  set z : ℤ := (D : ℤ) * (∑ k ∈ Finset.range n, (k : ℤ)^m) - N * n with hzdef
  have hzQ : (z : ℚ) = (D : ℚ) * ftail n m := by
    unfold ftail
    rw [hzdef]
    push_cast
    push_cast at hsplit
    rw [hsplit]
    linear_combination (n:ℚ) * hDN
  by_cases hft : ftail n m = 0
  · have : (z : ℚ) = 0 := by rw [hzQ, hft, mul_zero]
    have hz0 : z = 0 := by exact_mod_cast this
    rw [hz0]; simp
  · -- z ≠ 0
    have hzne : (z : ℚ) ≠ 0 := by rw [hzQ]; exact mul_ne_zero hDQ hft
    have hzint_ne : z ≠ 0 := by intro h; apply hzne; rw [h]; simp
    -- valuation
    have hval : (2 : ℤ) ≤ padicValRat p (z : ℚ) := by
      rw [hzQ, padicValRat.mul hDQ hft]
      have h1 : padicValRat p ((D:ℕ):ℚ) = 1 := by
        rw [padicValRat.of_nat]
        have := (vSC_den_pos hp3 m hm hd).1
        rw [hDdef]; exact_mod_cast this
      have h2 : (1 : ℤ) ≤ padicValRat p (ftail n m) := by
        rcases faulhaber_tail_base_pos hp3 n m hpn with h0 | h0
        · exact absurd h0 hft
        · exact h0
      rw [h1]; omega
    rw [padicValRat.of_int] at hval
    have hval' : 2 ≤ padicValInt p z := by exact_mod_cast hval
    exact int_sq_dvd_of_val z hzint_ne hval'

/-- For even `n ≥ 4`, `n` does not divide `S+1` (Giuga condition fails). -/
theorem even_no_dvd (n : ℕ) (hn4 : 4 ≤ n) (hev : Even n) :
    ¬ ((n:ℤ) ∣ ((∑ k ∈ Finset.range n, (k:ℤ)^(n-1)) + 1)) := by
  have hne : NeZero n := ⟨by omega⟩
  set m := n - 1 with hmdef
  have hmo : Odd m := by
    rcases hev with ⟨t, ht⟩; refine ⟨t-1, ?_⟩; omega
  set S : ℤ := ∑ k ∈ Finset.range n, (k:ℤ)^m with hSdef
  have hsum_neg : (∑ x : ZMod n, x^m) = - (∑ x : ZMod n, x^m) := by
    conv_lhs => rw [← Equiv.sum_comp (Equiv.neg (ZMod n)) (fun x => x^m)]
    simp only [Equiv.neg_apply]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [hmo.neg_pow]
  have h2z : (2 : ZMod n) * (∑ x : ZMod n, x^m) = 0 := by
    rw [two_mul]
    nth_rewrite 1 [hsum_neg]
    ring
  have hScast : ((S : ℤ) : ZMod n) = ∑ x : ZMod n, x^m := by
    rw [hSdef]
    push_cast
    exact sum_range_zmod n (fun x => x^m)
  have hn2S : (n:ℤ) ∣ 2 * S := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hScast, h2z]
  intro hdvd
  have h2 : (n:ℤ) ∣ 2 * (S + 1) := Dvd.dvd.mul_left hdvd 2
  have hdvd2 : (n:ℤ) ∣ 2 := by
    have hsub := dvd_sub h2 hn2S
    have heq : 2 * (S + 1) - 2 * S = 2 := by ring
    rwa [heq] at hsub
  have hle : (n:ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hdvd2
  omega

theorem split_den {p D : ℕ} (hp : p.Prime) (hv : padicValNat p D = 1) :
    ∃ D' : ℕ, D = p * D' ∧ ¬ p ∣ D' := by
  have hD0 : D ≠ 0 := by rintro rfl; simp [padicValNat.zero] at hv
  have hpD : p ∣ D := dvd_of_one_le_padicValNat (by omega)
  refine ⟨D/p, (Nat.mul_div_cancel' hpD).symm, ?_⟩
  intro hpd
  have hp2 : p^2 ∣ D := by
    obtain ⟨c, hc⟩ := hpd
    refine ⟨c, ?_⟩
    rw [← Nat.mul_div_cancel' hpD, hc]; ring
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.Prime.pow_dvd_iff_le_factorization hp hD0, Nat.factorization_def _ hp, hv] at hp2
  omega

/-- Per-prime equivalence (odd prime case). -/
theorem per_prime {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) (n : ℕ) (hn : 1 < n) (hpn : p ∣ n) :
    ((p:ℤ)^(2*(n.factorization p)) ∣ ((bernoulli (n-1)).num * (n:ℤ) + (bernoulli (n-1)).den)) ↔
    ((p:ℤ)^(n.factorization p) ∣ ((∑ k ∈ Finset.range n, (k:ℤ)^(n-1)) + 1)) := by
  have hp := (Fact.out : p.Prime)
  set m := n - 1 with hmdef
  have hm : 1 ≤ m := by omega
  set N : ℤ := (bernoulli m).num with hNdef
  set D : ℕ := (bernoulli m).den with hDdef
  set S : ℤ := ∑ k ∈ Finset.range n, (k:ℤ)^m with hSdef
  set a := n.factorization p with hadef
  have ha1 : 1 ≤ a := by
    rw [hadef, Nat.factorization_def _ hp]
    exact one_le_padicValNat_of_dvd (by omega) hpn
  have hpInt_n : (p:ℤ) ∣ (n:ℤ) := Int.natCast_dvd_natCast.mpr hpn
  -- cast of nat power sum
  have hScast : S = ((∑ k ∈ Finset.range n, k^m : ℕ):ℤ) := by rw [hSdef]; push_cast; rfl
  -- helper: from p ∣ nat sum, conclude RHS false
  have RHS_false_of : (p:ℤ) ∣ S → ¬ ((p:ℤ)^a ∣ (S+1)) := by
    intro hpS h
    have hpdvd : (p:ℤ) ∣ (S+1) := dvd_trans (dvd_pow_self (p:ℤ) (by omega : a ≠ 0)) h
    have h1 : (p:ℤ) ∣ 1 := by
      have := dvd_sub hpdvd hpS; simpa using this
    have hle : (p:ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
    have : (3:ℤ) ≤ (p:ℤ) := by exact_mod_cast hp3
    omega
  by_cases hAc : (p-1) ∣ m
  · -- (p-1) ∣ m
    obtain ⟨hDv, hpN⟩ := vSC_den_pos hp3 m hm hAc
    by_cases ha2 : 2 ≤ a
    · -- a ≥ 2: both false
      -- p ∣ S
      have hp2n : p^2 ∣ n := by
        have hpa : p^a ∣ n := by rw [hadef]; exact Nat.ordProj_dvd n p
        exact dvd_trans (pow_dvd_pow p ha2) hpa
      have hpdp : p ∣ (n/p) := (Nat.dvd_div_iff_mul_dvd hpn).mpr (by rw [← pow_two]; exact hp2n)
      have hpS_nat : p ∣ (∑ k ∈ Finset.range n, k^m) := nsum_dvd_of hpn hm (Or.inl hpdp)
      have hpS : (p:ℤ) ∣ S := by rw [hScast]; exact_mod_cast hpS_nat
      have hRfalse := RHS_false_of hpS
      -- LHS false
      have hLfalse : ¬ ((p:ℤ)^(2*a) ∣ (N*(n:ℤ)+(D:ℤ))) := by
        intro h
        have hp2int : (p:ℤ)^2 ∣ (N*(n:ℤ)+(D:ℤ)) :=
          dvd_trans (pow_dvd_pow (p:ℤ) (by omega : 2 ≤ 2*a)) h
        have hp2Nn : (p:ℤ)^2 ∣ N*(n:ℤ) := by
          have : (p:ℤ)^2 ∣ (n:ℤ) := by
            have : ((p^2:ℕ):ℤ) ∣ (n:ℤ) := Int.natCast_dvd_natCast.mpr hp2n
            simpa using this
          exact Dvd.dvd.mul_left this N
        have hp2D : (p:ℤ)^2 ∣ (D:ℤ) := by
          have := dvd_sub hp2int hp2Nn
          have heq : (N*(n:ℤ)+(D:ℤ)) - N*(n:ℤ) = (D:ℤ) := by ring
          rwa [heq] at this
        -- but p^2 ∤ D since padicValNat p D = 1
        have hD0 : D ≠ 0 := (Rat.den_pos _).ne'
        have hp2Dn : ¬ (p^2 ∣ D) := by
          rw [Nat.Prime.pow_dvd_iff_le_factorization hp hD0, Nat.factorization_def _ hp, hDv]
          omega
        apply hp2Dn
        have : ((p^2:ℕ):ℤ) ∣ (D:ℤ) := by simpa using hp2D
        exact_mod_cast this
      constructor
      · intro h; exact absurd h hLfalse
      · intro h; exact absurd h hRfalse
    · -- a = 1: MAGIC
      have ha_eq : a = 1 := by omega
      rw [ha_eq]; simp only [pow_one, mul_one]
      have hpvn : 1 ≤ padicValNat p n := by
        rw [← Nat.factorization_def _ hp, ← hadef]; omega
      have hmagic : (p:ℤ)^2 ∣ ((D:ℤ)*S - N*(n:ℤ)) := magic_local hp3 n m hm hpvn hAc
      -- LHS = p^2 ∣ Nn+D ↔ p^2 ∣ D(S+1)
      have key1 : ((p:ℤ)^2 ∣ (N*(n:ℤ)+(D:ℤ))) ↔ ((p:ℤ)^2 ∣ (D:ℤ)*(S+1)) := by
        have heq : (D:ℤ)*(S+1) = (N*(n:ℤ)+(D:ℤ)) + ((D:ℤ)*S - N*(n:ℤ)) := by ring
        constructor
        · intro h; rw [heq]; exact dvd_add h hmagic
        · intro h
          have : (N*(n:ℤ)+(D:ℤ)) = (D:ℤ)*(S+1) - ((D:ℤ)*S - N*(n:ℤ)) := by ring
          rw [this]; exact dvd_sub h hmagic
      -- p^2 ∣ D(S+1) ↔ p ∣ S+1
      obtain ⟨D', hDD', hpD'⟩ := split_den hp hDv
      have key2 : ((p:ℤ)^2 ∣ (D:ℤ)*(S+1)) ↔ ((p:ℤ) ∣ (S+1)) := by
        have hDcast : (D:ℤ) = (p:ℤ) * (D':ℤ) := by exact_mod_cast hDD'
        rw [hDcast]
        have hpz : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
        rw [sq, mul_assoc, mul_dvd_mul_iff_left hpz]
        -- p ∣ D' * (S+1) ↔ p ∣ S+1
        rw [(prime_iff_prime_int.mp hp).dvd_mul]
        have hpD'int : ¬ (p:ℤ) ∣ (D':ℤ) := by
          rw [Int.natCast_dvd_natCast]; exact hpD'
        constructor
        · rintro (h | h)
          · exact absurd h hpD'int
          · exact h
        · intro h; exact Or.inr h
      rw [key1, key2]
  · -- ¬(p-1) ∣ m : both false
    have hpD_nat : ¬ p ∣ D := vSC_den_zero hp3 m hm hAc
    have hpS_nat : p ∣ (∑ k ∈ Finset.range n, k^m) := nsum_dvd_of hpn hm (Or.inr hAc)
    have hpS : (p:ℤ) ∣ S := by rw [hScast]; exact_mod_cast hpS_nat
    have hRfalse := RHS_false_of hpS
    have hLfalse : ¬ ((p:ℤ)^(2*a) ∣ (N*(n:ℤ)+(D:ℤ))) := by
      intro h
      have hpdvd : (p:ℤ) ∣ (N*(n:ℤ)+(D:ℤ)) :=
        dvd_trans (dvd_pow_self (p:ℤ) (by omega : 2*a ≠ 0)) h
      have hpNn : (p:ℤ) ∣ N*(n:ℤ) := Dvd.dvd.mul_left hpInt_n N
      have hpD : (p:ℤ) ∣ (D:ℤ) := by
        have := dvd_sub hpdvd hpNn
        have heq : (N*(n:ℤ)+(D:ℤ)) - N*(n:ℤ) = (D:ℤ) := by ring
        rwa [heq] at this
      apply hpD_nat
      rwa [Int.natCast_dvd_natCast] at hpD
    constructor
    · intro h; exact absurd h hLfalse
    · intro h; exact absurd h hRfalse

theorem core (n : ℕ) (hn : 1 < n) :
    (n : ℤ)^2 ∣ ((bernoulli (n-1)).num * n + (bernoulli (n-1)).den) ↔
    (n : ℤ) ∣ ((∑ k ∈ Finset.range n, (k : ℤ)^(n-1)) + 1) := by
  by_cases hev : Even n
  · -- even n
    by_cases h2 : n = 2
    · subst h2
      rw [bernoulli_one]
      norm_num [Finset.sum_range_succ]
    · -- n even ≥ 4
      have hn4 : 4 ≤ n := by rcases hev with ⟨t, ht⟩; omega
      have hmo : Odd (n-1) := by rcases hev with ⟨t, ht⟩; exact ⟨t-1, by omega⟩
      have hb0 : bernoulli (n-1) = 0 := bernoulli_eq_zero_of_odd hmo (by omega)
      rw [hb0]
      simp only [Rat.num_zero, Rat.den_zero, Nat.cast_one, zero_mul, zero_add]
      constructor
      · intro h
        exfalso
        have hle : (n:ℤ)^2 ≤ 1 := Int.le_of_dvd one_pos h
        have : (4:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn4
        nlinarith
      · intro h
        exact absurd h (even_no_dvd n hn4 hev)
  · -- odd n
    have hn2 : ¬ 2 ∣ n := by rw [← even_iff_two_dvd]; exact hev
    rw [show (n:ℤ)^2 = ((n^2:ℕ):ℤ) by push_cast; ring]
    rw [int_dvd_iff_prime_pow (n^2) _ (by positivity)]
    rw [int_dvd_iff_prime_pow n _ (by omega)]
    apply forall_congr'
    intro p
    apply imp_congr_right
    intro hp
    have hfp : (n^2).factorization p = 2 * n.factorization p := by
      rw [Nat.factorization_pow]; rfl
    rw [hfp]
    by_cases hpn : p ∣ n
    · haveI : Fact p.Prime := ⟨hp⟩
      have hp3 : 3 ≤ p := by
        have hp2le : 2 ≤ p := hp.two_le
        have hpne2 : p ≠ 2 := by rintro rfl; exact hn2 hpn
        omega
      exact per_prime hp3 n hn hpn
    · have h0 : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpn
      rw [h0]
      simp
