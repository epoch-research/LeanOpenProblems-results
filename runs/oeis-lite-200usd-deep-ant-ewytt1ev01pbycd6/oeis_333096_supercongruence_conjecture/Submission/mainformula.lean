import FormalConjectures.Util.ProblemImports

open PowerSeries Finset

noncomputable def Cart (p : ℕ) (f : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (PowerSeries.coeff (p * n)) f

noncomputable def infl (p : ℕ) (h : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if p ∣ n then (PowerSeries.coeff (n / p)) h else 0

noncomputable def gc : ℕ → ℤ := fun n => if n = 0 then 1 else if n % 3 = 0 then 2 else -1

noncomputable def Gser : PowerSeries ℤ := PowerSeries.mk gc

noncomputable def qc (p : ℕ) : ℕ → ℤ := fun k => if 1 ≤ k ∧ k ≤ p - 1 then (p.choose k / p : ℕ) else 0

noncomputable def qser (p : ℕ) : PowerSeries ℤ := PowerSeries.mk (fun k => qc p k)

/- Basic coefficient lemmas -/

@[simp] lemma coeff_Cart (p n : ℕ) (f : PowerSeries ℤ) :
    (PowerSeries.coeff n) (Cart p f) = (PowerSeries.coeff (p * n)) f := by
  simp only [Cart, coeff_mk]

@[simp] lemma coeff_infl (p k : ℕ) (h : PowerSeries ℤ) :
    (PowerSeries.coeff k) (infl p h) = if p ∣ k then (PowerSeries.coeff (k / p)) h else 0 := by
  simp only [infl, coeff_mk]

@[simp] lemma coeff_Gser (n : ℕ) : (PowerSeries.coeff n) Gser = gc n := by
  simp only [Gser, coeff_mk]

@[simp] lemma coeff_qser (p k : ℕ) : (PowerSeries.coeff k) (qser p) = qc p k := by
  simp only [qser, coeff_mk]

/- Theorem 1: the key algebraic lemma -/

theorem cart_infl_mul (p : ℕ) (hp : 0 < p) (h H : PowerSeries ℤ) :
    Cart p (infl p h * H) = h * Cart p H := by
  ext n
  rw [coeff_Cart, coeff_mul, coeff_mul]
  simp only [coeff_Cart, coeff_infl]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (if p ∣ i then (PowerSeries.coeff (i / p)) h else 0) * (PowerSeries.coeff j) H)
        (p * n),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (PowerSeries.coeff i) h * (PowerSeries.coeff (p * j)) H) n]
  -- LHS: ∑ k ∈ range (p*n+1), (if p ∣ k then coeff (k/p) h else 0) * coeff (p*n - k) H
  -- RHS: ∑ k ∈ range (n+1), coeff k h * coeff (p*(n-k)) H
  have hL : ∀ k ∈ range (p * n + 1),
      (if p ∣ k then (PowerSeries.coeff (k / p)) h else 0) * (PowerSeries.coeff (p * n - k)) H
      = if p ∣ k then (PowerSeries.coeff (k / p)) h * (PowerSeries.coeff (p * n - k)) H else 0 := by
    intro k _; split_ifs <;> ring
  rw [Finset.sum_congr rfl hL, ← Finset.sum_filter]
  refine Finset.sum_bij' (fun k _ => k / p) (fun a _ => p * a) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    show k / p ∈ range (n + 1)
    rw [Finset.mem_filter, Finset.mem_range] at hk
    rw [Finset.mem_range]
    obtain ⟨hk1, hk2⟩ := hk
    have : k / p ≤ n := by
      apply Nat.div_le_of_le_mul
      omega
    omega
  · intro a ha
    show p * a ∈ (range (p * n + 1)).filter (fun k => p ∣ k)
    rw [Finset.mem_range] at ha
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by nlinarith [ha], Dvd.intro a rfl⟩
  · intro k hk
    show p * (k / p) = k
    rw [Finset.mem_filter] at hk
    exact Nat.mul_div_cancel' hk.2
  · intro a _
    show p * a / p = a
    exact Nat.mul_div_cancel_left a hp
  · intro k hk
    show (PowerSeries.coeff (k / p)) h * (PowerSeries.coeff (p * n - k)) H
        = (PowerSeries.coeff (k / p)) h * (PowerSeries.coeff (p * (n - k / p))) H
    rw [Finset.mem_filter] at hk
    have hdvd := hk.2
    have hle : k / p ≤ n := by
      rw [Finset.mem_range] at hk
      apply Nat.div_le_of_le_mul; omega
    rw [Nat.mul_sub, Nat.mul_div_cancel' hdvd]

/- Theorem 2 -/

lemma not_three_dvd_prime (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ (3 ∣ p) := by
  intro hd
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp 3 hd) with h | h <;> omega

theorem cart_G (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : Cart p Gser = Gser := by
  ext n
  rw [coeff_Cart, coeff_Gser, coeff_Gser]
  -- goal: gc (p * n) = gc n
  unfold gc
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hpn : p * n ≠ 0 := by positivity
    have hn0 : n ≠ 0 := by omega
    rw [if_neg hpn, if_neg hn0]
    have hp3 : ¬ (3 ∣ p) := not_three_dvd_prime p hp hp5
    have hpmod : p % 3 = 1 ∨ p % 3 = 2 := by omega
    have key : (p * n) % 3 = 0 ↔ n % 3 = 0 := by
      rw [Nat.mul_mod]
      rcases hpmod with h | h <;> rw [h] <;>
        · rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with hh | hh | hh <;>
            rw [hh] <;> decide
    by_cases hc : n % 3 = 0
    · rw [if_pos hc, if_pos (key.mpr hc)]
    · rw [if_neg hc, if_neg (fun h => hc (key.mp h))]

/- Equidistribution of binomial coefficients mod 3 -/

/-- Residue-`r` partial sum of binomial coefficients `C(m,k)`. -/
noncomputable def Sfun (m : ℕ) (r : ZMod 3) : ℤ :=
  ∑ k ∈ range (m + 1), if ((k : ℕ) : ZMod 3) = r then (m.choose k : ℤ) else 0

/-- The three residue classes exhaust the total. -/
lemma Stotal (m : ℕ) : Sfun m 0 + Sfun m 1 + Sfun m 2 = 2 ^ m := by
  unfold Sfun
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hpt : ∀ k ∈ range (m + 1),
      (if ((k : ℕ) : ZMod 3) = 0 then (m.choose k : ℤ) else 0)
        + (if ((k : ℕ) : ZMod 3) = 1 then (m.choose k : ℤ) else 0)
        + (if ((k : ℕ) : ZMod 3) = 2 then (m.choose k : ℤ) else 0)
      = (m.choose k : ℤ) := by
    intro k _
    have h3 := (by decide : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2) ((k : ℕ) : ZMod 3)
    rcases h3 with h | h | h
    · rw [h, if_pos rfl, if_neg (by decide), if_neg (by decide)]; ring
    · rw [h, if_neg (by decide), if_pos rfl, if_neg (by decide)]; ring
    · rw [h, if_neg (by decide), if_neg (by decide), if_pos rfl]; ring
  rw [Finset.sum_congr rfl hpt]
  have := Nat.sum_range_choose m
  exact_mod_cast this

/-- The condition equivalence used repeatedly. -/
lemma shift_cond (k : ℕ) (r : ZMod 3) :
    (((k + 1 : ℕ)) : ZMod 3) = r ↔ ((k : ℕ) : ZMod 3) = r - 1 := by
  push_cast
  constructor
  · intro h; rw [← h]; ring
  · intro h; rw [h]; ring

lemma Srec (m : ℕ) (r : ZMod 3) : Sfun (m + 1) r = Sfun m r + Sfun m (r - 1) := by
  unfold Sfun
  rw [Finset.sum_range_succ' (fun k => if ((k : ℕ) : ZMod 3) = r then ((m + 1).choose k : ℤ) else 0) (m + 1)]
  have hval : ∀ k ∈ range (m + 1),
      (if (((k + 1 : ℕ)) : ZMod 3) = r then ((m + 1).choose (k + 1) : ℤ) else 0)
      = (if ((k : ℕ) : ZMod 3) = r - 1 then (m.choose k : ℤ) else 0)
        + (if ((k : ℕ) : ZMod 3) = r - 1 then (m.choose (k + 1) : ℤ) else 0) := by
    intro k _
    rw [Nat.choose_succ_succ']
    by_cases h : (((k + 1 : ℕ)) : ZMod 3) = r
    · rw [if_pos h, if_pos ((shift_cond k r).mp h), if_pos ((shift_cond k r).mp h)]; push_cast; ring
    · rw [if_neg h, if_neg (fun hh => h ((shift_cond k r).mpr hh)),
        if_neg (fun hh => h ((shift_cond k r).mpr hh))]; ring
  rw [Finset.sum_congr rfl hval, Finset.sum_add_distrib]
  have hbndry : (if ((0 : ℕ) : ZMod 3) = r then ((m + 1).choose 0 : ℤ) else 0)
      = (if (0 : ZMod 3) = r then (1 : ℤ) else 0) := by simp
  rw [hbndry]
  -- unfolded second-sum identity
  have hsecond :
      (∑ k ∈ range (m + 1), if ((k : ℕ) : ZMod 3) = r - 1 then (m.choose (k + 1) : ℤ) else 0)
        + (if (0 : ZMod 3) = r then (1 : ℤ) else 0)
      = ∑ k ∈ range (m + 1), if ((k : ℕ) : ZMod 3) = r then (m.choose k : ℤ) else 0 := by
    rw [Finset.sum_range_succ' (fun k => if ((k : ℕ) : ZMod 3) = r then (m.choose k : ℤ) else 0) m]
    congr 1
    · rw [Finset.sum_range_succ (fun k => if ((k : ℕ) : ZMod 3) = r - 1 then (m.choose (k + 1) : ℤ) else 0) m]
      have hlast : (if ((m : ℕ) : ZMod 3) = r - 1 then (m.choose (m + 1) : ℤ) else 0) = 0 := by
        rw [Nat.choose_succ_self]; simp
      rw [hlast, add_zero]
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : (((k + 1 : ℕ)) : ZMod 3) = r
      · rw [if_pos ((shift_cond k r).mp h), if_pos h]
      · rw [if_neg (fun hh => h ((shift_cond k r).mpr hh)), if_neg h]
    · simp
  linarith [hsecond]

lemma Srange3 (m : ℕ) (r : ZMod 3) :
    Sfun m r + Sfun m (r - 1) + Sfun m (r - 2) = 2 ^ m := by
  have h3 := (by decide : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2) r
  have ht := Stotal m
  rcases h3 with h | h | h <;> subst h <;>
    simp only [show ((0 : ZMod 3) - 1) = 2 from by decide, show ((0 : ZMod 3) - 2) = 1 from by decide,
        show ((1 : ZMod 3) - 1) = 0 from by decide, show ((1 : ZMod 3) - 2) = 2 from by decide,
        show ((2 : ZMod 3) - 1) = 1 from by decide, show ((2 : ZMod 3) - 2) = 0 from by decide] <;>
    linarith [ht]

lemma Sshift3 (m : ℕ) (r : ZMod 3) : Sfun (m + 3) r = 3 * 2 ^ m - Sfun m r := by
  have h3z : (3 : ZMod 3) = 0 := by decide
  have hr21 : r - 2 - 1 = r := by linear_combination -h3z
  have htot := Srange3 m r
  have A : Sfun (m + 1) r = Sfun m r + Sfun m (r - 1) := Srec m r
  have B : Sfun (m + 1) (r - 1) = Sfun m (r - 1) + Sfun m (r - 2) := by
    have := Srec m (r - 1)
    rwa [show r - 1 - 1 = r - 2 from by ring] at this
  have C : Sfun (m + 1) (r - 2) = Sfun m (r - 2) + Sfun m r := by
    have := Srec m (r - 2)
    rwa [hr21] at this
  have D : Sfun (m + 2) r = Sfun (m + 1) r + Sfun (m + 1) (r - 1) := Srec (m + 1) r
  have E : Sfun (m + 2) (r - 1) = Sfun (m + 1) (r - 1) + Sfun (m + 1) (r - 2) := by
    have := Srec (m + 1) (r - 1)
    rwa [show r - 1 - 1 = r - 2 from by ring] at this
  have F : Sfun (m + 3) r = Sfun (m + 2) r + Sfun (m + 2) (r - 1) := Srec (m + 2) r
  linarith [A, B, C, D, E, F, htot]

/-- Descent for the difference `Sfun · 0 - Sfun · r` in steps of 3. -/
lemma Ddesc (b : ℕ) (r : ZMod 3) : ∀ t : ℕ,
    Sfun (b + 3 * t) 0 - Sfun (b + 3 * t) r = (-1 : ℤ) ^ t * (Sfun b 0 - Sfun b r) := by
  intro t
  induction t with
  | zero => simp
  | succ n ih =>
    have e : b + 3 * (n + 1) = (b + 3 * n) + 3 := by ring
    rw [e, Sshift3, Sshift3]
    linear_combination -ih

lemma Sfun_base :
    Sfun 1 0 = 1 ∧ Sfun 1 1 = 1 ∧ Sfun 1 2 = 0 ∧
    Sfun 2 0 = 1 ∧ Sfun 2 1 = 2 ∧ Sfun 2 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold Sfun; decide)

lemma binom_mid (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (ρ : ZMod 3) :
    3 * Sfun p ρ = 2 ^ p - 2 + 3 * (if ρ = 0 then (1 : ℤ) else 0)
      + 3 * (if ρ = ((p : ℕ) : ZMod 3) then (1 : ℤ) else 0) := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := Sfun_base
  have htot := Stotal p
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hb : p % 3 = 1 ∨ p % 3 = 2 := by
    have := not_three_dvd_prime p hp hp5; omega
  have hpe : p = p % 3 + 3 * (p / 3) := by omega
  have hD1 := Ddesc (p % 3) 1 (p / 3)
  have hD2 := Ddesc (p % 3) 2 (p / 3)
  rw [← hpe] at hD1 hD2
  have hpz : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod p 3).symm
  rcases hb with hb | hb
  · -- p % 3 = 1, p/3 even
    have hq : Even (p / 3) := by rw [Nat.even_iff]; omega
    rw [hq.neg_one_pow, one_mul] at hD1 hD2
    rw [hb] at hD1 hD2 hpz
    rw [b1, b2] at hD1
    rw [b1, b3] at hD2
    rw [hpz]
    have hρ := (by decide : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2) ρ
    rcases hρ with h | h | h <;> subst h <;>
      simp only [show ((1 : ℕ) : ZMod 3) = 1 from by decide, if_true, if_false,
        show ((0 : ZMod 3) = 1) = False from by decide, show ((1 : ZMod 3) = 0) = False from by decide,
        show ((2 : ZMod 3) = 0) = False from by decide, show ((2 : ZMod 3) = 1) = False from by decide] <;>
      linarith [hD1, hD2, htot]
  · -- p % 3 = 2, p/3 odd
    have hq : Odd (p / 3) := by rw [Nat.odd_iff]; omega
    rw [hq.neg_one_pow] at hD1 hD2
    rw [hb] at hD1 hD2 hpz
    rw [b4, b5] at hD1
    rw [b4, b6] at hD2
    rw [hpz]
    have hρ := (by decide : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2) ρ
    rcases hρ with h | h | h <;> subst h <;>
      simp only [show ((2 : ℕ) : ZMod 3) = 2 from by decide, if_true, if_false,
        show ((0 : ZMod 3) = 2) = False from by decide, show ((1 : ZMod 3) = 0) = False from by decide,
        show ((1 : ZMod 3) = 2) = False from by decide, show ((2 : ZMod 3) = 0) = False from by decide] <;>
      linarith [hD1, hD2, htot]

/- gc and coefficient helpers -/

lemma gc_pos (j : ℕ) (hj : 1 ≤ j) : gc j = 3 * (if 3 ∣ j then (1 : ℤ) else 0) - 1 := by
  unfold gc
  rw [if_neg (by omega)]
  by_cases h : j % 3 = 0
  · rw [if_pos h, if_pos (Nat.dvd_of_mod_eq_zero h)]; ring
  · rw [if_neg h, if_neg (show ¬ (3 ∣ j) from by omega)]; ring

/-- Coefficient of a product with `Gser`. -/
lemma coeffMulG (W : PowerSeries ℤ) (N : ℕ) :
    (PowerSeries.coeff N) (W * Gser)
      = ∑ k ∈ range (N + 1), (PowerSeries.coeff k) W * gc (N - k) := by
  rw [coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (PowerSeries.coeff i) W * (PowerSeries.coeff j) Gser) N]
  apply Finset.sum_congr rfl
  intro k _
  rw [coeff_Gser]

/-- Endpoint extraction: a sum over `range (p+1)` of a function vanishing on the middle. -/
lemma endpoint_sum (p : ℕ) (hp5 : 5 ≤ p) (g : ℕ → ℤ)
    (hz : ∀ k, 1 ≤ k → k ≤ p - 1 → g k = 0) :
    ∑ k ∈ range (p + 1), g k = g 0 + g p := by
  have hsub : ({0, p} : Finset ℕ) ⊆ range (p + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_subset hsub, Finset.sum_pair (by omega : (0 : ℕ) ≠ p)]
  intro x hx hxns
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxns
  push_neg at hxns
  rw [Finset.mem_range] at hx
  exact hz x (by omega) (by omega)

lemma pqc (p : ℕ) (hp : p.Prime) (k : ℕ) :
    (p : ℤ) * qc p k = if (1 ≤ k ∧ k ≤ p - 1) then (p.choose k : ℤ) else 0 := by
  unfold qc
  by_cases h : 1 ≤ k ∧ k ≤ p - 1
  · rw [if_pos h, if_pos h]
    have hk0 : k ≠ 0 := by omega
    have hkp : k < p := by omega
    have hdvd : p ∣ p.choose k := hp.dvd_choose_self hk0 hkp
    have he : p * (p.choose k / p) = p.choose k := Nat.mul_div_cancel' hdvd
    calc (p : ℤ) * ((p.choose k / p : ℕ) : ℤ)
        = ((p * (p.choose k / p) : ℕ) : ℤ) := by push_cast; ring
      _ = (p.choose k : ℤ) := by rw [he]
  · rw [if_neg h, if_neg h, mul_zero]

/-- The residue-restricted middle sum, times 3, equals `2^p - 2`. -/
lemma Umid (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (ρ : ZMod 3) :
    3 * (∑ k ∈ range (p + 1),
        if (((k : ℕ) : ZMod 3) = ρ ∧ 1 ≤ k ∧ k ≤ p - 1) then (p.choose k : ℤ) else 0)
      = 2 ^ p - 2 := by
  have hsplit : Sfun p ρ
      = (∑ k ∈ range (p + 1),
          if (((k : ℕ) : ZMod 3) = ρ ∧ 1 ≤ k ∧ k ≤ p - 1) then (p.choose k : ℤ) else 0)
        + ((if ((0 : ZMod 3) = ρ) then (1 : ℤ) else 0)
          + (if (((p : ℕ) : ZMod 3) = ρ) then (1 : ℤ) else 0)) := by
    unfold Sfun
    have hpt : ∀ k ∈ range (p + 1),
        (if ((k : ℕ) : ZMod 3) = ρ then (p.choose k : ℤ) else 0)
        = (if (((k : ℕ) : ZMod 3) = ρ ∧ 1 ≤ k ∧ k ≤ p - 1) then (p.choose k : ℤ) else 0)
          + (if (((k : ℕ) : ZMod 3) = ρ ∧ ¬(1 ≤ k ∧ k ≤ p - 1)) then (p.choose k : ℤ) else 0) := by
      intro k _
      by_cases hr : ((k : ℕ) : ZMod 3) = ρ <;> by_cases hm : (1 ≤ k ∧ k ≤ p - 1) <;>
        simp [hr, hm]
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
    congr 1
    rw [endpoint_sum p hp5
      (fun k => if (((k : ℕ) : ZMod 3) = ρ ∧ ¬(1 ≤ k ∧ k ≤ p - 1)) then (p.choose k : ℤ) else 0)]
    · have h0 : ¬(1 ≤ (0 : ℕ) ∧ (0 : ℕ) ≤ p - 1) := by omega
      have hp' : ¬(1 ≤ p ∧ p ≤ p - 1) := by omega
      simp only [Nat.cast_zero, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, h0, hp',
        not_false_eq_true, and_true]
    · intro k hk1 hk2
      rw [if_neg]
      rintro ⟨-, hnm⟩
      exact hnm ⟨hk1, hk2⟩
  have hb := binom_mid p hp hp5 ρ
  have e0 : (if ((0 : ZMod 3) = ρ) then (1 : ℤ) else 0) = (if (ρ = 0) then (1 : ℤ) else 0) := by
    by_cases h : ρ = 0 <;> simp [h, eq_comm]
  have ep : (if (((p : ℕ) : ZMod 3) = ρ) then (1 : ℤ) else 0)
      = (if (ρ = ((p : ℕ) : ZMod 3)) then (1 : ℤ) else 0) := by
    by_cases h : ρ = ((p : ℕ) : ZMod 3) <;> simp [h, eq_comm]
  rw [e0, ep] at hsplit
  linarith [hsplit, hb]

/-- Total middle sum equals `2^p - 2`. -/
lemma midV (p : ℕ) (hp5 : 5 ≤ p) :
    ∑ k ∈ range (p + 1), (if (1 ≤ k ∧ k ≤ p - 1) then (p.choose k : ℤ) else 0) = 2 ^ p - 2 := by
  have hpt : ∀ k ∈ range (p + 1), ((p.choose k : ℤ))
      = (if (1 ≤ k ∧ k ≤ p - 1) then (p.choose k : ℤ) else 0)
        + (if ¬(1 ≤ k ∧ k ≤ p - 1) then (p.choose k : ℤ) else 0) := by
    intro k _; by_cases hm : (1 ≤ k ∧ k ≤ p - 1) <;> simp [hm]
  have htot : ∑ k ∈ range (p + 1), (p.choose k : ℤ) = 2 ^ p := by
    have := Nat.sum_range_choose p; exact_mod_cast this
  have hends : ∑ k ∈ range (p + 1), (if ¬(1 ≤ k ∧ k ≤ p - 1) then (p.choose k : ℤ) else 0) = 2 := by
    rw [endpoint_sum p hp5 (fun k => if ¬(1 ≤ k ∧ k ≤ p - 1) then (p.choose k : ℤ) else 0)]
    · have h0 : ¬(1 ≤ (0 : ℕ) ∧ (0 : ℕ) ≤ p - 1) := by omega
      have hp' : ¬(1 ≤ p ∧ p ≤ p - 1) := by omega
      simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, h0, hp']
      norm_num
    · intro k hk1 hk2
      rw [if_neg (not_not.mpr ⟨hk1, hk2⟩)]
  have hsum := Finset.sum_congr rfl hpt
  rw [Finset.sum_add_distrib] at hsum
  rw [htot] at hsum
  rw [hends] at hsum
  linarith [hsum]

/- Theorem 3 -/

theorem cart_qG (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : Cart p (qser p * Gser) = 0 := by
  have hp0 : 0 < p := by omega
  ext n
  rw [coeff_Cart, coeffMulG, map_zero]
  simp only [coeff_qser]
  -- goal: ∑ k∈range(p*n+1), qc p k * gc(p*n-k) = 0
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [qc]
  -- n ≥ 1
  have hpn : p ≤ p * n := Nat.le_mul_of_pos_right p hn
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have key : (p : ℤ) * (∑ k ∈ range (p * n + 1), qc p k * gc (p * n - k)) = 0 := by
    rw [Finset.mul_sum]
    have step : ∀ k ∈ range (p * n + 1), (p : ℤ) * (qc p k * gc (p * n - k))
        = (if (1 ≤ k ∧ k ≤ p - 1) then (p.choose k : ℤ) else 0) * gc (p * n - k) := by
      intro k _; rw [← mul_assoc, pqc p hp k]
    rw [Finset.sum_congr rfl step]
    -- restrict to range (p+1)
    have hsub : range (p + 1) ⊆ range (p * n + 1) := by
      intro x hx; rw [Finset.mem_range] at hx ⊢; omega
    rw [← Finset.sum_subset hsub]
    · -- expand gc, split, apply Umid + midV
      have step2 : ∀ k ∈ range (p + 1),
          (if (1 ≤ k ∧ k ≤ p - 1) then (p.choose k : ℤ) else 0) * gc (p * n - k)
          = 3 * (if (((k : ℕ) : ZMod 3) = ((p * n : ℕ) : ZMod 3) ∧ 1 ≤ k ∧ k ≤ p - 1)
                  then (p.choose k : ℤ) else 0)
            - (if (1 ≤ k ∧ k ≤ p - 1) then (p.choose k : ℤ) else 0) := by
        intro k hk
        rw [Finset.mem_range] at hk
        have hdvd : (3 ∣ (p * n - k)) ↔ (((k : ℕ) : ZMod 3) = ((p * n : ℕ) : ZMod 3)) := by
          rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (by omega : k ≤ p * n), sub_eq_zero]
          exact eq_comm
        by_cases hm : (1 ≤ k ∧ k ≤ p - 1)
        · have hj : 1 ≤ p * n - k := by have := hm.2; omega
          rw [if_pos hm, gc_pos _ hj]
          by_cases hd : 3 ∣ (p * n - k)
          · rw [if_pos hd, if_pos ⟨hdvd.mp hd, hm⟩]; ring
          · rw [if_neg hd, if_neg (fun h => hd (hdvd.mpr h.1))]; ring
        · rw [if_neg hm, if_neg (fun h => hm h.2)]; ring
      rw [Finset.sum_congr rfl step2, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Umid p hp hp5 ((p * n : ℕ) : ZMod 3), midV p hp5]
      ring
    · intro x hx hxns
      rw [Finset.mem_range] at hx
      simp only [Finset.mem_range, not_lt] at hxns
      rw [if_neg (by omega : ¬(1 ≤ x ∧ x ≤ p - 1)), zero_mul]
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hpne
  · exact h


/- Theorem 4 machinery -/

/-- General coefficient of a product as a `range` sum. -/
lemma coeffMul (W Q : PowerSeries ℤ) (N : ℕ) :
    (PowerSeries.coeff N) (W * Q)
      = ∑ k ∈ range (N + 1), (PowerSeries.coeff k) W * (PowerSeries.coeff (N - k)) Q := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (PowerSeries.coeff i) W * (PowerSeries.coeff j) Q) N]

/-- Three consecutive positive coefficients of `G` sum to zero. -/
lemma gc_three (a : ℕ) (ha : 1 ≤ a) : gc a + gc (a + 1) + gc (a + 2) = 0 := by
  unfold gc
  rw [if_neg (by omega : ¬ a = 0), if_neg (by omega : ¬ a + 1 = 0),
      if_neg (by omega : ¬ a + 2 = 0)]
  rcases (by omega : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2) with h | h | h
  · rw [if_pos h, if_neg (by omega), if_neg (by omega)]; ring
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; ring
  · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega)]; ring

lemma coeff_X_mul_G (n : ℕ) :
    (PowerSeries.coeff n) (PowerSeries.X * Gser) = if n = 0 then 0 else gc (n - 1) := by
  cases n with
  | zero => rw [coeff_zero_X_mul, if_pos rfl]
  | succ k => rw [coeff_succ_X_mul, coeff_Gser]; simp

lemma coeff_X2_mul_G (n : ℕ) :
    (PowerSeries.coeff n) (PowerSeries.X ^ 2 * Gser) = if n ≤ 1 then 0 else gc (n - 2) := by
  rw [pow_two, mul_assoc]
  cases n with
  | zero => rw [coeff_zero_X_mul, if_pos (by omega)]
  | succ k =>
    rw [coeff_succ_X_mul, coeff_X_mul_G]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · rw [if_neg (by omega : ¬ k = 0), if_neg (by omega : ¬ k + 1 ≤ 1),
          (by omega : k + 1 - 2 = k - 1)]

/-- The defining identity `(1 + X + X²) · G = 1 - X²`. -/
lemma AG : ((1 : PowerSeries ℤ) + PowerSeries.X + PowerSeries.X ^ 2) * Gser
    = (1 : PowerSeries ℤ) - PowerSeries.X ^ 2 := by
  ext n
  rw [add_mul, add_mul, one_mul, map_add, map_add, map_sub, coeff_Gser,
      coeff_X_mul_G, coeff_X2_mul_G, coeff_one, coeff_X_pow]
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> simp [gc]
  · rw [if_neg (show ¬ n = 0 by omega), if_neg (show ¬ n ≤ 1 by omega),
        if_neg (show ¬ n = 0 by omega), if_neg (show ¬ n = 2 by omega)]
    have h3 := gc_three (n - 2) (by omega)
    rw [(by omega : (n - 2) + 1 = n - 1), (by omega : (n - 2) + 2 = n)] at h3
    linarith [h3]

/-- `(1 + X + X²) · (q·G) = q·(1 - X²)`. -/
lemma APeq (p : ℕ) :
    ((1 : PowerSeries ℤ) + PowerSeries.X + PowerSeries.X ^ 2) * (qser p * Gser)
      = qser p * (1 - PowerSeries.X ^ 2) := by
  rw [← mul_assoc, mul_comm ((1 : PowerSeries ℤ) + PowerSeries.X + PowerSeries.X ^ 2) (qser p),
      mul_assoc, AG]

/-- Recurrence for the coefficients of `q·G`. -/
lemma Rrec (p m : ℕ) :
    (PowerSeries.coeff (m + 2)) (qser p * Gser) + (PowerSeries.coeff (m + 1)) (qser p * Gser)
      + (PowerSeries.coeff m) (qser p * Gser) = qc p (m + 2) - qc p m := by
  have e1 : (PowerSeries.coeff (m + 2)) (PowerSeries.X * (qser p * Gser))
      = (PowerSeries.coeff (m + 1)) (qser p * Gser) := coeff_succ_X_mul (m + 1) _
  have e2 : (PowerSeries.coeff (m + 2)) (PowerSeries.X ^ 2 * (qser p * Gser))
      = (PowerSeries.coeff m) (qser p * Gser) := by
    rw [pow_two, mul_assoc, coeff_succ_X_mul (m + 1) (PowerSeries.X * (qser p * Gser)),
        coeff_succ_X_mul m (qser p * Gser)]
  calc (PowerSeries.coeff (m + 2)) (qser p * Gser)
          + (PowerSeries.coeff (m + 1)) (qser p * Gser) + (PowerSeries.coeff m) (qser p * Gser)
      = (PowerSeries.coeff (m + 2))
          (((1 : PowerSeries ℤ) + PowerSeries.X + PowerSeries.X ^ 2) * (qser p * Gser)) := by
        rw [add_mul, add_mul, one_mul, map_add, map_add, e1, e2]
    _ = (PowerSeries.coeff (m + 2)) (qser p * (1 - PowerSeries.X ^ 2)) := by rw [APeq]
    _ = qc p (m + 2) - qc p m := by
        rw [mul_sub, mul_one, map_sub, coeff_qser, mul_comm (qser p) (PowerSeries.X ^ 2), pow_two,
            mul_assoc, coeff_succ_X_mul, coeff_succ_X_mul, coeff_qser]

/-- `q` is palindromic. -/
lemma qc_symm (p x : ℕ) (hx : x ≤ p) : qc p (p - x) = qc p x := by
  unfold qc
  by_cases h : 1 ≤ x ∧ x ≤ p - 1
  · have h' : 1 ≤ p - x ∧ p - x ≤ p - 1 := by omega
    rw [if_pos h, if_pos h', Nat.choose_symm hx]
  · have h' : ¬ (1 ≤ p - x ∧ p - x ≤ p - 1) := by omega
    rw [if_neg h, if_neg h']

/-- `q·G` is a polynomial of degree `< p`: coefficients at index `≥ p` vanish. -/
lemma qG_coeff_zero (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N : ℕ) (hN : p ≤ N) :
    (PowerSeries.coeff N) (qser p * Gser) = 0 := by
  have hp0 : 0 < p := by omega
  rw [coeffMulG]
  simp only [coeff_qser]
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have key : (p : ℤ) * (∑ k ∈ range (N + 1), qc p k * gc (N - k)) = 0 := by
    rw [Finset.mul_sum]
    have step : ∀ k ∈ range (N + 1), (p : ℤ) * (qc p k * gc (N - k))
        = (if (1 ≤ k ∧ k ≤ p - 1) then (p.choose k : ℤ) else 0) * gc (N - k) := by
      intro k _; rw [← mul_assoc, pqc p hp k]
    rw [Finset.sum_congr rfl step]
    have hsub : range (p + 1) ⊆ range (N + 1) := by
      intro x hx; rw [Finset.mem_range] at hx ⊢; omega
    rw [← Finset.sum_subset hsub]
    · have step2 : ∀ k ∈ range (p + 1),
          (if (1 ≤ k ∧ k ≤ p - 1) then (p.choose k : ℤ) else 0) * gc (N - k)
          = 3 * (if (((k : ℕ) : ZMod 3) = ((N : ℕ) : ZMod 3) ∧ 1 ≤ k ∧ k ≤ p - 1)
                  then (p.choose k : ℤ) else 0)
            - (if (1 ≤ k ∧ k ≤ p - 1) then (p.choose k : ℤ) else 0) := by
        intro k hk
        rw [Finset.mem_range] at hk
        have hdvd : (3 ∣ (N - k)) ↔ (((k : ℕ) : ZMod 3) = ((N : ℕ) : ZMod 3)) := by
          rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (by omega : k ≤ N), sub_eq_zero]
          exact eq_comm
        by_cases hm : (1 ≤ k ∧ k ≤ p - 1)
        · have hj : 1 ≤ N - k := by have := hm.2; omega
          rw [if_pos hm, gc_pos _ hj]
          by_cases hd : 3 ∣ (N - k)
          · rw [if_pos hd, if_pos ⟨hdvd.mp hd, hm⟩]; ring
          · rw [if_neg hd, if_neg (fun h => hd (hdvd.mpr h.1))]; ring
        · rw [if_neg hm, if_neg (fun h => hm h.2)]; ring
      rw [Finset.sum_congr rfl step2, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Umid p hp hp5 ((N : ℕ) : ZMod 3), midV p hp5]
      ring
    · intro x hx hxns
      rw [Finset.mem_range] at hx
      simp only [Finset.mem_range, not_lt] at hxns
      rw [if_neg (by omega : ¬(1 ≤ x ∧ x ≤ p - 1)), zero_mul]
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hpne
  · exact h

/-- Coefficient of `q·G` (abbreviation). -/
noncomputable def Rr (p j : ℕ) : ℤ := (PowerSeries.coeff j) (qser p * Gser)

/-- Symmetrized coefficient. -/
noncomputable def Dd (p j : ℕ) : ℤ := Rr p j + Rr p (p - j)

lemma Drec (p j : ℕ) (h2 : 2 ≤ j) (hjp : j ≤ p) :
    Dd p j + Dd p (j - 1) + Dd p (j - 2) = 0 := by
  unfold Dd Rr
  have r1 := Rrec p (j - 2)
  have r2 := Rrec p (p - j)
  rw [(by omega : (j - 2) + 2 = j), (by omega : (j - 2) + 1 = j - 1)] at r1
  rw [(by omega : (p - j) + 2 = p - (j - 2)), (by omega : (p - j) + 1 = p - (j - 1)),
      qc_symm p (j - 2) (by omega), qc_symm p j hjp] at r2
  linarith [r1, r2]

lemma Deq3 (p j : ℕ) (h3 : 3 ≤ j) (hjp : j ≤ p) : Dd p j = Dd p (j - 3) := by
  have d1 := Drec p j (by omega) hjp
  have d2 := Drec p (j - 1) (by omega) (by omega)
  rw [(by omega : (j - 1) - 1 = j - 2), (by omega : (j - 1) - 2 = j - 3)] at d2
  linarith [d1, d2]

lemma Dmod (p : ℕ) : ∀ j, j ≤ p → Dd p j = Dd p (j % 3) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjp
    rcases Nat.lt_or_ge j 3 with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]
    · rw [Deq3 p j hge hjp, ih (j - 3) (by omega) (by omega)]
      congr 1; omega

lemma Dzero (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : ∀ j, j ≤ p → Dd p j = 0 := by
  have c0 : (PowerSeries.coeff 0) (qser p * Gser) = 0 := by
    rw [coeffMulG]; simp [qc]
  have cp : (PowerSeries.coeff p) (qser p * Gser) = 0 := qG_coeff_zero p hp hp5 p (le_refl p)
  have hD0 : Dd p 0 = 0 := by unfold Dd Rr; rw [Nat.sub_zero, c0, cp]; ring
  have hDp : Dd p p = 0 := by unfold Dd Rr; rw [Nat.sub_self, cp, c0]; ring
  have dp := Dmod p p (le_refl p)
  have hd2 : Dd p 2 + Dd p 1 + Dd p 0 = 0 := by
    have h := Drec p 2 (by norm_num) (by omega)
    norm_num at h; exact h
  have hp3 : ¬ 3 ∣ p := not_three_dvd_prime p hp hp5
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by omega
  have key3 : Dd p 0 = 0 ∧ Dd p 1 = 0 ∧ Dd p 2 = 0 := by
    rcases hmod with h | h
    · rw [h, hDp] at dp
      exact ⟨hD0, by linarith [dp], by linarith [hd2, hD0, dp]⟩
    · rw [h, hDp] at dp
      exact ⟨hD0, by linarith [hd2, hD0, dp], by linarith [dp]⟩
  intro j hj
  rw [Dmod p j hj]
  have hlt : j % 3 < 3 := by omega
  interval_cases (j % 3)
  · exact key3.1
  · exact key3.2.1
  · exact key3.2.2

/- Theorem 4 -/

theorem cart_q2G (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Cart p (qser p * qser p * Gser) = 0 := by
  have hp0 : 0 < p := by omega
  ext n
  rw [coeff_Cart, map_zero, mul_assoc, coeffMul]
  simp only [coeff_qser]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp [qc]
    · simp only [mul_one]
      have hterm : ∀ i ∈ range (p + 1),
          qc p (p - i) * (PowerSeries.coeff (p - (p - i))) (qser p * Gser)
          = -(qc p i * (PowerSeries.coeff (p - i)) (qser p * Gser)) := by
        intro i hi
        rw [Finset.mem_range] at hi
        have hip : i ≤ p := by omega
        rw [qc_symm p i hip, (by omega : p - (p - i) = i)]
        have hD := Dzero p hp hp5 i hip
        unfold Dd Rr at hD
        have hh : (PowerSeries.coeff i) (qser p * Gser)
            = -(PowerSeries.coeff (p - i)) (qser p * Gser) := by linarith [hD]
        rw [hh]; ring
      have hreflect := Finset.sum_range_reflect
        (fun k => qc p k * (PowerSeries.coeff (p - k)) (qser p * Gser)) (p + 1)
      simp only [Nat.add_sub_cancel] at hreflect
      rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib] at hreflect
      linarith [hreflect]
  · apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases hks : 1 ≤ k ∧ k ≤ p - 1
    · obtain ⟨hk1, hk2⟩ := hks
      have h2p : p * 2 ≤ p * n := Nat.mul_le_mul (le_refl p) hn
      have hz : (PowerSeries.coeff (p * n - k)) (qser p * Gser) = 0 :=
        qG_coeff_zero p hp hp5 _ (by omega)
      rw [hz, mul_zero]
    · rw [show qc p k = 0 by unfold qc; rw [if_neg hks], zero_mul]

/- ============================================================= -/
/-  NEW MATERIAL: the main transfer formula                       -/
/- ============================================================= -/

/- ### `infl` is the `expand` algebra homomorphism -/

lemma infl_eq_expand (p : ℕ) (hp : p ≠ 0) (h : PowerSeries ℤ) :
    infl p h = PowerSeries.expand p hp h := by
  ext n
  simp only [coeff_infl, PowerSeries.coeff_expand]

lemma infl_mul (p : ℕ) (hp : 0 < p) (a b : PowerSeries ℤ) :
    infl p a * infl p b = infl p (a * b) := by
  simp only [infl_eq_expand p hp.ne', map_mul]

lemma infl_one (p : ℕ) (hp : 0 < p) : infl p 1 = 1 := by
  rw [infl_eq_expand p hp.ne', map_one]

lemma inflXeq (p : ℕ) (hp : 0 < p) :
    infl p ((1 : PowerSeries ℤ) + PowerSeries.X) = 1 + PowerSeries.X ^ p := by
  rw [infl_eq_expand p hp.ne', map_add, map_one, PowerSeries.expand_X]

/- ### the inverse of `1 + X` and inflation of it -/

noncomputable def Xinv : PowerSeries ℤ := invOfUnit ((1 : PowerSeries ℤ) + PowerSeries.X) 1

lemma oneAddX_mul_Xinv : ((1 : PowerSeries ℤ) + PowerSeries.X) * Xinv = 1 := by
  unfold Xinv
  exact mul_invOfUnit _ 1 (by simp)

lemma inflinv (p : ℕ) (hp : 0 < p) :
    ((1 : PowerSeries ℤ) + PowerSeries.X ^ p) * infl p Xinv = 1 := by
  rw [show ((1 : PowerSeries ℤ) + PowerSeries.X ^ p) = infl p (1 + PowerSeries.X) from
        (inflXeq p hp).symm,
      infl_mul p hp, oneAddX_mul_Xinv, infl_one p hp]

/- ### `Cart` is additive / `ℤ`-linear -/

@[simp] lemma Cart_zero (p : ℕ) : Cart p 0 = 0 := by
  ext n; simp only [coeff_Cart, map_zero]

lemma Cart_add (p : ℕ) (a b : PowerSeries ℤ) : Cart p (a + b) = Cart p a + Cart p b := by
  ext n; simp only [coeff_Cart, map_add]

lemma Cart_sub (p : ℕ) (a b : PowerSeries ℤ) : Cart p (a - b) = Cart p a - Cart p b := by
  ext n; simp only [coeff_Cart, map_sub]

lemma Cart_smul (p : ℕ) (c : ℤ) (a : PowerSeries ℤ) : Cart p (c • a) = c • Cart p a := by
  ext n; simp only [coeff_Cart, map_smul]

lemma Cart_sum (p : ℕ) (s : Finset ℕ) (f : ℕ → PowerSeries ℤ) :
    Cart p (∑ j ∈ s, f j) = ∑ j ∈ s, Cart p (f j) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Cart_add, ih]

/- ### `ρ` and `p·ρ` -/

noncomputable def rho (p : ℕ) : PowerSeries ℤ := qser p * infl p Xinv

noncomputable def prho (p : ℕ) : PowerSeries ℤ := (p : ℤ) • rho p

lemma coeff_zero_qser (p : ℕ) : (PowerSeries.coeff 0) (qser p) = 0 := by
  rw [coeff_qser]; simp [qc]

lemma constantCoeff_prho (p : ℕ) : constantCoeff (prho p) = 0 := by
  have h0 : (PowerSeries.coeff 0) (qser p * infl p Xinv) = 0 := by
    rw [coeffMul]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    interval_cases k
    rw [coeff_zero_qser, zero_mul]
  have h : (PowerSeries.coeff 0) (prho p) = 0 := by
    unfold prho rho
    rw [map_smul, h0, smul_zero]
  rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h

lemma hasSubst_prho (p : ℕ) : PowerSeries.HasSubst (prho p) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_prho p)

/- ### the polynomial identity and the factorisation of `(1+X)^p` -/

lemma polyid (p : ℕ) (hp : p.Prime) :
    ((1 : PowerSeries ℤ) + PowerSeries.X) ^ p = 1 + PowerSeries.X ^ p + (p : ℤ) • qser p := by
  have hp2 : 2 ≤ p := hp.two_le
  ext n
  rw [← binomialSeries_nat (R := ℤ) (A := ℤ) p, binomialSeries_coeff, Ring.choose_natCast,
      map_add, map_add, coeff_one, coeff_X_pow, map_smul, coeff_qser]
  simp only [smul_eq_mul, mul_one]
  rw [pqc p hp]
  rcases Nat.lt_trichotomy n p with hlt | heq | hgt
  · rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      rw [Nat.choose_zero_right, if_pos rfl, if_neg (by omega : ¬ (0 : ℕ) = p),
          if_neg (by omega : ¬ (1 ≤ 0 ∧ (0 : ℕ) ≤ p - 1))]
      norm_num
    · rw [if_neg (by omega : ¬ n = 0), if_neg (by omega : ¬ n = p),
          if_pos (by omega : 1 ≤ n ∧ n ≤ p - 1)]; ring
  · rw [heq, if_neg (by omega : ¬ p = 0), if_pos rfl,
        if_neg (by omega : ¬ (1 ≤ p ∧ p ≤ p - 1)), Nat.choose_self]
    norm_num
  · rw [if_neg (by omega : ¬ n = 0), if_neg (by omega : ¬ n = p),
        if_neg (by omega : ¬ (1 ≤ n ∧ n ≤ p - 1)), Nat.choose_eq_zero_of_lt hgt]; simp

lemma core (p : ℕ) (hp : p.Prime) :
    ((1 : PowerSeries ℤ) + PowerSeries.X) ^ p
      = (1 + PowerSeries.X ^ p) * (1 + prho p) := by
  have hp0 : 0 < p := hp.pos
  have hinv := inflinv p hp0
  have key : (1 + PowerSeries.X ^ p) * (1 + prho p)
      = 1 + PowerSeries.X ^ p + (p : ℤ) • qser p := by
    unfold prho rho
    have hqq : (1 + PowerSeries.X ^ p) * ((p : ℤ) • (qser p * infl p Xinv))
        = (p : ℤ) • qser p := by
      rw [mul_smul_comm]
      congr 1
      rw [← mul_assoc, mul_comm (1 + PowerSeries.X ^ p) (qser p), mul_assoc, hinv, mul_one]
    rw [mul_add, mul_one, hqq]
  rw [key, polyid p hp]

/- ### the master identity `(1+X)^{z·p} = infl((1+X)^z) · (1+pρ)^z` -/

lemma master (p : ℕ) (hp : p.Prime) (z : ℤ) :
    binomialSeries ℤ (z * p)
      = infl p (binomialSeries ℤ z) * (binomialSeries ℤ z).subst (prho p) := by
  have hp0 : 0 < p := hp.pos
  have hsub := hasSubst_prho p
  set c : PowerSeries ℤ := binomialSeries ℤ (p : ℤ) with hc
  have hsubone : (1 : PowerSeries ℤ).subst (prho p) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hsub, map_one]
  have hcne : c ≠ 0 := by
    rw [hc, binomialSeries_nat]
    intro h
    have hcc : constantCoeff (((1 : PowerSeries ℤ) + PowerSeries.X) ^ p) = 0 := by rw [h]; simp
    rw [map_pow] at hcc; simp at hcc
  have hc1 : c = infl p (binomialSeries ℤ (1 : ℤ)) * (binomialSeries ℤ (1 : ℤ)).subst (prho p) := by
    have e1 : binomialSeries ℤ (1 : ℤ) = 1 + PowerSeries.X := by
      have h := binomialSeries_nat (A := ℤ) (R := ℤ) 1
      simpa using h
    rw [e1, hc, binomialSeries_nat, core p hp, inflXeq p hp0,
        PowerSeries.subst_add hsub, PowerSeries.subst_X hsub, hsubone]
  have Lstep : ∀ w : ℤ, binomialSeries ℤ ((w + 1) * p)
      = binomialSeries ℤ (w * p) * c := by
    intro w
    rw [add_mul, one_mul, binomialSeries_add, hc]
  have Rstep : ∀ w : ℤ,
      infl p (binomialSeries ℤ (w + 1)) * (binomialSeries ℤ (w + 1)).subst (prho p)
        = (infl p (binomialSeries ℤ w) * (binomialSeries ℤ w).subst (prho p)) * c := by
    intro w
    rw [binomialSeries_add, ← infl_mul p hp0, PowerSeries.subst_mul hsub, hc1]
    ring
  refine Int.induction_on z ?_ ?_ ?_
  · simp only [zero_mul, binomialSeries_zero]
    rw [infl_one p hp0, one_mul, hsubone]
  · intro i hi
    rw [Lstep (i : ℤ), Rstep (i : ℤ), hi]
  · intro i hi
    have hL := Lstep (-(i : ℤ) - 1)
    have hR := Rstep (-(i : ℤ) - 1)
    rw [show (-(i : ℤ) - 1) + 1 = -(i : ℤ) by ring] at hL hR
    have hcancel : binomialSeries ℤ ((-(i : ℤ) - 1) * p) * c
        = (infl p (binomialSeries ℤ (-(i : ℤ) - 1))
            * (binomialSeries ℤ (-(i : ℤ) - 1)).subst (prho p)) * c := by
      rw [← hL, ← hR]; exact hi
    exact mul_right_cancel₀ hcne hcancel

/- ### the named definitions `ℓ`, `u`, `ψ` -/

/-- `ℓ Ψ AM M = [X^M] ((1+X)^{AM} · Ψ)` where `(1+X)^{AM}` is the binomial series. -/
noncomputable def ℓ (Ψ : PowerSeries ℤ) (AM : ℤ) (M : ℕ) : ℤ :=
  (PowerSeries.coeff M) (binomialSeries ℤ AM * Ψ)

/-- `u AM M = ℓ Gser AM M`. -/
noncomputable def u (AM : ℤ) (M : ℕ) : ℤ := ℓ Gser AM M

/-- `ψ p j = Cart p (ρ^j · G)`. -/
noncomputable def ψ (p : ℕ) (j : ℕ) : PowerSeries ℤ := Cart p ((rho p) ^ j * Gser)

lemma ell_zero (AM : ℤ) (M : ℕ) : ℓ 0 AM M = 0 := by
  unfold ℓ; rw [mul_zero, map_zero]

/- ### the substitution expands as a finite binomial sum (up to the required order) -/

lemma coeff_prho_pow_high (p : ℕ) (n d : ℕ) (hnd : n < d) :
    (PowerSeries.coeff n) ((prho p) ^ d) = 0 := by
  have hX : (PowerSeries.X : PowerSeries ℤ) ∣ prho p := by
    rw [PowerSeries.X_dvd_iff]; exact constantCoeff_prho p
  have hpow : (PowerSeries.X : PowerSeries ℤ) ^ d ∣ (prho p) ^ d := pow_dvd_pow_of_dvd hX d
  exact (PowerSeries.X_pow_dvd_iff.mp hpow) n hnd

lemma B_coeff_eq (p : ℕ) (AM : ℤ) (K n : ℕ) (hn : n ≤ K) :
    (PowerSeries.coeff n) ((binomialSeries ℤ AM).subst (prho p))
      = (PowerSeries.coeff n) (∑ j ∈ range (K + 1), Ring.choose AM j • (prho p) ^ j) := by
  have hsub := hasSubst_prho p
  rw [PowerSeries.coeff_subst' hsub]
  simp only [binomialSeries_coeff, smul_eq_mul, mul_one, map_sum, map_smul]
  have hsupp : Function.support
      (fun d => Ring.choose AM d * (PowerSeries.coeff n) ((prho p) ^ d))
      ⊆ (range (K + 1) : Finset ℕ) := by
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    have hdlt : d < K + 1 := by
      by_contra hcon
      push_neg at hcon
      exact hd (by rw [coeff_prho_pow_high p n d (by omega), mul_zero])
    exact Finset.mem_coe.mpr (Finset.mem_range.mpr hdlt)
  rw [finsum_eq_finset_sum_of_support_subset _ hsupp]

/- ### the vanishing lemma controlling the truncation -/

lemma vanish (p : ℕ) (hp0 : 0 < p) (M : ℕ) (E D : PowerSeries ℤ)
    (hD : ∀ n, n ≤ M * p → (PowerSeries.coeff n) D = 0) :
    (PowerSeries.coeff M) (E * Cart p (D * Gser)) = 0 := by
  rw [coeffMul]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_range] at hk
  have hz : (PowerSeries.coeff (M - k)) (Cart p (D * Gser)) = 0 := by
    rw [coeff_Cart, coeffMulG]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    have hb : p * (M - k) ≤ p * M := Nat.mul_le_mul (le_refl p) (Nat.sub_le M k)
    have hpm : p * M = M * p := Nat.mul_comm p M
    rw [hD i (by omega), zero_mul]
  rw [hz, mul_zero]

lemma agree_coeffM (p : ℕ) (hp0 : 0 < p) (M : ℕ) (E D1 D2 : PowerSeries ℤ)
    (h : ∀ n, n ≤ M * p → (PowerSeries.coeff n) D1 = (PowerSeries.coeff n) D2) :
    (PowerSeries.coeff M) (E * Cart p (D1 * Gser)) = (PowerSeries.coeff M) (E * Cart p (D2 * Gser)) := by
  have hzero : (PowerSeries.coeff M) (E * Cart p ((D1 - D2) * Gser)) = 0 :=
    vanish p hp0 M E (D1 - D2) (by intro n hn; rw [map_sub, h n hn, sub_self])
  have hexp : E * Cart p ((D1 - D2) * Gser)
      = E * Cart p (D1 * Gser) - E * Cart p (D2 * Gser) := by
    rw [sub_mul, Cart_sub, mul_sub]
  rw [hexp, map_sub, sub_eq_zero] at hzero
  exact hzero

/- ### `Cart` of the finite binomial sum -/

lemma cart_prho_pow (p : ℕ) (j : ℕ) :
    Cart p ((prho p) ^ j * Gser) = (p : ℤ) ^ j • ψ p j := by
  unfold prho ψ
  rw [smul_pow, smul_mul_assoc, Cart_smul]

lemma cart_Bfin (p : ℕ) (K : ℕ) (AM : ℤ) :
    Cart p ((∑ j ∈ range (K + 1), Ring.choose AM j • (prho p) ^ j) * Gser)
      = ∑ j ∈ range (K + 1), Ring.choose AM j • ((p : ℤ) ^ j • ψ p j) := by
  rw [Finset.sum_mul, Cart_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_mul_assoc, Cart_smul, cart_prho_pow]

/- ### the values `ψ 0, ψ 1, ψ 2` -/

lemma psi0 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : ψ p 0 = Gser := by
  unfold ψ; rw [pow_zero, one_mul]; exact cart_G p hp hp5

lemma psi1 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : ψ p 1 = 0 := by
  unfold ψ rho
  rw [pow_one, mul_comm (qser p) (infl p Xinv), mul_assoc, cart_infl_mul p hp.pos,
      cart_qG p hp hp5, mul_zero]

lemma psi2 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : ψ p 2 = 0 := by
  have hp0 : 0 < p := hp.pos
  unfold ψ rho
  rw [mul_pow, sq (infl p Xinv), infl_mul p hp0, sq (qser p),
      mul_comm (qser p * qser p) (infl p (Xinv * Xinv)), mul_assoc,
      cart_infl_mul p hp0, cart_q2G p hp hp5, mul_zero]

/- ### the main transfer formula -/

theorem transfer (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (M : ℕ) (AM : ℤ) :
    u (AM * p) (M * p)
      = ∑ j ∈ Finset.range (M * p + 1),
          Ring.choose AM j * (p : ℤ) ^ j * ℓ (ψ p j) AM M := by
  have hp0 : 0 < p := hp.pos
  have step1 : u (AM * p) (M * p)
      = (PowerSeries.coeff M) (Cart p (binomialSeries ℤ (AM * p) * Gser)) := by
    unfold u ℓ
    rw [coeff_Cart, Nat.mul_comm p M]
  rw [step1, master p hp AM, mul_assoc, cart_infl_mul p hp0,
      agree_coeffM p hp0 M (binomialSeries ℤ AM) ((binomialSeries ℤ AM).subst (prho p))
        (∑ j ∈ range (M * p + 1), Ring.choose AM j • (prho p) ^ j)
        (fun n hn => B_coeff_eq p AM (M * p) n hn),
      cart_Bfin p (M * p) AM, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold ℓ
  rw [mul_smul_comm, mul_smul_comm, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/- ### the corollary: the difference is a sum over `j ≥ 3` -/

theorem main_formula (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (M : ℕ) (AM : ℤ) :
    u (AM * p) (M * p) - u AM M
      = ∑ j ∈ (range (M * p + 1)).filter (fun j => 3 ≤ j),
          Ring.choose AM j * (p : ℤ) ^ j * ℓ (ψ p j) AM M := by
  have ht := transfer p hp hp5 M AM
  set f : ℕ → ℤ := fun j => Ring.choose AM j * (p : ℤ) ^ j * ℓ (ψ p j) AM M with hf
  have hsplit := Finset.sum_filter_add_sum_filter_not (range (M * p + 1)) (fun j => 3 ≤ j) f
  have hnot : ∑ j ∈ (range (M * p + 1)).filter (fun j => ¬ 3 ≤ j), f j = u AM M := by
    have h0mem : (0 : ℕ) ∈ (range (M * p + 1)).filter (fun j => ¬ 3 ≤ j) := by
      rw [Finset.mem_filter, Finset.mem_range]; omega
    rw [Finset.sum_eq_single_of_mem 0 h0mem]
    · show Ring.choose AM 0 * (p : ℤ) ^ 0 * ℓ (ψ p 0) AM M = u AM M
      simp only [Ring.choose_zero_right, pow_zero, mul_one, one_mul, psi0 p hp hp5, u]
    · intro j hj hjne
      rw [Finset.mem_filter, Finset.mem_range] at hj
      have hj3 : j < 3 := by omega
      interval_cases j
      · exact absurd rfl hjne
      · show Ring.choose AM 1 * (p : ℤ) ^ 1 * ℓ (ψ p 1) AM M = 0
        rw [psi1 p hp hp5, ell_zero, mul_zero]
      · show Ring.choose AM 2 * (p : ℤ) ^ 2 * ℓ (ψ p 2) AM M = 0
        rw [psi2 p hp hp5, ell_zero, mul_zero]
  rw [ht, ← hsplit, hnot]
  ring

#print axioms transfer
#print axioms main_formula
