import FormalConjectures.Util.ProblemImports

section SpecDefs
open Nat Finset BigOperators Int

def generalized_choose_int (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else
    (Finset.prod (Finset.range k) fun i => r - (i : ℤ)) / (k.factorial : ℤ)

-- Helper definition for the generalized coefficient formula.
/--
The $k$-th power series coefficient of $c(x)^r$: $\frac{r}{r+k}\binom{r+2k-1}{k}$.
This expression is known to be an integer for all $r \in \mathbb{Z}$.
-/
def generalized_catalan_coefficient (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else
    let num_choose := generalized_choose_int (r + 2 * (k : ℤ) - 1) k
    let denominator : ℤ := r + k
    -- The division is exact because the coefficient is an integer.
    -- We rely on integer division to compute the result.
    (r * num_choose) / denominator

/--
The generalized sequence $a_m(n)$ is the $n$-th order Taylor polynomial (centered at 0) of $c(x)^{m \cdot n}$ evaluated at $x=1$.
$$a_m(n) = \sum_{k=0}^n [x^k] c(x)^{m n}$$
-/
def a_gen (m : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 1
  else
    let r : ℤ := m * (n : ℤ)
    Finset.sum (range (n + 1)) fun k =>
      generalized_catalan_coefficient r k

/--
A333096: The $n$-th order Taylor polynomial (centered at 0) of $c(x)^{4n}$ evaluated at $x=1$, where $c(x) = \frac{1 - \sqrt{1 - 4x}}{2x}$ is the o.g.f. of the sequence of Catalan numbers $A000108$.
The sequence is defined by the formula:
$$a(n) = \sum_{k = 0}^n \frac{4n}{4n+k}\binom{4n+2k-1}{k} \quad \text{for } n \ge 1$$
and $a(0) = 1.$$
The summand is the $k$-th coefficient of the power series $c(x)^{4n}$, which is an integer.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.sum (range (n + 1)) fun k =>
      let m : ℕ := 4 * n
      let numerator : ℕ := m * (m + 2 * k - 1).choose k
      let denominator : ℕ := m + k
      -- Since the combinatorial identity guarantees exact divisibility, Nat division is equivalent to integer division.
      numerator / denominator


end SpecDefs

section Mainformula
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

end Mainformula

section P1
open Nat Finset BigOperators Int

def gcoef (j : ℕ) : ℤ := if j = 0 then 1 else if j % 3 = 0 then 2 else -1

open Polynomial in
/-- The descending Pochhammer product form. -/
lemma prodk (N : ℤ) (j : ℕ) :
    (∏ i ∈ range j, (N - (i:ℤ))) = (j.factorial : ℤ) * Ring.choose N j := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) N j
  rw [nsmul_eq_mul] at h
  rw [← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range] at h
  exact h

/-- (L0) `generalized_choose_int` agrees with `Ring.choose`. -/
lemma L0 (r : ℤ) (k : ℕ) : generalized_choose_int r k = Ring.choose r k := by
  rw [generalized_choose_int]
  split_ifs with hk
  · subst hk; rw [Ring.choose_zero_right]
  · rw [prodk, Int.mul_ediv_cancel_left]
    exact_mod_cast Nat.factorial_ne_zero k

/-- Absorption identity for `Ring.choose`. -/
lemma ABS (N : ℤ) (k : ℕ) :
    ((k + 1 : ℕ) : ℤ) * Ring.choose N (k + 1) = (N - (k:ℤ)) * Ring.choose N k := by
  have hk : ((k.factorial : ℤ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  apply mul_left_cancel₀ hk
  have e1 : (k.factorial : ℤ) * (((k + 1 : ℕ) : ℤ) * Ring.choose N (k + 1))
      = ∏ i ∈ range (k + 1), (N - (i:ℤ)) := by
    rw [prodk]
    have : ((k + 1).factorial : ℤ) = ((k + 1 : ℕ) : ℤ) * (k.factorial : ℤ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [this]; ring
  have e2 : (k.factorial : ℤ) * ((N - (k:ℤ)) * Ring.choose N k)
      = ∏ i ∈ range (k + 1), (N - (i:ℤ)) := by
    rw [Finset.prod_range_succ, prodk]; ring
  rw [e1, e2]

/-- (L1) Fuss–Catalan coefficient equals a difference of binomials. -/
lemma L1 (r : ℤ) (k : ℕ) (hk : 1 ≤ k) (hne : r + (k:ℤ) ≠ 0) :
    generalized_catalan_coefficient r k
      = Ring.choose (r + 2 * (k:ℤ) - 1) k - Ring.choose (r + 2 * (k:ℤ) - 1) (k - 1) := by
  have hk0 : k ≠ 0 := by omega
  rw [generalized_catalan_coefficient, if_neg hk0]
  simp only []
  rw [L0]
  set N : ℤ := r + 2 * (k:ℤ) - 1 with hNdef
  -- absorption specialized to (k-1)
  have habs := ABS N (k - 1)
  rw [Nat.sub_add_cancel hk] at habs
  have hcast : ((k - 1 : ℕ) : ℤ) = (k:ℤ) - 1 := by rw [Nat.cast_sub hk]; simp
  have hNk : N - ((k - 1 : ℕ) : ℤ) = r + (k:ℤ) := by
    rw [hcast, hNdef]; ring
  -- (r+k) * choose N (k-1) = k * choose N k
  have h2 : (r + (k:ℤ)) * Ring.choose N (k - 1) = (k:ℤ) * Ring.choose N k := by
    rw [← hNk, ← habs]
  have hmain : r * Ring.choose N k = (r + (k:ℤ)) * (Ring.choose N k - Ring.choose N (k - 1)) := by
    linear_combination h2
  rw [hmain, Int.mul_ediv_cancel_left _ hne]

def P (A : ℤ) (m : ℕ) : ℤ := ∑ j ∈ range (m + 1), gcoef j * Ring.choose A (m - j)

lemma P_def (A : ℤ) (m : ℕ) :
    P A m = ∑ j ∈ range (m + 1), gcoef j * Ring.choose A (m - j) := rfl

/-- Reflected form of `P` (choose index as summation variable). -/
lemma Preflect (A : ℤ) (m : ℕ) :
    P A m = ∑ i ∈ range (m + 1), gcoef (m - i) * Ring.choose A i := by
  rw [P_def, ← Finset.sum_range_reflect (fun j => gcoef j * Ring.choose A (m - j)) (m + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have h1 : m + 1 - 1 - i = m - i := by omega
  have h2 : m - (m - i) = i := by omega
  rw [h1, h2]

lemma gpos (t : ℕ) (ht : t ≠ 0) : gcoef t = if t % 3 = 0 then (2:ℤ) else -1 := by
  unfold gcoef; rw [if_neg ht]

lemma gsum3 (t : ℕ) (ht : 1 ≤ t) : gcoef t + gcoef (t + 1) + gcoef (t + 2) = 0 := by
  rw [gpos t (by omega), gpos (t + 1) (by omega), gpos (t + 2) (by omega)]
  rcases (by omega : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2) with h | h | h
  · rw [if_pos h, if_neg (show (t+1)%3 ≠ 0 by omega), if_neg (show (t+2)%3 ≠ 0 by omega)]; ring
  · rw [if_neg (show t%3 ≠ 0 by omega), if_neg (show (t+1)%3 ≠ 0 by omega),
        if_pos (show (t+2)%3 = 0 by omega)]; ring
  · rw [if_neg (show t%3 ≠ 0 by omega), if_pos (show (t+1)%3 = 0 by omega),
        if_neg (show (t+2)%3 ≠ 0 by omega)]; ring

/-- (COLLAPSE) three consecutive `P` values collapse (period-3 of `gcoef`). -/
lemma collapse (A : ℤ) (n : ℕ) :
    P A n + P A (n + 1) + P A (n + 2) = Ring.choose A (n + 2) - Ring.choose A n := by
  rw [Preflect A n, Preflect A (n + 1), Preflect A (n + 2)]
  -- peel the top terms
  rw [Finset.sum_range_succ (fun i => gcoef (n + 2 - i) * Ring.choose A i) (n + 2),
      Finset.sum_range_succ (fun i => gcoef (n + 2 - i) * Ring.choose A i) (n + 1)]
  rw [Finset.sum_range_succ (fun i => gcoef (n + 1 - i) * Ring.choose A i) (n + 1)]
  -- combine the three range (n+1) sums
  have hcomb : (∑ i ∈ range (n + 1), gcoef (n + 2 - i) * Ring.choose A i)
      + (∑ i ∈ range (n + 1), gcoef (n + 1 - i) * Ring.choose A i)
      + (∑ i ∈ range (n + 1), gcoef (n - i) * Ring.choose A i)
      = ∑ i ∈ range (n + 1),
          (gcoef (n + 2 - i) + gcoef (n + 1 - i) + gcoef (n - i)) * Ring.choose A i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i hi; ring
  -- evaluate the combined sum via sum_eq_single at i = n
  have hsingle : (∑ i ∈ range (n + 1),
        (gcoef (n + 2 - i) + gcoef (n + 1 - i) + gcoef (n - i)) * Ring.choose A i)
      = - Ring.choose A n := by
    rw [Finset.sum_eq_single n]
    · have : gcoef (n + 2 - n) + gcoef (n + 1 - n) + gcoef (n - n) = -1 := by
        simp only [Nat.add_sub_cancel_left, Nat.sub_self]
        decide
      rw [this]; ring
    · intro b hb hbn
      simp only [Finset.mem_range] at hb
      have e2 : n + 2 - b = (n - b) + 2 := by omega
      have e1 : n + 1 - b = (n - b) + 1 := by omega
      rw [e2, e1]
      have h3 := gsum3 (n - b) (by omega)
      linear_combination Ring.choose A b * h3
    · intro h; exact absurd (Finset.self_mem_range_succ n) h
  -- gcoef values at the boundary
  have g0 : gcoef 0 = 1 := rfl
  have g1 : gcoef 1 = -1 := rfl
  have hS : (∑ i ∈ range (n + 1), gcoef (n + 2 - i) * Ring.choose A i)
        + (∑ i ∈ range (n + 1), gcoef (n + 1 - i) * Ring.choose A i)
        + (∑ i ∈ range (n + 1), gcoef (n - i) * Ring.choose A i)
      = - Ring.choose A n := hcomb.trans hsingle
  have en1 : n + 2 - (n + 1) = 1 := by omega
  have en2 : n + 2 - (n + 2) = 0 := by omega
  have en3 : n + 1 - (n + 1) = 0 := by omega
  rw [en1, en2, en3, g0, g1]
  linear_combination hS

/-- (PP) Pascal-type recursion for `P`. -/
lemma PP (B : ℤ) (m : ℕ) : P (B + 1) (m + 1) = P B (m + 1) + P B m := by
  rw [P_def, P_def, P_def]
  rw [Finset.sum_range_succ (fun j => gcoef j * Ring.choose (B + 1) (m + 1 - j)) (m + 1)]
  rw [Finset.sum_range_succ (fun j => gcoef j * Ring.choose B (m + 1 - j)) (m + 1)]
  have hbdry1 : m + 1 - (m + 1) = 0 := by omega
  rw [hbdry1, Ring.choose_zero_right, Ring.choose_zero_right]
  -- pointwise Pascal on the range (m+1) part
  have hkey : (∑ j ∈ range (m + 1), gcoef j * Ring.choose (B + 1) (m + 1 - j))
      = (∑ j ∈ range (m + 1), gcoef j * Ring.choose B (m + 1 - j))
        + (∑ j ∈ range (m + 1), gcoef j * Ring.choose B (m - j)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hmj : m + 1 - j = (m - j) + 1 := by omega
    rw [hmj, Ring.choose_succ_succ]
    ring
  rw [hkey]; ring

/-- (GG) key binomial telescoping identity. -/
lemma GG (A : ℤ) (n : ℕ) :
    P A (n + 1) + P (A + 1) n = Ring.choose (A + 1) (n + 1) - Ring.choose (A + 1) n := by
  cases n with
  | zero =>
    -- P A 1 + P (A+1) 0
    rw [P_def, P_def]
    have g0 : gcoef 0 = 1 := rfl
    have g1 : gcoef 1 = -1 := rfl
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.sub_self, Nat.sub_zero,
      zero_add, g0, g1, Ring.choose_zero_right, Ring.choose_one_right]
    ring
  | succ t =>
    have hpp := PP A t  -- P (A+1)(t+1) = P A (t+1) + P A t
    have hcol := collapse A t  -- P A t + P A (t+1) + P A (t+2) = choose A (t+2) - choose A t
    -- Pascal to relate choose (A+1) to choose A
    have hp1 : Ring.choose (A + 1) (t + 2) = Ring.choose A (t + 1) + Ring.choose A (t + 2) := by
      have := Ring.choose_succ_succ A (t + 1); simpa using this
    have hp2 : Ring.choose (A + 1) (t + 1) = Ring.choose A t + Ring.choose A (t + 1) :=
      Ring.choose_succ_succ A t
    -- assemble
    rw [hpp, hp1, hp2]
    -- goal: P A (t+2) + (P A (t+1) + P A t) = ...
    linear_combination hcol

/-- (SI) step identity for the telescoping. -/
lemma SI (A : ℤ) (n : ℕ) :
    P (A + 2) (n + 1) - P A n = Ring.choose (A + 1) (n + 1) - Ring.choose (A + 1) n := by
  have hAA : A + 1 + 1 = A + 2 := by ring
  have e1 : P (A + 2) (n + 1) = P (A + 1) (n + 1) + P (A + 1) n := by
    have h := PP (A + 1) n
    rw [hAA] at h
    exact h
  have e2 : P (A + 1) (n + 1) = P A (n + 1) + P A n := PP A n
  rw [e1, e2]
  linear_combination GG A n

/-- Nonvanishing of the denominator when `m ≠ -1`. -/
lemma denom_ne (m : ℤ) (hm : m ≠ -1) (n k : ℕ) (hn : 1 ≤ n) (hk1 : 1 ≤ k) (hk2 : k ≤ n) :
    m * (n:ℤ) + (k:ℤ) ≠ 0 := by
  intro h
  have hn' : (1:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
  have hk1' : (1:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk1
  have hk2' : (k:ℤ) ≤ (n:ℤ) := by exact_mod_cast hk2
  rcases (by omega : m ≤ -2 ∨ 0 ≤ m) with hm' | hm'
  · have hprod : 0 ≤ (-(m + 2)) * (n:ℤ) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hprod]
  · have hprod : 0 ≤ m * (n:ℤ) := mul_nonneg hm' (by linarith)
    nlinarith [hprod]

/-- (telescoping) the running sum of Fuss–Catalan coefficients equals `P`. -/
lemma telescope (r : ℤ) (n : ℕ)
    (hpos : ∀ k, 1 ≤ k → k ≤ n → r + (k:ℤ) ≠ 0) :
    ∑ k ∈ range (n + 1), generalized_catalan_coefficient r k = P (r + 2 * (n:ℤ)) n := by
  induction n with
  | zero =>
    rw [P_def, show (0:ℕ) + 1 = 1 from rfl, Finset.sum_range_one, Finset.sum_range_one,
      generalized_catalan_coefficient, if_pos rfl]
    norm_num [gcoef, Ring.choose_zero_right]
  | succ t ih =>
    rw [Finset.sum_range_succ]
    rw [ih (fun k hk1 hk2 => hpos k hk1 (by omega))]
    -- gcc r (t+1) via L1
    have hne : r + ((t + 1 : ℕ):ℤ) ≠ 0 := by
      have := hpos (t + 1) (by omega) (le_refl _)
      simpa using this
    have hL1 := L1 r (t + 1) (by omega) hne
    have hsub : (t + 1) - 1 = t := by omega
    rw [hsub] at hL1
    have hNc : r + 2 * ((t + 1 : ℕ):ℤ) - 1 = (r + 2 * (t:ℤ)) + 1 := by push_cast; ring
    rw [hNc] at hL1
    rw [hL1]
    -- now use SI with A = r + 2 t
    have hSI := SI (r + 2 * (t:ℤ)) t
    have hA2 : (r + 2 * (t:ℤ)) + 2 = r + 2 * ((t + 1 : ℕ):ℤ) := by push_cast; ring
    rw [hA2] at hSI
    -- goal: P (r+2 t) t + (choose ((r+2t)+1)(t+1) - choose ((r+2t)+1) t)
    --       = P (r + 2 (t+1)) (t+1)
    linear_combination -hSI

theorem closed_form (m : ℤ) (hm : m ≠ -1) (n : ℕ) :
    a_gen m n = ∑ j ∈ range (n + 1), gcoef j * Ring.choose ((m + 2) * (n:ℤ)) (n - j) := by
  have hlhs : a_gen m n = ∑ k ∈ range (n + 1), generalized_catalan_coefficient (m * (n:ℤ)) k := by
    rw [a_gen]
    split_ifs with hn
    · subst hn
      rw [Finset.sum_range_one]
      simp [generalized_catalan_coefficient]
    · rfl
  rw [hlhs]
  have htel := telescope (m * (n:ℤ)) n
    (fun k hk1 hk2 => denom_ne m hm n k (le_trans hk1 hk2) hk1 hk2)
  rw [htel]
  have hval : m * (n:ℤ) + 2 * (n:ℤ) = (m + 2) * (n:ℤ) := by ring
  rw [hval, P_def]

end P1

section Gk
open Finset

/-- If `x ≡ v (mod m)` (as integers) with `v < m`, then `x % m = v` for naturals. -/
lemma resmod (x m v : ℕ) (hv : v < m) (h : (x:ℤ) ≡ (v:ℤ) [ZMOD (m:ℤ)]) :
    x % m = v := by
  have h2 : x ≡ v [MOD m] := (Int.natCast_modEq_iff).mp h
  have := h2  -- x % m = v % m
  rw [Nat.ModEq] at this
  rw [this, Nat.mod_eq_of_lt hv]

/-- Core counting bound via Legendre + Kummer. -/
lemma count_bound {p : ℕ} [hp : Fact p.Prime] {E k N a : ℕ} (hkN : k ≤ N)
    (H : ∀ i, 1 ≤ i → i ≤ E → p ^ i ≤ a - 1 ∨ p ^ i ≤ k % p ^ i + (N - k) % p ^ i) :
    E ≤ padicValNat p (Nat.choose N k) + padicValNat p ((a - 1).factorial) := by
  set B := N + a + E + 2 with hB
  have hlogN : Nat.log p N < B := lt_of_le_of_lt (Nat.log_le_self p N) (by omega)
  have hloga : Nat.log p (a - 1) < B := lt_of_le_of_lt (Nat.log_le_self p (a - 1)) (by omega)
  have pvc := padicValNat_choose (p := p) hkN hlogN
  have pvf := padicValNat_factorial (p := p) (n := a - 1) hloga
  rw [pvc, pvf]
  -- rewrite the card as a sum of booleans
  rw [Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  -- E = card (Ico 1 (E+1)) = sum of ones
  have hEcard : E = ∑ _i ∈ Finset.Ico 1 (E + 1), 1 := by
    rw [Finset.sum_const, Nat.card_Ico]; simp
  rw [hEcard]
  -- Ico 1 (E+1) ⊆ Ico 1 B
  have hsub : Finset.Ico 1 (E + 1) ⊆ Finset.Ico 1 B := by
    apply Finset.Ico_subset_Ico (le_refl 1); omega
  calc ∑ _i ∈ Finset.Ico 1 (E + 1), 1
      ≤ ∑ i ∈ Finset.Ico 1 (E + 1),
          ((if p ^ i ≤ k % p ^ i + (N - k) % p ^ i then 1 else 0) + (a - 1) / p ^ i) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_Ico] at hi
        rcases H i hi.1 (by omega) with hleft | hcarry
        · have hppos : 0 < p ^ i := pow_pos hp.out.pos i
          have hd : 1 ≤ (a - 1) / p ^ i := Nat.div_pos hleft hppos
          exact le_trans hd (Nat.le_add_left _ _)
        · rw [if_pos hcarry]; exact Nat.le_add_right 1 _
    _ ≤ ∑ i ∈ Finset.Ico 1 B,
          ((if p ^ i ≤ k % p ^ i + (N - k) % p ^ i then 1 else 0) + (a - 1) / p ^ i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro i _ _; exact Nat.zero_le _

/-- The main divisibility, reduced to naturals. -/
lemma keydvd_nat {p : ℕ} [hp : Fact p.Prime] {E M a b N : ℕ}
    (hpEM : p ^ E ∣ M) (hb : 0 < b) (hab : b < a) (hbM : b < M) (hkN : M - b ≤ N)
    (hres : ∀ i, 1 ≤ i → i ≤ E → a ≤ p ^ i → b ≤ (N - (M - b)) % p ^ i) :
    p ^ E ∣ (a - 1).factorial * Nat.choose N (M - b) := by
  have hchoose_pos : 0 < Nat.choose N (M - b) := Nat.choose_pos hkN
  have hprodpos : 0 < (a - 1).factorial * Nat.choose N (M - b) :=
    Nat.mul_pos (Nat.factorial_pos _) hchoose_pos
  rw [padicValNat_dvd_iff_le hprodpos.ne']
  rw [padicValNat.mul (Nat.factorial_pos _).ne' hchoose_pos.ne', Nat.add_comm]
  apply count_bound hkN
  intro i hi1 hiE
  by_cases hlt : p ^ i ≤ a - 1
  · exact Or.inl hlt
  · right
    push_neg at hlt
    have hai : a ≤ p ^ i := by omega
    have hbm : b < p ^ i := by omega
    have hmM : p ^ i ∣ M := (pow_dvd_pow p hiE).trans hpEM
    have hkval : ((M - b : ℕ) : ℤ) = (M : ℤ) - (b : ℤ) := by
      rw [Nat.cast_sub (le_of_lt hbM)]
    have hkm : (M - b) % p ^ i = p ^ i - b := by
      apply resmod
      · omega
      · rw [Int.modEq_iff_dvd]
        rw [Nat.cast_sub (le_of_lt hbm), hkval]
        have : ((p : ℤ) ^ i - (b : ℤ)) - ((M : ℤ) - (b : ℤ)) = (p : ℤ) ^ i - (M : ℤ) := by
          push_cast; ring
        rw [show ((p ^ i : ℕ) : ℤ) = (p : ℤ) ^ i by push_cast; ring, this]
        exact dvd_sub (dvd_refl _) (by exact_mod_cast hmM)
    have hres_i := hres i hi1 hiE hai
    omega

/-- Integer version of the reduced divisibility. -/
lemma core_int {p : ℕ} [hp : Fact p.Prime] {E M a b N : ℕ}
    (hpEM : p ^ E ∣ M) (hb : 0 < b) (hab : b < a) (hbM : b < M) (hkN : M - b ≤ N)
    (hres : ∀ i, 1 ≤ i → i ≤ E → a ≤ p ^ i → b ≤ (N - (M - b)) % p ^ i) :
    (p : ℤ) ^ E ∣ ((a - 1).factorial : ℤ) * (Nat.choose N (M - b) : ℤ) := by
  have hnat := keydvd_nat hpEM hb hab hbM hkN hres
  have : ((p ^ E : ℕ) : ℤ) ∣ (((a - 1).factorial * Nat.choose N (M - b) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hnat
  rw [Nat.cast_mul] at this
  rwa [show ((p ^ E : ℕ) : ℤ) = (p : ℤ) ^ E by push_cast; ring] at this

/-- Residue bound in the direct case (top `= A·M − a ≥ 0`). -/
lemma res_pos {p : ℕ} [hp : Fact p.Prime] {E M a b N : ℕ} (A : ℤ)
    (hpEM : p ^ E ∣ M) (hb : 0 < b) (hab : b < a) (hbM : b < M) (hkN : M - b ≤ N)
    (hNval : (N : ℤ) = A * (M : ℤ) - (a : ℤ)) :
    ∀ i, 1 ≤ i → i ≤ E → a ≤ p ^ i → b ≤ (N - (M - b)) % p ^ i := by
  intro i hi1 hiE hai
  have hmM : p ^ i ∣ M := (pow_dvd_pow p hiE).trans hpEM
  have hbm : b < p ^ i := by omega
  have habm : a - b < p ^ i := by omega
  have hres : (N - (M - b)) % p ^ i = p ^ i - (a - b) := by
    apply resmod
    · omega
    · rw [Int.modEq_iff_dvd]
      have hdvd : ((p : ℤ) ^ i) ∣ (M : ℤ) := by exact_mod_cast hmM
      have e : ((p ^ i - (a - b) : ℕ) : ℤ) - ((N - (M - b) : ℕ) : ℤ)
          = (p : ℤ) ^ i - (A - 1) * (M : ℤ) := by
        rw [Nat.cast_sub (le_of_lt habm), Nat.cast_sub hkN, Nat.cast_sub (le_of_lt hbM),
          Nat.cast_sub (le_of_lt hab), hNval,
          show ((p ^ i : ℕ) : ℤ) = (p : ℤ) ^ i by push_cast; ring]
        ring
      rw [e, show ((p ^ i : ℕ) : ℤ) = (p : ℤ) ^ i by push_cast; ring]
      exact dvd_sub (dvd_refl _) (Dvd.dvd.mul_left hdvd (A - 1))
  omega

/-- Residue bound in the reflected case (top `= A·M − a < 0`). -/
lemma res_neg {p : ℕ} [hp : Fact p.Prime] {E M a b N : ℕ} (A : ℤ)
    (hpEM : p ^ E ∣ M) (hb : 0 < b) (hab : b < a) (hbM : b < M) (hkN : M - b ≤ N)
    (hNval : (N : ℤ) = (a : ℤ) - A * (M : ℤ) + (M : ℤ) - (b : ℤ) - 1) :
    ∀ i, 1 ≤ i → i ≤ E → a ≤ p ^ i → b ≤ (N - (M - b)) % p ^ i := by
  intro i hi1 hiE hai
  have hmM : p ^ i ∣ M := (pow_dvd_pow p hiE).trans hpEM
  have ha1 : a - 1 < p ^ i := by omega
  have hres : (N - (M - b)) % p ^ i = a - 1 := by
    apply resmod
    · omega
    · rw [Int.modEq_iff_dvd]
      have hdvd : ((p : ℤ) ^ i) ∣ (M : ℤ) := by exact_mod_cast hmM
      have e : ((a - 1 : ℕ) : ℤ) - ((N - (M - b) : ℕ) : ℤ) = A * (M : ℤ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_sub hkN, Nat.cast_sub (le_of_lt hbM),
          hNval]
        push_cast; ring
      rw [e, show ((p ^ i : ℕ) : ℤ) = (p : ℤ) ^ i by push_cast; ring]
      exact Dvd.dvd.mul_left hdvd A
  omega

/-- **Generalized Kummer bound.** -/
theorem GK (p : ℕ) (hp : p.Prime) (A : ℤ) (M : ℕ) (a b : ℕ) (hab : b < a) (hb : 0 < b) :
    (p:ℤ) ^ (padicValNat p M) ∣ ((a-1).factorial : ℤ) * Ring.choose (A * (M:ℤ) - a) (M - b) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set E := padicValNat p M with hE
  by_cases hE0 : E = 0
  · rw [hE0, pow_zero]; exact one_dvd _
  · have hM : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h | h
      · exfalso; apply hE0; rw [hE, h, padicValNat.zero]
      · exact h
    have hpEM : p ^ E ∣ M := by rw [hE]; exact pow_padicValNat_dvd
    by_cases hbM : b < M
    · by_cases hkN0 : (0 : ℤ) ≤ A * (M:ℤ) - (a:ℤ)
      · -- top ≥ 0
        set N := (A * (M:ℤ) - (a:ℤ)).toNat with hNdef
        have hNval : (N : ℤ) = A * (M:ℤ) - (a:ℤ) := Int.toNat_of_nonneg hkN0
        have hch : Ring.choose (A * (M:ℤ) - (a:ℤ)) (M - b) = (Nat.choose N (M - b) : ℤ) := by
          rw [← hNval, Ring.choose_natCast]
        rw [hch]
        by_cases hkN : M - b ≤ N
        · exact core_int hpEM hb hab hbM hkN (res_pos A hpEM hb hab hbM hkN hNval)
        · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]; exact dvd_zero _
      · -- top < 0
        push_neg at hkN0
        set N := ((a:ℤ) - A * (M:ℤ) + (M:ℤ) - (b:ℤ) - 1).toNat with hNdef
        have hbMz : (b:ℤ) < (M:ℤ) := by exact_mod_cast hbM
        have hpos : (0:ℤ) ≤ (a:ℤ) - A * (M:ℤ) + (M:ℤ) - (b:ℤ) - 1 := by linarith
        have hNval : (N : ℤ) = (a:ℤ) - A * (M:ℤ) + (M:ℤ) - (b:ℤ) - 1 :=
          Int.toNat_of_nonneg hpos
        have hch : Ring.choose (A * (M:ℤ) - (a:ℤ)) (M - b)
            = (Int.negOnePow ((M - b : ℕ) : ℤ) : ℤ) * (Nat.choose N (M - b) : ℤ) := by
          have h1 : A * (M:ℤ) - (a:ℤ) = -((a:ℤ) - A * (M:ℤ)) := by ring
          rw [h1, Ring.choose_neg]
          have h2 : (a:ℤ) - A * (M:ℤ) + ((M - b : ℕ):ℤ) - 1 = (N:ℤ) := by
            rw [hNval, Nat.cast_sub (le_of_lt hbM)]; ring
          rw [h2, Ring.choose_natCast, Units.smul_def, smul_eq_mul]
        rw [hch]
        by_cases hkN : M - b ≤ N
        · have hcore := core_int hpEM hb hab hbM hkN (res_neg A hpEM hb hab hbM hkN hNval)
          have hmul := hcore.mul_left (Int.negOnePow ((M - b : ℕ) : ℤ) : ℤ)
          rw [show ((a-1).factorial : ℤ) * ((Int.negOnePow ((M - b : ℕ) : ℤ):ℤ) * (Nat.choose N (M-b):ℤ))
              = (Int.negOnePow ((M - b : ℕ) : ℤ):ℤ) * (((a-1).factorial:ℤ) * (Nat.choose N (M-b):ℤ)) by ring]
          exact hmul
        · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero]
          exact dvd_zero _
    · -- b ≥ M, so M - b = 0
      have hk0 : M - b = 0 := by omega
      rw [hk0, Ring.choose_zero_right, mul_one]
      have hMfac : M ∣ (a-1).factorial := Nat.dvd_factorial hM (by omega)
      have hfin : p ^ E ∣ (a-1).factorial := hpEM.trans hMfac
      exact_mod_cast hfin

end Gk

section Lemmaa
open PowerSeries Finset

/-!
# Lemma A' (clean divisibility form)

We prove:
`(p:ℤ)^(2·v_p(M)) ∣ (p:ℤ)^(2·v_p((2μ)!)) · ℓ (ψ p j) (A·M) M`,
where `μ = (j-1)/2`.

Following `/tmp/proof.md`, this reduces (via the regime split) to the
dominant-regime bound (Prop 5): when `2μ < p^E` (E = v_p(M)),
`v_p(ℓ) ≥ 2E - 2 v_p((2μ)!)`, i.e. the same divisibility.
-/

/-- Arithmetic lemma: if `p^E ≤ n` then `E ≤ v_p(n!)` (Legendre). -/
lemma pow_le_imp_valNat_le (p : ℕ) (hp : p.Prime) (E n : ℕ) (hn : 0 < n)
    (h : p ^ E ≤ n) : E ≤ padicValNat p n.factorial := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  -- E ≤ log p n
  have hElog : E ≤ Nat.log p n := (Nat.le_log_iff_pow_le hp1 (by omega)).mpr h
  -- Legendre with bound b = log p n + 1
  have hb : Nat.log p n < Nat.log p n + 1 := by omega
  rw [padicValNat_factorial hb]
  -- E ≤ ∑_{i ∈ Ico 1 (E+1)} n/p^i ≤ ∑_{i ∈ Ico 1 (log+1)} n/p^i
  have hsub : Finset.Ico 1 (E + 1) ⊆ Finset.Ico 1 (Nat.log p n + 1) := by
    apply Finset.Ico_subset_Ico (le_refl 1)
    omega
  have hlow : E ≤ ∑ i ∈ Finset.Ico 1 (E + 1), n / p ^ i := by
    have hcard : (Finset.Ico 1 (E + 1)).card = E := by
      rw [Nat.card_Ico]; omega
    calc E = ∑ _i ∈ Finset.Ico 1 (E + 1), 1 := by rw [Finset.sum_const, hcard]; ring
      _ ≤ ∑ i ∈ Finset.Ico 1 (E + 1), n / p ^ i := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_Ico] at hi
          have hpi : p ^ i ≤ n := le_trans (Nat.pow_le_pow_right (by omega) (by omega)) h
          exact Nat.one_le_div_iff (by positivity) |>.mpr hpi
  have hmono : ∑ i ∈ Finset.Ico 1 (E + 1), n / p ^ i
      ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p n + 1), n / p ^ i :=
    Finset.sum_le_sum_of_subset hsub
  omega

/- ## Verified building block: the descent identity (Prop 1 core)

The pure `Ring.choose` identity underlying the descent step (§1 of proof.md):
`s·(C(s-1,k) - C(s-1,k+1)) = (2(k+1) - s)·C(s,k+1)`. -/

/-- Absorption identity for `Ring.choose` (as in `p1.lean`). -/
lemma ABS' (N : ℤ) (k : ℕ) :
    ((k + 1 : ℕ) : ℤ) * Ring.choose N (k + 1) = (N - (k:ℤ)) * Ring.choose N k := by
  have hk : ((k.factorial : ℤ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  apply mul_left_cancel₀ hk
  have e1 : (k.factorial : ℤ) * (((k + 1 : ℕ) : ℤ) * Ring.choose N (k + 1))
      = ∏ i ∈ range (k + 1), (N - (i:ℤ)) := by
    have hpk : (∏ i ∈ range (k+1), (N - (i:ℤ)))
        = ((k+1).factorial : ℤ) * Ring.choose N (k+1) := by
      have h := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) N (k+1)
      rw [nsmul_eq_mul] at h
      rw [← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range] at h
      exact h
    rw [hpk]
    have : ((k + 1).factorial : ℤ) = ((k + 1 : ℕ) : ℤ) * (k.factorial : ℤ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [this]; ring
  have e2 : (k.factorial : ℤ) * ((N - (k:ℤ)) * Ring.choose N k)
      = ∏ i ∈ range (k + 1), (N - (i:ℤ)) := by
    have hpk : (∏ i ∈ range k, (N - (i:ℤ))) = (k.factorial : ℤ) * Ring.choose N k := by
      have h := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) N k
      rw [nsmul_eq_mul] at h
      rw [← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range] at h
      exact h
    rw [Finset.prod_range_succ, hpk]; ring
  rw [e1, e2]

/-- **Prop 1 (descent identity core).** Pure generalized-binomial identity. -/
lemma descKey (s : ℤ) (k : ℕ) :
    s * (Ring.choose (s - 1) k - Ring.choose (s - 1) (k + 1))
      = (2 * ((k : ℤ) + 1) - s) * Ring.choose s (k + 1) := by
  have P1 : Ring.choose s (k + 1) = Ring.choose (s - 1) k + Ring.choose (s - 1) (k + 1) := by
    have h := Ring.choose_succ_succ (s - 1) k
    rw [sub_add_cancel] at h
    exact h
  have A2 := ABS' (s - 1) k
  push_cast at A2
  rw [P1]
  linear_combination (-2 : ℤ) * A2

/- ## Verified building block: the finite closed form (§0 of proof.md)

`ψ p j = (1+X)^{-j} · Wⱼ`, where `Wⱼ = Cart p (qser p ^ j * Gser)`.  Consequently
`ℓ` has the finite closed form below.  Note: the sum is naturally finite (`k ≤ M`),
so no polynomial/finite-support argument for `Wⱼ` is needed here. -/

lemma infl_pow (p : ℕ) (hp0 : 0 < p) (a : PowerSeries ℤ) (j : ℕ) :
    (infl p a) ^ j = infl p (a ^ j) := by
  induction j with
  | zero => simp [infl_one p hp0]
  | succ n ih => rw [pow_succ, ih, infl_mul p hp0, pow_succ]

lemma binNeg1 : binomialSeries ℤ (-1 : ℤ) = Xinv := by
  have h1 : binomialSeries ℤ (1 : ℤ) = 1 + PowerSeries.X := by
    have := binomialSeries_nat (A := ℤ) (R := ℤ) 1
    simpa using this
  have hmul : ((1 : PowerSeries ℤ) + PowerSeries.X) * binomialSeries ℤ (-1 : ℤ) = 1 := by
    rw [← h1, ← binomialSeries_add]; norm_num
  have hne : ((1 : PowerSeries ℤ) + PowerSeries.X) ≠ 0 := by
    intro h; have := congrArg (PowerSeries.coeff 0) h; simp at this
  apply mul_left_cancel₀ hne
  rw [hmul, oneAddX_mul_Xinv]

lemma binomialSeries_negNat (j : ℕ) : binomialSeries ℤ (-(j : ℤ)) = Xinv ^ j := by
  induction j with
  | zero => simp
  | succ n ih =>
    have : (-(↑(n+1) : ℤ)) = (-(n:ℤ)) + (-1) := by push_cast; ring
    rw [this, binomialSeries_add, ih, binNeg1, pow_succ]

lemma psi_eq (p j : ℕ) (hp0 : 0 < p) :
    ψ p j = Xinv ^ j * Cart p (qser p ^ j * Gser) := by
  unfold ψ rho
  rw [mul_pow, infl_pow p hp0, mul_comm (qser p ^ j) (infl p (Xinv ^ j)), mul_assoc,
      cart_infl_mul p hp0]

/-- **Closed form (§0).** `ℓ (ψ p j) (A·M) M = ∑_{k≤M} C(A·M - j, k)·(qser^j·G)_{p(M-k)}`. -/
lemma closed_form_ell (p : ℕ) (hp0 : 0 < p) (A : ℤ) (M j : ℕ) :
    ℓ (ψ p j) (A * (M : ℤ)) M
      = ∑ k ∈ range (M + 1),
          Ring.choose (A * (M : ℤ) - (j : ℤ)) k
            * PowerSeries.coeff (p * (M - k)) (qser p ^ j * Gser) := by
  unfold ℓ
  rw [psi_eq p j hp0]
  have hcomb : binomialSeries ℤ (A * (M : ℤ)) * (Xinv ^ j * Cart p (qser p ^ j * Gser))
      = binomialSeries ℤ (A * (M : ℤ) - (j : ℤ)) * Cart p (qser p ^ j * Gser) := by
    rw [← binomialSeries_negNat, ← mul_assoc, ← binomialSeries_add]; ring_nf
  rw [hcomb, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => (PowerSeries.coeff a) (binomialSeries ℤ (A * (M:ℤ) - (j:ℤ)))
          * (PowerSeries.coeff b) (Cart p (qser p ^ j * Gser))) M]
  apply Finset.sum_congr rfl
  intro k hk
  rw [binomialSeries_coeff, coeff_Cart]
  simp

/-- **Denominator exactness (§5).** If `p^E ∣ M` and `0 < t < p^E`, then subtracting `t`
from the multiple `M` does not change the `p`-adic valuation: `v_p(M - t) = v_p(t)`.
This is the exact-cancellation fact used to evaluate the descent denominators
`∏_r (M - i - r)` in the dominant regime. -/
lemma vp_sub_eq (p : ℕ) (hp : p.Prime) (E M t : ℕ) (hM : 0 < M) (hpE : p ^ E ∣ M)
    (ht0 : 0 < t) (htE : t < p ^ E) : padicValNat p (M - t) = padicValNat p t := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  set w := padicValNat p t with hwdef
  -- w < E
  have hwt : p ^ w ∣ t := pow_padicValNat_dvd
  have hwE : w < E := by
    by_contra hge
    push_neg at hge
    have : p ^ E ∣ t := dvd_trans (pow_dvd_pow p hge) hwt
    have := Nat.le_of_dvd ht0 this
    omega
  have hMle : p ^ E ≤ M := Nat.le_of_dvd (by omega) hpE
  have hMt : t ≤ M := by omega
  have hMtpos : 0 < M - t := by omega
  -- p^w ∣ (M - t)
  have hdvdM : p ^ w ∣ M := dvd_trans (pow_dvd_pow p (le_of_lt hwE)) hpE
  have h1 : p ^ w ∣ (M - t) := Nat.dvd_sub hdvdM hwt
  -- ¬ p^(w+1) ∣ (M - t)
  have h2 : ¬ p ^ (w + 1) ∣ (M - t) := by
    intro hcon
    have hdvdM' : p ^ (w + 1) ∣ M := dvd_trans (pow_dvd_pow p (by omega)) hpE
    have : p ^ (w + 1) ∣ (M - (M - t)) := Nat.dvd_sub hdvdM' hcon
    rw [Nat.sub_sub_self hMt] at this
    exact pow_succ_padicValNat_not_dvd (by omega) this
  -- conclude
  have hle : w ≤ padicValNat p (M - t) :=
    (padicValNat_dvd_iff_le (by omega)).mp h1
  have hlt : ¬ (w + 1 ≤ padicValNat p (M - t)) := by
    intro hc; exact h2 ((padicValNat_dvd_iff_le (by omega)).mpr hc)
  omega

/-- **Descent engine (§2–§3), summed form of `descKey`.**  For a coefficient
sequence `c` supported in `[0, n)` (i.e. `c i = 0` for `i ≥ n`), and any `s : ℤ`,
```
s · Σ_i c_i (C(s-1, n-i-1) - C(s-1, n-i)) = Σ_i (2(n-i) - s) c_i · C(s, n-i).
```
This is the exact discrete form of the descent identity `(★)` of `/tmp/proof.md`,
obtained by summing `descKey` term by term; the left side is `s·ℓ`, the right the
raw combination that (after the palindrome/center substitution `2(n-i)-s ↦
-(A-2)N + 2(c-i)`) becomes `-(A-2)N·P₁ + 2·(next level)`. -/
lemma descent_sum (s : ℤ) (n : ℕ) (c : ℕ → ℤ) (hsupp : ∀ i, n ≤ i → c i = 0) :
    s * (∑ i ∈ range (n + 1), c i *
          (Ring.choose (s - 1) (n - i - 1) - Ring.choose (s - 1) (n - i)))
      = ∑ i ∈ range (n + 1), (2 * ((n : ℤ) - (i : ℤ)) - s) * c i * Ring.choose s (n - i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
  · -- i < n
    have hk : n - i - 1 + 1 = n - i := by omega
    have hcast : ((n - i : ℕ) : ℤ) = (n : ℤ) - (i : ℤ) := by
      rw [Nat.cast_sub (le_of_lt hlt)]
    have hdk := descKey s (n - i - 1)
    rw [hk] at hdk
    -- hdk : s * (C(s-1, n-i-1) - C(s-1, n-i)) = (2*((n-i-1:ℕ)+1) - s) * C(s, n-i)
    have hcast2 : ((n - i - 1 : ℕ) : ℤ) + 1 = (n : ℤ) - (i : ℤ) := by
      have : ((n - i - 1 : ℕ) : ℤ) + 1 = ((n - i : ℕ) : ℤ) := by
        rw [← hk]; push_cast; ring
      rw [this, hcast]
    calc s * (c i * (Ring.choose (s - 1) (n - i - 1) - Ring.choose (s - 1) (n - i)))
        = c i * (s * (Ring.choose (s - 1) (n - i - 1) - Ring.choose (s - 1) (n - i))) := by ring
      _ = c i * ((2 * (((n - i - 1 : ℕ) : ℤ) + 1) - s) * Ring.choose s (n - i)) := by rw [hdk]
      _ = (2 * ((n : ℤ) - (i : ℤ)) - s) * c i * Ring.choose s (n - i) := by rw [hcast2]; ring
  · -- i = n : c i = 0
    subst heq
    rw [hsupp i (le_refl i)]; ring

end Lemmaa

section Structa
open PowerSeries Finset

/-- Lower support: `qser^j` has order `≥ j`. -/
lemma qpow_low (p : ℕ) : ∀ (j N : ℕ), N < j → (PowerSeries.coeff N) (qser p ^ j) = 0 := by
  intro j
  induction j with
  | zero => intro N hN; omega
  | succ k ih =>
    intro N hN
    rw [pow_succ, coeffMul]
    apply Finset.sum_eq_zero
    intro a ha
    rw [Finset.mem_range] at ha
    -- term: coeff a (qser^k) * coeff (N-a) (qser)
    -- qser coeff nonzero only for 1≤ idx ≤ p-1
    by_cases hidx : 1 ≤ N - a ∧ N - a ≤ p - 1
    · -- then N - a ≥ 1, so a ≤ N-1 < k, use ih on coeff a (qser^k)
      have : a < k := by omega
      rw [ih a this, zero_mul]
    · rw [coeff_qser, show qc p (N - a) = 0 by unfold qc; rw [if_neg hidx], mul_zero]

/-- coeff 0 of qser^j is 0 for j ≥ 1. -/
lemma qpow_coeff0 (p j : ℕ) (hj : 1 ≤ j) : (PowerSeries.coeff 0) (qser p ^ j) = 0 :=
  qpow_low p j 0 (by omega)

/-- coeff 0 of qser^j*Gser is 0 for j ≥ 1. -/
lemma qpowG_coeff0 (p j : ℕ) (hj : 1 ≤ j) : (PowerSeries.coeff 0) (qser p ^ j * Gser) = 0 := by
  rw [coeffMulG, Finset.sum_range_one, qpow_coeff0 p j hj, zero_mul]

/-- Lower support of the product: `coeff N = 0` for `N < j`. -/
lemma qpowG_low (p j N : ℕ) (hN : N < j) : (PowerSeries.coeff N) (qser p ^ j * Gser) = 0 := by
  rw [coeffMulG]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_range] at hk
  rw [qpow_low p j k (by omega), zero_mul]

/-- Upper support of the product: `coeff N = 0` for `N > j*(p-1)`, `j ≥ 1`. -/
lemma qpowG_high (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ (j : ℕ), 1 ≤ j → ∀ (N : ℕ), j * (p - 1) < N → (PowerSeries.coeff N) (qser p ^ j * Gser) = 0 := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro N hN
    rw [pow_one]
    exact qG_coeff_zero p hp hp5 N (by omega)
  | succ k hk ih =>
    intro N hN
    -- qser^(k+1) * G = qser * (qser^k * G)
    rw [pow_succ, mul_comm (qser p ^ k) (qser p), mul_assoc, coeffMul]
    apply Finset.sum_eq_zero
    intro a ha
    rw [Finset.mem_range] at ha
    by_cases hidx : 1 ≤ a ∧ a ≤ p - 1
    · -- coeff (N-a) (qser^k * G) = 0 since N-a > k*(p-1)
      have hexp : (k + 1) * (p - 1) = k * (p - 1) + (p - 1) := by ring
      have : k * (p - 1) < N - a := by omega
      rw [ih (N - a) this, mul_zero]
    · rw [coeff_qser, show qc p a = 0 by unfold qc; rw [if_neg hidx], zero_mul]

/-- Convolution with `qser` expressed as a sum over `range (p+1)`, valid when `coeff 0 H = 0`. -/
lemma qmul_coeff (p n : ℕ) (H : PowerSeries ℤ) (h0 : (PowerSeries.coeff 0) H = 0) :
    (PowerSeries.coeff n) (qser p * H)
      = ∑ a ∈ range (p + 1), qc p a * (PowerSeries.coeff (n - a)) H := by
  rw [coeffMul]
  simp only [coeff_qser]
  have e1 : ∑ a ∈ range (n + 1), qc p a * (PowerSeries.coeff (n - a)) H
          = ∑ a ∈ range (n + p + 1), qc p a * (PowerSeries.coeff (n - a)) H := by
    apply Finset.sum_subset
    · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
    · intro x hx hxns
      rw [Finset.mem_range] at hxns
      rw [show n - x = 0 by omega, h0, mul_zero]
  have e2 : ∑ a ∈ range (p + 1), qc p a * (PowerSeries.coeff (n - a)) H
          = ∑ a ∈ range (n + p + 1), qc p a * (PowerSeries.coeff (n - a)) H := by
    apply Finset.sum_subset
    · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
    · intro x hx hxns
      rw [Finset.mem_range] at hxns
      rw [show qc p x = 0 by unfold qc; rw [if_neg (by omega)], zero_mul]
  rw [e1, ← e2]

/-- Antipalindrome symmetry about `j*p/2`. -/
lemma qpowG_anti (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ (j : ℕ), 1 ≤ j → ∀ (n : ℕ),
      (PowerSeries.coeff n) (qser p ^ j * Gser)
        + (PowerSeries.coeff (j * p - n)) (qser p ^ j * Gser) = 0 := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro n
    simp only [pow_one, one_mul]
    by_cases hn : n ≤ p
    · have hD := Dzero p hp hp5 n hn
      unfold Dd Rr at hD
      linarith [hD]
    · have h1 : (PowerSeries.coeff n) (qser p * Gser) = 0 :=
        qG_coeff_zero p hp hp5 n (by omega)
      have h2 : (PowerSeries.coeff (p - n)) (qser p * Gser) = 0 := by
        rw [show p - n = 0 by omega]
        have := qpowG_coeff0 p 1 (by norm_num)
        rwa [pow_one] at this
      rw [h1, h2]; ring
  | succ k hk ih =>
    have hPP : qser p ^ (k + 1) * Gser = qser p * (qser p ^ k * Gser) := by
      rw [pow_succ']; ring
    have h0 : (PowerSeries.coeff 0) (qser p ^ k * Gser) = 0 := qpowG_coeff0 p k hk
    have hexp : (k + 1) * p = k * p + p := by ring
    have hkp : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
    have key : ∀ n, n ≤ k * p →
        (PowerSeries.coeff n) (qser p ^ (k + 1) * Gser)
          + (PowerSeries.coeff ((k + 1) * p - n)) (qser p ^ (k + 1) * Gser) = 0 := by
      intro n hn
      rw [hPP, qmul_coeff p n _ h0, qmul_coeff p ((k + 1) * p - n) _ h0]
      have hrefl := Finset.sum_range_reflect
        (fun a => qc p a * (PowerSeries.coeff ((k + 1) * p - n - a)) (qser p ^ k * Gser)) (p + 1)
      simp only [Nat.add_sub_cancel] at hrefl
      rw [← hrefl, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro a ha
      rw [Finset.mem_range] at ha
      have ha_le : a ≤ p := by omega
      rw [qc_symm p a ha_le]
      have hidx : (k + 1) * p - n - (p - a) = k * p - n + a := by omega
      rw [hidx]
      have hih := ih (k * p - n + a)
      have hidx2 : k * p - (k * p - n + a) = n - a := by omega
      rw [hidx2] at hih
      have hsum : (PowerSeries.coeff (n - a)) (qser p ^ k * Gser)
          + (PowerSeries.coeff (k * p - n + a)) (qser p ^ k * Gser) = 0 := by linarith [hih]
      rw [← mul_add, hsum, mul_zero]
    intro n
    by_cases hn : n ≤ k * p
    · exact key n hn
    · by_cases hnM : n ≤ (k + 1) * p
      · have h' := key ((k + 1) * p - n) (by omega)
        rw [show (k + 1) * p - ((k + 1) * p - n) = n by omega] at h'
        linarith [h']
      · have hz1 : (PowerSeries.coeff n) (qser p ^ (k + 1) * Gser) = 0 := by
          apply qpowG_high p hp hp5 (k + 1) (by omega) n
          have he2 : (k + 1) * (p - 1) + (k + 1) = (k + 1) * p := by
            rw [← Nat.mul_succ]; congr 1; omega
          omega
        have hz2 : (PowerSeries.coeff ((k + 1) * p - n)) (qser p ^ (k + 1) * Gser) = 0 := by
          rw [show (k + 1) * p - n = 0 by omega]
          exact qpowG_coeff0 p (k + 1) (by omega)
        rw [hz1, hz2]; ring

/-- Cartier coefficient sequence `W`. -/
noncomputable def Wc (p j k : ℕ) : ℤ := (PowerSeries.coeff (p * k)) (qser p ^ j * Gser)

lemma Wc_anti (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (j : ℕ) (hj : 1 ≤ j) (k : ℕ) :
    Wc p j k + Wc p j (j - k) = 0 := by
  unfold Wc
  have h := qpowG_anti p hp hp5 j hj (p * k)
  have he : j * p - p * k = p * (j - k) := by rw [Nat.mul_sub, mul_comm p j]
  rwa [he] at h

lemma Wc_high (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (j : ℕ) (hj : 1 ≤ j) (k : ℕ) (hk : j ≤ k) :
    Wc p j k = 0 := by
  unfold Wc
  apply qpowG_high p hp hp5 j hj
  have h1 : j * (p - 1) = j * p - j := by rw [Nat.mul_sub, Nat.mul_one]
  have h2 : j * p ≤ p * k := by rw [mul_comm]; exact Nat.mul_le_mul_left p hk
  have h5 : 0 < j * p := Nat.mul_pos (by omega) (by omega)
  rw [h1]; omega

lemma Wc_zero (p j : ℕ) (hj : 1 ≤ j) : Wc p j 0 = 0 := by
  unfold Wc; rw [Nat.mul_zero]; exact qpowG_coeff0 p j hj

lemma Wc_total (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (j : ℕ) (hj : 1 ≤ j) :
    ∑ k ∈ range (j + 1), Wc p j k = 0 := by
  have hrefl := Finset.sum_range_reflect (fun k => Wc p j k) (j + 1)
  simp only [Nat.add_sub_cancel] at hrefl
  have hneg : ∑ k ∈ range (j + 1), Wc p j (j - k) = - ∑ k ∈ range (j + 1), Wc p j k := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have := Wc_anti p hp hp5 j hj k
    linarith [this]
  rw [hneg] at hrefl
  linarith [hrefl]

/-- Prefix-sum reflection: the key to palindromy of the partial sums. -/
lemma Sc_pref (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (j : ℕ) (hj : 1 ≤ j) (i : ℕ) (hi : i < j) :
    ∑ k ∈ range (i + 1), Wc p j k = ∑ k ∈ range (j - i), Wc p j k := by
  have hC : ∑ m ∈ Finset.Ico (i + 1) (j + 1), Wc p j m
          = ∑ k ∈ range (j - i), Wc p j (i + 1 + k) := by
    rw [Finset.sum_Ico_eq_sum_range, show (j + 1) - (i + 1) = j - i from by omega]
  have hD : (∑ k ∈ range (i + 1), Wc p j k)
              + (∑ m ∈ Finset.Ico (i + 1) (j + 1), Wc p j m) = 0 := by
    rw [Finset.sum_range_add_sum_Ico (fun k => Wc p j k) (show i + 1 ≤ j + 1 from by omega)]
    exact Wc_total p hp hp5 j hj
  have hB : ∑ k ∈ range (j - i), Wc p j (j - i - 1 - k)
          = - ∑ k ∈ range (j - i), Wc p j (i + 1 + k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hidx : j - (j - i - 1 - k) = i + 1 + k := by omega
    have hh := Wc_anti p hp hp5 j hj (j - i - 1 - k)
    rw [hidx] at hh
    linarith [hh]
  have hA := Finset.sum_range_reflect (fun k => Wc p j k) (j - i)
  calc ∑ k ∈ range (i + 1), Wc p j k
      = - ∑ m ∈ Finset.Ico (i + 1) (j + 1), Wc p j m := by linarith [hD]
    _ = - ∑ k ∈ range (j - i), Wc p j (i + 1 + k) := by rw [hC]
    _ = ∑ k ∈ range (j - i), Wc p j (j - i - 1 - k) := hB.symm
    _ = ∑ k ∈ range (j - i), Wc p j k := hA

/-- The palindromic sequence `S` = negative partial sums of `W`. -/
noncomputable def Sc (p j i : ℕ) : ℤ := - ∑ k ∈ range (i + 1), Wc p j k

theorem structA (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (j : ℕ) (hj : 3 ≤ j) :
    ∃ S : ℕ → ℤ,
      (∀ i, S i = S (j - 1 - i)) ∧
      (∀ i, j - 1 < i → S i = 0) ∧
      (∀ i, i < 1 + (j - 1) / p → S i = 0) ∧
      (∀ i, (PowerSeries.coeff (p * i)) (qser p ^ j * Gser)
              = (if i = 0 then - S 0 else S (i - 1) - S i)) := by
  have hj1 : 1 ≤ j := by omega
  refine ⟨Sc p j, ?_, ?_, ?_, ?_⟩
  · -- palindromy
    intro i
    by_cases hi : i < j
    · show - ∑ k ∈ range (i + 1), Wc p j k = - ∑ k ∈ range ((j - 1 - i) + 1), Wc p j k
      rw [show (j - 1 - i) + 1 = j - i from by omega, Sc_pref p hp hp5 j hj1 i hi]
    · -- i ≥ j: both zero
      have hup1 : Sc p j i = 0 := by
        show - ∑ k ∈ range (i + 1), Wc p j k = 0
        have heq : ∑ k ∈ range (i + 1), Wc p j k = ∑ k ∈ range (j + 1), Wc p j k := by
          symm; apply Finset.sum_subset
          · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
          · intro x hx hxns; rw [Finset.mem_range] at hx hxns
            exact Wc_high p hp hp5 j hj1 x (by omega)
        rw [heq, Wc_total p hp hp5 j hj1]; ring
      have hup2 : Sc p j (j - 1 - i) = 0 := by
        rw [show j - 1 - i = 0 from by omega]
        show - ∑ k ∈ range (0 + 1), Wc p j k = 0
        rw [Finset.sum_range_one, Wc_zero p j hj1]; ring
      rw [hup1, hup2]
  · -- support upper
    intro i hi
    show - ∑ k ∈ range (i + 1), Wc p j k = 0
    have heq : ∑ k ∈ range (i + 1), Wc p j k = ∑ k ∈ range (j + 1), Wc p j k := by
      symm; apply Finset.sum_subset
      · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
      · intro x hx hxns; rw [Finset.mem_range] at hx hxns
        exact Wc_high p hp hp5 j hj1 x (by omega)
    rw [heq, Wc_total p hp hp5 j hj1]; ring
  · -- support lower
    intro i hi
    show - ∑ k ∈ range (i + 1), Wc p j k = 0
    have hz : ∀ k ∈ range (i + 1), Wc p j k = 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      unfold Wc
      apply qpowG_low
      -- p * k < j
      have hdiv : p * ((j - 1) / p) ≤ j - 1 := Nat.mul_div_le (j - 1) p
      have : k ≤ (j - 1) / p := by omega
      have : p * k ≤ p * ((j - 1) / p) := Nat.mul_le_mul_left p this
      omega
    rw [Finset.sum_eq_zero hz]; ring
  · -- W = (X-1)·S relation
    intro i
    show (PowerSeries.coeff (p * i)) (qser p ^ j * Gser) = _
    have hW : (PowerSeries.coeff (p * i)) (qser p ^ j * Gser) = Wc p j i := rfl
    rw [hW]
    by_cases hi0 : i = 0
    · subst hi0
      rw [if_pos rfl]
      show Wc p j 0 = - Sc p j 0
      unfold Sc
      rw [Finset.sum_range_one]; ring
    · rw [if_neg hi0]
      show Wc p j i = Sc p j (i - 1) - Sc p j i
      unfold Sc
      rw [show i - 1 + 1 = i from by omega, Finset.sum_range_succ]
      ring

end Structa

section Dominant
open PowerSeries Finset

/-- p-adic cancellation: if `p^v ∣ X` exactly and `p^(v+k) ∣ X*Y`, then `p^k ∣ Y`. -/
lemma pcancel (p : ℕ) (hp : p.Prime) (v k : ℕ) (X Y : ℤ)
    (hdvd : (p:ℤ)^v ∣ X) (hnd : ¬ ((p:ℤ)^(v+1) ∣ X)) (hXY : (p:ℤ)^(v+k) ∣ X*Y) :
    (p:ℤ)^k ∣ Y := by
  have hpint : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨X', hX'⟩ := hdvd
  have hnpX' : ¬ ((p:ℤ) ∣ X') := by
    intro h
    obtain ⟨t, ht⟩ := h
    apply hnd
    exact ⟨t, by rw [hX', ht, pow_succ]; ring⟩
  have hpv0 : ((p:ℤ)^v) ≠ 0 := pow_ne_zero v (by exact_mod_cast hp.ne_zero)
  rw [hX', mul_assoc, pow_add, mul_dvd_mul_iff_left hpv0] at hXY
  exact hpint.pow_dvd_of_dvd_mul_left k hnpX' hXY

/-- Abel/summation-by-parts identity for finite sums, with vanishing boundary. -/
lemma abel_id (N : ℕ) (g c : ℕ → ℤ) (hg0 : g 0 = 0) (hgN : g N = 0) :
    ∑ i ∈ Finset.range (N+1), (g (i-1) - g i) * c i
      = ∑ i ∈ Finset.range (N+1), g i * (c (i+1) - c i) := by
  have key : (∑ i ∈ Finset.range (N+1), (g (i-1) - g i) * c i)
           - (∑ i ∈ Finset.range (N+1), g i * (c (i+1) - c i))
           = g 0 * c 0 - g N * c (N+1) := by
    have e1 : ∑ i ∈ Finset.range (N+1), (g (i-1) - g i) * c i
            = (∑ i ∈ Finset.range (N+1), g (i-1) * c i)
                - ∑ i ∈ Finset.range (N+1), g i * c i := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    have e2 : ∑ i ∈ Finset.range (N+1), g i * (c (i+1) - c i)
            = (∑ i ∈ Finset.range (N+1), g i * c (i+1))
                - ∑ i ∈ Finset.range (N+1), g i * c i := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    have e3 : ∑ i ∈ Finset.range (N+1), g (i-1) * c i
            = g 0 * c 0 + ∑ i ∈ Finset.range N, g i * c (i+1) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.add_sub_cancel, Nat.zero_sub]
      ring
    have e4 : ∑ i ∈ Finset.range (N+1), g i * c (i+1)
            = (∑ i ∈ Finset.range N, g i * c (i+1)) + g N * c (N+1) := by
      rw [Finset.sum_range_succ]
    rw [e1, e2, e3, e4]; ring
  have : (∑ i ∈ Finset.range (N+1), (g (i-1) - g i) * c i)
           - (∑ i ∈ Finset.range (N+1), g i * (c (i+1) - c i)) = 0 := by
    rw [key, hg0, hgN]; ring
  linarith

/-- Prefix reflection identity for an antipalindromic sequence with zero total sum. -/
lemma prefix_reflect (W : ℕ → ℤ) (w : ℕ) (hanti : ∀ k, W (w - k) = - W k)
    (i : ℕ) (hi : i < w) :
    ∑ k ∈ Finset.range (i+1), W k = ∑ k ∈ Finset.range (w-i), W k := by
  have htot : ∑ k ∈ Finset.range (w+1), W k = 0 := by
    have hrefl := Finset.sum_range_reflect (fun k => W k) (w+1)
    simp only [Nat.add_sub_cancel] at hrefl
    have hneg : ∑ k ∈ Finset.range (w+1), W (w - k) = - ∑ k ∈ Finset.range (w+1), W k := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _; exact hanti k
    rw [hneg] at hrefl
    linarith
  have hC : ∑ m ∈ Finset.Ico (i + 1) (w + 1), W m
          = ∑ k ∈ Finset.range (w - i), W (i + 1 + k) := by
    rw [Finset.sum_Ico_eq_sum_range, show (w + 1) - (i + 1) = w - i from by omega]
  have hD : (∑ k ∈ Finset.range (i + 1), W k)
              + (∑ m ∈ Finset.Ico (i + 1) (w + 1), W m) = 0 := by
    rw [Finset.sum_range_add_sum_Ico (fun k => W k) (show i + 1 ≤ w + 1 from by omega)]
    exact htot
  have hB : ∑ k ∈ Finset.range (w - i), W (w - i - 1 - k)
          = - ∑ k ∈ Finset.range (w - i), W (i + 1 + k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hidx : w - (i + 1 + k) = w - i - 1 - k := by omega
    have hh := hanti (i + 1 + k)
    rw [hidx] at hh
    linarith
  have hA := Finset.sum_range_reflect (fun k => W k) (w - i)
  calc ∑ k ∈ Finset.range (i + 1), W k
      = - ∑ m ∈ Finset.Ico (i + 1) (w + 1), W m := by linarith [hD]
    _ = - ∑ k ∈ Finset.range (w - i), W (i + 1 + k) := by rw [hC]
    _ = ∑ k ∈ Finset.range (w - i), W (w - i - 1 - k) := hB.symm
    _ = ∑ k ∈ Finset.range (w - i), W k := hA

/-- The descent integral form. -/
noncomputable def Lint (A : ℤ) (M : ℕ) (V : ℕ → ℤ) (w : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (M+1), V i *
    (Ring.choose (A*(M:ℤ) - (w:ℤ) - 1) (M-i-1) - Ring.choose (A*(M:ℤ) - (w:ℤ) - 1) (M-i))

/-- Antipalindromic first-moment sequence. -/
noncomputable def Wtil (w : ℕ) (V : ℕ → ℤ) (i : ℕ) : ℤ := ((w:ℤ) - 2*(i:ℤ)) * V i

/-- Negative partial sums of `Wtil` (the "next level" palindromic sequence). -/
noncomputable def Vpr (w : ℕ) (V : ℕ → ℤ) (i : ℕ) : ℤ :=
  - ∑ k ∈ Finset.range (i+1), Wtil w V k

/-- **Descent divisibility (key induction).** -/
lemma DESC (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (A : ℤ) (M : ℕ) (hM : 0 < M) :
    ∀ w : ℕ, ∀ V : ℕ → ℤ,
      (∀ i, V i = V (w - i)) →
      (∀ i, w < i → V i = 0) →
      (∃ t₀, 1 ≤ t₀ ∧ ∀ i, i < t₀ → V i = 0) →
      w < p ^ (padicValNat p M) →
      (p:ℤ)^(2 * padicValNat p M)
        ∣ (p:ℤ)^(padicValNat p w.factorial + padicValNat p (w-1).factorial) * Lint A M V w := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro w
  induction w using Nat.strong_induction_on with
  | _ w IH =>
    intro V hpal hsU hsL hsm
    obtain ⟨t₀, ht₀1, ht₀L⟩ := hsL
    set E := padicValNat p M with hEdef
    have hpEM : p ^ E ∣ M := pow_padicValNat_dvd
    have hpEMle : p ^ E ≤ M := Nat.le_of_dvd hM hpEM
    have hwM : w < M := lt_of_lt_of_le hsm hpEMle
    by_cases hbase : w < 2 * t₀
    · -- base: V ≡ 0
      have hV0all : ∀ i, V i = 0 := by
        intro i
        by_cases hi : i < t₀
        · exact ht₀L i hi
        · by_cases hiw : w < i
          · exact hsU i hiw
          · have : V (w - i) = 0 := ht₀L (w - i) (by omega)
            rw [hpal i]; exact this
      have hLint0 : Lint A M V w = 0 := by
        unfold Lint; apply Finset.sum_eq_zero; intro i _; rw [hV0all i, zero_mul]
      rw [hLint0, mul_zero]; exact dvd_zero _
    · -- inductive step
      push_neg at hbase
      have hw2 : 2 ≤ w := by omega
      have hwpos : 0 < w := by omega
      have hV0 : V 0 = 0 := ht₀L 0 (by omega)
      have hVw : V w = 0 := by rw [hpal w, Nat.sub_self]; exact hV0
      -- antipalindromy of Wtil
      have hWanti : ∀ i, Wtil w V (w - i) = - Wtil w V i := by
        intro i
        by_cases hiw : i ≤ w
        · have hVeq : V (w - i) = V i := by
            have h := hpal (w - i); rw [show w - (w - i) = i from by omega] at h; rw [h]
          simp only [Wtil]; rw [hVeq, Nat.cast_sub hiw]; ring
        · push_neg at hiw
          have hVi : V i = 0 := hsU i hiw
          have hz : w - i = 0 := by omega
          simp only [Wtil, hz, hVi, hV0, Nat.cast_zero]; ring
      -- (X-1)·Vpr = Wtil (Nat-subtraction convention)
      have hrel : ∀ i, Wtil w V i = Vpr w V (i-1) - Vpr w V i := by
        intro i
        rcases Nat.eq_zero_or_pos i with hi0 | hipos
        · subst hi0
          have h0 : Wtil w V 0 = 0 := by simp only [Wtil]; rw [hV0]; ring
          simp only [Nat.zero_sub]; rw [h0]; ring
        · simp only [Vpr]
          rw [show i - 1 + 1 = i from by omega, Finset.sum_range_succ]; ring
      -- total sum of Wtil is zero
      have hWtot : ∑ k ∈ Finset.range (w+1), Wtil w V k = 0 := by
        have hrefl := Finset.sum_range_reflect (fun k => Wtil w V k) (w+1)
        simp only [Nat.add_sub_cancel] at hrefl
        have hneg : ∑ k ∈ Finset.range (w+1), Wtil w V (w - k)
            = - ∑ k ∈ Finset.range (w+1), Wtil w V k := by
          rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro k _; exact hWanti k
        rw [hneg] at hrefl; linarith
      -- Vpr support (lower)
      have hVprL : ∀ i, i < t₀ → Vpr w V i = 0 := by
        intro i hi
        simp only [Vpr]
        have hz : ∀ k ∈ Finset.range (i+1), Wtil w V k = 0 := by
          intro k hk; rw [Finset.mem_range] at hk
          simp only [Wtil]; rw [ht₀L k (by omega), mul_zero]
        rw [Finset.sum_eq_zero hz]; ring
      -- Vpr support (upper)
      have hVprU : ∀ i, w - 1 < i → Vpr w V i = 0 := by
        intro i hi
        simp only [Vpr]
        have heq : ∑ k ∈ Finset.range (i+1), Wtil w V k
            = ∑ k ∈ Finset.range (w+1), Wtil w V k := by
          symm; apply Finset.sum_subset
          · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
          · intro x hx hxns; rw [Finset.mem_range] at hx hxns
            simp only [Wtil]; rw [hsU x (by omega), mul_zero]
        rw [heq, hWtot]; ring
      have hVpr0 : Vpr w V 0 = 0 := hVprL 0 (by omega)
      have hVprM : Vpr w V M = 0 := hVprU M (by omega)
      -- Vpr palindromy about (w-1)/2
      have hVprpal : ∀ i, Vpr w V i = Vpr w V ((w-1) - i) := by
        intro i
        by_cases hi : i < w
        · simp only [Vpr]; congr 1
          rw [show (w - 1 - i) + 1 = w - i from by omega]
          exact prefix_reflect (Wtil w V) w hWanti i hi
        · push_neg at hi
          have h1 : Vpr w V i = 0 := hVprU i (by omega)
          have h2 : Vpr w V ((w-1)-i) = 0 := by
            rw [show w - 1 - i = 0 from by omega]; exact hVprL 0 (by omega)
          rw [h1, h2]
      -- set abbreviations
      set vw := padicValNat p w with hvwdef
      set G := padicValNat p (w-1).factorial with hGdef
      set Fw := padicValNat p w.factorial + padicValNat p (w-1).factorial with hFwdef
      set P1 : ℤ := ∑ i ∈ Finset.range (M+1), V i * Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i)
        with hPdef
      -- factorial valuation splits
      have hwfact : w.factorial = w * (w-1).factorial := by
        conv_lhs => rw [show w = (w-1)+1 from by omega]
        rw [Nat.factorial_succ, show (w-1)+1 = w from by omega]
      have hval : padicValNat p w.factorial = vw + G := by
        rw [hwfact, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
      have hFw2 : Fw = vw + 2*G := by rw [hFwdef, hval]; ring
      -- recursion identity
      have hsupp : ∀ i, M ≤ i → V i = 0 := by intro i hi; exact hsU i (by omega)
      have hrec : (A*(M:ℤ) - (w:ℤ)) * Lint A M V w
          = -((A - 2)*(M:ℤ)) * P1 + Lint A M (Vpr w V) (w - 1) := by
        have hds := descent_sum (A*(M:ℤ) - (w:ℤ)) M V hsupp
        have hL : Lint A M V w
            = ∑ i ∈ Finset.range (M+1), V i *
                (Ring.choose ((A*(M:ℤ)-(w:ℤ)) - 1) (M-i-1) - Ring.choose ((A*(M:ℤ)-(w:ℤ))-1) (M-i)) := rfl
        rw [hL, hds]
        -- split the RHS
        have hsplit : (∑ i ∈ Finset.range (M+1),
              (2*((M:ℤ)-(i:ℤ)) - (A*(M:ℤ)-(w:ℤ))) * V i * Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i))
            = -((A-2)*(M:ℤ)) * P1
                + ∑ i ∈ Finset.range (M+1), Wtil w V i * Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i) := by
          rw [hPdef, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _; simp only [Wtil]; ring
        rw [hsplit]
        -- abel: the Wtil-sum becomes next-level Lint
        have habel : (∑ i ∈ Finset.range (M+1), Wtil w V i * Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i))
            = Lint A M (Vpr w V) (w - 1) := by
          have key := abel_id M (Vpr w V) (fun i => Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i)) hVpr0 hVprM
          calc ∑ i ∈ Finset.range (M+1), Wtil w V i * Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i)
              = ∑ i ∈ Finset.range (M+1), (Vpr w V (i-1) - Vpr w V i)
                  * (fun i => Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i)) i := by
                apply Finset.sum_congr rfl; intro i _; rw [hrel i]
            _ = ∑ i ∈ Finset.range (M+1), Vpr w V i
                  * ((fun i => Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i)) (i+1)
                      - (fun i => Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i)) i) := key
            _ = Lint A M (Vpr w V) (w-1) := by
                unfold Lint
                apply Finset.sum_congr rfl
                intro i _
                dsimp only
                have hcast : A*(M:ℤ) - ((w-1 : ℕ):ℤ) - 1 = A*(M:ℤ) - (w:ℤ) := by
                  rw [Nat.cast_sub (by omega : 1 ≤ w)]; push_cast; ring
                rw [hcast, show M - (i+1) = M - i - 1 from by omega]
        rw [habel]
      -- (5) GK sum: p^E ∣ (w-1)! · P1
      have hgk : (p:ℤ)^E ∣ ((w-1).factorial : ℤ) * P1 := by
        rw [hPdef, Finset.mul_sum]
        apply Finset.dvd_sum
        intro i hi; rw [Finset.mem_range] at hi
        by_cases hpos : 0 < i ∧ i < w
        · have hgki := GK p hp A M w i hpos.2 hpos.1
          have hre : ((w-1).factorial:ℤ) * (V i * Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i))
               = V i * (((w-1).factorial:ℤ) * Ring.choose (A*(M:ℤ)-(w:ℤ)) (M-i)) := by ring
          rw [hre]
          exact Dvd.dvd.mul_left hgki (V i)
        · have hVi0 : V i = 0 := by
            rcases Nat.eq_zero_or_pos i with h0 | h0
            · rw [h0]; exact hV0
            · push_neg at hpos
              have hiw : w ≤ i := hpos h0
              rcases eq_or_lt_of_le hiw with he | hl
              · rw [← he]; exact hVw
              · exact hsU i hl
          rw [hVi0]; simp
      -- exact valuations for cancellations
      have hGdvd : (p:ℤ)^G ∣ ((w-1).factorial : ℤ) := by
        have h : p^G ∣ (w-1).factorial := by rw [hGdef]; exact pow_padicValNat_dvd
        exact_mod_cast h
      have hGnd : ¬ ((p:ℤ)^(G+1) ∣ ((w-1).factorial:ℤ)) := by
        intro hcon
        have h : p^(G+1) ∣ (w-1).factorial := by exact_mod_cast hcon
        rw [hGdef] at h
        exact pow_succ_padicValNat_not_dvd (Nat.factorial_pos _).ne' h
      have hP1div : (p:ℤ)^(E - G) ∣ P1 := by
        rcases le_or_gt G E with hGE | hEG
        · have hh : (p:ℤ)^(G + (E-G)) ∣ ((w-1).factorial:ℤ) * P1 := by
            rw [show G + (E - G) = E from by omega]; exact hgk
          exact pcancel p hp G (E-G) ((w-1).factorial:ℤ) P1 hGdvd hGnd hh
        · rw [show E - G = 0 from by omega, pow_zero]; exact one_dvd _
      have hAM2 : (p:ℤ)^E ∣ (A-2)*(M:ℤ) := by
        have hMint : (p:ℤ)^E ∣ (M:ℤ) := by exact_mod_cast hpEM
        exact hMint.mul_left (A-2)
      -- TermA
      have hTermA : (p:ℤ)^(2*E) ∣ (p:ℤ)^(2*G) * ((A-2)*(M:ℤ)*P1) := by
        have hmul : (p:ℤ)^(E + (E - G)) ∣ (A-2)*(M:ℤ) * P1 := by
          rw [pow_add]; exact mul_dvd_mul hAM2 hP1div
        have hmul2 : (p:ℤ)^(2*G + (E + (E-G))) ∣ (p:ℤ)^(2*G) * ((A-2)*(M:ℤ)*P1) := by
          rw [pow_add]; exact mul_dvd_mul_left _ hmul
        exact dvd_trans (pow_dvd_pow (p:ℤ) (by omega : 2*E ≤ 2*G + (E + (E-G)))) hmul2
      have hTermA' : (p:ℤ)^(vw + 2*E) ∣ (p:ℤ)^Fw * ((A-2)*(M:ℤ)*P1) := by
        have h1 : (p:ℤ)^Fw * ((A-2)*(M:ℤ)*P1)
            = (p:ℤ)^vw * ((p:ℤ)^(2*G) * ((A-2)*(M:ℤ)*P1)) := by
          rw [hFw2, pow_add, mul_assoc]
        rw [h1, pow_add]
        exact mul_dvd_mul_left _ hTermA
      -- TermB via IH
      have hIH := IH (w-1) (by omega) (Vpr w V) hVprpal hVprU
        ⟨t₀, ht₀1, hVprL⟩ (by omega)
      set Fw1 := padicValNat p (w-1).factorial + padicValNat p (w-1-1).factorial with hFw1def
      have hwfact1 : (w-1).factorial = (w-1) * (w-1-1).factorial := by
        conv_lhs => rw [show w-1 = (w-1-1)+1 from by omega]
        rw [Nat.factorial_succ, show (w-1-1)+1 = w-1 from by omega]
      have hval1 : G = padicValNat p (w-1) + padicValNat p (w-1-1).factorial := by
        rw [hGdef, hwfact1, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
      have hle : vw + Fw1 ≤ Fw := by
        rw [hFwdef, hFw1def, ← hGdef]; omega
      have hTermB : (p:ℤ)^(vw + 2*E) ∣ (p:ℤ)^Fw * Lint A M (Vpr w V) (w-1) := by
        have step1 : (p:ℤ)^(vw + 2*E)
            ∣ (p:ℤ)^vw * ((p:ℤ)^Fw1 * Lint A M (Vpr w V) (w-1)) := by
          rw [pow_add]; exact mul_dvd_mul_left _ hIH
        have step2 : (p:ℤ)^vw * ((p:ℤ)^Fw1 * Lint A M (Vpr w V) (w-1))
            = (p:ℤ)^(vw+Fw1) * Lint A M (Vpr w V) (w-1) := by rw [← mul_assoc, ← pow_add]
        rw [step2] at step1
        exact dvd_trans step1 (mul_dvd_mul_right (pow_dvd_pow _ hle) _)
      -- big divisibility
      have hbig : (p:ℤ)^(vw + 2*E)
          ∣ (A*(M:ℤ)-(w:ℤ)) * ((p:ℤ)^Fw * Lint A M V w) := by
        have hEq : (A*(M:ℤ)-(w:ℤ)) * ((p:ℤ)^Fw * Lint A M V w)
            = -((p:ℤ)^Fw * ((A-2)*(M:ℤ) * P1)) + (p:ℤ)^Fw * Lint A M (Vpr w V) (w-1) := by
          have hh : (A*(M:ℤ)-(w:ℤ)) * ((p:ℤ)^Fw * Lint A M V w)
               = (p:ℤ)^Fw * ((A*(M:ℤ)-(w:ℤ)) * Lint A M V w) := by ring
          rw [hh, hrec]; ring
        rw [hEq]; apply dvd_add
        · rw [dvd_neg]; exact hTermA'
        · exact hTermB
      -- valuation of A*M - w is exactly vw
      have hvwE : vw < E := by
        have h1 : p^vw ∣ w := by rw [hvwdef]; exact pow_padicValNat_dvd
        have h2 : p^vw ≤ w := Nat.le_of_dvd hwpos h1
        exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp (lt_of_le_of_lt h2 hsm)
      have hXdvd : (p:ℤ)^vw ∣ (A*(M:ℤ) - (w:ℤ)) := by
        apply dvd_sub
        · have hnat : p^vw ∣ M := dvd_trans (pow_dvd_pow p (le_of_lt hvwE)) hpEM
          have : (p:ℤ)^vw ∣ (M:ℤ) := by exact_mod_cast hnat
          exact this.mul_left A
        · have hnat : p^vw ∣ w := by rw [hvwdef]; exact pow_padicValNat_dvd
          exact_mod_cast hnat
      have hXnd : ¬ ((p:ℤ)^(vw+1) ∣ (A*(M:ℤ) - (w:ℤ))) := by
        intro hcon
        have hAMdvd : (p:ℤ)^(vw+1) ∣ A*(M:ℤ) := by
          have hnat : p^(vw+1) ∣ M := dvd_trans (pow_dvd_pow p (by omega : vw+1 ≤ E)) hpEM
          have : (p:ℤ)^(vw+1) ∣ (M:ℤ) := by exact_mod_cast hnat
          exact this.mul_left A
        have hwdvd : (p:ℤ)^(vw+1) ∣ (w:ℤ) := by
          have hsub := dvd_sub hAMdvd hcon
          rwa [show A*(M:ℤ) - (A*(M:ℤ) - (w:ℤ)) = (w:ℤ) from by ring] at hsub
        have hwnat : p^(vw+1) ∣ w := by exact_mod_cast hwdvd
        rw [hvwdef] at hwnat
        exact pow_succ_padicValNat_not_dvd hwpos.ne' hwnat
      -- cancel p^vw
      exact pcancel p hp vw (2*E) (A*(M:ℤ)-(w:ℤ)) ((p:ℤ)^Fw * Lint A M V w) hXdvd hXnd hbig

/-- **Prop 5 (dominant regime), clean form.** -/
theorem prop5dom (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (A : ℤ) (M : ℕ) (hM : 0 < M) (j : ℕ)
    (hj : 3 ≤ j) (hE : j - 1 < p ^ (padicValNat p M)) :
    (p : ℤ) ^ (2 * padicValNat p M)
      ∣ (p : ℤ) ^ (padicValNat p (j-1).factorial + padicValNat p (j-2).factorial)
          * ℓ (ψ p j) (A * (M : ℤ)) M := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSpal, hSU, hSL, hSrel⟩ := structA p hp hp5 j hj
  have hpEM : p ^ (padicValNat p M) ∣ M := pow_padicValNat_dvd
  have hjM : j - 1 < M := lt_of_lt_of_le hE (Nat.le_of_dvd hM hpEM)
  have hSM : S M = 0 := hSU M (by omega)
  have hS0 : S 0 = 0 := hSL 0 (Nat.add_pos_left one_pos _)
  have hell : ℓ (ψ p j) (A * (M:ℤ)) M = Lint A M S (j-1) := by
    rw [closed_form_ell p hp.pos A M j]
    have hrefl := Finset.sum_range_reflect
      (fun k => Ring.choose (A*(M:ℤ)-(j:ℤ)) k
        * PowerSeries.coeff (p*(M-k)) (qser p^j*Gser)) (M+1)
    simp only [Nat.add_sub_cancel] at hrefl
    rw [← hrefl]
    have hstep : ∀ k ∈ Finset.range (M+1),
        Ring.choose (A*(M:ℤ)-(j:ℤ)) (M-k) * PowerSeries.coeff (p*(M-(M-k))) (qser p^j*Gser)
        = (S (k-1) - S k) * Ring.choose (A*(M:ℤ)-(j:ℤ)) (M-k) := by
      intro k hk; rw [Finset.mem_range] at hk
      rw [show M-(M-k) = k from by omega, hSrel k]
      by_cases hk0 : k = 0
      · subst hk0; simp [hS0]
      · rw [if_neg hk0]; ring
    rw [Finset.sum_congr rfl hstep]
    calc ∑ k ∈ Finset.range (M+1), (S (k-1) - S k) * Ring.choose (A*(M:ℤ)-(j:ℤ)) (M-k)
        = ∑ k ∈ Finset.range (M+1), (S (k-1) - S k)
            * (fun i => Ring.choose (A*(M:ℤ)-(j:ℤ)) (M-i)) k := by
          apply Finset.sum_congr rfl; intro k _; rfl
      _ = ∑ i ∈ Finset.range (M+1), S i
            * ((fun i => Ring.choose (A*(M:ℤ)-(j:ℤ)) (M-i)) (i+1)
                - (fun i => Ring.choose (A*(M:ℤ)-(j:ℤ)) (M-i)) i) :=
          abel_id M S (fun i => Ring.choose (A*(M:ℤ)-(j:ℤ)) (M-i)) hS0 hSM
      _ = Lint A M S (j-1) := by
          unfold Lint
          apply Finset.sum_congr rfl
          intro i _; dsimp only
          have hcast : A*(M:ℤ) - ((j-1:ℕ):ℤ) - 1 = A*(M:ℤ) - (j:ℤ) := by
            rw [Nat.cast_sub (by omega : 1 ≤ j)]; push_cast; ring
          rw [hcast, show M - (i+1) = M - i - 1 from by omega]
  rw [hell]
  have hdesc := DESC p hp hp5 A M hM (j-1) S hSpal hSU
    ⟨1 + (j-1)/p, Nat.le_add_right 1 _, hSL⟩ hE
  rw [show j - 1 - 1 = j - 2 from by omega] at hdesc
  exact hdesc

end Dominant

section Termdvd
open PowerSeries Finset

/-! ## Elementary power bound -/

lemma pow5ge : ∀ n : ℕ, 4 * n + 1 ≤ 5 ^ n
  | 0 => by norm_num
  | (n + 1) => by
    have ih := pow5ge n
    have h2 : 5 * (4 * n + 1) ≤ 5 * 5 ^ n := mul_le_mul_left' ih 5
    have he : 5 ^ (n + 1) = 5 * 5 ^ n := by rw [pow_succ]; ring
    omega

/-! ## Absorption identity for `Ring.choose` -/

/-- `(k+1)·C(N,k+1) = N·C(N-1,k)` (committee–chair identity for `Ring.choose`). -/
lemma absorb (N : ℤ) (k : ℕ) :
    ((k + 1 : ℕ) : ℤ) * Ring.choose N (k + 1) = N * Ring.choose (N - 1) k := by
  have hk : ((k.factorial : ℤ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  apply mul_left_cancel₀ hk
  have e1 : (k.factorial : ℤ) * (((k + 1 : ℕ) : ℤ) * Ring.choose N (k + 1))
      = ∏ i ∈ range (k + 1), (N - (i:ℤ)) := by
    have hpk : (∏ i ∈ range (k+1), (N - (i:ℤ)))
        = ((k+1).factorial : ℤ) * Ring.choose N (k+1) := by
      have h := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) N (k+1)
      rw [nsmul_eq_mul] at h
      rw [← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range] at h
      exact h
    rw [hpk]
    have : ((k + 1).factorial : ℤ) = ((k + 1 : ℕ) : ℤ) * (k.factorial : ℤ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [this]; ring
  have e2 : (k.factorial : ℤ) * (N * Ring.choose (N - 1) k)
      = ∏ i ∈ range (k + 1), (N - (i:ℤ)) := by
    have hpk : (∏ i ∈ range k, ((N - 1) - (i:ℤ))) = (k.factorial : ℤ) * Ring.choose (N-1) k := by
      have h := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) (N-1) k
      rw [nsmul_eq_mul] at h
      rw [← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range] at h
      exact h
    rw [Finset.prod_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
    rw [show (∏ i ∈ range k, (N - ((i:ℤ) + 1))) = ∏ i ∈ range k, ((N - 1) - (i:ℤ)) from
      Finset.prod_congr rfl (fun i _ => by ring)]
    rw [hpk]; ring
  rw [e1, e2]

/-! ## Arithmetic (valuation) lemmas -/

/-- ARITH1: for `p ≥ 5` prime and `j ≥ 3`,
`v_p(j) + v_p((j-1)!) + v_p((j-2)!) + 3 ≤ j`. -/
lemma arith1 (p j : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 3 ≤ j) :
    padicValNat p j + padicValNat p (j-1).factorial + padicValNat p (j-2).factorial + 3 ≤ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hfact : j.factorial = j * (j-1).factorial := by
    conv_lhs => rw [show j = (j-1)+1 from by omega]
    rw [Nat.factorial_succ, show (j-1)+1 = j from by omega]
  have hsplit : padicValNat p j.factorial
      = padicValNat p j + padicValNat p (j-1).factorial := by
    rw [hfact, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
  have h4 : 4 ≤ p - 1 := by omega
  -- Legendre bounds
  have hL1 : (p - 1) * padicValNat p j.factorial < j :=
    sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega)
  have hL2 : (p - 1) * padicValNat p (j-2).factorial < (j-2) :=
    sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega)
  have b1 : 4 * padicValNat p j.factorial < j :=
    lt_of_le_of_lt (mul_le_mul_right' h4 _) hL1
  have b2 : 4 * padicValNat p (j-2).factorial < (j-2) :=
    lt_of_le_of_lt (mul_le_mul_right' h4 _) hL2
  omega

/-- ARITH2: for `p ≥ 5` prime, `j ≥ 3` and `p^E ≤ j - 1`,
`v_p(j) + 2E + 3 ≤ j`. -/
lemma arith2 (p E j : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 3 ≤ j)
    (hb : p ^ E ≤ j - 1) :
    padicValNat p j + 2 * E + 3 ≤ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- Bound on E
  have h5E : (5:ℕ) ^ E ≤ p ^ E := Nat.pow_le_pow_left hp5 E
  have hEb : 4 * E + 1 ≤ j - 1 := le_trans (pow5ge E) (le_trans h5E hb)
  -- Bound on v_p(j)
  have hvjdvd : p ^ (padicValNat p j) ∣ j := pow_padicValNat_dvd
  have hvjle : p ^ (padicValNat p j) ≤ j := Nat.le_of_dvd (by omega) hvjdvd
  have h5vj : (5:ℕ) ^ (padicValNat p j) ≤ p ^ (padicValNat p j) := Nat.pow_le_pow_left hp5 _
  have hvjb : 4 * padicValNat p j + 1 ≤ j := le_trans (pow5ge _) (le_trans h5vj hvjle)
  omega

/-! ## Divisibility combination lemmas -/

lemma combine_dom (p : ℕ) (E vj F j : ℕ) (C L : ℤ)
    (h1 : (p:ℤ)^E ∣ (p:ℤ)^vj * C)
    (h2 : (p:ℤ)^(2*E) ∣ (p:ℤ)^F * L)
    (harith : vj + F + 3 ≤ j) :
    (p:ℤ)^(3*E+3) ∣ C * (p:ℤ)^j * L := by
  have hmul := mul_dvd_mul h1 h2
  have hL : (p:ℤ)^E * (p:ℤ)^(2*E) = (p:ℤ)^(3*E) := by
    rw [← pow_add, show E + 2*E = 3*E from by ring]
  have hR : ((p:ℤ)^vj * C) * ((p:ℤ)^F * L) = (p:ℤ)^(vj+F) * (C*L) := by
    rw [pow_add]; ring
  rw [hL, hR] at hmul
  have hmul2 := mul_dvd_mul_left ((p:ℤ)^(j-vj-F)) hmul
  have e1 : (p:ℤ)^(j-vj-F) * (p:ℤ)^(3*E) = (p:ℤ)^((j-vj-F)+3*E) := by rw [← pow_add]
  have e2 : (p:ℤ)^(j-vj-F) * ((p:ℤ)^(vj+F) * (C*L)) = (p:ℤ)^j * (C*L) := by
    rw [← mul_assoc, ← pow_add, show (j-vj-F)+(vj+F) = j from by omega]
  rw [e1, e2] at hmul2
  have hfin : (p:ℤ)^(3*E+3) ∣ (p:ℤ)^((j-vj-F)+3*E) := pow_dvd_pow _ (by omega)
  have hfinal := dvd_trans hfin hmul2
  rwa [show (p:ℤ)^j * (C*L) = C * (p:ℤ)^j * L from by ring] at hfinal

lemma combine_small (p : ℕ) (E vj j : ℕ) (C L : ℤ)
    (h1 : (p:ℤ)^E ∣ (p:ℤ)^vj * C)
    (harith : vj + 2*E + 3 ≤ j) :
    (p:ℤ)^(3*E+3) ∣ C * (p:ℤ)^j * L := by
  have hm : (p:ℤ)^E ∣ ((p:ℤ)^vj * C) * L := h1.mul_right L
  have hm2 := mul_dvd_mul_left ((p:ℤ)^(j-vj)) hm
  have e1 : (p:ℤ)^(j-vj) * (p:ℤ)^E = (p:ℤ)^((j-vj)+E) := by rw [← pow_add]
  have e2 : (p:ℤ)^(j-vj) * (((p:ℤ)^vj * C) * L) = (p:ℤ)^j * (C*L) := by
    rw [show ((p:ℤ)^vj * C) * L = (p:ℤ)^vj * (C*L) from by ring, ← mul_assoc, ← pow_add,
      show (j-vj)+vj = j from by omega]
  rw [e1, e2] at hm2
  have hfin : (p:ℤ)^(3*E+3) ∣ (p:ℤ)^((j-vj)+E) := pow_dvd_pow _ (by omega)
  have hfinal := dvd_trans hfin hm2
  rwa [show (p:ℤ)^j * (C*L) = C * (p:ℤ)^j * L from by ring] at hfinal

/-! ## Main theorem -/

theorem termDvd (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (A : ℤ) (M : ℕ) (hM : 0 < M) (j : ℕ)
    (hj : 3 ≤ j) :
    (p : ℤ) ^ (3 * padicValNat p M + 3)
      ∣ Ring.choose (A * (M:ℤ)) j * (p : ℤ) ^ j * ℓ (ψ p j) (A * (M:ℤ)) M := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- p^E divides A*M
  have hpEM : p ^ (padicValNat p M) ∣ M := pow_padicValNat_dvd
  have hpEAM : (p:ℤ) ^ (padicValNat p M) ∣ A * (M:ℤ) := by
    have hMint : (p:ℤ) ^ (padicValNat p M) ∣ (M:ℤ) := by exact_mod_cast hpEM
    exact hMint.mul_left A
  -- (i): p^E ∣ j * C
  have hi : (p:ℤ) ^ (padicValNat p M) ∣ ((j:ℕ):ℤ) * Ring.choose (A * (M:ℤ)) j := by
    have habs := absorb (A * (M:ℤ)) (j-1)
    rw [show (j-1)+1 = j from by omega] at habs
    rw [habs]
    exact hpEAM.mul_right _
  -- corollary: p^E ∣ p^(v_p j) * C
  have hcor : (p:ℤ) ^ (padicValNat p M)
      ∣ (p:ℤ) ^ (padicValNat p j) * Ring.choose (A * (M:ℤ)) j := by
    obtain ⟨jc, hjc⟩ := (pow_padicValNat_dvd : p ^ (padicValNat p j) ∣ j)
    have hpjc : ¬ (p ∣ jc) := by
      rintro ⟨t, ht⟩
      refine pow_succ_padicValNat_not_dvd (p := p) (n := j) (show j ≠ 0 from by omega) ⟨t, ?_⟩
      rw [pow_succ, mul_assoc, ← ht]
      exact hjc
    have hjcZ : ((j:ℕ):ℤ) = (p:ℤ) ^ (padicValNat p j) * (jc:ℤ) := by
      exact_mod_cast hjc
    rw [hjcZ] at hi
    have hi2 : (p:ℤ) ^ (padicValNat p M)
        ∣ ((p:ℤ) ^ (padicValNat p j) * Ring.choose (A * (M:ℤ)) j) * (jc:ℤ) := by
      have hre : (p:ℤ) ^ (padicValNat p j) * (jc:ℤ) * Ring.choose (A * (M:ℤ)) j
          = ((p:ℤ) ^ (padicValNat p j) * Ring.choose (A * (M:ℤ)) j) * (jc:ℤ) := by ring
      rwa [hre] at hi
    have hcop : IsCoprime ((p:ℤ) ^ (padicValNat p M)) ((jc:ℤ)) :=
      (((hp.coprime_iff_not_dvd).mpr hpjc).isCoprime).pow_left
    exact hcop.dvd_of_dvd_mul_right hi2
  -- Regime split
  by_cases hcase : j - 1 < p ^ (padicValNat p M)
  · -- Dominant
    have hprop := prop5dom p hp hp5 A M hM j hj hcase
    refine combine_dom p (padicValNat p M) (padicValNat p j)
      (padicValNat p (j-1).factorial + padicValNat p (j-2).factorial) j
      (Ring.choose (A * (M:ℤ)) j) (ℓ (ψ p j) (A * (M:ℤ)) M) hcor hprop ?_
    have := arith1 p j hp hp5 hj
    omega
  · -- Small
    have hb : p ^ (padicValNat p M) ≤ j - 1 := Nat.le_of_not_lt hcase
    refine combine_small p (padicValNat p M) (padicValNat p j) j
      (Ring.choose (A * (M:ℤ)) j) (ℓ (ψ p j) (A * (M:ℤ)) M) hcor ?_
    have := arith2 p (padicValNat p M) j hp hp5 hj hb
    omega

end Termdvd

section Reduce
open PowerSeries Finset

lemma gc_eq_gcoef (t : ℕ) : gc t = gcoef t := by
  unfold gc gcoef; rfl

theorem agen_eq_u (m : ℤ) (hm : m ≠ -1) (n : ℕ) :
    a_gen m n = u ((m + 2) * (n:ℤ)) n := by
  rw [closed_form m hm n]
  unfold u ℓ
  rw [coeffMul]
  -- RHS coefficient forms
  have hR : ∀ i, (PowerSeries.coeff i) (binomialSeries ℤ ((m + 2) * (n:ℤ)))
      * (PowerSeries.coeff (n - i)) Gser
      = Ring.choose ((m + 2) * (n:ℤ)) i * gc (n - i) := by
    intro i
    rw [binomialSeries_coeff, coeff_Gser, smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl (fun i _ => hR i)]
  -- reflect the LHS sum
  have hrefl := Finset.sum_range_reflect
    (fun j => gcoef j * Ring.choose ((m + 2) * (n:ℤ)) (n - j)) (n + 1)
  simp only [Nat.add_sub_cancel] at hrefl
  rw [← hrefl]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hni : n - (n - i) = i := by omega
  rw [hni, gc_eq_gcoef, mul_comm]

theorem reduce_conj (m : ℤ) (hm : m ≠ -1) (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5)
    (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    a_gen m (n * p ^ k) ≡ a_gen m (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  have hp0 : 0 < p := hp.pos
  set M : ℕ := n * p ^ (k - 1) with hMdef
  have hMne : M ≠ 0 := by
    rw [hMdef]; exact Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  have hM0 : 0 < M := Nat.pos_of_ne_zero hMne
  have hMp : M * p = n * p ^ k := by
    have hk1 : k - 1 + 1 = k := by omega
    rw [hMdef, mul_assoc, ← pow_succ, hk1]
  -- express a_gens as u
  have hAlo : a_gen m M = u ((m + 2) * (M:ℤ)) M := agen_eq_u m hm M
  have hAhi : a_gen m (n * p ^ k) = u (((m + 2) * (M:ℤ)) * (p:ℤ)) (M * p) := by
    rw [← hMp, agen_eq_u m hm (M * p)]
    congr 1
    push_cast; ring
  -- main formula
  have hmf := main_formula p hp hp5 M ((m + 2) * (M:ℤ))
  -- difference as a sum
  have hdiff : a_gen m (n * p ^ k) - a_gen m M
      = ∑ j ∈ (range (M * p + 1)).filter (fun j => 3 ≤ j),
          Ring.choose ((m + 2) * (M:ℤ)) j * (p:ℤ) ^ j * ℓ (ψ p j) ((m + 2) * (M:ℤ)) M := by
    rw [hAhi, hAlo]; exact hmf
  -- divisibility of the difference
  have hdvdSum : (p:ℤ) ^ (3 * k) ∣ a_gen m (n * p ^ k) - a_gen m M := by
    rw [hdiff]
    apply Finset.dvd_sum
    intro j hj
    rw [Finset.mem_filter] at hj
    have hj3 : 3 ≤ j := hj.2
    have ht := termDvd p hp hp5 (m + 2) M hM0 j hj3
    have hpow : p ^ (k - 1) ∣ M := by rw [hMdef]; exact dvd_mul_left _ _
    have hle : k - 1 ≤ padicValNat p M := by
      have h := (Nat.Prime.pow_dvd_iff_le_factorization hp hMne).mp hpow
      rwa [Nat.factorization_def M hp] at h
    have hexp : 3 * k ≤ 3 * padicValNat p M + 3 := by omega
    exact dvd_trans (pow_dvd_pow (p:ℤ) hexp) ht
  -- conclude the congruence
  rw [Int.modEq_iff_dvd]
  have hneg : a_gen m M - a_gen m (n * p ^ k)
      = -(a_gen m (n * p ^ k) - a_gen m M) := by ring
  rw [hneg]
  exact dvd_neg.mpr hdvdSum

end Reduce

section Mneg1
open Nat Finset BigOperators Int

/-- Step 1: `a_gen (-1) N = P ((N:ℤ)-2) (N-1)` for `N ≥ 1`. -/
lemma step1 (N : ℕ) (hN : 1 ≤ N) :
    a_gen (-1) N = P ((N:ℤ) - 2) (N - 1) := by
  have hN0 : N ≠ 0 := by omega
  rw [a_gen, if_neg hN0]
  rw [Finset.sum_range_succ]
  set r : ℤ := (-1) * (N:ℤ) with hr
  -- last term vanishes
  have hzero : generalized_catalan_coefficient r N = 0 := by
    unfold generalized_catalan_coefficient
    rw [if_neg hN0]
    have hden : r + (N:ℤ) = 0 := by rw [hr]; ring
    simp only []
    rw [hden, Int.ediv_zero]
  rw [hzero, add_zero]
  -- telescope on range N = range ((N-1)+1)
  have htel := telescope r (N - 1) (by
    intro k hk1 hk2
    have h1 : (k:ℤ) ≤ ((N - 1 : ℕ):ℤ) := by exact_mod_cast hk2
    have hc : ((N - 1 : ℕ):ℤ) = (N:ℤ) - 1 := by rw [Nat.cast_sub hN]; push_cast; ring
    rw [hc] at h1
    rw [hr]
    intro hcon
    have : (k:ℤ) = (N:ℤ) := by linarith [hcon]
    linarith [h1])
  have hrng : Finset.range ((N - 1) + 1) = Finset.range N := by rw [Nat.sub_add_cancel hN]
  rw [hrng] at htel
  rw [htel]
  congr 1
  rw [hr]
  have hc : ((N - 1 : ℕ):ℤ) = (N:ℤ) - 1 := by rw [Nat.cast_sub hN]; push_cast; ring
  rw [hc]; ring

/-- Step 2: `P ((N:ℤ)-2) (N-1) = P (N:ℤ) N + 1` for `N ≥ 1`. -/
lemma step2 (N : ℕ) (hN : 1 ≤ N) :
    P ((N:ℤ) - 2) (N - 1) = P (N:ℤ) N + 1 := by
  have hSI := SI ((N:ℤ) - 2) (N - 1)
  have e1 : (N:ℤ) - 2 + 2 = (N:ℤ) := by ring
  have e2 : (N - 1) + 1 = N := by omega
  rw [e1, e2] at hSI
  have e3 : (N:ℤ) - 2 + 1 = (N:ℤ) - 1 := by ring
  rw [e3] at hSI
  have hc1 : Ring.choose ((N:ℤ) - 1) N = 0 := by
    have hcast : (N:ℤ) - 1 = ((N - 1 : ℕ):ℤ) := by rw [Nat.cast_sub hN]; push_cast; ring
    rw [hcast, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have hc2 : Ring.choose ((N:ℤ) - 1) (N - 1) = 1 := by
    have hcast : (N:ℤ) - 1 = ((N - 1 : ℕ):ℤ) := by rw [Nat.cast_sub hN]; push_cast; ring
    rw [hcast, Ring.choose_natCast, Nat.choose_self]
    simp
  rw [hc1, hc2] at hSI
  linarith [hSI]

/-- Step 3: `P (N:ℤ) N = 3 * Sfun N 0 - 2^N - 1`. -/
lemma step3 (N : ℕ) :
    P (N:ℤ) N = 3 * Sfun N 0 - 2 ^ N - 1 := by
  rw [P_def]
  have hconv : ∀ j ∈ Finset.range (N + 1),
      gcoef j * Ring.choose (N:ℤ) (N - j) = gcoef j * (Nat.choose N j : ℤ) := by
    intro j hj
    rw [mem_range] at hj
    rw [Ring.choose_natCast, Nat.choose_symm (show j ≤ N by omega)]
  rw [Finset.sum_congr rfl hconv]
  have hpt : ∀ j ∈ Finset.range (N + 1),
      gcoef j * (Nat.choose N j : ℤ)
        = (3 * (if ((j:ℕ):ZMod 3) = 0 then (Nat.choose N j : ℤ) else 0) - (Nat.choose N j : ℤ))
          - (if j = 0 then (1:ℤ) else 0) := by
    intro j _
    by_cases hj0 : j = 0
    · subst hj0
      rw [if_pos rfl]
      norm_num [gcoef]
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      rw [if_neg hj0, sub_zero]
      have hg : gcoef j = 3 * (if 3 ∣ j then (1:ℤ) else 0) - 1 := by
        rw [← gc_eq_gcoef]; exact gc_pos j hj1
      rw [hg]
      have hiff : (((j:ℕ):ZMod 3) = 0) ↔ (3 ∣ j) := ZMod.natCast_eq_zero_iff j 3
      by_cases hd : 3 ∣ j
      · rw [if_pos hd, if_pos (hiff.mpr hd)]; ring
      · rw [if_neg hd, if_neg (fun h => hd (hiff.mp h))]; ring
  rw [Finset.sum_congr rfl hpt]
  have hS : (∑ j ∈ range (N + 1),
      if ((j:ℕ):ZMod 3) = 0 then (Nat.choose N j : ℤ) else 0) = Sfun N 0 := by
    unfold Sfun; rfl
  have hC : (∑ j ∈ range (N + 1), (Nat.choose N j : ℤ)) = 2 ^ N := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
  have hE : (∑ j ∈ range (N + 1), if j = 0 then (1:ℤ) else 0) = 1 := by
    rw [Finset.sum_ite_eq' (range (N + 1)) 0 (fun _ => (1:ℤ))]
    rw [if_pos (by simp)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hS, hC, hE]

/-- Step 4: closed form of `a_gen (-1) N` for `N ≥ 1`. -/
lemma aneg1 (N : ℕ) (hN : 1 ≤ N) :
    a_gen (-1) N = 3 * Sfun N 0 - 2 ^ N := by
  rw [step1 N hN, step2 N hN, step3 N]; ring

/-- Period-6 for the closed form (all `N`). -/
lemma gper (N : ℕ) :
    3 * Sfun (N + 6) 0 - 2 ^ (N + 6) = 3 * Sfun N 0 - 2 ^ N := by
  have h1 := Sshift3 N 0
  have h2 := Sshift3 (N + 3) 0
  have e : N + 3 + 3 = N + 6 := by ring
  rw [e] at h2
  have p6 : (2:ℤ) ^ (N + 6) = 64 * 2 ^ N := by rw [pow_add]; ring
  have p3 : (2:ℤ) ^ (N + 3) = 8 * 2 ^ N := by rw [pow_add]; ring
  rw [h2, h1, p6, p3]; ring

/-- Explicit residue function. -/
def Gr (i : ℕ) : ℤ :=
  if i = 0 then 2 else if i = 1 then 1 else if i = 2 then -1
  else if i = 3 then -2 else if i = 4 then -1 else if i = 5 then 1 else 0

lemma gval : ∀ N : ℕ, 3 * Sfun N 0 - 2 ^ N = Gr (N % 6) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N 6 with h | h
    · interval_cases N <;> (unfold Gr Sfun; decide)
    · have hlt : N - 6 < N := by omega
      have hmod : N % 6 = (N - 6) % 6 := by omega
      have hp := gper (N - 6)
      rw [show N - 6 + 6 = N from by omega] at hp
      rw [hmod, hp]
      exact ih (N - 6) hlt

/-- `a_gen (-1) N` depends only on `N % 6` for `N ≥ 1`. -/
lemma aneg1_mod (N : ℕ) (hN : 1 ≤ N) : a_gen (-1) N = Gr (N % 6) := by
  rw [aneg1 N hN, gval N]

theorem mneg1_conj (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    a_gen (-1) (n * p ^ k) ≡ a_gen (-1) (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  -- positivity of arguments
  have hppos : 0 < p := by omega
  have hx1 : 1 ≤ n * p ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hy1 : 1 ≤ n * p ^ (k - 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- x = p * y
  have hxy : n * p ^ k = p * (n * p ^ (k - 1)) := by
    have : p ^ k = p * p ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 from by omega]
      rw [pow_succ]; ring
    rw [this]; ring
  -- residue of p mod 6 is 1 or 5
  have hp2 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · omega
    · exact hodd
  have hp3 : ¬ (3 ∣ p) := not_three_dvd_prime p hp hp5
  have hp3' : p % 3 ≠ 0 := by
    intro h; exact hp3 (Nat.dvd_of_mod_eq_zero h)
  have hp6 : p % 6 = 1 ∨ p % 6 = 5 := by omega
  set y := n * p ^ (k - 1) with hydef
  -- reduce to equality of Gr values
  have hxmod : (n * p ^ k) % 6 = (p % 6 * (y % 6)) % 6 := by
    rw [hxy, Nat.mul_mod]
  have key : a_gen (-1) (n * p ^ k) = a_gen (-1) y := by
    rw [aneg1_mod _ hx1, aneg1_mod _ hy1]
    rw [hxmod]
    rcases hp6 with h1 | h5
    · rw [h1, one_mul]; congr 1; omega
    · rw [h5]
      -- finite check over y % 6
      have hylt : y % 6 < 6 := Nat.mod_lt _ (by norm_num)
      set m := y % 6 with hm
      interval_cases m <;> decide
  rw [key]

end Mneg1

section Final
open Nat Finset BigOperators Int

theorem oeis_333096_supercongruence_conjecture (m : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    a_gen m (n * p ^ k) ≡ a_gen m (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  rcases eq_or_ne m (-1) with hm | hm
  · subst hm; exact mneg1_conj p hp hp5 n k hn hk
  · exact reduce_conj m hm p hp hp5 n k hn hk

end Final


