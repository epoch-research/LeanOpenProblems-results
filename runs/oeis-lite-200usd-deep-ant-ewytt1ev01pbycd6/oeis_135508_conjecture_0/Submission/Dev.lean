import FormalConjectures.Util.ProblemImports

open Nat

/-- Same definition as in Spec.lean. -/
def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

/-- The defining recurrence, valid for all `n ≥ 1`. -/
theorem x_seq_succ (n : ℕ) (hn : 1 ≤ n) :
    x_seq (n + 1) = 2 * x_seq n + Nat.lcm (x_seq n) (n + 1) := by
  cases n with
  | zero => omega
  | succ m => rfl

/-- `x_seq n` is positive for `n ≥ 1`. -/
theorem x_seq_pos : ∀ n, 1 ≤ n → 0 < x_seq n := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hn with h | h
    · -- m + 1 = 1, i.e. n = 1
      simp only [← h]
      decide
    · -- m ≥ 1
      have hm : 1 ≤ m := by omega
      have := ih hm
      rw [x_seq_succ m hm]
      have : 0 < 2 * x_seq m := by omega
      omega

/-- `x_seq n ∣ x_seq (n+1)` for `n ≥ 1`. -/
theorem x_seq_dvd_succ (n : ℕ) (hn : 1 ≤ n) : x_seq n ∣ x_seq (n + 1) := by
  rw [x_seq_succ n hn]
  have h1 : x_seq n ∣ 2 * x_seq n := Dvd.intro_left 2 rfl
  have h2 : x_seq n ∣ Nat.lcm (x_seq n) (n + 1) := Nat.dvd_lcm_left _ _
  exact Nat.dvd_add h1 h2

/-- For positive `x`, `lcm x m = x * (m / gcd x m)`. -/
theorem lcm_eq_mul_div_gcd (x m : ℕ) (hx : 0 < x) :
    Nat.lcm x m = x * (m / Nat.gcd x m) := by
  have hg : 0 < Nat.gcd x m := Nat.gcd_pos_of_pos_left m hx
  have hgm : Nat.gcd x m ∣ m := Nat.gcd_dvd_right x m
  -- gcd * lcm = x * m
  have key : Nat.gcd x m * Nat.lcm x m = x * m := Nat.gcd_mul_lcm x m
  -- multiply target by gcd and compare
  apply Nat.eq_of_mul_eq_mul_left hg
  calc Nat.gcd x m * Nat.lcm x m = x * m := key
    _ = x * (Nat.gcd x m * (m / Nat.gcd x m)) := by
          rw [Nat.mul_div_cancel' hgm]
    _ = Nat.gcd x m * (x * (m / Nat.gcd x m)) := by ring

/-- The multiplicative ratio: `x_seq (n+1) = x_seq n * (2 + (n+1)/gcd(x_seq n, n+1))`. -/
theorem x_seq_ratio (n : ℕ) (hn : 1 ≤ n) :
    x_seq (n + 1) = x_seq n * (2 + (n + 1) / Nat.gcd (x_seq n) (n + 1)) := by
  have hx : 0 < x_seq n := x_seq_pos n hn
  rw [x_seq_succ n hn, lcm_eq_mul_div_gcd (x_seq n) (n + 1) hx]
  ring

/-- Same definition as in Spec.lean. -/
def A135508 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let x_n_plus_1 := x_seq (n + 1)
    let x_n := x_seq n
    (x_n_plus_1 / x_n) - 2

/-- The closed form `A135508 n = (n+1) / gcd (x_seq n) (n+1)` for `n ≥ 1`. -/
theorem A135508_eq (n : ℕ) (hn : 1 ≤ n) :
    A135508 n = (n + 1) / Nat.gcd (x_seq n) (n + 1) := by
  have hx : 0 < x_seq n := x_seq_pos n hn
  have hne : n ≠ 0 := by omega
  have hr : x_seq (n + 1) / x_seq n = 2 + (n + 1) / Nat.gcd (x_seq n) (n + 1) := by
    rw [x_seq_ratio n hn, Nat.mul_div_cancel_left _ hx]
  simp only [A135508, hne, if_false]
  rw [hr, Nat.add_sub_cancel_left]

/-- **Reduction lemma** (fully proved): for a prime `p`, the conjecture's conclusion
`A135508 (p-1) = p` is equivalent to `p ∤ x_seq (p-1)`. Here is the forward-useful direction. -/
theorem A135508_pred_eq_iff (p : ℕ) (hp : p.Prime) :
    A135508 (p - 1) = p ↔ ¬ p ∣ x_seq (p - 1) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : 1 ≤ p - 1 := by omega
  have hpp : 1 ≤ p := by omega
  rw [A135508_eq (p - 1) hp1, Nat.sub_add_cancel hpp]
  constructor
  · -- if p / gcd = p then p ∤ x_seq (p-1)
    intro h hdvd
    -- p ∣ x_seq (p-1) ⇒ gcd (x_seq (p-1)) p = p ⇒ p / p = 1 ≠ p
    have hg : Nat.gcd (x_seq (p - 1)) p = p := Nat.gcd_eq_right hdvd
    rw [hg, Nat.div_self (by omega)] at h
    omega
  · -- if p ∤ x_seq (p-1) then gcd = 1 and p / 1 = p
    intro hdvd
    have hcop : Nat.Coprime p (x_seq (p - 1)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd
    have hg : Nat.gcd (x_seq (p - 1)) p = 1 := by
      rw [Nat.gcd_comm]; exact hcop
    rw [hg, Nat.div_one]

/-- The two trivial base cases are provable directly. -/
example : ¬ (2 : ℕ) ∣ x_seq (2 - 1) := by decide
example : ¬ (3 : ℕ) ∣ x_seq (3 - 1) := by decide

/-- The step multiplier `M(n+1) = 2 + (n+1)/gcd(x_seq n, n+1)` is bounded by `n + 3`
and is at least `2`. -/
theorem mult_bounds (n : ℕ) :
    2 ≤ 2 + (n + 1) / Nat.gcd (x_seq n) (n + 1) ∧
    2 + (n + 1) / Nat.gcd (x_seq n) (n + 1) ≤ n + 3 := by
  constructor
  · exact Nat.le_add_right 2 _
  · have : (n + 1) / Nat.gcd (x_seq n) (n + 1) ≤ n + 1 := Nat.div_le_self _ _
    omega

/-- **Lemma A**: a prime `p` divides none of the early terms `x_seq n` for `1 ≤ n ≤ p - 3`. -/
theorem prime_not_dvd_early (p : ℕ) (hp : p.Prime) :
    ∀ n, 1 ≤ n → n ≤ p - 3 → ¬ p ∣ x_seq n := by
  have hp2 : 2 ≤ p := hp.two_le
  intro n
  induction n with
  | zero => omega
  | succ m ih =>
    intro _ hub
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- m = 0, so n = 1, x_seq 1 = 1
      subst hm0
      have h1 : x_seq (0 + 1) = 1 := rfl
      rw [h1, Nat.dvd_one]
      exact hp.ne_one
    · -- m ≥ 1
      have hm1 : 1 ≤ m := hmpos
      have hmub : m ≤ p - 3 := by omega
      have ihm : ¬ p ∣ x_seq m := ih hm1 hmub
      -- x_seq (m+1) = x_seq m * mult
      rw [x_seq_ratio m hm1]
      intro hdvd
      -- p prime divides product ⇒ divides a factor
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
      · exact ihm h
      · -- p ∣ mult, but 0 < mult < p
        have hb := mult_bounds m
        have hlt : 2 + (m + 1) / Nat.gcd (x_seq m) (m + 1) < p := by omega
        have hpos : 0 < 2 + (m + 1) / Nat.gcd (x_seq m) (m + 1) := by omega
        exact Nat.not_dvd_of_pos_of_lt hpos hlt h

/-- Helper: if a prime `p` divides `m` with `0 < m < 2*p`, then `m = p`. -/
theorem prime_dvd_eq (p m : ℕ) (hp : p.Prime) (hm0 : m ≠ 0) (hlt : m < 2 * p)
    (hd : p ∣ m) : m = p :=
  Nat.eq_of_dvd_of_lt_two_mul hm0 hd hlt

/-- **Lemma B** (in the form `p = a+3`): for prime `p = a+3` with `a ≥ 2`,
`p ∣ x_seq (a+2) ↔ gcd (x_seq a) (a+1) = 1`. Here `a+2 = p-1`, `a+1 = p-2`, `a = p-3`. -/
theorem dvd_iff_gcd (a : ℕ) (ha : 2 ≤ a) (hp : (a + 3).Prime) :
    (a + 3) ∣ x_seq (a + 2) ↔ Nat.gcd (x_seq a) (a + 1) = 1 := by
  set p := a + 3 with hpdef
  have hp5 : 5 ≤ p := by omega
  -- the two ratio expansions
  have e1 : x_seq (a + 2) =
      x_seq (a + 1) * (2 + (a + 2) / Nat.gcd (x_seq (a + 1)) (a + 2)) := by
    have := x_seq_ratio (a + 1) (by omega)
    simpa using this
  have e2 : x_seq (a + 1) =
      x_seq a * (2 + (a + 1) / Nat.gcd (x_seq a) (a + 1)) := by
    have := x_seq_ratio a (by omega)
    simpa using this
  -- p does not divide x_seq a
  have hA : ¬ p ∣ x_seq a := by
    have := prime_not_dvd_early p hp a (by omega) (by omega)
    simpa using this
  -- set the two gcds / multipliers
  set g1 := Nat.gcd (x_seq (a + 1)) (a + 2) with hg1
  set g2 := Nat.gcd (x_seq a) (a + 1) with hg2
  have hg1dvd : g1 ∣ (a + 2) := Nat.gcd_dvd_right _ _
  have hg2dvd : g2 ∣ (a + 1) := Nat.gcd_dvd_right _ _
  have hg1pos : 0 < g1 := Nat.gcd_pos_of_pos_right _ (by omega)
  have hg2pos : 0 < g2 := Nat.gcd_pos_of_pos_right _ (by omega)
  -- multiplier M1 = 2 + (a+2)/g1 is not divisible by p
  have hM1 : ¬ p ∣ (2 + (a + 2) / g1) := by
    intro hd
    have hle : (a + 2) / g1 ≤ a + 2 := Nat.div_le_self _ _
    have hcancel : g1 * ((a + 2) / g1) = a + 2 := Nat.mul_div_cancel' hg1dvd
    -- abstract the division term as an opaque variable so omega does not choke
    set D := (a + 2) / g1 with hD
    clear_value D
    clear hD e1 e2 hg1dvd hg2dvd
    -- hd : p ∣ 2 + D, hle : D ≤ a+2, hcancel : g1 * D = a+2
    have hM1ne : 2 + D ≠ 0 := by omega
    have hM1lt : 2 + D < 2 * p := by omega
    have hM1eqp : 2 + D = p := prime_dvd_eq p _ hp hM1ne hM1lt hd
    have hdiv : D = a + 1 := by omega
    rw [hdiv] at hcancel
    -- hcancel : g1 * (a+1) = a+2 ; contradiction
    rcases Nat.lt_or_ge g1 2 with h | h
    · have hg11 : g1 = 1 := by omega
      rw [hg11] at hcancel; omega
    · have hb : 2 * (a + 1) ≤ g1 * (a + 1) := by gcongr
      omega
  -- multiplier M2 = 2 + (a+1)/g2 : p ∣ M2 ↔ g2 = 1
  have hM2 : p ∣ (2 + (a + 1) / g2) ↔ g2 = 1 := by
    constructor
    · intro hd
      have hle : (a + 1) / g2 ≤ a + 1 := Nat.div_le_self _ _
      have hcancel : g2 * ((a + 1) / g2) = a + 1 := Nat.mul_div_cancel' hg2dvd
      set D := (a + 1) / g2 with hD
      clear_value D
      clear hD e1 e2 hg1dvd hg2dvd
      -- hd : p ∣ 2 + D, hle : D ≤ a+1, hcancel : g2 * D = a+1
      have hM2ne : 2 + D ≠ 0 := by omega
      have hM2lt : 2 + D < 2 * p := by omega
      have hM2eqp : 2 + D = p := prime_dvd_eq p _ hp hM2ne hM2lt hd
      have hdiv : D = a + 1 := by omega
      rw [hdiv] at hcancel
      -- hcancel : g2 * (a+1) = a+1 ; with a+1 > 0 forces g2 = 1
      rcases Nat.lt_or_ge g2 2 with h | h
      · omega
      · have hb : 2 * (a + 1) ≤ g2 * (a + 1) := by gcongr
        omega
    · intro hg
      have hpeq : (2 + (a + 1) / g2) = p := by rw [hg, Nat.div_one]; omega
      rw [hpeq]  -- goal: p ∣ p
  -- assemble the equivalence
  rw [e1, Nat.Prime.dvd_mul hp, e2, Nat.Prime.dvd_mul hp]
  simp only [hA, hM1, or_false, false_or]
  exact hM2

-- Axiom check: the reduction uses only the permitted axioms.
#print axioms A135508_pred_eq_iff
#print axioms A135508_eq
#print axioms dvd_iff_gcd
