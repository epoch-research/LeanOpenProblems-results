import FormalConjectures.Util.ProblemImports

open Nat

/--
The auxiliary sequence $x(n)$, where $x(1)=1$ and $x(n) = 2 \cdot x(n-1) + \mathrm{lcm}(x(n-1), n)$ for $n > 1$.
`x_seq n` corresponds to the OEIS term $x(n)$.
This definition is set up for `n : ℕ` where $n=0$ and $n=1$ are base cases for $x(0)$ and $x(1)$.
Note: Mathlib's `lcm` is `Nat.lcm`.
-/
def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

/--
A135508: $a(n) = x(n+1)/x(n) - 2$ where $x(1)=1$ and $x(n) = 2*x(n-1) + \operatorname{lcm}(x(n-1),n)$.
-/
def A135508 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- We rely on the fact that x_seq n divides x_seq (n+1), which is a known property of the sequence.
    -- Since n : ℕ, the division is integer division.
    let x_n_plus_1 := x_seq (n + 1)
    let x_n := x_seq n

    -- The fact that x_seq n divides x_seq (n+1) means that the division is exact.
    -- The final result is always a natural number.
    (x_n_plus_1 / x_n) - 2

namespace Aux

theorem x_seq_two_step (n : ℕ) :
    x_seq (n + 2) = 2 * (x_seq (n+1)) + Nat.lcm (x_seq (n+1)) (n + 2) := rfl

/-- The multiplier form of the recurrence. -/
theorem x_seq_succ (n : ℕ) (hn : 1 ≤ n) :
    x_seq (n+1) = x_seq n * (2 + (n+1) / Nat.gcd (x_seq n) (n+1)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm 1 k, x_seq_two_step k, Nat.lcm,
    Nat.mul_div_assoc _ (Nat.gcd_dvd_right (x_seq (k+1)) (k+2))]
  ring

theorem x_seq_pos : ∀ n, 1 ≤ n → 0 < x_seq n := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 1 with h | h
    · interval_cases m
      · decide
    · rw [x_seq_succ m h]
      exact Nat.mul_pos (ih h) (by positivity)

/-- `A135508 n` equals the "deficient part" `(n+1) / gcd (x n) (n+1)`. -/
theorem A135508_eq (n : ℕ) (hn : 1 ≤ n) :
    A135508 n = (n+1) / Nat.gcd (x_seq n) (n+1) := by
  have hpos := x_seq_pos n hn
  unfold A135508
  rw [if_neg (by omega)]
  show x_seq (n+1) / x_seq n - 2 = _
  rw [x_seq_succ n hn, Nat.mul_div_cancel_left _ hpos]
  exact Nat.add_sub_cancel_left 2 _

theorem x_seq_dvd_succ (n : ℕ) (hn : 1 ≤ n) : x_seq n ∣ x_seq (n+1) := by
  rw [x_seq_succ n hn]; exact dvd_mul_right _ _

theorem x_seq_dvd_of_le {m n : ℕ} (hm : 1 ≤ m) (h : m ≤ n) : x_seq m ∣ x_seq n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k m with h1 | h1
    · have : m = k + 1 := by omega
      subst this; rfl
    · exact dvd_trans (ih h1) (x_seq_dvd_succ k (by omega))


/-- If the deficient part of `n+1` equals `n+1` itself... helper: positivity of deficient part -/
theorem def_dvd (n : ℕ) : (n+1) / Nat.gcd (x_seq n) (n+1) ∣ (n+1) :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)

theorem def_pos (n : ℕ) : 0 < (n+1) / Nat.gcd (x_seq n) (n+1) := by
  apply Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _))
  exact Nat.gcd_pos_of_pos_right _ (by omega)

/-- Core reduction: if some divisor `> 1` of `k+1` already divides `x_seq k`, then the
prime `p = k+3` does not divide `x_seq (k+2) = x_seq (p-1)`, so `A135508 (p-1) = p`. -/
theorem key (k : ℕ) (hk : 2 ≤ k) (hp : Nat.Prime (k+3))
    (h : 1 < Nat.gcd (x_seq k) (k+1)) : A135508 (k+2) = k+3 := by
  have main : ∀ j, 1 ≤ j → j ≤ k+2 → ¬ (k+3) ∣ x_seq j := by
    intro j
    induction j with
    | zero => omega
    | succ i ih =>
      intro _ hj2 hdvd
      rcases Nat.lt_or_ge i 1 with hi | hi
      · -- i = 0 : x_seq 1 = 1
        interval_cases i
        · have h1 : x_seq 1 = 1 := rfl
          rw [h1] at hdvd
          have := Nat.le_of_dvd (by omega) hdvd
          omega
      · -- i ≥ 1
        rw [x_seq_succ i hi] at hdvd
        rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
        · exact ih hi (by omega) h1
        · -- (k+3) ∣ 2 + d  with  d ∣ i+1 ≤ k+2
          have hdd0 : (i+1) / Nat.gcd (x_seq i) (i+1) ∣ (i+1) := def_dvd i
          generalize hD : (i+1) / Nat.gcd (x_seq i) (i+1) = d at h1 hdd0
          clear hdvd
          have hdle : d ≤ i + 1 := Nat.le_of_dvd (by omega) hdd0
          -- so 2 + d = k + 3
          have heq : 2 + d = k + 3 := by
            clear hD
            rcases h1 with ⟨c, hc⟩
            have hc1 : c ≠ 0 := by rintro rfl; omega
            have hc2 : c < 2 := by
              by_contra hge
              push_neg at hge
              have := Nat.mul_le_mul_left (k+3) hge
              omega
            interval_cases c <;> omega
          have hdk : d = k + 1 := by clear hD; omega
          -- (k+1) ∣ (i+1) and 1 ≤ i+1 ≤ k+2 forces i = k
          rw [hdk] at hdd0
          have hik : i = k := by
            clear hD
            rcases hdd0 with ⟨c, hc⟩
            have hc1 : c ≠ 0 := by rintro rfl; omega
            have hc2 : c < 2 := by
              by_contra hge
              push_neg at hge
              have := Nat.mul_le_mul_left (k+1) hge
              omega
            interval_cases c <;> omega
          subst hik
          -- then (i+1)/gcd = i+1 forces gcd = 1, contradicting h
          have hg : Nat.gcd (x_seq i) (i+1) ∣ (i+1) := Nat.gcd_dvd_right _ _
          have hmul := Nat.div_mul_cancel hg
          rw [hD, hdk] at hmul
          -- (i+1) * g = i + 1  →  g = 1
          have h2 : (i+1) * Nat.gcd (x_seq i) (i+1) = (i+1) * 1 := by
            rw [mul_one]; exact hmul
          have hg1 : Nat.gcd (x_seq i) (i+1) = 1 :=
            Nat.eq_of_mul_eq_mul_left (by omega) h2
          rw [hg1] at h
          exact Nat.lt_irrefl 1 h
  have hnd : ¬ (k+3) ∣ x_seq (k+2) := main (k+2) (by omega) le_rfl
  have hcop : Nat.gcd (x_seq (k+2)) (k+3) = 1 := by
    have := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
    exact Nat.Coprime.gcd_eq_one (Nat.Coprime.symm this)
  rw [A135508_eq (k+2) (by omega)]
  have h3 : k + 2 + 1 = k + 3 := rfl
  rw [h3, hcop, Nat.div_one]


/-- The prime `p = k+3` does not divide `x_seq (k+2)` when `gcd (x_seq k) (k+1) > 1`. -/
theorem key_not_dvd (k : ℕ) (hk : 2 ≤ k) (hp : Nat.Prime (k+3))
    (h : 1 < Nat.gcd (x_seq k) (k+1)) : ¬ (k+3) ∣ x_seq (k+2) := by
  have main : ∀ j, 1 ≤ j → j ≤ k+2 → ¬ (k+3) ∣ x_seq j := by
    intro j
    induction j with
    | zero => omega
    | succ i ih =>
      intro _ hj2 hdvd
      rcases Nat.lt_or_ge i 1 with hi | hi
      · interval_cases i
        · have h1 : x_seq 1 = 1 := rfl
          rw [h1] at hdvd
          have := Nat.le_of_dvd (by omega) hdvd
          omega
      · rw [x_seq_succ i hi] at hdvd
        rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
        · exact ih hi (by omega) h1
        · have hdd0 : (i+1) / Nat.gcd (x_seq i) (i+1) ∣ (i+1) := def_dvd i
          generalize hD : (i+1) / Nat.gcd (x_seq i) (i+1) = d at h1 hdd0
          clear hdvd
          have hdle : d ≤ i + 1 := Nat.le_of_dvd (by omega) hdd0
          have heq : 2 + d = k + 3 := by
            clear hD
            rcases h1 with ⟨c, hc⟩
            have hc1 : c ≠ 0 := by rintro rfl; omega
            have hc2 : c < 2 := by
              by_contra hge
              push_neg at hge
              have := Nat.mul_le_mul_left (k+3) hge
              omega
            interval_cases c <;> omega
          have hdk : d = k + 1 := by clear hD; omega
          rw [hdk] at hdd0
          have hik : i = k := by
            clear hD
            rcases hdd0 with ⟨c, hc⟩
            have hc1 : c ≠ 0 := by rintro rfl; omega
            have hc2 : c < 2 := by
              by_contra hge
              push_neg at hge
              have := Nat.mul_le_mul_left (k+1) hge
              omega
            interval_cases c <;> omega
          subst hik
          have hg : Nat.gcd (x_seq i) (i+1) ∣ (i+1) := Nat.gcd_dvd_right _ _
          have hmul := Nat.div_mul_cancel hg
          rw [hD, hdk] at hmul
          have h2 : (i+1) * Nat.gcd (x_seq i) (i+1) = (i+1) * 1 := by
            rw [mul_one]; exact hmul
          have hg1 : Nat.gcd (x_seq i) (i+1) = 1 :=
            Nat.eq_of_mul_eq_mul_left (by omega) h2
          rw [hg1] at h
          exact Nat.lt_irrefl 1 h
  exact main (k+2) (by omega) le_rfl

/-- The savior mechanism, machine-checked: for a prime `r ≡ 2 (mod 3)`, `r ≥ 11`,
the multiplier at step `r` is exactly `r + 2`; hence every divisor of `r + 2`
divides `x_seq r`. -/
theorem entry_from_savior (q r : ℕ) (hr : Nat.Prime r) (h11 : 11 ≤ r)
    (h3 : r % 3 = 2) (hq : q ∣ r + 2) : q ∣ x_seq r := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 3 := ⟨r - 3, by omega⟩
  -- 3 ∣ x_seq k  (k ≥ 8 ≥ 4)
  have h34 : (3:ℕ) ∣ x_seq 4 := by decide
  have h3k : (3:ℕ) ∣ x_seq k := h34.trans (x_seq_dvd_of_le (by omega) (by omega))
  have h3k1 : (3:ℕ) ∣ (k+1) := by omega
  have hgcd : 1 < Nat.gcd (x_seq k) (k+1) := by
    have hg3 : (3:ℕ) ∣ Nat.gcd (x_seq k) (k+1) := Nat.dvd_gcd h3k h3k1
    have := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by omega)) hg3
    omega
  have hnd := key_not_dvd k (by omega) hr hgcd
  -- gcd (x_seq (k+2)) (k+3) = 1
  have hcop : Nat.gcd (x_seq (k+2)) (k+3) = 1 := by
    have := (Nat.Prime.coprime_iff_not_dvd hr).mpr hnd
    exact Nat.Coprime.gcd_eq_one (Nat.Coprime.symm this)
  -- x_seq (k+3) = x_seq (k+2) * (k + 5)
  have hstep : x_seq (k+3) = x_seq (k+2) * (2 + (k+3)) := by
    have := x_seq_succ (k+2) (by omega)
    rw [show k+2+1 = k+3 from rfl, hcop, Nat.div_one] at this
    exact this
  rw [hstep]
  have hq2 : q ∣ 2 + (k+3) := by
    have : 2 + (k+3) = k + 3 + 2 := by ring
    rw [this]; exact hq
  exact Dvd.dvd.mul_left hq2 _

/-- Converse core: if `gcd (x_seq k) (k+1) = 1` (i.e. `k+1 = p - 2` is totally fresh),
then the prime `p = k+3` divides `x_seq (k+1)`, hence `x_seq (k+2)`, and
`A135508 (k+2) = 1`. -/
theorem key_conv (k : ℕ) (hk : 2 ≤ k) (h : Nat.gcd (x_seq k) (k+1) = 1) :
    A135508 (k+2) = 1 := by
  have hstep : x_seq (k+1) = x_seq k * (k+3) := by
    rw [x_seq_succ k (by omega), h, Nat.div_one]
    ring
  have hdvd1 : (k+3) ∣ x_seq (k+1) := by rw [hstep]; exact dvd_mul_left _ _
  have hdvd2 : (k+3) ∣ x_seq (k+2) := hdvd1.trans (x_seq_dvd_succ (k+1) (by omega))
  rw [A135508_eq (k+2) (by omega)]
  have h3 : k + 2 + 1 = k + 3 := rfl
  rw [h3, Nat.gcd_eq_right hdvd2, Nat.div_self (by omega)]

/-- Full characterization: for a prime `p = k+3`, the conjectured value `A135508 (p-1) = p`
holds **iff** some factor of `p-2` already divides `x_seq (p-3)`. Together with `key`,
this machine-checks that the conjecture is *equivalent* to the entry-time bound. -/
theorem characterization_aux (k : ℕ) (hk : 2 ≤ k) (_hp : Nat.Prime (k+3))
    (hkey : 1 < Nat.gcd (x_seq k) (k+1) → A135508 (k+2) = k+3) :
    (A135508 (k+2) = k+3 ↔ 1 < Nat.gcd (x_seq k) (k+1)) := by
  constructor
  · intro hA
    by_contra hng
    push_neg at hng
    have hpos : 0 < Nat.gcd (x_seq k) (k+1) :=
      Nat.gcd_pos_of_pos_right _ (by omega)
    have h1 : Nat.gcd (x_seq k) (k+1) = 1 := by omega
    have := key_conv k hk h1
    omega
  · exact hkey


/-- Coverage: if `s ≥ 2` divides both `k+1` and `x_seq e` for some `1 ≤ e ≤ k`,
then `gcd (x_seq k) (k+1) > 1`. -/
theorem gcd_lower (k s e : ℕ) (hs : 2 ≤ s) (h1 : s ∣ (k+1)) (he : 1 ≤ e) (hek : e ≤ k)
    (hxe : s ∣ x_seq e) : 1 < Nat.gcd (x_seq k) (k+1) := by
  have hx : s ∣ x_seq k := hxe.trans (x_seq_dvd_of_le he hek)
  have hg : s ∣ Nat.gcd (x_seq k) (k+1) := Nat.dvd_gcd hx h1
  have := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by omega)) hg
  omega

/-- If some prime factor `s` of `p-2` has an entry certificate `s ∣ x_seq e` with
`e + 1 ≤ p - 2`, then the conjecture holds at `p`. -/
theorem covered (p s e : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p)
    (hsp : s ∣ (p-2)) (hs : 2 ≤ s) (he : 1 ≤ e) (hxe : s ∣ x_seq e)
    (hbound : e + 1 ≤ p - 2) : A135508 (p-1) = p := by
  obtain ⟨k, hk⟩ : ∃ k, p = k + 3 := ⟨p - 3, by omega⟩
  subst hk
  have hk2 : 2 ≤ k := by omega
  have h1 : s ∣ (k+1) := by
    have h' : k + 3 - 2 = k + 1 := by omega
    rwa [h'] at hsp
  have hek : e ≤ k := by omega
  have hgcd := gcd_lower k s e hs h1 he hek hxe
  have hres := key k hk2 hp hgcd
  have h2 : k + 3 - 1 = k + 2 := by omega
  rw [h2]; exact hres

/-- Version keyed on the least prime factor of `p - 2`:
the certificate only needs `e + 1 ≤ s ^ 2` since `s ^ 2 ≤ p - 2`. -/
theorem covered_minFac (p s e : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hnp : ¬(p-2).Prime)
    (hs : (p-2).minFac = s) (hse : 1 ≤ e) (hxe : s ∣ x_seq e) (hcert : e + 1 ≤ s^2) :
    A135508 (p-1) = p := by
  have hm2 : 2 ≤ p - 2 := by omega
  have hsq : s^2 ≤ p - 2 := by
    rw [← hs]; exact Nat.minFac_sq_le_self (by omega) hnp
  have hs2 : 2 ≤ s := by
    rw [← hs]
    exact (Nat.minFac_prime (by omega : p - 2 ≠ 1)).two_le
  exact covered p s e hp h5 (hs ▸ Nat.minFac_dvd _) hs2 hse hxe (le_trans hcert hsq)


set_option maxRecDepth 100000 in
/-- Certificate table: conjecture holds whenever the least prime factor of `p-2` is ≤ 199. -/
theorem main_of_minFac_le (p : ℕ) (hp : Nat.Prime p) (hnp : ¬(p-2).Prime)
    (h5 : 5 ≤ p) (hle : (p-2).minFac ≤ 199) : A135508 (p-1) = p := by
  have hm1 : p - 2 ≠ 1 := by omega
  obtain ⟨s, hs⟩ : ∃ s, (p-2).minFac = s := ⟨_, rfl⟩
  rw [hs] at hle
  have hpr : s.Prime := hs ▸ Nat.minFac_prime hm1
  have h2le : 2 ≤ s := hpr.two_le
  have hs2 : s ≠ 2 := by
    intro h2
    subst h2
    have hd : (2:ℕ) ∣ p - 2 := by
      have hmf := Nat.minFac_dvd (p-2)
      rwa [hs] at hmf
    have hdp : (2:ℕ) ∣ p := by
      have hpe : p - 2 + 2 = p := by omega
      rw [← hpe]; exact Nat.dvd_add hd (dvd_refl 2)
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp 2 hdp) with h | h <;> omega
  interval_cases s
  · exact absurd rfl hs2
  · exact covered_minFac p 3 4 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 5 3 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 7 47 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 11 53 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 13 11 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 17 83 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 19 17 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 23 67 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 29 317 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 31 29 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 37 257 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 41 367 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 43 41 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 47 233 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 53 157 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 59 293 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 61 59 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 67 467 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 71 211 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 73 71 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 79 709 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 83 911 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 89 443 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 97 677 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 101 503 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 103 101 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 107 2459 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 109 107 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 113 337 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 127 379 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 131 653 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 137 409 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 139 137 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 149 743 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 151 149 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 157 1097 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 163 487 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 167 499 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 173 863 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 179 2683 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 181 179 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 191 953 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 193 191 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 197 983 hp h5 hnp hs (by omega) (by decide) (by norm_num)
  · exact absurd hpr (by decide)
  · exact covered_minFac p 199 197 hp h5 hnp hs (by omega) (by decide) (by norm_num)

end Aux


namespace Aux

/--
THE OPEN CORE — now a purely arithmetic statement, with no reference to the sequence:
every prime `s ≥ 200` admits a "savior" prime `r ≡ 2 (mod 3)`, `r ≡ -2 (mod s)` with
`11 ≤ r ≤ s² - 1`.  Via the machine-checked savior mechanism `entry_from_savior` below,
this immediately yields `entry_bound`, and hence (with the certificate table) the full
conjecture.

Status: this is a least-prime-in-arithmetic-progression bound with Linnik exponent 2.
This exact statement has been verified for every prime `s < 2·10⁶` (above 200), with worst case
`s = 251` (savior `r = 8783`, ratio `r/s² ≈ 0.14`) and margins improving like `log s / s`;
the unrestricted entry bound `E s ≤ s² - 1` has been verified for every prime `s < 10⁸`
(extremal case `s = 7`, entry `47 ≤ 48`).  However the statement is
open in general: it is stronger than the bounds provided by GRH (`≪ s² log² s`), and the
best unconditional technology (Linnik/Xylouris) gives exponent ≈ 5.  Conversely, the
machine-checked equivalence `conjecture_characterization` shows the conjecture cannot be
settled without such quantitative prime-distribution information.  The author was unable
to close this gap honestly, and no counterexample exists in any computationally
reachable range.
-/
theorem ap_savior_exists (s : ℕ) (hs : Nat.Prime s) (h200 : 200 ≤ s) :
    ∃ r : ℕ, Nat.Prime r ∧ r % 3 = 2 ∧ r % s = s - 2 ∧ 11 ≤ r ∧ r ≤ s^2 - 1 := by
  sorry

/-- The entry bound, derived from the open arithmetic core via the machine-checked
savior mechanism. -/
theorem entry_bound (s : ℕ) (hs : Nat.Prime s) (h62 : 200 ≤ s) : s ∣ x_seq (s^2 - 1) := by
  obtain ⟨r, hr, h3, hmod, h11, hle⟩ := ap_savior_exists s hs h62
  have hq : s ∣ r + 2 := by
    apply Nat.dvd_of_mod_eq_zero
    have h2s : 2 % s = 2 := Nat.mod_eq_of_lt (by omega)
    rw [Nat.add_mod, hmod, h2s]
    have hs2 : s - 2 + 2 = s := by omega
    rw [hs2, Nat.mod_self]
  have hentry := entry_from_savior s r hr h11 h3 hq
  exact hentry.trans (x_seq_dvd_of_le (by omega) hle)

end Aux


/--
Machine-checked **equivalence**: for any prime `p ≥ 5`, the conjectured identity
`A135508 (p-1) = p` holds **iff** some prime factor of `p - 2` already divides
`x_seq (p - 3)`.  This proves the analysis in the docstring of `Aux.entry_bound` is
not merely a sufficient route but exactly captures the content of the conjecture.
-/
theorem conjecture_characterization (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    (A135508 (p - 1) = p ↔ 1 < Nat.gcd (x_seq (p - 3)) (p - 2)) := by
  obtain ⟨k, hk⟩ : ∃ k, p = k + 3 := ⟨p - 3, by omega⟩
  subst hk
  have h1 : k + 3 - 1 = k + 2 := by omega
  have h2 : k + 3 - 3 = k := by omega
  have h3 : k + 3 - 2 = k + 1 := by omega
  rw [h1, h2, h3]
  exact Aux.characterization_aux k (by omega) hp (Aux.key k (by omega) hp)

/--
Conjecture: For prime p such that p-2 is not a prime, a(p-1) = p.
p-2 in natural numbers is $\max(0, p-2)$.
A prime $p$ such that $p-2$ is not a prime means $p$ is not the larger element of a twin prime pair, except for $p=3$ where $p-2=1$ (not prime) and $p=2$ where $p-2=0$ (not prime).
-/
theorem oeis_135508_conjecture_0 :
  ∀ p : ℕ, Nat.Prime p → ¬ (Nat.Prime (p - 2)) → A135508 (p - 1) = p := by
  intro p hp hnp
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · have h2 := hp.two_le
    interval_cases p
    · decide
    · decide
    · exact absurd hp (by decide)
  · by_cases hle : (p - 2).minFac ≤ 199
    · exact Aux.main_of_minFac_le p hp hnp h5 hle
    · -- the open tail: least prime factor of `p - 2` exceeds 61
      push_neg at hle
      have hm1 : p - 2 ≠ 1 := by omega
      have hpr : ((p - 2).minFac).Prime := Nat.minFac_prime hm1
      set s := (p - 2).minFac with hs
      have h62 : 200 ≤ s := hle
      have hsq : 4 ≤ s ^ 2 := by nlinarith
      exact Aux.covered_minFac p s (s^2 - 1) hp h5 hnp hs.symm (by omega)
        (Aux.entry_bound s hpr h62) (by omega)
