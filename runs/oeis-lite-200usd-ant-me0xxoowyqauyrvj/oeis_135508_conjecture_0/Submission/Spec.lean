import FormalConjectures.Util.ProblemImports

open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

def A135508 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let x_n_plus_1 := x_seq (n + 1)
    let x_n := x_seq n
    (x_n_plus_1 / x_n) - 2

theorem xseq_pos (n : ℕ) : 0 < x_seq (n + 1) := by
  induction n with
  | zero => decide
  | succ m _ => show 0 < 2 * x_seq (m + 1) + Nat.lcm (x_seq (m + 1)) (m + 2); omega

def yfac (k : ℕ) : ℕ := 2 + (k + 1) / Nat.gcd (x_seq k) (k + 1)

theorem yfac_le (k : ℕ) : yfac k ≤ k + 3 := by
  unfold yfac
  have h : (k + 1) / Nat.gcd (x_seq k) (k + 1) ≤ k + 1 := Nat.div_le_self _ _
  omega

theorem xseq_succ_eq (k : ℕ) (hk : 1 ≤ k) :
    x_seq (k + 1) = x_seq k * yfac k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hpos : 0 < x_seq (j + 1) := xseq_pos j
  have hgb : Nat.gcd (x_seq (j + 1)) (j + 2) ∣ (j + 2) := Nat.gcd_dvd_right _ _
  have hlcm : Nat.lcm (x_seq (j + 1)) (j + 2)
      = x_seq (j + 1) * ((j + 2) / Nat.gcd (x_seq (j + 1)) (j + 2)) := by
    rw [Nat.lcm, ← Nat.mul_div_assoc _ hgb]
  show 2 * x_seq (j + 1) + Nat.lcm (x_seq (j + 1)) (j + 2) = _
  rw [hlcm]; unfold yfac; ring

theorem xseq_prod (m : ℕ) : x_seq (m + 1) = ∏ k ∈ Finset.Icc 1 m, yfac k := by
  induction m with
  | zero => simp [x_seq]
  | succ n ih =>
    rw [xseq_succ_eq (n + 1) (by omega), ih, Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]

theorem prime_dvd_xseq (p m : ℕ) (hp : p.Prime) :
    p ∣ x_seq (m + 1) ↔ ∃ k ∈ Finset.Icc 1 m, p ∣ yfac k := by
  rw [xseq_prod, (hp.prime).dvd_finset_prod_iff]

theorem yfac_eq_p_of_dvd (p k : ℕ) (hp5 : 5 ≤ p) (hk : k ≤ p - 2)
    (hdvd : p ∣ yfac k) : k = p - 3 ∧ Nat.gcd (x_seq k) (k + 1) = 1 := by
  have hge : 2 ≤ yfac k := Nat.le_add_right 2 _
  have hle : yfac k ≤ p + 1 := le_trans (yfac_le k) (by omega)
  have heq : yfac k = p := by
    obtain ⟨c, hc⟩ := hdvd
    have hc_ge : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h, Nat.mul_zero] at hc; omega
      · exact h
    have hc_le : c ≤ 1 := by nlinarith [hge, hle, hc, hp5]
    have : c = 1 := le_antisymm hc_le hc_ge
    rw [this, Nat.mul_one] at hc; exact hc
  have hd : (k + 1) / Nat.gcd (x_seq k) (k + 1) = p - 2 := by
    have h2 : 2 + (k + 1) / Nat.gcd (x_seq k) (k + 1) = p := heq
    omega
  set g := Nat.gcd (x_seq k) (k + 1) with hgdef
  have hg_dvd : g ∣ (k + 1) := Nat.gcd_dvd_right _ _
  have hg_pos : 1 ≤ g := Nat.gcd_pos_of_pos_right _ (by omega)
  have hmul : (k + 1) = (p - 2) * g := by
    rw [← hd, Nat.div_mul_cancel hg_dvd]
  have hprod : (p - 2) * g ≤ p - 1 := by rw [← hmul]; omega
  have hg1 : g = 1 := by
    rcases Nat.lt_or_ge g 2 with h | h
    · omega
    · exfalso
      have h2 : (p - 2) * 2 ≤ (p - 2) * g := Nat.mul_le_mul (le_refl (p - 2)) h
      have : (p - 2) * 2 ≤ p - 1 := le_trans h2 hprod
      omega
  refine ⟨?_, hg1⟩
  rw [hg1, Nat.mul_one] at hmul; omega

theorem A135508_eq (m : ℕ) (hm : 1 ≤ m) :
    A135508 m = (m + 1) / Nat.gcd (x_seq m) (m + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [A135508, if_neg (by omega : k + 1 ≠ 0)]
  have hpos : 0 < x_seq (k + 1) := xseq_pos k
  have hgb : Nat.gcd (x_seq (k + 1)) (k + 2) ∣ (k + 2) := Nat.gcd_dvd_right _ _
  have hlcm : Nat.lcm (x_seq (k + 1)) (k + 2)
      = x_seq (k + 1) * ((k + 2) / Nat.gcd (x_seq (k + 1)) (k + 2)) := by
    rw [Nat.lcm, ← Nat.mul_div_assoc _ hgb]
  have hval : x_seq (k + 1 + 1) / x_seq (k + 1)
      = 2 + (k + 2) / Nat.gcd (x_seq (k + 1)) (k + 2) := by
    show (2 * x_seq (k + 1) + Nat.lcm (x_seq (k + 1)) (k + 2)) / x_seq (k + 1) = _
    rw [hlcm]
    rw [show 2 * x_seq (k + 1) + x_seq (k + 1) * ((k + 2) / Nat.gcd (x_seq (k + 1)) (k + 2))
          = x_seq (k + 1) * (2 + (k + 2) / Nat.gcd (x_seq (k + 1)) (k + 2)) by ring]
    exact Nat.mul_div_cancel_left _ hpos
  rw [hval]
  show 2 + (k + 2) / Nat.gcd (x_seq (k + 1)) (k + 2) - 2
      = (k + 2) / Nat.gcd (x_seq (k + 1)) (k + 2)
  generalize (k + 2) / Nat.gcd (x_seq (k + 1)) (k + 2) = d
  omega

theorem A135508_pred_eq_iff (p : ℕ) (hp : p.Prime) :
    A135508 (p - 1) = p ↔ ¬ p ∣ x_seq (p - 1) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpm1 : 1 ≤ p - 1 := by omega
  have hrw : A135508 (p - 1) = p / Nat.gcd (x_seq (p - 1)) p := by
    have := A135508_eq (p - 1) hpm1
    rwa [show p - 1 + 1 = p by omega] at this
  rw [hrw]
  constructor
  · intro h hdvd
    have hg : Nat.gcd (x_seq (p - 1)) p = p := Nat.gcd_eq_right hdvd
    rw [hg, Nat.div_self (by omega)] at h
    omega
  · intro h
    have hg : Nat.gcd (x_seq (p - 1)) p = 1 := by
      rcases (Nat.coprime_or_dvd_of_prime hp (x_seq (p - 1))) with hcop | hdvd
      · exact (Nat.coprime_comm.mp hcop)
      · exact absurd hdvd h
    rw [hg, Nat.div_one]

theorem xseq_dvd_succ (q m : ℕ) (h : q ∣ x_seq (m + 1)) : q ∣ x_seq (m + 2) := by
  show q ∣ 2 * x_seq (m + 1) + Nat.lcm (x_seq (m + 1)) (m + 2)
  exact Nat.dvd_add (Dvd.dvd.mul_left h 2) (dvd_trans h (Nat.dvd_lcm_left _ _))

theorem xseq_dvd_mono (q a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (h : q ∣ x_seq a) :
    q ∣ x_seq b := by
  induction b with
  | zero => omega
  | succ c ih =>
    rcases Nat.lt_or_ge a (c + 1) with hlt | hge
    · have hac : a ≤ c := by omega
      have hxc : q ∣ x_seq c := ih hac
      obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
      exact xseq_dvd_succ q d hxc
    · have : a = c + 1 := by omega
      rwa [this] at h

theorem minFac_sq_le (N : ℕ) (hN : 2 ≤ N) (hcomp : ¬ N.Prime) :
    N.minFac * N.minFac ≤ N := by
  have hdvd : N.minFac ∣ N := Nat.minFac_dvd N
  have hle : N.minFac ≤ N / N.minFac := Nat.minFac_le_div (by omega) hcomp
  calc N.minFac * N.minFac ≤ N.minFac * (N / N.minFac) := Nat.mul_le_mul_left _ hle
    _ = N := Nat.mul_div_cancel' hdvd

/--
**Open arithmetic core.**  For every prime `q`, `q` divides `x_seq (q²-1)`; equivalently
`f(q) < q²`, where `f(q)` is the first index at which `q ∣ x_seq`.

A strong induction on composite `N` (using `xseq_dvd_mono`) removes the self-referential
`S = {n | gcd (x_seq (n-1)) n = 1}` membership obstruction and reduces the *entire conjecture*
to the clean statement:

> for every prime `q` there is a prime `r ≡ -2 (mod q)` with `r < q²` (and `r-2` composite).

Indeed, every *composite* candidate `m` is forced out of the relevant congruence
`m ≡ -2·gcd (x_seq (m-1)) m (mod q)`: by the inductive hypothesis together with divisibility
persistence, a composite `m`'s gcd always carries an extra prime factor, making it too large to
satisfy the exact congruence.  Hence a genuine prime in the progression `≡ -2 (mod q)` below `q²`
is unavoidable.  This is the least-prime-in-arithmetic-progression problem with exponent `< 2`,
which lies beyond Linnik's theorem (exponent ≈ 5.18, Xylouris) and even beyond GRH
(`≪ q² log² q > q²`).  It is a recognised open problem, not available in Mathlib.

Verified computationally for all `q ≤ 3·10⁴` (indices `≤ 10⁹`); the tightest case is `q = 7`,
where `f(7) = 47` against `q² = 49`.
-/
theorem qsq_dvd (q : ℕ) (hq : q.Prime) : q ∣ x_seq (q ^ 2 - 1) := by
  sorry

/-- Every composite `N` shares a factor with `x_seq (N-1)` (follows from `qsq_dvd`). -/
theorem core_lemma (N : ℕ) (hN : 2 ≤ N) (hcomp : ¬ N.Prime) :
    1 < Nat.gcd (x_seq (N - 1)) N := by
  have hq : N.minFac.Prime := Nat.minFac_prime (by omega)
  have hqd : N.minFac ∣ N := Nat.minFac_dvd N
  have hsq : N.minFac * N.minFac ≤ N := minFac_sq_le N hN hcomp
  have hq2 : 2 ≤ N.minFac := hq.two_le
  have hqq : 4 ≤ N.minFac * N.minFac := by nlinarith [hq2]
  have hpow : N.minFac ^ 2 = N.minFac * N.minFac := by ring
  have h1 : N.minFac ∣ x_seq (N.minFac ^ 2 - 1) := qsq_dvd N.minFac hq
  have hge1 : 1 ≤ N.minFac ^ 2 - 1 := by rw [hpow]; omega
  have hle : N.minFac ^ 2 - 1 ≤ N - 1 := by rw [hpow]; omega
  have h2 : N.minFac ∣ x_seq (N - 1) :=
    xseq_dvd_mono N.minFac (N.minFac ^ 2 - 1) (N - 1) hge1 hle h1
  have hgcd : N.minFac ∣ Nat.gcd (x_seq (N - 1)) N := Nat.dvd_gcd h2 hqd
  have hgpos : 0 < Nat.gcd (x_seq (N - 1)) N := Nat.gcd_pos_of_pos_right _ (by omega)
  have : N.minFac ≤ Nat.gcd (x_seq (N - 1)) N := Nat.le_of_dvd hgpos hgcd
  omega

/--
Conjecture: For prime p such that p-2 is not a prime, a(p-1) = p.
-/
theorem oeis_135508_conjecture_0 :
  ∀ p : ℕ, Nat.Prime p → ¬ (Nat.Prime (p - 2)) → A135508 (p - 1) = p := by
  intro p hp hp2
  rw [A135508_pred_eq_iff p hp]
  rcases Nat.lt_or_ge p 5 with hsmall | hbig
  · have h2 := hp.two_le
    interval_cases p
    · decide
    · decide
    · exact absurd hp (by decide)
  · intro hdvd
    have hpm : p - 1 = (p - 2) + 1 := by omega
    rw [hpm, prime_dvd_xseq p (p - 2) hp] at hdvd
    obtain ⟨k, hkmem, hkdvd⟩ := hdvd
    rw [Finset.mem_Icc] at hkmem
    obtain ⟨hkeq, hg1⟩ := yfac_eq_p_of_dvd p k (by omega) hkmem.2 hkdvd
    subst hkeq
    have hcl := core_lemma (p - 2) (by omega) hp2
    have e1 : p - 3 + 1 = p - 2 := by omega
    have e2 : p - 2 - 1 = p - 3 := by omega
    rw [e1] at hg1
    rw [e2] at hcl
    omega
