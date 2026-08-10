import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

/--
A340079: $a(n) = n / \gcd(n, 1+A018804(n))$, where $A018804(n) = \sum_{k=1..n} \gcd(k, n)$.
$$a(n) = \frac{n}{\gcd(n, 1+\sum_{k=1}^n \gcd(k, n))}$$
-/
def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

/-- The Pillai arithmetical function `A018804`, written as a `Finset` sum. -/
def S (n : ℕ) : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n

theorem a_eq (n : ℕ) : a n = n / Nat.gcd n (1 + S n) := rfl

/-- Reduction: for `n ≥ 1`, `a n = 1` iff `n` divides `1 + S n`. -/
theorem a_eq_one_iff_dvd (n : ℕ) (hn : 1 ≤ n) : a n = 1 ↔ n ∣ (1 + S n) := by
  rw [a_eq]
  set d := Nat.gcd n (1 + S n) with hd
  have hdvd : d ∣ n := Nat.gcd_dvd_left _ _
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ hn
  constructor
  · intro h
    have hdn : d = n := by
      rcases hdvd with ⟨c, hc⟩
      have hc' : n / d = c := by rw [hc]; exact Nat.mul_div_cancel_left c hdpos
      rw [hc'] at h; subst h
      have := hc; omega
    have hd_dvd : d ∣ 1 + S n := hd ▸ Nat.gcd_dvd_right n (1 + S n)
    exact hdn ▸ hd_dvd
  · intro h
    have hdn : d = n := by rw [hd]; exact Nat.gcd_eq_left h
    rw [hdn]; exact Nat.div_self hn

/-- `S 1 = 1`. -/
theorem S_one : S 1 = 1 := by decide

/-- For a prime `p`, `S p = 2 * p - 1` (this is `A018804(p) = 2p - 1`). -/
theorem S_prime (p : ℕ) (hp : p.Prime) : S p = 2 * p - 1 := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  unfold S
  rw [Finset.sum_Ico_succ_top hp1]
  have hpp : Nat.gcd p p = p := Nat.gcd_self p
  have hrest : (Finset.Ico 1 p).sum (fun k => Nat.gcd k p) = p - 1 := by
    have hall : ∀ k ∈ Finset.Ico 1 p, Nat.gcd k p = 1 := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk1 : 1 ≤ k := hk.1
      have hkp : k < p := hk.2
      have hndvd : ¬ p ∣ k := by
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      have hcop : Nat.Coprime p k := (hp.coprime_iff_not_dvd).mpr hndvd
      rw [Nat.coprime_comm] at hcop
      exact hcop
    rw [Finset.sum_congr rfl hall]
    simp [Nat.card_Ico]
  rw [hrest, hpp]
  omega

/-- `S n` as a sum over `range n`. -/
theorem S_eq_range (n : ℕ) (hn : 1 ≤ n) :
    S n = ∑ k ∈ Finset.range n, Nat.gcd n k := by
  unfold S
  rw [Finset.sum_Ico_succ_top hn]
  have e2 : Finset.range n = insert 0 (Finset.Ico 1 n) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
  rw [e2, Finset.sum_insert (by simp)]
  rw [Nat.gcd_self, Nat.gcd_zero_right]
  have hc : (Finset.Ico 1 n).sum (fun k => Nat.gcd k n)
      = (Finset.Ico 1 n).sum (fun k => Nat.gcd n k) :=
    Finset.sum_congr rfl (fun k _ => Nat.gcd_comm k n)
  rw [hc]; ring

/-- The gcd-sum identity: `S n = ∑_{d ∣ n} d * φ(n/d)`. -/
theorem S_eq_sum_div (n : ℕ) (hn : 1 ≤ n) :
    S n = ∑ d ∈ n.divisors, d * Nat.totient (n / d) := by
  rw [S_eq_range n hn]
  rw [← Finset.sum_fiberwise_of_maps_to (t := n.divisors) (g := fun k => Nat.gcd n k)
        (f := fun k => Nat.gcd n k)]
  · apply Finset.sum_congr rfl
    intro d hd
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hall : ∀ k ∈ (Finset.range n).filter (fun k => Nat.gcd n k = d),
        Nat.gcd n k = d := fun k hk => (Finset.mem_filter.1 hk).2
    rw [Finset.sum_congr rfl hall, Finset.sum_const, ← Nat.totient_div_of_dvd hdvd,
        smul_eq_mul, mul_comm]
  · intro k _
    rw [Nat.mem_divisors]
    exact ⟨Nat.gcd_dvd_left n k, by omega⟩

/-- If `p²∣m` then `p ∣ φ(m)`. -/
theorem p_dvd_totient_of_sq {p m : ℕ} (hp : p.Prime) (hm0 : m ≠ 0) (h : p ^ 2 ∣ m) :
    p ∣ Nat.totient m := by
  set a := m.factorization p with ha
  have ha2 : 2 ≤ a := by
    rw [ha]; exact (Nat.Prime.pow_dvd_iff_le_factorization hp hm0).1 h
  have hsplit : p ^ a * (ordCompl[p] m) = m := by
    have h2 := Nat.ordProj_mul_ordCompl_eq_self m p
    simpa [ha] using h2
  have hcop : Nat.Coprime (p ^ a) (ordCompl[p] m) := (Nat.coprime_ordCompl hp hm0).pow_left a
  rw [← hsplit, Nat.totient_mul hcop]
  have hpt : p ∣ Nat.totient (p ^ a) := by
    rw [Nat.totient_prime_pow hp (by omega)]
    exact Dvd.dvd.mul_right (dvd_pow_self p (by omega : a - 1 ≠ 0)) _
  exact Dvd.dvd.mul_right hpt _

/-- Non-squarefree case: if `p²∣n` (p prime) then `p ∣ S n`. -/
theorem nonsquarefree_dvd_S {p n : ℕ} (hp : p.Prime) (hpp : p ^ 2 ∣ n) : p ∣ S n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [S]
  · rw [S_eq_sum_div n hn]
    apply Finset.dvd_sum
    intro d hd
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
    by_cases hpd : p ∣ d
    · exact Dvd.dvd.mul_right hpd _
    · have hnd0 : n / d ≠ 0 := by
        have := Nat.div_pos (Nat.le_of_dvd hn hdvd) hd_pos; omega
      have hcop : Nat.Coprime (p ^ 2) d := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd).pow_left 2
      obtain ⟨c, hc⟩ := hdvd
      have hnd : n / d = c := by rw [hc]; exact Nat.mul_div_cancel_left c hd_pos
      have hsq : p ^ 2 ∣ (n / d) := by
        rw [hnd]; rw [hc] at hpp
        exact Nat.Coprime.dvd_of_dvd_mul_left hcop hpp
      exact Dvd.dvd.mul_left (p_dvd_totient_of_sq hp hnd0 hsq) d

/--
It is conjectured that $a(n) = 1$ if and only if $n$ is 1 or a prime number.
A340079: It is conjectured that this is 1 iff n is 1 or a prime. See _Thomas Ordowski_'s Oct 22 2014 comment in A018804.
-/
theorem oeis_340079_conjecture_0 (n : ℕ) : a n = 1 ↔ (n = 1 ∨ Nat.Prime n) := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [a_eq] at h; simp only [Nat.zero_div] at h; exact absurd h (by norm_num)
    · rw [a_eq_one_iff_dvd n hn] at h
      by_contra hcon
      push_neg at hcon
      obtain ⟨hne1, hnp⟩ := hcon
      by_cases hsf : Squarefree n
      · -- Squarefree composite case: the open Ordowski crux
        -- (reduces to: for squarefree composite n = ∏ pᵢ, ∏(2pᵢ-1) ≢ -1 (mod n)).
        sorry
      · -- Non-squarefree case: fully proved.
        rw [Nat.squarefree_iff_prime_squarefree] at hsf
        push_neg at hsf
        obtain ⟨x, hxp, hxdvd⟩ := hsf
        have hp : Nat.Prime x := hxp
        have hpp : x ^ 2 ∣ n := by rw [sq]; exact hxdvd
        have hpS : x ∣ S n := nonsquarefree_dvd_S hp hpp
        have hpn : x ∣ n := dvd_trans (dvd_pow_self x (by norm_num)) hpp
        have hx1 : ¬ x ∣ (1 + S n) := by
          intro hd
          rw [add_comm] at hd
          have hx1' : x ∣ 1 := (Nat.dvd_add_right hpS).mp hd
          have := Nat.le_of_dvd one_pos hx1'
          have := hp.two_le; omega
        exact hx1 (dvd_trans hpn h)
  · intro h
    rcases h with h1 | hp
    · subst h1
      rw [a_eq_one_iff_dvd 1 (le_refl 1)]
      exact one_dvd _
    · have hp1 : 1 ≤ n := hp.one_lt.le
      rw [a_eq_one_iff_dvd n hp1, S_prime n hp]
      have : 1 + (2 * n - 1) = 2 * n := by
        have : 1 ≤ n := hp1
        omega
      rw [this]
      exact dvd_mul_left n 2
