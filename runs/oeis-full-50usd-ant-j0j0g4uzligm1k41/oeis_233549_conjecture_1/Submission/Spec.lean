import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A233549: Number of ways to write $n = p + q$ ($q > 0$) with $p$ prime and $(\phi(p)\phi(q))^4 + 1$ prime,
where $\phi(\cdot)$ is Euler's totient function (A000010).
-/
def a (n : ℕ) : ℕ :=
  Finset.card <| Finset.filter (fun p : ℕ =>
    p.Prime ∧
    let q := n - p
    Nat.Prime ((p.totient * q.totient) ^ 4 + 1)
  ) (Finset.range n)

/-- A lower bound for the totient function: `n ≤ 2 * φ(n)^2`, with the sharper
`n ≤ φ(n)^2` for odd `n`. This is proved by induction over the prime factorization. -/
lemma totient_sq_bound : ∀ n : ℕ,
    n ≤ 2 * (Nat.totient n)^2 ∧ (¬ 2 ∣ n → n ≤ (Nat.totient n)^2) := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.totient_prime_pow hp (Nat.succ_pos m)]
    simp only [Nat.succ_sub_one]
    by_cases hp2 : p = 2
    · subst hp2
      constructor
      · have hx : (2:ℕ)^(m+1) = 2 * 2^m := by rw [pow_succ]; ring
        have h1 : (1:ℕ) ≤ 2^m := Nat.one_le_pow m 2 (by norm_num)
        rw [hx]
        have : (2:ℕ) - 1 = 1 := rfl
        rw [this, mul_one]
        nlinarith [h1]
      · intro h
        exact absurd (dvd_pow_self 2 (Nat.succ_ne_zero m)) h
    · -- p odd prime, p ≥ 3
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hsub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
      have h1 : 2 ≤ p - 1 := by omega
      have hd : p ≤ (p - 1) ^ 2 := by nlinarith [hsub, h1]
      have e1 : (p ^ m * (p - 1)) ^ 2 = p ^ (2 * m) * (p - 1) ^ 2 := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm m 2]
      have h3 : p ^ (m + 1) ≤ p ^ (2 * m + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h4 : p ^ (2 * m + 1) = p ^ (2 * m) * p := by rw [pow_succ]
      have h2 : p ^ (2 * m) * p ≤ p ^ (2 * m) * (p - 1) ^ 2 :=
        Nat.mul_le_mul_left _ hd
      have key : p ^ (m + 1) ≤ (p ^ m * (p - 1)) ^ 2 := by
        rw [e1]; exact h3.trans (h4 ▸ h2)
      refine ⟨?_, fun _ => key⟩
      exact le_trans key (by linarith [Nat.zero_le ((p ^ m * (p - 1)) ^ 2)])
  | zero => exact ⟨by simp, fun h => absurd (dvd_zero 2) h⟩
  | one => exact ⟨by simp, fun _ => by simp⟩
  | coprime a b ha hb hcop iha ihb =>
    rw [Nat.totient_mul hcop]
    have hnotboth : ¬ (2 ∣ a ∧ 2 ∣ b) := by
      rintro ⟨h1, h2⟩
      have : 2 ∣ Nat.gcd a b := Nat.dvd_gcd h1 h2
      rw [hcop] at this
      omega
    constructor
    · have sq : (a.totient * b.totient)^2 = a.totient^2 * b.totient^2 := by rw [mul_pow]
      rw [sq]
      by_cases h2a : 2 ∣ a
      · have h2b : ¬ 2 ∣ b := fun hb2 => hnotboth ⟨h2a, hb2⟩
        have := Nat.mul_le_mul iha.1 (ihb.2 h2b)
        calc a * b ≤ (2 * a.totient^2) * b.totient^2 := this
          _ = 2 * (a.totient^2 * b.totient^2) := by ring
      · have := Nat.mul_le_mul (iha.2 h2a) ihb.1
        calc a * b ≤ a.totient^2 * (2 * b.totient^2) := this
          _ = 2 * (a.totient^2 * b.totient^2) := by ring
    · intro hab
      have h2a : ¬ 2 ∣ a := fun h => hab (h.mul_right b)
      have h2b : ¬ 2 ∣ b := fun h => hab (h.mul_left a)
      have := Nat.mul_le_mul (iha.2 h2a) (ihb.2 h2b)
      have sq : (a.totient * b.totient)^2 = a.totient^2 * b.totient^2 := by rw [mul_pow]
      rw [sq]; exact this

/--
Conjecture: (i) a(n) > 0 for all n > 2.
Part (i) of the conjecture implies that there are infinitely many primes of the form x^4 + 1.
-/
theorem oeis_233549_conjecture_1 :
  (∀ n, 2 < n → 0 < a n) →
  Set.Infinite {p : ℕ | Nat.Prime p ∧ ∃ x : ℕ, p = x ^ 4 + 1} :=
by
  intro h hfin
  set S := {p : ℕ | Nat.Prime p ∧ ∃ x : ℕ, p = x ^ 4 + 1} with hS
  -- The set of `x` with `x^4+1 ∈ S` is finite.
  have hinj : Function.Injective (fun x : ℕ => x ^ 4 + 1) := by
    intro u v huv
    simp only [add_left_inj] at huv
    exact (Nat.pow_left_inj (by norm_num)).mp huv
  have hTfin : {x : ℕ | (fun x : ℕ => x ^ 4 + 1) x ∈ S}.Finite :=
    Set.Finite.preimage (hinj.injOn) hfin
  obtain ⟨K, hK⟩ := hTfin.bddAbove
  rw [mem_upperBounds] at hK
  -- Every `n > 2` satisfies `n ≤ K + 1 + 2 * K ^ 2`.
  have hbound : ∀ n, 2 < n → n ≤ K + 1 + 2 * K ^ 2 := by
    intro n hn
    have hpos := h n hn
    rw [a] at hpos
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpn, hpprime, hqprime⟩ := hp
    set q := n - p with hq
    have hqpos : 0 < q := by omega
    have hphi_p : p.totient = p - 1 := Nat.totient_prime hpprime
    have hmem : (p.totient * q.totient) ∈ {x : ℕ | (fun x : ℕ => x ^ 4 + 1) x ∈ S} := by
      simp only [Set.mem_setOf_eq, hS]
      refine ⟨hqprime, ⟨p.totient * q.totient, rfl⟩⟩
    have hle : p.totient * q.totient ≤ K := hK _ hmem
    have hphi_q_pos : 0 < q.totient := Nat.totient_pos.mpr hqpos
    have hphi_p_pos : 0 < p.totient := Nat.totient_pos.mpr hpprime.pos
    have hp1 : p - 1 ≤ K := by
      calc p - 1 = p.totient := hphi_p.symm
        _ = p.totient * 1 := by rw [mul_one]
        _ ≤ p.totient * q.totient := by
            apply Nat.mul_le_mul_left; omega
        _ ≤ K := hle
    have hphiq : q.totient ≤ K := by
      calc q.totient = 1 * q.totient := by rw [one_mul]
        _ ≤ p.totient * q.totient := by
            apply Nat.mul_le_mul_right; omega
        _ ≤ K := hle
    have hqbound : q ≤ 2 * K ^ 2 := by
      have := (totient_sq_bound q).1
      calc q ≤ 2 * q.totient ^ 2 := this
        _ ≤ 2 * K ^ 2 := by
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_left hphiq 2
    have hpbound : p ≤ K + 1 := by omega
    omega
  have := hbound (K + 1 + 2 * K ^ 2 + 3) (by omega)
  omega

