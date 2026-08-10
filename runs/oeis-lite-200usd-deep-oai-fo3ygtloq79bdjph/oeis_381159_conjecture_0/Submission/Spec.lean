import FormalConjectures.Util.ProblemImports

open Nat

/--
Numbers whose prime divisors all end in the same digit.
-/
def A381159_condition (n : ℕ) : Prop :=
  Finset.card (n.primeFactors.image (fun p => p % 10)) ≤ 1

/--
A381159: Numbers whose prime divisors all end in the same digit.
-/
noncomputable def A381159 (n : ℕ) : ℕ := n.nth A381159_condition

namespace oeis_381159_conjecture_0

private def pairList : List (ℕ × ℕ) :=
  [(2,3),(2,5),(2,7),(2,11),(2,13),
   (3,5),(3,7),(3,11),(3,17),
   (5,7),(5,11),(5,13),
   (7,11),(7,13),(11,13)]

private def hasPair (d : ℕ) : Bool :=
  pairList.any (fun x =>
    let p := x.1
    let q := x.2
    (d % p != 0) && (d % q != 0))

private def allUpTo (n : ℕ) (f : ℕ → Bool) : Bool :=
  match n with
  | 0 => true
  | k + 1 => allUpTo k f && f k

private lemma allUpTo_eq_true {f : ℕ → Bool} {n x : ℕ}
    (h : allUpTo n f = true) (hx : x < n) : f x = true := by
  induction n with
  | zero => omega
  | succ k ih =>
      simp [allUpTo] at h
      rcases h with ⟨hprev, hlast⟩
      by_cases hxk : x < k
      · exact ih hprev hxk
      · have : x = k := by omega
        simpa [this] using hlast

private lemma pair_check : allUpTo 2026 (fun d => decide (d = 0) || hasPair d) = true := by
  set_option maxRecDepth 10000 in
  decide

private lemma exists_pair (d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ 2025) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p % 10 ≠ q % 10 ∧
      p * q ≤ 150 ∧ ¬ p ∣ d ∧ ¬ q ∣ d := by
  have hdlt : d < 2026 := by omega
  have h := allUpTo_eq_true (f := fun d => decide (d = 0) || hasPair d) pair_check hdlt
  have hdne : ¬ d = 0 := by omega
  have hp : hasPair d = true := by
    simpa [hdne] using h
  unfold hasPair at hp
  rw [List.any_eq_true] at hp
  rcases hp with ⟨⟨p, q⟩, hmem, hb⟩
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
  rcases hb with ⟨hpmod, hqmod⟩
  have hpd : ¬ p ∣ d := by simpa [Nat.dvd_iff_mod_eq_zero] using hpmod
  have hqd : ¬ q ∣ d := by simpa [Nat.dvd_iff_mod_eq_zero] using hqmod
  have hfacts : p.Prime ∧ q.Prime ∧ p ≠ q ∧ p % 10 ≠ q % 10 ∧ p * q ≤ 150 := by
    simp [pairList] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      rcases h with ⟨rfl, rfl⟩ <;> norm_num
  exact ⟨p, q, hfacts.1, hfacts.2.1, hfacts.2.2.1, hfacts.2.2.2.1,
    hfacts.2.2.2.2, hpd, hqd⟩

private lemma exists_hit (a d p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpd : ¬ p ∣ d) (hqd : ¬ q ∣ d) :
    ∃ i < p * q, p ∣ a + i * d ∧ q ∣ a + i * d := by
  let N := p * q
  have hNpos : N ≠ 0 := by
    dsimp [N]
    exact Nat.mul_ne_zero hp.ne_zero hq.ne_zero
  have hp_coprime_q : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
  have hcop_p : d.Coprime p := by
    exact ((hp.coprime_iff_not_dvd).mpr hpd).symm
  have hcop_q : d.Coprime q := by
    exact ((hq.coprime_iff_not_dvd).mpr hqd).symm
  have hcop : d.Coprime N := by
    dsimp [N]
    exact hcop_p.mul_right hcop_q
  obtain ⟨i, hi_lt, hi⟩ := Nat.exists_mul_mod_eq_of_coprime (N - a % N) hcop hNpos
  refine ⟨i, hi_lt, ?_⟩
  have hmodN : (a + i * d) % N = 0 := by
    have hi' : (i * d) % N = (N - a % N) % N := by
      rw [mul_comm]
      exact hi
    calc
      (a + i * d) % N = (a % N + (N - a % N) % N) % N := by
        rw [Nat.add_mod, hi']
      _ = 0 := by
        have ha_lt : a % N < N := Nat.mod_lt _ (Nat.pos_of_ne_zero hNpos)
        by_cases hz : a % N = 0
        · simp [hz]
        · have hlt : N - a % N < N := by omega
          have hsum : a % N + (N - a % N) = N := by omega
          rw [Nat.mod_eq_of_lt hlt, hsum, Nat.mod_self]
  have hNdvd : N ∣ a + i * d := (Nat.dvd_iff_mod_eq_zero).mpr hmodN
  have hpN : p ∣ N := by exact ⟨q, by simp [N]⟩
  have hqN : q ∣ N := by exact ⟨p, by simp [N, mul_comm]⟩
  exact ⟨dvd_trans hpN hNdvd, dvd_trans hqN hNdvd⟩

private lemma not_condition_of_two_prime_factors {n p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpn : p ∣ n) (hqn : q ∣ n)
    (hmod : p % 10 ≠ q % 10) (hn : n ≠ 0) : ¬ A381159_condition n := by
  intro hc
  unfold A381159_condition at hc
  have hp_mem : p ∈ n.primeFactors := hp.mem_primeFactors hpn hn
  have hq_mem : q ∈ n.primeFactors := hq.mem_primeFactors hqn hn
  have hp_img : p % 10 ∈ n.primeFactors.image (fun p => p % 10) := Finset.mem_image.mpr ⟨p, hp_mem, rfl⟩
  have hq_img : q % 10 ∈ n.primeFactors.image (fun p => p % 10) := Finset.mem_image.mpr ⟨q, hq_mem, rfl⟩
  have hcard : 1 < (n.primeFactors.image (fun p => p % 10)).card :=
    Finset.one_lt_card.mpr ⟨p % 10, hp_img, q % 10, hq_img, hmod⟩
  omega

end oeis_381159_conjecture_0

/--
A381159 51st All-Russian Mathematical Olympiad for Schoolchildren. Problem.
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)

We formalize the positive answer to the question/conjecture.
The condition for "lopsided" for n > 1 is exactly A381159_condition n.
We require the starting term a to be at least 2 to ensure all terms are > 1.
-/
theorem oeis_381159_conjecture_0.disproof :
  ¬ (∃ (a d : ℕ),
    2 ≤ a ∧ -- The starting number 'a' must be lopsided, hence > 1. All subsequent terms will also be > 1.
    1 ≤ d ∧ -- 'd' must be positive for an increasing arithmetic progression
    d ≤ 2025 ∧ -- difference not exceeding 2025
    ∀ (i : Fin 150), A381159_condition (a + i.val * d)) := by
  rintro ⟨a, d, ha, hd1, hd2, hcond⟩
  obtain ⟨p, q, hp, hq, hpq, hmod, hpq_le, hpd, hqd⟩ :=
    oeis_381159_conjecture_0.exists_pair d hd1 hd2
  obtain ⟨i, hi_lt, hpi, hqi⟩ :=
    oeis_381159_conjecture_0.exists_hit a d p q hp hq hpq hpd hqd
  have hi150 : i < 150 := by omega
  let fi : Fin 150 := ⟨i, hi150⟩
  have hn_pos : a + i * d ≠ 0 := by omega
  exact oeis_381159_conjecture_0.not_condition_of_two_prime_factors hp hq hpi hqi hmod hn_pos (hcond fi)
