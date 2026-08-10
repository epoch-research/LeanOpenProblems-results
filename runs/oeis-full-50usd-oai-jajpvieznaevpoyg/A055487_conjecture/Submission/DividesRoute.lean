import FormalConjectures.Util.ProblemImports
open Set
open Nat

noncomputable def A055487 (n : ℕ) : ℕ := sInf {m : ℕ | Nat.totient m = Nat.factorial n}
def prime_candidates (n : ℕ) : Set ℕ :=
  let N := Nat.factorial n
  { p : ℕ | Nat.Prime p ∧ Nat.sqrt N < p ∧ (p - 1) ∣ N ∧ Nat.Prime (N / (p - 1) + 1) }

lemma candidate_mem {n : ℕ} (h : (prime_candidates n).Nonempty) :
    sInf (prime_candidates n) ∈ prime_candidates n := Nat.sInf_mem h

lemma candidate_totient (n : ℕ) (h : (prime_candidates n).Nonempty)
    (hc : (sInf (prime_candidates n)).Coprime (Nat.factorial n / (sInf (prime_candidates n) - 1) + 1)) :
    Nat.totient (sInf (prime_candidates n) * (Nat.factorial n / (sInf (prime_candidates n) - 1) + 1)) = Nat.factorial n := by
  let p := sInf (prime_candidates n)
  let q := Nat.factorial n / (p - 1) + 1
  have hp_mem : p ∈ prime_candidates n := by simpa [p] using candidate_mem h
  have hp : Nat.Prime p := hp_mem.1
  have hdvd : p - 1 ∣ Nat.factorial n := hp_mem.2.2.1
  have hq : Nat.Prime q := by simpa [prime_candidates, p, q] using hp_mem.2.2.2
  change Nat.totient (p * q) = Nat.factorial n
  rw [Nat.totient_mul]
  · rw [Nat.totient_prime hp, Nat.totient_prime hq]
    have hqsub : q - 1 = Nat.factorial n / (p - 1) := by unfold q; exact Nat.add_one_sub_one _
    rw [hqsub]
    exact Nat.mul_div_cancel' hdvd
  · simpa [p, q] using hc

lemma equality_from_divides (n : ℕ) (h : (prime_candidates n).Nonempty)
    (hc : (sInf (prime_candidates n)).Coprime (Nat.factorial n / (sInf (prime_candidates n) - 1) + 1))
    (hdiv : A055487 n ∣ sInf (prime_candidates n) * (Nat.factorial n / (sInf (prime_candidates n) - 1) + 1))
    (hodd : Odd (sInf (prime_candidates n) * (Nat.factorial n / (sInf (prime_candidates n) - 1) + 1))) :
    A055487 n = sInf (prime_candidates n) * (Nat.factorial n / (sInf (prime_candidates n) - 1) + 1) := by
  have hnon : ({m : ℕ | Nat.totient m = Nat.factorial n}).Nonempty := by
    refine ⟨sInf (prime_candidates n) * (Nat.factorial n / (sInf (prime_candidates n) - 1) + 1), ?_⟩
    exact candidate_totient n h hc
  have hAphi : Nat.totient (A055487 n) = Nat.factorial n := by
    unfold A055487
    exact Nat.sInf_mem hnon
  have hBphi := candidate_totient n h hc
  have heqphi : Nat.totient (A055487 n) = Nat.totient (sInf (prime_candidates n) * (Nat.factorial n / (sInf (prime_candidates n) - 1) + 1)) := by
    rw [hAphi, hBphi]
  have hor := Nat.eq_or_eq_of_totient_eq_totient hdiv heqphi
  rcases hor with hEq | hTwo
  · exact hEq
  · exfalso
    rw [← hTwo] at hodd
    have hev : Even (2 * A055487 n) := ⟨A055487 n, by ring⟩
    exact Nat.not_even_iff_odd.mpr hodd hev
