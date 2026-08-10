import FormalConjectures.Util.ProblemImports
open Set
open Nat

noncomputable def A055487 (n : ℕ) : ℕ :=
  sInf {m : ℕ | Nat.totient m = Nat.factorial n}

def prime_candidates (n : ℕ) : Set ℕ :=
  let N := Nat.factorial n
  { p : ℕ | Nat.Prime p ∧ Nat.sqrt N < p ∧ (p - 1) ∣ N ∧ Nat.Prime (N / (p - 1) + 1) }

lemma candidate_sInf_mem {n : ℕ} (h : (prime_candidates n).Nonempty) :
    sInf (prime_candidates n) ∈ prime_candidates n := by
  exact Nat.sInf_mem h

lemma candidate_pos {n : ℕ} (h : (prime_candidates n).Nonempty) :
    0 < sInf (prime_candidates n) := by
  have hp := (candidate_sInf_mem h).1
  exact hp.pos

lemma candidate_two_le {n : ℕ} (h : (prime_candidates n).Nonempty) :
    2 ≤ sInf (prime_candidates n) := by
  have hp := (candidate_sInf_mem h).1
  exact hp.two_le

-- Main upper bound, assuming the two primes are coprime.
lemma A055487_le_candidate_of_coprime (n : ℕ) (h : (prime_candidates n).Nonempty)
    (hc : (sInf (prime_candidates n)).Coprime (Nat.factorial n / (sInf (prime_candidates n) - 1) + 1)) :
    A055487 n ≤
      let N := Nat.factorial n
      let p := sInf (prime_candidates n)
      p * (N / (p - 1) + 1) := by
  unfold A055487
  let p := sInf (prime_candidates n)
  let q := Nat.factorial n / (p - 1) + 1
  have hp_mem : p ∈ prime_candidates n := by
    simpa [p] using candidate_sInf_mem h
  have hp : Nat.Prime p := hp_mem.1
  have hdvd : p - 1 ∣ Nat.factorial n := hp_mem.2.2.1
  have hq : Nat.Prime q := by
    simpa [prime_candidates, p, q] using hp_mem.2.2.2
  apply Nat.sInf_le
  change Nat.totient (p * q) = Nat.factorial n
  rw [Nat.totient_mul hc, Nat.totient_prime hp, Nat.totient_prime hq]
  have hp1pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hmul : (p - 1) * (Nat.factorial n / (p - 1)) = Nat.factorial n := by
    exact Nat.mul_div_cancel' hdvd
  have hqsub : q - 1 = Nat.factorial n / (p - 1) := by
    unfold q
    exact Nat.add_one_sub_one _
  rw [hqsub]
  exact hmul
