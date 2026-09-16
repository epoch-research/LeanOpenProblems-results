import FormalConjectures.Util.ProblemImports

open Finset

def a (n : ℕ) : ℕ :=
  (Icc 1 n).filter (fun k => Nat.primeFactors k ⊆ Nat.primeFactors n) |>.card

lemma a_prime_le_two {p : ℕ} (hp : p.Prime) : a p ≤ 2 := by
  have : (Icc 1 p).filter (fun k => Nat.primeFactors k ⊆ Nat.primeFactors p) ⊆ {1, p} := by
    intro k hk
    rw [mem_filter, mem_Icc] at hk
    rcases hk with ⟨⟨h1, hpk⟩, hsub⟩
    rw [hp.primeFactors] at hsub
    rw [mem_insert, mem_singleton]
    by_cases hk1 : k = 1
    · exact Or.inl hk1
    · right
      have hk_gt1 : 1 < k := lt_of_le_of_ne h1 (Ne.symm hk1)
      have hex : ∃ q, q.Prime ∧ q ∣ k := Nat.exists_prime_and_dvd hk_gt1.ne'
      rcases hex with ⟨q, hq, hqk⟩
      have hq_mem : q ∈ k.primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨hq, hqk, _root_.ne_of_gt (lt_trans zero_lt_one hk_gt1)⟩
      have hqp : q ∈ ({p} : Finset ℕ) := hsub hq_mem
      rw [mem_singleton] at hqp
      subst hqp
      exact le_antisymm hpk (Nat.le_of_dvd (lt_trans zero_lt_one hk_gt1) hqk)
  calc
    a p = ((Icc 1 p).filter (fun k => Nat.primeFactors k ⊆ Nat.primeFactors p)).card := rfl
    _ ≤ ({1, p} : Finset ℕ).card := card_le_card this
    _ ≤ 2 := by
      calc
        ({1, p} : Finset ℕ).card ≤ ({p} : Finset ℕ).card + 1 := card_insert_le 1 {p}
        _ = 1 + 1 := by rw [card_singleton]
        _ = 2 := rfl
