import FormalConjectures.Util.ProblemImports
open Finset Nat Set
noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card
noncomputable def A047983_count (m : ℕ) : ℕ :=
  let tau_m := tau m
  Finset.card ((Finset.Ico 1 m).filter (fun k : ℕ => tau k = tau_m))
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | A047983_count m = n}

lemma tau_prime {p : ℕ} (hp : Nat.Prime p) : tau p = 2 := by
  unfold tau
  rw [Nat.card_divisors hp.ne_zero]
  rw [hp.primeFactors]
  simp [hp.factorization_self]

lemma A_count_prime {p : ℕ} (hp : Nat.Prime p) : A047983_count p = Nat.primeCounting' p := by
  unfold A047983_count
  rw [tau_prime hp]
  unfold Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]
  congr 1
  ext k
  simp only [mem_filter, mem_Ico, mem_range]
  constructor
  · rintro ⟨⟨hk1, hkp⟩, ht⟩
    have hkprime : Nat.Prime k := by
      -- tau k = 2 iff prime for positive k
      unfold tau at ht
      rw [Nat.card_divisors (ne_of_gt hk1)] at ht
      -- need show from product over factors =2
      sorry
    exact ⟨hkp, hkprime⟩
  · rintro ⟨hkp, hkprime⟩
    exact ⟨⟨hkprime.one_le, hkp⟩, tau_prime hkprime⟩
