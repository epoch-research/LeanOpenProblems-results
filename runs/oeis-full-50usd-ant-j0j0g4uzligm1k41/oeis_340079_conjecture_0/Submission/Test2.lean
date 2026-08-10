import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

def S (n : ℕ) : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n

-- S(1) = 1
example : S 1 = 1 := by decide

-- S(prime p) = 2p - 1
example (p : ℕ) (hp : p.Prime) : S p = 2 * p - 1 := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  unfold S
  rw [Finset.sum_Ico_succ_top hp1]
  have hpp : Nat.gcd p p = p := Nat.gcd_self p
  have hrest : (Finset.Ico 1 p).sum (fun k => Nat.gcd k p) = p - 1 := by
    have : ∀ k ∈ Finset.Ico 1 p, Nat.gcd k p = 1 := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk1 : 1 ≤ k := hk.1
      have hkp : k < p := hk.2
      have hndvd : ¬ p ∣ k := by
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      have : Nat.Coprime p k := (hp.coprime_iff_not_dvd).mpr hndvd
      rw [Nat.coprime_comm] at this
      exact this
    rw [Finset.sum_congr rfl this]
    simp [Nat.card_Ico]
  rw [hrest, hpp]
  omega
