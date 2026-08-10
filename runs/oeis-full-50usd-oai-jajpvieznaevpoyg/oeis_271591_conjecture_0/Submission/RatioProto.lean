import FormalConjectures.Util.ProblemImports
open Nat

def tribonacci (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => (tribonacci (n + 2)) + (tribonacci (n + 1)) + (tribonacci n)

def Plo (n : ℕ) : Prop := 1838*tribonacci n ≤ 1000*tribonacci (n+1)
def Phi (n : ℕ) : Prop := 1000*tribonacci (n+1) ≤ 1841*tribonacci n

lemma tri_rec (n : ℕ) : tribonacci (n+3) = tribonacci (n+2) + tribonacci (n+1) + tribonacci n := by rfl

lemma Plo_step {n} (h0:Plo n) (h1:Plo (n+1)) (h2:Plo (n+2)) : Plo (n+3) := by
  unfold Plo at *
  simp only [Plo, tribonacci] at *
  nlinarith

lemma Phi_step {n} (h0:Phi n) (h1:Phi (n+1)) (h2:Phi (n+2)) : Phi (n+3) := by
  unfold Phi at *
  simp only [Phi, tribonacci] at *
  nlinarith

lemma Plo_aux : ∀ k, Plo (k+9) ∧ Plo (k+10) ∧ Plo (k+11)
| 0 => by norm_num [Plo, tribonacci]
| k+1 => by
  rcases Plo_aux k with ⟨h7,h8,h9⟩
  constructor
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h8
  constructor
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h9
  · have hs := Plo_step h7 h8 h9
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

lemma Phi_aux : ∀ k, Phi (k+9) ∧ Phi (k+10) ∧ Phi (k+11)
| 0 => by norm_num [Phi, tribonacci]
| k+1 => by
  rcases Phi_aux k with ⟨h7,h8,h9⟩
  constructor
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h8
  constructor
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h9
  · have hs := Phi_step h7 h8 h9
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

lemma Plo_of_ge {n} (hn:9≤n): Plo n := by
  let k := n-9
  have hn' : n = k+9 := by omega
  rw [hn']
  exact (Plo_aux k).1

lemma Phi_of_ge {n} (hn:9≤n): Phi n := by
  let k := n-9
  have hn' : n = k+9 := by omega
  rw [hn']
  exact (Phi_aux k).1
