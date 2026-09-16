import FormalConjectures.Util.ProblemImports
import Submission.Final

open Nat Finset
open scoped Nat.Prime

set_option maxHeartbeats 20000000
set_option maxRecDepth 20000000

noncomputable def A263001 (n : ℕ) : ℕ :=
  let bound : ℕ := n + 1
  let K_set : Finset ℕ := Icc 1 bound
  let M_set : Finset ℕ := Icc 1 bound
  (filter (fun p : ℕ × ℕ =>
    Nat.primeCounting (p.fst * (p.fst + 1)) + Nat.primeCounting (p.snd * (p.snd + 1) / 2) = n
  ) (Finset.product K_set M_set)).card

theorem oeis_a263001_conjecture :
  (∀ (n : ℕ), 2 < n → A263001 n > 0) ∧
  (∀ (n : ℕ), A263001 n = 1 ↔ n = 1 ∨ n = 4 ∨ n = 6) :=
by sorry

theorem oeis_a263001_conjecture.disproof : ¬ (type_of% oeis_a263001_conjecture) := by
  intro h
  have h2 := h.2 51156
  have a263001_51156_eq_1 : A263001 51156 = 1 := by
    unfold A263001
    dsimp only
    have h_filter : filter (fun p : ℕ × ℕ => Nat.primeCounting (p.fst * (p.fst + 1)) + Nat.primeCounting (p.snd * (p.snd + 1) / 2) = 51156) (Finset.product (Icc 1 51157) (Icc 1 51157)) = {(16, 1119)} := by
      ext ⟨k, m⟩
      simp only [mem_filter, mem_product, mem_Icc, mem_singleton, Prod.mk.injEq]
      constructor
      · intro hyp
        rcases hyp with ⟨⟨⟨hk1, hk2⟩, ⟨hm1, hm2⟩⟩, heq⟩
        rw [← my_pi_eq, ← my_pi_eq] at heq
        have h_general := no_sol_general k m hm1
        rcases h_general with h_ans | h_ans
        · exact h_ans
        · contradiction
      · intro hyp
        rcases hyp with ⟨rfl, rfl⟩
        refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ?_⟩
        have hk_eq : 16 * (16 + 1) = 272 := by decide
        have hm_eq : 1119 * (1119 + 1) / 2 = 626640 := by decide
        rw [hk_eq, hm_eq]
        have h1 : Nat.primeCounting 272 = 58 := by rw [← my_pi_eq, pi_272]
        have h2 : Nat.primeCounting 626640 = 51098 := by rw [← my_pi_eq, pi_626640]
        omega
    rw [h_filter]
    exact card_singleton (16, 1119)
  rw [a263001_51156_eq_1] at h2
  revert h2
  decide
