import Submission.DisjointCoverBound

/-! General prime-class covers cannot always be replaced by exact covers of
    the same interval using the same or a smaller number of primes. -/
namespace Erdos970.DisjointCover
open Finset

lemma hits_nine_le {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (hits 9 p a).card ≤ 1 + (if p = 3 then 2 else 0) +
      (if p = 5 then 1 else 0) + (if p = 7 then 1 else 0) := by
  apply (hits_card_le 9 p a).trans
  norm_num only [Nat.reduceSub]
  by_cases hle : p ≤ 8
  · interval_cases p <;> first | contradiction | (norm_num at hp ⊢)
  · have hd : 8 / p = 0 := Nat.div_eq_of_lt (by omega)
    rw [hd]
    omega

/-- No four distinct prime classes exactly cover nine consecutive positions. -/
theorem no_exact_cover_nine {P : Finset ℕ} {r : ℕ → ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hk : P.card ≤ 4) : ¬ExactCover P r 9 := by
  classical
  intro h
  have htwo : 2 ∉ P := by
    intro hp
    have hh := length_le_of_member h hp
      (fun q hq => (hP q hq).one_lt)
      (fun q hq hne => (Nat.coprime_primes (by norm_num) (hP q hq)).mpr hne)
    omega
  have hcount := cover_card_le_sum h.1
  have hupper : (∑ p ∈ P, (hits 9 p (r p)).card) ≤ P.card + 4 := by
    calc
      _ ≤ ∑ p ∈ P, (1 + (if p = 3 then 2 else 0) +
          (if p = 5 then 1 else 0) + (if p = 7 then 1 else 0)) := by
        apply sum_le_sum
        intro p hp
        exact hits_nine_le (hP p hp) (by rintro rfl; exact htwo hp)
      _ ≤ _ := by
        simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_one,
          sum_ite_eq']
        split_ifs <;> omega
  omega

/-- Four prime classes do cover nine consecutive positions when overlaps are allowed. -/
theorem general_cover_nine : ∃ P : Finset ℕ, ∃ r : ℕ → ℕ,
    (∀ p ∈ P, p.Prime) ∧ P.card = 4 ∧
    ∀ i < 9, ∃ p ∈ P, i ≡ r p [MOD p] := by
  refine ⟨{2, 3, 5, 7}, (fun p => p - 2), ?_, ?_, ?_⟩
  · intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  · decide
  · intro i hi
    interval_cases i <;> decide

/-- Negates a putative lossless exactification step, not the Jacobsthal conjecture. -/
theorem no_lossless_exactification : ¬(∀ (P : Finset ℕ) (r : ℕ → ℕ) (m : ℕ),
    (∀ p ∈ P, p.Prime) → (∀ i < m, ∃ p ∈ P, i ≡ r p [MOD p]) →
    ∃ Q : Finset ℕ, ∃ s : ℕ → ℕ,
      (∀ q ∈ Q, q.Prime) ∧ Q.card ≤ P.card ∧ ExactCover Q s m) := by
  intro hh
  obtain ⟨P, r, hP, hc, hcov⟩ := general_cover_nine
  obtain ⟨Q, s, hQ, hQc, hQs⟩ := hh P r 9 hP hcov
  exact no_exact_cover_nine hQ (by omega) hQs

#print axioms no_exact_cover_nine
#print axioms no_lossless_exactification
end Erdos970.DisjointCover
