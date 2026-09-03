import Submission.ComplementNFACover

/-! A local simulation converts each accepting run on4n into an accepting
run on n. No simulation with a rejected power-of-four seed is provided. -/
namespace Erdos406BackwardNFASimulation
open Erdos406MSDCertificate Erdos406ComplementNFA

structure Simulation (σ : Type*) where
  M : NFA ℕ σ
  R : σ → σ → ℕ → Prop
  initial : ∀ c, c < 4 → ∀ p ∈ evalNat M.toDFA c, ∃ q ∈ M.start, R p q c
  step : ∀ p q c d e c' r,
    c < 4 → d < 3 → e < 3 → c' < 4 → 4 * d + c' = 3 * c + e →
    R p q c → r ∈ M.step p e → ∃ s ∈ M.step q d, R r s c'
  finish : ∀ p q, R p q 0 → p ∈ M.accept → q ∈ M.accept

namespace Simulation
variable {σ : Type*} (C : Simulation σ)

/-- Match an arbitrary output state, not just an accepting one. -/
theorem match_output : ∀ n c, c < 4 → ∀ p ∈ evalNat C.M.toDFA (4 * n + c),
    ∃ q ∈ evalNat C.M.toDFA n, C.R p q c := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro c hc p hp
    by_cases hn : n = 0
    · subst n
      simp only [mul_zero, zero_add] at hp
      obtain ⟨q, hq, hr⟩ := C.initial c hc p hp
      exact ⟨q, by simpa only [evalNat_zero, NFA.toDFA] using hq, hr⟩
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      let d := n % 3
      let a := (4 * d + c) / 3
      let e := (4 * d + c) % 3
      have hd : d < 3 := Nat.mod_lt _ (by decide)
      have ha : a < 4 := by dsimp [a]; omega
      have he : e < 3 := Nat.mod_lt _ (by decide)
      have hcarry : 4 * d + c = 3 * a + e := by
        dsimp [a, e]
        omega
      have hdiv : (4 * n + c) / 3 = 4 * (n / 3) + a :=
        (affine_div_mod 4 n c).1
      have hmod : (4 * n + c) % 3 = e := (affine_div_mod 4 n c).2
      rw [evalNat_pos C.M.toDFA (by omega : 0 < 4 * n + c), hdiv, hmod] at hp
      obtain ⟨r, hr, hrp⟩ := NFA.mem_stepSet.mp hp
      obtain ⟨q, hq, hrq⟩ := ih (n / 3) (Nat.div_lt_self hnpos (by decide)) a ha r hr
      obtain ⟨s, hqs, hps⟩ := C.step r q a d e c p ha hd he hc hcarry hrq hrp
      refine ⟨s, ?_, hps⟩
      rw [evalNat_pos C.M.toDFA hnpos]
      exact NFA.mem_stepSet.mpr ⟨q, hq, hqs⟩

theorem backward (n : ℕ) : acceptsNat C.M (4 * n) → acceptsNat C.M n := by
  rintro ⟨p, hp, hpa⟩
  obtain ⟨q, hq, hpq⟩ := C.match_output n 0 (by decide) p (by simpa using hp)
  exact ⟨q, hq, C.finish p q hpq hpa⟩

/-- A checked simulation and rejected seed would settle the conjecture.
Their existence is not asserted by this theorem. -/
theorem finite_of_cover (g : σ)
    (hfirst : g ∈ C.M.stepSet C.M.start 1)
    (hloop : ∀ d, d < 2 → g ∈ C.M.step g d)
    (haccept : g ∈ C.M.accept) (E : ℕ)
    (hseed : ¬ acceptsNat C.M (4 ^ E)) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  exact Erdos406BackwardComplement.finite_of_backward_cover_above E (acceptsNat C.M)
    hseed (fun n _ => C.backward n) (covers_positive_good C.M g hfirst hloop haccept)

end Simulation
#print axioms Simulation.match_output
#print axioms Simulation.backward
#print axioms Simulation.finite_of_cover
end Erdos406BackwardNFASimulation
