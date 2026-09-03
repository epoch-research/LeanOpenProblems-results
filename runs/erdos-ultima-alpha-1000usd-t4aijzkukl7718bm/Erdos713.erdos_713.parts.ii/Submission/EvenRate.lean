import FormalConjecturesUtil
import Submission.BreadthFirst
import Submission.C10

/-! Upper growth rates for even cycles, and the exact power threshold for the ten-cycle. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713EvenCycle

theorem upper {k : ℕ} (hk : 2 ≤ k) :
    (fun n : ℕ => (extremalNumber n (cycleGraph (2 * k)) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (((k + 1 : ℕ) : ℝ) / k)) :=
  Erdos713Rate.upper_of_power_bound (by omega) (Erdos713BreadthFirst.extremal_power_bound hk)

theorem exponent_upper_of_containment {W : Type*} {H : SimpleGraph W} {k : ℕ} (hk : 2 ≤ k)
    (hH : H ⊑ cycleGraph (2 * k)) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ≤ ((k + 1 : ℕ) : ℝ) / k := by
  apply Erdos713Forest.exponent_le_of_isBigO
  exact ((isBigO_const_mul_left_iff hc).mp h.isBigO_symm).trans
    ((Erdos713Rate.extremal_mono_bigO hH).trans (upper hk))

theorem rate_upper_of_containment {W : Type*} {H : SimpleGraph W} {k : ℕ} (hk : 2 ≤ k)
    (hH : H ⊑ cycleGraph (2 * k)) {a : ℝ} (h : Erdos713Rate.HasRate H a) :
    a ≤ ((k + 1 : ℕ) : ℝ) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  apply h.lower _ ((le_div_iff₀ hk').mpr ?_)
    ((Erdos713Rate.extremal_mono_bigO hH).trans (upper hk))
  simp only [one_mul, Nat.cast_add, Nat.cast_one]
  linarith

end Erdos713EvenCycle

namespace Erdos713C10

theorem rate_of_containment {W : Type*} {H : SimpleGraph W}
    (hlo : C10 ⊑ H) (hhi : H ⊑ C10) : Erdos713Rate.HasRate H ((6 : ℝ) / 5) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · apply (Erdos713Rate.extremal_mono_bigO hhi).trans
    simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] using
      Erdos713EvenCycle.upper (by decide : 2 ≤ 5)
  · intro a _ h
    apply lower_exponent_of_prime_bound h
    intro p hp
    exact (extremal_lower_prime p hp).trans hlo.extremalNumber_le

theorem rate : Erdos713Rate.HasRate C10 ((6 : ℝ) / 5) :=
  rate_of_containment (IsContained.refl _) (IsContained.refl _)

theorem exponent_eq_of_containment {W : Type*} {H : SimpleGraph W}
    (hlo : C10 ⊑ H) (hhi : H ⊑ C10) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = (6 : ℝ) / 5 := by
  have ha := exponent_lower_of_containment hlo hc h
  exact Erdos713Rate.exponent_eq (rate_of_containment hlo hhi) (by linarith) hc h

theorem rational_exponent_of_containment {W : Type*} {H : SimpleGraph W}
    (hlo : C10 ⊑ H) (hhi : H ⊑ C10) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨6 / 5, ?_⟩
  simpa using (exponent_eq_of_containment hlo hhi hc h).symm

#print axioms rate
#print axioms rational_exponent_of_containment
#print axioms Erdos713EvenCycle.rate_upper_of_containment

end Erdos713C10
