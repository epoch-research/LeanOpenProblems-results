import FormalConjecturesUtil

/-! A local obstruction for quadratic fifth-power identities with target five.
This is not a bound for the unrestricted representation count. -/
namespace Erdos322Research.QuinticQuadraticMaximalResidue
open Polynomial
set_option maxHeartbeats 2000000
private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private theorem fifth_cases (x : ZMod 11) :
    x^5 = 0 ∨ x^5 = 1 ∨ x^5 = -1 := by
  fin_cases x <;> decide

private theorem maximal_sum (x : Fin 5 → ZMod 11)
    (h : ∑ i, (x i)^5 = 5) : ∀ i, (x i)^5 = 1 := by
  have h0 := fifth_cases (x 0)
  have h1 := fifth_cases (x 1)
  have h2 := fifth_cases (x 2)
  have h3 := fifth_cases (x 3)
  have h4 := fifth_cases (x 4)
  simp only [Fin.sum_univ_succ] at h
  change (x 0)^5 + ((x 1)^5 + ((x 2)^5 + ((x 3)^5 + ((x 4)^5 + 0)))) = 5 at h
  rcases h0 with h0 | h0 | h0 <;>
    rcases h1 with h1 | h1 | h1 <;>
    rcases h2 with h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3 <;>
    rcases h4 with h4 | h4 | h4
  all_goals norm_num [h0, h1, h2, h3, h4] at h
  all_goals first
    | exact False.elim ((by decide : ¬ _) h)
    | (intro i; fin_cases i <;> assumption)

/-- Every summand in a five-term quadratic identity with target five over
`ZMod 11` is constant. This includes all coefficient patterns. -/
theorem quadratic_constant (p : Fin 5 → (ZMod 11)[X])
    (hd : ∀ i, (p i).natDegree ≤ 2)
    (h : ∑ i, p i ^ 5 = 5) : ∀ i, (p i).natDegree = 0 := by
  intro i
  have heval (t : ZMod 11) : ∀ j, (eval t (p j))^5 = 1 := by
    apply maximal_sum
    have ht := congrArg (eval t) h
    simpa only [eval_finset_sum, eval_pow, eval_ofNat] using ht
  have hpow : p i ^ 5 = 1 := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (p i ^ 5) 1
      (f := fun t : ZMod 11 => t) Function.injective_id
    · intro t
      simpa using heval t i
    · simp only [natDegree_pow, natDegree_one, Nat.max_zero, ZMod.card]
      have hi := hd i
      omega
  have hdeg := congrArg natDegree hpow
  rw [natDegree_pow, natDegree_one] at hdeg
  omega

end Erdos322Research.QuinticQuadraticMaximalResidue
