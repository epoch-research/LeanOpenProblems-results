import FormalConjectures.Util.ProblemImports

open Nat Finset List

-- Let's define the variables and see if we can prove the inequality
lemma growth_rate_bound (n q p_r : ℕ) (qs ms : List ℕ)
    (hn : ¬ n ≤ 1) (h_sp : n.factorization.support.sort (· ≤ ·) = q :: qs)
    (h_qs_eq : qs = ms ++ [p_r]) (h_eq : a067599 n = n) :
    let e_r := n.factorization p_r
    let K := ms.length + 1
    p_r^(e_r - 1) < 110 * 100^K * e_r := by
  sorry
