import Submission.PairedBound
import Submission.PairedMates

/-!
# Polynomial bound for coherent paired systems

Coherent prime-wise paired classes provide both a consistent orientation
and the capacity-five mates required by the abstract matrix estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos126Aux.Paired

variable {ι τ P : Type*} [Fintype ι] [Fintype τ] [Fintype P] [DecidableEq P]

/-- The finite matrix estimate with its orientation and mate hypotheses
replaced by prime-wise coherent laminarity. -/
theorem polynomial_bound_of_coherent
    (b : τ → Block ι) (owner : τ → P)
    (hn : 2 ≤ Fintype.card ι) (hb : ∀ t, (b t).Valid)
    (hcnd : CND (crossSum b))
    (hoff : ∀ i j, i ≠ j → gramSum b i j < 0)
    (hcoh : ∀ p, Coherent b (Finset.univ.filter (fun t => owner t = p))) :
    (Fintype.card ι : ℝ) < 12 * (Fintype.card P : ℝ) ^ 2 := by
  classical
  have hs (p : P) := exists_orientation b
    (Finset.univ.filter (fun t => owner t = p)) (fun t _ => hb t) (hcoh p)
  choose sigma hsigma hleft hright using hs
  have hm (p : P) := exists_balanced_capacity_mate b
    (Finset.univ.filter (fun t => owner t = p)) 5 (by omega)
    (fun t _ => hb t) (hcoh p)
  choose mate hdegree hcover using hm
  apply polynomial_bound_of_filter_card b owner hn hb hcnd hoff sigma hsigma
    (fun t i hi => hleft (owner t) t (by simp) i hi)
    (fun t i hi => hright (owner t) t (by simp) i hi) mate hdegree
  intro p t howner hbal
  exact hcover p t (by simp [howner]) hbal

end Erdos126Aux.Paired
