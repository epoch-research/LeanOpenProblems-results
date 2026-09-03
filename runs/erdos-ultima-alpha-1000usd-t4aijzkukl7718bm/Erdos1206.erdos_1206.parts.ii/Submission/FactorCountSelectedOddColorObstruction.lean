import Submission.ExactFactorCountOddColorObstruction
import Submission.BoundedFactorCountDensity

/-! No positive-lower-density source selected only by factor count within the
squarefree integers coprime to 210 admits an odd edge-sum coloring. This is a
restricted obstruction and does not exclude ordinary proper coloring. -/
namespace Erdos1206.FactorCountSelectedOddColorObstruction

/-- Arbitrary selection of exact factor-count fibers. -/
def source (B : Set ℕ) : Set ℕ :=
  {n | Squarefree n ∧ Nat.Coprime n 210 ∧ n.primeFactors.card ∈ B}

/-- Changing from parity to any other rule on the factor count cannot repair
the odd edge-sum criterion on a positive-density source of this form. -/
theorem no_odd_coloring_of_positive_density (B : Set ℕ)
    (hden : 0 < (source B).lowerDensity) :
    ¬ ∃ c : ℕ → ZMod 2, ∀ a b d e : ℕ,
      a ∈ source B → b ∈ source B → d ∈ source B → e ∈ source B →
      a < b → b < d → d < e → a^3+e^3=b^3+d^3 →
      c a+c b+c d+c e=1 := by
  rintro ⟨c,hc⟩
  obtain ⟨n,hn,hcount⟩ := BoundedFactorCountDensity.exists_large_count
    (fun n hn => Nat.pos_of_ne_zero hn.1.ne_zero) hden 7
  have hsub {m : ℕ} (hm : m ∈ ExactFactorCountOddColorObstruction.source n.primeFactors.card) :
      m ∈ source B := by
    refine ⟨hm.1, hm.2.1, ?_⟩
    rw [hm.2.2]
    exact hn.2.2
  apply ExactFactorCountOddColorObstruction.no_odd_coloring_exact_count
    n.primeFactors.card (by omega)
  refine ⟨c, ?_⟩
  intro a b d e ha hb hd he hab hbd hde heq
  exact hc a b d e (hsub ha) (hsub hb) (hsub hd) (hsub he) hab hbd hde heq

#print axioms no_odd_coloring_of_positive_density
end Erdos1206.FactorCountSelectedOddColorObstruction
