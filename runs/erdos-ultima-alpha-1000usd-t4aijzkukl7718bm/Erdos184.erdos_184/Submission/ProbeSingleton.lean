import Submission.SingletonCycleExchange
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SingletonExchange
open Critical MaximumCycles Subfamilies
variable {V : Type*} [Fintype V]
def Optimal (G F : SimpleGraph V) : Prop :=
  F ≤ G ∧ (∀ v, Even (Nat.card ((G \ F).neighborSet v))) ∧
    number (G \ F) + Nat.card F.edgeSet = number G
def Best (G F : SimpleGraph V) : Prop :=
  Optimal G F ∧ ∀ R, Optimal G R → Nat.card F.edgeSet ≤ Nat.card R.edgeSet
end Erdos184Work.SingletonExchange
