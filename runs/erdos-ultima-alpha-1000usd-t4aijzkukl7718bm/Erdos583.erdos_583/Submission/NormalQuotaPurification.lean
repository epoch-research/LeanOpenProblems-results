import Submission.NormalForestRestoration

/-! Nil path slots can be purified at nonisolated vertices without losing
normal endpoint quotas. This is not an existence theorem for prescribed zeros. -/
namespace Erdos583NormalQuotaPurificationDevelopment
open SimpleGraph Erdos583Work Erdos583NormalForestRestorationDevelopment
open Erdos583Work.QuotaTrails Erdos583Work.EndpointSelection Erdos583Work.PendantCompletion
open scoped Classical
set_option maxHeartbeats 1600000

lemma path_family_partition_quota_exact {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hsupp : ∀ x, x ∈ G.support)
    (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath) (hb : ∀ x, T.quota x ≤ 2) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card=k ∧
      (∀ H ∈ D, H.edgeSet.Nonempty) ∧ ∀ x, endpointMultiplicity D x=T.quota x := by
  classical
  obtain ⟨D,hD,_,hne,hq⟩ := path_family_partition_quota_le T hp
  let A := Finset.univ.filter fun x ↦ T.quota x=0
  have hA : A ⊆ inactive D := by
    intro x hx
    have hz := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by have := hq x; omega⟩
  obtain ⟨E,hE,hEne,hEb,hEi,_⟩ := realize_subset hsupp hD hne
    (fun x ↦ (hq x).trans (hb x)) A hA
  have hEq (x : V) : endpointMultiplicity E x=T.quota x := by
    have hz : endpointMultiplicity E x=0 ↔ T.quota x=0 := by
      have hh := congrArg (fun S : Finset V ↦ x ∈ S) hEi
      simpa only [inactive,A,Finset.mem_filter,Finset.mem_univ,true_and] using Iff.of_eq hh
    have hpar : Odd (endpointMultiplicity E x) ↔ Odd (T.quota x) := by
      rw [hE.odd_endpointMultiplicity_iff,QuotaParity.quota_odd_iff]
      simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
    have h1 := hEb x
    have h2 := hb x
    simp only [Nat.odd_iff] at hpar
    omega
  have hcard : E.card=k := by
    have hh := hE.sum_endpointMultiplicity hEne
    simp_rw [hEq] at hh
    rw [RootEnergy.sum_quota] at hh
    omega
  exact ⟨E,hE,hcard,hEne,hEq⟩

end Erdos583NormalQuotaPurificationDevelopment
