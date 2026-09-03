import Submission.CentralTripleCountsExplore
import Submission.NatPairAlgebraExplore

/-! Exact finite downward corrections and their central-triple collateral.
No infinite repair schedule is asserted. -/
namespace Erdos66CentralTripleDeletion
open AdditiveCombinatorics Erdos66CentralTripleCounts Erdos66Compactness Erdos66NatPairAlgebra
open scoped Classical
set_option maxHeartbeats 2200000

noncomputable def hits (A : Set ℕ) (D : Finset ℕ) (z : ℕ) : Finset ℕ :=
  D.filter (fun a ↦ a ≤ z ∧ z-a∈A)

lemma deletion_identity (A : Set ℕ) (D : Finset ℕ) (hD : (D : Set ℕ) ⊆ A) (z : ℕ) :
    sumRep A z + sumRep (D : Set ℕ) z =
      sumRep (A \ (D : Set ℕ)) z + 2*(hits A D z).card := by
  let L := max z (D.sup id)
  let Q := (Finset.range (L+1)).filter (fun a ↦ a∈A)
  have hzL : z ≤ L := le_max_left _ _
  have hDQ : D ⊆ Q := by
    intro a ha
    have hsup := Finset.le_sup (f := id) ha
    change a ≤ D.sup id at hsup
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := le_max_right z (D.sup id); dsimp only [L]; omega),hD ha⟩
  have hQ : sumRep (Q : Set ℕ) z=sumRep A z := sumRep_truncate A L z hzL
  have hQD : sumRep ((Q\D : Finset ℕ) : Set ℕ) z=sumRep (A\(D : Set ℕ)) z := by
    apply sumRep_congr_below
    intro a ha
    have haL : a<L+1 := by omega
    simp only [Finset.mem_coe,Finset.mem_sdiff,Q,Finset.mem_filter,Finset.mem_range,
      haL,true_and,Set.mem_diff]
  have hhits : pairs D Q z=(hits A D z).card := by
    rw [pairs_eq_filter]
    congr 1
    ext a
    simp only [hits,Finset.mem_filter,Q,Finset.mem_range]
    have haL : z-a<L+1 := by omega
    simp only [haL,true_and]
  have he : (Q\D)∪D=Q := Finset.sdiff_union_of_subset hDQ
  have hd : Disjoint (Q\D) D := Finset.sdiff_disjoint
  have hrep := sumRep_union_self (Q\D) D z hd
  rw [he,hQ,hQD] at hrep
  have hmix := pairs_union_right D (Q\D) D z hd
  rw [he,hhits,pairs_comm D (Q\D),pairs_self] at hmix
  omega

lemma deletion_loss_le (A : Set ℕ) (D : Finset ℕ) (hD : (D : Set ℕ) ⊆ A) (z : ℕ) :
    sumRep A z - sumRep (A\(D : Set ℕ)) z ≤ 2*(hits A D z).card := by
  have hh := deletion_identity A D hD z
  omega

noncomputable def endpoints (A : Set ℕ) (N n : ℕ) : Finset ℕ :=
  (Finset.range (n+1)).filter (fun a ↦ N ≤ a ∧ N ≤ n-a ∧ a∈A ∧ n-a∈A)

lemma mem_endpoints {A : Set ℕ} {N n a : ℕ} : a∈endpoints A N n ↔
    a ≤ n ∧ N ≤ a ∧ N ≤ n-a ∧ a∈A ∧ n-a∈A := by
  simp only [endpoints,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]

lemma endpoints_subset (A : Set ℕ) (N n : ℕ) : (endpoints A N n : Set ℕ) ⊆ A := by
  intro a ha
  exact (mem_endpoints.mp ha).2.2.2.1

lemma hits_subset_fiber (A : Set ℕ) (D : Finset ℕ) (N n z : ℕ)
    (hD : D ⊆ endpoints A N n) : hits A D z ⊆ fiber A N n z := by
  intro a ha
  obtain ⟨ha,haz,hza⟩ := Finset.mem_filter.mp ha
  obtain ⟨han,hNa,hNb,haA,hbA⟩ := mem_endpoints.mp (hD ha)
  exact mem_fiber.mpr ⟨han,hNa,hNb,haz,haA,hbA,hza⟩

lemma one_target_loss (A : Set ℕ) (D : Finset ℕ) (N n z : ℕ)
    (hD : D ⊆ endpoints A N n) :
    sumRep A z - sumRep (A\(D : Set ℕ)) z ≤ 2*(fiber A N n z).card := by
  have hh := deletion_loss_le A D (fun a ha ↦ endpoints_subset A N n (hD ha)) z
  exact hh.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card (hits_subset_fiber A D N n z hD)))

lemma many_target_loss (A : Set ℕ) (D T : Finset ℕ) (N : ℕ → ℕ) (z : ℕ)
    (hD : D ⊆ T.biUnion (fun n ↦ endpoints A (N n) n)) :
    sumRep A z - sumRep (A\(D : Set ℕ)) z ≤ 2*∑ n∈T, (fiber A (N n) n z).card := by
  have hDA : (D : Set ℕ) ⊆ A := by
    intro a ha
    obtain ⟨n,hn,ha⟩ := Finset.mem_biUnion.mp (hD ha)
    exact endpoints_subset A (N n) n ha
  have hsub : hits A D z ⊆ T.biUnion (fun n ↦ fiber A (N n) n z) := by
    intro a ha
    obtain ⟨ha,haz,hza⟩ := Finset.mem_filter.mp ha
    obtain ⟨n,hn,ha⟩ := Finset.mem_biUnion.mp (hD ha)
    obtain ⟨han,hNa,hNb,haA,hbA⟩ := mem_endpoints.mp ha
    exact Finset.mem_biUnion.mpr ⟨n,hn,mem_fiber.mpr ⟨han,hNa,hNb,haz,haA,hbA,hza⟩⟩
  have hc := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  exact (deletion_loss_le A D hDA z).trans (Nat.mul_le_mul_left 2 hc)

lemma many_target_uniform_loss (A : Set ℕ) (D T : Finset ℕ) (N : ℕ → ℕ) (z R : ℕ)
    (hD : D ⊆ T.biUnion (fun n ↦ endpoints A (N n) n))
    (hR : ∀ n∈T, (fiber A (N n) n z).card ≤ R) :
    sumRep A z - sumRep (A\(D : Set ℕ)) z ≤ 2*T.card*R := by
  have hs : (∑ n∈T, (fiber A (N n) n z).card) ≤ T.card*R := by
    calc
      _ ≤ ∑ _n∈T, R := Finset.sum_le_sum hR
      _ = _ := by simp
  have hh := many_target_loss A D T N z hD
  exact hh.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hs)

noncomputable def upperEndpoints (A : Set ℕ) (N n : ℕ) : Finset ℕ :=
  (endpoints A N n).filter (fun a ↦ n < 2*a)

lemma upper_target_exact (A : Set ℕ) (D : Finset ℕ) (N n : ℕ)
    (hD : D ⊆ upperEndpoints A N n) :
    sumRep A n = sumRep (A\(D : Set ℕ)) n + 2*D.card := by
  have hDE : D ⊆ endpoints A N n := hD.trans (Finset.filter_subset _ _)
  have hDA : (D : Set ℕ) ⊆ A := fun a ha ↦ endpoints_subset A N n (hDE ha)
  have hself : sumRep (D : Set ℕ) n=0 := by
    rw [←pairs_self,pairs,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
    intro p hp hp'
    obtain ⟨h1,h2⟩ := Finset.mem_product.mp hp
    have h1 := (Finset.mem_filter.mp (hD h1)).2
    have h2 := (Finset.mem_filter.mp (hD h2)).2
    omega
  have hhits : hits A D n=D := by
    apply Finset.filter_eq_self.mpr
    intro a ha
    have hh := mem_endpoints.mp (hDE ha)
    exact ⟨hh.1,hh.2.2.2.2⟩
  have hh := deletion_identity A D hDA n
  rwa [hself,hhits,Nat.add_zero] at hh

 theorem exists_exact_downward_correction (A : Set ℕ) (N n k : ℕ)
    (hk : k ≤ (upperEndpoints A N n).card) :
    ∃ D : Finset ℕ, D ⊆ upperEndpoints A N n ∧ D.card=k ∧
      sumRep A n = sumRep (A\(D : Set ℕ)) n+2*k ∧
      ∀ z, sumRep A z-sumRep (A\(D : Set ℕ)) z ≤ 2*(fiber A N n z).card := by
  obtain ⟨D,hD,hcard⟩ := Finset.exists_subset_card_eq hk
  refine ⟨D,hD,hcard,by simpa only [hcard] using upper_target_exact A D N n hD,?_⟩
  intro z
  exact one_target_loss A D N n z (hD.trans (Finset.filter_subset _ _))

end Erdos66CentralTripleDeletion
