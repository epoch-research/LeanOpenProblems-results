import FormalConjecturesUtil
import Submission.ThetaClusterMoments
import Submission.ConditionalThetaWeighted

/-! A square-root degree bound IF every row link has a cluster light graph.
The additional partition property is not inferred from pattern-freeness. -/
open Finset SimpleGraph
open scoped Classical
namespace Erdos713ThetaClusterLinks
open Erdos713ThetaCluster Erdos713GlobalLight Erdos713GlobalTheta
open Erdos713ConditionalThetaWeighted Erdos713ThetaHeavyShadow Erdos713ThetaCross
set_option maxHeartbeats 2000000

lemma degree_numeric {n d e : ℕ} (hd : d ≤ n) (hde : d*(d-1) ≤ e)
    (he : e^2 ≤ 98*n^2) : d^2 ≤ 11*n := by
  by_cases hd0 : d = 0
  · simp [hd0]
  have hd1 : 1 ≤ d := by omega
  have hpow := (Nat.pow_le_pow_left hde 2).trans he
  have hh : d*(d-1) ≤ 10*n := by
    by_contra hn
    have hg : 10*n+1 ≤ d*(d-1) := by omega
    have hp := Nat.pow_le_pow_left hg 2
    nlinarith only [hp.trans hpow,Nat.zero_le n,Nat.zero_le (n^2)]
  have hsub : d-1+1 = d := Nat.sub_add_cancel hd1
  nlinarith only [hh,hd,hsub]

def ClusterLinks {A B : Type*} (R : A → B → Prop) : Prop :=
  ∀ a : A, ∃ τ : {b : B // R a b} → ℕ,
    CrossHeavy (link R a) τ ∧ SameLight (link R a) τ

lemma degree_of_selected {n d : ℕ} (R : Fin n → Fin n → Prop) (a : Fin n)
    (hFree : pattern.Free (Erdos713C6.bipGraph R))
    (τ : {b : Fin n // R a b} → ℕ) (hH : CrossHeavy (link R a) τ)
    (hL : SameLight (link R a) τ) (ht' : lightCount (link R a) ≤ 3*n)
    (hrows : ∀ a, d ≤ Nat.card {b // R a b})
    (hcols : ∀ b, d ≤ Nat.card {a // R a b}) : d^2 ≤ 11*n := by
  let E := ∑ x : {x : Fin n // x ≠ a}, (row (link R a) x).card
  let M := Fintype.card {x : Fin n // x ≠ a}
  have hM : M ≤ n := by
    exact (Fintype.card_le_of_injective (fun x : {x : Fin n // x ≠ a} => x.val)
      Subtype.val_injective).trans_eq (Fintype.card_fin n)
  have hE : E^2 ≤ 98*n^2 := by
    have hh := incidence_square_le (no_theta_links hFree a) hH hL
    change E^2 ≤ 26*M^2+24*M*lightCount (link R a) at hh
    calc
      _ ≤ 26*M^2+24*M*lightCount (link R a) := hh
      _ ≤ 26*n^2+24*n*(3*n) := Nat.add_le_add
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM 2))
        (Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) ht')
      _ = 98*n^2 := by ring
  have hLower : d*(d-1) ≤ E := by
    have hh := link_incidence_lower R a d (hrows a) hcols
    rw [Erdos713ThetaSplit.edge_card_eq_rows] at hh
    simpa only [E,row,Nat.card_eq_fintype_card,Fintype.card_subtype] using hh
  have hdn : d ≤ n := by
    apply (hrows a).trans
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
      (fun b : {b : Fin n // R a b} => b.val) Subtype.val_injective
  exact degree_numeric hdn hLower hE

lemma degree_square_le {n d : ℕ} (hn : 0 < n) (R : Fin n → Fin n → Prop)
    (hFree : pattern.Free (Erdos713C6.bipGraph R)) (hCluster : ClusterLinks R)
    (hrows : ∀ a, d ≤ Nat.card {b // R a b})
    (hcols : ∀ b, d ≤ Nat.card {a // R a b}) : d^2 ≤ 11*n := by
  haveI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨a,ha⟩ := exists_row_with_few_light_pairs R 3
  simp only [Fintype.card_fin] at ha
  have ht : (lightPairs R 3 a).card ≤ 3*n := by
    have ht' : n*(lightPairs R 3 a).card ≤ n*(3*n) := by nlinarith only [ha]
    exact Nat.le_of_mul_le_mul_left ht' hn
  have ht' : lightCount (link R a) ≤ 3*n := by rw [link_lightCount]; exact ht
  obtain ⟨τ,hH,hL⟩ := hCluster a
  exact degree_of_selected R a hFree τ hH hL ht' hrows hcols

#print axioms degree_numeric
#print axioms degree_of_selected
#print axioms degree_square_le
end Erdos713ThetaClusterLinks
