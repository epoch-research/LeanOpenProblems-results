import Submission.Work

/-! Energy minimization restricted to even roots. This does not assert that
an even-rooted lollipop can be replaced by a whole cycle. -/
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
namespace Erdos583EvenRootEnergyDevelopment
open scoped Classical
set_option maxHeartbeats 1600000
set_option Elab.async false

lemma exists_minimum_even_root_energy {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V)
    (hr : HasRoot T r) (he : Even (T.quota r)) :
    ∃ (S : TrailFamily G k) (s : V), S.score=T.score ∧ HasRoot S s ∧
      Even (S.quota s) ∧
      ∀ (U : TrailFamily G k) (u : V), U.score=S.score → HasRoot U u →
        Even (U.quota u) → RootEnergy.quotaEnergy S ≤ RootEnergy.quotaEnergy U := by
  classical
  let P (m : ℕ) := ∃ (S : TrailFamily G k) (s : V), S.score=T.score ∧
    HasRoot S s ∧ Even (S.quota s) ∧ RootEnergy.quotaEnergy S=m
  have hex : ∃ m, P m := ⟨RootEnergy.quotaEnergy T,T,r,rfl,hr,he,rfl⟩
  obtain ⟨S,s,hSs,hSr,hSe,hSE⟩ := Nat.find_spec hex
  refine ⟨S,s,hSs,hSr,hSe,?_⟩
  intro U u hUs hUr hUe
  rw [hSE]
  exact Nat.find_min' hex ⟨U,u,hUs.trans hSs,hUr,hUe,rfl⟩

lemma even_root_quota_eq_two_of_minimum {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hr : HasRoot T r) (he : Even (T.quota r))
    (hmin : ∀ (U : TrailFamily G k) (u : V), U.score=T.score → HasRoot U u →
      Even (U.quota u) → RootEnergy.quotaEnergy T ≤ RootEnergy.quotaEnergy U) :
    T.quota r=2 := by
  have hpos := RootEnergy.root_quota_pos hr
  have htwo : 2 ≤ T.quota r := by obtain ⟨a,ha⟩ := he; omega
  by_contra hne
  have hlarge : 3 ≤ T.quota r := by omega
  obtain ⟨A,R,ρ,hρ,hn⟩ := hr
  obtain ⟨B,_,x,_,_,hrx,_,hxB,_,hEx,_⟩ := R.two_root_exposures ρ hρ hn
  have hx : T.quota x=0 := RootEnergy.exposed_quota_zero hEx hs hm hxB
  obtain ⟨U,hUq,hU⟩ := exposedRoot_move_pair_or_repair hEx hs htwo
  rcases hU with hp | ⟨hUs,hUr⟩
  · exact RootEnergy.maximum_defect_no_paths T hs hm U hp
  · have hUx : U.quota x=2 := by
      have hbal := hUq x
      simp only [if_neg hrx.ne,mul_zero,add_zero,hx,zero_add] at hbal
      exact hbal
    have hb := hmin U x hUs hUr (by rw [hUx]; decide)
    have hE := RootEnergy.pair_energy_balance T.quota U.quota r x hrx.ne hx hUq
    change RootEnergy.quotaEnergy U+4*T.quota r=RootEnergy.quotaEnergy T+8 at hE
    omega

/-- An even root remains even when minimizing root energy over even roots.
The unrestricted minimization in `RootEnergy` does not supply this assertion. -/
lemma exists_quota_two_root {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hr : HasRoot T r) (he : Even (T.quota r)) :
    ∃ (S : TrailFamily G k) (s : V), S.score=T.score ∧ HasRoot S s ∧
      S.quota s=2 ∧
      (∀ U : TrailFamily G k, U.score ≤ S.score) ∧
      ∀ (U : TrailFamily G k) (u : V), U.score=S.score → HasRoot U u →
        Even (U.quota u) → RootEnergy.quotaEnergy S ≤ RootEnergy.quotaEnergy U := by
  obtain ⟨S,s,hSs,hSr,hSe,hmin⟩ := exists_minimum_even_root_energy T r hr he
  have hSm (U : TrailFamily G k) : U.score ≤ S.score := by rw [hSs]; exact hm U
  have hq := even_root_quota_eq_two_of_minimum S s (by omega) hSm hSr hSe hmin
  exact ⟨S,s,hSs,hSr,hq,hSm,hmin⟩

/-- An even-even nonbridge in an edge-critical failure supplies an even root
with quota exactly two, without switching to an odd root during minimization. -/
lemma even_even_edge_quota_two_root {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ}
    (hmin : EdgeCritical.EdgeMinimal G k) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    {u v : V} (h : G.Adj v u)
    (hu : Even (Nat.card (G.neighborSet u)))
    (hv : Even (Nat.card (G.neighborSet v))) (hnb : ¬G.IsBridge s(v,u)) :
    ∃ (T : TrailFamily G k) (r : V), T.score+1=G.edgeSet.ncard+k ∧ HasRoot T r ∧
      T.quota r=2 ∧ Even (Nat.card (G.neighborSet r)) ∧
      (∀ U : TrailFamily G k, U.score ≤ T.score) ∧
      ∀ (U : TrailFamily G k) (s : V), U.score=T.score → HasRoot U s →
        Even (U.quota s) → RootEnergy.quotaEnergy T ≤ RootEnergy.quotaEnergy U := by
  obtain ⟨S,hs,hr,hm⟩ := hmin.root_at_other_endpoint hG hfail h hu hnb
  obtain ⟨T,r,hTs,hTr,hTq,hTm,hTe⟩ := exists_quota_two_root S v hs hm hr
    ((QuotaParity.quota_even_iff S v).mpr hv)
  exact ⟨T,r,by omega,hTr,hTq,(QuotaParity.quota_even_iff T r).mp (by rw [hTq]; decide),hTm,hTe⟩

end Erdos583EvenRootEnergyDevelopment
