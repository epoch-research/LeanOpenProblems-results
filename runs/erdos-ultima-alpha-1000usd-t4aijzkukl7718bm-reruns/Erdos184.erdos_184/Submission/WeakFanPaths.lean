import Submission.FanPaths

/-! A fan only needs some reachable surviving target after each small deletion. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.FanPaths
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
set_option maxHeartbeats 800000

lemma fan_of_reaches_set (S : Set V) {a : V} (ha : a ∉ S) (k : ℕ)
    (hconn : ∀ T : Set V, T.ncard < k → (haT : a ∉ T) →
      ∃ b ∈ S, ∃ hbT : b ∉ T, (G.induce Tᶜ).Reachable ⟨a,haT⟩ ⟨b,hbT⟩) :
    ∃ w : Fin k → V, ∃ p : ∀ i, G.Walk a (w i),
      Function.Injective w ∧ (∀ i, w i ∈ S) ∧ (∀ i, (p i).IsPath) ∧
      (∀ i j, i ≠ j → ∀ x, x ∈ (p i).support → x ∈ (p j).support → x = a) ∧
      (∀ i x, x ∈ (p i).support → x ∈ S → x = w i) := by
  have hcone : ∀ T : Set (Option V), T.ncard < k →
      (haT : some a ∉ T) → (hnT : none ∉ T) →
      ((cone G S).induce Tᶜ).Reachable ⟨some a,haT⟩ ⟨none,hnT⟩ := by
    intro T hT haT hnT
    let U : Set V := Option.some ⁻¹' T
    have hU : U.ncard < k :=
      (Set.ncard_le_ncard_of_injOn Option.some (fun _ hx => hx)
        (Option.some_injective V).injOn).trans_lt hT
    have haU : a ∉ U := haT
    obtain ⟨b,hb,hbU,hr⟩ := hconn U hU haU
    let f : G.induce Uᶜ →g (cone G S).induce Tᶜ := {
      toFun := fun x => ⟨some x.val,x.property⟩
      map_rel' := fun h => h }
    have hr := hr.map f
    have hadj : ((cone G S).induce Tᶜ).Adj (f ⟨b,hbU⟩) ⟨none,hnT⟩ := hb
    exact hr.trans hadj.reachable
  obtain ⟨p,hp,_,hi⟩ := MengerMatching.exists_internally_disjoint_paths
    (G := cone G S) (k := k) (u := some a) (v := none) (by simp) ha hcone
  have hex : ∀ i : Fin k, ∃ w ∈ S, ∃ q : G.Walk a w, q.IsPath ∧
      (∀ x, x ∈ q.support → some x ∈ (p i).support) ∧
      (∀ x, x ∈ q.support → x ∈ S → x = w) := by
    intro i
    obtain ⟨b,hb,q,hq,hsub⟩ := path_to_apex (p i) (hp i)
    obtain ⟨w,hw,r,hr,hrq,hfirst⟩ := first_hit_path S q hq hb
    exact ⟨w,hw,r,hr,fun x hx => hsub x (hrq hx),hfirst⟩
  choose w hw q hq hsub hfirst using hex
  have hmeet : ∀ i j, i ≠ j → ∀ x, x ∈ (q i).support → x ∈ (q j).support → x = a := by
    intro i j hij x hxi hxj
    have hh := hi i j hij (some x) (hsub i x hxi) (hsub j x hxj)
    simpa only [Option.some.injEq,Option.some_ne_none,or_false] using hh
  refine ⟨w,q,?_,hw,hq,hmeet,hfirst⟩
  intro i j hij
  by_contra hn
  have hx : w i = a := hmeet i j hn (w i) (q i).end_mem_support
    (by rw [hij]; exact (q j).end_mem_support)
  exact ha (hx ▸ hw i)


end Erdos184.FanPaths
