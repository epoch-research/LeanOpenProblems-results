import Submission.LongestEndpointLossObstruction

/-! The large-loss cone family has an explicit linear decomposition and is
not count-critical. Thus its loss obstruction is not a disproof of Erdos 184. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.LongestEndpointLossObstruction
open ConeEnvelopeLoss CountCritical CycleNumberSubmodularity
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

lemma succ_ne (r : ℕ) (i : Fin (r+3)) : i+1 ≠ i := by
  intro hh
  have h1 : (1 : Fin (r+3)) = 0 := by simpa using add_left_cancel (show i+1=i+0 by simpa using hh)
  have hv := congrArg Fin.val h1
  simp at hv

lemma no_two_step (r : ℕ) (i : Fin (r+3)) : i+1+1 ≠ i := by
  intro hh
  have h1 : (2 : Fin (r+3)) = 0 := by
    apply add_left_cancel (a := i)
    simpa [add_assoc] using hh
  have hv := congrArg Fin.val h1
  simp [Nat.mod_eq_of_lt (show 2 < r+3 by omega)] at hv

lemma ring_adj (r : ℕ) (i : Fin (r+3)) : (cycleGraph (r+3)).Adj i (i+1) := by
  apply cycleGraph_adj.mpr
  right
  simp

def fiveCycle (r : ℕ) (i : Fin (r+3)) : (fullCone (prism r)).Walk none none :=
  .cons (by trivial : (fullCone (prism r)).Adj none (some (i+1,false))) <|
  .cons (show (fullCone (prism r)).Adj (some (i+1,false)) (some (i,false)) from
    Or.inr ⟨rfl,(ring_adj r i).symm⟩) <|
  .cons (show (fullCone (prism r)).Adj (some (i,false)) (some (i,true)) from
    Or.inl ⟨rfl,by simp⟩) <|
  .cons (show (fullCone (prism r)).Adj (some (i,true)) (some (i+1,true)) from
    Or.inr ⟨rfl,ring_adj r i⟩) <|
  .cons (by trivial : (fullCone (prism r)).Adj (some (i+1,true)) none) .nil

lemma fiveCycle_cycle (r : ℕ) (i : Fin (r+3)) : (fiveCycle r i).IsCycle := by
  apply path_close_isCycle (fiveCycle r i).tail
  · rw [Walk.isPath_def]
    change [some (i+1,false),some (i,false),some (i,true),some (i+1,true),none].Nodup
    simp [Ne.symm (succ_ne r i)]
  · change 2 ≤ 4
    omega

lemma fiveCycle_disjoint (r : ℕ) (i j : Fin (r+3)) (hij : i ≠ j) :
    List.Disjoint (fiveCycle r i).edges (fiveCycle r j).edges := by
  have hrev : ¬(i+1=j ∧ j+1=i) := by
    rintro ⟨h₁,h₂⟩
    exact no_two_step r i (by rw [h₁,h₂])
  simp only [fiveCycle,Walk.edges_cons,Walk.edges_nil] at *
  simp [List.disjoint_left,Prod.mk.injEq,hij]
  exact ⟨fun h₁ h₂ => hrev ⟨h₁,h₂.symm⟩,fun h₁ h₂ => hrev ⟨h₂,h₁.symm⟩⟩

lemma fiveCycle_cover (r : ℕ) (x y : Option (W r)) :
    (fullCone (prism r)).Adj x y ↔ ∃ i, s(x,y) ∈ (fiveCycle r i).edges := by
  constructor
  · intro hxy
    cases x with
    | none =>
      cases y with
      | none => exact hxy.elim
      | some y =>
        rcases y with ⟨j,b⟩
        refine ⟨j-1,?_⟩
        cases b <;> simp [fiveCycle]
    | some x =>
      cases y with
      | none =>
        rcases x with ⟨j,b⟩
        refine ⟨j-1,?_⟩
        cases b <;> simp [fiveCycle]
      | some y =>
        rcases x with ⟨i,b⟩
        rcases y with ⟨j,c⟩
        change (i=j ∧ b≠c) ∨ (b=c ∧ (cycleGraph (r+3)).Adj i j) at hxy
        rcases hxy with ⟨hij,hbc⟩ | ⟨hbc,ha⟩
        · subst j
          refine ⟨i,?_⟩
          cases b <;> cases c <;> simp_all [fiveCycle]
        · subst c
          rcases cycleGraph_adj.mp ha with h | h
          · have h' : j+1=i := by simpa [add_comm] using (sub_eq_iff_eq_add.mp h).symm
            refine ⟨j,?_⟩
            cases b <;> simp [fiveCycle,h']
          · have h' : i+1=j := by simpa [add_comm] using (sub_eq_iff_eq_add.mp h).symm
            refine ⟨i,?_⟩
            cases b <;> simp [fiveCycle,h']
  · rintro ⟨i,hi⟩
    exact ((fiveCycle r i).adj_of_mem_edges hi)

lemma prism_cone_number (r : ℕ) : cycleNumber (fullCone (prism r)) = r+3 := by
  apply cycleNumber_eq
  · have hh := upper_of_walk_family (fullCone (prism r))
      (fun i : Fin (r+3) => ⟨none,fiveCycle r i⟩)
      (fiveCycle_cycle r) (fiveCycle_disjoint r) (fiveCycle_cover r)
    simpa using hh
  · intro D hc hd
    have hh := cycle_decomposition_degree_lower (fullCone (prism r)) D hc hd none
    rw [degree_apex] at hh
    simp only [W,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hh
    omega

lemma prism_cone_not_all_optimal (r : ℕ) :
    ¬ MinimalCounterexample.AllCyclesOptimal (fullCone (prism r)) := by
  intro ho
  have he := cone_even_of_odd (prism r) (by simp [W]) (by
    intro x
    rw [prism_degree]
    decide)
  have hn : fullCone (prism r) ≠ ⊥ := by
    intro hh
    have hd := degree_apex (prism r)
    rw [hh] at hd
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hd
    simp [W] at hd
  obtain ⟨D,hc,hd,hcard⟩ := minimum_exists (fullCone (prism r)) he
  have ht : (fullCone (prism r)).degree none = 2*D.card := by
    rw [degree_apex,hcard,prism_cone_number]
    simp [W,mul_comm]
  obtain ⟨v,hv⟩ := DegreeTightOptimal.all_optimal_degree_tight_has_degree_two
    he hn ho D hc hd none ht
  cases v with
  | none =>
    rw [degree_apex] at hv
    simp only [W,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hv
    omega
  | some x =>
    rw [degree_old,prism_degree] at hv
    omega

lemma prism_cone_not_critical (r k : ℕ) :
    ¬ IsCountCritical k (fullCone (prism r)) := by
  intro hk
  exact prism_cone_not_all_optimal r hk.allCyclesOptimal

end Erdos184.LongestEndpointLossObstruction
