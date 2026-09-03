import Submission.Work
set_option maxHeartbeats 1000000
lemma test_recovery (p : Fin 7 → Fin 7) (hp : (List.ofFn p).Nodup) : True := by
  classical
  let fromList (a b : Fin 7) (l : List (Fin 7)) (i : Fin 7) : Fin 7 := (a::b::l).getD i.val 0
  have hperm : List.Perm (List.ofFn p) ([0,1,2,3,4,5,6] : List (Fin 7)) := by
    apply (List.perm_ext_iff_of_nodup hp (by decide)).mpr
    intro x
    constructor
    · intro _; fin_cases x <;> decide
    · intro _
      exact List.mem_ofFn.mpr ((Finite.injective_iff_surjective.mp (List.nodup_ofFn.mp hp)) x)
  let q : Fin 5 → Fin 7 := fun i ↦ p i.succ.succ
  have hmem : List.ofFn q ∈ ((([0,1,2,3,4,5,6] : List (Fin 7)).erase (p 0)).erase (p 1)).permutations' := by
    apply List.mem_permutations'.mpr
    have he := (hperm.erase (p 0)).erase (p 1)
    rw [List.ofFn_succ,List.erase_cons_head,List.ofFn_succ] at he
    simp only [show (0 : Fin 6).succ=(1 : Fin 7) by rfl,List.erase_cons_head] at he
    exact he
  have he : fromList (p 0) (p 1) (List.ofFn q)=p := by
    funext i
    fin_cases i <;> rfl
  have h01 : p 0 ≠ p 1 := fun hh ↦ (by decide : (0 : Fin 7) ≠ 1) (List.nodup_ofFn.mp hp hh)
  trivial
