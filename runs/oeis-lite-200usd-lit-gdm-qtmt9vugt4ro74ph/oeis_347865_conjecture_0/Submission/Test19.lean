import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

mutual
  def MyType (n : Nat) : Type :=
    if n < 745 then
      Unit
    else if n = 745 then
      PLift (a 745 > 0)
    else
      PLift (a n > 0) ⊕ (PLift (a n = 0) × (a n = 0 → MyType (n - 1)) × PLift (a (n - 1) = 0 → False))

  def get_proof (n : Nat) (hn : n ≥ 745) (x : MyType n) : a n = 0 → False := by
    unfold MyType at x
    split at x
    · omega
    · split at x
      · rename_i h_eq
        subst h_eq
        intro h_eq_hyp
        have h_pos := x.down
        omega
      · rcases x with val | ⟨⟨h_eq⟩, h_rec, ⟨h_impl⟩⟩
        · intro h_eq_hyp
          have h_pos := val.down
          omega
        · intro h_eq_hyp
          have hn_sub : n - 1 ≥ 745 := by omega
          have x' := h_rec h_eq_hyp
          have p_sub := get_proof (n - 1) hn_sub x'
          exact p_sub
end
termination_by
  MyType n => n
  get_proof n hn x => n
decreasing_by omega
