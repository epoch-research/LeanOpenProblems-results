import FormalConjectures.Util.ProblemImports
open List Nat Filter Real

noncomputable def A330731 : ℕ → ℕ
| n =>
  let S : List ℕ := List.ofFn (fun i : Fin n => A330731 i.val)
  let count_sublist (P S : List ℕ) : ℕ :=
    (List.tails S).countP (fun l => P.isPrefixOf l)
  let rec check_tail (L_len : ℕ) : Option ℕ :=
    match L_len with
    | 0 => none
    | L' + 1 =>
      let L := L' + 1
      let T := S.drop (n - L)
      let P0 := T ++ [0]
      let P1 := T ++ [1]
      let N0 := count_sublist P0 S
      let N1 := count_sublist P1 S
      if N0 ≠ N1 then
        if N0 < N1 then some 0 else some 1
      else
        check_tail L'
  let max_L := n.pred
  match check_tail max_L with
  | some d => d
  | none =>
    let N0_empty := count_sublist [0] S;
    let N1_empty := count_sublist [1] S;
    if N0_empty ≠ N1_empty then
      if N0_empty < N1_empty then 0 else 1
    else
      0

noncomputable def OEIS_count_word (w : List ℕ) (N : ℕ) : ℕ :=
  if N ≥ w.length then
    let S := List.ofFn (fun i : Fin N => A330731 i.val);
    (List.tails S).countP (fun l => w.isPrefixOf l)
  else 0

noncomputable def A330731_asymptotic_freq (w : List ℕ) : Prop := False

def is_normal_A330731 : Prop :=
  ∀ (w : List ℕ), w.length > 0 ∧ (∀ x ∈ w, x = 0 ∨ x = 1) →
  A330731_asymptotic_freq w

theorem oeis_330731_conjecture_0 : is_normal_A330731 := by
  sorry

theorem oeis_330731_conjecture_0.disproof : ¬ (type_of% @oeis_330731_conjecture_0) := by
  intro h
  have hw : A330731_asymptotic_freq [0, 0, 0] := h [0, 0, 0] (by
    constructor
    · decide
    · intro x hx
      simp at hx
      subst hx
      left
      rfl
  )
  exact hw
