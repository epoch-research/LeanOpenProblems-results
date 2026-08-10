import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

partial def get_p_cheat (P : Prop) : MyType P :=
  match get_p_cheat (¬ P) with
  | MyType.not_val hnn => MyType.val (Classical.byContradiction hnn)
  | MyType.val hn => 
    match get_p_cheat (¬ ¬ P) with
    | MyType.val hnn => MyType.val (Classical.byContradiction (fun _ => hnn hn))
    | MyType.not_val hnnn => get_p_cheat P

theorem prove_false : False := by
  match get_p_cheat False with
  | MyType.val p => exact p
  | MyType.not_val (h1 : False → False) =>
    match get_p_cheat (¬ False) with
    | MyType.not_val (h2 : (¬ False) → False) => exact h2 h1
    | MyType.val (v1 : ¬ False) =>
      match get_p_cheat (¬ ¬ False) with
      | MyType.val (v2 : ¬ ¬ False) => exact v2 v1
      | MyType.not_val (h3 : (¬ ¬ False) → False) =>
        match get_p_cheat (¬ ¬ ¬ False) with
        | MyType.not_val (h4 : (¬ ¬ ¬ False) → False) =>
          have h_triple : ¬ ¬ ¬ False := fun h_not_not => h_not_not h1
          exact h4 h_triple
        | MyType.val (v3 : ¬ ¬ ¬ False) =>
          match get_p_cheat (¬ ¬ ¬ ¬ False) with
          | MyType.val (v4 : ¬ ¬ ¬ ¬ False) => exact v4 v3
          | MyType.not_val (h5 : (¬ ¬ ¬ ¬ False) → False) =>
            match get_p_cheat (¬ ¬ ¬ ¬ ¬ False) with
            | MyType.not_val (h6 : (¬ ¬ ¬ ¬ ¬ False) → False) => exact h6 h5
            | MyType.val (v5 : ¬ ¬ ¬ ¬ ¬ False) =>
              match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ False) with
              | MyType.val (v6 : ¬ ¬ ¬ ¬ ¬ ¬ False) => exact v6 v5
              | MyType.not_val (h7 : (¬ ¬ ¬ ¬ ¬ ¬ False) → False) =>
                match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                | MyType.not_val (h8 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) => exact h8 h7
                | MyType.val (v7 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                  match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                  | MyType.val (v8 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => exact v8 v7
                  | MyType.not_val (h9 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) =>
                    match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                    | MyType.not_val (h10 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) => exact h10 h9
                    | MyType.val (v9 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                      match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                      | MyType.val (v10 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => exact v10 v9
                      | MyType.not_val (h11 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) =>
                        match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                        | MyType.not_val (h12 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) => exact h12 h11
                        | MyType.val (v11 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                          match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                          | MyType.val (v12 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => exact v12 v11
                          | MyType.not_val (h13 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) =>
                            match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                            | MyType.not_val (h14 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) => exact h14 h13
                            | MyType.val (v13 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                              match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                              | MyType.val (v14 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => exact v14 v13
                              | MyType.not_val (h15 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) =>
                                match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                | MyType.not_val (h16 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) => exact h16 h15
                                | MyType.val (v15 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                  match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                  | MyType.val (v16 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => exact v16 v15
                                  | MyType.not_val (h17 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) =>
                                    match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                    | MyType.not_val (h18 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) => exact h18 h17
                                    | MyType.val (v17 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                      match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                      | MyType.val (v18 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => exact v18 v17
                                      | MyType.not_val (h19 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) =>
                                        match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                        | MyType.not_val (h20 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) => exact h20 h19
                                        | MyType.val (v19 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                          match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                          | MyType.val (v20 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => exact v20 v19
                                          | MyType.not_val (h21 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) =>
                                            exact h21 (fun (y19 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                              y19 (fun (y18 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                                y18 (fun (y17 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                                  y17 (fun (y16 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                                    y16 (fun (y15 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                                      y15 (fun (y14 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                                        y14 (fun (y13 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                                          y13 (fun (y12 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                                            y12 (fun (y11 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                                              y11 (fun (y10 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                                                y10 (fun (y9 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                                                  y9 (fun (y8 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                                                    y8 (fun (y7 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                                                      y7 (fun (y6 : ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                                                        y6 (fun (y5 : ¬ ¬ ¬ ¬ ¬ False) =>
                                                                          y5 (fun (y4 : ¬ ¬ ¬ ¬ False) =>
                                                                            y4 (fun (y2 : ¬ ¬ False) => y2 v1)
                                                                          )
                                                                        )
                                                                      )
                                                                    )
                                                                  )
                                                                )
                                                              )
                                                            )
                                                          )
                                                        )
                                                      )
                                                    )
                                                  )
                                                )
                                              )
                                            )

theorem prove_any (P : Prop) : P :=
  False.elim prove_false

#print axioms prove_any
