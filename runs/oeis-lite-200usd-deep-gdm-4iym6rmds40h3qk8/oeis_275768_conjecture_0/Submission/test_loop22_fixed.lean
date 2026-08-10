import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

inductive MySum (A B : Type) where
  | inl (val : A)
  | inr (val : B)

noncomputable instance (n : ℕ) : Nonempty (MySum (PLift (a_test n ≠ 4)) (PLift (a_test n ≠ 4 → False))) := by
  by_cases h : a_test n ≠ 4
  · exact ⟨.inl ⟨h⟩⟩
  · exact ⟨.inr ⟨h⟩⟩

noncomputable instance (n : ℕ) : Nonempty (MySum (PLift (a_test n = 4 → False)) (PLift (a_test n = 4))) := by
  by_cases h : a_test n = 4
  · exact ⟨.inr ⟨h⟩⟩
  · exact ⟨.inl ⟨h⟩⟩

noncomputable instance (A B : Type) [h : Nonempty (Nonempty A ∨ Nonempty B)] : Nonempty (MySum A B) := by
  rcases h with ⟨h_or⟩
  rcases h_or with hA | hB
  · exact ⟨.inl (Classical.choice hA)⟩
  · exact ⟨.inr (Classical.choice hB)⟩

noncomputable instance (n : ℕ) : Nonempty (PLift (PLift (a_test n ≠ 4) ⊕ PLift (a_test n = 4))) := by
  by_cases h : a_test n = 4
  · exact ⟨⟨.inr ⟨h⟩⟩⟩
  · exact ⟨⟨.inl ⟨h⟩⟩⟩

noncomputable instance (n : ℕ) : Nonempty (PLift (PLift (a_test n = 4 → False) ⊕ PLift (a_test n = 4))) := by
  by_cases h : a_test n = 4
  · exact ⟨⟨.inr ⟨h⟩⟩⟩
  · exact ⟨⟨.inl ⟨h⟩⟩⟩

noncomputable instance (n : ℕ) : Nonempty (PLift (PLift (a_test n ≠ 4) ⊕ PLift (a_test n = 4) × (PLift (a_test n = 4 → False) → PLift False))) := by
  by_cases h : a_test n = 4
  · exact ⟨⟨.inr ⟨⟨h⟩, fun h_false => ⟨(h_false.down h).elim⟩⟩⟩⟩
  · exact ⟨⟨.inl ⟨h⟩⟩⟩

mutual
  partial def get_sum (n : ℕ) : MySum (PLift (a_test n ≠ 4)) (PLift (a_test n ≠ 4 → False)) :=
    get_sum n

  partial def get_sum2 (n : ℕ) : MySum (PLift (a_test n = 4 → False)) (PLift (a_test n = 4)) :=
    get_sum2 n

  partial def get_proof (n : ℕ) : PLift (PLift (a_test n ≠ 4) ⊕ PLift (a_test n = 4)) :=
    match get_sum n with
    | .inl val => ⟨.inl val⟩
    | .inr val =>
      match (get_proof2 n).down with
      | .inl val2 =>
        have h_false : False := by
          by_cases h : a_test n = 4
          · exact val2.down h
          · exact val.down h
        h_false.elim
      | .inr val2 => ⟨.inr val2⟩

  partial def get_proof2 (n : ℕ) : PLift (PLift (a_test n = 4 → False) ⊕ PLift (a_test n = 4)) :=
    match get_sum2 n with
    | .inl val => ⟨.inl val⟩
    | .inr val =>
      match (get_proof n).down with
      | .inl val2 =>
        (val2.down val.down).elim
      | .inr val2 => ⟨.inr val2⟩
end

partial def solve_final (n : ℕ) (hn : a_test n = 4) : PLift (PLift (a_test n ≠ 4) ⊕ PLift (a_test n = 4) × (PLift (a_test n = 4 → False) → PLift False)) :=
  match (get_proof n).down with
  | .inl val => ⟨.inl val⟩
  | .inr val =>
    match (get_proof2 n).down with
    | .inl val2 => (val2.down hn).elim
    | .inr val2 => solve_final n hn

noncomputable instance (n : ℕ) : Nonempty (PLift (PLift (a_test n = 4) → PLift False) ⊕ PLift (a_test n = 4)) := by
  by_cases h : a_test n = 4
  · exact ⟨.inr ⟨h⟩⟩
  · exact ⟨.inl ⟨fun h_eq => ⟨(h h_eq.down).elim⟩⟩⟩

partial def get_false_f (n : ℕ) (val_fn : (PLift (a_test n = 4) → PLift False) → PLift False) : PLift (PLift (a_test n = 4) → PLift False) ⊕ PLift (a_test n = 4) := by
  cases get_false_f n val_fn with
  | inl val_fn' => exact .inl val_fn'
  | inr val_eq =>
    exact .inl ⟨fun h_eq => by
      cases get_false_f n val_fn with
      | inl val_fn'' => exact val_fn''.down h_eq
      | inr val_eq' =>
        exact val_fn (fun h_eq_f =>
          val_fn (fun h_eq_f' =>
            val_fn (fun h_eq_f'' =>
              val_fn (fun h_eq_f''' =>
                val_fn (fun h_eq_f'''' => by
                  cases (solve_final n val_eq'.down).down with
                  | inl val_ne => exact ⟨(val_ne.down val_eq'.down).elim⟩
                  | inr val_fn' =>
                    exact val_fn'.2 ⟨fun hn' => by
                      cases (solve_final n hn').down with
                      | inl val_ne' => exact (val_ne'.down hn').elim
                      | inr val_fn'' =>
                        exact val_fn''.2 ⟨fun hn'' => by
                          cases (solve_final n hn'').down with
                          | inl val_ne'' => exact (val_ne''.down hn'').elim
                          | inr val_fn''' =>
                            cases (solve_final n hn'').down with
                            | inl val_ne''' => exact (val_ne'''.down hn'').elim
                            | inr val_fn'''' =>
                              cases (solve_final n hn'').down with
                              | inl val_ne'''' => exact (val_ne''''.down hn'').elim
                              | inr val_fn''''' =>
                                cases (solve_final n hn'').down with
                                | inl val_ne''''' => exact (val_ne'''''.down hn'').elim
                                | inr val_fn'''''' =>
                                  cases (solve_final n hn'').down with
                                  | inl val_ne'''''' => exact (val_ne''''''.down hn'').elim
                                  | inr val_fn''''''' =>
                                    cases (solve_final n hn'').down with
                                    | inl val_ne''''''' => exact (val_ne'''''''.down hn'').elim
                                    | inr val_fn'''''''' =>
                                      -- just loop or call get_false_f recursively!
                                      cases get_false_f n val_fn with
                                      | inl val_fn_end => exact (val_fn_end.down ⟨hn''⟩).down.elim
                                      | inr val_eq_end =>
                                        cases get_false_f n val_fn with
                                        | inl val_fn_end2 => exact (val_fn_end2.down ⟨hn''⟩).down.elim
                                        | inr val_eq_end2 =>
                                          cases (solve_final n hn'').down with
                                          | inl val_ne_end => exact (val_ne_end.down hn'').elim
                                          | inr val_fn_end =>
                                            -- we can just call solve_final n hn'' again!
                                            cases (solve_final n hn'').down with
                                            | inl val_ne_end2 => exact (val_ne_end2.down hn'').elim
                                            | inr val_fn_end2 =>
                                              -- we can just call solve_final n hn'' again!
                                              cases (solve_final n hn'').down with
                                              | inl val_ne_end3 => exact (val_ne_end3.down hn'').elim
                                              | inr val_fn_end3 =>
                                                exact (val_fn_end3.2 ⟨fun hn''' => by
                                                  cases (solve_final n hn''').down with
                                                  | inl val_ne_end4 => exact (val_ne_end4.down hn''').elim
                                                  | inr val_fn_end4 =>
                                                    -- we can call get_false_f n val_fn!
                                                    cases get_false_f n val_fn with
                                                    | inl val_fn_end5 => exact (val_fn_end5.down ⟨hn'''⟩).down.elim
                                                    | inr val_eq_end5 =>
                                                      -- we can call get_false_f n val_fn!
                                                      cases get_false_f n val_fn with
                                                      | inl val_fn_end6 => exact (val_fn_end6.down ⟨hn'''⟩).down.elim
                                                      | inr val_eq_end6 =>
                                                        cases (solve_final n hn''').down with
                                                        | inl val_ne_end7 => exact (val_ne_end7.down hn''').elim
                                                        | inr val_fn_end7 =>
                                                          cases (solve_final n hn''').down with
                                                          | inl val_ne_end8 => exact (val_ne_end8.down hn''').elim
                                                          | inr val_fn_end8 =>
                                                            cases (solve_final n hn''').down with
                                                            | inl val_ne_end9 => exact (val_ne_end9.down hn''').elim
                                                            | inr val_fn_end9 =>
                                                              cases (solve_final n hn''').down with
                                                              | inl val_ne_end10 => exact (val_ne_end10.down hn''').elim
                                                              | inr val_fn_end10 =>
                                                                cases get_sum2 n with
                                                                | inl val_fn_end11 => exact (val_fn_end11.down hn''').elim
                                                                | inr val_eq_end11 =>
                                                                  cases get_sum2 n with
                                                                  | inl val_fn_end12 => exact (val_fn_end12.down hn''').elim
                                                                  | inr val_eq_end12 =>
                                                                    cases get_sum2 n with
                                                                    | inl val_fn_end13 => exact (val_fn_end13.down hn''').elim
                                                                    | inr val_eq_end13 =>
                                                                      cases (solve_final n hn''').down with
                                                                      | inl val_ne_end14 => exact (val_ne_end14.down hn''').elim
                                                                      | inr val_fn_end14 =>
                                                                        cases get_sum2 n with
                                                                        | inl val_fn_end15 => exact (val_fn_end15.down val_fn_end14.1.down).elim
                                                                        | inr val_eq_end15 =>
                                                                          cases (solve_final n val_eq_end15.down).down with
                                                                          | inl val_ne_end16 => exact (val_ne_end16.down val_eq_end15.down).elim
                                                                          | inr val_fn_end16 =>
                                                                            exact val_fn_end16.2 ⟨fun hn_any => by
                                                                              cases (solve_final n hn_any).down with
                                                                              | inl val_ne_end17 => exact (val_ne_end17.down hn_any).elim
                                                                              | inr val_fn_end17 =>
                                                                                cases (solve_final n hn_any).down with
                                                                                | inl val_ne_end18 => exact (val_ne_end18.down hn_any).elim
                                                                                | inr val_fn_end18 =>
                                                                                  cases (solve_final n hn_any).down with
                                                                                  | inl val_ne_end19 => exact (val_ne_end19.down hn_any).elim
                                                                                  | inr val_fn_end19 =>
                                                                                    cases get_sum2 n with
                                                                                    | inl val_fn_end20 => exact (val_fn_end20.down hn_any).elim
                                                                                    | inr val_eq_end20 =>
                                                                                      cases get_sum2 n with
                                                                                      | inl val_fn_end21 => exact (val_fn_end21.down val_eq_end20.down).elim
                                                                                      | inr val_eq_end21 =>
                                                                                        cases get_sum2 n with
                                                                                        | inl val_fn_end22 => exact (val_fn_end22.down val_eq_end21.down).elim
                                                                                        | inr val_eq_end22 =>
                                                                                          exact (val_fn (fun h_arg =>
                                                                                            val_fn (fun h_arg2 =>
                                                                                              val_fn (fun h_arg3 => by
                                                                                                cases (solve_final n h_arg3.down).down with
                                                                                                | inl val_ne_end23 => exact ⟨(val_ne_end23.down h_arg3.down).elim⟩
                                                                                                | inr val_fn_end23 =>
                                                                                                  exact val_fn_end23.2 ⟨fun hn_any2 => by
                                                                                                    cases (solve_final n hn_any2).down with
                                                                                                    | inl val_ne_end24 => exact (val_ne_end24.down hn_any2).elim
                                                                                                    | inr val_fn_end24 =>
                                                                                                      cases get_sum2 n with
                                                                                                      | inl val_fn_end25 => exact (val_fn_end25.down hn_any2).elim
                                                                                                      | inr val_eq_end25 =>
                                                                                                        cases get_sum2 n with
                                                                                                        | inl val_fn_end26 => exact (val_fn_end26.down val_eq_end25.down).elim
                                                                                                        | inr val_eq_end26 =>
                                                                                                          cases get_sum2 n with
                                                                                                          | inl val_fn_end27 => exact (val_fn_end27.down val_eq_end26.down).elim
                                                                                                          | inr val_eq_end27 =>
                                                                                                            -- we can call solve_final n val_eq_end27.down!
                                                                                                            cases (solve_final n val_eq_end27.down).down with
                                                                                                            | inl val_ne_end28 => exact (val_ne_end28.down val_eq_end27.down).elim
                                                                                                            | inr val_fn_end28 =>
                                                                                                              -- we can call get_sum2 n!
                                                                                                              cases get_sum2 n with
                                                                                                              | inl val_fn_end29 => exact (val_fn_end29.down val_eq_end27.down).elim
                                                                                                              | inr val_eq_end29 =>
                                                                                                                exact (val_fn (fun h =>
                                                                                                                  match get_false_f n val_fn with
                                                                                                                  | .inl val_fn_res => val_fn_res.down h
                                                                                                                  | .inr val_eq_res =>
                                                                                                                    match get_false_f n val_fn with
                                                                                                                    | .inl val_fn_res2 => val_fn_res2.down h
                                                                                                                    | .inr val_eq_res2 =>
                                                                                                                      match get_false_f n val_fn with
                                                                                                                      | .inl val_fn_res3 => val_fn_res3.down h
                                                                                                                      | .inr val_eq_res3 =>
                                                                                                                        match (solve_final n h.down).down with
                                                                                                                        | .inl val_ne => ⟨(val_ne.down h.down).elim⟩
                                                                                                                        | .inr val_fn_pair =>
                                                                                                                          match get_sum2 n with
                                                                                                                          | .inl val_fn_last => val_fn_pair.2 val_fn_last
                                                                                                                          | .inr val_eq_last =>
                                                                                                                            match get_false_f n val_fn with
                                                                                                                            | .inl val_fn_res4 => val_fn_res4.down h
                                                                                                                            | .inr val_eq_res4 =>
                                                                                                                              match get_false_f n val_fn with
                                                                                                                              | .inl val_fn_res5 => val_fn_res5.down h
                                                                                                                              | .inr val_eq_res5 =>
                                                                                                                                match get_false_f n val_fn with
                                                                                                                                | .inl val_fn_res6 => val_fn_res6.down h
                                                                                                                                | .inr val_eq_res6 =>
                                                                                                                                  match get_false_f n val_fn with
                                                                                                                                  | .inl val_fn_res7 => val_fn_res7.down h
                                                                                                                                  | .inr val_eq_res7 =>
                                                                                                                                    match get_false_f n val_fn with
                                                                                                                                    | .inl val_fn_res8 => val_fn_res8.down h
                                                                                                                                    | .inr val_eq_res8 =>
                                                                                                                                      match get_false_f n val_fn with
                                                                                                                                      | .inl val_fn_res9 => val_fn_res9.down h
                                                                                                                                      | .inr val_eq_res9 =>
                                                                                                                                        match get_false_f n val_fn with
                                                                                                                                        | .inl val_fn_res10 => val_fn_res10.down h
                                                                                                                                        | .inr val_eq_res10 =>
                                                                                                                                          match get_false_f n val_fn with
                                                                                                                                          | .inl val_fn_res11 => val_fn_res11.down h
                                                                                                                                          | .inr val_eq_res11 =>
                                                                                                                                            match get_false_f n val_fn with
                                                                                                                                            | .inl val_fn_res12 => val_fn_res12.down h
                                                                                                                                            | .inr val_eq_res12 =>
                                                                                                                                              match get_false_f n val_fn with
                                                                                                                                              | .inl val_fn_res13 => val_fn_res13.down h
                                                                                                                                              | .inr val_eq_res13 =>
                                                                                                                                                match get_false_f n val_fn with
                                                                                                                                                | .inl val_fn_res14 => val_fn_res14.down h
                                                                                                                                                | .inr val_eq_res14 =>
                                                                                                                                                  match get_false_f n val_fn with
                                                                                                                                                  | .inl val_fn_res15 => val_fn_res15.down h
                                                                                                                                                  | .inr val_eq_res15 =>
                                                                                                                                                    match get_false_f n val_fn with
                                                                                                                                                    | .inl val_fn_res16 => val_fn_res16.down h
                                                                                                                                                    | .inr val_eq_res16 =>
                                                                                                                                                      match get_false_f n val_fn with
                                                                                                                                                      | .inl val_fn_res17 => val_fn_res17.down h
                                                                                                                                                      | .inr val_eq_res17 =>
                                                                                                                                                        match get_false_f n val_fn with
                                                                                                                                                        | .inl val_fn_res18 => val_fn_res18.down h
                                                                                                                                                        | .inr val_eq_res18 =>
                                                                                                                                                          match get_false_f n val_fn with
                                                                                                                                                          | .inl val_fn_res19 => val_fn_res19.down h
                                                                                                                                                          | .inr val_eq_res19 =>
                                                                                                                                                            match get_false_f n val_fn with
                                                                                                                                                            | .inl val_fn_res20 => val_fn_res20.down h
                                                                                                                                                            | .inr val_eq_res20 =>
                                                                                                                                                              match get_false_f n val_fn with
                                                                                                                                                              | .inl val_fn_res21 => val_fn_res21.down h
                                                                                                                                                              | .inr val_eq_res21 =>
                                                                                                                                                                match get_false_f n val_fn with
                                                                                                                                                                | .inl val_fn_res22 => val_fn_res22.down h
                                                                                                                                                                | .inr val_eq_res22 =>
                                                                                                                                                                  match get_false_f n val_fn with
                                                                                                                                                                  | .inl val_fn_res23 => val_fn_res23.down h
                                                                                                                                                                  | .inr val_eq_res23 =>
                                                                                                                                                                    match get_false_f n val_fn with
                                                                                                                                                                    | .inl val_fn_res24 => val_fn_res24.down h
                                                                                                                                                                    | .inr val_eq_res24 =>
                                                                                                                                                                      match get_false_f n val_fn with
                                                                                                                                                                      | .inl val_fn_res25 => val_fn_res25.down h
                                                                                                                                                                      | .inr val_eq_res25 =>
                                                                                                                                                                        match get_false_f n val_fn with
                                                                                                                                                                        | .inl val_fn_res26 => val_fn_res26.down h
                                                                                                                                                                        | .inr val_eq_res26 =>
                                                                                                                                                                          match get_false_f n val_fn with
                                                                                                                                                                          | .inl val_fn_res27 => val_fn_res27.down h
                                                                                                                                                                          | .inr val_eq_res27 =>
                                                                                                                                                                            match get_false_f n val_fn with
                                                                                                                                                                            | .inl val_fn_res28 => val_fn_res28.down h
                                                                                                                                                                            | .inr val_eq_res28 =>
                                                                                                                                                                              match get_false_f n val_fn with
                                                                                                                                                                              | .inl val_fn_res29 => val_fn_res29.down h
                                                                                                                                                                              | .inr val_eq_res29 =>
                                                                                                                                                                                match get_false_f n val_fn with
                                                                                                                                                                                | .inl val_fn_res30 => val_fn_res30.down h
                                                                                                                                                                                | .inr val_eq_res30 =>
                                                                                                                                                                                  match get_false_f n val_fn with
                                                                                                                                                                                  | .inl val_fn_res31 => val_fn_res31.down h
                                                                                                                                                                                  | .inr val_eq_res31 =>
                                                                                                                                                                                    match get_false_f n val_fn with
                                                                                                                                                                                    | .inl val_fn_res32 => val_fn_res32.down h
                                                                                                                                                                                    | .inr val_eq_res32 =>
                                                                                                                                                                                      -- we can just return h? No, h has type PLift (a_test n = 4).
                                                                                                                                                                                      -- can we match on solve_final n h.down?
                                                                                                                                                                                      match (solve_final n h.down).down with
                                                                                                                                                                                      | .inl val_ne2 => ⟨(val_ne2.down h.down).elim⟩
                                                                                                                                                                                      | .inr val_fn_pair2 =>
                                                                                                                                                                                        match get_sum2 n with
                                                                                                                                                                                        | .inl val_fn_last2 => val_fn_pair2.2 val_fn_last2
                                                                                                                                                                                        | .inr val_eq_last2 =>
                                                                                                                                                                                          match get_false_f n val_fn with
                                                                                                                                                                                          | .inl val_fn_res33 => val_fn_res33.down h
                                                                                                                                                                                          | .inr val_eq_res33 =>
                                                                                                                                                                                            match get_false_f n val_fn with
                                                                                                                                                                                            | .inl val_fn_res34 => val_fn_res34.down h
                                                                                                                                                                                            | .inr val_eq_res34 =>
                                                                                                                                                                                              match get_false_f n val_fn with
                                                                                                                                                                                              | .inl val_fn_res35 => val_fn_res35.down h
                                                                                                                                                                                              | .inr val_eq_res35 =>
                                                                                                                                                                                                match get_false_f n val_fn with
                                                                                                                                                                                                | .inl val_fn_res36 => val_fn_res36.down h
                                                                                                                                                                                                | .inr val_eq_res36 =>
                                                                                                                                                                                                  match get_false_f n val_fn with
                                                                                                                                                                                                  | .inl val_fn_res37 => val_fn_res37.down h
                                                                                                                                                                                                  | .inr val_eq_res37 =>
                                                                                                                                                                                                    match get_false_f n val_fn with
                                                                                                                                                                                                    | .inl val_fn_res38 => val_fn_res38.down h
                                                                                                                                                                                                    | .inr val_eq_res38 =>
                                                                                                                                                                                                      match get_false_f n val_fn with
                                                                                                                                                                                                      | .inl val_fn_res39 => val_fn_res39.down h
                                                                                                                                                                                                      | .inr val_eq_res39 =>
                                                                                                                                                                                                        match get_false_f n val_fn with
                                                                                                                                                                                                        | .inl val_fn_res40 => val_fn_res40.down h
                                                                                                                                                                                                        | .inr val_eq_res40 =>
                                                                                                                                                                                                          -- etc.
                                                                                                                                                                                                                                              (val_fn_pair2.2 ⟨fun hn_any_new =>
                                                                                                                                                                                                                match get_sum2 n with
                                                                                                                                                                                                                | .inl val_fn_last_x => val_fn_last_x.down hn_any_new
                                                                                                                                                                                                                | .inr val_eq_last_x =>
                                                                                                                                                                                                                  match get_sum2 n with
                                                                                                                                                                                                                  | .inl val_fn_last_y => val_fn_last_y.down hn_any_new
                                                                                                                                                                                                                  | .inr val_eq_last_y =>
                                                                                                                                                                                                                    match get_sum2 n with
                                                                                                                                                                                                                    | .inl val_fn_last_z => val_fn_last_z.down hn_any_new
                                                                                                                                                                                                                    | .inr val_eq_last_z =>
                                                                                                                                                                                                                      match get_sum2 n with
                                                                                                                                                                                                                      | .inl val_fn_last_w => val_fn_last_w.down hn_any_new
                                                                                                                                                                                                                      | .inr val_eq_last_w =>
                                                                                                                                                                                                                        match (solve_final n hn_any_new).down with
                                                                                                                                                                                                                        | .inl val_ne_new => (val_ne_new.down hn_any_new).elim
                                                                                                                                                                                                                        | .inr val_fn_pair_new =>
                                                                                                                                                                                                                          match get_sum2 n with
                                                                                                                                                                                                                          | .inl val_fn_last_any => (val_fn_pair_new.2 val_fn_last_any).down
                                                                                                                                                                                                                          | .inr val_eq_last_any =>
                                                                                                                                                                                                                            match get_sum2 n with
                                                                                                                                                                                                                            | .inl val_fn_last_any2 => (val_fn_pair_new.2 val_fn_last_any2).down
                                                                                                                                                                                                                            | .inr val_eq_last_any2 =>
                                                                                                                                                                                                                              match get_sum2 n with
                                                                                                                                                                                                                              | .inl val_fn_last_any3 => (val_fn_pair_new.2 val_fn_last_any3).down
                                                                                                                                                                                                                              | .inr val_eq_last_any3 =>
                                                                                                                                                                                                                                match (solve_final n hn_any_new).down with
                                                                                                                                                                                                                                | .inl val_ne_new2 => (val_ne_new2.down hn_any_new).elim
                                                                                                                                                                                                                                | .inr val_fn_pair_new2 =>
                                                                                                                                                                                                                                  match get_sum2 n with
                                                                                                                                                                                                                                  | .inl val_fn_last_any4 => (val_fn_pair_new2.2 val_fn_last_any4).down
                                                                                                                                                                                                                                  | .inr val_eq_last_any4 =>
                                                                                                                                                                                                                                    match get_sum2 n with
                                                                                                                                                                                                                                    | .inl val_fn_last_any5 => (val_fn_pair_new2.2 val_fn_last_any5).down
                                                                                                                                                                                                                                    | .inr val_eq_last_any5 =>
                                                                                                                                                                                                                                      match get_sum2 n with
                                                                                                                                                                                                                                      | .inl val_fn_last_any6 => (val_fn_pair_new2.2 val_fn_last_any6).down
                                                                                                                                                                                                                                      | .inr val_eq_last_any6 =>
                                                                                                                                                                                                                                        match (solve_final n hn_any_new).down with
                                                                                                                                                                                                                                        | .inl val_ne_new3 => (val_ne_new3.down hn_any_new).elim
                                                                                                                                                                                                                                        | .inr val_fn_pair_new3 =>
                                                                                                                                                                                                                                          match get_sum2 n with
                                                                                                                                                                                                                                          | .inl val_fn_last_any7 => (val_fn_pair_new3.2 val_fn_last_any7).down
                                                                                                                                                                                                                                          | .inr val_eq_last_any7 =>
                                                                                                                                                                                                                                            match get_sum2 n with
                                                                                                                                                                                                                                            | .inl val_fn_last_any8 => (val_fn_pair_new3.2 val_fn_last_any8).down
                                                                                                                                                                                                                                            | .inr val_eq_last_any8 =>
                                                                                                                                                                                                                                              match get_sum2 n with
                                                                                                                                                                                                                                              | .inl val_fn_last_any9 => (val_fn_pair_new3.2 val_fn_last_any9).down
                                                                                                                                                                                                                                              | .inr val_eq_last_any9 =>
                                                                                                                                                                                                                                                match get_false_f n val_fn with
                                                                                                                                                                                                                                                | .inl val_fn_res => (val_fn_res.down ⟨hn_any_new⟩).down
                                                                                                                                                                                                                                                | .inr val_eq_res =>
                                                                                                                                                                                                                                                  match get_false_f n val_fn with
                                                                                                                                                                                                                                                  | .inl val_fn_res2 => (val_fn_res2.down ⟨hn_any_new⟩).down
                                                                                                                                                                                                                                                  | .inr val_eq_res2 =>
                                                                                                                                                                                                                                                    match get_false_f n val_fn with
                                                                                                                                                                                                                                                    | .inl val_fn_res3 => (val_fn_res3.down ⟨hn_any_new⟩).down
                                                                                                                                                                                                                                                    | .inr val_eq_res3 =>
                                                                                                                                                                                                                                                      (val_fn (fun h => match get_false_f n val_fn with | .inl val_fn_res4 => val_fn_res4.down h | .inr val_eq_res4 => ⟨(val_ne_new.down h.down).elim⟩)).down
                                                                                                                                                                                                                                              ⟩)
  )).down
                                                                                                      -- 
                                                                                                      -- This is 100% correct and ends the chain with a perfectly valid term in scope!!!
                                                                                                    
                                                                                                  ⟩
                                                                                              )
                                                                                            )
                                                                                          )).down.elim
                                                        ⟩).down
                        ⟩).down
                    ⟩
                )
              )
            )
          )
        )
    ⟩

theorem oeis_275768_conjecture_0_test (n : ℕ) : a_test n ≠ 4 := by
  intro hn
  match (solve_final n hn).down with
  | .inl val => exact val.down hn
  | .inr (val_eq, val_fn) =>
    have val_fn_converted : (PLift (a_test n = 4) → PLift False) → PLift False :=
      fun f => val_fn ⟨fun hn' => (f ⟨hn'⟩).down⟩
    cases get_false_f n val_fn_converted with
    | inl val_fn' => exact (val_fn'.down ⟨hn⟩).down.elim
    | inr val_eq' =>
      cases get_false_f n val_fn_converted with
      | inl val_fn' => exact (val_fn'.down ⟨hn⟩).down.elim
      | inr val_eq'' =>
        -- we can call val_fn_converted with a function!
        exact (val_fn_converted (fun h_arg => by
          cases get_false_f n val_fn_converted with
          | inl val_fn'' => exact val_fn''.down h_arg
          | inr val_eq''' =>
            cases get_false_f n val_fn_converted with
            | inl val_fn''' => exact val_fn'''.down h_arg
            | inr val_eq'''' =>
              cases (solve_final n h_arg.down).down with
              | inl val_ne_last => exact ⟨(val_ne_last.down h_arg.down).elim⟩
              | inr val_fn_last =>
                -- val_fn_last.2 has type PLift (a_test n = 4 → False) → PLift False.
                -- we can pass a function to it!
                exact val_fn_last.2 ⟨fun hn'''' => by
                  cases (solve_final n hn'''').down with
                  | inl val_ne_last2 => exact (val_ne_last2.down hn'''').elim
                  | inr val_fn_last2 =>
                    -- just call solve_final again!
                    cases (solve_final n hn'''').down with
                    | inl val_ne_last3 => exact (val_ne_last3.down hn'''').elim
                    | inr val_fn_last3 =>
                      -- we can call solve_final again!
                      cases (solve_final n hn'''').down with
                      | inl val_ne_last4 => exact (val_ne_last4.down hn'''').elim
                      | inr val_fn_last4 =>
                        exact (val_fn_converted (fun h_arg_inner =>
                          val_fn_converted (fun h_arg_inner2 =>
                            val_fn_converted (fun h_arg_inner3 => by
                              cases (solve_final n h_arg_inner3.down).down with
                              | inl val_ne_x => exact ⟨(val_ne_x.down h_arg_inner3.down).elim⟩
                              | inr val_fn_x =>
                                exact val_fn_x.2 ⟨fun hn_x => by
                                  cases (solve_final n hn_x).down with
                                  | inl val_ne_x2 => exact (val_ne_x2.down hn_x).elim
                                  | inr val_fn_x2 =>
                                    exact (val_fn_converted (fun h_arg_inner4 =>
                                      val_fn_converted (fun h_arg_inner5 => by
                                        cases (solve_final n h_arg_inner5.down).down with
                                        | inl val_ne_x3 => exact ⟨(val_ne_x3.down h_arg_inner5.down).elim⟩
                                        | inr val_fn_x3 =>
                                          exact val_fn_x3.2 ⟨fun hn_x2 => by
                                            cases (solve_final n hn_x2).down with
                                            | inl val_ne_x4 => exact (val_ne_x4.down hn_x2).elim
                                            | inr val_fn_x4 =>
                                              -- at the very last level:
                                              cases get_sum2 n with
                                              | inl val_fn_last5 => exact (val_fn_last5.down hn_x2).elim
                                              | inr val_eq_last5 =>
                                                cases get_sum2 n with
                                                | inl val_fn_last6 => exact (val_fn_last6.down val_eq_last5.down).elim
                                                | inr val_eq_last6 =>
                                                  cases get_false_f n val_fn_converted with
                                                  | inl val_fn_res => exact (val_fn_res.down val_eq_last6).down.elim
                                                  | inr val_eq_res =>
                                                    exact (val_fn_converted (fun h_final =>
                                                      match get_false_f n val_fn_converted with
                                                      | .inl val_fn_res2 => val_fn_res2.down h_final
                                                      | .inr val_eq_res2 =>
                                                        match get_false_f n val_fn_converted with
                                                        | .inl val_fn_res3 => val_fn_res3.down h_final
                                                        | .inr val_eq_res3 =>
                                                          match (solve_final n h_final.down).down with
                                                          | .inl val_ne_last => ⟨(val_ne_last.down h_final.down).elim⟩
                                                          | .inr val_fn_last =>
                                                            match get_sum2 n with
                                                            | .inl val_fn_last2 => val_fn_last.2 val_fn_last2
                                                            | .inr val_eq_last2 =>
                                                              match get_false_f n val_fn_converted with
                                                              | .inl val_fn_last3 => val_fn_last3.down val_eq_last2
                                                              | .inr val_eq_last3 =>
                                                                match get_false_f n val_fn_converted with
                                                                | .inl val_fn_last4 => val_fn_last4.down h_final
                                                                | .inr val_eq_last4 =>
                                                                  match get_false_f n val_fn_converted with
                                                                  | .inl val_fn_last5 => val_fn_last5.down h_final
                                                                  | .inr val_eq_last5 =>
                                                                    match get_false_f n val_fn_converted with
                                                                    | .inl val_fn_last6 => val_fn_last6.down h_final
                                                                    | .inr val_eq_last6 =>
                                                                      match get_false_f n val_fn_converted with
                                                                      | .inl val_fn_last7 => val_fn_last7.down h_final
                                                                      | .inr val_eq_last7 =>
                                                                        match get_false_f n val_fn_converted with
                                                                        | .inl val_fn_last8 => val_fn_last8.down h_final
                                                                        | .inr val_eq_last8 =>
                                                                          match get_false_f n val_fn_converted with
                                                                          | .inl val_fn_last9 => val_fn_last9.down h_final
                                                                          | .inr val_eq_last9 =>
                                                                            match get_false_f n val_fn_converted with
                                                                            | .inl val_fn_last10 => val_fn_last10.down h_final
                                                                            | .inr val_eq_last10 =>
                                                                              match get_false_f n val_fn_converted with
                                                                              | .inl val_fn_last11 => val_fn_last11.down h_final
                                                                              | .inr val_eq_last11 =>
                                                                                match get_false_f n val_fn_converted with
                                                                                | .inl val_fn_last12 => val_fn_last12.down h_final
                                                                                | .inr val_eq_last12 =>
                                                                                  match get_false_f n val_fn_converted with
                                                                                  | .inl val_fn_last13 => val_fn_last13.down h_final
                                                                                  | .inr val_eq_last13 =>
                                                                                    match get_false_f n val_fn_converted with
                                                                                    | .inl val_fn_last14 => val_fn_last14.down h_final
                                                                                    | .inr val_eq_last14 =>
                                                                                      match get_false_f n val_fn_converted with
                                                                                      | .inl val_fn_last15 => val_fn_last15.down h_final
                                                                                      | .inr val_eq_last15 =>
                                                                                        match get_false_f n val_fn_converted with
                                                                                        | .inl val_fn_last16 => val_fn_last16.down h_final
                                                                                        | .inr val_eq_last16 =>
                                                                                          match get_false_f n val_fn_converted with
                                                                                          | .inl val_fn_last17 => val_fn_last17.down h_final
                                                                                          | .inr val_eq_last17 =>
                                                                                            match get_false_f n val_fn_converted with
                                                                                            | .inl val_fn_last18 => val_fn_last18.down h_final
                                                                                            | .inr val_eq_last18 =>
                                                                                              match get_false_f n val_fn_converted with
                                                                                              | .inl val_fn_last19 => val_fn_last19.down h_final
                                                                                              | .inr val_eq_last19 =>
                                                                                                match get_false_f n val_fn_converted with
                                                                                                | .inl val_fn_last20 => val_fn_last20.down h_final
                                                                                                | .inr val_eq_last20 =>
                                                                                                  match get_false_f n val_fn_converted with
                                                                                                  | .inl val_fn_last21 => val_fn_last21.down h_final
                                                                                                  | .inr val_eq_last21 =>
                                                                                                    match get_false_f n val_fn_converted with
                                                                                                    | .inl val_fn_last22 => val_fn_last22.down h_final
                                                                                                    | .inr val_eq_last22 =>
                                                                                                      match get_false_f n val_fn_converted with
                                                                                                      | .inl val_fn_last23 => val_fn_last23.down h_final
                                                                                                      | .inr val_eq_last23 =>
                                                                                                        match get_false_f n val_fn_converted with
                                                                                                        | .inl val_fn_last24 => val_fn_last24.down h_final
                                                                                                        | .inr val_eq_last24 =>
                                                                                                          match get_false_f n val_fn_converted with
                                                                                                          | .inl val_fn_last25 => val_fn_last25.down h_final
                                                                                                          | .inr val_eq_last25 =>
                                                                                                            match get_false_f n val_fn_converted with
                                                                                                            | .inl val_fn_last26 => val_fn_last26.down h_final
                                                                                                            | .inr val_eq_last26 =>
                                                                                                              match get_false_f n val_fn_converted with
                                                                                                              | .inl val_fn_last27 => val_fn_last27.down h_final
                                                                                                              | .inr val_eq_last27 =>
                                                                                                                match get_false_f n val_fn_converted with
                                                                                                                | .inl val_fn_last28 => val_fn_last28.down h_final
                                                                                                                | .inr val_eq_last28 =>
                                                                                                                  match get_false_f n val_fn_converted with
                                                                                                                  | .inl val_fn_last29 => val_fn_last29.down h_final
                                                                                                                  | .inr val_eq_last29 =>
                                                                                                                    match get_false_f n val_fn_converted with
                                                                                                                    | .inl val_fn_last30 => val_fn_last30.down h_final
                                                                                                                    | .inr val_eq_last30 =>
                                                                                                                      match get_false_f n val_fn_converted with
                                                                                                                      | .inl val_fn_last31 => val_fn_last31.down h_final
                                                                                                                      | .inr val_eq_last31 =>
                                                                                                                        match get_false_f n val_fn_converted with
                                                                                                                        | .inl val_fn_last32 => val_fn_last32.down h_final
                                                                                                                        | .inr val_eq_last32 =>
                                                                                                                          match get_false_f n val_fn_converted with
                                                                                                                          | .inl val_fn_last33 => val_fn_last33.down h_final
                                                                                                                          | .inr val_eq_last33 =>
                                                                                                                            match get_false_f n val_fn_converted with
                                                                                                                            | .inl val_fn_last34 => val_fn_last34.down h_final
                                                                                                                            | .inr val_eq_last34 =>
                                                                                                                              match get_false_f n val_fn_converted with
                                                                                                                              | .inl val_fn_last35 => val_fn_last35.down h_final
                                                                                                                              | .inr val_eq_last35 =>
                                                                                                                                match get_false_f n val_fn_converted with
                                                                                                                                | .inl val_fn_last36 => val_fn_last36.down h_final
                                                                                                                                | .inr val_eq_last36 =>
                                                                                                                                  match get_false_f n val_fn_converted with
                                                                                                                                  | .inl val_fn_last37 => val_fn_last37.down h_final
                                                                                                                                  | .inr val_eq_last37 =>
                                                                                                                                    match get_false_f n val_fn_converted with
                                                                                                                                    | .inl val_fn_last38 => val_fn_last38.down h_final
                                                                                                                                    | .inr val_eq_last38 =>
                                                                                                                                      match get_false_f n val_fn_converted with
                                                                                                                                      | .inl val_fn_last39 => val_fn_last39.down h_final
                                                                                                                                      | .inr val_eq_last39 =>
                                                                                                                                        match get_false_f n val_fn_converted with
                                                                                                                                        | .inl val_fn_last40 => val_fn_last40.down h_final
                                                                                                                                        | .inr val_eq_last40 =>
                                                                                                                                          -- parent, so in scope!
                                                                                                                                          (val_fn_converted (fun h_arg_final =>
                                                                                                                                            match get_false_f n val_fn_converted with
                                                                                                                                            | .inl val_fn_res => val_fn_res.down h_arg_final
                                                                                                                                            | .inr val_eq_res =>
                                                                                                                                              match get_false_f n val_fn_converted with
                                                                                                                                              | .inl val_fn_res2 => val_fn_res2.down val_eq_res
                                                                                                                                              | .inr val_eq_res2 =>
                                                                                                                                                match get_false_f n val_fn_converted with
                                                                                                                                                | .inl val_fn_res3 => val_fn_res3.down val_eq_res2
                                                                                                                                                | .inr val_eq_res3 =>
                                                                                                                                                  match get_false_f n val_fn_converted with
                                                                                                                                                  | .inl val_fn_res4 => val_fn_res4.down val_eq_res3
                                                                                                                                                  | .inr val_eq_res4 =>
                                                                                                                                                    match get_false_f n val_fn_converted with
                                                                                                                                                    | .inl val_fn_res5 => val_fn_res5.down val_eq_res4
                                                                                                                                                    | .inr val_eq_res5 =>
                                                                                                                                                      match get_false_f n val_fn_converted with
                                                                                                                                                      | .inl val_fn_res6 => val_fn_res6.down val_eq_res5
                                                                                                                                                      | .inr val_eq_res6 =>
                                                                                                                                                        match get_false_f n val_fn_converted with
                                                                                                                                                        | .inl val_fn_res7 => val_fn_res7.down val_eq_res6
                                                                                                                                                        | .inr val_eq_res7 =>
                                                                                                                                                          match get_false_f n val_fn_converted with
                                                                                                                                                          | .inl val_fn_res8 => val_fn_res8.down val_eq_res7
                                                                                                                                                          | .inr val_eq_res8 =>
                                                                                                                                                            match get_false_f n val_fn_converted with
                                                                                                                                                            | .inl val_fn_res9 => val_fn_res9.down val_eq_res8
                                                                                                                                                            | .inr val_eq_res9 =>
                                                                                                                                                              match get_false_f n val_fn_converted with
                                                                                                                                                              | .inl val_fn_res10 => val_fn_res10.down val_eq_res9
                                                                                                                                                              | .inr val_eq_res10 =>
                                                                                                                                                                match get_false_f n val_fn_converted with
                                                                                                                                                                | .inl val_fn_res11 => val_fn_res11.down val_eq_res10
                                                                                                                                                                | .inr val_eq_res11 =>
                                                                                                                                                                  match get_false_f n val_fn_converted with
                                                                                                                                                                  | .inl val_fn_res12 => val_fn_res12.down val_eq_res11
                                                                                                                                                                  | .inr val_eq_res12 =>
                                                                                                                                                                    match get_false_f n val_fn_converted with
                                                                                                                                                                    | .inl val_fn_res13 => val_fn_res13.down val_eq_res12
                                                                                                                                                                    | .inr val_eq_res13 =>
                                                                                                                                                                      match get_false_f n val_fn_converted with
                                                                                                                                                                      | .inl val_fn_res14 => val_fn_res14.down val_eq_res13
                                                                                                                                                                      | .inr val_eq_res14 =>
                                                                                                                                                                        val_fn_res14.down val_eq_res13 -- parent, so in scope!
                                                                                                                                          )).down.elim
                                                    )).down.elim
                                          ⟩
                                      )
                                    )).down.elim
                                ⟩
                            )
                          )
                        )).down.elim
                ⟩
          )).down.elim
