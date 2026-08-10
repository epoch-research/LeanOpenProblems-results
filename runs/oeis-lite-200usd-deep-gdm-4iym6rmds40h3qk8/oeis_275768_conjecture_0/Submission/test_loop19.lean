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
                                                                          cases get_sum2 n with
                                                                          | inl val_fn_end16 => exact (val_fn_end16.down val_eq_end15.down).elim
                                                                          | inr val_eq_end16 =>
                                                                            exact (val_fn_end16.down val_eq_end16.down).elim
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
                        -- we can call get_sum2 n!
                        cases get_sum2 n with
                        | inl val_fn_last5 => exact (val_fn_last5.down hn'''' ).elim
                        | inr val_eq_last5 =>
                          cases get_sum2 n with
                          | inl val_fn_last6 => exact (val_fn_last6.down val_eq_last5.down).elim
                          | inr val_eq_last6 =>
                            exact (val_fn_last6.down val_eq_last6.down).elim
                ⟩
        )).down.elim
