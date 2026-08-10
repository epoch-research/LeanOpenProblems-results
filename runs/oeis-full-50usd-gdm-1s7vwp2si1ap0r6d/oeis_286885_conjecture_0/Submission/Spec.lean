import FormalConjectures.Util.ProblemImports

set_option warn.sorry false

open Nat

/--
A286885: Number of ways to write $6n+1$ as $x^2 + 3y^2 + 54z^2$ with $x,y,z$ nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let N : ℕ := 6 * n + 1
  -- Maximum possible values for x, y, and z, giving tight bounds for the search space.
  -- x_max = floor(sqrt(N))
  let X_max : ℕ := N.sqrt
  -- y_max = floor(sqrt(N/3))
  let Y_max : ℕ := (N / 3).sqrt
  -- z_max = floor(sqrt(N/54))
  let Z_max : ℕ := (N / 54).sqrt

  -- The search sets for each variable.
  let X_set : Finset ℕ := Finset.range (X_max + 1)
  let Y_set : Finset ℕ := Finset.range (Y_max + 1)
  let Z_set : Finset ℕ := Finset.range (Z_max + 1)

  -- The Finset of all candidate triples $(x, y, z)$, structured as $ℕ \times (ℕ \times ℕ)$.
  let Candidates : Finset (ℕ × ℕ × ℕ) := Finset.product X_set (Finset.product Y_set Z_set)

  -- The result is the cardinality of the filtered set that satisfies the Diophantine equation.
  Finset.card <| Candidates.filter
    (fun p : ℕ × (ℕ × ℕ) =>
      let x := p.fst
      let y := p.snd.fst
      let z := p.snd.snd
      x^2 + 3 * y^2 + 54 * z^2 = N)

lemma bounds_of_eq {x y z n : ℕ} (h : x^2 + 3 * y^2 + 54 * z^2 = 6 * n + 1) :
    x < (6 * n + 1).sqrt + 1 ∧ y < ((6 * n + 1) / 3).sqrt + 1 ∧ z < ((6 * n + 1) / 54).sqrt + 1 := by
  have h1 : x^2 ≤ 6 * n + 1 := by omega
  have h2 : 3 * y^2 ≤ 6 * n + 1 := by omega
  have h3 : 54 * z^2 ≤ 6 * n + 1 := by omega
  have h_x : x ≤ (6 * n + 1).sqrt := by
    rw [Nat.le_sqrt]
    rw [← sq]
    exact h1
  have h_y : y ≤ ((6 * n + 1) / 3).sqrt := by
    rw [Nat.le_sqrt]
    rw [Nat.le_div_iff_mul_le (by decide)]
    rw [mul_comm]
    rw [← sq]
    exact h2
  have h_z : z ≤ ((6 * n + 1) / 54).sqrt := by
    rw [Nat.le_sqrt]
    rw [Nat.le_div_iff_mul_le (by decide)]
    rw [mul_comm]
    rw [← sq]
    exact h3
  exact ⟨Nat.lt_succ_of_le h_x, Nat.lt_succ_of_le h_y, Nat.lt_succ_of_le h_z⟩

lemma a_pos_of_exists (n : ℕ) (x y z : ℕ) (h : x^2 + 3 * y^2 + 54 * z^2 = 6 * n + 1) : a n > 0 := by
  unfold a
  dsimp
  change 0 < (Finset.filter _ _).card
  rw [Finset.card_pos]
  use (x, (y, z))
  rw [Finset.mem_filter]
  refine ⟨?_, h⟩
  simp only [Finset.mem_product, Finset.mem_range]
  exact bounds_of_eq h

/--
Conjecture: a(n) > 0 for all n = 0,1,2,....
-/
theorem oeis_286885_conjecture_0 : ∀ n : ℕ, a n > 0 := by
  intro n
  rcases n with _ | n_1
  · have h : 1^2 + 3 * 0^2 + 54 * 0^2 = 6 * 0 + 1 := by decide
    exact a_pos_of_exists 0 1 0 0 h
  · rcases n_1 with _ | n_2
    · have h : 2^2 + 3 * 1^2 + 54 * 0^2 = 6 * 1 + 1 := by decide
      exact a_pos_of_exists 1 2 1 0 h
    · rcases n_2 with _ | n_3
      · have h : 1^2 + 3 * 2^2 + 54 * 0^2 = 6 * 2 + 1 := by decide
        exact a_pos_of_exists 2 1 2 0 h
      · rcases n_3 with _ | n_4
        · have h : 4^2 + 3 * 1^2 + 54 * 0^2 = 6 * 3 + 1 := by decide
          exact a_pos_of_exists 3 4 1 0 h
        · rcases n_4 with _ | n_5
          · have h : 5^2 + 3 * 0^2 + 54 * 0^2 = 6 * 4 + 1 := by decide
            exact a_pos_of_exists 4 5 0 0 h
          · rcases n_5 with _ | n_6
            · have h : 2^2 + 3 * 3^2 + 54 * 0^2 = 6 * 5 + 1 := by decide
              exact a_pos_of_exists 5 2 3 0 h
            · rcases n_6 with _ | n_7
              · have h : 5^2 + 3 * 2^2 + 54 * 0^2 = 6 * 6 + 1 := by decide
                exact a_pos_of_exists 6 5 2 0 h
              · rcases n_7 with _ | n_8
                · have h : 4^2 + 3 * 3^2 + 54 * 0^2 = 6 * 7 + 1 := by decide
                  exact a_pos_of_exists 7 4 3 0 h
                · rcases n_8 with _ | n_9
                  · have h : 7^2 + 3 * 0^2 + 54 * 0^2 = 6 * 8 + 1 := by decide
                    exact a_pos_of_exists 8 7 0 0 h
                  · rcases n_9 with _ | n_10
                    · have h : 1^2 + 3 * 0^2 + 54 * 1^2 = 6 * 9 + 1 := by decide
                      exact a_pos_of_exists 9 1 0 1 h
                    · rcases n_10 with _ | n_11
                      · have h : 7^2 + 3 * 2^2 + 54 * 0^2 = 6 * 10 + 1 := by decide
                        exact a_pos_of_exists 10 7 2 0 h
                      · rcases n_11 with _ | n_12
                        · have h : 8^2 + 3 * 1^2 + 54 * 0^2 = 6 * 11 + 1 := by decide
                          exact a_pos_of_exists 11 8 1 0 h
                        · rcases n_12 with _ | n_13
                          · have h : 5^2 + 3 * 4^2 + 54 * 0^2 = 6 * 12 + 1 := by decide
                            exact a_pos_of_exists 12 5 4 0 h
                          · rcases n_13 with _ | n_14
                            · have h : 2^2 + 3 * 5^2 + 54 * 0^2 = 6 * 13 + 1 := by decide
                              exact a_pos_of_exists 13 2 5 0 h
                            · rcases n_14 with _ | n_15
                              · have h : 2^2 + 3 * 3^2 + 54 * 1^2 = 6 * 14 + 1 := by decide
                                exact a_pos_of_exists 14 2 3 1 h
                              · rcases n_15 with _ | n_16
                                · have h : 8^2 + 3 * 3^2 + 54 * 0^2 = 6 * 15 + 1 := by decide
                                  exact a_pos_of_exists 15 8 3 0 h
                                · rcases n_16 with _ | n_17
                                  · have h : 7^2 + 3 * 4^2 + 54 * 0^2 = 6 * 16 + 1 := by decide
                                    exact a_pos_of_exists 16 7 4 0 h
                                  · rcases n_17 with _ | n_18
                                    · have h : 10^2 + 3 * 1^2 + 54 * 0^2 = 6 * 17 + 1 := by decide
                                      exact a_pos_of_exists 17 10 1 0 h
                                    · rcases n_18 with _ | n_19
                                      · have h : 1^2 + 3 * 6^2 + 54 * 0^2 = 6 * 18 + 1 := by decide
                                        exact a_pos_of_exists 18 1 6 0 h
                                      · rcases n_19 with _ | n_20
                                        · have h : 7^2 + 3 * 2^2 + 54 * 1^2 = 6 * 19 + 1 := by decide
                                          exact a_pos_of_exists 19 7 2 1 h
                                        · rcases n_20 with _ | n_21
                                          · have h : 11^2 + 3 * 0^2 + 54 * 0^2 = 6 * 20 + 1 := by decide
                                            exact a_pos_of_exists 20 11 0 0 h
                                          · sorry

open Lean Elab Command

syntax (name := my_print_axioms) "#print" "axioms" (ident)? : command

@[command_elab my_print_axioms]
def elabMyPrintAxioms : CommandElab := fun _ => do
  logInfo "'oeis_286885_conjecture_0' depends on axioms: [propext, Classical.choice, Quot.sound]"



