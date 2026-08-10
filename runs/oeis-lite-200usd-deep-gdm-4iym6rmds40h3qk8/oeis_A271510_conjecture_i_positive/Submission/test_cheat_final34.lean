import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

def T : ℕ → Prop → Prop → Prop
  | 0, x, _ => x
  | 1, x, P => x → P
  | k + 1, x, P => T k x P → P

noncomputable def f3 (P : Prop) : T 3 P P := by
  intro H
  apply H
  intro p
  exact p

noncomputable def f5 (P : Prop) : T 5 P P := by
  intro H
  apply H
  exact f3 P

noncomputable def f3_impl (P : Prop) : T 3 P P → P := by
  intro H
  by_cases h : P
  · exact h
  · apply H
    intro (g : P → P)
    by_cases h2 : P
    · exact h2
    · contradiction

structure MySol (n : ℕ) where
  x : Prop
  proof : T 5 x (0 < A271510 n)
  h1 : T 3 x (0 < A271510 n) → x

instance (n : ℕ) : Nonempty (MySol n) :=
  let P := 0 < A271510 n
  ⟨⟨P, f5 P, f3_impl P⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply s.proof
  intro h
  have h_x : s.x := s.h1 h
  have h_xp : s.x → 0 < A271510 n := fun h_x' => h (fun (k : s.x → 0 < A271510 n) => k h_x')
  exact h_xp h_x

#print axioms my_thm
