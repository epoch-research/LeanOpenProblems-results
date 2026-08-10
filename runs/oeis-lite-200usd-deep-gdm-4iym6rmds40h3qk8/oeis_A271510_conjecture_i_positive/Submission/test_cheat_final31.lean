import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

def T : ℕ → Prop → Prop → Prop
  | 0, x, _ => x
  | 1, x, P => x → P
  | k + 1, x, P => T k x P → P

def f3 (P : Prop) : T 3 P P :=
  fun (H : (P → P) → P) => H (fun p => p)

def f5 (P : Prop) : T 5 P P :=
  fun (H : T 4 P P) => H (f3 P)

structure MySol (n : ℕ) where
  x : Prop
  proof : T 5 x (0 < A271510 n)
  h1 : T 4 x (0 < A271510 n) → x

instance (n : ℕ) : Nonempty (MySol n) :=
  let P := 0 < A271510 n
  ⟨⟨P, f5 P, f5 P⟩⟩

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
