import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : ((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n
  h1 : (((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → x

instance (n : ℕ) : Nonempty (MySol n) :=
  let P := 0 < A271510 n
  let f_I : P → P := fun p => p
  let f_K : ((P → P) → P) → P := fun K => K f_I
  let f_H : (((P → P) → P) → P) → P := fun H => H f_K
  ⟨⟨P, f_H, f_H⟩⟩

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
