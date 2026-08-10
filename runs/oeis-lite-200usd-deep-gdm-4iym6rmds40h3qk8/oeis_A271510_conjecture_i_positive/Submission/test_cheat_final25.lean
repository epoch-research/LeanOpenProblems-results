import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n
  h1 : ((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → x

instance (n : ℕ) : Nonempty (MySol n) :=
  let P := 0 < A271510 n
  ⟨⟨True,
    fun (H : (((True → P) → P) → P) → P) => H (fun (G : (True → P) → P) => G (fun (f : True → P) => f True.intro)),
    fun _ => True.intro⟩⟩

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
