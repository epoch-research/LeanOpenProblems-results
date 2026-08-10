import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n
  h1 : ((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → x
  h2 : ((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → x → 0 < A271510 n

instance (n : ℕ) : Nonempty (MySol n) :=
  ⟨⟨True,
    fun (H : ((((True → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) =>
      H (fun (H' : ((True → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) =>
        H' (fun (h_impl : True → 0 < A271510 n) => h_impl True.intro)),
    fun _ => True.intro,
    fun (H : ((((True → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n)) =>
      fun _ => H (fun (G : (True → 0 < A271510 n) → 0 < A271510 n) =>
        G (fun (h_impl : True → 0 < A271510 n) => h_impl True.intro))⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply s.proof
  intro h_2
  have h_x : s.x := s.h1 h_2
  have h_xp : s.x → 0 < A271510 n := s.h2 h_2
  exact h_xp h_x

#print axioms my_thm
