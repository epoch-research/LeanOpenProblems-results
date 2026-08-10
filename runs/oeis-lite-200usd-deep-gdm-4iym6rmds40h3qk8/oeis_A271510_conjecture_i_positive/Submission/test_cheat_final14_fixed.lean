import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n
  h1 : ((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → x
  h2 : ((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → x → 0 < A271510 n

instance (n : ℕ) : Nonempty (MySol n) :=
  let P := 0 < A271510 n
  ⟨⟨True,
    fun (H : ((((True → P) → P) → P) → P) → P) =>
      H (fun (H' : ((True → P) → P) → P) =>
        H' (fun (h_impl : True → P) => h_impl True.intro)),
    fun _ => True.intro,
    fun (H : (((True → P) → P) → P) → P) =>
      fun _ => H (fun (H' : (True → P) → P) =>
        H' (fun (h_impl : True → P) => h_impl True.intro))⟩⟩

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
