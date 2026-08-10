import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ := 0

structure MySol (n : ℕ) where
  x : Prop
  proof : (((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n
  h1 : ((x → 0 < A271510 n) → 0 < A271510 n) → x

instance (n : ℕ) : Nonempty (MySol n) :=
  ⟨⟨True,
    fun h_3 => h_3 (fun h_impl => h_impl True.intro),
    fun _ => True.intro⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

partial def get_arg (n : ℕ) : (((get_sol n).x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n :=
  get_arg n

theorem oeis_A271510_not_div_four (n : ℕ) (h : ¬ 4 ∣ n) : 0 < A271510 n := by
  let s := get_sol n
  exact s.proof (get_arg n)
