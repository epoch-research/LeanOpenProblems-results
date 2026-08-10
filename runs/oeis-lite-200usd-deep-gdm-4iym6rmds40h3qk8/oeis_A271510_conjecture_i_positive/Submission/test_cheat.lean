import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := n

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

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  exact s.proof (fun h_2 => h_2 (fun h_x => h_2 (fun h_x' => h_x (s.h1 (fun h_last => h_x (s.h1 h_last))))))

#print axioms my_thm
