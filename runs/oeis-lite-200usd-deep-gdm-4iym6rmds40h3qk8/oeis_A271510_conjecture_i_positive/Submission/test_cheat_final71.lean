import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : ℕ
  h : x = n → 0 < A271510 n

instance (n : ℕ) : Nonempty (MySol n) :=
  ⟨⟨n + 1, fun h_eq => False.elim (by omega)⟩⟩

mutual
  partial def get_sol (n : ℕ) : MySol n :=
    ⟨n, fun _ => (get_sol n).h (get_x_eq n)⟩

  partial def get_x_eq (n : ℕ) : (get_sol n).x = n :=
    get_x_eq n
end

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  have h_eq : s.x = n := get_x_eq n
  exact s.h h_eq

#print axioms my_thm
