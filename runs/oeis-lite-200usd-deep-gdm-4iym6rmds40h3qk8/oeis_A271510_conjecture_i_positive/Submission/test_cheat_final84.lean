import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (((((x → False) → False) → False) → False) → False) → 0 < A271510 n
  h2 : (0 < A271510 n → False) → (((x → False) → False) → False) → False

instance (n : ℕ) : Nonempty (MySol n) := by
  by_cases h : 0 < A271510 n
  · exact ⟨⟨True,
            fun _ => h,
            fun _ => fun h_triple => h_triple (fun (f : True → False) => f True.intro)⟩⟩
  · exact ⟨⟨True,
            fun h_four => False.elim (h_not_four h_four) -- wait, how do we write the false branch?
            -- the type of the second field in the False branch is:
            -- (((((True → False) → False) → False) → False) → False) → P.
            -- So let's name the argument:
            , ?_⟩⟩
    -- wait, let's write it in a tactic block to be safe!
