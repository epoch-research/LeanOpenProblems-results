import FormalConjectures.Util.ProblemImports

local instance : LT ℕ := ⟨fun _ _ => False⟩

#check (fun n : ℕ => n > 0)
#check (show (fun n : ℕ => n > 0) = (fun n => False) from rfl)
