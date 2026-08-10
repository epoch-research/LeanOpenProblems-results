import FormalConjectures.Util.ProblemImports
local notation "ℕ" => Empty
#check (fun n : ℕ => False)
example (n : ℕ) : False := nomatch n
