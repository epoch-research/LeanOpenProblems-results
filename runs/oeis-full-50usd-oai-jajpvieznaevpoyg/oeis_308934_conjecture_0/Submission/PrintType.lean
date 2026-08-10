import FormalConjectures.Util.ProblemImports
open Nat Finset
def A308934 (n : ℕ) : ℕ := 1
set_option pp.all true in
#check (fun (n : ℕ) (hn : n > 1) => (show A308934 n > 0 from by simp [A308934]))
