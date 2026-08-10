import FormalConjectures.Util.ProblemImports
open BigOperators Finset Nat Real

def omega_mult (k : ℕ) : ℕ := k.factorization.sum (fun _ e => e)
#eval List.map omega_mult [0,1,2,3,4,5,6,8,9,12]
#eval (List.range 20).map (fun k => (k, ((k : Int) - (omega_mult k : Int)) % 2))
