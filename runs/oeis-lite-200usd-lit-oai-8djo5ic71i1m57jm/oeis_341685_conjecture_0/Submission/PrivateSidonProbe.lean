import FormalConjectures.Util.ProblemImports

#check _private.FormalConjecturesForMathlib.Combinatorics.Basic.«0».Set.IsSidon.avoids_isAPOfLength_three._proof_1_1
#print _private.FormalConjecturesForMathlib.Combinatorics.Basic.«0».Set.IsSidon.avoids_isAPOfLength_three._proof_1_1
#print axioms _private.FormalConjecturesForMathlib.Combinatorics.Basic.«0».Set.IsSidon.avoids_isAPOfLength_three._proof_1_1

example : False := by
  have h := _private.FormalConjecturesForMathlib.Combinatorics.Basic.«0».Set.IsSidon.avoids_isAPOfLength_three._proof_1_1 (A := (Set.univ : Set ℕ)) (Y := (Set.univ : Set ℕ)) 0 0
  exact h (by norm_num)
