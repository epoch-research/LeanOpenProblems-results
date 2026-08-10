import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num

-- candidate X for not_preirreducible_nontrivial_t2
#synth TopologicalSpace ℝ
#synth T2Space ℝ
#synth Nontrivial ℝ
#synth PreirreducibleSpace ℝ

#synth TopologicalSpace (Padic 3)
#synth T2Space (Padic 3)
#synth Nontrivial (Padic 3)
#synth PreirreducibleSpace (Padic 3)

#synth TopologicalSpace Prop
#synth T2Space Prop
#synth Nontrivial Prop
#synth Subsingleton Prop
#synth PreirreducibleSpace Prop

-- Nontrivial+Subsingleton candidates
#synth Nontrivial (Fin 0)
#synth Subsingleton (Fin 0)
#synth Nontrivial (Fin 1)
#synth Subsingleton (Fin 1)
#synth Nontrivial PUnit
#synth Subsingleton PUnit
#synth Nontrivial Empty
#synth Subsingleton Empty

-- Infinite+Finite candidates
#synth Infinite Prop
#synth Finite Prop
#synth Infinite (ULift Prop)
#synth Finite (ULift Prop)

-- CharP 1 candidates
#synth Nontrivial (ZMod 1)
#synth CharP (ZMod 1) 1
#synth Nontrivial PUnit
#synth CharP PUnit 1
