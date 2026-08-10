import FormalConjectures.Util.ProblemImports
set_option synthInstance.maxHeartbeats 50000
set_option maxHeartbeats 200000

-- Subsingleton/Nontrivial pairs
#synth Subsingleton PUnit.{0}
#synth Nontrivial PUnit.{0}
#synth Subsingleton Unit
#synth Nontrivial Unit
#synth Subsingleton (Fin 1)
#synth Nontrivial (Fin 1)
#synth Subsingleton (ULift.{1,0} PUnit.{0})
#synth Nontrivial (ULift.{1,0} PUnit.{0})
#synth Subsingleton Empty
#synth Nontrivial Empty
#synth Subsingleton False
#synth Nontrivial False
#synth Subsingleton True
#synth Nontrivial True

-- Finite/Infinite pairs
#synth Finite PUnit.{0}
#synth Infinite PUnit.{0}
#synth Finite Unit
#synth Infinite Unit
#synth Finite (Fin 1)
#synth Infinite (Fin 1)
#synth Finite Empty
#synth Infinite Empty
#synth Finite False
#synth Infinite False
#synth Finite True
#synth Infinite True
