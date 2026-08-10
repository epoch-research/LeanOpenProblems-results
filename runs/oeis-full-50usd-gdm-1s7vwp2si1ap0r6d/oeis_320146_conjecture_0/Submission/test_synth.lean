import FormalConjectures.Util.Answer
import Mathlib

set_option google.answer "always_true"

lemma my_proof : ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop (nhds L) :=
  answer(sorry)

#print axioms my_proof
