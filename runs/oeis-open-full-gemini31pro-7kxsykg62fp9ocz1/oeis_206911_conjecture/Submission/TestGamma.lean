import Mathlib

open Real Finset

lemma H600_bound : eulerMascheroniConstant < harmonic 600 - log 600 :=
  eulerMascheroniConstant_lt_eulerMascheroniSeq' 600
