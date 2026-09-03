import Submission.PureSixDoubleBase
namespace Erdos184Work.PureSixDoublePatterns
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check9_part0 (b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![false,true,false,false,true,false,false,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![false,true,false,false,true,false,false,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![false,true,false,false,true,false,false,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![false,true,false,false,true,false,false,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![false,true,false,false,true,false,false,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  revert b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
lemma check9_part1 (b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![false,true,false,false,true,false,true,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![false,true,false,false,true,false,true,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![false,true,false,false,true,false,true,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![false,true,false,false,true,false,true,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![false,true,false,false,true,false,true,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  revert b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
lemma check9_part2 (b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![false,true,false,false,true,true,false,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![false,true,false,false,true,true,false,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![false,true,false,false,true,true,false,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![false,true,false,false,true,true,false,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![false,true,false,false,true,true,false,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  revert b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
lemma check9_part3 (b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![false,true,false,false,true,true,true,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![false,true,false,false,true,true,true,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![false,true,false,false,true,true,true,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![false,true,false,false,true,true,true,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![false,true,false,false,true,true,true,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  revert b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
lemma check9 (b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![false,true,false,false,true,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![false,true,false,false,true,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![false,true,false,false,true,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![false,true,false,false,true,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![false,true,false,false,true,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  cases b5 <;> cases b6
  · exact check9_part0 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check9_part1 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check9_part2 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check9_part3 b7 b8 b9 b10 b11 b12 b13 b14
#print axioms check9
end Erdos184Work.PureSixDoublePatterns
