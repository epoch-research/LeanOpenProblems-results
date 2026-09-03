import Submission.PureSixDoubleBase
namespace Erdos184Work.PureSixDoublePatterns
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check3_part0 (b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![false,false,false,true,true,false,false,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![false,false,false,true,true,false,false,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![false,false,false,true,true,false,false,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![false,false,false,true,true,false,false,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![false,false,false,true,true,false,false,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  revert b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
lemma check3_part1 (b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![false,false,false,true,true,false,true,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![false,false,false,true,true,false,true,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![false,false,false,true,true,false,true,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![false,false,false,true,true,false,true,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![false,false,false,true,true,false,true,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  revert b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
lemma check3_part2 (b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![false,false,false,true,true,true,false,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![false,false,false,true,true,true,false,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![false,false,false,true,true,true,false,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![false,false,false,true,true,true,false,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![false,false,false,true,true,true,false,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  revert b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
lemma check3_part3 (b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![false,false,false,true,true,true,true,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![false,false,false,true,true,true,true,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![false,false,false,true,true,true,true,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![false,false,false,true,true,true,true,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![false,false,false,true,true,true,true,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  revert b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel
lemma check3 (b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    Admissible ![false,false,false,true,true,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14] → ∀ i j : Fin 6,
    between ![false,false,false,true,true,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14] (permutations (normalizer ![false,false,false,true,true,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14]).2 i) (permutations (normalizer ![false,false,false,true,true,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14]).2 j) =
      between (representative (normalizer ![false,false,false,true,true,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14]).1) i j := by
  cases b5 <;> cases b6
  · exact check3_part0 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check3_part1 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check3_part2 b7 b8 b9 b10 b11 b12 b13 b14
  · exact check3_part3 b7 b8 b9 b10 b11 b12 b13 b14
#print axioms check3
end Erdos184Work.PureSixDoublePatterns
