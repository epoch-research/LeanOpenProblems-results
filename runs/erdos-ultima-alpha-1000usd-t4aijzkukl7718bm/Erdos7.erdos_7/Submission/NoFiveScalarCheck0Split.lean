import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
open Erdos7RationalGeometricBudget
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma test_good_0 : (states 0).Good := by unfold State.Good; decide +kernel
#eval IO.println "GOOD0"
lemma test_good_1 : (states 1).Good := by unfold State.Good; decide +kernel
#eval IO.println "GOOD1"
lemma test_part_0 : ∀ x : Fin 32,
    loss (primes 0) (0+x.val) + budget (primes 0) (cap (primes 0)) (states 1).eval
      (states 1).slope (501/(0+x.val)) (0+x.val) ≤ (states 0).eval (0+x.val) := by
  decide +kernel
#eval IO.println "PART 0"
lemma test_part_32 : ∀ x : Fin 32,
    loss (primes 0) (32+x.val) + budget (primes 0) (cap (primes 0)) (states 1).eval
      (states 1).slope (501/(32+x.val)) (32+x.val) ≤ (states 0).eval (32+x.val) := by
  decide +kernel
#eval IO.println "PART 32"
lemma test_part_64 : ∀ x : Fin 32,
    loss (primes 0) (64+x.val) + budget (primes 0) (cap (primes 0)) (states 1).eval
      (states 1).slope (501/(64+x.val)) (64+x.val) ≤ (states 0).eval (64+x.val) := by
  decide +kernel
#eval IO.println "PART 64"
lemma test_part_96 : ∀ x : Fin 32,
    loss (primes 0) (96+x.val) + budget (primes 0) (cap (primes 0)) (states 1).eval
      (states 1).slope (501/(96+x.val)) (96+x.val) ≤ (states 0).eval (96+x.val) := by
  decide +kernel
#eval IO.println "PART 96"
lemma test_part_128 : ∀ x : Fin 32,
    loss (primes 0) (128+x.val) + budget (primes 0) (cap (primes 0)) (states 1).eval
      (states 1).slope (501/(128+x.val)) (128+x.val) ≤ (states 0).eval (128+x.val) := by
  decide +kernel
#eval IO.println "PART 128"
lemma test_part_160 : ∀ x : Fin 32,
    loss (primes 0) (160+x.val) + budget (primes 0) (cap (primes 0)) (states 1).eval
      (states 1).slope (501/(160+x.val)) (160+x.val) ≤ (states 0).eval (160+x.val) := by
  decide +kernel
#eval IO.println "PART 160"
lemma test_part_192 : ∀ x : Fin 32,
    loss (primes 0) (192+x.val) + budget (primes 0) (cap (primes 0)) (states 1).eval
      (states 1).slope (501/(192+x.val)) (192+x.val) ≤ (states 0).eval (192+x.val) := by
  decide +kernel
#eval IO.println "PART 192"
lemma test_part_224 : ∀ x : Fin 32,
    loss (primes 0) (224+x.val) + budget (primes 0) (cap (primes 0)) (states 1).eval
      (states 1).slope (501/(224+x.val)) (224+x.val) ≤ (states 0).eval (224+x.val) := by
  decide +kernel
#eval IO.println "PART 224"
lemma test_part_256 : ∀ x : Fin 32,
    loss (primes 0) (256+x.val) + budget (primes 0) (cap (primes 0)) (states 1).eval
      (states 1).slope (501/(256+x.val)) (256+x.val) ≤ (states 0).eval (256+x.val) := by
  decide +kernel
#eval IO.println "PART 256"
lemma test_part_288 : ∀ x : Fin 32,
    loss (primes 0) (288+x.val) + budget (primes 0) (cap (primes 0)) (states 1).eval
      (states 1).slope (501/(288+x.val)) (288+x.val) ≤ (states 0).eval (288+x.val) := by
  decide +kernel
#eval IO.println "PART 288"
lemma test_part_320 : ∀ x : Fin 32,
    loss (primes 0) (320+x.val) + budget (primes 0) (cap (primes 0)) (states 1).eval
      (states 1).slope (501/(320+x.val)) (320+x.val) ≤ (states 0).eval (320+x.val) := by
  decide +kernel
#eval IO.println "PART 320"
lemma test_part_352 : ∀ x : Fin 32,
    loss (primes 0) (352+x.val) + budget (primes 0) (cap (primes 0)) (states 1).eval
      (states 1).slope (501/(352+x.val)) (352+x.val) ≤ (states 0).eval (352+x.val) := by
  decide +kernel
#eval IO.println "PART 352"
lemma test_part_384 : ∀ x : Fin 32,
    loss (primes 0) (384+x.val) + budget (primes 0) (cap (primes 0)) (states 1).eval
      (states 1).slope (501/(384+x.val)) (384+x.val) ≤ (states 0).eval (384+x.val) := by
  decide +kernel
#eval IO.println "PART 384"
lemma test_part_416 : ∀ x : Fin 32,
    loss (primes 0) (416+x.val) + budget (primes 0) (cap (primes 0)) (states 1).eval
      (states 1).slope (501/(416+x.val)) (416+x.val) ≤ (states 0).eval (416+x.val) := by
  decide +kernel
#eval IO.println "PART 416"
lemma test_part_448 : ∀ x : Fin 32,
    loss (primes 0) (448+x.val) + budget (primes 0) (cap (primes 0)) (states 1).eval
      (states 1).slope (501/(448+x.val)) (448+x.val) ≤ (states 0).eval (448+x.val) := by
  decide +kernel
#eval IO.println "PART 448"
lemma test_part_480 : ∀ x : Fin 22,
    loss (primes 0) (480+x.val) + budget (primes 0) (cap (primes 0)) (states 1).eval
      (states 1).slope (501/(480+x.val)) (480+x.val) ≤ (states 0).eval (480+x.val) := by
  decide +kernel
#eval IO.println "PART 480"
end Erdos7NoFiveScalar
