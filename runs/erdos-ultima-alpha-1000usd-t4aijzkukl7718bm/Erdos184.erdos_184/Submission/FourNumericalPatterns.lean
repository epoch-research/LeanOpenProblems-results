import Submission.MaximumTriplePatterns

/-! The nine numerical four-color contact patterns, up to permutation of colors.
This is only a numerical classification; cyclic-order completeness is separate. -/
namespace Erdos184Work.FourNumericalPatterns
open MaximumCoreFamilies
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def permutations : Fin 24 → Fin 4 → Fin 4 :=
  ![![0,1,2,3],
    ![0,1,3,2],
    ![0,2,1,3],
    ![0,2,3,1],
    ![0,3,1,2],
    ![0,3,2,1],
    ![1,0,2,3],
    ![1,0,3,2],
    ![1,2,0,3],
    ![1,2,3,0],
    ![1,3,0,2],
    ![1,3,2,0],
    ![2,0,1,3],
    ![2,0,3,1],
    ![2,1,0,3],
    ![2,1,3,0],
    ![2,3,0,1],
    ![2,3,1,0],
    ![3,0,1,2],
    ![3,0,2,1],
    ![3,1,0,2],
    ![3,1,2,0],
    ![3,2,0,1],
    ![3,2,1,0]]

def representative : Fin 9 → Fin 6 → Fin 3 :=
  ![![0,2,2,2,2,0],
    ![0,2,2,2,2,1],
    ![1,1,1,1,1,1],
    ![1,1,1,1,1,2],
    ![1,1,1,1,2,2],
    ![1,1,2,1,2,2],
    ![1,1,2,2,1,1],
    ![1,1,2,2,1,2],
    ![1,2,2,2,2,1]]

def pairIndex : Fin 4 → Fin 4 → Fin 6 :=
  ![![0,0,1,2],![0,0,3,4],![1,3,0,5],![2,4,5,0]]

def between (b : Fin 6 → Fin 3) (i j : Fin 4) : Fin 3 :=
  if i = j then 0 else b (pairIndex i j)

def Admissible (b : Fin 6 → Fin 3) : Prop :=
  AdmissibleTriple (b 0).val (b 1).val (b 3).val ∧
  AdmissibleTriple (b 0).val (b 2).val (b 4).val ∧
  AdmissibleTriple (b 1).val (b 2).val (b 5).val ∧
  AdmissibleTriple (b 3).val (b 4).val (b 5).val

instance (b : Fin 6 → Fin 3) : Decidable (Admissible b) := by
  unfold Admissible AdmissibleTriple
  infer_instance

def encode (b : Fin 6 → Fin 3) : ℕ :=
  (b 0).val + 3*(b 1).val + 9*(b 2).val + 27*(b 3).val +
    81*(b 4).val + 243*(b 5).val

def witnessCode : ℕ → ℕ
  | 240 => 0
  | 241 => 40
  | 364 => 48
  | 365 => 88
  | 367 => 82
  | 368 => 117
  | 373 => 80
  | 374 => 111
  | 376 => 105
  | 377 => 129
  | 391 => 76
  | 392 => 115
  | 394 => 114
  | 400 => 144
  | 401 => 184
  | 403 => 178
  | 445 => 74
  | 446 => 109
  | 448 => 145
  | 449 => 185
  | 454 => 108
  | 457 => 176
  | 472 => 99
  | 473 => 123
  | 475 => 172
  | 481 => 170
  | 483 => 24
  | 484 => 192
  | 560 => 2
  | 563 => 34
  | 607 => 72
  | 608 => 147
  | 610 => 103
  | 611 => 179
  | 616 => 102
  | 617 => 177
  | 634 => 97
  | 635 => 173
  | 637 => 121
  | 641 => 26
  | 643 => 168
  | 644 => 194
  | 656 => 4
  | 665 => 32
  | 683 => 28
  | 688 => 96
  | 689 => 171
  | 691 => 169
  | 692 => 196
  | 697 => 120
  | _ => 0

def normalizer (b : Fin 6 → Fin 3) : Fin 9 × Fin 24 :=
  (Fin.ofNat 9 (witnessCode (encode b) / 24), Fin.ofNat 24 (witnessCode (encode b)))

lemma permutations_bijective (i : Fin 24) : Function.Bijective (permutations i) := by
  fin_cases i <;> decide

lemma table_correct (a b c d e f : Fin 3) :
    Admissible ![a,b,c,d,e,f] → ∀ i j : Fin 4,
      between ![a,b,c,d,e,f] (permutations (normalizer ![a,b,c,d,e,f]).2 i)
        (permutations (normalizer ![a,b,c,d,e,f]).2 j) =
      between (representative (normalizer ![a,b,c,d,e,f]).1) i j := by
  revert a b c d e f
  decide +kernel

lemma classified (b : Fin 6 → Fin 3) (hb : Admissible b) :
    ∃ k : Fin 9, ∃ p : Equiv.Perm (Fin 4), ∀ i j,
      between b (p i) (p j) = between (representative k) i j := by
  have he : b = ![b 0,b 1,b 2,b 3,b 4,b 5] := by
    funext i
    fin_cases i <;> rfl
  have ht := table_correct (b 0) (b 1) (b 2) (b 3) (b 4) (b 5)
  rw [← he] at ht
  refine ⟨(normalizer b).1, Equiv.ofBijective (permutations (normalizer b).2)
    (permutations_bijective _), ht hb⟩

#print axioms classified
end Erdos184Work.FourNumericalPatterns
