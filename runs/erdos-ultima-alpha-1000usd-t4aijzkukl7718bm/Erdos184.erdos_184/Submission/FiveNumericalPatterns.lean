import Submission.AllowedFourDoubleBound

/-! The five numerical contact patterns on five colors, assuming positive
contacts and at most two doubled pairs on every four-color subset. -/
namespace Erdos184Work.FiveNumericalPatterns
open PairJunctionCoding
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def permutations : Fin 120 → Fin 5 → Fin 5 := ![
  ![0,1,2,3,4],
  ![0,1,2,4,3],
  ![0,1,3,2,4],
  ![0,1,3,4,2],
  ![0,1,4,2,3],
  ![0,1,4,3,2],
  ![0,2,1,3,4],
  ![0,2,1,4,3],
  ![0,2,3,1,4],
  ![0,2,3,4,1],
  ![0,2,4,1,3],
  ![0,2,4,3,1],
  ![0,3,1,2,4],
  ![0,3,1,4,2],
  ![0,3,2,1,4],
  ![0,3,2,4,1],
  ![0,3,4,1,2],
  ![0,3,4,2,1],
  ![0,4,1,2,3],
  ![0,4,1,3,2],
  ![0,4,2,1,3],
  ![0,4,2,3,1],
  ![0,4,3,1,2],
  ![0,4,3,2,1],
  ![1,0,2,3,4],
  ![1,0,2,4,3],
  ![1,0,3,2,4],
  ![1,0,3,4,2],
  ![1,0,4,2,3],
  ![1,0,4,3,2],
  ![1,2,0,3,4],
  ![1,2,0,4,3],
  ![1,2,3,0,4],
  ![1,2,3,4,0],
  ![1,2,4,0,3],
  ![1,2,4,3,0],
  ![1,3,0,2,4],
  ![1,3,0,4,2],
  ![1,3,2,0,4],
  ![1,3,2,4,0],
  ![1,3,4,0,2],
  ![1,3,4,2,0],
  ![1,4,0,2,3],
  ![1,4,0,3,2],
  ![1,4,2,0,3],
  ![1,4,2,3,0],
  ![1,4,3,0,2],
  ![1,4,3,2,0],
  ![2,0,1,3,4],
  ![2,0,1,4,3],
  ![2,0,3,1,4],
  ![2,0,3,4,1],
  ![2,0,4,1,3],
  ![2,0,4,3,1],
  ![2,1,0,3,4],
  ![2,1,0,4,3],
  ![2,1,3,0,4],
  ![2,1,3,4,0],
  ![2,1,4,0,3],
  ![2,1,4,3,0],
  ![2,3,0,1,4],
  ![2,3,0,4,1],
  ![2,3,1,0,4],
  ![2,3,1,4,0],
  ![2,3,4,0,1],
  ![2,3,4,1,0],
  ![2,4,0,1,3],
  ![2,4,0,3,1],
  ![2,4,1,0,3],
  ![2,4,1,3,0],
  ![2,4,3,0,1],
  ![2,4,3,1,0],
  ![3,0,1,2,4],
  ![3,0,1,4,2],
  ![3,0,2,1,4],
  ![3,0,2,4,1],
  ![3,0,4,1,2],
  ![3,0,4,2,1],
  ![3,1,0,2,4],
  ![3,1,0,4,2],
  ![3,1,2,0,4],
  ![3,1,2,4,0],
  ![3,1,4,0,2],
  ![3,1,4,2,0],
  ![3,2,0,1,4],
  ![3,2,0,4,1],
  ![3,2,1,0,4],
  ![3,2,1,4,0],
  ![3,2,4,0,1],
  ![3,2,4,1,0],
  ![3,4,0,1,2],
  ![3,4,0,2,1],
  ![3,4,1,0,2],
  ![3,4,1,2,0],
  ![3,4,2,0,1],
  ![3,4,2,1,0],
  ![4,0,1,2,3],
  ![4,0,1,3,2],
  ![4,0,2,1,3],
  ![4,0,2,3,1],
  ![4,0,3,1,2],
  ![4,0,3,2,1],
  ![4,1,0,2,3],
  ![4,1,0,3,2],
  ![4,1,2,0,3],
  ![4,1,2,3,0],
  ![4,1,3,0,2],
  ![4,1,3,2,0],
  ![4,2,0,1,3],
  ![4,2,0,3,1],
  ![4,2,1,0,3],
  ![4,2,1,3,0],
  ![4,2,3,0,1],
  ![4,2,3,1,0],
  ![4,3,0,1,2],
  ![4,3,0,2,1],
  ![4,3,1,0,2],
  ![4,3,1,2,0],
  ![4,3,2,0,1],
  ![4,3,2,1,0]]

def representative : Fin 5 → Fin 10 → Bool := ![
  ![false,false,false,false,false,false,false,false,false,false],
  ![true,false,false,false,false,false,false,false,false,false],
  ![true,true,false,false,false,false,false,false,false,false],
  ![true,false,false,false,false,false,false,true,false,false],
  ![true,true,false,false,false,false,false,false,false,true]]

def pairIndex : Fin 5 → Fin 5 → Fin 10 := ![
  ![0,0,1,2,3],
  ![0,0,4,5,6],
  ![1,4,0,7,8],
  ![2,5,7,0,9],
  ![3,6,8,9,0]]

def pairCoords : Fin 10 → Fin 5 × Fin 5 := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

def omission : Fin 5 → Fin 6 → Fin 10 := ![
  ![4,5,6,7,8,9],
  ![1,2,3,7,8,9],
  ![0,2,3,5,6,9],
  ![0,1,3,4,6,8],
  ![0,1,2,4,5,7]]

def embedding : Fin 5 → Fin 4 → Fin 5 := ![
  ![1,2,3,4],
  ![0,2,3,4],
  ![0,1,3,4],
  ![0,1,2,4],
  ![0,1,2,3]]

def between (b : Fin 10 → Bool) (i j : Fin 5) : ℕ :=
  if i = j then 0 else 1 + (b (pairIndex i j)).toNat

def Admissible (b : Fin 10 → Bool) : Prop :=
  ∀ v : Fin 5, (Finset.univ.filter (fun q : Fin 6 => b (omission v q))).card ≤ 2

instance (b : Fin 10 → Bool) : Decidable (Admissible b) := by
  unfold Admissible
  infer_instance

def encode (b : Fin 10 → Bool) : ℕ :=
  (b 0).toNat + 2*(b 1).toNat + 4*(b 2).toNat + 8*(b 3).toNat + 16*(b 4).toNat + 32*(b 5).toNat + 64*(b 6).toNat + 128*(b 7).toNat + 256*(b 8).toNat + 512*(b 9).toNat

def witnessCode : ℕ → ℕ
  | 0 => 0
  | 1 => 120
  | 2 => 126
  | 3 => 240
  | 4 => 132
  | 5 => 242
  | 6 => 248
  | 8 => 138
  | 9 => 244
  | 10 => 250
  | 12 => 256
  | 16 => 150
  | 17 => 264
  | 18 => 288
  | 20 => 372
  | 24 => 378
  | 28 => 496
  | 32 => 156
  | 33 => 266
  | 34 => 366
  | 36 => 312
  | 40 => 379
  | 42 => 490
  | 48 => 272
  | 56 => 512
  | 64 => 162
  | 65 => 268
  | 66 => 367
  | 68 => 373
  | 70 => 488
  | 72 => 336
  | 80 => 274
  | 84 => 514
  | 96 => 280
  | 98 => 520
  | 128 => 180
  | 129 => 360
  | 130 => 290
  | 132 => 314
  | 136 => 381
  | 137 => 484
  | 144 => 296
  | 152 => 536
  | 160 => 320
  | 168 => 560
  | 192 => 405
  | 193 => 508
  | 194 => 530
  | 196 => 554
  | 200 => 576
  | 256 => 186
  | 257 => 361
  | 258 => 292
  | 260 => 375
  | 261 => 482
  | 264 => 338
  | 272 => 298
  | 276 => 538
  | 288 => 399
  | 289 => 506
  | 290 => 532
  | 292 => 552
  | 296 => 578
  | 320 => 344
  | 324 => 584
  | 384 => 304
  | 385 => 544
  | 512 => 210
  | 513 => 363
  | 514 => 369
  | 515 => 480
  | 516 => 316
  | 520 => 340
  | 528 => 393
  | 529 => 504
  | 530 => 528
  | 532 => 556
  | 536 => 580
  | 544 => 322
  | 546 => 562
  | 576 => 346
  | 578 => 586
  | 640 => 328
  | 641 => 568
  | 768 => 352
  | 769 => 592
  | _ => 0

def normalizer (b : Fin 10 → Bool) : Fin 5 × Fin 120 :=
  (Fin.ofNat 5 (witnessCode (encode b) / 120), Fin.ofNat 120 (witnessCode (encode b)))

lemma permutations_bijective (i : Fin 120) : Function.Bijective (permutations i) := by
  fin_cases i <;> decide

lemma embedding_injective (v : Fin 5) : Function.Injective (embedding v) := by
  fin_cases v <;> decide

lemma pairCoords_pairIndex : ∀ i j : Fin 5, i ≠ j →
    pairCoords (pairIndex i j) = (i,j) ∨ pairCoords (pairIndex i j) = (j,i) := by
  decide +kernel

lemma pairCoords_ne : ∀ q, (pairCoords q).1 ≠ (pairCoords q).2 := by decide +kernel

lemma table_correct (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Bool) :
    Admissible ![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9] → ∀ i j : Fin 5,
      between ![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9] (permutations (normalizer ![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9]).2 i)
        (permutations (normalizer ![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9]).2 j) =
      between (representative (normalizer ![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9]).1) i j := by
  revert a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  decide +kernel

lemma omit_double_card (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Bool) : ∀ v : Fin 5,
    (Finset.univ.filter (fun q : Fin 6 => (![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9] : Fin 10 → Bool) (omission v q))).card =
      (AllowedFourCounts.doublePairs (fun i j => between ![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9] (embedding v i) (embedding v j))).card := by
  revert a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  decide +kernel

lemma classified (b : Fin 10 → Bool) (hb : Admissible b) :
    ∃ k : Fin 5, ∃ p : Equiv.Perm (Fin 5), ∀ i j,
      between b (p i) (p j) = between (representative k) i j := by
  have he : b = ![b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9] := by
    funext i
    fin_cases i <;> rfl
  have ht := table_correct (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9)
  rw [← he] at ht
  refine ⟨(normalizer b).1, Equiv.ofBijective (permutations (normalizer b).2)
    (permutations_bijective _), ht hb⟩

#print axioms classified
#print axioms omit_double_card
end Erdos184Work.FiveNumericalPatterns
