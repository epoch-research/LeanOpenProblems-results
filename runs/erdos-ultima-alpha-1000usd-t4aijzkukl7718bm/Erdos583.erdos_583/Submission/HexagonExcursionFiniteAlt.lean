import Submission.Work

/-! Finite certificates for a hexagon with a selected split path link. -/
namespace Erdos583HexagonExcursionRoutesDevelopment
open SimpleGraph Erdos583Work Erdos583Work.PieceRoutes
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option Elab.async false

def extended (p : Fin 6 → Fin 6) (d : Fin 5) (i : Fin 7) : Fin 7 :=
  if h : i.val ≤ d.val then (p ⟨i.val,by omega⟩).castSucc
  else if i.val=d.val+1 then 6 else (p ⟨i.val-1,by omega⟩).castSucc

def pieceSource (p : Fin 6 → Fin 6) (d : Fin 5) (e : Fin 12) : Fin 7 :=
  if h : e.val < 6 then (⟨e.val,h⟩ : Fin 6).castSucc
  else extended p d ⟨e.val-6,by omega⟩

def pieceTarget (p : Fin 6 → Fin 6) (d : Fin 5) (e : Fin 12) : Fin 7 :=
  if e.val < 6 then (⟨(e.val+1)%6,Nat.mod_lt _ (by decide)⟩ : Fin 6).castSucc
  else extended p d ⟨e.val-5,by omega⟩

def adjacent (a b : Fin 6) : Prop := (a.val+1)%6=b.val ∨ (b.val+1)%6=a.val
instance (a b : Fin 6) : Decidable (adjacent a b) := inferInstanceAs (Decidable (_ ∨ _))

abbrev Steps := List (Fin 12 × Bool)

def Valid (p : Fin 6 → Fin 6) (d : Fin 5) (v : Steps × Steps) : Prop :=
  Route.compatible (s := pieceSource p d) (t := pieceTarget p d) (p 0).castSucc 6 v.1=true ∧
  Route.compatible (s := pieceSource p d) (t := pieceTarget p d) (p 5).castSucc 6 v.2=true ∧
  ((p 0).castSucc :: v.1.map (fun ed ↦ target (pieceSource p d) (pieceTarget p d) ed.1 ed.2)).Nodup ∧
  ((p 5).castSucc :: v.2.map (fun ed ↦ target (pieceSource p d) (pieceTarget p d) ed.1 ed.2)).Nodup ∧
  (∀ e : Fin 12, e ∈ v.1.map Prod.fst → e ∉ v.2.map Prod.fst) ∧
  ∀ e : Fin 12, e ∈ v.1.map Prod.fst ∨ e ∈ v.2.map Prod.fst

instance (p : Fin 6 → Fin 6) (d : Fin 5) (v : Steps × Steps) : Decidable (Valid p d v) := by
  unfold Valid
  infer_instance

def code (p : Fin 6 → Fin 6) (d : Fin 5) : ℕ :=
  (p 0).val+6*(p 1).val+36*(p 2).val+216*(p 3).val+1296*(p 4).val+7776*(p 5).val+46656*d.val

def GoodGap (p : Fin 6 → Fin 6) (d : Fin 5) : Prop := adjacent (p 1) (p 2) → d=1
instance (p : Fin 6 → Fin 6) (d : Fin 5) : Decidable (GoodGap p d) := inferInstanceAs (Decidable (_ → _))

def chosenGap (p : Fin 6 → Fin 6) (d : Fin 5) : Fin 5 := if adjacent (p 1) (p 2) then 1 else d

lemma chosenGap_good (p : Fin 6 → Fin 6) (d : Fin 5) : GoodGap p (chosenGap p d) := by
  intro h
  simp [chosenGap,h]

lemma chosenGap_spec (p : Fin 6 → Fin 6) (d : Fin 5) :
    chosenGap p d=d ∨ adjacent (p (chosenGap p d).castSucc) (p (chosenGap p d).succ) := by
  by_cases h : adjacent (p 1) (p 2)
  · simp only [chosenGap,if_pos h]
    exact Or.inr h
  · exact Or.inl (by simp [chosenGap,h])

inductive CertificateTree where
  | empty : CertificateTree
  | node (key : ℕ) (value : Steps × Steps) (left right : CertificateTree) : CertificateTree

def CertificateTree.lookup (t : CertificateTree) (key : ℕ) : Option (Steps × Steps) :=
  match t with
  | .empty => none
  | .node k v l r => if key=k then some v else if key<k then l.lookup key else r.lookup key

def certificates : CertificateTree :=
(.node 99117 ([(2,false),(1,false),(0,false),(11,false),(4,true),(8,true)],[(5,false),(7,false),(6,false),(3,true),(10,false),(9,false)])
  (.node 60281 ([(4,false),(3,false),(2,false),(1,false),(0,false),(8,false)],[(11,false),(10,false),(9,false),(5,false),(6,true),(7,true)])
    (.node 31820 ([(1,false),(0,false),(10,false),(3,true),(4,true),(7,false)],[(11,false),(5,false),(8,true),(9,true),(2,false),(6,true)])
      (.node 16535 ([(4,false),(3,false),(2,false),(11,false),(0,true),(7,false)],[(1,false),(8,true),(9,true),(10,true),(5,false),(6,true)])
        (.node 12545 ([(4,false),(3,false),(11,true),(0,false),(8,false),(7,false)],[(1,true),(2,true),(10,false),(9,false),(5,false),(6,true)])
          (.node 4855 ([(0,false),(11,false),(3,true),(9,false),(8,false),(7,false)],[(5,false),(4,false),(10,true),(2,false),(1,false),(6,true)])
            (.node 3655 ([(0,false),(11,false),(10,false),(4,true),(8,false),(7,false)],[(5,false),(9,true),(3,false),(2,false),(1,false),(6,true)])
              (.node 3525 ([(2,false),(10,false),(9,false),(0,false),(5,false),(7,false)],[(11,false),(1,false),(8,false),(4,false),(3,false),(6,true)])
                (.node 3430 ([(3,false),(2,false),(11,true),(5,false),(8,false),(7,false)],[(0,true),(1,true),(10,false),(9,false),(4,false),(6,true)])
                  (.node 3395 ([(5,true),(11,false),(2,true),(3,true),(8,false),(7,false)],[(0,true),(1,true),(10,false),(9,false),(4,true),(6,true)])
                    .empty
                    .empty)
                  (.node 3515 ([(5,true),(0,true),(1,true),(10,false),(3,false),(7,false)],[(11,false),(2,true),(8,true),(9,true),(4,true),(6,true)])
                    .empty
                    .empty))
                (.node 3595 ([(0,false),(11,false),(2,true),(3,true),(4,true),(7,false)],[(5,false),(8,true),(9,true),(10,true),(1,false),(6,true)])
                  (.node 3575 ([(5,true),(11,false),(10,false),(3,false),(8,false),(7,false)],[(0,true),(1,true),(2,true),(9,true),(4,true),(6,true)])
                    .empty
                    .empty)
                  (.node 3645 ([(2,false),(10,false),(4,true),(5,true),(0,true),(7,false)],[(11,false),(1,false),(8,true),(9,true),(3,false),(6,true)])
                    .empty
                    .empty)))
              (.node 4300 ([(3,false),(10,false),(0,false),(5,false),(8,false),(7,false)],[(11,false),(2,false),(1,false),(9,false),(4,false),(6,true)])
                (.node 3825 ([(2,false),(11,true),(5,false),(4,false),(8,false),(7,false)],[(0,true),(1,true),(10,false),(9,false),(3,false),(6,true)])
                  (.node 3790 ([(3,false),(2,false),(10,false),(5,true),(0,true),(7,false)],[(11,false),(1,false),(8,true),(9,true),(4,false),(6,true)])
                    .empty
                    .empty)
                  (.node 4265 ([(5,true),(0,true),(9,false),(3,false),(2,false),(7,false)],[(11,false),(10,false),(1,true),(8,true),(4,true),(6,true)])
                    .empty
                    .empty))
                (.node 4510 ([(3,false),(2,false),(9,false),(5,true),(0,true),(7,false)],[(11,false),(10,false),(1,false),(8,true),(4,false),(6,true)])
                  (.node 4475 ([(5,true),(11,false),(2,false),(9,false),(8,false),(7,false)],[(0,true),(1,true),(10,true),(3,true),(4,true),(6,true)])
                    .empty
                    .empty)
                  (.node 4820 ([(1,false),(0,false),(11,false),(3,true),(4,true),(7,false)],[(5,false),(8,true),(9,true),(10,true),(2,false),(6,true)])
                    .empty
                    .empty))))
            (.node 5755 ([(0,false),(11,false),(10,false),(2,true),(8,false),(7,false)],[(5,false),(4,false),(3,false),(9,true),(1,false),(6,true)])
              (.node 5540 ([(1,false),(0,false),(11,false),(3,false),(8,false),(7,false)],[(5,false),(4,false),(10,false),(9,false),(2,false),(6,true)])
                (.node 5065 ([(0,false),(5,false),(9,false),(2,true),(3,true),(7,false)],[(11,false),(10,false),(4,false),(8,true),(1,false),(6,true)])
                  (.node 5030 ([(1,false),(0,false),(11,false),(10,false),(4,false),(7,false)],[(5,false),(9,false),(8,false),(3,false),(2,false),(6,true)])
                    .empty
                    .empty)
                  (.node 5505 ([(2,false),(1,false),(0,false),(11,false),(4,true),(7,false)],[(5,false),(8,true),(9,true),(10,true),(3,false),(6,true)])
                    .empty
                    .empty))
                (.node 5685 ([(2,false),(1,false),(0,false),(11,false),(4,true),(7,false)],[(5,false),(8,true),(9,true),(10,true),(3,false),(6,true)])
                  (.node 5675 ([(5,true),(11,false),(10,false),(1,false),(8,false),(7,false)],[(0,true),(9,true),(2,true),(3,true),(4,true),(6,true)])
                    .empty
                    .empty)
                  (.node 5735 ([(5,true),(11,false),(3,false),(2,false),(1,false),(7,false)],[(0,true),(8,true),(9,true),(10,true),(4,true),(6,true)])
                    .empty
                    .empty)))
              (.node 5935 ([(0,false),(11,false),(3,false),(2,false),(8,false),(7,false)],[(5,false),(4,false),(10,false),(9,false),(1,false),(6,true)])
                (.node 5815 ([(0,false),(5,false),(4,false),(10,false),(2,true),(7,false)],[(11,false),(3,false),(8,true),(9,true),(1,false),(6,true)])
                  (.node 5805 ([(2,false),(9,false),(4,false),(11,true),(0,true),(7,false)],[(5,false),(8,false),(1,true),(10,true),(3,false),(6,true)])
                    .empty
                    .empty)
                  (.node 5900 ([(1,false),(9,true),(3,true),(11,true),(5,false),(7,false)],[(0,true),(8,false),(4,false),(10,false),(2,false),(6,true)])
                    .empty
                    .empty))
                (.node 11860 ([(3,false),(11,true),(0,false),(5,false),(8,false),(7,false)],[(1,true),(2,true),(10,false),(9,false),(4,false),(6,true)])
                  (.node 11825 ([(4,false),(3,false),(10,false),(0,true),(1,true),(7,false)],[(11,false),(2,false),(8,true),(9,true),(5,false),(6,true)])
                    .empty
                    .empty)
                  .empty))))
          (.node 14150 ([(1,false),(11,false),(4,true),(9,false),(8,false),(7,false)],[(0,false),(5,false),(10,true),(3,false),(2,false),(6,true)])
            (.node 13065 ([(2,false),(1,false),(11,false),(10,false),(5,false),(7,false)],[(0,false),(9,false),(8,false),(4,false),(3,false),(6,true)])
              (.node 12820 ([(3,false),(10,false),(9,false),(1,false),(0,false),(7,false)],[(11,false),(2,false),(8,false),(5,false),(4,false),(6,true)])
                (.node 12760 ([(3,false),(10,false),(5,true),(0,true),(1,true),(7,false)],[(11,false),(2,false),(8,true),(9,true),(4,false),(6,true)])
                  (.node 12720 ([(0,true),(11,false),(3,true),(4,true),(8,false),(7,false)],[(1,true),(2,true),(10,false),(9,false),(5,true),(6,true)])
                    .empty
                    .empty)
                  (.node 12770 ([(1,false),(11,false),(10,false),(5,true),(8,false),(7,false)],[(0,false),(9,true),(4,false),(3,false),(2,false),(6,true)])
                    .empty
                    .empty))
                (.node 12890 ([(1,false),(11,false),(3,true),(4,true),(5,true),(7,false)],[(0,false),(8,true),(9,true),(10,true),(2,false),(6,true)])
                  (.node 12840 ([(0,true),(1,true),(2,true),(10,false),(4,false),(7,false)],[(11,false),(3,true),(8,true),(9,true),(5,true),(6,true)])
                    .empty
                    .empty)
                  (.node 12900 ([(0,true),(11,false),(10,false),(4,false),(8,false),(7,false)],[(1,true),(2,true),(3,true),(9,true),(5,true),(6,true)])
                    .empty
                    .empty)))
              (.node 13625 ([(4,false),(3,false),(9,false),(0,true),(1,true),(7,false)],[(11,false),(10,false),(2,false),(8,true),(5,false),(6,true)])
                (.node 13415 ([(4,false),(10,false),(1,false),(0,false),(8,false),(7,false)],[(11,false),(3,false),(2,false),(9,false),(5,false),(6,true)])
                  (.node 13100 ([(1,false),(0,false),(9,false),(3,true),(4,true),(7,false)],[(11,false),(10,false),(5,false),(8,true),(2,false),(6,true)])
                    .empty
                    .empty)
                  (.node 13590 ([(0,true),(1,true),(9,false),(4,false),(3,false),(7,false)],[(11,false),(10,false),(2,true),(8,true),(5,true),(6,true)])
                    .empty
                    .empty))
                (.node 14115 ([(2,false),(1,false),(11,false),(4,true),(5,true),(7,false)],[(0,false),(8,true),(9,true),(10,true),(3,false),(6,true)])
                  (.node 13800 ([(0,true),(11,false),(3,false),(9,false),(8,false),(7,false)],[(1,true),(2,true),(10,true),(4,true),(5,true),(6,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 15060 ([(0,true),(11,false),(4,false),(3,false),(2,false),(7,false)],[(1,true),(8,true),(9,true),(10,true),(5,true),(6,true)])
              (.node 14930 ([(1,false),(0,false),(5,false),(10,false),(3,true),(7,false)],[(11,false),(4,false),(8,true),(9,true),(2,false),(6,true)])
                (.node 14835 ([(2,false),(1,false),(11,false),(4,false),(8,false),(7,false)],[(0,false),(5,false),(10,false),(9,false),(3,false),(6,true)])
                  (.node 14800 ([(3,false),(2,false),(1,false),(11,false),(5,true),(7,false)],[(0,false),(8,true),(9,true),(10,true),(4,false),(6,true)])
                    .empty
                    .empty)
                  (.node 14920 ([(3,false),(9,false),(5,false),(11,true),(1,true),(7,false)],[(0,false),(8,false),(2,true),(10,true),(4,false),(6,true)])
                    .empty
                    .empty))
                (.node 15000 ([(0,true),(11,false),(10,false),(2,false),(8,false),(7,false)],[(1,true),(9,true),(3,true),(4,true),(5,true),(6,true)])
                  (.node 14980 ([(3,false),(2,false),(1,false),(11,false),(5,true),(7,false)],[(0,false),(8,true),(9,true),(10,true),(4,false),(6,true)])
                    .empty
                    .empty)
                  (.node 15050 ([(1,false),(11,false),(10,false),(3,true),(8,false),(7,false)],[(0,false),(5,false),(4,false),(9,true),(2,false),(6,true)])
                    .empty
                    .empty)))
              (.node 16390 ([(3,false),(2,false),(11,false),(5,false),(8,false),(7,false)],[(1,false),(0,false),(10,false),(9,false),(4,false),(6,true)])
                (.node 15230 ([(1,false),(11,false),(4,false),(3,false),(8,false),(7,false)],[(0,false),(5,false),(10,false),(9,false),(2,false),(6,true)])
                  (.node 15195 ([(2,false),(9,true),(4,true),(11,true),(0,false),(7,false)],[(1,true),(8,false),(5,false),(10,false),(3,false),(6,true)])
                    .empty
                    .empty)
                  (.node 16355 ([(4,false),(3,false),(2,false),(11,false),(0,true),(7,false)],[(1,false),(8,true),(9,true),(10,true),(5,false),(6,true)])
                    .empty
                    .empty))
                (.node 16485 ([(2,false),(1,false),(0,false),(10,false),(4,true),(7,false)],[(11,false),(5,false),(8,true),(9,true),(3,false),(6,true)])
                  (.node 16475 ([(4,false),(9,false),(0,false),(11,true),(2,true),(7,false)],[(1,false),(8,false),(3,true),(10,true),(5,false),(6,true)])
                    .empty
                    .empty)
                  .empty)))))
        (.node 24470 ([(2,true),(11,false),(5,false),(9,false),(8,false),(7,false)],[(3,true),(4,true),(10,true),(0,true),(1,true),(6,true)])
          (.node 21870 ([(0,true),(9,true),(4,false),(11,true),(2,true),(7,false)],[(1,false),(8,false),(3,true),(10,false),(5,true),(6,true)])
            (.node 20855 ([(4,false),(10,false),(9,false),(2,false),(1,false),(7,false)],[(11,false),(3,false),(8,false),(0,false),(5,false),(6,true)])
              (.node 16750 ([(3,false),(9,true),(5,true),(11,true),(1,false),(7,false)],[(2,true),(8,false),(0,false),(10,false),(4,false),(6,true)])
                (.node 16605 ([(2,false),(11,false),(10,false),(4,true),(8,false),(7,false)],[(1,false),(0,false),(5,false),(9,true),(3,false),(6,true)])
                  (.node 16555 ([(1,true),(11,false),(10,false),(3,false),(8,false),(7,false)],[(2,true),(9,true),(4,true),(5,true),(0,true),(6,true)])
                    .empty
                    .empty)
                  (.node 16615 ([(1,true),(11,false),(5,false),(4,false),(3,false),(7,false)],[(2,true),(8,true),(9,true),(10,true),(0,true),(6,true)])
                    .empty
                    .empty))
                (.node 20795 ([(4,false),(10,false),(0,true),(1,true),(2,true),(7,false)],[(11,false),(3,false),(8,true),(9,true),(5,false),(6,true)])
                  (.node 16785 ([(2,false),(11,false),(5,false),(4,false),(8,false),(7,false)],[(1,false),(0,false),(10,false),(9,false),(3,false),(6,true)])
                    .empty
                    .empty)
                  (.node 20805 ([(2,false),(11,false),(10,false),(0,true),(8,false),(7,false)],[(1,false),(9,true),(5,false),(4,false),(3,false),(6,true)])
                    .empty
                    .empty)))
              (.node 20975 ([(4,false),(11,true),(1,false),(0,false),(8,false),(7,false)],[(2,true),(3,true),(10,false),(9,false),(5,false),(6,true)])
                (.node 20925 ([(2,false),(11,false),(4,true),(5,true),(0,true),(7,false)],[(1,false),(8,true),(9,true),(10,true),(3,false),(6,true)])
                  (.node 20875 ([(1,true),(2,true),(3,true),(10,false),(5,false),(7,false)],[(11,false),(4,true),(8,true),(9,true),(0,true),(6,true)])
                    .empty
                    .empty)
                  (.node 20935 ([(1,true),(11,false),(10,false),(5,false),(8,false),(7,false)],[(2,true),(3,true),(4,true),(9,true),(0,true),(6,true)])
                    .empty
                    .empty))
                (.node 21835 ([(1,true),(11,false),(4,true),(5,true),(8,false),(7,false)],[(2,true),(3,true),(10,false),(9,false),(0,true),(6,true)])
                  (.node 21150 ([(0,true),(1,true),(11,false),(4,true),(8,false),(7,false)],[(2,true),(3,true),(10,false),(9,false),(5,true),(6,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 22950 ([(0,true),(1,true),(11,false),(4,false),(3,false),(7,false)],[(2,true),(8,true),(9,true),(10,true),(5,true),(6,true)])
              (.node 22395 ([(2,false),(1,false),(9,false),(4,true),(5,true),(7,false)],[(11,false),(10,false),(0,false),(8,true),(3,false),(6,true)])
                (.node 22185 ([(2,false),(11,false),(5,true),(9,false),(8,false),(7,false)],[(1,false),(0,false),(10,true),(4,false),(3,false),(6,true)])
                  (.node 22150 ([(3,false),(2,false),(11,false),(5,true),(0,true),(7,false)],[(1,false),(8,true),(9,true),(10,true),(4,false),(6,true)])
                    .empty
                    .empty)
                  (.node 22360 ([(3,false),(2,false),(11,false),(10,false),(0,false),(7,false)],[(1,false),(9,false),(8,false),(5,false),(4,false),(6,true)])
                    .empty
                    .empty))
                (.node 22740 ([(0,true),(1,true),(11,false),(10,false),(3,true),(7,false)],[(2,true),(9,false),(8,false),(4,true),(5,true),(6,true)])
                  (.node 22705 ([(1,true),(2,true),(9,false),(5,false),(4,false),(7,false)],[(11,false),(10,false),(3,true),(8,true),(0,true),(6,true)])
                    .empty
                    .empty)
                  (.node 22915 ([(1,true),(11,false),(4,false),(9,false),(8,false),(7,false)],[(2,true),(3,true),(10,true),(5,true),(0,true),(6,true)])
                    .empty
                    .empty)))
              (.node 23950 ([(3,false),(2,false),(9,false),(5,true),(0,true),(7,false)],[(11,false),(10,false),(1,false),(8,true),(4,false),(6,true)])
                (.node 23740 ([(3,false),(11,false),(0,true),(9,false),(8,false),(7,false)],[(2,false),(1,false),(10,true),(5,false),(4,false),(6,true)])
                  (.node 23705 ([(4,false),(3,false),(11,false),(0,true),(1,true),(7,false)],[(2,false),(8,true),(9,true),(10,true),(5,false),(6,true)])
                    .empty
                    .empty)
                  (.node 23915 ([(4,false),(3,false),(11,false),(10,false),(1,false),(7,false)],[(2,false),(9,false),(8,false),(0,false),(5,false),(6,true)])
                    .empty
                    .empty))
                (.node 24295 ([(0,false),(10,false),(3,false),(2,false),(8,false),(7,false)],[(11,false),(5,false),(4,false),(9,false),(1,false),(6,true)])
                  (.node 24260 ([(2,true),(3,true),(9,false),(0,false),(5,false),(7,false)],[(11,false),(10,false),(4,true),(8,true),(1,true),(6,true)])
                    .empty
                    .empty)
                  .empty))))
          (.node 30050 ([(2,true),(11,false),(10,false),(0,false),(8,false),(7,false)],[(3,true),(4,true),(5,true),(9,true),(1,true),(6,true)])
            (.node 25780 ([(3,false),(2,false),(1,false),(10,false),(5,true),(7,false)],[(11,false),(0,false),(8,true),(9,true),(4,false),(6,true)])
              (.node 25505 ([(4,false),(3,false),(11,false),(0,false),(8,false),(7,false)],[(2,false),(1,false),(10,false),(9,false),(5,false),(6,true)])
                (.node 24785 ([(4,false),(9,true),(0,true),(11,true),(2,false),(7,false)],[(3,true),(8,false),(1,false),(10,false),(5,false),(6,true)])
                  (.node 24505 ([(0,false),(5,false),(9,false),(2,true),(3,true),(7,false)],[(11,false),(10,false),(4,false),(8,true),(1,false),(6,true)])
                    .empty
                    .empty)
                  (.node 24820 ([(3,false),(11,false),(0,false),(5,false),(8,false),(7,false)],[(2,false),(1,false),(10,false),(9,false),(4,false),(6,true)])
                    .empty
                    .empty))
                (.node 25720 ([(3,false),(11,false),(10,false),(5,true),(8,false),(7,false)],[(2,false),(1,false),(0,false),(9,true),(4,false),(6,true)])
                  (.node 25680 ([(0,true),(11,true),(3,true),(4,true),(8,false),(7,false)],[(2,false),(1,false),(10,false),(9,false),(5,true),(6,true)])
                    .empty
                    .empty)
                  (.node 25730 ([(2,true),(11,false),(0,false),(5,false),(4,false),(7,false)],[(3,true),(8,true),(9,true),(10,true),(1,true),(6,true)])
                    .empty
                    .empty)))
              (.node 29870 ([(2,true),(11,false),(5,true),(0,true),(8,false),(7,false)],[(3,true),(4,true),(10,false),(9,false),(1,true),(6,true)])
                (.node 25850 ([(2,true),(11,false),(10,false),(4,false),(8,false),(7,false)],[(3,true),(9,true),(5,true),(0,true),(1,true),(6,true)])
                  (.node 25800 ([(0,true),(10,false),(9,false),(2,true),(3,true),(7,false)],[(11,false),(1,true),(8,false),(4,true),(5,true),(6,true)])
                    .empty
                    .empty)
                  (.node 25860 ([(0,true),(10,false),(4,false),(3,false),(2,false),(7,false)],[(11,false),(1,true),(8,true),(9,true),(5,true),(6,true)])
                    .empty
                    .empty))
                (.node 30040 ([(3,false),(11,false),(5,true),(0,true),(1,true),(7,false)],[(2,false),(8,true),(9,true),(10,true),(4,false),(6,true)])
                  (.node 29905 ([(0,false),(5,false),(11,true),(2,false),(8,false),(7,false)],[(3,true),(4,true),(10,false),(9,false),(1,false),(6,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 31460 ([(1,false),(0,false),(11,true),(3,false),(8,false),(7,false)],[(4,true),(5,true),(10,false),(9,false),(2,false),(6,true)])
              (.node 30180 ([(0,true),(9,false),(4,true),(11,true),(2,false),(7,false)],[(3,true),(8,false),(1,false),(10,true),(5,true),(6,true)])
                (.node 30120 ([(0,true),(1,true),(2,true),(11,false),(4,false),(7,false)],[(3,true),(8,true),(9,true),(10,true),(5,true),(6,true)])
                  (.node 30100 ([(3,false),(11,false),(10,false),(1,true),(8,false),(7,false)],[(2,false),(9,true),(0,false),(5,false),(4,false),(6,true)])
                    .empty
                    .empty)
                  (.node 30170 ([(2,true),(3,true),(4,true),(10,false),(0,false),(7,false)],[(11,false),(5,true),(8,true),(9,true),(1,true),(6,true)])
                    .empty
                    .empty))
                (.node 30300 ([(0,true),(1,true),(2,true),(11,false),(4,false),(7,false)],[(3,true),(8,true),(9,true),(10,true),(5,true),(6,true)])
                  (.node 30265 ([(0,false),(5,false),(10,false),(2,true),(3,true),(7,false)],[(11,false),(4,false),(8,true),(9,true),(1,false),(6,true)])
                    .empty
                    .empty)
                  (.node 31425 ([(3,true),(11,false),(0,true),(1,true),(8,false),(7,false)],[(4,true),(5,true),(10,false),(9,false),(2,true),(6,true)])
                    .empty
                    .empty)))
              (.node 31675 ([(0,false),(10,false),(2,true),(3,true),(4,true),(7,false)],[(11,false),(5,false),(8,true),(9,true),(1,false),(6,true)])
                (.node 31605 ([(3,true),(11,false),(10,false),(1,false),(8,false),(7,false)],[(4,true),(5,true),(0,true),(9,true),(2,true),(6,true)])
                  (.node 31595 ([(4,false),(11,false),(0,true),(1,true),(2,true),(7,false)],[(3,false),(8,true),(9,true),(10,true),(5,false),(6,true)])
                    .empty
                    .empty)
                  (.node 31655 ([(4,false),(11,false),(10,false),(2,true),(8,false),(7,false)],[(3,false),(9,true),(1,false),(0,false),(5,false),(6,true)])
                    .empty
                    .empty))
                (.node 31735 ([(0,false),(10,false),(9,false),(4,false),(3,false),(7,false)],[(11,false),(5,false),(8,false),(2,false),(1,false),(6,true)])
                  (.node 31725 ([(3,true),(4,true),(5,true),(10,false),(1,false),(7,false)],[(11,false),(0,true),(8,true),(9,true),(2,true),(6,true)])
                    .empty
                    .empty)
                  .empty))))))
      (.node 50446 ([(3,false),(2,false),(10,false),(5,true),(0,true),(7,true)],[(11,false),(1,false),(6,false),(4,true),(9,false),(8,false)])
        (.node 41590 ([(4,true),(5,true),(9,false),(2,false),(1,false),(7,false)],[(11,false),(10,false),(0,true),(8,true),(3,true),(6,true)])
          (.node 33895 ([(0,false),(5,false),(4,false),(11,false),(2,true),(7,false)],[(3,false),(8,true),(9,true),(10,true),(1,false),(6,true)])
            (.node 33555 ([(3,true),(4,true),(9,false),(1,false),(0,false),(7,false)],[(11,false),(10,false),(5,true),(8,true),(2,true),(6,true)])
              (.node 32855 ([(4,false),(11,false),(1,true),(9,false),(8,false),(7,false)],[(3,false),(2,false),(10,true),(0,false),(5,false),(6,true)])
                (.node 32505 ([(3,true),(11,false),(0,false),(9,false),(8,false),(7,false)],[(4,true),(5,true),(10,true),(1,true),(2,true),(6,true)])
                  (.node 31855 ([(0,false),(11,true),(3,false),(2,false),(8,false),(7,false)],[(4,true),(5,true),(10,false),(9,false),(1,false),(6,true)])
                    .empty
                    .empty)
                  (.node 32540 ([(1,false),(0,false),(9,false),(3,true),(4,true),(7,false)],[(11,false),(10,false),(5,false),(8,true),(2,false),(6,true)])
                    .empty
                    .empty))
                (.node 33065 ([(4,false),(3,false),(9,false),(0,true),(1,true),(7,false)],[(11,false),(10,false),(2,false),(8,true),(5,false),(6,true)])
                  (.node 33030 ([(0,true),(1,true),(9,false),(4,false),(3,false),(7,false)],[(11,false),(10,false),(2,true),(8,true),(5,true),(6,true)])
                    .empty
                    .empty)
                  (.node 33240 ([(0,true),(10,false),(3,true),(4,true),(8,false),(7,false)],[(11,false),(1,true),(2,true),(9,false),(5,true),(6,true)])
                    .empty
                    .empty)))
              (.node 33815 ([(4,false),(3,false),(2,false),(10,false),(0,true),(7,false)],[(11,false),(1,false),(8,true),(9,true),(5,false),(6,true)])
                (.node 33755 ([(4,false),(11,false),(10,false),(0,true),(8,false),(7,false)],[(3,false),(2,false),(1,false),(9,true),(5,false),(6,true)])
                  (.node 33590 ([(1,false),(10,false),(4,false),(3,false),(8,false),(7,false)],[(11,false),(0,false),(5,false),(9,false),(2,false),(6,true)])
                    .empty
                    .empty)
                  (.node 33765 ([(3,true),(11,false),(1,false),(0,false),(5,false),(7,false)],[(4,true),(8,true),(9,true),(10,true),(2,true),(6,true)])
                    .empty
                    .empty))
                (.node 33885 ([(3,true),(11,false),(10,false),(5,false),(8,false),(7,false)],[(4,true),(9,true),(0,true),(1,true),(2,true),(6,true)])
                  (.node 33835 ([(0,false),(9,false),(2,false),(11,true),(4,true),(7,false)],[(3,false),(8,false),(5,true),(10,true),(1,false),(6,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 40850 ([(1,false),(10,false),(9,false),(5,false),(4,false),(7,false)],[(11,false),(0,false),(8,false),(3,false),(2,false),(6,true)])
              (.node 34830 ([(0,true),(1,true),(10,false),(4,false),(3,false),(7,false)],[(11,false),(2,true),(8,true),(9,true),(5,true),(6,true)])
                (.node 34110 ([(0,true),(1,true),(11,true),(4,true),(8,false),(7,false)],[(3,false),(2,false),(10,false),(9,false),(5,true),(6,true)])
                  (.node 33935 ([(4,false),(11,false),(1,false),(0,false),(8,false),(7,false)],[(3,false),(2,false),(10,false),(9,false),(5,false),(6,true)])
                    .empty
                    .empty)
                  (.node 34795 ([(0,false),(5,false),(4,false),(11,false),(2,true),(7,false)],[(3,false),(8,true),(9,true),(10,true),(1,false),(6,true)])
                    .empty
                    .empty))
                (.node 40755 ([(2,false),(1,false),(11,true),(4,false),(8,false),(7,false)],[(5,true),(0,true),(10,false),(9,false),(3,false),(6,true)])
                  (.node 40720 ([(4,true),(11,false),(1,true),(2,true),(8,false),(7,false)],[(5,true),(0,true),(10,false),(9,false),(3,true),(6,true)])
                    .empty
                    .empty)
                  (.node 40840 ([(4,true),(5,true),(0,true),(10,false),(2,false),(7,false)],[(11,false),(1,true),(8,true),(9,true),(3,true),(6,true)])
                    .empty
                    .empty)))
              (.node 40980 ([(5,false),(11,false),(10,false),(3,true),(8,false),(7,false)],[(4,false),(9,true),(2,false),(1,false),(0,false),(6,true)])
                (.node 40920 ([(5,false),(11,false),(1,true),(2,true),(3,true),(7,false)],[(4,false),(8,true),(9,true),(10,true),(0,false),(6,true)])
                  (.node 40900 ([(4,true),(11,false),(10,false),(2,false),(8,false),(7,false)],[(5,true),(0,true),(1,true),(9,true),(3,true),(6,true)])
                    .empty
                    .empty)
                  (.node 40970 ([(1,false),(10,false),(3,true),(4,true),(5,true),(7,false)],[(11,false),(0,false),(8,true),(9,true),(2,false),(6,true)])
                    .empty
                    .empty))
                (.node 41150 ([(1,false),(11,true),(4,false),(3,false),(8,false),(7,false)],[(5,true),(0,true),(10,false),(9,false),(2,false),(6,true)])
                  (.node 41115 ([(2,false),(1,false),(10,false),(4,true),(5,true),(7,false)],[(11,false),(0,false),(8,true),(9,true),(3,false),(6,true)])
                    .empty
                    .empty)
                  .empty))))
          (.node 43140 ([(5,false),(4,false),(3,false),(10,false),(1,true),(7,false)],[(11,false),(2,false),(8,true),(9,true),(0,false),(6,true)])
            (.node 42830 ([(1,false),(0,false),(5,false),(11,false),(3,true),(7,false)],[(4,false),(8,true),(9,true),(10,true),(2,false),(6,true)])
              (.node 42145 ([(0,false),(5,false),(11,false),(2,true),(3,true),(7,false)],[(4,false),(8,true),(9,true),(10,true),(1,false),(6,true)])
                (.node 41800 ([(4,true),(11,false),(1,false),(9,false),(8,false),(7,false)],[(5,true),(0,true),(10,true),(2,true),(3,true),(6,true)])
                  (.node 41625 ([(2,false),(10,false),(5,false),(4,false),(8,false),(7,false)],[(11,false),(1,false),(0,false),(9,false),(3,false),(6,true)])
                    .empty
                    .empty)
                  (.node 41835 ([(2,false),(1,false),(9,false),(4,true),(5,true),(7,false)],[(11,false),(10,false),(0,false),(8,true),(3,false),(6,true)])
                    .empty
                    .empty))
                (.node 42355 ([(0,false),(5,false),(11,false),(10,false),(3,false),(7,false)],[(4,false),(9,false),(8,false),(2,false),(1,false),(6,true)])
                  (.node 42180 ([(5,false),(11,false),(2,true),(9,false),(8,false),(7,false)],[(4,false),(3,false),(10,true),(1,false),(0,false),(6,true)])
                    .empty
                    .empty)
                  (.node 42390 ([(5,false),(4,false),(9,false),(1,true),(2,true),(7,false)],[(11,false),(10,false),(3,false),(8,true),(0,false),(6,true)])
                    .empty
                    .empty)))
              (.node 43060 ([(4,true),(11,false),(2,false),(1,false),(0,false),(7,false)],[(5,true),(8,true),(9,true),(10,true),(3,true),(6,true)])
                (.node 43000 ([(4,true),(11,false),(10,false),(0,false),(8,false),(7,false)],[(5,true),(9,true),(1,true),(2,true),(3,true),(6,true)])
                  (.node 42865 ([(0,false),(5,false),(11,false),(2,false),(8,false),(7,false)],[(4,false),(3,false),(10,false),(9,false),(1,false),(6,true)])
                    .empty
                    .empty)
                  (.node 43010 ([(1,false),(0,false),(5,false),(11,false),(3,true),(7,false)],[(4,false),(8,true),(9,true),(10,true),(2,false),(6,true)])
                    .empty
                    .empty))
                (.node 43130 ([(1,false),(9,false),(3,false),(11,true),(5,true),(7,false)],[(4,false),(8,false),(0,true),(10,true),(2,false),(6,true)])
                  (.node 43080 ([(5,false),(11,false),(10,false),(1,true),(8,false),(7,false)],[(4,false),(3,false),(2,false),(9,true),(0,false),(6,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 50101 ([(0,false),(11,false),(2,true),(3,true),(4,true),(8,false)],[(5,false),(9,true),(10,true),(1,false),(6,true),(7,true)])
              (.node 49641 ([(2,false),(1,false),(0,false),(5,false),(4,false),(8,false)],[(11,false),(10,false),(9,false),(3,false),(6,true),(7,true)])
                (.node 43260 ([(5,false),(11,false),(2,false),(1,false),(8,false),(7,false)],[(4,false),(3,false),(10,false),(9,false),(0,false),(6,true)])
                  (.node 43225 ([(0,false),(9,true),(2,true),(11,true),(4,false),(7,false)],[(5,true),(8,false),(3,false),(10,false),(1,false),(6,true)])
                    .empty
                    .empty)
                  (.node 49631 ([(5,true),(0,true),(1,true),(2,true),(3,true),(8,false)],[(11,false),(10,false),(9,false),(4,true),(6,true),(7,true)])
                    .empty
                    .empty))
                (.node 50071 ([(0,false),(11,false),(2,true),(3,true),(4,true),(7,true)],[(5,false),(6,false),(1,true),(10,false),(9,false),(8,false)])
                  (.node 50051 ([(4,false),(3,false),(2,false),(11,true),(0,true),(7,true)],[(5,false),(6,true),(1,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 50086 ([(3,false),(2,false),(1,false),(0,false),(5,false),(8,false)],[(11,false),(10,false),(9,false),(4,false),(6,true),(7,true)])
                    .empty
                    .empty)))
              (.node 50251 ([(0,false),(11,false),(2,true),(3,true),(4,true),(7,true)],[(5,false),(6,false),(1,true),(10,false),(9,false),(8,false)])
                (.node 50181 ([(2,false),(10,false),(4,true),(5,true),(0,true),(8,false)],[(11,false),(1,false),(9,true),(3,false),(6,true),(7,true)])
                  (.node 50171 ([(4,false),(9,false),(0,false),(11,false),(2,true),(7,true)],[(5,false),(6,true),(3,true),(10,true),(1,false),(8,false)])
                    .empty
                    .empty)
                  (.node 50231 ([(4,false),(3,false),(2,false),(11,true),(0,true),(7,true)],[(5,false),(6,true),(1,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 50311 ([(0,false),(5,false),(4,false),(10,true),(2,true),(7,true)],[(11,false),(1,false),(6,true),(3,true),(9,false),(8,false)])
                  (.node 50301 ([(2,false),(10,false),(4,true),(5,true),(0,true),(7,true)],[(11,false),(1,false),(6,false),(3,true),(9,false),(8,false)])
                    .empty
                    .empty)
                  .empty)))))
        (.node 52541 ([(5,true),(11,false),(3,false),(2,false),(1,false),(8,false)],[(0,true),(9,true),(10,true),(4,true),(6,true),(7,true)])
          (.node 51511 ([(0,false),(5,false),(4,false),(3,false),(2,false),(8,false)],[(11,false),(10,false),(9,false),(1,false),(6,true),(7,true)])
            (.node 51131 ([(4,false),(9,true),(2,true),(11,true),(0,true),(7,true)],[(5,false),(6,true),(1,true),(10,true),(3,true),(8,false)])
              (.node 50921 ([(4,false),(3,false),(11,true),(0,true),(1,true),(7,true)],[(5,false),(6,true),(2,true),(10,false),(9,false),(8,false)])
                (.node 50481 ([(2,false),(1,false),(0,false),(5,false),(4,false),(8,false)],[(11,false),(10,false),(9,false),(3,false),(6,true),(7,true)])
                  (.node 50461 ([(0,false),(5,false),(10,true),(2,true),(3,true),(7,true)],[(11,false),(1,false),(6,true),(4,true),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 50491 ([(1,true),(11,true),(5,false),(4,false),(3,false),(7,true)],[(0,true),(6,true),(2,false),(10,false),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 50956 ([(3,false),(2,false),(1,false),(0,false),(5,false),(8,false)],[(11,false),(10,false),(9,false),(4,false),(6,true),(7,true)])
                  (.node 50936 ([(1,false),(0,false),(11,false),(3,true),(4,true),(7,true)],[(5,false),(6,false),(2,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 50966 ([(1,false),(0,false),(11,false),(3,true),(4,true),(8,false)],[(5,false),(9,true),(10,true),(2,false),(6,true),(7,true)])
                    .empty
                    .empty)))
              (.node 51461 ([(4,false),(3,false),(11,true),(0,true),(1,true),(7,true)],[(5,false),(6,true),(2,true),(10,false),(9,false),(8,false)])
                (.node 51166 ([(3,false),(2,false),(1,false),(0,false),(5,false),(8,false)],[(11,false),(10,false),(9,false),(4,false),(6,true),(7,true)])
                  (.node 51151 ([(0,false),(11,false),(2,false),(9,false),(4,true),(7,true)],[(5,false),(6,false),(1,true),(10,true),(3,true),(8,false)])
                    .empty
                    .empty)
                  (.node 51181 ([(0,false),(5,false),(9,true),(2,true),(3,true),(7,true)],[(11,false),(10,false),(1,false),(6,true),(4,true),(8,false)])
                    .empty
                    .empty))
                (.node 51491 ([(5,true),(11,false),(3,true),(9,false),(1,false),(7,true)],[(0,true),(6,false),(4,false),(10,true),(2,false),(8,false)])
                  (.node 51476 ([(1,false),(0,false),(11,false),(3,true),(4,true),(7,true)],[(5,false),(6,false),(2,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  .empty)))
            (.node 52196 ([(1,false),(0,false),(5,false),(4,false),(3,false),(8,false)],[(11,false),(10,false),(9,false),(2,false),(6,true),(7,true)])
              (.node 51721 ([(0,false),(5,false),(4,false),(3,false),(2,false),(8,false)],[(11,false),(10,false),(9,false),(1,false),(6,true),(7,true)])
                (.node 51686 ([(1,false),(0,false),(5,false),(10,true),(3,true),(7,true)],[(11,false),(2,false),(6,true),(4,true),(9,false),(8,false)])
                  (.node 51676 ([(3,false),(10,false),(5,true),(0,true),(1,true),(7,true)],[(11,false),(2,false),(6,false),(4,true),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 51706 ([(3,false),(2,false),(9,true),(5,true),(0,true),(7,true)],[(11,false),(10,false),(4,false),(6,true),(1,true),(8,false)])
                    .empty
                    .empty))
                (.node 52161 ([(2,false),(1,false),(0,false),(11,false),(4,true),(7,true)],[(5,false),(6,false),(3,true),(10,false),(9,false),(8,false)])
                  (.node 52151 ([(4,false),(11,true),(0,true),(1,true),(2,true),(7,true)],[(5,false),(6,true),(3,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 52181 ([(4,false),(11,true),(0,true),(9,false),(2,false),(7,true)],[(5,false),(6,true),(1,false),(10,true),(3,false),(8,false)])
                    .empty
                    .empty)))
              (.node 52411 ([(0,false),(5,false),(4,false),(10,false),(2,true),(8,false)],[(11,false),(3,false),(9,true),(1,false),(6,true),(7,true)])
                (.node 52341 ([(2,false),(1,false),(0,false),(11,false),(4,true),(7,true)],[(5,false),(6,false),(3,true),(10,false),(9,false),(8,false)])
                  (.node 52331 ([(4,false),(11,true),(0,true),(1,true),(2,true),(7,true)],[(5,false),(6,true),(3,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 52391 ([(5,true),(11,false),(3,false),(2,false),(1,false),(7,true)],[(0,true),(6,false),(4,false),(10,false),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 52471 ([(0,false),(5,false),(4,false),(10,false),(2,true),(7,true)],[(11,false),(3,false),(6,false),(1,true),(9,false),(8,false)])
                  (.node 52461 ([(2,false),(1,false),(0,false),(11,false),(4,true),(8,false)],[(5,false),(9,true),(10,true),(3,false),(6,true),(7,true)])
                    .empty
                    .empty)
                  .empty))))
          (.node 59376 ([(0,true),(1,true),(2,true),(3,true),(4,true),(8,false)],[(11,false),(10,false),(9,false),(5,true),(6,true),(7,true)])
            (.node 58516 ([(3,false),(2,false),(1,false),(0,false),(5,false),(8,false)],[(11,false),(10,false),(9,false),(4,false),(6,true),(7,true)])
              (.node 53001 ([(2,false),(9,true),(4,false),(11,true),(0,true),(7,true)],[(5,false),(10,true),(3,false),(6,true),(1,true),(8,false)])
                (.node 52571 ([(5,true),(11,false),(3,false),(2,false),(1,false),(7,true)],[(0,true),(6,false),(4,false),(10,false),(9,false),(8,false)])
                  (.node 52556 ([(2,true),(3,true),(4,true),(5,true),(0,true),(8,false)],[(11,false),(10,false),(9,false),(1,true),(6,true),(7,true)])
                    .empty
                    .empty)
                  (.node 52591 ([(0,false),(5,false),(4,false),(3,false),(2,false),(8,false)],[(11,false),(10,false),(9,false),(1,false),(6,true),(7,true)])
                    .empty
                    .empty))
                (.node 58481 ([(4,false),(3,false),(10,false),(0,true),(1,true),(7,true)],[(11,false),(2,false),(6,false),(5,true),(9,false),(8,false)])
                  (.node 53011 ([(0,false),(5,false),(4,false),(3,false),(2,false),(8,false)],[(11,false),(10,false),(9,false),(1,false),(6,true),(7,true)])
                    .empty
                    .empty)
                  (.node 58496 ([(1,false),(0,false),(10,true),(3,true),(4,true),(7,true)],[(11,false),(2,false),(6,true),(5,true),(9,false),(8,false)])
                    .empty
                    .empty)))
              (.node 59201 ([(4,false),(3,false),(2,false),(1,false),(0,false),(8,false)],[(11,false),(10,false),(9,false),(5,false),(6,true),(7,true)])
                (.node 58936 ([(3,false),(2,false),(1,false),(0,false),(5,false),(8,false)],[(11,false),(10,false),(9,false),(4,false),(6,true),(7,true)])
                  (.node 58526 ([(2,true),(11,true),(0,false),(5,false),(4,false),(7,true)],[(1,true),(6,true),(3,false),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 58956 ([(0,true),(1,true),(2,true),(3,true),(4,true),(8,false)],[(11,false),(10,false),(9,false),(5,true),(6,true),(7,true)])
                    .empty
                    .empty))
                (.node 59366 ([(1,false),(11,false),(3,true),(4,true),(5,true),(7,true)],[(0,false),(6,false),(2,true),(10,false),(9,false),(8,false)])
                  (.node 59216 ([(1,false),(11,false),(3,true),(4,true),(5,true),(8,false)],[(0,false),(9,true),(10,true),(2,false),(6,true),(7,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 59721 ([(2,false),(1,false),(0,false),(10,true),(4,true),(7,true)],[(11,false),(3,false),(6,true),(5,true),(9,false),(8,false)])
              (.node 59496 ([(0,true),(1,true),(2,true),(10,false),(4,false),(7,true)],[(11,false),(3,true),(6,false),(5,false),(9,false),(8,false)])
                (.node 59426 ([(1,false),(0,false),(5,false),(10,true),(3,true),(7,true)],[(11,false),(2,false),(6,true),(4,true),(9,false),(8,false)])
                  (.node 59416 ([(3,false),(10,false),(5,true),(0,true),(1,true),(7,true)],[(11,false),(2,false),(6,false),(4,true),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 59476 ([(3,false),(10,false),(5,true),(0,true),(1,true),(8,false)],[(11,false),(2,false),(9,true),(4,false),(6,true),(7,true)])
                    .empty
                    .empty))
                (.node 59556 ([(0,true),(1,true),(2,true),(10,false),(4,false),(8,false)],[(11,false),(3,true),(9,true),(5,true),(6,true),(7,true)])
                  (.node 59546 ([(1,false),(11,false),(3,true),(4,true),(5,true),(7,true)],[(0,false),(6,false),(2,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 59711 ([(4,false),(10,false),(0,true),(1,true),(2,true),(7,true)],[(11,false),(3,false),(6,false),(5,true),(9,false),(8,false)])
                    .empty
                    .empty)))
              (.node 60081 ([(2,false),(1,false),(11,false),(4,true),(5,true),(8,false)],[(0,false),(9,true),(10,true),(3,false),(6,true),(7,true)])
                (.node 59756 ([(1,false),(0,false),(5,false),(4,false),(3,false),(8,false)],[(11,false),(10,false),(9,false),(2,false),(6,true),(7,true)])
                  (.node 59741 ([(4,false),(3,false),(9,true),(0,true),(1,true),(7,true)],[(11,false),(10,false),(5,false),(6,true),(2,true),(8,false)])
                    .empty
                    .empty)
                  (.node 60071 ([(4,false),(3,false),(2,false),(1,false),(0,false),(8,false)],[(11,false),(10,false),(9,false),(5,false),(6,true),(7,true)])
                    .empty
                    .empty))
                (.node 60246 ([(0,true),(1,true),(2,true),(3,true),(4,true),(8,false)],[(11,false),(10,false),(9,false),(5,true),(6,true),(7,true)])
                  (.node 60231 ([(2,false),(1,false),(11,false),(4,true),(5,true),(7,true)],[(0,false),(6,false),(3,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  .empty)))))))
    (.node 78071 ([(4,false),(11,false),(0,true),(1,true),(2,true),(7,true)],[(3,false),(6,false),(5,true),(10,false),(9,false),(8,false)])
      (.node 69016 ([(3,false),(2,false),(1,false),(10,true),(5,true),(7,true)],[(11,false),(4,false),(6,true),(0,true),(9,false),(8,false)])
        (.node 63131 ([(4,false),(3,false),(2,false),(11,false),(0,true),(8,false)],[(1,false),(9,true),(10,true),(5,false),(6,true),(7,true)])
          (.node 61586 ([(1,false),(0,false),(5,false),(10,false),(3,true),(7,true)],[(11,false),(4,false),(6,false),(2,true),(9,false),(8,false)])
            (.node 61036 ([(3,false),(9,true),(5,false),(11,true),(1,true),(7,true)],[(0,false),(10,true),(4,false),(6,true),(2,true),(8,false)])
              (.node 60771 ([(2,false),(1,false),(11,false),(4,true),(5,true),(7,true)],[(0,false),(6,false),(3,true),(10,false),(9,false),(8,false)])
                (.node 60446 ([(1,false),(11,false),(3,false),(9,false),(5,true),(7,true)],[(0,false),(6,false),(2,true),(10,true),(4,true),(8,false)])
                  (.node 60296 ([(1,false),(0,false),(9,true),(3,true),(4,true),(7,true)],[(11,false),(10,false),(2,false),(6,true),(5,true),(8,false)])
                    .empty
                    .empty)
                  (.node 60456 ([(0,true),(1,true),(2,true),(3,true),(4,true),(8,false)],[(11,false),(10,false),(9,false),(5,true),(6,true),(7,true)])
                    .empty
                    .empty))
                (.node 60806 ([(1,false),(0,false),(5,false),(4,false),(3,false),(8,false)],[(11,false),(10,false),(9,false),(2,false),(6,true),(7,true)])
                  (.node 60786 ([(0,true),(1,true),(9,true),(4,false),(3,false),(7,true)],[(11,false),(10,false),(5,true),(6,true),(2,false),(8,false)])
                    .empty
                    .empty)
                  (.node 60816 ([(0,true),(11,false),(4,true),(9,false),(2,false),(7,true)],[(1,true),(6,false),(5,false),(10,true),(3,false),(8,false)])
                    .empty
                    .empty)))
              (.node 61491 ([(2,false),(1,false),(0,false),(5,false),(4,false),(8,false)],[(11,false),(10,false),(9,false),(3,false),(6,true),(7,true)])
                (.node 61456 ([(3,false),(2,false),(1,false),(11,false),(5,true),(7,true)],[(0,false),(6,false),(4,true),(10,false),(9,false),(8,false)])
                  (.node 61046 ([(1,false),(0,false),(5,false),(4,false),(3,false),(8,false)],[(11,false),(10,false),(9,false),(2,false),(6,true),(7,true)])
                    .empty
                    .empty)
                  (.node 61476 ([(5,false),(11,true),(1,true),(2,true),(3,true),(7,true)],[(0,false),(6,true),(4,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 61576 ([(3,false),(2,false),(1,false),(11,false),(5,true),(8,false)],[(0,false),(9,true),(10,true),(4,false),(6,true),(7,true)])
                  (.node 61506 ([(0,true),(1,true),(10,true),(4,false),(3,false),(7,true)],[(11,false),(5,true),(6,true),(2,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  .empty)))
            (.node 61896 ([(0,true),(11,false),(4,false),(3,false),(2,false),(7,true)],[(1,true),(6,false),(5,false),(10,false),(9,false),(8,false)])
              (.node 61716 ([(0,true),(11,false),(4,false),(3,false),(2,false),(7,true)],[(1,true),(6,false),(5,false),(10,false),(9,false),(8,false)])
                (.node 61656 ([(0,true),(1,true),(2,true),(10,true),(4,false),(7,true)],[(11,false),(5,true),(6,true),(3,false),(9,false),(8,false)])
                  (.node 61636 ([(3,false),(2,false),(1,false),(11,false),(5,true),(7,true)],[(0,false),(6,false),(4,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 61706 ([(1,false),(0,false),(5,false),(10,false),(3,true),(8,false)],[(11,false),(4,false),(9,true),(2,false),(6,true),(7,true)])
                    .empty
                    .empty))
                (.node 61866 ([(0,true),(11,false),(4,false),(3,false),(2,false),(8,false)],[(1,true),(9,true),(10,true),(5,true),(6,true),(7,true)])
                  (.node 61851 ([(3,true),(4,true),(5,true),(0,true),(1,true),(8,false)],[(11,false),(10,false),(9,false),(2,true),(6,true),(7,true)])
                    .empty
                    .empty)
                  (.node 61886 ([(1,false),(0,false),(5,false),(4,false),(3,false),(8,false)],[(11,false),(10,false),(9,false),(2,false),(6,true),(7,true)])
                    .empty
                    .empty)))
              (.node 63031 ([(0,false),(11,true),(2,true),(3,true),(4,true),(7,true)],[(1,false),(6,true),(5,true),(10,false),(9,false),(8,false)])
                (.node 62601 ([(2,false),(1,false),(0,false),(5,false),(4,false),(8,false)],[(11,false),(10,false),(9,false),(3,false),(6,true),(7,true)])
                  (.node 62591 ([(4,false),(9,true),(0,false),(11,true),(2,true),(7,true)],[(1,false),(10,true),(5,false),(6,true),(3,true),(8,false)])
                    .empty
                    .empty)
                  (.node 63011 ([(4,false),(3,false),(2,false),(11,false),(0,true),(7,true)],[(1,false),(6,false),(5,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 63061 ([(0,false),(11,true),(2,true),(9,false),(4,false),(7,true)],[(1,false),(6,true),(3,false),(10,true),(5,false),(8,false)])
                  (.node 63046 ([(3,false),(2,false),(1,false),(0,false),(5,false),(8,false)],[(11,false),(10,false),(9,false),(4,false),(6,true),(7,true)])
                    .empty
                    .empty)
                  .empty))))
          (.node 67591 ([(0,false),(5,false),(4,false),(11,true),(2,true),(7,true)],[(1,false),(6,true),(3,true),(10,false),(9,false),(8,false)])
            (.node 63441 ([(2,false),(1,false),(0,false),(5,false),(4,false),(8,false)],[(11,false),(10,false),(9,false),(3,false),(6,true),(7,true)])
              (.node 63261 ([(2,false),(1,false),(0,false),(10,false),(4,true),(8,false)],[(11,false),(5,false),(9,true),(3,false),(6,true),(7,true)])
                (.node 63191 ([(4,false),(3,false),(2,false),(11,false),(0,true),(7,true)],[(1,false),(6,false),(5,true),(10,false),(9,false),(8,false)])
                  (.node 63141 ([(2,false),(1,false),(0,false),(10,false),(4,true),(7,true)],[(11,false),(5,false),(6,false),(3,true),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 63211 ([(0,false),(11,true),(2,true),(3,true),(4,true),(7,true)],[(1,false),(6,true),(5,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 63406 ([(4,true),(5,true),(0,true),(1,true),(2,true),(8,false)],[(11,false),(10,false),(9,false),(3,true),(6,true),(7,true)])
                  (.node 63271 ([(1,true),(11,false),(5,false),(4,false),(3,false),(7,true)],[(2,true),(6,false),(0,false),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 63421 ([(1,true),(11,false),(5,false),(4,false),(3,false),(8,false)],[(2,true),(9,true),(10,true),(0,true),(6,true),(7,true)])
                    .empty
                    .empty)))
              (.node 67511 ([(4,false),(10,false),(0,true),(1,true),(2,true),(8,false)],[(11,false),(3,false),(9,true),(5,false),(6,true),(7,true)])
                (.node 67451 ([(4,false),(10,false),(0,true),(1,true),(2,true),(7,true)],[(11,false),(3,false),(6,false),(5,true),(9,false),(8,false)])
                  (.node 63451 ([(1,true),(11,false),(5,false),(4,false),(3,false),(7,true)],[(2,true),(6,false),(0,false),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 67461 ([(2,false),(1,false),(0,false),(10,true),(4,true),(7,true)],[(11,false),(3,false),(6,true),(5,true),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 67581 ([(2,false),(11,false),(4,true),(5,true),(0,true),(7,true)],[(1,false),(6,false),(3,true),(10,false),(9,false),(8,false)])
                  (.node 67531 ([(0,false),(9,false),(2,false),(11,false),(4,true),(7,true)],[(1,false),(6,true),(5,true),(10,true),(3,false),(8,false)])
                    .empty
                    .empty)
                  .empty)))
            (.node 68491 ([(0,false),(5,false),(4,false),(11,true),(2,true),(7,true)],[(1,false),(6,true),(3,true),(10,false),(9,false),(8,false)])
              (.node 67806 ([(0,true),(1,true),(2,true),(3,true),(4,true),(8,false)],[(11,false),(10,false),(9,false),(5,true),(6,true),(7,true)])
                (.node 67641 ([(3,true),(11,true),(1,false),(0,false),(5,false),(7,true)],[(2,true),(6,true),(4,false),(10,false),(9,false),(8,false)])
                  (.node 67631 ([(4,false),(3,false),(2,false),(1,false),(0,false),(8,false)],[(11,false),(10,false),(9,false),(5,false),(6,true),(7,true)])
                    .empty
                    .empty)
                  (.node 67791 ([(2,false),(1,false),(10,true),(4,true),(5,true),(7,true)],[(11,false),(3,false),(6,true),(0,true),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 68071 ([(1,true),(2,true),(3,true),(4,true),(5,true),(8,false)],[(11,false),(10,false),(9,false),(0,true),(6,true),(7,true)])
                  (.node 68051 ([(4,false),(3,false),(2,false),(1,false),(0,false),(8,false)],[(11,false),(10,false),(9,false),(5,false),(6,true),(7,true)])
                    .empty
                    .empty)
                  (.node 68481 ([(2,false),(11,false),(4,true),(5,true),(0,true),(7,true)],[(1,false),(6,false),(3,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)))
              (.node 68821 ([(0,false),(5,false),(11,true),(2,true),(3,true),(7,true)],[(1,false),(6,true),(4,true),(10,false),(9,false),(8,false)])
                (.node 68526 ([(5,false),(4,false),(3,false),(2,false),(1,false),(8,false)],[(11,false),(10,false),(9,false),(0,false),(6,true),(7,true)])
                  (.node 68511 ([(2,false),(11,false),(4,true),(5,true),(0,true),(8,false)],[(1,false),(9,true),(10,true),(3,false),(6,true),(7,true)])
                    .empty
                    .empty)
                  (.node 68806 ([(3,false),(2,false),(11,false),(5,true),(0,true),(7,true)],[(1,false),(6,false),(4,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 68851 ([(1,true),(11,false),(5,true),(9,false),(3,false),(7,true)],[(2,true),(6,false),(0,false),(10,true),(4,false),(8,false)])
                  (.node 68841 ([(2,false),(1,false),(0,false),(5,false),(4,false),(8,false)],[(11,false),(10,false),(9,false),(3,false),(6,true),(7,true)])
                    .empty
                    .empty)
                  .empty)))))
        (.node 71476 ([(3,false),(2,false),(1,false),(0,false),(5,false),(8,false)],[(11,false),(10,false),(9,false),(4,false),(6,true),(7,true)])
          (.node 70406 ([(2,true),(11,false),(0,true),(9,false),(4,false),(7,true)],[(3,true),(6,false),(1,false),(10,true),(5,false),(8,false)])
            (.node 69561 ([(2,false),(11,false),(4,false),(9,false),(0,true),(7,true)],[(1,false),(6,false),(3,true),(10,true),(5,true),(8,false)])
              (.node 69346 ([(3,false),(2,false),(11,false),(5,true),(0,true),(7,true)],[(1,false),(6,false),(4,true),(10,false),(9,false),(8,false)])
                (.node 69051 ([(2,false),(1,false),(0,false),(5,false),(4,false),(8,false)],[(11,false),(10,false),(9,false),(3,false),(6,true),(7,true)])
                  (.node 69036 ([(0,true),(1,true),(11,false),(4,false),(3,false),(8,false)],[(2,true),(9,true),(10,true),(5,true),(6,true),(7,true)])
                    .empty
                    .empty)
                  (.node 69066 ([(0,true),(1,true),(11,false),(4,false),(3,false),(7,true)],[(2,true),(6,false),(5,false),(10,false),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 69376 ([(3,false),(2,false),(11,false),(5,true),(0,true),(8,false)],[(1,false),(9,true),(10,true),(4,false),(6,true),(7,true)])
                  (.node 69361 ([(0,false),(5,false),(11,true),(2,true),(3,true),(7,true)],[(1,false),(6,true),(4,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 69396 ([(0,true),(1,true),(2,true),(10,true),(4,false),(7,true)],[(11,false),(5,true),(6,true),(3,false),(9,false),(8,false)])
                    .empty
                    .empty)))
              (.node 70361 ([(4,false),(3,false),(11,false),(0,true),(1,true),(7,true)],[(2,false),(6,false),(5,true),(10,false),(9,false),(8,false)])
                (.node 69591 ([(2,false),(1,false),(9,true),(4,true),(5,true),(7,true)],[(11,false),(10,false),(3,false),(6,true),(0,true),(8,false)])
                  (.node 69571 ([(0,false),(9,true),(4,true),(11,true),(2,true),(7,true)],[(1,false),(6,true),(3,true),(10,true),(5,true),(8,false)])
                    .empty
                    .empty)
                  (.node 69606 ([(0,true),(1,true),(11,false),(4,false),(3,false),(7,true)],[(2,true),(6,false),(5,false),(10,false),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 70396 ([(3,false),(2,false),(1,false),(0,false),(5,false),(8,false)],[(11,false),(10,false),(9,false),(4,false),(6,true),(7,true)])
                  (.node 70376 ([(1,false),(0,false),(11,true),(3,true),(4,true),(7,true)],[(2,false),(6,true),(5,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  .empty)))
            (.node 70951 ([(0,false),(5,false),(4,false),(3,false),(2,false),(8,false)],[(11,false),(10,false),(9,false),(1,false),(6,true),(7,true)])
              (.node 70621 ([(0,false),(5,false),(9,true),(2,true),(3,true),(7,true)],[(11,false),(10,false),(1,false),(6,true),(4,true),(8,false)])
                (.node 70591 ([(0,false),(10,false),(2,true),(3,true),(4,true),(7,true)],[(11,false),(5,false),(6,false),(1,true),(9,false),(8,false)])
                  (.node 70571 ([(4,false),(3,false),(2,false),(10,true),(0,true),(7,true)],[(11,false),(5,false),(6,true),(1,true),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 70606 ([(3,false),(2,false),(1,false),(0,false),(5,false),(8,false)],[(11,false),(10,false),(9,false),(4,false),(6,true),(7,true)])
                    .empty
                    .empty))
                (.node 70916 ([(1,false),(0,false),(11,true),(3,true),(4,true),(7,true)],[(2,false),(6,true),(5,true),(10,false),(9,false),(8,false)])
                  (.node 70901 ([(4,false),(3,false),(11,false),(0,true),(1,true),(7,true)],[(2,false),(6,false),(5,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 70931 ([(4,false),(3,false),(11,false),(0,true),(1,true),(8,false)],[(2,false),(9,true),(10,true),(5,false),(6,true),(7,true)])
                    .empty
                    .empty)))
              (.node 71161 ([(0,false),(5,false),(4,false),(3,false),(2,false),(8,false)],[(11,false),(10,false),(9,false),(1,false),(6,true),(7,true)])
                (.node 71126 ([(1,false),(9,true),(5,true),(11,true),(3,true),(7,true)],[(2,false),(6,true),(4,true),(10,true),(0,true),(8,false)])
                  (.node 71116 ([(3,false),(11,false),(5,false),(9,false),(1,true),(7,true)],[(2,false),(6,false),(4,true),(10,true),(0,true),(8,false)])
                    .empty
                    .empty)
                  (.node 71146 ([(3,false),(2,false),(9,true),(5,true),(0,true),(7,true)],[(11,false),(10,false),(4,false),(6,true),(1,true),(8,false)])
                    .empty
                    .empty))
                (.node 71456 ([(2,true),(11,false),(0,false),(5,false),(4,false),(8,false)],[(3,true),(9,true),(10,true),(1,true),(6,true),(7,true)])
                  (.node 71441 ([(5,true),(0,true),(1,true),(2,true),(3,true),(8,false)],[(11,false),(10,false),(9,false),(4,true),(6,true),(7,true)])
                    .empty
                    .empty)
                  .empty))))
          (.node 76526 ([(1,false),(0,false),(5,false),(11,true),(3,true),(7,true)],[(2,false),(6,true),(4,true),(10,false),(9,false),(8,false)])
            (.node 72376 ([(3,false),(2,false),(1,false),(10,false),(5,true),(8,false)],[(11,false),(0,false),(9,true),(4,false),(6,true),(7,true)])
              (.node 72161 ([(4,false),(3,false),(2,false),(1,false),(0,false),(8,false)],[(11,false),(10,false),(9,false),(5,false),(6,true),(7,true)])
                (.node 71896 ([(3,false),(2,false),(1,false),(0,false),(5,false),(8,false)],[(11,false),(10,false),(9,false),(4,false),(6,true),(7,true)])
                  (.node 71486 ([(2,true),(11,false),(0,false),(5,false),(4,false),(7,true)],[(3,true),(6,false),(1,false),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 71916 ([(0,true),(1,true),(2,true),(3,true),(4,true),(8,false)],[(11,false),(10,false),(9,false),(5,true),(6,true),(7,true)])
                    .empty
                    .empty))
                (.node 72326 ([(1,false),(11,true),(3,true),(4,true),(5,true),(7,true)],[(2,false),(6,true),(0,true),(10,false),(9,false),(8,false)])
                  (.node 72176 ([(1,false),(11,true),(3,true),(9,false),(5,false),(7,true)],[(2,false),(6,true),(4,false),(10,true),(0,false),(8,false)])
                    .empty
                    .empty)
                  (.node 72336 ([(0,true),(1,true),(2,true),(3,true),(4,true),(8,false)],[(11,false),(10,false),(9,false),(5,true),(6,true),(7,true)])
                    .empty
                    .empty)))
              (.node 72506 ([(1,false),(11,true),(3,true),(4,true),(5,true),(7,true)],[(2,false),(6,true),(0,true),(10,false),(9,false),(8,false)])
                (.node 72436 ([(3,false),(2,false),(1,false),(10,false),(5,true),(7,true)],[(11,false),(0,false),(6,false),(4,true),(9,false),(8,false)])
                  (.node 72386 ([(2,true),(11,false),(0,false),(5,false),(4,false),(7,true)],[(3,true),(6,false),(1,false),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 72456 ([(0,true),(10,false),(4,false),(3,false),(2,false),(8,false)],[(11,false),(1,true),(9,true),(5,true),(6,true),(7,true)])
                    .empty
                    .empty))
                (.node 76516 ([(3,false),(11,false),(5,true),(0,true),(1,true),(7,true)],[(2,false),(6,false),(4,true),(10,false),(9,false),(8,false)])
                  (.node 72516 ([(0,true),(10,false),(4,false),(3,false),(2,false),(7,true)],[(11,false),(1,true),(6,false),(5,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  .empty)))
            (.node 76836 ([(0,true),(1,true),(2,true),(11,false),(4,false),(8,false)],[(3,true),(9,true),(10,true),(5,true),(6,true),(7,true)])
              (.node 76706 ([(1,false),(0,false),(5,false),(11,true),(3,true),(7,true)],[(2,false),(6,true),(4,true),(10,false),(9,false),(8,false)])
                (.node 76561 ([(0,false),(5,false),(4,false),(3,false),(2,false),(8,false)],[(11,false),(10,false),(9,false),(1,false),(6,true),(7,true)])
                  (.node 76546 ([(3,false),(11,false),(5,true),(0,true),(1,true),(8,false)],[(2,false),(9,true),(10,true),(4,false),(6,true),(7,true)])
                    .empty
                    .empty)
                  (.node 76696 ([(3,false),(11,false),(5,true),(0,true),(1,true),(7,true)],[(2,false),(6,false),(4,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 76776 ([(0,true),(1,true),(2,true),(11,false),(4,false),(7,true)],[(3,true),(6,false),(5,false),(10,false),(9,false),(8,false)])
                  (.node 76756 ([(3,false),(2,false),(1,false),(10,true),(5,true),(7,true)],[(11,false),(4,false),(6,true),(0,true),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 76826 ([(1,false),(9,false),(3,false),(11,false),(5,true),(7,true)],[(2,false),(6,true),(0,true),(10,true),(4,false),(8,false)])
                    .empty
                    .empty)))
              (.node 76956 ([(0,true),(1,true),(2,true),(11,false),(4,false),(7,true)],[(3,true),(6,false),(5,false),(10,false),(9,false),(8,false)])
                (.node 76921 ([(0,false),(5,false),(10,false),(2,true),(3,true),(7,true)],[(11,false),(4,false),(6,false),(1,true),(9,false),(8,false)])
                  (.node 76906 ([(3,false),(2,false),(10,true),(5,true),(0,true),(7,true)],[(11,false),(4,false),(6,true),(1,true),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 76936 ([(4,true),(11,true),(2,false),(1,false),(0,false),(7,true)],[(3,true),(6,true),(5,false),(10,false),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 77376 ([(0,true),(9,true),(4,true),(11,true),(2,false),(7,true)],[(3,true),(10,true),(5,true),(6,true),(1,false),(8,false)])
                  (.node 77366 ([(2,true),(3,true),(4,true),(5,true),(0,true),(8,false)],[(11,false),(10,false),(9,false),(1,true),(6,true),(7,true)])
                    .empty
                    .empty)
                  .empty))))))
      (.node 87771 ([(2,false),(1,false),(10,false),(4,true),(5,true),(7,true)],[(11,false),(0,false),(6,false),(3,true),(9,false),(8,false)])
        (.node 80246 ([(1,false),(0,false),(5,false),(4,false),(3,false),(8,false)],[(11,false),(10,false),(9,false),(2,false),(6,true),(7,true)])
          (.node 78931 ([(0,false),(5,false),(4,false),(3,false),(2,false),(8,false)],[(11,false),(10,false),(9,false),(1,false),(6,true),(7,true)])
            (.node 78381 ([(2,false),(9,false),(4,false),(11,false),(0,true),(7,true)],[(3,false),(6,true),(1,true),(10,true),(5,false),(8,false)])
              (.node 78251 ([(4,false),(11,false),(0,true),(1,true),(2,true),(7,true)],[(3,false),(6,false),(5,true),(10,false),(9,false),(8,false)])
                (.node 78101 ([(4,false),(11,false),(0,true),(1,true),(2,true),(8,false)],[(3,false),(9,true),(10,true),(5,false),(6,true),(7,true)])
                  (.node 78081 ([(2,false),(1,false),(0,false),(11,true),(4,true),(7,true)],[(3,false),(6,true),(5,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 78116 ([(1,false),(0,false),(5,false),(4,false),(3,false),(8,false)],[(11,false),(10,false),(9,false),(2,false),(6,true),(7,true)])
                    .empty
                    .empty))
                (.node 78311 ([(4,false),(3,false),(2,false),(10,true),(0,true),(7,true)],[(11,false),(5,false),(6,true),(1,true),(9,false),(8,false)])
                  (.node 78261 ([(2,false),(1,false),(0,false),(11,true),(4,true),(7,true)],[(3,false),(6,true),(5,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 78331 ([(0,false),(10,false),(2,true),(3,true),(4,true),(7,true)],[(11,false),(5,false),(6,false),(1,true),(9,false),(8,false)])
                    .empty
                    .empty)))
              (.node 78491 ([(5,true),(11,true),(3,false),(2,false),(1,false),(7,true)],[(4,true),(6,true),(0,false),(10,false),(9,false),(8,false)])
                (.node 78461 ([(4,false),(3,false),(10,true),(0,true),(1,true),(7,true)],[(11,false),(5,false),(6,true),(2,true),(9,false),(8,false)])
                  (.node 78391 ([(0,false),(10,false),(2,true),(3,true),(4,true),(8,false)],[(11,false),(5,false),(9,true),(1,false),(6,true),(7,true)])
                    .empty
                    .empty)
                  (.node 78476 ([(1,false),(0,false),(10,false),(3,true),(4,true),(7,true)],[(11,false),(5,false),(6,false),(2,true),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 78921 ([(3,true),(4,true),(5,true),(0,true),(1,true),(8,false)],[(11,false),(10,false),(9,false),(2,true),(6,true),(7,true)])
                  (.node 78511 ([(0,false),(5,false),(4,false),(3,false),(2,false),(8,false)],[(11,false),(10,false),(9,false),(1,false),(6,true),(7,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 79686 ([(0,true),(1,true),(2,true),(3,true),(4,true),(8,false)],[(11,false),(10,false),(9,false),(5,true),(6,true),(7,true)])
              (.node 79196 ([(1,false),(0,false),(5,false),(4,false),(3,false),(8,false)],[(11,false),(10,false),(9,false),(2,false),(6,true),(7,true)])
                (.node 79161 ([(2,false),(9,true),(0,true),(11,true),(4,true),(7,true)],[(3,false),(6,true),(5,true),(10,true),(1,true),(8,false)])
                  (.node 79151 ([(4,false),(11,false),(0,false),(9,false),(2,true),(7,true)],[(3,false),(6,false),(5,true),(10,true),(1,true),(8,false)])
                    .empty
                    .empty)
                  (.node 79181 ([(4,false),(3,false),(9,true),(0,true),(1,true),(7,true)],[(11,false),(10,false),(5,false),(6,true),(2,true),(8,false)])
                    .empty
                    .empty))
                (.node 79521 ([(3,true),(11,false),(1,true),(9,false),(5,false),(7,true)],[(4,true),(6,false),(2,false),(10,true),(0,false),(8,false)])
                  (.node 79511 ([(4,false),(3,false),(2,false),(1,false),(0,false),(8,false)],[(11,false),(10,false),(9,false),(5,false),(6,true),(7,true)])
                    .empty
                    .empty)
                  (.node 79671 ([(2,false),(1,false),(11,true),(4,true),(5,true),(7,true)],[(3,false),(6,true),(0,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)))
              (.node 79896 ([(0,true),(1,true),(2,true),(3,true),(4,true),(8,false)],[(11,false),(10,false),(9,false),(5,true),(6,true),(7,true)])
                (.node 79736 ([(1,false),(0,false),(9,true),(3,true),(4,true),(7,true)],[(11,false),(10,false),(2,false),(6,true),(5,true),(8,false)])
                  (.node 79721 ([(4,false),(3,false),(2,false),(1,false),(0,false),(8,false)],[(11,false),(10,false),(9,false),(5,false),(6,true),(7,true)])
                    .empty
                    .empty)
                  (.node 79886 ([(1,false),(10,false),(3,true),(4,true),(5,true),(7,true)],[(11,false),(0,false),(6,false),(2,true),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 80226 ([(0,true),(1,true),(9,true),(4,false),(3,false),(7,true)],[(11,false),(10,false),(5,true),(6,true),(2,false),(8,false)])
                  (.node 80211 ([(2,false),(1,false),(11,true),(4,true),(5,true),(7,true)],[(3,false),(6,true),(0,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  .empty))))
          (.node 81451 ([(0,false),(5,false),(4,false),(11,false),(2,true),(7,true)],[(3,false),(6,false),(1,true),(10,false),(9,false),(8,false)])
            (.node 80591 ([(4,false),(3,false),(2,false),(1,false),(0,false),(8,false)],[(11,false),(10,false),(9,false),(5,false),(6,true),(7,true)])
              (.node 80471 ([(4,false),(3,false),(2,false),(10,false),(0,true),(7,true)],[(11,false),(1,false),(6,false),(5,true),(9,false),(8,false)])
                (.node 80411 ([(4,false),(3,false),(2,false),(10,false),(0,true),(8,false)],[(11,false),(1,false),(9,true),(5,false),(6,true),(7,true)])
                  (.node 80256 ([(0,true),(10,false),(4,false),(3,false),(2,false),(7,true)],[(11,false),(1,true),(6,false),(5,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 80421 ([(3,true),(11,false),(1,false),(0,false),(5,false),(7,true)],[(4,true),(6,false),(2,false),(10,false),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 80541 ([(2,false),(11,true),(4,true),(5,true),(0,true),(7,true)],[(3,false),(6,true),(1,true),(10,false),(9,false),(8,false)])
                  (.node 80491 ([(0,false),(5,false),(4,false),(11,false),(2,true),(8,false)],[(3,false),(9,true),(10,true),(1,false),(6,true),(7,true)])
                    .empty
                    .empty)
                  (.node 80551 ([(0,false),(5,false),(4,false),(11,false),(2,true),(7,true)],[(3,false),(6,false),(1,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)))
              (.node 81011 ([(4,false),(3,false),(2,false),(1,false),(0,false),(8,false)],[(11,false),(10,false),(9,false),(5,false),(6,true),(7,true)])
                (.node 80751 ([(3,true),(11,false),(1,false),(0,false),(5,false),(8,false)],[(4,true),(9,true),(10,true),(2,true),(6,true),(7,true)])
                  (.node 80601 ([(3,true),(11,false),(1,false),(0,false),(5,false),(7,true)],[(4,true),(6,false),(2,false),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 80766 ([(0,true),(1,true),(2,true),(3,true),(4,true),(8,false)],[(11,false),(10,false),(9,false),(5,true),(6,true),(7,true)])
                    .empty
                    .empty))
                (.node 81441 ([(2,false),(11,true),(4,true),(5,true),(0,true),(7,true)],[(3,false),(6,true),(1,true),(10,false),(9,false),(8,false)])
                  (.node 81031 ([(0,false),(9,true),(2,false),(11,true),(4,true),(7,true)],[(3,false),(10,true),(1,false),(6,true),(5,true),(8,false)])
                    .empty
                    .empty)
                  .empty)))
            (.node 87426 ([(5,false),(11,false),(1,true),(2,true),(3,true),(8,false)],[(4,false),(9,true),(10,true),(0,false),(6,true),(7,true)])
              (.node 86966 ([(1,false),(0,false),(5,false),(4,false),(3,false),(8,false)],[(11,false),(10,false),(9,false),(2,false),(6,true),(7,true)])
                (.node 81486 ([(0,true),(1,true),(10,false),(4,false),(3,false),(7,true)],[(11,false),(2,true),(6,false),(5,false),(9,false),(8,false)])
                  (.node 81471 ([(2,false),(11,true),(4,true),(9,false),(0,false),(7,true)],[(3,false),(6,true),(5,false),(10,true),(1,false),(8,false)])
                    .empty
                    .empty)
                  (.node 86956 ([(4,true),(5,true),(0,true),(1,true),(2,true),(8,false)],[(11,false),(10,false),(9,false),(3,true),(6,true),(7,true)])
                    .empty
                    .empty))
                (.node 87396 ([(5,false),(11,false),(1,true),(2,true),(3,true),(7,true)],[(4,false),(6,false),(0,true),(10,false),(9,false),(8,false)])
                  (.node 87376 ([(3,false),(2,false),(1,false),(11,true),(5,true),(7,true)],[(4,false),(6,true),(0,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 87411 ([(2,false),(1,false),(0,false),(5,false),(4,false),(8,false)],[(11,false),(10,false),(9,false),(3,false),(6,true),(7,true)])
                    .empty
                    .empty)))
              (.node 87576 ([(5,false),(11,false),(1,true),(2,true),(3,true),(7,true)],[(4,false),(6,false),(0,true),(10,false),(9,false),(8,false)])
                (.node 87506 ([(1,false),(10,false),(3,true),(4,true),(5,true),(8,false)],[(11,false),(0,false),(9,true),(2,false),(6,true),(7,true)])
                  (.node 87496 ([(3,false),(9,false),(5,false),(11,false),(1,true),(7,true)],[(4,false),(6,true),(2,true),(10,true),(0,false),(8,false)])
                    .empty
                    .empty)
                  (.node 87556 ([(3,false),(2,false),(1,false),(11,true),(5,true),(7,true)],[(4,false),(6,true),(0,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 87636 ([(0,true),(11,true),(4,false),(3,false),(2,false),(7,true)],[(5,true),(6,true),(1,false),(10,false),(9,false),(8,false)])
                  (.node 87626 ([(1,false),(10,false),(3,true),(4,true),(5,true),(7,true)],[(11,false),(0,false),(6,false),(2,true),(9,false),(8,false)])
                    .empty
                    .empty)
                  .empty)))))
        (.node 89866 ([(4,true),(11,false),(2,false),(1,false),(0,false),(8,false)],[(5,true),(9,true),(10,true),(3,true),(6,true),(7,true)])
          (.node 88836 ([(0,true),(9,true),(2,false),(11,true),(4,false),(7,true)],[(5,true),(6,true),(3,false),(10,true),(1,false),(8,false)])
            (.node 88456 ([(3,false),(9,true),(1,true),(11,true),(5,true),(7,true)],[(4,false),(6,true),(0,true),(10,true),(2,true),(8,false)])
              (.node 88246 ([(3,false),(2,false),(11,true),(5,true),(0,true),(7,true)],[(4,false),(6,true),(1,true),(10,false),(9,false),(8,false)])
                (.node 87806 ([(1,false),(0,false),(5,false),(4,false),(3,false),(8,false)],[(11,false),(10,false),(9,false),(2,false),(6,true),(7,true)])
                  (.node 87786 ([(0,true),(11,true),(4,false),(9,false),(2,true),(7,true)],[(5,true),(6,true),(3,true),(10,true),(1,true),(8,false)])
                    .empty
                    .empty)
                  (.node 87816 ([(0,true),(11,true),(4,false),(3,false),(2,false),(7,true)],[(5,true),(6,true),(1,false),(10,false),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 88281 ([(2,false),(1,false),(0,false),(5,false),(4,false),(8,false)],[(11,false),(10,false),(9,false),(3,false),(6,true),(7,true)])
                  (.node 88261 ([(0,false),(5,false),(11,false),(2,true),(3,true),(7,true)],[(4,false),(6,false),(1,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 88291 ([(0,false),(5,false),(11,false),(2,true),(3,true),(8,false)],[(4,false),(9,true),(10,true),(1,false),(6,true),(7,true)])
                    .empty
                    .empty)))
              (.node 88786 ([(3,false),(2,false),(11,true),(5,true),(0,true),(7,true)],[(4,false),(6,true),(1,true),(10,false),(9,false),(8,false)])
                (.node 88491 ([(2,false),(1,false),(0,false),(5,false),(4,false),(8,false)],[(11,false),(10,false),(9,false),(3,false),(6,true),(7,true)])
                  (.node 88476 ([(5,false),(11,false),(1,false),(9,false),(3,true),(7,true)],[(4,false),(6,false),(0,true),(10,true),(2,true),(8,false)])
                    .empty
                    .empty)
                  (.node 88506 ([(0,true),(1,true),(11,true),(4,false),(3,false),(7,true)],[(5,true),(6,true),(2,false),(10,false),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 88816 ([(4,true),(11,false),(2,true),(9,false),(0,false),(7,true)],[(5,true),(6,false),(3,false),(10,true),(1,false),(8,false)])
                  (.node 88801 ([(0,false),(5,false),(11,false),(2,true),(3,true),(7,true)],[(4,false),(6,false),(1,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  .empty)))
            (.node 89521 ([(0,false),(5,false),(4,false),(3,false),(2,false),(8,false)],[(11,false),(10,false),(9,false),(1,false),(6,true),(7,true)])
              (.node 89046 ([(0,true),(1,true),(11,true),(4,false),(3,false),(7,true)],[(5,true),(6,true),(2,false),(10,false),(9,false),(8,false)])
                (.node 89011 ([(0,false),(5,false),(4,false),(10,true),(2,true),(7,true)],[(11,false),(1,false),(6,true),(3,true),(9,false),(8,false)])
                  (.node 89001 ([(2,false),(10,false),(4,true),(5,true),(0,true),(7,true)],[(11,false),(1,false),(6,false),(3,true),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 89031 ([(2,false),(1,false),(9,true),(4,true),(5,true),(7,true)],[(11,false),(10,false),(3,false),(6,true),(0,true),(8,false)])
                    .empty
                    .empty))
                (.node 89486 ([(1,false),(0,false),(5,false),(11,false),(3,true),(7,true)],[(4,false),(6,false),(2,true),(10,false),(9,false),(8,false)])
                  (.node 89476 ([(3,false),(11,true),(5,true),(0,true),(1,true),(7,true)],[(4,false),(6,true),(2,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 89506 ([(3,false),(11,true),(5,true),(9,false),(1,false),(7,true)],[(4,false),(6,true),(0,false),(10,true),(2,false),(8,false)])
                    .empty
                    .empty)))
              (.node 89736 ([(0,true),(1,true),(2,true),(11,true),(4,false),(7,true)],[(5,true),(6,true),(3,false),(10,false),(9,false),(8,false)])
                (.node 89666 ([(1,false),(0,false),(5,false),(11,false),(3,true),(7,true)],[(4,false),(6,false),(2,true),(10,false),(9,false),(8,false)])
                  (.node 89656 ([(3,false),(11,true),(5,true),(0,true),(1,true),(7,true)],[(4,false),(6,true),(2,true),(10,false),(9,false),(8,false)])
                    .empty
                    .empty)
                  (.node 89716 ([(4,true),(11,false),(2,false),(1,false),(0,false),(7,true)],[(5,true),(6,false),(3,false),(10,false),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 89796 ([(0,true),(9,false),(4,true),(11,false),(2,false),(7,true)],[(5,true),(6,true),(1,false),(10,true),(3,true),(8,false)])
                  (.node 89786 ([(1,false),(0,false),(5,false),(11,false),(3,true),(8,false)],[(4,false),(9,true),(10,true),(2,false),(6,true),(7,true)])
                    .empty
                    .empty)
                  .empty))))
          (.node 97137 ([(2,false),(10,false),(5,true),(0,true),(7,true),(8,true)],[(11,false),(1,false),(6,false),(3,true),(4,true),(9,false)])
            (.node 96827 ([(4,false),(3,false),(2,false),(11,true),(0,true),(8,true)],[(5,false),(6,true),(7,true),(1,true),(10,false),(9,false)])
              (.node 90326 ([(1,false),(9,true),(3,false),(11,true),(5,true),(7,true)],[(4,false),(10,true),(2,false),(6,true),(0,true),(8,false)])
                (.node 89896 ([(4,true),(11,false),(2,false),(1,false),(0,false),(7,true)],[(5,true),(6,false),(3,false),(10,false),(9,false),(8,false)])
                  (.node 89881 ([(1,true),(2,true),(3,true),(4,true),(5,true),(8,false)],[(11,false),(10,false),(9,false),(0,true),(6,true),(7,true)])
                    .empty
                    .empty)
                  (.node 89916 ([(0,true),(1,true),(2,true),(11,true),(4,false),(7,true)],[(5,true),(6,true),(3,false),(10,false),(9,false),(8,false)])
                    .empty
                    .empty))
                (.node 96707 ([(4,false),(7,false),(0,false),(11,false),(2,true),(9,false)],[(5,false),(6,true),(1,true),(10,false),(3,true),(8,true)])
                  (.node 90336 ([(5,false),(4,false),(3,false),(2,false),(1,false),(8,false)],[(11,false),(10,false),(9,false),(0,false),(6,true),(7,true)])
                    .empty
                    .empty)
                  (.node 96742 ([(3,false),(2,false),(11,true),(0,true),(7,true),(8,true)],[(5,false),(4,false),(6,true),(1,true),(10,false),(9,false)])
                    .empty
                    .empty)))
              (.node 96957 ([(2,false),(1,false),(0,false),(5,false),(4,false),(9,false)],[(11,false),(10,false),(3,false),(6,true),(7,true),(8,true)])
                (.node 96887 ([(4,false),(10,true),(11,true),(0,true),(7,true),(8,true)],[(5,false),(6,true),(1,true),(2,true),(3,true),(9,false)])
                  (.node 96837 ([(2,false),(1,false),(0,false),(5,false),(4,false),(9,false)],[(11,false),(10,false),(3,false),(6,true),(7,true),(8,true)])
                    .empty
                    .empty)
                  (.node 96907 ([(0,false),(5,false),(4,false),(10,true),(2,true),(8,true)],[(11,false),(1,false),(6,true),(7,true),(3,true),(9,false)])
                    .empty
                    .empty))
                (.node 97102 ([(3,false),(2,false),(1,false),(0,false),(5,false),(9,false)],[(11,false),(10,false),(4,false),(6,true),(7,true),(8,true)])
                  (.node 96967 ([(0,false),(5,false),(7,false),(2,false),(10,false),(9,false)],[(11,false),(1,false),(6,true),(3,true),(4,true),(8,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 98377 ([(0,false),(5,false),(10,true),(3,true),(7,true),(8,true)],[(11,false),(2,false),(1,false),(6,true),(4,true),(9,false)])
              (.node 97822 ([(6,true),(1,true),(2,true),(11,true),(5,false),(8,true)],[(0,true),(7,true),(4,false),(3,false),(10,false),(9,false)])
                (.node 97612 ([(3,false),(2,false),(7,true),(5,true),(0,true),(9,false)],[(11,false),(10,false),(1,true),(6,false),(4,true),(8,true)])
                  (.node 97577 ([(4,false),(7,false),(2,true),(11,true),(0,true),(9,false)],[(5,false),(6,true),(1,false),(10,true),(3,true),(8,true)])
                    .empty
                    .empty)
                  (.node 97787 ([(4,false),(7,false),(0,false),(11,false),(2,false),(9,false)],[(5,false),(6,true),(1,true),(10,true),(3,true),(8,true)])
                    .empty
                    .empty))
                (.node 98167 ([(0,false),(5,false),(7,true),(2,true),(3,true),(9,false)],[(11,false),(10,false),(4,true),(6,false),(1,true),(8,true)])
                  (.node 98132 ([(6,true),(4,false),(3,false),(11,true),(0,true),(8,true)],[(5,false),(7,true),(1,true),(2,true),(10,false),(9,false)])
                    .empty
                    .empty)
                  (.node 98342 ([(1,false),(0,false),(11,false),(3,true),(4,true),(9,false)],[(5,false),(10,true),(2,false),(6,true),(7,true),(8,true)])
                    .empty
                    .empty)))
              (.node 98997 ([(2,false),(10,true),(4,true),(5,true),(0,true),(8,true)],[(11,false),(3,false),(6,true),(7,true),(1,true),(9,false)])
                (.node 98852 ([(1,false),(0,false),(11,false),(4,true),(7,true),(8,true)],[(5,false),(6,false),(2,true),(3,true),(10,false),(9,false)])
                  (.node 98817 ([(2,false),(7,false),(4,false),(11,true),(0,true),(9,false)],[(5,false),(6,false),(3,true),(10,false),(1,true),(8,true)])
                    .empty
                    .empty)
                  (.node 98987 ([(4,false),(11,true),(0,true),(7,false),(2,false),(9,false)],[(5,false),(6,true),(3,true),(10,false),(1,false),(8,true)])
                    .empty
                    .empty))
                (.node 99067 ([(0,false),(5,false),(4,false),(3,false),(2,false),(9,false)],[(11,false),(10,false),(1,false),(6,true),(7,true),(8,true)])
                  (.node 99047 ([(4,false),(11,true),(0,true),(1,true),(2,true),(8,true)],[(5,false),(6,true),(7,true),(3,true),(10,false),(9,false)])
                    .empty
                    .empty)
                  .empty))))))))
  (.node 165688 ([(3,false),(11,false),(1,true),(7,true),(5,false),(9,true)],[(2,false),(6,false),(4,true),(8,false),(0,true),(10,false)])
    (.node 134212 ([(3,false),(10,true),(11,true),(5,true),(7,true),(8,true)],[(4,false),(6,true),(0,true),(1,true),(2,true),(9,false)])
      (.node 117017 ([(6,true),(1,false),(0,false),(11,true),(3,true),(8,true)],[(2,false),(7,true),(4,true),(5,true),(10,false),(9,false)])
        (.node 108507 ([(2,false),(1,false),(0,false),(5,false),(4,false),(9,false)],[(11,false),(10,false),(3,false),(6,true),(7,true),(8,true)])
          (.node 106412 ([(1,false),(0,false),(10,true),(4,true),(7,true),(8,true)],[(11,false),(3,false),(2,false),(6,true),(5,true),(9,false)])
            (.node 106072 ([(3,false),(2,false),(1,false),(0,false),(5,false),(9,false)],[(11,false),(10,false),(4,false),(6,true),(7,true),(8,true)])
              (.node 105137 ([(4,false),(3,false),(2,false),(1,false),(0,false),(9,false)],[(11,false),(10,false),(5,false),(6,true),(7,true),(8,true)])
                (.node 99212 ([(1,false),(0,false),(5,false),(4,false),(3,false),(9,false)],[(11,false),(10,false),(2,false),(6,true),(7,true),(8,true)])
                  (.node 99127 ([(0,false),(5,false),(4,false),(3,false),(2,false),(9,false)],[(11,false),(10,false),(1,false),(6,true),(7,true),(8,true)])
                    .empty
                    .empty)
                  (.node 99247 ([(1,true),(7,false),(5,true),(11,false),(3,false),(9,false)],[(0,true),(6,true),(4,false),(10,false),(2,false),(8,true)])
                    .empty
                    .empty))
                (.node 105857 ([(4,false),(3,false),(11,true),(1,true),(7,true),(8,true)],[(0,false),(5,false),(6,true),(2,true),(10,false),(9,false)])
                  (.node 105172 ([(3,false),(10,false),(0,true),(1,true),(7,true),(8,true)],[(11,false),(2,false),(6,false),(4,true),(5,true),(9,false)])
                    .empty
                    .empty)
                  (.node 106032 ([(5,false),(7,false),(1,false),(11,false),(3,true),(9,false)],[(0,false),(6,true),(2,true),(10,false),(4,true),(8,true)])
                    .empty
                    .empty)))
              (.node 106202 ([(1,false),(0,false),(5,false),(10,true),(3,true),(8,true)],[(11,false),(2,false),(6,true),(7,true),(4,true),(9,false)])
                (.node 106132 ([(3,false),(2,false),(1,false),(0,false),(5,false),(9,false)],[(11,false),(10,false),(4,false),(6,true),(7,true),(8,true)])
                  (.node 106082 ([(1,false),(0,false),(7,false),(3,false),(10,false),(9,false)],[(11,false),(2,false),(6,true),(4,true),(5,true),(8,true)])
                    .empty
                    .empty)
                  (.node 106152 ([(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(11,false),(10,false),(5,true),(6,true),(7,true),(8,true)])
                    .empty
                    .empty))
                (.node 106377 ([(2,false),(1,false),(11,false),(4,true),(5,true),(9,false)],[(0,false),(10,true),(3,false),(6,true),(7,true),(8,true)])
                  (.node 106212 ([(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(11,false),(10,false),(5,true),(6,true),(7,true),(8,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 108147 ([(2,false),(1,false),(11,false),(5,true),(7,true),(8,true)],[(0,false),(6,false),(3,true),(4,true),(10,false),(9,false)])
              (.node 107112 ([(0,true),(1,true),(7,true),(4,false),(3,false),(9,false)],[(11,false),(10,false),(2,false),(6,false),(5,false),(8,true)])
                (.node 106902 ([(0,true),(1,true),(10,true),(3,false),(7,true),(8,true)],[(11,false),(4,true),(5,true),(6,true),(2,false),(9,false)])
                  (.node 106727 ([(4,false),(3,false),(7,true),(0,true),(1,true),(9,false)],[(11,false),(10,false),(2,true),(6,false),(5,true),(8,true)])
                    .empty
                    .empty)
                  (.node 106937 ([(6,true),(2,true),(3,true),(11,true),(0,false),(8,true)],[(1,true),(7,true),(5,false),(4,false),(10,false),(9,false)])
                    .empty
                    .empty))
                (.node 107462 ([(1,false),(0,false),(7,true),(3,true),(4,true),(9,false)],[(11,false),(10,false),(5,true),(6,false),(2,true),(8,true)])
                  (.node 107427 ([(6,true),(5,false),(4,false),(11,true),(1,true),(8,true)],[(0,false),(7,true),(2,true),(3,true),(10,false),(9,false)])
                    .empty
                    .empty)
                  (.node 108112 ([(3,false),(7,false),(5,false),(11,true),(1,true),(9,false)],[(0,false),(6,false),(4,true),(10,false),(2,true),(8,true)])
                    .empty
                    .empty)))
              (.node 108312 ([(0,true),(1,true),(7,false),(4,true),(10,false),(9,false)],[(11,false),(5,true),(6,true),(3,false),(2,false),(8,true)])
                (.node 108242 ([(1,false),(0,false),(5,false),(4,false),(3,false),(9,false)],[(11,false),(10,false),(2,false),(6,true),(7,true),(8,true)])
                  (.node 108232 ([(3,false),(2,false),(1,false),(11,false),(5,true),(8,true)],[(0,false),(7,false),(6,false),(4,true),(10,false),(9,false)])
                    .empty
                    .empty)
                  (.node 108292 ([(3,false),(10,true),(5,true),(0,true),(1,true),(8,true)],[(11,false),(4,false),(6,true),(7,true),(2,true),(9,false)])
                    .empty
                    .empty))
                (.node 108372 ([(0,true),(1,true),(2,true),(10,true),(4,false),(8,true)],[(11,false),(5,true),(6,true),(7,true),(3,false),(9,false)])
                  (.node 108362 ([(1,false),(0,false),(5,false),(4,false),(3,false),(9,false)],[(11,false),(10,false),(2,false),(6,true),(7,true),(8,true)])
                    .empty
                    .empty)
                  .empty))))
          (.node 114187 ([(0,false),(5,false),(4,false),(11,true),(2,true),(8,true)],[(1,false),(6,true),(7,true),(3,true),(10,false),(9,false)])
            (.node 109917 ([(2,false),(1,false),(0,false),(5,false),(4,false),(9,false)],[(11,false),(10,false),(3,false),(6,true),(7,true),(8,true)])
              (.node 109787 ([(4,false),(3,false),(2,false),(11,false),(0,true),(8,true)],[(1,false),(7,false),(6,false),(5,true),(10,false),(9,false)])
                (.node 109667 ([(4,false),(7,false),(0,false),(11,true),(2,true),(9,false)],[(1,false),(6,false),(5,true),(10,false),(3,true),(8,true)])
                  (.node 108542 ([(2,true),(7,false),(0,true),(11,false),(4,false),(9,false)],[(1,true),(6,true),(5,false),(10,false),(3,false),(8,true)])
                    .empty
                    .empty)
                  (.node 109702 ([(3,false),(2,false),(11,false),(0,true),(7,true),(8,true)],[(1,false),(6,false),(4,true),(5,true),(10,false),(9,false)])
                    .empty
                    .empty))
                (.node 109847 ([(4,false),(10,true),(0,true),(1,true),(2,true),(8,true)],[(11,false),(5,false),(6,true),(7,true),(3,true),(9,false)])
                  (.node 109797 ([(2,false),(1,false),(0,false),(5,false),(4,false),(9,false)],[(11,false),(10,false),(3,false),(6,true),(7,true),(8,true)])
                    .empty
                    .empty)
                  (.node 109867 ([(0,false),(11,true),(2,true),(7,false),(4,false),(9,false)],[(1,false),(6,true),(5,true),(10,false),(3,false),(8,true)])
                    .empty
                    .empty)))
              (.node 114107 ([(4,false),(3,false),(2,false),(1,false),(0,false),(9,false)],[(11,false),(10,false),(5,false),(6,true),(7,true),(8,true)])
                (.node 110062 ([(3,false),(2,false),(1,false),(0,false),(5,false),(9,false)],[(11,false),(10,false),(4,false),(6,true),(7,true),(8,true)])
                  (.node 109927 ([(0,false),(11,true),(2,true),(3,true),(4,true),(8,true)],[(1,false),(6,true),(7,true),(5,true),(10,false),(9,false)])
                    .empty
                    .empty)
                  (.node 110097 ([(3,true),(7,false),(1,true),(11,false),(5,false),(9,false)],[(2,true),(6,true),(0,false),(10,false),(4,false),(8,true)])
                    .empty
                    .empty))
                (.node 114167 ([(4,false),(3,false),(2,false),(1,false),(0,false),(9,false)],[(11,false),(10,false),(5,false),(6,true),(7,true),(8,true)])
                  (.node 114117 ([(2,false),(1,false),(7,false),(4,false),(10,false),(9,false)],[(11,false),(3,false),(6,true),(5,true),(0,true),(8,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 115497 ([(2,false),(1,false),(7,true),(4,true),(5,true),(9,false)],[(11,false),(10,false),(0,true),(6,false),(3,true),(8,true)])
              (.node 114462 ([(0,true),(1,true),(11,false),(3,false),(7,true),(8,true)],[(2,true),(6,false),(5,false),(4,false),(10,false),(9,false)])
                (.node 114247 ([(0,false),(10,true),(11,true),(2,true),(7,true),(8,true)],[(1,false),(6,true),(3,true),(4,true),(5,true),(9,false)])
                  (.node 114237 ([(2,false),(1,false),(0,false),(10,true),(4,true),(8,true)],[(11,false),(3,false),(6,true),(7,true),(5,true),(9,false)])
                    .empty
                    .empty)
                  (.node 114287 ([(4,false),(10,false),(1,true),(2,true),(7,true),(8,true)],[(11,false),(3,false),(6,false),(5,true),(0,true),(9,false)])
                    .empty
                    .empty))
                (.node 115182 ([(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(11,false),(10,false),(5,true),(6,true),(7,true),(8,true)])
                  (.node 115147 ([(0,false),(7,false),(2,false),(11,false),(4,true),(9,false)],[(1,false),(6,true),(3,true),(10,false),(5,true),(8,true)])
                    .empty
                    .empty)
                  (.node 115462 ([(6,true),(0,false),(5,false),(11,true),(2,true),(8,true)],[(1,false),(7,true),(3,true),(4,true),(10,false),(9,false)])
                    .empty
                    .empty)))
              (.node 116052 ([(0,true),(1,true),(11,false),(4,false),(3,false),(9,false)],[(2,true),(10,true),(5,true),(6,true),(7,true),(8,true)])
                (.node 115707 ([(2,false),(1,false),(10,true),(5,true),(7,true),(8,true)],[(11,false),(4,false),(3,false),(6,true),(0,true),(9,false)])
                  (.node 115672 ([(3,false),(2,false),(11,false),(5,true),(0,true),(9,false)],[(1,false),(10,true),(4,false),(6,true),(7,true),(8,true)])
                    .empty
                    .empty)
                  (.node 116017 ([(0,false),(7,false),(4,true),(11,true),(2,true),(9,false)],[(1,false),(6,true),(3,false),(10,true),(5,true),(8,true)])
                    .empty
                    .empty))
                (.node 116262 ([(6,true),(3,true),(4,true),(11,true),(1,false),(8,true)],[(2,true),(7,true),(0,false),(5,false),(10,false),(9,false)])
                  (.node 116227 ([(0,false),(7,false),(2,false),(11,false),(4,false),(9,false)],[(1,false),(6,true),(3,true),(10,true),(5,true),(8,true)])
                    .empty
                    .empty)
                  .empty)))))
        (.node 124907 ([(4,false),(3,false),(2,false),(10,true),(0,true),(8,true)],[(11,false),(5,false),(6,true),(7,true),(1,true),(9,false)])
          (.node 119112 ([(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(11,false),(10,false),(5,true),(6,true),(7,true),(8,true)])
            (.node 118097 ([(4,false),(3,false),(2,false),(1,false),(0,false),(9,false)],[(11,false),(10,false),(5,false),(6,true),(7,true),(8,true)])
              (.node 117572 ([(1,false),(7,false),(5,true),(11,true),(3,true),(9,false)],[(2,false),(6,true),(4,false),(10,true),(0,true),(8,true)])
                (.node 117227 ([(4,false),(3,false),(11,false),(0,true),(1,true),(9,false)],[(2,false),(10,true),(5,false),(6,true),(7,true),(8,true)])
                  (.node 117052 ([(3,false),(2,false),(7,true),(5,true),(0,true),(9,false)],[(11,false),(10,false),(1,true),(6,false),(4,true),(8,true)])
                    .empty
                    .empty)
                  (.node 117262 ([(3,false),(2,false),(10,true),(0,true),(7,true),(8,true)],[(11,false),(5,false),(4,false),(6,true),(1,true),(9,false)])
                    .empty
                    .empty))
                (.node 117782 ([(1,false),(7,false),(3,false),(11,false),(5,false),(9,false)],[(2,false),(6,true),(4,true),(10,true),(0,true),(8,true)])
                  (.node 117607 ([(0,false),(5,false),(7,true),(2,true),(3,true),(9,false)],[(11,false),(10,false),(4,true),(6,false),(1,true),(8,true)])
                    .empty
                    .empty)
                  (.node 117817 ([(6,true),(4,true),(5,true),(11,true),(2,false),(8,true)],[(3,true),(7,true),(1,false),(0,false),(10,false),(9,false)])
                    .empty
                    .empty)))
              (.node 119032 ([(3,false),(2,false),(1,false),(0,false),(5,false),(9,false)],[(11,false),(10,false),(4,false),(6,true),(7,true),(8,true)])
                (.node 118817 ([(4,false),(3,false),(11,false),(1,true),(7,true),(8,true)],[(2,false),(6,false),(5,true),(0,true),(10,false),(9,false)])
                  (.node 118132 ([(4,true),(7,false),(2,true),(11,false),(0,false),(9,false)],[(3,true),(6,true),(1,false),(10,false),(5,false),(8,true)])
                    .empty
                    .empty)
                  (.node 118992 ([(0,true),(10,false),(3,false),(2,false),(7,true),(8,true)],[(11,false),(1,true),(6,false),(5,false),(4,false),(9,false)])
                    .empty
                    .empty))
                (.node 119092 ([(3,false),(2,false),(1,false),(0,false),(5,false),(9,false)],[(11,false),(10,false),(4,false),(6,true),(7,true),(8,true)])
                  (.node 119042 ([(1,false),(11,true),(3,true),(4,true),(5,true),(8,true)],[(2,false),(6,true),(7,true),(0,true),(10,false),(9,false)])
                    .empty
                    .empty)
                  .empty)))
            (.node 123432 ([(0,true),(10,true),(4,false),(3,false),(2,false),(8,true)],[(11,false),(5,true),(6,true),(7,true),(1,false),(9,false)])
              (.node 123217 ([(0,false),(5,false),(11,true),(3,true),(7,true),(8,true)],[(2,false),(1,false),(6,true),(4,true),(10,false),(9,false)])
                (.node 119172 ([(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(11,false),(10,false),(5,true),(6,true),(7,true),(8,true)])
                  (.node 119162 ([(1,false),(11,true),(3,true),(7,false),(5,false),(9,false)],[(2,false),(6,true),(0,true),(10,false),(4,false),(8,true)])
                    .empty
                    .empty)
                  (.node 123182 ([(1,false),(7,false),(3,false),(11,false),(5,true),(9,false)],[(2,false),(6,true),(4,true),(10,false),(0,true),(8,true)])
                    .empty
                    .empty))
                (.node 123362 ([(1,false),(10,true),(11,true),(3,true),(7,true),(8,true)],[(2,false),(6,true),(4,true),(5,true),(0,true),(9,false)])
                  (.node 123352 ([(3,false),(2,false),(1,false),(10,true),(5,true),(8,true)],[(11,false),(4,false),(6,true),(7,true),(0,true),(9,false)])
                    .empty
                    .empty)
                  (.node 123412 ([(3,false),(2,false),(7,false),(5,false),(10,false),(9,false)],[(11,false),(4,false),(6,true),(0,true),(1,true),(8,true)])
                    .empty
                    .empty)))
              (.node 123612 ([(0,true),(7,false),(4,true),(11,true),(2,false),(9,false)],[(3,true),(6,false),(5,false),(10,false),(1,false),(8,true)])
                (.node 123492 ([(0,true),(1,true),(2,true),(11,false),(4,false),(8,true)],[(3,true),(7,false),(6,false),(5,false),(10,false),(9,false)])
                  (.node 123482 ([(1,false),(0,false),(5,false),(11,true),(3,true),(8,true)],[(2,false),(6,true),(7,true),(4,true),(10,false),(9,false)])
                    .empty
                    .empty)
                  (.node 123577 ([(0,false),(5,false),(4,false),(3,false),(2,false),(9,false)],[(11,false),(10,false),(1,false),(6,true),(7,true),(8,true)])
                    .empty
                    .empty))
                (.node 124772 ([(1,false),(0,false),(11,true),(4,true),(7,true),(8,true)],[(3,false),(2,false),(6,true),(5,true),(10,false),(9,false)])
                  (.node 124737 ([(2,false),(7,false),(4,false),(11,false),(0,true),(9,false)],[(3,false),(6,true),(5,true),(10,false),(1,true),(8,true)])
                    .empty
                    .empty)
                  .empty))))
          (.node 126902 ([(1,false),(0,false),(7,true),(3,true),(4,true),(9,false)],[(11,false),(10,false),(5,true),(6,false),(2,true),(8,true)])
            (.node 125817 ([(2,false),(7,false),(4,false),(11,false),(0,false),(9,false)],[(3,false),(6,true),(5,true),(10,true),(1,true),(8,true)])
              (.node 125037 ([(2,false),(1,false),(0,false),(11,true),(4,true),(8,true)],[(3,false),(6,true),(7,true),(5,true),(10,false),(9,false)])
                (.node 124967 ([(4,false),(3,false),(7,false),(0,false),(10,false),(9,false)],[(11,false),(5,false),(6,true),(1,true),(2,true),(8,true)])
                  (.node 124917 ([(2,false),(10,true),(11,true),(4,true),(7,true),(8,true)],[(3,false),(6,true),(5,true),(0,true),(1,true),(9,false)])
                    .empty
                    .empty)
                  (.node 124987 ([(0,false),(5,false),(4,false),(3,false),(2,false),(9,false)],[(11,false),(10,false),(1,false),(6,true),(7,true),(8,true)])
                    .empty
                    .empty))
                (.node 125132 ([(1,false),(0,false),(5,false),(4,false),(3,false),(9,false)],[(11,false),(10,false),(2,false),(6,true),(7,true),(8,true)])
                  (.node 125047 ([(0,false),(5,false),(4,false),(3,false),(2,false),(9,false)],[(11,false),(10,false),(1,false),(6,true),(7,true),(8,true)])
                    .empty
                    .empty)
                  (.node 125167 ([(0,false),(10,false),(3,true),(4,true),(7,true),(8,true)],[(11,false),(5,false),(6,false),(1,true),(2,true),(9,false)])
                    .empty
                    .empty)))
              (.node 126377 ([(4,false),(3,false),(10,true),(1,true),(7,true),(8,true)],[(11,false),(0,false),(5,false),(6,true),(2,true),(9,false)])
                (.node 126167 ([(4,false),(3,false),(7,true),(0,true),(1,true),(9,false)],[(11,false),(10,false),(2,true),(6,false),(5,true),(8,true)])
                  (.node 125852 ([(6,true),(5,true),(0,true),(11,true),(3,false),(8,true)],[(4,true),(7,true),(2,false),(1,false),(10,false),(9,false)])
                    .empty
                    .empty)
                  (.node 126342 ([(6,true),(2,false),(1,false),(11,true),(4,true),(8,true)],[(3,false),(7,true),(5,true),(0,true),(10,false),(9,false)])
                    .empty
                    .empty))
                (.node 126867 ([(2,false),(7,false),(0,true),(11,true),(4,true),(9,false)],[(3,false),(6,true),(5,false),(10,true),(1,true),(8,true)])
                  (.node 126552 ([(0,true),(1,true),(7,true),(4,false),(3,false),(9,false)],[(11,false),(10,false),(2,false),(6,false),(5,false),(8,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 127422 ([(0,true),(1,true),(11,true),(3,false),(7,true),(8,true)],[(4,true),(5,true),(6,true),(2,false),(10,false),(9,false)])
              (.node 127147 ([(0,false),(5,false),(4,false),(11,false),(2,true),(8,true)],[(3,false),(7,false),(6,false),(1,true),(10,false),(9,false)])
                (.node 127077 ([(2,false),(11,true),(4,true),(5,true),(0,true),(8,true)],[(3,false),(6,true),(7,true),(1,true),(10,false),(9,false)])
                  (.node 127067 ([(4,false),(3,false),(2,false),(1,false),(0,false),(9,false)],[(11,false),(10,false),(5,false),(6,true),(7,true),(8,true)])
                    .empty
                    .empty)
                  (.node 127127 ([(4,false),(3,false),(2,false),(1,false),(0,false),(9,false)],[(11,false),(10,false),(5,false),(6,true),(7,true),(8,true)])
                    .empty
                    .empty))
                (.node 127207 ([(0,false),(10,true),(2,true),(3,true),(4,true),(8,true)],[(11,false),(1,false),(6,true),(7,true),(5,true),(9,false)])
                  (.node 127197 ([(2,false),(11,true),(4,true),(7,false),(0,false),(9,false)],[(3,false),(6,true),(1,true),(10,false),(5,false),(8,true)])
                    .empty
                    .empty)
                  (.node 127247 ([(5,true),(7,false),(3,true),(11,false),(1,false),(9,false)],[(4,true),(6,true),(2,false),(10,false),(0,false),(8,true)])
                    .empty
                    .empty)))
              (.node 134067 ([(2,false),(1,false),(11,true),(5,true),(7,true),(8,true)],[(4,false),(3,false),(6,true),(0,true),(10,false),(9,false)])
                (.node 128142 ([(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(11,false),(10,false),(5,true),(6,true),(7,true),(8,true)])
                  (.node 128107 ([(0,false),(7,false),(2,false),(11,true),(4,true),(9,false)],[(3,false),(6,false),(1,true),(10,false),(5,true),(8,true)])
                    .empty
                    .empty)
                  (.node 134032 ([(3,false),(7,false),(5,false),(11,false),(1,true),(9,false)],[(4,false),(6,true),(0,true),(10,false),(2,true),(8,true)])
                    .empty
                    .empty))
                (.node 134162 ([(1,false),(0,false),(5,false),(4,false),(3,false),(9,false)],[(11,false),(10,false),(2,false),(6,true),(7,true),(8,true)])
                  (.node 134152 ([(3,false),(2,false),(1,false),(11,true),(5,true),(8,true)],[(4,false),(6,true),(7,true),(0,true),(10,false),(9,false)])
                    .empty
                    .empty)
                  .empty))))))
      (.node 152858 ([(1,false),(0,false),(5,false),(4,false),(3,false),(10,false)],[(11,false),(2,false),(6,true),(7,true),(8,true),(9,true)])
        (.node 143613 ([(2,false),(11,true),(0,true),(7,true),(4,false),(9,true)],[(5,false),(8,true),(3,false),(6,true),(1,true),(10,false)])
          (.node 136177 ([(0,false),(5,false),(11,false),(3,true),(7,true),(8,true)],[(4,false),(6,false),(1,true),(2,true),(10,false),(9,false)])
            (.node 135112 ([(3,false),(7,false),(5,false),(11,false),(1,false),(9,false)],[(4,false),(6,true),(0,true),(10,true),(2,true),(8,true)])
              (.node 134427 ([(2,false),(1,false),(0,false),(5,false),(4,false),(9,false)],[(11,false),(10,false),(3,false),(6,true),(7,true),(8,true)])
                (.node 134282 ([(1,false),(0,false),(5,false),(4,false),(3,false),(9,false)],[(11,false),(10,false),(2,false),(6,true),(7,true),(8,true)])
                  (.node 134232 ([(0,true),(11,true),(4,false),(3,false),(2,false),(8,true)],[(5,true),(6,true),(7,true),(1,false),(10,false),(9,false)])
                    .empty
                    .empty)
                  (.node 134292 ([(0,true),(11,true),(4,false),(7,false),(2,true),(9,false)],[(5,true),(6,true),(1,false),(10,false),(3,true),(8,true)])
                    .empty
                    .empty))
                (.node 134902 ([(3,false),(7,false),(1,true),(11,true),(5,true),(9,false)],[(4,false),(6,true),(0,false),(10,true),(2,true),(8,true)])
                  (.node 134462 ([(1,false),(10,false),(4,true),(5,true),(7,true),(8,true)],[(11,false),(0,false),(6,false),(2,true),(3,true),(9,false)])
                    .empty
                    .empty)
                  (.node 134937 ([(2,false),(1,false),(7,true),(4,true),(5,true),(9,false)],[(11,false),(10,false),(0,true),(6,false),(3,true),(8,true)])
                    .empty
                    .empty)))
              (.node 135667 ([(0,false),(5,false),(11,false),(2,true),(3,true),(9,false)],[(4,false),(10,true),(1,false),(6,true),(7,true),(8,true)])
                (.node 135457 ([(6,true),(3,false),(2,false),(11,true),(5,true),(8,true)],[(4,false),(7,true),(0,true),(1,true),(10,false),(9,false)])
                  (.node 135147 ([(6,true),(0,true),(1,true),(11,true),(4,false),(8,true)],[(5,true),(7,true),(3,false),(2,false),(10,false),(9,false)])
                    .empty
                    .empty)
                  (.node 135492 ([(0,true),(7,false),(4,true),(11,false),(2,true),(9,false)],[(5,true),(6,true),(3,false),(10,true),(1,false),(8,true)])
                    .empty
                    .empty))
                (.node 136142 ([(1,false),(7,false),(3,false),(11,true),(5,true),(9,false)],[(4,false),(6,false),(2,true),(10,false),(0,true),(8,true)])
                  (.node 135702 ([(0,true),(7,false),(2,false),(11,true),(4,false),(9,false)],[(5,true),(6,true),(3,true),(10,true),(1,false),(8,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 136572 ([(0,true),(7,false),(4,true),(11,false),(2,false),(9,false)],[(5,true),(6,true),(3,false),(10,false),(1,false),(8,true)])
              (.node 136392 ([(0,true),(10,true),(11,true),(4,false),(7,true),(8,true)],[(5,true),(6,true),(3,false),(2,false),(1,false),(9,false)])
                (.node 136322 ([(1,false),(10,true),(3,true),(4,true),(5,true),(8,true)],[(11,false),(2,false),(6,true),(7,true),(0,true),(9,false)])
                  (.node 136312 ([(3,false),(11,true),(5,true),(7,false),(1,false),(9,false)],[(4,false),(6,true),(2,true),(10,false),(0,false),(8,true)])
                    .empty
                    .empty)
                  (.node 136372 ([(3,false),(11,true),(5,true),(0,true),(1,true),(8,true)],[(4,false),(6,true),(7,true),(2,true),(10,false),(9,false)])
                    .empty
                    .empty))
                (.node 136452 ([(0,true),(1,true),(2,true),(11,true),(4,false),(8,true)],[(5,true),(6,true),(7,true),(3,false),(10,false),(9,false)])
                  (.node 136442 ([(1,false),(0,false),(5,false),(11,false),(3,true),(8,true)],[(4,false),(7,false),(6,false),(2,true),(10,false),(9,false)])
                    .empty
                    .empty)
                  (.node 136537 ([(0,false),(5,false),(4,false),(3,false),(2,false),(9,false)],[(11,false),(10,false),(1,false),(6,true),(7,true),(8,true)])
                    .empty
                    .empty)))
              (.node 143493 ([(2,false),(11,true),(0,true),(7,false),(4,false),(9,true)],[(5,false),(6,false),(3,true),(8,false),(1,true),(10,false)])
                (.node 143398 ([(3,false),(8,false),(7,false),(0,false),(11,false),(10,false)],[(5,false),(4,false),(6,true),(1,true),(2,true),(9,true)])
                  (.node 143363 ([(5,true),(0,true),(7,true),(3,false),(2,false),(10,false)],[(11,false),(1,false),(6,false),(4,false),(8,true),(9,true)])
                    .empty
                    .empty)
                  (.node 143483 ([(4,false),(3,false),(7,true),(0,false),(11,false),(10,false)],[(5,false),(6,true),(2,false),(1,false),(8,true),(9,true)])
                    .empty
                    .empty))
                (.node 143563 ([(0,false),(5,false),(4,false),(3,false),(2,false),(10,false)],[(11,false),(1,false),(6,true),(7,true),(8,true),(9,true)])
                  (.node 143543 ([(4,false),(3,false),(7,false),(0,false),(11,false),(10,false)],[(5,false),(6,true),(1,true),(2,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  .empty))))
          (.node 145653 ([(2,false),(1,false),(0,false),(5,false),(4,false),(10,false)],[(11,false),(3,false),(6,true),(7,true),(8,true),(9,true)])
            (.node 144788 ([(1,false),(0,false),(5,false),(4,false),(3,false),(10,false)],[(11,false),(2,false),(6,true),(7,true),(8,true),(9,true)])
              (.node 144233 ([(4,false),(7,false),(1,false),(0,false),(11,false),(10,false)],[(5,false),(6,true),(2,true),(3,true),(8,true),(9,true)])
                (.node 143758 ([(3,false),(7,false),(1,true),(11,true),(5,false),(9,true)],[(0,true),(6,false),(4,true),(8,false),(2,false),(10,false)])
                  (.node 143623 ([(0,false),(5,false),(4,false),(3,false),(2,false),(10,false)],[(11,false),(1,false),(6,true),(7,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  (.node 143793 ([(2,false),(11,true),(0,true),(7,true),(4,true),(9,true)],[(5,false),(8,false),(3,false),(6,true),(1,true),(10,false)])
                    .empty
                    .empty))
                (.node 144443 ([(4,false),(3,false),(11,true),(0,true),(1,true),(9,true)],[(5,false),(6,true),(7,true),(8,true),(2,true),(10,false)])
                  (.node 144268 ([(3,false),(11,true),(5,false),(7,false),(1,false),(9,true)],[(0,true),(8,false),(4,false),(6,true),(2,true),(10,false)])
                    .empty
                    .empty)
                  (.node 144478 ([(3,false),(11,true),(0,true),(7,true),(8,true),(9,true)],[(5,false),(4,false),(6,true),(1,true),(2,true),(10,false)])
                    .empty
                    .empty)))
              (.node 145473 ([(2,false),(1,false),(0,false),(5,false),(4,false),(10,false)],[(11,false),(3,false),(6,true),(7,true),(8,true),(9,true)])
                (.node 144998 ([(1,false),(0,false),(5,false),(4,false),(3,false),(10,false)],[(11,false),(2,false),(6,true),(7,true),(8,true),(9,true)])
                  (.node 144823 ([(0,false),(5,false),(7,true),(8,true),(3,false),(10,false)],[(11,false),(2,false),(1,false),(6,true),(4,false),(9,true)])
                    .empty
                    .empty)
                  (.node 145033 ([(0,false),(5,false),(4,false),(7,true),(2,true),(10,false)],[(11,false),(3,true),(6,false),(1,true),(8,true),(9,true)])
                    .empty
                    .empty))
                (.node 145643 ([(5,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(11,false),(4,true),(6,true),(7,true),(8,true),(9,true)])
                  (.node 145508 ([(1,false),(0,false),(5,false),(7,true),(3,true),(10,false)],[(11,false),(4,true),(6,false),(2,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 151828 ([(3,false),(11,true),(1,true),(7,true),(5,true),(9,true)],[(0,false),(8,false),(4,false),(6,true),(2,true),(10,false)])
              (.node 145783 ([(0,false),(5,false),(8,true),(2,true),(3,true),(10,false)],[(11,false),(4,true),(7,false),(6,false),(1,true),(9,true)])
                (.node 145723 ([(0,false),(11,false),(4,true),(7,true),(2,false),(9,true)],[(5,false),(6,false),(1,true),(8,false),(3,true),(10,false)])
                  (.node 145703 ([(4,false),(11,true),(0,true),(7,true),(2,false),(9,true)],[(5,false),(6,true),(1,true),(8,false),(3,true),(10,false)])
                    .empty
                    .empty)
                  (.node 145773 ([(2,false),(1,false),(0,false),(5,false),(4,false),(10,false)],[(11,false),(3,false),(6,true),(7,true),(8,true),(9,true)])
                    .empty
                    .empty))
                (.node 145903 ([(0,false),(5,false),(7,true),(2,true),(3,true),(10,false)],[(11,false),(4,true),(6,false),(1,true),(8,true),(9,true)])
                  (.node 145868 ([(1,false),(7,false),(5,true),(11,false),(3,false),(9,true)],[(0,true),(8,true),(2,false),(6,true),(4,false),(10,false)])
                    .empty
                    .empty)
                  (.node 151793 ([(4,false),(7,false),(2,true),(11,true),(0,false),(9,true)],[(1,true),(6,false),(5,true),(8,false),(3,false),(10,false)])
                    .empty
                    .empty)))
              (.node 152738 ([(1,false),(0,false),(5,false),(4,false),(3,false),(10,false)],[(11,false),(2,false),(6,true),(7,true),(8,true),(9,true)])
                (.node 152688 ([(0,true),(1,true),(7,true),(4,false),(3,false),(10,false)],[(11,false),(2,false),(6,false),(5,false),(8,true),(9,true)])
                  (.node 152513 ([(4,false),(8,false),(7,false),(1,false),(11,false),(10,false)],[(0,false),(5,false),(6,true),(2,true),(3,true),(9,true)])
                    .empty
                    .empty)
                  (.node 152728 ([(3,false),(11,true),(1,true),(7,true),(5,false),(9,true)],[(0,false),(8,true),(4,false),(6,true),(2,true),(10,false)])
                    .empty
                    .empty))
                (.node 152808 ([(0,true),(1,true),(8,true),(4,false),(3,false),(10,false)],[(11,false),(2,false),(7,false),(6,false),(5,false),(9,true)])
                  (.node 152788 ([(3,false),(11,true),(1,true),(7,false),(5,false),(9,true)],[(0,false),(6,false),(4,true),(8,false),(2,true),(10,false)])
                    .empty
                    .empty)
                  .empty)))))
        (.node 160763 ([(4,false),(11,true),(2,true),(7,true),(0,false),(9,true)],[(1,false),(8,true),(5,false),(6,true),(3,true),(10,false)])
          (.node 154968 ([(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(11,false),(5,true),(6,true),(7,true),(8,true),(9,true)])
            (.node 154083 ([(2,false),(1,false),(0,false),(5,false),(4,false),(10,false)],[(11,false),(3,false),(6,true),(7,true),(8,true),(9,true)])
              (.node 153383 ([(4,false),(11,true),(0,false),(7,false),(2,false),(9,true)],[(1,true),(8,false),(5,false),(6,true),(3,true),(10,false)])
                (.node 153033 ([(2,false),(1,false),(0,false),(5,false),(4,false),(10,false)],[(11,false),(3,false),(6,true),(7,true),(8,true),(9,true)])
                  (.node 152868 ([(0,true),(11,false),(2,false),(7,true),(4,true),(9,true)],[(1,true),(6,false),(5,false),(8,false),(3,false),(10,false)])
                    .empty
                    .empty)
                  (.node 153068 ([(1,false),(0,false),(5,false),(7,true),(3,true),(10,false)],[(11,false),(4,true),(6,false),(2,true),(8,true),(9,true)])
                    .empty
                    .empty))
                (.node 153593 ([(4,false),(11,true),(0,false),(7,false),(2,true),(9,true)],[(1,true),(6,false),(5,true),(8,true),(3,true),(10,false)])
                  (.node 153558 ([(0,true),(1,true),(2,true),(7,true),(4,false),(10,false)],[(11,false),(3,false),(6,false),(5,false),(8,true),(9,true)])
                    .empty
                    .empty)
                  (.node 153768 ([(0,true),(1,true),(7,true),(8,true),(3,true),(10,false)],[(11,false),(4,true),(5,true),(6,true),(2,true),(9,true)])
                    .empty
                    .empty)))
              (.node 154888 ([(3,false),(2,false),(1,false),(0,false),(5,false),(10,false)],[(11,false),(4,false),(6,true),(7,true),(8,true),(9,true)])
                (.node 154768 ([(3,false),(2,false),(1,false),(0,false),(5,false),(10,false)],[(11,false),(4,false),(6,true),(7,true),(8,true),(9,true)])
                  (.node 154118 ([(1,false),(0,false),(7,true),(8,true),(4,false),(10,false)],[(11,false),(3,false),(2,false),(6,true),(5,false),(9,true)])
                    .empty
                    .empty)
                  (.node 154803 ([(2,false),(1,false),(0,false),(7,true),(4,true),(10,false)],[(11,false),(5,true),(6,false),(3,true),(8,true),(9,true)])
                    .empty
                    .empty))
                (.node 154948 ([(3,false),(2,false),(1,false),(0,false),(5,false),(10,false)],[(11,false),(4,false),(6,true),(7,true),(8,true),(9,true)])
                  (.node 154898 ([(1,false),(0,false),(8,true),(3,true),(4,true),(10,false)],[(11,false),(5,true),(7,false),(6,false),(2,true),(9,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 156453 ([(2,false),(1,false),(8,true),(4,true),(5,true),(10,false)],[(11,false),(0,true),(7,false),(6,false),(3,true),(9,true)])
              (.node 155198 ([(1,false),(0,false),(7,true),(3,true),(4,true),(10,false)],[(11,false),(5,true),(6,false),(2,true),(8,true),(9,true)])
                (.node 155028 ([(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(11,false),(5,true),(6,true),(7,true),(8,true),(9,true)])
                  (.node 155018 ([(1,false),(11,false),(5,true),(7,true),(3,false),(9,true)],[(0,false),(6,false),(2,true),(8,false),(4,true),(10,false)])
                    .empty
                    .empty)
                  (.node 155163 ([(2,false),(7,false),(0,true),(11,false),(4,false),(9,true)],[(1,true),(8,true),(3,false),(6,true),(5,false),(10,false)])
                    .empty
                    .empty))
                (.node 156358 ([(3,false),(2,false),(1,false),(7,true),(5,true),(10,false)],[(11,false),(0,true),(6,false),(4,true),(8,true),(9,true)])
                  (.node 156323 ([(4,false),(3,false),(2,false),(1,false),(0,false),(10,false)],[(11,false),(5,false),(6,true),(7,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  (.node 156443 ([(4,false),(3,false),(2,false),(1,false),(0,false),(10,false)],[(11,false),(5,false),(6,true),(7,true),(8,true),(9,true)])
                    .empty
                    .empty)))
              (.node 156583 ([(0,false),(11,true),(2,true),(7,true),(4,false),(9,true)],[(1,false),(6,true),(3,true),(8,false),(5,true),(10,false)])
                (.node 156523 ([(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(11,false),(0,true),(6,true),(7,true),(8,true),(9,true)])
                  (.node 156503 ([(4,false),(3,false),(2,false),(1,false),(0,false),(10,false)],[(11,false),(5,false),(6,true),(7,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  (.node 156573 ([(2,false),(11,false),(0,true),(7,true),(4,false),(9,true)],[(1,false),(6,false),(3,true),(8,false),(5,true),(10,false)])
                    .empty
                    .empty))
                (.node 156753 ([(2,false),(1,false),(7,true),(4,true),(5,true),(10,false)],[(11,false),(0,true),(6,false),(3,true),(8,true),(9,true)])
                  (.node 156718 ([(3,false),(7,false),(1,true),(11,false),(5,false),(9,true)],[(2,true),(8,true),(4,false),(6,true),(0,false),(10,false)])
                    .empty
                    .empty)
                  .empty))))
          (.node 162708 ([(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(11,false),(5,true),(6,true),(7,true),(8,true),(9,true)])
            (.node 161803 ([(1,true),(2,true),(7,true),(5,false),(4,false),(10,false)],[(11,false),(3,false),(6,false),(0,false),(8,true),(9,true)])
              (.node 160893 ([(2,false),(1,false),(0,false),(5,false),(4,false),(10,false)],[(11,false),(3,false),(6,true),(7,true),(8,true),(9,true)])
                (.node 160823 ([(4,false),(11,true),(2,true),(7,false),(0,false),(9,true)],[(1,false),(6,false),(5,true),(8,false),(3,true),(10,false)])
                  (.node 160773 ([(2,false),(1,false),(0,false),(5,false),(4,false),(10,false)],[(11,false),(3,false),(6,true),(7,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  (.node 160843 ([(0,false),(5,false),(7,true),(2,false),(11,false),(10,false)],[(1,false),(6,true),(4,false),(3,false),(8,true),(9,true)])
                    .empty
                    .empty))
                (.node 160943 ([(4,false),(11,true),(2,true),(7,true),(0,true),(9,true)],[(1,false),(8,false),(5,false),(6,true),(3,true),(10,false)])
                  (.node 160903 ([(0,false),(5,false),(7,false),(2,false),(11,false),(10,false)],[(1,false),(6,true),(3,true),(4,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  (.node 161118 ([(0,true),(1,true),(2,true),(7,true),(4,false),(10,false)],[(11,false),(3,false),(6,false),(5,false),(8,true),(9,true)])
                    .empty
                    .empty)))
              (.node 162328 ([(3,false),(2,false),(1,false),(0,false),(5,false),(10,false)],[(11,false),(4,false),(6,true),(7,true),(8,true),(9,true)])
                (.node 162118 ([(3,false),(2,false),(1,false),(0,false),(5,false),(10,false)],[(11,false),(4,false),(6,true),(7,true),(8,true),(9,true)])
                  (.node 161838 ([(0,true),(7,false),(2,false),(11,false),(4,true),(9,true)],[(1,false),(8,true),(5,true),(6,true),(3,true),(10,false)])
                    .empty
                    .empty)
                  (.node 162153 ([(2,false),(1,false),(7,true),(8,true),(5,false),(10,false)],[(11,false),(4,false),(3,false),(6,true),(0,false),(9,true)])
                    .empty
                    .empty))
                (.node 162673 ([(0,false),(7,false),(3,false),(2,false),(11,false),(10,false)],[(1,false),(6,true),(4,true),(5,true),(8,true),(9,true)])
                  (.node 162363 ([(2,false),(1,false),(0,false),(7,true),(4,true),(10,false)],[(11,false),(5,true),(6,false),(3,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 164263 ([(0,false),(11,true),(2,false),(7,false),(4,false),(9,true)],[(3,true),(8,false),(1,false),(6,true),(5,true),(10,false)])
              (.node 163708 ([(3,false),(2,false),(7,true),(8,true),(0,false),(10,false)],[(11,false),(5,false),(4,false),(6,true),(1,false),(9,true)])
                (.node 162918 ([(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(11,false),(5,true),(6,true),(7,true),(8,true),(9,true)])
                  (.node 162883 ([(0,false),(5,false),(11,true),(2,true),(3,true),(9,true)],[(1,false),(6,true),(7,true),(8,true),(4,true),(10,false)])
                    .empty
                    .empty)
                  (.node 163673 ([(4,false),(3,false),(2,false),(1,false),(0,false),(10,false)],[(11,false),(5,false),(6,true),(7,true),(8,true),(9,true)])
                    .empty
                    .empty))
                (.node 163918 ([(3,false),(2,false),(1,false),(7,true),(5,true),(10,false)],[(11,false),(0,true),(6,false),(4,true),(8,true),(9,true)])
                  (.node 163883 ([(4,false),(3,false),(2,false),(1,false),(0,false),(10,false)],[(11,false),(5,false),(6,true),(7,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  (.node 164228 ([(1,false),(7,false),(4,false),(3,false),(11,false),(10,false)],[(2,false),(6,true),(5,true),(0,true),(8,true),(9,true)])
                    .empty
                    .empty)))
              (.node 164788 ([(3,false),(2,false),(7,true),(5,true),(0,true),(10,false)],[(11,false),(1,true),(6,false),(4,true),(8,true),(9,true)])
                (.node 164473 ([(0,false),(11,true),(2,false),(7,false),(4,true),(9,true)],[(3,true),(6,false),(1,true),(8,true),(5,true),(10,false)])
                  (.node 164438 ([(1,false),(0,false),(11,true),(3,true),(4,true),(9,true)],[(2,false),(6,true),(7,true),(8,true),(5,true),(10,false)])
                    .empty
                    .empty)
                  (.node 164753 ([(4,false),(7,false),(2,true),(11,false),(0,false),(9,true)],[(3,true),(8,true),(5,false),(6,true),(1,false),(10,false)])
                    .empty
                    .empty))
                (.node 165648 ([(0,true),(11,true),(2,false),(7,true),(4,false),(9,true)],[(3,true),(8,false),(5,true),(6,true),(1,false),(10,false)])
                  (.node 165473 ([(4,false),(3,false),(2,false),(7,true),(0,true),(10,false)],[(11,false),(1,true),(6,false),(5,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  .empty)))))))
    (.node 201544 ([(3,false),(9,true),(5,true),(7,false),(1,false),(11,false)],[(0,false),(8,true),(2,false),(6,false),(4,true),(10,true)])
      (.node 182323 ([(0,false),(5,false),(4,false),(3,false),(2,false),(10,false)],[(11,false),(1,false),(6,true),(7,true),(8,true),(9,true)])
        (.node 173033 ([(4,false),(3,false),(2,false),(7,true),(0,true),(10,false)],[(11,false),(1,true),(6,false),(5,true),(8,true),(9,true)])
          (.node 170268 ([(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(11,false),(5,true),(6,true),(7,true),(8,true),(9,true)])
            (.node 170008 ([(3,false),(2,false),(1,false),(0,false),(5,false),(10,false)],[(11,false),(4,false),(6,true),(7,true),(8,true),(9,true)])
              (.node 165818 ([(2,true),(3,true),(4,true),(5,true),(0,true),(10,false)],[(11,false),(1,true),(6,true),(7,true),(8,true),(9,true)])
                (.node 165748 ([(3,false),(2,false),(8,true),(5,true),(0,true),(10,false)],[(11,false),(1,true),(7,false),(6,false),(4,true),(9,true)])
                  (.node 165698 ([(1,false),(11,true),(3,true),(7,true),(5,false),(9,true)],[(2,false),(6,true),(4,true),(8,false),(0,true),(10,false)])
                    .empty
                    .empty)
                  (.node 165768 ([(0,true),(11,true),(2,false),(7,false),(4,true),(9,true)],[(3,true),(6,false),(5,false),(8,false),(1,false),(10,false)])
                    .empty
                    .empty))
                (.node 169838 ([(2,true),(3,true),(7,true),(0,false),(5,false),(10,false)],[(11,false),(4,false),(6,false),(1,false),(8,true),(9,true)])
                  (.node 165828 ([(0,true),(11,true),(2,false),(7,true),(4,true),(9,true)],[(3,true),(8,true),(5,true),(6,true),(1,false),(10,false)])
                    .empty
                    .empty)
                  (.node 169873 ([(0,false),(8,false),(7,false),(3,false),(11,false),(10,false)],[(2,false),(1,false),(6,true),(4,true),(5,true),(9,true)])
                    .empty
                    .empty)))
              (.node 170138 ([(1,false),(0,false),(7,true),(3,false),(11,false),(10,false)],[(2,false),(6,true),(5,false),(4,false),(8,true),(9,true)])
                (.node 170068 ([(3,false),(2,false),(1,false),(0,false),(5,false),(10,false)],[(11,false),(4,false),(6,true),(7,true),(8,true),(9,true)])
                  (.node 170018 ([(1,false),(0,false),(7,false),(3,false),(11,false),(10,false)],[(2,false),(6,true),(4,true),(5,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  (.node 170088 ([(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(11,false),(5,true),(6,true),(7,true),(8,true),(9,true)])
                    .empty
                    .empty))
                (.node 170233 ([(0,false),(7,false),(4,true),(11,true),(2,false),(9,true)],[(3,true),(6,false),(1,true),(8,false),(5,false),(10,false)])
                  (.node 170148 ([(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(11,false),(5,true),(6,true),(7,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 171703 ([(0,false),(11,true),(4,true),(7,false),(2,false),(9,true)],[(3,false),(6,false),(1,true),(8,false),(5,true),(10,false)])
              (.node 171573 ([(2,false),(1,false),(7,false),(4,false),(11,false),(10,false)],[(3,false),(6,true),(5,true),(0,true),(8,true),(9,true)])
                (.node 171428 ([(1,false),(8,false),(7,false),(4,false),(11,false),(10,false)],[(3,false),(2,false),(6,true),(5,true),(0,true),(9,true)])
                  (.node 171393 ([(3,true),(4,true),(7,true),(1,false),(0,false),(10,false)],[(11,false),(5,false),(6,false),(2,false),(8,true),(9,true)])
                    .empty
                    .empty)
                  (.node 171563 ([(4,false),(3,false),(2,false),(1,false),(0,false),(10,false)],[(11,false),(5,false),(6,true),(7,true),(8,true),(9,true)])
                    .empty
                    .empty))
                (.node 171643 ([(0,false),(11,true),(4,true),(7,true),(2,false),(9,true)],[(3,false),(8,true),(1,false),(6,true),(5,true),(10,false)])
                  (.node 171623 ([(4,false),(3,false),(2,false),(1,false),(0,false),(10,false)],[(11,false),(5,false),(6,true),(7,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  (.node 171693 ([(2,false),(1,false),(7,true),(4,false),(11,false),(10,false)],[(3,false),(6,true),(0,false),(5,false),(8,true),(9,true)])
                    .empty
                    .empty)))
              (.node 172508 ([(1,false),(11,true),(3,false),(7,false),(5,true),(9,true)],[(4,true),(6,false),(2,true),(8,true),(0,true),(10,false)])
                (.node 171823 ([(0,false),(11,true),(4,true),(7,true),(2,true),(9,true)],[(3,false),(8,false),(1,false),(6,true),(5,true),(10,false)])
                  (.node 171788 ([(1,false),(7,false),(5,true),(11,true),(3,false),(9,true)],[(4,true),(6,false),(2,true),(8,false),(0,false),(10,false)])
                    .empty
                    .empty)
                  (.node 172473 ([(2,false),(1,false),(11,true),(4,true),(5,true),(9,true)],[(3,false),(6,true),(7,true),(8,true),(0,true),(10,false)])
                    .empty
                    .empty))
                (.node 172998 ([(0,true),(11,true),(3,false),(7,true),(8,true),(9,true)],[(4,true),(5,true),(6,true),(2,false),(1,false),(10,false)])
                  (.node 172823 ([(4,false),(3,false),(7,true),(8,true),(1,false),(10,false)],[(11,false),(0,false),(5,false),(6,true),(2,false),(9,true)])
                    .empty
                    .empty)
                  .empty))))
          (.node 180723 ([(2,false),(8,false),(7,false),(5,false),(11,false),(10,false)],[(4,false),(3,false),(6,true),(0,true),(1,true),(9,true)])
            (.node 173853 ([(3,true),(4,true),(5,true),(0,true),(1,true),(10,false)],[(11,false),(2,true),(6,true),(7,true),(8,true),(9,true)])
              (.node 173723 ([(4,false),(11,false),(2,true),(7,true),(0,false),(9,true)],[(3,false),(6,false),(5,true),(8,false),(1,true),(10,false)])
                (.node 173523 ([(2,false),(7,false),(0,true),(11,true),(4,true),(9,true)],[(3,false),(6,true),(5,false),(8,false),(1,false),(10,false)])
                  (.node 173208 ([(0,true),(11,true),(4,true),(7,false),(2,true),(9,true)],[(3,false),(8,false),(5,true),(6,true),(1,false),(10,false)])
                    .empty
                    .empty)
                  (.node 173558 ([(1,false),(11,true),(3,false),(7,false),(5,false),(9,true)],[(4,true),(8,false),(2,false),(6,true),(0,true),(10,false)])
                    .empty
                    .empty))
                (.node 173783 ([(4,false),(3,false),(8,true),(0,true),(1,true),(10,false)],[(11,false),(2,true),(7,false),(6,false),(5,true),(9,true)])
                  (.node 173733 ([(2,false),(11,true),(4,true),(7,true),(0,false),(9,true)],[(3,false),(6,true),(5,true),(8,false),(1,true),(10,false)])
                    .empty
                    .empty)
                  (.node 173803 ([(0,false),(5,false),(4,false),(3,false),(2,false),(10,false)],[(11,false),(1,false),(6,true),(7,true),(8,true),(9,true)])
                    .empty
                    .empty)))
              (.node 174763 ([(0,false),(5,false),(4,false),(3,false),(2,false),(10,false)],[(11,false),(1,false),(6,true),(7,true),(8,true),(9,true)])
                (.node 173903 ([(4,false),(3,false),(7,true),(0,true),(1,true),(10,false)],[(11,false),(2,true),(6,false),(5,true),(8,true),(9,true)])
                  (.node 173863 ([(0,false),(5,false),(4,false),(3,false),(2,false),(10,false)],[(11,false),(1,false),(6,true),(7,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  (.node 174078 ([(0,true),(8,false),(7,false),(3,true),(11,false),(10,false)],[(4,true),(5,true),(6,true),(2,false),(1,false),(9,true)])
                    .empty
                    .empty))
                (.node 180688 ([(4,true),(5,true),(7,true),(2,false),(1,false),(10,false)],[(11,false),(0,false),(6,false),(3,false),(8,true),(9,true)])
                  (.node 174798 ([(0,true),(7,false),(2,false),(11,true),(4,true),(9,true)],[(3,false),(6,false),(5,false),(8,false),(1,true),(10,false)])
                    .empty
                    .empty)
                  .empty)))
            (.node 181118 ([(1,false),(11,true),(5,true),(7,true),(3,true),(9,true)],[(4,false),(8,false),(2,false),(6,true),(0,true),(10,false)])
              (.node 180888 ([(0,true),(11,true),(4,false),(7,true),(2,true),(9,true)],[(5,true),(6,true),(3,false),(8,false),(1,false),(10,false)])
                (.node 180818 ([(1,false),(11,true),(5,true),(7,false),(3,false),(9,true)],[(4,false),(6,false),(2,true),(8,false),(0,true),(10,false)])
                  (.node 180808 ([(3,false),(2,false),(7,true),(5,false),(11,false),(10,false)],[(4,false),(6,true),(1,false),(0,false),(8,true),(9,true)])
                    .empty
                    .empty)
                  (.node 180868 ([(3,false),(2,false),(7,false),(5,false),(11,false),(10,false)],[(4,false),(6,true),(0,true),(1,true),(8,true),(9,true)])
                    .empty
                    .empty))
                (.node 180948 ([(5,false),(4,false),(3,false),(2,false),(1,false),(10,false)],[(11,false),(0,false),(6,true),(7,true),(8,true),(9,true)])
                  (.node 180938 ([(1,false),(11,true),(5,true),(7,true),(3,false),(9,true)],[(4,false),(8,true),(2,false),(6,true),(0,true),(10,false)])
                    .empty
                    .empty)
                  (.node 181083 ([(2,false),(7,false),(0,true),(11,true),(4,false),(9,true)],[(5,true),(6,false),(3,true),(8,false),(1,false),(10,false)])
                    .empty
                    .empty)))
              (.node 181803 ([(2,false),(11,true),(4,false),(7,false),(0,true),(9,true)],[(5,true),(6,false),(3,true),(8,true),(1,true),(10,false)])
                (.node 181593 ([(2,false),(11,true),(4,false),(7,false),(0,false),(9,true)],[(5,true),(8,false),(3,false),(6,true),(1,true),(10,false)])
                  (.node 181558 ([(3,false),(7,false),(0,false),(5,false),(11,false),(10,false)],[(4,false),(6,true),(1,true),(2,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  (.node 181768 ([(3,false),(2,false),(11,true),(5,true),(0,true),(9,true)],[(4,false),(6,true),(7,true),(8,true),(1,true),(10,false)])
                    .empty
                    .empty))
                (.node 182148 ([(0,true),(1,true),(11,true),(4,false),(3,false),(9,true)],[(5,true),(6,true),(7,true),(8,true),(2,false),(10,false)])
                  (.node 182113 ([(0,false),(5,false),(4,false),(3,false),(2,false),(10,false)],[(11,false),(1,false),(6,true),(7,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  .empty)))))
        (.node 192129 ([(2,false),(1,false),(9,true),(4,true),(5,true),(11,false)],[(0,true),(8,false),(7,false),(6,false),(3,true),(10,true)])
          (.node 190149 ([(2,false),(1,false),(8,true),(4,true),(5,true),(11,false)],[(0,true),(7,false),(6,false),(3,true),(9,true),(10,true)])
            (.node 183098 ([(1,false),(0,false),(5,false),(4,false),(3,false),(10,false)],[(11,false),(2,false),(6,true),(7,true),(8,true),(9,true)])
              (.node 182968 ([(4,true),(5,true),(0,true),(1,true),(2,true),(10,false)],[(11,false),(3,true),(6,true),(7,true),(8,true),(9,true)])
                (.node 182798 ([(1,false),(0,false),(5,false),(4,false),(3,false),(10,false)],[(11,false),(2,false),(6,true),(7,true),(8,true),(9,true)])
                  (.node 182358 ([(0,true),(7,false),(2,false),(11,true),(4,false),(9,true)],[(5,true),(6,true),(3,true),(8,false),(1,true),(10,false)])
                    .empty
                    .empty)
                  (.node 182833 ([(0,false),(5,false),(4,false),(7,true),(2,true),(10,false)],[(11,false),(3,true),(6,false),(1,true),(8,true),(9,true)])
                    .empty
                    .empty))
                (.node 183028 ([(3,false),(11,true),(5,true),(7,true),(1,false),(9,true)],[(4,false),(6,true),(0,true),(8,false),(2,true),(10,false)])
                  (.node 182978 ([(1,false),(0,false),(5,false),(4,false),(3,false),(10,false)],[(11,false),(2,false),(6,true),(7,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  (.node 183048 ([(0,true),(1,true),(7,false),(4,true),(11,false),(10,false)],[(5,true),(6,true),(3,false),(2,false),(8,true),(9,true)])
                    .empty
                    .empty)))
              (.node 190019 ([(4,false),(3,false),(2,false),(1,false),(0,false),(11,false)],[(5,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 183193 ([(0,false),(7,false),(4,true),(11,false),(2,false),(9,true)],[(5,true),(8,true),(1,false),(6,true),(3,false),(10,false)])
                  (.node 183108 ([(0,true),(1,true),(7,true),(4,true),(11,false),(10,false)],[(5,true),(6,true),(2,true),(3,true),(8,true),(9,true)])
                    .empty
                    .empty)
                  (.node 183228 ([(5,false),(4,false),(7,true),(1,true),(2,true),(10,false)],[(11,false),(3,true),(6,false),(0,true),(8,true),(9,true)])
                    .empty
                    .empty))
                (.node 190139 ([(4,false),(3,false),(2,false),(1,false),(0,false),(11,false)],[(5,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 190054 ([(3,false),(2,false),(1,false),(7,true),(5,true),(11,false)],[(0,true),(6,false),(4,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 190924 ([(3,false),(2,false),(7,true),(8,true),(0,false),(11,false)],[(5,false),(4,false),(6,true),(1,false),(9,true),(10,true)])
              (.node 190279 ([(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(0,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 190219 ([(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(0,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 190199 ([(4,false),(3,false),(2,false),(1,false),(0,false),(11,false)],[(5,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 190269 ([(2,false),(9,false),(4,true),(7,false),(0,false),(11,false)],[(5,false),(8,true),(3,false),(6,true),(1,true),(10,true)])
                    .empty
                    .empty))
                (.node 190449 ([(2,false),(1,false),(7,true),(4,true),(5,true),(11,false)],[(0,true),(6,false),(3,true),(8,true),(9,true),(10,true)])
                  (.node 190414 ([(3,false),(7,false),(1,true),(9,false),(5,true),(11,false)],[(0,true),(6,false),(4,true),(8,false),(2,false),(10,true)])
                    .empty
                    .empty)
                  (.node 190889 ([(4,false),(3,false),(2,false),(1,false),(0,false),(11,false)],[(5,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)))
              (.node 191479 ([(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(0,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 191134 ([(3,false),(2,false),(1,false),(7,true),(5,true),(11,false)],[(0,true),(6,false),(4,true),(8,true),(9,true),(10,true)])
                  (.node 191099 ([(4,false),(3,false),(2,false),(1,false),(0,false),(11,false)],[(5,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 191444 ([(2,true),(3,true),(4,true),(7,true),(0,false),(11,false)],[(5,false),(6,false),(1,false),(8,true),(9,true),(10,true)])
                    .empty
                    .empty))
                (.node 191689 ([(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(0,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 191654 ([(1,false),(7,false),(3,false),(9,false),(5,true),(11,false)],[(0,true),(8,true),(4,false),(6,false),(2,true),(10,true)])
                    .empty
                    .empty)
                  .empty))))
          (.node 199394 ([(2,true),(3,true),(4,true),(5,true),(0,true),(11,false)],[(1,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
            (.node 192524 ([(1,false),(8,true),(3,true),(4,true),(5,true),(11,false)],[(0,true),(7,false),(6,false),(2,true),(9,true),(10,true)])
              (.node 192359 ([(4,false),(3,false),(2,false),(1,false),(0,false),(11,false)],[(5,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 192299 ([(4,false),(3,false),(2,false),(1,false),(0,false),(11,false)],[(5,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 192164 ([(1,false),(9,true),(3,false),(7,false),(5,true),(11,false)],[(0,true),(8,false),(2,false),(6,true),(4,false),(10,true)])
                    .empty
                    .empty)
                  (.node 192309 ([(3,true),(9,false),(1,false),(7,false),(5,true),(11,false)],[(0,true),(8,true),(2,true),(6,true),(4,false),(10,true)])
                    .empty
                    .empty))
                (.node 192429 ([(2,false),(9,true),(4,true),(7,false),(0,false),(11,false)],[(5,false),(8,true),(1,false),(6,false),(3,true),(10,true)])
                  (.node 192379 ([(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(0,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 192439 ([(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(0,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)))
              (.node 199169 ([(4,false),(3,false),(2,false),(7,true),(0,true),(11,false)],[(1,true),(6,false),(5,true),(8,true),(9,true),(10,true)])
                (.node 198449 ([(4,false),(7,false),(2,true),(9,false),(0,true),(11,false)],[(1,true),(6,false),(5,true),(8,false),(3,false),(10,true)])
                  (.node 192559 ([(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(0,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 198484 ([(3,false),(2,false),(7,true),(5,true),(0,true),(11,false)],[(1,true),(6,false),(4,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty))
                (.node 199384 ([(3,false),(9,false),(5,true),(7,false),(1,false),(11,false)],[(0,false),(8,true),(4,false),(6,true),(2,true),(10,true)])
                  (.node 199344 ([(5,false),(4,false),(3,false),(2,false),(1,false),(11,false)],[(0,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 200214 ([(5,false),(4,false),(3,false),(2,false),(1,false),(11,false)],[(0,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
              (.node 199524 ([(5,false),(4,false),(3,false),(2,false),(1,false),(11,false)],[(0,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 199464 ([(5,false),(4,false),(3,false),(2,false),(1,false),(11,false)],[(0,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 199444 ([(3,false),(2,false),(8,true),(5,true),(0,true),(11,false)],[(1,true),(7,false),(6,false),(4,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 199514 ([(2,true),(3,true),(4,true),(5,true),(0,true),(11,false)],[(1,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty))
                (.node 199724 ([(2,true),(3,true),(4,true),(5,true),(0,true),(11,false)],[(1,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 199689 ([(2,false),(7,false),(4,false),(9,false),(0,true),(11,false)],[(1,true),(8,true),(5,false),(6,false),(3,true),(10,true)])
                    .empty
                    .empty)
                  (.node 200039 ([(4,false),(3,false),(7,true),(8,true),(1,false),(11,false)],[(0,false),(5,false),(6,true),(2,false),(9,true),(10,true)])
                    .empty
                    .empty)))
              (.node 200774 ([(2,true),(3,true),(4,true),(5,true),(0,true),(11,false)],[(1,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 200424 ([(5,false),(4,false),(3,false),(2,false),(1,false),(11,false)],[(0,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 200249 ([(4,false),(3,false),(2,false),(7,true),(0,true),(11,false)],[(1,true),(6,false),(5,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 200739 ([(3,true),(4,true),(5,true),(7,true),(1,false),(11,false)],[(0,false),(6,false),(2,false),(8,true),(9,true),(10,true)])
                    .empty
                    .empty))
                (.node 201459 ([(2,false),(9,true),(4,false),(7,false),(0,true),(11,false)],[(1,true),(8,false),(3,false),(6,true),(5,false),(10,true)])
                  (.node 201424 ([(3,false),(2,false),(9,true),(5,true),(0,true),(11,false)],[(1,true),(8,false),(7,false),(6,false),(4,true),(10,true)])
                    .empty
                    .empty)
                  .empty))))))
      (.node 216794 ([(1,false),(0,false),(5,false),(4,false),(3,false),(11,false)],[(2,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
        (.node 208984 ([(3,false),(7,false),(5,false),(9,false),(1,true),(11,false)],[(2,true),(8,true),(0,false),(6,false),(4,true),(10,true)])
          (.node 203239 ([(0,false),(5,false),(4,false),(3,false),(2,false),(11,false)],[(1,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
            (.node 202979 ([(4,false),(3,false),(9,true),(0,true),(1,true),(11,false)],[(2,true),(8,false),(7,false),(6,false),(5,true),(10,true)])
              (.node 201674 ([(2,true),(3,true),(4,true),(5,true),(0,true),(11,false)],[(1,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 201604 ([(4,true),(9,false),(2,false),(7,false),(0,true),(11,false)],[(1,true),(8,true),(3,true),(6,true),(5,false),(10,true)])
                  (.node 201554 ([(2,true),(3,true),(4,true),(5,true),(0,true),(11,false)],[(1,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 201624 ([(5,false),(4,false),(3,false),(2,false),(1,false),(11,false)],[(0,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty))
                (.node 201819 ([(2,false),(8,true),(4,true),(5,true),(0,true),(11,false)],[(1,true),(7,false),(6,false),(3,true),(9,true),(10,true)])
                  (.node 201684 ([(5,false),(4,false),(3,false),(2,false),(1,false),(11,false)],[(0,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 201854 ([(2,true),(3,true),(4,true),(5,true),(0,true),(11,false)],[(1,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)))
              (.node 203159 ([(5,true),(9,false),(3,false),(7,false),(1,true),(11,false)],[(2,true),(8,true),(4,true),(6,true),(0,false),(10,true)])
                (.node 203099 ([(4,false),(9,true),(0,true),(7,false),(2,false),(11,false)],[(1,false),(8,true),(3,false),(6,false),(5,true),(10,true)])
                  (.node 203014 ([(3,false),(9,true),(5,false),(7,false),(1,true),(11,false)],[(2,true),(8,false),(4,false),(6,true),(0,false),(10,true)])
                    .empty
                    .empty)
                  (.node 203109 ([(3,true),(4,true),(5,true),(0,true),(1,true),(11,false)],[(2,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty))
                (.node 203229 ([(3,true),(4,true),(5,true),(0,true),(1,true),(11,false)],[(2,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 203179 ([(0,false),(5,false),(4,false),(3,false),(2,false),(11,false)],[(1,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 207559 ([(0,false),(5,false),(4,false),(3,false),(2,false),(11,false)],[(1,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
              (.node 207429 ([(3,true),(4,true),(5,true),(0,true),(1,true),(11,false)],[(2,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 203409 ([(3,true),(4,true),(5,true),(0,true),(1,true),(11,false)],[(2,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 203374 ([(3,false),(8,true),(5,true),(0,true),(1,true),(11,false)],[(2,true),(7,false),(6,false),(4,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 207419 ([(4,false),(9,false),(0,true),(7,false),(2,false),(11,false)],[(1,false),(8,true),(5,false),(6,true),(3,true),(10,true)])
                    .empty
                    .empty))
                (.node 207499 ([(0,false),(5,false),(4,false),(3,false),(2,false),(11,false)],[(1,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 207479 ([(4,false),(3,false),(8,true),(0,true),(1,true),(11,false)],[(2,true),(7,false),(6,false),(5,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 207549 ([(3,true),(4,true),(5,true),(0,true),(1,true),(11,false)],[(2,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)))
              (.node 208494 ([(0,true),(8,true),(4,false),(3,false),(2,false),(11,false)],[(1,false),(7,false),(6,false),(5,false),(9,true),(10,true)])
                (.node 207774 ([(0,true),(9,true),(4,true),(7,false),(2,false),(11,false)],[(1,false),(8,false),(5,true),(6,true),(3,true),(10,true)])
                  (.node 207599 ([(4,false),(3,false),(7,true),(0,true),(1,true),(11,false)],[(2,true),(6,false),(5,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 208459 ([(0,false),(5,false),(4,false),(3,false),(2,false),(11,false)],[(1,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty))
                (.node 208809 ([(3,true),(4,true),(5,true),(0,true),(1,true),(11,false)],[(2,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 208774 ([(4,true),(5,true),(0,true),(7,true),(2,false),(11,false)],[(1,false),(6,false),(3,false),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  .empty))))
          (.node 211444 ([(4,true),(5,true),(0,true),(1,true),(2,true),(11,false)],[(3,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
            (.node 210539 ([(4,false),(7,false),(0,false),(9,false),(2,true),(11,false)],[(3,true),(8,true),(1,false),(6,false),(5,true),(10,true)])
              (.node 209539 ([(0,false),(5,false),(4,false),(3,false),(2,false),(11,false)],[(1,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 209329 ([(0,false),(5,false),(4,false),(3,false),(2,false),(11,false)],[(1,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 209019 ([(3,true),(4,true),(5,true),(0,true),(1,true),(11,false)],[(2,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 209364 ([(0,true),(7,false),(4,true),(9,false),(2,false),(11,false)],[(1,false),(8,true),(3,true),(6,false),(5,false),(10,true)])
                    .empty
                    .empty))
                (.node 210329 ([(5,true),(0,true),(1,true),(7,true),(3,false),(11,false)],[(2,false),(6,false),(4,false),(8,true),(9,true),(10,true)])
                  (.node 209574 ([(5,false),(4,false),(3,false),(7,true),(1,true),(11,false)],[(2,true),(6,false),(0,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 210364 ([(4,true),(5,true),(0,true),(1,true),(2,true),(11,false)],[(3,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)))
              (.node 211094 ([(1,false),(0,false),(5,false),(4,false),(3,false),(11,false)],[(2,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 210884 ([(1,false),(0,false),(5,false),(4,false),(3,false),(11,false)],[(2,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 210574 ([(4,true),(5,true),(0,true),(1,true),(2,true),(11,false)],[(3,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 210919 ([(0,false),(5,false),(7,true),(8,true),(3,false),(11,false)],[(2,false),(1,false),(6,true),(4,false),(9,true),(10,true)])
                    .empty
                    .empty))
                (.node 211409 ([(4,false),(8,true),(0,true),(1,true),(2,true),(11,false)],[(3,true),(7,false),(6,false),(5,true),(9,true),(10,true)])
                  (.node 211129 ([(0,false),(5,false),(4,false),(7,true),(2,true),(11,false)],[(3,true),(6,false),(1,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 212484 ([(0,true),(9,false),(4,false),(7,false),(2,true),(11,false)],[(3,true),(8,true),(5,true),(6,true),(1,false),(10,true)])
              (.node 212354 ([(1,false),(0,false),(5,false),(4,false),(3,false),(11,false)],[(2,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 212304 ([(0,true),(1,true),(7,true),(4,false),(3,false),(11,false)],[(2,false),(6,false),(5,false),(8,true),(9,true),(10,true)])
                  (.node 212129 ([(4,false),(9,true),(0,false),(7,false),(2,true),(11,false)],[(3,true),(8,false),(5,false),(6,true),(1,false),(10,true)])
                    .empty
                    .empty)
                  (.node 212344 ([(4,true),(5,true),(0,true),(1,true),(2,true),(11,false)],[(3,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty))
                (.node 212424 ([(0,true),(1,true),(8,true),(4,false),(3,false),(11,false)],[(2,false),(7,false),(6,false),(5,false),(9,true),(10,true)])
                  (.node 212404 ([(4,true),(5,true),(0,true),(1,true),(2,true),(11,false)],[(3,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 212474 ([(1,false),(0,false),(5,false),(4,false),(3,false),(11,false)],[(2,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)))
              (.node 216674 ([(1,false),(0,false),(5,false),(4,false),(3,false),(11,false)],[(2,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 216529 ([(0,false),(5,false),(4,false),(7,true),(2,true),(11,false)],[(3,true),(6,false),(1,true),(8,true),(9,true),(10,true)])
                  (.node 216494 ([(1,false),(0,false),(5,false),(4,false),(3,false),(11,false)],[(2,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 216664 ([(4,true),(5,true),(0,true),(1,true),(2,true),(11,false)],[(3,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty))
                (.node 216744 ([(5,false),(9,false),(1,true),(7,false),(3,false),(11,false)],[(2,false),(8,true),(0,false),(6,true),(4,true),(10,true)])
                  (.node 216724 ([(4,true),(5,true),(0,true),(1,true),(2,true),(11,false)],[(3,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  .empty)))))
        (.node 221419 ([(0,false),(5,false),(9,true),(2,true),(3,true),(11,false)],[(4,true),(8,false),(7,false),(6,false),(1,true),(10,true)])
          (.node 219164 ([(1,false),(0,false),(5,false),(7,true),(3,true),(11,false)],[(4,true),(6,false),(2,true),(8,true),(9,true),(10,true)])
            (.node 218279 ([(5,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(4,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
              (.node 218049 ([(2,false),(1,false),(0,false),(5,false),(4,false),(11,false)],[(3,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 216889 ([(0,false),(7,false),(4,true),(9,false),(2,true),(11,false)],[(3,true),(6,false),(1,true),(8,false),(5,false),(10,true)])
                  (.node 216804 ([(0,true),(9,true),(4,false),(7,false),(2,true),(11,false)],[(3,true),(8,true),(1,true),(6,false),(5,false),(10,true)])
                    .empty
                    .empty)
                  (.node 216924 ([(0,true),(1,true),(9,true),(4,false),(3,false),(11,false)],[(2,false),(8,false),(7,false),(6,false),(5,false),(10,true)])
                    .empty
                    .empty))
                (.node 218219 ([(5,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(4,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 218084 ([(1,false),(0,false),(5,false),(7,true),(3,true),(11,false)],[(4,true),(6,false),(2,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 218229 ([(2,false),(1,false),(0,false),(5,false),(4,false),(11,false)],[(3,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)))
              (.node 218444 ([(1,false),(7,false),(5,true),(9,false),(3,true),(11,false)],[(4,true),(6,false),(2,true),(8,false),(0,false),(10,true)])
                (.node 218349 ([(2,false),(1,false),(0,false),(5,false),(4,false),(11,false)],[(3,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 218299 ([(0,false),(9,false),(2,true),(7,false),(4,false),(11,false)],[(3,false),(8,true),(1,false),(6,true),(5,true),(10,true)])
                    .empty
                    .empty)
                  (.node 218359 ([(0,false),(5,false),(8,true),(2,true),(3,true),(11,false)],[(4,true),(7,false),(6,false),(1,true),(9,true),(10,true)])
                    .empty
                    .empty))
                (.node 219129 ([(2,false),(1,false),(0,false),(5,false),(4,false),(11,false)],[(3,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 218479 ([(0,false),(5,false),(7,true),(2,true),(3,true),(11,false)],[(4,true),(6,false),(1,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 220389 ([(2,false),(1,false),(0,false),(5,false),(4,false),(11,false)],[(3,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
              (.node 219864 ([(0,true),(1,true),(7,true),(8,true),(3,true),(11,false)],[(4,true),(5,true),(6,true),(2,true),(9,true),(10,true)])
                (.node 219654 ([(0,true),(1,true),(2,true),(7,true),(4,false),(11,false)],[(3,false),(6,false),(5,false),(8,true),(9,true),(10,true)])
                  (.node 219479 ([(5,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(4,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 219689 ([(5,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(4,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty))
                (.node 220214 ([(1,false),(0,false),(7,true),(8,true),(4,false),(11,false)],[(3,false),(2,false),(6,true),(5,false),(9,true),(10,true)])
                  (.node 220179 ([(2,false),(1,false),(0,false),(5,false),(4,false),(11,false)],[(3,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 220379 ([(5,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(4,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)))
              (.node 220519 ([(1,true),(9,false),(5,false),(7,false),(3,true),(11,false)],[(4,true),(8,true),(0,true),(6,true),(2,false),(10,true)])
                (.node 220459 ([(0,false),(9,true),(2,true),(7,false),(4,false),(11,false)],[(3,false),(8,true),(5,false),(6,false),(1,true),(10,true)])
                  (.node 220439 ([(5,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(4,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 220509 ([(2,false),(1,false),(0,false),(5,false),(4,false),(11,false)],[(3,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty))
                (.node 220734 ([(0,true),(1,true),(2,true),(7,true),(4,false),(11,false)],[(3,false),(6,false),(5,false),(8,true),(9,true),(10,true)])
                  (.node 220559 ([(5,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(4,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  .empty))))
          (.node 228459 ([(2,false),(1,false),(0,false),(7,true),(4,true),(11,false)],[(5,true),(6,false),(3,true),(8,true),(9,true),(10,true)])
            (.node 227594 ([(1,false),(9,false),(3,true),(7,false),(5,false),(11,false)],[(4,false),(8,true),(2,false),(6,true),(0,true),(10,true)])
              (.node 227464 ([(3,false),(2,false),(1,false),(0,false),(5,false),(11,false)],[(4,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 227344 ([(3,false),(2,false),(1,false),(0,false),(5,false),(11,false)],[(4,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 221454 ([(0,true),(7,false),(2,false),(9,false),(4,false),(11,false)],[(3,false),(6,false),(5,false),(8,false),(1,true),(10,true)])
                    .empty
                    .empty)
                  (.node 227379 ([(2,false),(1,false),(0,false),(7,true),(4,true),(11,false)],[(5,true),(6,false),(3,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty))
                (.node 227524 ([(3,false),(2,false),(1,false),(0,false),(5,false),(11,false)],[(4,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 227474 ([(1,false),(0,false),(8,true),(3,true),(4,true),(11,false)],[(5,true),(7,false),(6,false),(2,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 227544 ([(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(5,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)))
              (.node 228214 ([(3,false),(2,false),(1,false),(0,false),(5,false),(11,false)],[(4,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 227739 ([(2,false),(7,false),(0,true),(9,false),(4,true),(11,false)],[(5,true),(6,false),(3,true),(8,false),(1,false),(10,true)])
                  (.node 227604 ([(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(5,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 227774 ([(1,false),(0,false),(7,true),(3,true),(4,true),(11,false)],[(5,true),(6,false),(2,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty))
                (.node 228424 ([(3,false),(2,false),(1,false),(0,false),(5,false),(11,false)],[(4,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 228249 ([(2,false),(1,false),(7,true),(8,true),(5,false),(11,false)],[(4,false),(3,false),(6,true),(0,false),(9,true),(10,true)])
                    .empty
                    .empty)
                  .empty)))
            (.node 229634 ([(2,true),(9,false),(0,false),(7,false),(4,true),(11,false)],[(5,true),(8,true),(1,true),(6,true),(3,false),(10,true)])
              (.node 229014 ([(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(5,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 228804 ([(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(5,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 228769 ([(1,true),(2,true),(3,true),(7,true),(5,false),(11,false)],[(4,false),(6,false),(0,false),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 228979 ([(0,false),(7,false),(2,false),(9,false),(4,true),(11,false)],[(5,true),(8,true),(3,false),(6,false),(1,true),(10,true)])
                    .empty
                    .empty))
                (.node 229489 ([(0,false),(9,true),(2,false),(7,false),(4,true),(11,false)],[(5,true),(8,false),(1,false),(6,true),(3,false),(10,true)])
                  (.node 229454 ([(1,false),(0,false),(9,true),(3,true),(4,true),(11,false)],[(5,true),(8,false),(7,false),(6,false),(2,true),(10,true)])
                    .empty
                    .empty)
                  (.node 229624 ([(3,false),(2,false),(1,false),(0,false),(5,false),(11,false)],[(4,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)))
              (.node 229764 ([(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(5,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 229704 ([(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(5,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 229684 ([(3,false),(2,false),(1,false),(0,false),(5,false),(11,false)],[(4,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  (.node 229754 ([(1,false),(9,true),(3,true),(7,false),(5,false),(11,false)],[(4,false),(8,true),(0,false),(6,false),(2,true),(10,true)])
                    .empty
                    .empty))
                (.node 229884 ([(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(5,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 229849 ([(0,false),(8,true),(2,true),(3,true),(4,true),(11,false)],[(5,true),(7,false),(6,false),(1,true),(9,true),(10,true)])
                    .empty
                    .empty)
                  .empty)))))))))

def choice (p : Fin 6 → Fin 6) (d : Fin 5) : Steps × Steps := (CertificateTree.lookup certificates (code p d)).getD ([],[])

def fromList (l : List (Fin 6)) (i : Fin 6) : Fin 6 := l.getD i.val 0

lemma finite_certificate_orders : ∀ l ∈ ([0,1,2,3,4,5] : List (Fin 6)).permutations,
    ¬adjacent (fromList l 0) (fromList l 1) → ¬adjacent (fromList l 4) (fromList l 5) →
    ∀ g : Fin 5, GoodGap (fromList l) g → Valid (fromList l) g (choice (fromList l) g) := by
  decide

lemma finite_certificate (p : Fin 6 → Fin 6)
    (hp : (List.ofFn p).Nodup) (hf : ¬adjacent (p 0) (p 1)) (hl : ¬adjacent (p 4) (p 5))
    (d : Fin 5) (hg : GoodGap p d) : Valid p d (choice p d) := by
  have he : fromList (List.ofFn p)=p := by
    funext i
    simp [fromList,List.getD_eq_getElem,List.length_ofFn,i.isLt]
  have hmem : List.ofFn p ∈ ([0,1,2,3,4,5] : List (Fin 6)).permutations := by
    apply List.mem_permutations.mpr
    apply (List.perm_ext_iff_of_nodup hp (by decide)).mpr
    intro x
    constructor
    · intro _; fin_cases x <;> decide
    · intro _
      exact List.mem_ofFn.mpr ((Finite.injective_iff_surjective.mp (List.nodup_ofFn.mp hp)) x)
  have hh := finite_certificate_orders (List.ofFn p) hmem
  rw [he] at hh
  exact hh hf hl d hg

lemma exists_routes (p : Fin 6 → Fin 6) (hp : Function.Injective p)
    (hfirst : ¬adjacent (p 0) (p 1)) (hlast : ¬adjacent (p 4) (p 5)) (d : Fin 5) (hg : GoodGap p d) :
    ∃ X : Route (pieceSource p d) (pieceTarget p d) (p 0).castSucc 6,
    ∃ Y : Route (pieceSource p d) (pieceTarget p d) (p 5).castSucc 6,
      X.support.Nodup ∧ Y.support.Nodup ∧ X.pieces.Disjoint Y.pieces ∧
        ∀ e, e ∈ X.pieces ∨ e ∈ Y.pieces := by
  obtain ⟨ha,hb,hnX,hnY,hd,hc⟩ := finite_certificate p (List.nodup_ofFn.mpr hp) hfirst hlast d hg
  obtain ⟨X,hXs,hXp⟩ := Route.of_compatible (choice p d).1 ha
  obtain ⟨Y,hYs,hYp⟩ := Route.of_compatible (choice p d).2 hb
  exact ⟨X,Y,hXs.symm ▸ hnX,hYs.symm ▸ hnY,by simpa only [hXp,hYp] using hd,
    by simpa only [hXp,hYp] using hc⟩

end Erdos583HexagonExcursionRoutesDevelopment
