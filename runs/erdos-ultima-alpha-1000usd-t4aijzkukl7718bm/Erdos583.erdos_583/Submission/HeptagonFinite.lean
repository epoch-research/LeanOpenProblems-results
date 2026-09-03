import Submission.Work

/-! Kernel-checked routes for a seven-cycle missing one path vertex. -/
namespace Erdos583HeptagonRoutesDevelopment
open SimpleGraph Erdos583Work Erdos583Work.PieceRoutes
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option Elab.async false

def next (i : Fin 7) : Fin 7 := ⟨(i.val+1)%7,Nat.mod_lt _ (by decide)⟩

def pieceSource (p : Fin 6 → Fin 6) (e : Fin 12) : Fin 7 :=
  if h : e.val < 7 then ⟨e.val,h⟩ else (p ⟨e.val-7,by omega⟩).castSucc

def pieceTarget (p : Fin 6 → Fin 6) (e : Fin 12) : Fin 7 :=
  if e.val < 7 then ⟨(e.val+1)%7,Nat.mod_lt _ (by decide)⟩ else (p ⟨e.val-6,by omega⟩).castSucc

def adjacent (a b : Fin 6) : Prop := a.val+1=b.val ∨ b.val+1=a.val
instance (a b : Fin 6) : Decidable (adjacent a b) := inferInstanceAs (Decidable (_ ∨ _))

abbrev Steps := List (Fin 12 × Bool)

def Valid (p : Fin 6 → Fin 6) (v : Steps × Steps) : Prop :=
  Route.compatible (s := pieceSource p) (t := pieceTarget p) (p 0).castSucc 6 v.1=true ∧
  Route.compatible (s := pieceSource p) (t := pieceTarget p) (p 5).castSucc 6 v.2=true ∧
  ((p 0).castSucc :: v.1.map (fun ed ↦ target (pieceSource p) (pieceTarget p) ed.1 ed.2)).Nodup ∧
  ((p 5).castSucc :: v.2.map (fun ed ↦ target (pieceSource p) (pieceTarget p) ed.1 ed.2)).Nodup ∧
  (∀ e : Fin 12, e ∈ v.1.map Prod.fst → e ∉ v.2.map Prod.fst) ∧
  ∀ e : Fin 12, e ∈ v.1.map Prod.fst ∨ e ∈ v.2.map Prod.fst

instance (p : Fin 6 → Fin 6) (v : Steps × Steps) : Decidable (Valid p v) := by
  unfold Valid
  infer_instance

def code (p : Fin 6 → Fin 6) : ℕ :=
  (p 0).val+6*(p 1).val+36*(p 2).val+216*(p 3).val+1296*(p 4).val+7776*(p 5).val

def Exceptional (p : Fin 6 → Fin 6) : Prop :=
  code p=30710 ∨ code p=24830 ∨ code p=21825 ∨ code p=15945
instance (p : Fin 6 → Fin 6) : Decidable (Exceptional p) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

inductive CertificateTree where
  | empty : CertificateTree
  | node (key : ℕ) (value : Steps × Steps) (left right : CertificateTree) : CertificateTree

def CertificateTree.lookup (t : CertificateTree) (key : ℕ) : Option (Steps × Steps) :=
  match t with
  | .empty => none
  | .node k v l r => if key=k then some v else if key<k then l.lookup key else r.lookup key

def certificates : CertificateTree := (.node 23705 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
  (.node 13100 ([(1,false),(0,false),(10,true),(3,false),(8,false),(5,true)],[(11,false),(4,true),(7,false),(2,true),(9,true),(6,false)])
    (.node 5815 ([(1,true),(2,true),(8,true),(4,false),(11,true),(6,false)],[(0,true),(7,true),(3,true),(10,false),(9,false),(5,true)])
      (.node 4475 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
        (.node 3645 ([(2,false),(10,false),(4,true),(8,false),(0,false),(6,false)],[(11,false),(1,false),(7,false),(3,true),(9,false),(5,true)])
          (.node 3445 ([(7,true),(4,true),(9,true),(2,false),(11,true),(6,false)],[(0,true),(1,true),(10,false),(3,true),(8,true),(5,true)])
            (.node 3395 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
              (.node 2985 ([(7,true),(4,false),(9,true),(1,true),(11,true),(6,false)],[(0,true),(10,true),(2,true),(3,true),(8,false),(5,true)])
                (.node 2975 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 3430 ([(4,true),(9,true),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(3,true),(7,true),(8,true),(5,true)])
                (.node 3415 ([(7,true),(4,false),(3,false),(2,false),(11,true),(6,false)],[(0,true),(1,true),(10,false),(9,false),(8,false),(5,true)])
                  .empty
                  .empty)
                .empty))
            (.node 3575 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
              (.node 3525 ([(2,false),(10,false),(4,true),(8,true),(0,false),(6,false)],[(11,false),(1,false),(9,true),(3,false),(7,true),(5,true)])
                (.node 3515 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 3595 ([(7,true),(4,false),(3,false),(2,false),(11,true),(6,false)],[(0,true),(1,true),(10,false),(9,false),(8,false),(5,true)])
                .empty
                .empty)))
          (.node 3835 ([(7,true),(3,true),(4,true),(10,true),(11,true),(6,false)],[(0,true),(1,true),(2,true),(8,true),(9,true),(5,true)])
            (.node 3805 ([(7,true),(3,false),(9,true),(10,true),(11,true),(6,false)],[(0,true),(1,true),(2,true),(8,false),(4,true),(5,true)])
              (.node 3790 ([(3,false),(9,true),(10,true),(1,false),(0,false),(6,false)],[(11,false),(2,true),(8,false),(7,false),(4,true),(5,true)])
                (.node 3655 ([(7,true),(8,true),(4,false),(10,true),(11,true),(6,false)],[(0,true),(1,true),(2,true),(3,true),(9,false),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 3825 ([(2,false),(10,false),(4,false),(8,false),(0,false),(6,false)],[(11,false),(1,false),(7,false),(3,true),(9,true),(5,true)])
                .empty
                .empty))
            (.node 4300 ([(3,false),(2,false),(8,true),(9,true),(0,false),(6,false)],[(11,false),(10,false),(1,true),(7,false),(4,true),(5,true)])
              (.node 4280 ([(7,true),(4,false),(3,false),(10,false),(0,false),(6,false)],[(11,false),(2,false),(1,false),(9,false),(8,false),(5,true)])
                (.node 4265 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 4310 ([(1,false),(9,false),(4,false),(3,false),(11,true),(6,false)],[(0,true),(10,true),(2,false),(7,true),(8,true),(5,true)])
                .empty
                .empty))))
        (.node 5065 ([(1,true),(8,false),(4,true),(10,true),(11,true),(6,false)],[(0,true),(7,true),(3,false),(2,false),(9,true),(5,true)])
          (.node 4835 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
            (.node 4525 ([(7,true),(4,true),(9,true),(2,true),(11,true),(6,false)],[(0,true),(1,true),(10,true),(3,true),(8,true),(5,true)])
              (.node 4510 ([(3,false),(2,false),(9,false),(8,false),(0,false),(6,false)],[(11,false),(10,false),(1,false),(7,false),(4,true),(5,true)])
                (.node 4495 ([(7,true),(4,false),(9,true),(2,true),(11,true),(6,false)],[(0,true),(1,true),(10,true),(3,true),(8,false),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 4820 ([(1,false),(8,false),(4,false),(3,false),(11,true),(6,false)],[(0,true),(9,true),(10,true),(2,false),(7,true),(5,true)])
                (.node 4805 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                  .empty
                  .empty)
                .empty))
            (.node 5030 ([(1,false),(9,true),(4,false),(3,false),(11,true),(6,false)],[(0,true),(8,false),(7,false),(2,true),(10,false),(5,true)])
              (.node 5020 ([(4,true),(9,false),(1,true),(2,true),(11,true),(6,false)],[(0,true),(8,false),(7,false),(3,false),(10,false),(5,true)])
                (.node 4855 ([(7,true),(8,true),(9,true),(3,false),(11,true),(6,false)],[(0,true),(1,true),(2,true),(10,false),(4,true),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 5050 ([(3,false),(10,false),(9,false),(1,false),(0,false),(6,false)],[(11,false),(2,false),(8,false),(7,false),(4,true),(5,true)])
                .empty
                .empty)))
          (.node 5675 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
            (.node 5525 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
              (.node 5505 ([(3,true),(4,true),(8,true),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(2,true),(7,true),(5,true)])
                (.node 5495 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 5540 ([(1,false),(9,false),(8,false),(4,false),(11,true),(6,false)],[(0,true),(10,true),(3,false),(2,false),(7,true),(5,true)])
                .empty
                .empty))
            (.node 5755 ([(7,true),(8,true),(2,false),(10,true),(11,true),(6,false)],[(0,true),(1,true),(9,false),(3,true),(4,true),(5,true)])
              (.node 5735 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                (.node 5685 ([(2,false),(1,false),(8,false),(4,false),(11,true),(6,false)],[(0,true),(9,true),(10,true),(3,false),(7,true),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 5805 ([(2,false),(1,false),(8,true),(4,false),(11,true),(6,false)],[(0,true),(7,false),(3,true),(10,false),(9,false),(5,true)])
                .empty
                .empty)))))
      (.node 11860 ([(3,false),(10,false),(0,true),(1,true),(8,true),(5,true)],[(11,false),(2,false),(7,false),(4,true),(9,true),(6,false)])
        (.node 7065 ([(2,false),(1,false),(8,true),(4,true),(11,true),(6,false)],[(0,true),(7,false),(3,true),(9,true),(10,true),(5,true)])
          (.node 6355 ([(7,true),(2,false),(9,true),(4,false),(11,true),(6,false)],[(0,true),(1,true),(8,false),(3,true),(10,false),(5,true)])
            (.node 5915 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
              (.node 5900 ([(2,true),(3,true),(4,true),(8,true),(0,false),(6,false)],[(11,false),(10,false),(9,false),(1,true),(7,true),(5,true)])
                (.node 5885 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 6345 ([(7,true),(1,true),(9,true),(4,false),(11,true),(6,false)],[(0,true),(8,true),(2,true),(3,true),(10,false),(5,true)])
                (.node 5935 ([(7,true),(8,true),(2,true),(3,true),(11,true),(6,false)],[(0,true),(1,true),(9,true),(10,true),(4,true),(5,true)])
                  .empty
                  .empty)
                .empty))
            (.node 7030 ([(7,true),(8,true),(2,false),(10,true),(11,true),(6,false)],[(0,true),(1,true),(9,false),(3,true),(4,true),(5,true)])
              (.node 6830 ([(7,true),(3,false),(9,true),(10,true),(11,true),(6,false)],[(0,true),(1,true),(2,true),(8,false),(4,true),(5,true)])
                (.node 6820 ([(3,false),(2,false),(1,false),(10,true),(11,true),(6,false)],[(0,true),(9,false),(8,false),(7,false),(4,true),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 7045 ([(1,true),(2,true),(3,true),(4,true),(11,true),(6,false)],[(0,true),(7,true),(8,true),(9,true),(10,true),(5,true)])
                .empty
                .empty)))
          (.node 7225 ([(1,true),(2,true),(3,true),(4,true),(11,true),(6,false)],[(0,true),(7,true),(8,true),(9,true),(10,true),(5,true)])
            (.node 7190 ([(1,false),(8,false),(3,false),(10,true),(11,true),(6,false)],[(0,true),(9,true),(2,false),(7,true),(4,true),(5,true)])
              (.node 7180 ([(7,true),(1,false),(9,true),(10,true),(11,true),(6,false)],[(0,true),(8,false),(2,true),(3,true),(4,true),(5,true)])
                (.node 7075 ([(1,true),(2,true),(3,true),(4,true),(11,true),(6,false)],[(0,true),(7,true),(8,true),(9,true),(10,true),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 7210 ([(7,true),(1,true),(2,true),(10,true),(11,true),(6,false)],[(0,true),(8,true),(9,true),(3,true),(4,true),(5,true)])
                .empty
                .empty))
            (.node 11825 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
              (.node 7435 ([(1,true),(2,true),(3,true),(4,true),(11,true),(6,false)],[(0,true),(7,true),(8,true),(9,true),(10,true),(5,true)])
                (.node 7425 ([(7,true),(1,true),(9,true),(4,true),(11,true),(6,false)],[(0,true),(8,true),(2,true),(3,true),(10,true),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 11840 ([(1,false),(0,false),(10,true),(3,true),(4,true),(5,true)],[(11,false),(2,false),(7,true),(8,true),(9,true),(6,false)])
                .empty
                .empty))))
        (.node 12720 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
          (.node 12545 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
            (.node 12270 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
              (.node 12245 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                (.node 11870 ([(1,false),(0,false),(10,true),(3,true),(4,true),(5,true)],[(11,false),(2,false),(7,true),(8,true),(9,true),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 12300 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                (.node 12280 ([(3,false),(2,false),(1,false),(0,false),(8,true),(5,true)],[(11,false),(10,false),(9,false),(4,false),(7,true),(6,false)])
                  .empty
                  .empty)
                .empty))
            (.node 12630 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
              (.node 12605 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                (.node 12560 ([(1,false),(11,false),(3,true),(4,true),(8,true),(6,false)],[(0,false),(9,true),(10,true),(2,false),(7,true),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 12710 ([(1,false),(11,false),(3,true),(4,true),(8,false),(6,false)],[(0,false),(7,false),(2,true),(10,false),(9,false),(5,true)])
                .empty
                .empty)))
          (.node 12890 ([(1,false),(11,false),(10,false),(4,false),(8,false),(6,false)],[(0,false),(7,false),(2,true),(3,true),(9,true),(5,true)])
            (.node 12820 ([(3,false),(10,false),(9,false),(1,false),(0,false),(6,false)],[(11,false),(2,false),(8,false),(7,false),(4,true),(5,true)])
              (.node 12770 ([(1,false),(0,false),(8,false),(3,false),(10,false),(5,true)],[(11,false),(2,false),(7,true),(4,true),(9,false),(6,false)])
                (.node 12760 ([(3,false),(2,false),(1,false),(0,false),(9,true),(5,true)],[(11,false),(10,false),(4,false),(7,true),(8,true),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 12840 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                .empty
                .empty))
            (.node 13065 ([(2,false),(1,false),(0,false),(10,true),(4,true),(5,true)],[(11,false),(3,false),(7,true),(8,true),(9,true),(6,false)])
              (.node 13055 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                (.node 12900 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 13085 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                .empty
                .empty))))))
    (.node 16605 ([(2,false),(1,false),(8,true),(4,false),(10,true),(6,false)],[(11,false),(0,true),(7,false),(3,true),(9,false),(5,true)])
      (.node 14835 ([(2,false),(1,false),(0,false),(8,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(3,false),(7,true),(6,false)])
        (.node 13790 ([(1,false),(11,false),(3,false),(9,false),(8,false),(6,false)],[(0,false),(7,false),(2,true),(10,true),(4,true),(5,true)])
          (.node 13590 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
            (.node 13505 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
              (.node 13425 ([(2,false),(1,false),(11,false),(4,true),(8,true),(6,false)],[(0,false),(9,true),(10,true),(3,false),(7,true),(5,true)])
                (.node 13415 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 13575 ([(2,false),(1,false),(11,false),(4,true),(8,false),(6,false)],[(0,false),(7,false),(3,true),(10,false),(9,false),(5,true)])
                (.node 13530 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                  .empty
                  .empty)
                .empty))
            (.node 13685 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
              (.node 13640 ([(1,false),(0,false),(9,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(2,false),(7,true),(8,true),(6,false)])
                (.node 13625 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 13710 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                .empty
                .empty)))
          (.node 14160 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
            (.node 14130 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
              (.node 14115 ([(2,false),(8,false),(0,true),(11,false),(4,true),(5,true)],[(1,true),(9,true),(10,true),(3,false),(7,true),(6,false)])
                (.node 13800 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 14150 ([(1,false),(0,false),(8,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(2,false),(7,true),(6,false)])
                .empty
                .empty))
            (.node 14800 ([(3,false),(2,false),(10,true),(11,true),(0,false),(6,false)],[(1,true),(9,false),(8,false),(7,false),(4,true),(5,true)])
              (.node 14390 ([(2,true),(3,true),(4,true),(11,true),(0,false),(6,false)],[(1,true),(7,true),(8,true),(9,true),(10,true),(5,true)])
                (.node 14380 ([(3,false),(2,false),(1,false),(0,false),(10,true),(5,true)],[(11,false),(4,false),(7,true),(8,true),(9,true),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 14820 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                .empty
                .empty))))
        (.node 15240 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
          (.node 15050 ([(1,false),(0,false),(8,true),(3,false),(10,true),(5,true)],[(11,false),(4,false),(9,true),(2,false),(7,true),(6,false)])
            (.node 14930 ([(1,false),(0,false),(8,false),(3,false),(10,true),(5,true)],[(11,false),(4,false),(7,false),(2,true),(9,false),(6,false)])
              (.node 14920 ([(3,false),(2,false),(8,true),(0,true),(11,false),(5,true)],[(1,true),(7,false),(4,true),(10,false),(9,false),(6,false)])
                (.node 14850 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 15000 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                (.node 14980 ([(3,false),(2,false),(8,false),(0,true),(11,false),(5,true)],[(1,true),(9,true),(10,true),(4,false),(7,true),(6,false)])
                  .empty
                  .empty)
                .empty))
            (.node 15210 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
              (.node 15195 ([(2,false),(9,true),(4,true),(11,true),(0,false),(6,false)],[(1,true),(8,false),(7,false),(3,true),(10,true),(5,true)])
                (.node 15060 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 15230 ([(1,false),(0,false),(8,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(2,false),(7,true),(6,false)])
                .empty
                .empty)))
          (.node 16405 ([(0,false),(11,true),(2,true),(3,true),(4,true),(5,true)],[(1,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
            (.node 16375 ([(0,false),(11,true),(2,true),(3,true),(4,true),(5,true)],[(1,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
              (.node 16355 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                (.node 15935 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 16390 ([(3,false),(2,false),(11,false),(0,true),(8,true),(5,true)],[(1,false),(7,false),(4,true),(9,true),(10,true),(6,false)])
                .empty
                .empty))
            (.node 16535 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
              (.node 16485 ([(2,false),(1,false),(8,false),(4,false),(10,true),(6,false)],[(11,false),(0,true),(9,true),(3,false),(7,true),(5,true)])
                (.node 16475 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 16555 ([(0,false),(11,true),(2,true),(3,true),(4,true),(5,true)],[(1,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
                .empty
                .empty)))))
      (.node 21450 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
        (.node 20935 ([(0,false),(10,true),(11,true),(2,true),(8,true),(5,true)],[(1,false),(7,true),(3,true),(4,true),(9,true),(6,false)])
          (.node 20795 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
            (.node 16765 ([(0,false),(11,true),(2,true),(3,true),(4,true),(5,true)],[(1,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
              (.node 16750 ([(3,false),(8,false),(1,true),(11,false),(10,false),(5,true)],[(2,true),(9,true),(4,false),(7,true),(0,false),(6,false)])
                (.node 16615 ([(0,false),(11,true),(2,true),(3,true),(4,true),(5,true)],[(1,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 16795 ([(0,false),(11,true),(2,true),(3,true),(4,true),(5,true)],[(1,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
                (.node 16785 ([(2,false),(1,false),(8,true),(4,true),(10,true),(6,false)],[(11,false),(0,true),(7,false),(3,true),(9,true),(5,true)])
                  .empty
                  .empty)
                .empty))
            (.node 20875 ([(0,false),(9,false),(2,false),(11,false),(4,true),(5,true)],[(1,false),(7,true),(8,true),(3,true),(10,false),(6,false)])
              (.node 20855 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                (.node 20805 ([(2,false),(1,false),(0,false),(10,true),(4,true),(5,true)],[(11,false),(3,false),(7,true),(8,true),(9,true),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 20925 ([(2,false),(1,false),(0,false),(10,true),(4,true),(5,true)],[(11,false),(3,false),(7,true),(8,true),(9,true),(6,false)])
                .empty
                .empty)))
          (.node 21135 ([(2,false),(1,false),(10,true),(4,true),(8,false),(6,false)],[(11,false),(3,false),(7,true),(0,true),(9,false),(5,true)])
            (.node 21065 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
              (.node 20985 ([(3,true),(11,true),(1,false),(0,false),(8,false),(5,true)],[(2,true),(7,true),(4,false),(10,false),(9,false),(6,false)])
                (.node 20975 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 21090 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                .empty
                .empty))
            (.node 21415 ([(1,true),(2,true),(3,true),(4,true),(8,true),(6,false)],[(11,false),(10,false),(9,false),(0,true),(7,true),(5,true)])
              (.node 21395 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                (.node 21150 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 21425 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                .empty
                .empty))))
        (.node 22395 ([(2,false),(1,false),(0,false),(8,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(3,false),(7,true),(6,false)])
          (.node 22165 ([(1,true),(11,false),(4,false),(3,false),(9,true),(6,false)],[(2,true),(8,false),(7,false),(0,false),(10,true),(5,true)])
            (.node 21870 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
              (.node 21855 ([(2,false),(11,false),(4,true),(9,false),(0,false),(6,false)],[(1,false),(8,false),(7,false),(3,true),(10,false),(5,true)])
                (.node 21835 ([(0,false),(8,false),(2,false),(11,false),(4,true),(5,true)],[(1,false),(7,true),(3,true),(10,false),(9,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 22150 ([(3,false),(2,false),(1,false),(0,false),(10,true),(5,true)],[(11,false),(4,false),(7,true),(8,true),(9,true),(6,false)])
                .empty
                .empty))
            (.node 22360 ([(3,false),(2,false),(11,false),(10,false),(0,false),(6,false)],[(1,false),(9,false),(8,false),(7,false),(4,true),(5,true)])
              (.node 22195 ([(0,false),(9,false),(3,false),(2,false),(11,false),(5,true)],[(1,false),(7,true),(8,true),(4,true),(10,false),(6,false)])
                (.node 22185 ([(2,false),(1,false),(8,true),(9,true),(10,true),(5,true)],[(11,false),(4,false),(3,false),(7,true),(0,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 22380 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                .empty
                .empty)))
          (.node 22740 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
            (.node 22705 ([(0,false),(8,false),(3,false),(2,false),(11,false),(5,true)],[(1,false),(7,true),(4,true),(10,false),(9,false),(6,false)])
              (.node 22690 ([(3,false),(9,false),(0,true),(1,true),(11,false),(5,true)],[(2,true),(10,true),(4,false),(7,true),(8,true),(6,false)])
                (.node 22410 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 22720 ([(3,false),(10,true),(11,true),(1,false),(0,false),(6,false)],[(2,true),(9,false),(8,false),(7,false),(4,true),(5,true)])
                .empty
                .empty))
            (.node 22935 ([(2,false),(11,false),(4,false),(9,false),(0,false),(6,false)],[(1,false),(8,false),(7,false),(3,true),(10,true),(5,true)])
              (.node 22915 ([(1,true),(2,true),(8,true),(9,true),(4,true),(5,true)],[(11,false),(10,false),(3,false),(7,false),(0,false),(6,false)])
                (.node 22905 ([(2,false),(1,false),(0,false),(9,true),(4,true),(5,true)],[(11,false),(10,false),(3,false),(7,true),(8,true),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 22950 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                .empty
                .empty)))))))
  (.node 33570 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
    (.node 30120 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
      (.node 25240 ([(3,false),(2,false),(1,false),(0,false),(8,true),(5,true)],[(11,false),(10,false),(9,false),(4,false),(7,true),(6,false)])
        (.node 24295 ([(0,false),(11,true),(3,true),(9,false),(8,false),(5,true)],[(2,false),(1,false),(7,true),(4,false),(10,true),(6,false)])
          (.node 23950 ([(3,false),(2,false),(9,false),(8,false),(0,false),(6,false)],[(11,false),(10,false),(1,false),(7,false),(4,true),(5,true)])
            (.node 23750 ([(1,false),(0,false),(11,true),(3,true),(4,true),(5,true)],[(2,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
              (.node 23740 ([(3,false),(2,false),(8,true),(9,true),(0,false),(6,false)],[(11,false),(10,false),(1,true),(7,false),(4,true),(5,true)])
                (.node 23720 ([(1,false),(0,false),(11,true),(3,true),(4,true),(5,true)],[(2,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 23935 ([(0,false),(11,true),(2,false),(9,false),(4,true),(5,true)],[(3,true),(8,false),(7,false),(1,true),(10,true),(6,false)])
                (.node 23915 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                  .empty
                  .empty)
                .empty))
            (.node 24260 ([(1,false),(0,false),(11,true),(3,true),(4,true),(5,true)],[(2,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
              (.node 24245 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                (.node 23965 ([(1,true),(9,false),(4,false),(3,false),(11,false),(6,false)],[(2,false),(10,true),(0,true),(7,true),(8,true),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 24275 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                .empty
                .empty)))
          (.node 24785 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
            (.node 24490 ([(3,false),(11,false),(0,true),(1,true),(9,true),(5,true)],[(2,false),(8,false),(7,false),(4,true),(10,true),(6,false)])
              (.node 24470 ([(1,false),(0,false),(11,true),(3,true),(4,true),(5,true)],[(2,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
                (.node 24460 ([(3,false),(2,false),(1,false),(9,true),(10,true),(6,false)],[(11,false),(0,true),(8,false),(7,false),(4,true),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 24505 ([(0,false),(11,true),(2,false),(8,false),(4,true),(5,true)],[(3,true),(7,false),(1,true),(9,true),(10,true),(6,false)])
                .empty
                .empty))
            (.node 25205 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
              (.node 24820 ([(4,true),(8,false),(2,true),(11,false),(0,false),(6,false)],[(3,true),(7,true),(1,false),(10,false),(9,false),(5,true)])
                (.node 24800 ([(2,true),(11,false),(0,false),(9,false),(4,true),(5,true)],[(3,true),(8,false),(7,false),(1,false),(10,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 25230 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                .empty
                .empty))))
        (.node 25800 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
          (.node 25670 ([(1,false),(11,true),(3,true),(4,true),(8,false),(6,false)],[(2,false),(7,true),(0,true),(10,false),(9,false),(5,true)])
            (.node 25520 ([(1,false),(11,true),(3,true),(9,false),(8,false),(5,true)],[(2,false),(7,true),(4,false),(10,true),(0,false),(6,false)])
              (.node 25505 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                (.node 25260 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 25590 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                (.node 25565 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                  .empty
                  .empty)
                .empty))
            (.node 25730 ([(1,false),(11,true),(3,true),(4,true),(9,false),(6,false)],[(2,false),(7,true),(8,true),(0,true),(10,false),(5,true)])
              (.node 25720 ([(3,false),(2,false),(1,false),(0,false),(9,true),(5,true)],[(11,false),(10,false),(4,false),(7,true),(8,true),(6,false)])
                (.node 25680 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 25780 ([(3,false),(2,false),(8,false),(0,true),(10,false),(5,true)],[(11,false),(1,true),(9,true),(4,false),(7,true),(6,false)])
                .empty
                .empty)))
          (.node 29890 ([(3,false),(2,false),(1,false),(0,false),(10,true),(5,true)],[(11,false),(4,false),(7,true),(8,true),(9,true),(6,false)])
            (.node 29860 ([(3,false),(2,false),(1,false),(0,false),(10,true),(5,true)],[(11,false),(4,false),(7,true),(8,true),(9,true),(6,false)])
              (.node 25860 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                (.node 25850 ([(2,true),(3,true),(4,true),(10,true),(0,false),(6,false)],[(11,false),(1,true),(7,true),(8,true),(9,true),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 29870 ([(2,true),(3,true),(8,true),(0,false),(10,true),(5,true)],[(11,false),(4,false),(7,false),(1,false),(9,true),(6,false)])
                .empty
                .empty))
            (.node 30050 ([(1,false),(0,false),(8,false),(3,false),(11,false),(5,true)],[(2,false),(7,true),(4,true),(10,false),(9,false),(6,false)])
              (.node 30040 ([(3,false),(2,false),(8,true),(0,true),(10,true),(5,true)],[(11,false),(4,false),(7,true),(1,false),(9,false),(6,false)])
                (.node 29905 ([(0,false),(9,false),(8,false),(3,false),(11,false),(5,true)],[(2,false),(1,false),(7,true),(4,true),(10,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 30100 ([(3,false),(11,false),(10,false),(1,true),(8,false),(6,false)],[(2,false),(9,true),(0,false),(7,false),(4,true),(5,true)])
                .empty
                .empty)))))
      (.node 31855 ([(0,false),(11,true),(3,false),(2,false),(8,false),(5,true)],[(4,true),(7,false),(1,true),(9,true),(10,true),(6,false)])
        (.node 31460 ([(1,false),(0,false),(11,true),(3,false),(8,false),(5,true)],[(4,true),(7,false),(2,true),(9,true),(10,true),(6,false)])
          (.node 30300 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
            (.node 30250 ([(3,false),(11,false),(10,false),(1,false),(0,false),(6,false)],[(2,false),(9,false),(8,false),(7,false),(4,true),(5,true)])
              (.node 30180 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                (.node 30170 ([(1,false),(10,true),(11,true),(3,true),(8,false),(6,false)],[(2,false),(7,true),(0,true),(9,false),(4,true),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 30280 ([(3,false),(11,false),(10,false),(1,false),(0,false),(6,false)],[(2,false),(9,false),(8,false),(7,false),(4,true),(5,true)])
                (.node 30265 ([(0,false),(8,false),(3,false),(2,false),(10,true),(5,true)],[(11,false),(4,false),(7,false),(1,true),(9,false),(6,false)])
                  .empty
                  .empty)
                .empty))
            (.node 31425 ([(2,false),(1,false),(0,false),(11,true),(4,true),(5,true)],[(3,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
              (.node 31415 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                (.node 30720 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 31445 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                .empty
                .empty)))
          (.node 31725 ([(2,false),(1,false),(0,false),(11,true),(4,true),(5,true)],[(3,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
            (.node 31655 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
              (.node 31605 ([(2,false),(1,false),(0,false),(11,true),(4,true),(5,true)],[(3,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
                (.node 31595 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 31675 ([(1,true),(2,true),(8,false),(4,false),(11,false),(6,false)],[(3,false),(9,true),(10,true),(0,true),(7,true),(5,true)])
                .empty
                .empty))
            (.node 31820 ([(1,false),(8,false),(4,false),(3,false),(10,true),(6,false)],[(11,false),(0,true),(9,true),(2,false),(7,true),(5,true)])
              (.node 31805 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                (.node 31735 ([(0,false),(11,true),(3,false),(2,false),(9,false),(5,true)],[(4,true),(8,false),(7,false),(1,true),(10,true),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 31835 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                .empty
                .empty))))
        (.node 32970 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
          (.node 32525 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
            (.node 32495 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
              (.node 32275 ([(1,true),(2,true),(3,true),(4,true),(10,true),(6,false)],[(11,false),(0,true),(7,true),(8,true),(9,true),(5,true)])
                (.node 32265 ([(2,false),(1,false),(0,false),(11,true),(4,true),(5,true)],[(3,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 32505 ([(2,false),(9,true),(0,true),(11,true),(4,true),(5,true)],[(3,false),(7,true),(8,true),(1,false),(10,false),(6,false)])
                .empty
                .empty))
            (.node 32865 ([(3,true),(11,false),(1,true),(9,false),(8,false),(5,true)],[(4,true),(7,false),(2,false),(10,true),(0,false),(6,false)])
              (.node 32855 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                (.node 32540 ([(2,true),(8,false),(4,false),(11,false),(0,false),(6,false)],[(3,false),(9,true),(10,true),(1,true),(7,true),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 32945 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                .empty
                .empty)))
          (.node 33125 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
            (.node 33065 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
              (.node 33030 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                (.node 33015 ([(2,false),(1,false),(11,true),(4,true),(8,false),(6,false)],[(3,false),(7,true),(0,true),(10,false),(9,false),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 33080 ([(1,false),(0,false),(9,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(2,false),(7,true),(8,true),(6,false)])
                .empty
                .empty))
            (.node 33240 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
              (.node 33230 ([(1,false),(10,false),(3,true),(4,true),(8,false),(6,false)],[(11,false),(0,false),(7,false),(2,true),(9,false),(5,true)])
                (.node 33150 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 33555 ([(2,false),(9,true),(4,false),(11,false),(0,false),(6,false)],[(3,false),(7,true),(8,true),(1,false),(10,false),(5,true)])
                .empty
                .empty))))))
    (.node 40850 ([(1,false),(0,false),(9,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(2,false),(7,true),(8,true),(6,false)])
      (.node 34815 ([(2,false),(11,true),(4,true),(9,false),(0,false),(6,false)],[(3,false),(7,true),(8,true),(1,true),(10,false),(5,true)])
        (.node 34025 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
          (.node 33835 ([(0,false),(9,false),(2,false),(11,true),(4,true),(5,true)],[(3,false),(8,false),(7,false),(1,true),(10,false),(6,false)])
            (.node 33755 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
              (.node 33600 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                (.node 33590 ([(1,false),(0,false),(8,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(2,false),(7,true),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 33815 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                (.node 33765 ([(3,true),(11,false),(10,false),(0,true),(8,false),(5,true)],[(4,true),(7,false),(2,false),(1,false),(9,true),(6,false)])
                  .empty
                  .empty)
                .empty))
            (.node 33935 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
              (.node 33895 ([(0,false),(10,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(1,false),(7,true),(8,true),(9,true),(6,false)])
                (.node 33885 ([(2,false),(11,true),(4,true),(8,false),(0,false),(6,false)],[(3,false),(7,true),(1,true),(10,false),(9,false),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 33945 ([(3,true),(11,false),(1,false),(0,false),(8,false),(5,true)],[(4,true),(7,false),(2,false),(10,false),(9,false),(6,false)])
                .empty
                .empty)))
          (.node 34375 ([(0,false),(9,true),(2,false),(11,true),(4,true),(5,true)],[(3,false),(10,true),(1,false),(7,true),(8,true),(6,false)])
            (.node 34110 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
              (.node 34095 ([(3,true),(11,false),(1,false),(0,false),(8,true),(5,true)],[(4,true),(9,true),(10,true),(2,true),(7,true),(6,false)])
                (.node 34050 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 34355 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                .empty
                .empty))
            (.node 34785 ([(3,true),(4,true),(10,true),(1,false),(0,false),(6,false)],[(11,false),(2,true),(7,true),(8,true),(9,true),(5,true)])
              (.node 34410 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                (.node 34385 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false)],[(11,false),(10,false),(9,false),(8,false),(7,false),(5,true)])
                  .empty
                  .empty)
                .empty)
              (.node 34795 ([(0,false),(8,false),(2,false),(11,true),(4,true),(5,true)],[(3,false),(7,false),(1,true),(10,false),(9,false),(6,false)])
                .empty
                .empty))))
        (.node 39625 ([(7,true),(8,true),(2,true),(10,true),(11,true),(5,true)],[(4,false),(3,false),(9,false),(1,false),(0,false),(6,false)])
          (.node 39465 ([(2,false),(9,false),(8,false),(0,false),(11,true),(5,true)],[(4,false),(3,false),(7,true),(1,true),(10,true),(6,false)])
            (.node 39230 ([(7,true),(3,false),(9,true),(0,false),(11,true),(5,true)],[(4,false),(8,true),(2,false),(1,false),(10,true),(6,false)])
              (.node 39220 ([(3,false),(2,false),(1,false),(0,false),(11,true),(5,true)],[(4,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
                (.node 34830 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 39445 ([(7,true),(3,false),(2,false),(10,true),(11,true),(5,true)],[(4,false),(8,true),(9,true),(1,false),(0,false),(6,false)])
                (.node 39430 ([(3,false),(2,false),(1,false),(0,false),(11,true),(5,true)],[(4,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
                  .empty
                  .empty)
                .empty))
            (.node 39590 ([(1,false),(8,false),(3,false),(10,true),(11,true),(5,true)],[(4,false),(7,false),(2,true),(9,false),(0,false),(6,false)])
              (.node 39580 ([(3,false),(2,false),(1,false),(0,false),(11,true),(5,true)],[(4,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
                (.node 39475 ([(7,true),(3,true),(9,true),(10,true),(11,true),(5,true)],[(4,false),(8,false),(2,false),(1,false),(0,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 39610 ([(3,false),(2,false),(1,false),(0,false),(11,true),(5,true)],[(4,false),(7,true),(8,true),(9,true),(10,true),(6,false)])
                .empty
                .empty)))
          (.node 40720 ([(7,true),(8,true),(2,false),(1,false),(11,true),(5,true)],[(4,false),(3,false),(9,true),(10,true),(0,false),(6,false)])
            (.node 40300 ([(7,true),(2,true),(9,true),(0,true),(11,true),(5,true)],[(4,false),(3,false),(8,false),(1,false),(10,false),(6,false)])
              (.node 39835 ([(1,true),(2,true),(3,true),(10,true),(11,true),(5,true)],[(4,false),(9,false),(8,false),(7,false),(0,false),(6,false)])
                (.node 39825 ([(7,true),(1,true),(9,true),(10,true),(11,true),(5,true)],[(4,false),(3,false),(2,false),(8,false),(0,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 40310 ([(7,true),(3,false),(9,true),(0,true),(11,true),(5,true)],[(4,false),(8,true),(2,false),(1,false),(10,false),(6,false)])
                .empty
                .empty))
            (.node 40770 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
              (.node 40755 ([(2,false),(1,false),(0,false),(8,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(3,false),(7,true),(6,false)])
                (.node 40740 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 40840 ([(3,false),(2,false),(8,true),(0,true),(11,true),(5,true)],[(4,false),(7,true),(1,false),(10,false),(9,false),(6,false)])
                .empty
                .empty)))))
      (.node 42345 ([(2,false),(1,false),(0,false),(9,true),(4,true),(5,true)],[(11,false),(10,false),(3,false),(7,true),(8,true),(6,false)])
        (.node 41625 ([(2,false),(10,false),(0,true),(8,true),(4,true),(5,true)],[(11,false),(1,false),(7,false),(3,true),(9,true),(6,false)])
          (.node 41130 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
            (.node 40970 ([(2,true),(3,true),(8,false),(0,true),(11,true),(5,true)],[(4,false),(9,true),(10,true),(1,true),(7,true),(6,false)])
              (.node 40920 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                (.node 40900 ([(7,true),(8,true),(2,true),(10,true),(11,true),(5,true)],[(4,false),(3,false),(9,false),(1,false),(0,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 41115 ([(2,false),(8,false),(0,true),(10,false),(4,true),(5,true)],[(11,false),(1,true),(9,true),(3,false),(7,true),(6,false)])
                (.node 40980 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                  .empty
                  .empty)
                .empty))
            (.node 41590 ([(3,false),(8,false),(0,false),(10,true),(11,true),(5,true)],[(4,false),(7,true),(1,true),(2,true),(9,true),(6,false)])
              (.node 41160 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                (.node 41150 ([(1,false),(0,false),(8,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(2,false),(7,true),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 41605 ([(0,false),(10,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(1,false),(7,true),(8,true),(9,true),(6,false)])
                .empty
                .empty)))
          (.node 41850 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
            (.node 41820 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
              (.node 41800 ([(7,true),(8,true),(9,true),(1,true),(11,true),(5,true)],[(4,false),(3,false),(2,false),(10,false),(0,false),(6,false)])
                (.node 41635 ([(0,false),(9,false),(3,false),(2,false),(11,true),(5,true)],[(4,false),(8,false),(7,false),(1,true),(10,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 41835 ([(2,false),(1,false),(0,false),(8,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(3,false),(7,true),(6,false)])
                .empty
                .empty))
            (.node 42160 ([(7,true),(0,true),(9,true),(2,false),(11,true),(5,true)],[(4,false),(3,false),(10,true),(1,false),(8,false),(6,false)])
              (.node 42145 ([(0,false),(8,false),(3,false),(2,false),(11,true),(5,true)],[(4,false),(7,false),(1,true),(10,false),(9,false),(6,false)])
                (.node 42130 ([(7,true),(0,false),(9,true),(2,false),(11,true),(5,true)],[(4,false),(3,false),(10,true),(1,false),(8,true),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 42180 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                .empty
                .empty))))
        (.node 43060 ([(7,true),(0,true),(1,true),(2,true),(11,true),(5,true)],[(4,false),(3,false),(10,false),(9,false),(8,false),(6,false)])
          (.node 42830 ([(1,false),(0,false),(10,true),(3,true),(4,true),(5,true)],[(11,false),(2,false),(7,true),(8,true),(9,true),(6,false)])
            (.node 42390 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
              (.node 42375 ([(7,true),(0,true),(1,true),(10,false),(4,true),(5,true)],[(11,false),(2,true),(3,true),(9,false),(8,false),(6,false)])
                (.node 42355 ([(0,false),(8,false),(2,false),(10,false),(4,true),(5,true)],[(11,false),(1,false),(7,true),(3,true),(9,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 42820 ([(7,true),(1,false),(0,false),(10,true),(11,true),(5,true)],[(4,false),(3,false),(2,false),(8,true),(9,true),(6,false)])
                .empty
                .empty))
            (.node 43000 ([(7,true),(8,true),(0,true),(10,true),(11,true),(5,true)],[(4,false),(3,false),(2,false),(1,false),(9,false),(6,false)])
              (.node 42865 ([(0,false),(9,false),(8,false),(3,false),(11,true),(5,true)],[(4,false),(7,false),(1,true),(2,true),(10,false),(6,false)])
                (.node 42850 ([(7,true),(1,true),(9,true),(10,true),(11,true),(5,true)],[(4,false),(3,false),(2,false),(8,false),(0,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 43010 ([(1,false),(0,false),(8,false),(3,false),(11,true),(5,true)],[(4,false),(7,false),(2,true),(10,false),(9,false),(6,false)])
                .empty
                .empty)))
          (.node 43225 ([(0,false),(9,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(1,false),(7,true),(8,true),(6,false)])
            (.node 43140 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
              (.node 43130 ([(1,false),(0,false),(8,true),(3,false),(11,true),(5,true)],[(4,false),(9,true),(10,true),(2,false),(7,true),(6,false)])
                (.node 43080 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 43210 ([(7,true),(0,false),(9,true),(2,true),(11,true),(5,true)],[(4,false),(3,false),(10,false),(1,false),(8,true),(6,false)])
                .empty
                .empty))
            (.node 43670 ([(7,true),(0,true),(9,true),(3,false),(11,true),(5,true)],[(4,false),(10,true),(2,false),(1,false),(8,false),(6,false)])
              (.node 43260 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                (.node 43240 ([(7,true),(0,true),(1,true),(2,true),(11,true),(5,true)],[(4,false),(3,false),(10,false),(9,false),(8,false),(6,false)])
                  .empty
                  .empty)
                .empty)
              (.node 43680 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true)],[(11,false),(10,false),(9,false),(8,false),(7,false),(6,false)])
                .empty
                .empty))))))))

def choice (p : Fin 6 → Fin 6) : Steps × Steps := (CertificateTree.lookup certificates (code p)).getD ([],[])

def fromList (l : List (Fin 6)) (i : Fin 6) : Fin 6 := l.getD i.val 0

lemma finite_certificate_orders : ∀ l ∈ ([0,1,2,3,4,5] : List (Fin 6)).permutations',
    ¬adjacent (fromList l 0) (fromList l 1) → ¬adjacent (fromList l 4) (fromList l 5) →
    ¬Exceptional (fromList l) → Valid (fromList l) (choice (fromList l)) := by
  decide

lemma finite_certificate (p : Fin 6 → Fin 6)
    (hp : (List.ofFn p).Nodup) (hf : ¬adjacent (p 0) (p 1)) (hl : ¬adjacent (p 4) (p 5))
    (hex : ¬Exceptional p) : Valid p (choice p) := by
  have he : fromList (List.ofFn p)=p := by
    funext i
    fin_cases i <;> rfl
  have hmem : List.ofFn p ∈ ([0,1,2,3,4,5] : List (Fin 6)).permutations' := by
    apply List.mem_permutations'.mpr
    apply (List.perm_ext_iff_of_nodup hp (by decide)).mpr
    intro x
    constructor
    · intro _; fin_cases x <;> decide
    · intro _
      exact List.mem_ofFn.mpr ((Finite.injective_iff_surjective.mp (List.nodup_ofFn.mp hp)) x)
  have hh := finite_certificate_orders (List.ofFn p) hmem
  rw [he] at hh
  exact hh hf hl hex

lemma exists_routes (p : Fin 6 → Fin 6) (hp : Function.Injective p)
    (hfirst : ¬adjacent (p 0) (p 1)) (hlast : ¬adjacent (p 4) (p 5)) (hex : ¬Exceptional p) :
    ∃ X : Route (pieceSource p) (pieceTarget p) (p 0).castSucc 6,
    ∃ Y : Route (pieceSource p) (pieceTarget p) (p 5).castSucc 6,
      X.support.Nodup ∧ Y.support.Nodup ∧ X.pieces.Disjoint Y.pieces ∧
        ∀ e, e ∈ X.pieces ∨ e ∈ Y.pieces := by
  obtain ⟨ha,hb,hnX,hnY,hd,hc⟩ := finite_certificate p (List.nodup_ofFn.mpr hp) hfirst hlast hex
  obtain ⟨X,hXs,hXp⟩ := Route.of_compatible (choice p).1 ha
  obtain ⟨Y,hYs,hYp⟩ := Route.of_compatible (choice p).2 hb
  exact ⟨X,Y,hXs.symm ▸ hnX,hYs.symm ▸ hnY,by simpa only [hXp,hYp] using hd,
    by simpa only [hXp,hYp] using hc⟩

end Erdos583HeptagonRoutesDevelopment
