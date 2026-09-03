import Submission.Work

namespace Erdos583Work
/- Kernel-checked routes for a seven-cycle missing one path vertex. -/
namespace HeptagonRoutes
open SimpleGraph PieceRoutes
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

end HeptagonRoutes

/- Expansion of checked seven-cycle / six-visit routes. -/
namespace HeptagonRoutes
open SimpleGraph PieceRoutes
set_option maxHeartbeats 1800000

lemma cycle_source (p : Fin 6 → Fin 6) (i : Fin 7) :
    pieceSource p (Fin.castAdd 5 i)=i := by simp [pieceSource,i.isLt]

lemma cycle_target (p : Fin 6 → Fin 6) (i : Fin 7) :
    pieceTarget p (Fin.castAdd 5 i)=next i := by simp [pieceTarget,next,i.isLt]

lemma path_source (p : Fin 6 → Fin 6) (i : Fin 5) :
    pieceSource p (Fin.natAdd 7 i)=(p i.castSucc).castSucc := by
  simp [pieceSource,Fin.natAdd,Nat.add_comm]
  rfl

lemma path_target (p : Fin 6 → Fin 6) (i : Fin 5) :
    pieceTarget p (Fin.natAdd 7 i)=(p i.succ).castSucc := by
  simp [pieceTarget,Fin.natAdd,Nat.add_comm]
  rfl

lemma expand_certificate {V : Type*} {G : SimpleGraph V}
    (p : Fin 6 → Fin 6) (hp : Function.Injective p)
    (hfirst : ¬adjacent (p 0) (p 1)) (hlast : ¬adjacent (p 4) (p 5)) (hex : ¬Exceptional p)
    (f : Fin 7 → V) (hf : Function.Injective f)
    (R : ∀ e : Fin 12, G.Walk (f (pieceSource p e)) (f (pieceTarget p e)))
    (hpath : ∀ e, (R e).IsPath)
    (hcore : ∀ e x, f x ∈ (R e).support → x=pieceSource p e ∨ x=pieceTarget p e)
    (hinter : ∀ e j, e ≠ j → ∀ x ∈ (R e).support, x ∈ (R j).support → ∃ a, x=f a)
    (hdis : ∀ e j, e ≠ j → Disjoint (R e).toSubgraph.edgeSet (R j).toSubgraph.edgeSet) :
    ∃ X : G.Walk (f (p 0).castSucc) (f 6), ∃ Y : G.Walk (f (p 5).castSucc) (f 6),
      X.IsPath ∧ Y.IsPath ∧ Disjoint X.toSubgraph.edgeSet Y.toSubgraph.edgeSet ∧
        X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=⋃ e, (R e).toSubgraph.edgeSet := by
  obtain ⟨X,Y,hX,hY,hd,hc⟩ := exists_routes p hp hfirst hlast hex
  exact ⟨X.expand f R,Y.expand f R,Route.expand_two_cover f R hf hpath hcore hinter hdis X Y hX hY hd hc⟩

end HeptagonRoutes

/- Shifted coordinates put a missing base vertex last on a seven-cycle. -/
namespace HeptagonCoordinates
open SimpleGraph PathIntervals
open HeptagonRoutes
open scoped Classical
set_option maxHeartbeats 1800000
variable {V : Type*} {G : SimpleGraph V} {r a b : V}

def coordinates (C : G.Walk r r) (i : Fin 7) : V := C.getVert (i.val+1)

lemma coordinates_last (C : G.Walk r r) (hl : C.length=7) : coordinates C 6=r := by
  change C.getVert 7=r
  rw [←hl,Walk.getVert_length]

lemma coordinates_injective (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7) :
    Function.Injective (coordinates C) := by
  intro i j he
  have hh := hC.getVert_injOn (show 1 ≤ i.val+1 ∧ i.val+1 ≤ C.length by constructor <;> omega)
    (show 1 ≤ j.val+1 ∧ j.val+1 ≤ C.length by constructor <;> omega) he
  exact Fin.ext (by omega)

lemma coordinates_support (C : G.Walk r r) (hl : C.length=7) (x : V) :
    x ∈ C.support ↔ ∃ i : Fin 7, coordinates C i=x := by
  constructor
  · intro hx
    obtain ⟨j,hj,hjl⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    by_cases hj0 : j=0
    · refine ⟨6,?_⟩
      rw [coordinates_last C hl]
      simpa only [hj0,Walk.getVert_zero] using hj
    · refine ⟨⟨j-1,by omega⟩,?_⟩
      simpa only [coordinates,show j-1+1=j by omega] using hj
  · rintro ⟨i,rfl⟩
    exact C.getVert_mem_support _

lemma coordinates_edge_positions (C : G.Walk r r) (hl : C.length=7) (i : Fin 7) :
    s(coordinates C i,coordinates C (next i))=
      s(C.getVert ((i.val+1)%7),C.getVert (((i.val+1)%7)+1)) := by
  have h6 : C.getVert 7=C.getVert 0 := by rw [←hl,Walk.getVert_length,Walk.getVert_zero]
  fin_cases i <;> simp [coordinates,next,h6]

lemma coordinates_adj (C : G.Walk r r) (hl : C.length=7) (i : Fin 7) :
    G.Adj (coordinates C i) (coordinates C (next i)) := by
  apply G.adj_congr_of_sym2 (coordinates_edge_positions C hl i) |>.mpr
  exact C.adj_getVert_succ (by have hh := Nat.mod_lt (i.val+1) (by decide : 0<7); omega)

lemma coordinates_edges (C : G.Walk r r) (hl : C.length=7) :
    C.toSubgraph.edgeSet=⋃ i : Fin 7, ({s(coordinates C i,coordinates C (next i))} : Set (Sym2 V)) := by
  ext e
  rw [Walk.mem_edges_toSubgraph,edges_positions]
  simp only [Set.mem_iUnion,Set.mem_singleton_iff]
  constructor
  · rintro ⟨j,hj,he⟩
    let i : Fin 7 := if j=0 then 6 else ⟨j-1,by omega⟩
    have hij : (i.val+1)%7=j := by
      dsimp [i]
      split_ifs with h0
      · omega
      · have hh : j-1+1=j := by omega
        rw [hh,Nat.mod_eq_of_lt (by omega)]
    exact ⟨i,by rw [coordinates_edge_positions C hl i,hij]; exact he⟩
  · rintro ⟨i,he⟩
    rw [coordinates_edge_positions C hl i] at he
    exact ⟨(i.val+1)%7,by have hh := Nat.mod_lt (i.val+1) (by decide : 0<7); omega,he⟩

lemma coordinates_cycle_adj (C : G.Walk r r) (hl : C.length=7) (i j : Fin 6)
    (hij : adjacent i j) : C.toSubgraph.Adj (coordinates C i.castSucc) (coordinates C j.castSucc) := by
  change s(coordinates C i.castSucc,coordinates C j.castSucc) ∈ C.toSubgraph.edgeSet
  rw [coordinates_edges C hl]
  rcases hij with hij|hji
  · refine Set.mem_iUnion.mpr ⟨i.castSucc,?_⟩
    have he : next i.castSucc=j.castSucc := Fin.ext (by dsimp [next]; rw [hij,Nat.mod_eq_of_lt (by omega)])
    rw [he]; rfl
  · refine Set.mem_iUnion.mpr ⟨j.castSucc,?_⟩
    have he : next j.castSucc=i.castSucc := Fin.ext (by dsimp [next]; rw [hji,Nat.mod_eq_of_lt (by omega)])
    rw [he]; exact Sym2.eq_swap

lemma ordered_visit_position (C : G.Walk r r) (hl : C.length=7) (P : G.Walk a b) (hp : P.IsPath)
    (hmiss : r ∉ P.support)
    (h : Fin 6 → ℕ) (p : Fin 6 → Fin 6) (hpinj : Function.Injective p)
    (hb : ∀ i, h i ≤ P.length) (hc : ∀ i, P.getVert (h i)=coordinates C (p i).castSucc)
    {m : ℕ} (hm : m ≤ P.length) (hx : P.getVert m ∈ C.support) : ∃ i, m=h i := by
  obtain ⟨j,hj⟩ := (coordinates_support C hl _).mp hx
  have hj5 : j.val < 6 := by
    by_contra hn
    have he : j=6 := Fin.ext (by omega)
    rw [he,coordinates_last C hl] at hj
    exact hmiss (hj.symm ▸ P.getVert_mem_support m)
  let j' : Fin 6 := ⟨j.val,hj5⟩
  have hj' : j'.castSucc=j := Fin.ext rfl
  obtain ⟨i,hi⟩ := (Finite.injective_iff_surjective.mp hpinj) j'
  have he : P.getVert m=P.getVert (h i) := by rw [hc i,hi,hj',hj]
  exact ⟨i,hp.getVert_injOn hm (hb i) he⟩

end HeptagonCoordinates

/- Realizing the seven-cycle certificates on five consecutive marked path intervals. -/
namespace HeptagonPieceSystem
open SimpleGraph PieceRoutes
open HeptagonRoutes PathIntervals OrderedPathPieces
set_option maxHeartbeats 2000000
variable {V : Type*} {G : SimpleGraph V} {a b : V}

variable (p : Fin 6 → Fin 6) (f : Fin 7 → V)
variable (P : G.Walk a b) (h : Fin 6 → ℕ) (hh : StrictMono h)
variable (hc : ∀ i, P.getVert (h i)=f (p i).castSucc)
variable (ha : ∀ i : Fin 7, G.Adj (f i) (f (next i)))

def pieces (e : Fin 12) : G.Walk (f (pieceSource p e)) (f (pieceTarget p e)) :=
  Fin.addCases (motive := fun e : Fin 12 ↦ G.Walk (f (pieceSource p e)) (f (pieceTarget p e)))
    (fun i : Fin 7 ↦ (Walk.cons (ha i) Walk.nil).copy
      (congrArg f (cycle_source p i).symm) (congrArg f (cycle_target p i).symm))
    (fun i : Fin 5 ↦ (gap P h hh i).copy
      ((hc i.castSucc).trans (congrArg f (path_source p i).symm))
      ((hc i.succ).trans (congrArg f (path_target p i).symm))) e

lemma cycle_support (i : Fin 7) :
    (pieces p f P h hh hc ha (Fin.castAdd 5 i)).support=[f i,f (next i)] := by
  simp [pieces]

lemma path_support (i : Fin 5) :
    (pieces p f P h hh hc ha (Fin.natAdd 7 i)).support=(gap P h hh i).support := by
  simp [pieces]

lemma cycle_edges (i : Fin 7) :
    (pieces p f P h hh hc ha (Fin.castAdd 5 i)).toSubgraph.edgeSet={s(f i,f (next i))} := by
  ext e
  simp [pieces]

lemma path_edges (i : Fin 5) :
    (pieces p f P h hh hc ha (Fin.natAdd 7 i)).toSubgraph.edgeSet=(gap P h hh i).toSubgraph.edgeSet := by
  ext e
  simp [pieces]

lemma pieces_isPath (hp : P.IsPath) : ∀ e, (pieces p f P h hh hc ha e).IsPath := by
  refine Fin.addCases (m := 7) (n := 5) ?_ ?_
  · intro i
    simp [pieces,(ha i).ne]
  · intro i
    simpa [pieces] using gap_isPath P hp h hh i

lemma pieces_core (hmiss : f 6 ∉ P.support) (hpinj : Function.Injective p) (hf : Function.Injective f) (hp : P.IsPath)
    (hb : ∀ i, h i ≤ P.length) :
    ∀ e x, f x ∈ (pieces p f P h hh hc ha e).support →
      x=pieceSource p e ∨ x=pieceTarget p e := by
  refine Fin.addCases (m := 7) (n := 5) ?_ ?_
  · intro i x hx
    rw [cycle_support] at hx
    rcases (show f x=f i ∨ f x=f (next i) by simpa using hx) with hx|hx
    · exact Or.inl ((hf hx).trans (cycle_source p i).symm)
    · exact Or.inr ((hf hx).trans (cycle_target p i).symm)
  · intro i x hx
    rw [path_support] at hx
    by_cases hxi : x.val < 6
    · let y : Fin 6 := ⟨x.val,hxi⟩
      have hy : y.castSucc=x := Fin.ext rfl
      obtain ⟨j,hj⟩ := (Finite.injective_iff_surjective.mp hpinj) y
      have hx' : P.getVert (h j) ∈ (gap P h hh i).support := by rw [hc j,hj,hy]; exact hx
      rcases (gap_core P hp h hh hb i j).mp hx' with rfl|rfl
      · exact Or.inl (((congrArg Fin.castSucc hj).trans hy).symm.trans (path_source p i).symm)
      · exact Or.inr (((congrArg Fin.castSucc hj).trans hy).symm.trans (path_target p i).symm)
    · have he : x=6 := Fin.ext (by omega)
      have hxP : f x ∈ P.support := by
        obtain ⟨m,_,_,he'⟩ := (interval_support P _ (hb i.succ) (f x)).mp hx
        rw [he']; exact P.getVert_mem_support _
      exact (hmiss (he ▸ hxP)).elim

lemma pieces_intersection (hp : P.IsPath) (hb : ∀ i, h i ≤ P.length) :
    ∀ e j, e ≠ j → ∀ x ∈ (pieces p f P h hh hc ha e).support,
      x ∈ (pieces p f P h hh hc ha j).support → ∃ z, x=f z := by
  refine Fin.addCases (m := 7) (n := 5) ?_ ?_
  · intro i j hij x hx hy
    rw [cycle_support] at hx
    rcases (show x=f i ∨ x=f (next i) by simpa using hx) with hx|hx
    · exact ⟨_,hx⟩
    · exact ⟨_,hx⟩
  · intro i
    refine Fin.addCases (m := 7) (n := 5) ?_ ?_
    · intro j hij x hx hy
      rw [cycle_support] at hy
      rcases (show x=f j ∨ x=f (next j) by simpa using hy) with hy|hy
      · exact ⟨_,hy⟩
      · exact ⟨_,hy⟩
    · intro j hij x hx hy
      rw [path_support] at hx hy
      have hne : i ≠ j := fun he ↦ hij (congrArg (Fin.natAdd 7) he)
      obtain ⟨z,hz⟩ := gap_intersection P hp h hh hb i j hne hx hy
      exact ⟨(p z).castSucc,hz.trans (hc z)⟩

lemma cycle_edge_injective (hf : Function.Injective f) :
    Function.Injective (fun i : Fin 7 ↦ s(f i,f (next i))) := by
  intro i j he
  rcases Sym2.eq_iff.mp he with ⟨he,_⟩|⟨he,he'⟩
  · have hv : i.val=j.val := congrArg (fun x : Fin 7 ↦ x.val) (hf he)
    exact Fin.ext hv
  · have h1 := congrArg Fin.val (hf he)
    have h2 := congrArg Fin.val (hf he')
    dsimp [next] at h1 h2
    omega

lemma pieces_disjoint (hf : Function.Injective f) (hp : P.IsPath) (hb : ∀ i, h i ≤ P.length)
    (havoid : ∀ i : Fin 7, s(f i,f (next i)) ∉ P.edges) :
    ∀ e j, e ≠ j → Disjoint (pieces p f P h hh hc ha e).toSubgraph.edgeSet
      (pieces p f P h hh hc ha j).toSubgraph.edgeSet := by
  refine Fin.addCases (m := 7) (n := 5) ?_ ?_
  · intro i
    refine Fin.addCases (m := 7) (n := 5) ?_ ?_
    · intro j hij
      rw [cycle_edges,cycle_edges]
      apply Set.disjoint_singleton_left.mpr
      intro he
      have he' := cycle_edge_injective f hf he
      exact hij (congrArg (Fin.castAdd 5) he')
    · intro j hij
      rw [cycle_edges,path_edges]
      apply Set.disjoint_singleton_left.mpr
      intro he
      exact havoid i (P.mem_edges_toSubgraph.mp (gap_edges_subset P h hh hb j he))
  · intro i
    refine Fin.addCases (m := 7) (n := 5) ?_ ?_
    · intro j hij
      rw [path_edges,cycle_edges]
      apply Disjoint.symm
      apply Set.disjoint_singleton_left.mpr
      intro he
      exact havoid j (P.mem_edges_toSubgraph.mp (gap_edges_subset P h hh hb i he))
    · intro j hij
      rw [path_edges,path_edges]
      exact gap_edges_disjoint P hp h hh hb i j (fun he ↦ hij (congrArg (Fin.natAdd 7) he))

def cycleEdges : Set (Sym2 V) := ⋃ i : Fin 7, ({s(f i,f (next i))} : Set (Sym2 V))

lemma pieces_cover (hb : ∀ i, h i ≤ P.length) :
    (⋃ e, (pieces p f P h hh hc ha e).toSubgraph.edgeSet)=cycleEdges f ∪
      (interval P (h 0) (h 5) (hh.monotone (Fin.zero_le _))).toSubgraph.edgeSet := by
  rw [show (5 : Fin 6)=Fin.last 5 from rfl,←gap_cover P h hh hb]
  ext e
  simp only [cycleEdges,Set.mem_union,Set.mem_iUnion]
  constructor
  · rintro ⟨j,hj⟩
    have haux : ∀ j : Fin 12, e ∈ (pieces p f P h hh hc ha j).toSubgraph.edgeSet →
        (∃ i : Fin 7, e ∈ ({s(f i,f (next i))} : Set (Sym2 V))) ∨
        ∃ i : Fin 5, e ∈ (gap P h hh i).toSubgraph.edgeSet := by
      refine Fin.addCases (m := 7) (n := 5) ?_ ?_
      · intro i hi
        exact Or.inl ⟨i,(cycle_edges p f P h hh hc ha i) ▸ hi⟩
      · intro i hi
        exact Or.inr ⟨i,(path_edges p f P h hh hc ha i) ▸ hi⟩
    exact haux j hj
  · rintro (⟨i,hi⟩|⟨i,hi⟩)
    · exact ⟨Fin.castAdd 5 i,(cycle_edges p f P h hh hc ha i).symm ▸ hi⟩
    · exact ⟨Fin.natAdd 7 i,(path_edges p f P h hh hc ha i).symm ▸ hi⟩

include hc in
lemma core_in_middle (hpinj : Function.Injective p) (hb : ∀ i, h i ≤ P.length) (x : Fin 6) :
    f x.castSucc ∈ (interval P (h 0) (h 5) (hh.monotone (Fin.zero_le _))).support := by
  obtain ⟨j,hj⟩ := (Finite.injective_iff_surjective.mp hpinj) x
  rw [interval_support P _ (hb 5)]
  exact ⟨h j,hh.monotone (Fin.zero_le _),hh.monotone (Fin.le_last _),by rw [hc j,hj]⟩

lemma pieces_on_path_middle (hmiss : f 6 ∉ P.support)
    (hpinj : Function.Injective p) (hb : ∀ i, h i ≤ P.length) :
    ∀ e x, x ∈ (pieces p f P h hh hc ha e).support → x ∈ P.support →
      x ∈ (interval P (h 0) (h 5) (hh.monotone (Fin.zero_le _))).support := by
  have hcore (i : Fin 7) (hi : f i ∈ P.support) :
      f i ∈ (interval P (h 0) (h 5) (hh.monotone (Fin.zero_le _))).support := by
    have hi5 : i.val < 6 := by
      by_contra hh
      have he : i=6 := Fin.ext (by omega)
      exact hmiss (he ▸ hi)
    exact core_in_middle p f P h hh hc hpinj hb ⟨i.val,hi5⟩
  refine Fin.addCases (m := 7) (n := 5) ?_ ?_
  · intro i x hx hxP
    rw [cycle_support] at hx
    rcases (show x=f i ∨ x=f (next i) by simpa using hx) with rfl|rfl
    · exact hcore i hxP
    · exact hcore (next i) hxP
  · intro i x hx hxP
    rw [path_support,gap,interval_support P _ (hb i.succ)] at hx
    obtain ⟨m,him,hmi,hxm⟩ := hx
    rw [interval_support P _ (hb 5)]
    exact ⟨m,(hh.monotone (Fin.zero_le _)).trans him,hmi.trans (hh.monotone (Fin.le_last _)),hxm⟩

include hc ha in
lemma ordered_absorption (hmiss : f 6 ∉ P.support) (hpinj : Function.Injective p) (hf : Function.Injective f) (hp : P.IsPath)
    (hfirst : ¬adjacent (p 0) (p 1)) (hlast : ¬adjacent (p 4) (p 5)) (hex : ¬Exceptional p)
    (hb : ∀ i, h i ≤ P.length)
    (havoid : ∀ i : Fin 7, s(f i,f (next i)) ∉ P.edges) :
    ∃ X : G.Walk (f (p 0).castSucc) (f 6), ∃ Y : G.Walk (f (p 5).castSucc) (f 6),
      X.IsPath ∧ Y.IsPath ∧ Disjoint X.toSubgraph.edgeSet Y.toSubgraph.edgeSet ∧
        X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=cycleEdges f ∪
          (interval P (h 0) (h 5) (hh.monotone (Fin.zero_le _))).toSubgraph.edgeSet ∧
      (∀ x ∈ X.support, x ∈ P.support → x ∈ (interval P (h 0) (h 5) (hh.monotone (Fin.zero_le _))).support) ∧
      (∀ x ∈ Y.support, x ∈ P.support → x ∈ (interval P (h 0) (h 5) (hh.monotone (Fin.zero_le _))).support) := by
  obtain ⟨X,Y,hX,hY,hd,he⟩ := expand_certificate p hpinj hfirst hlast hex f hf (pieces p f P h hh hc ha)
    (pieces_isPath p f P h hh hc ha hp) (pieces_core p f P h hh hc ha hmiss hpinj hf hp hb)
    (pieces_intersection p f P h hh hc ha hp hb) (pieces_disjoint p f P h hh hc ha hf hp hb havoid)
  have hnX : ¬X.Nil := Walk.not_nil_of_ne (by
    intro hh
    have hv := congrArg (fun z : Fin 7 ↦ z.val) (hf hh)
    have hp0 := (p 0).isLt
    simp only [Fin.val_castSucc] at hv
    omega)
  have hnY : ¬Y.Nil := Walk.not_nil_of_ne (by
    intro hh
    have hv := congrArg (fun z : Fin 7 ↦ z.val) (hf hh)
    have hp4 := (p 5).isLt
    simp only [Fin.val_castSucc] at hv
    omega)
  have hsupport {u v : V} (W : G.Walk u v) (hn : ¬W.Nil)
      (hw : W.toSubgraph.edgeSet ⊆ ⋃ e, (pieces p f P h hh hc ha e).toSubgraph.edgeSet) :
      ∀ x ∈ W.support, x ∈ P.support → x ∈ (interval P (h 0) (h 5) (hh.monotone (Fin.zero_le _))).support := by
    intro x hx hxP
    obtain ⟨y,hy⟩ := VertexTracking.walk_vertex_has_subgraph_neighbor W hn (W.mem_verts_toSubgraph.mpr hx)
    obtain ⟨e,he⟩ := Set.mem_iUnion.mp (hw (show s(x,y) ∈ W.toSubgraph.edgeSet from hy))
    exact pieces_on_path_middle p f P h hh hc ha hmiss hpinj hb e x (Walk.mem_support_of_adj_toSubgraph he) hxP
  exact ⟨X,Y,hX,hY,hd,he.trans (pieces_cover p f P h hh hc ha hb),
    hsupport X hnX (fun e hx ↦ he ▸ Or.inl hx),hsupport Y hnY (fun e hy ↦ he ▸ Or.inr hy)⟩

end HeptagonPieceSystem

/- The four exceptional seven-cycle visit orders, split at their second path gap. -/
namespace HeptagonSplitRoutes
open SimpleGraph PieceRoutes
open _root_.Erdos583Work.HeptagonRoutes (Exceptional adjacent code fromList)
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option Elab.async false

def extended (p : Fin 6 → Fin 6) (i : Fin 7) : Fin 8 :=
  if h : i.val ≤ 1 then (p ⟨i.val,by omega⟩).castSucc.castSucc
  else if i.val=2 then 7 else (p ⟨i.val-1,by omega⟩).castSucc.castSucc

def pieceSource (p : Fin 6 → Fin 6) (e : Fin 13) : Fin 8 :=
  if h : e.val < 7 then (⟨e.val,h⟩ : Fin 7).castSucc
  else extended p ⟨e.val-7,by omega⟩

def pieceTarget (p : Fin 6 → Fin 6) (e : Fin 13) : Fin 8 :=
  if e.val < 7 then (⟨(e.val+1)%7,Nat.mod_lt _ (by decide)⟩ : Fin 7).castSucc
  else extended p ⟨e.val-6,by omega⟩

abbrev Steps := List (Fin 13 × Bool)

def Valid (p : Fin 6 → Fin 6) (v : Steps × Steps) : Prop :=
  Route.compatible (s := pieceSource p) (t := pieceTarget p) (p 0).castSucc.castSucc 7 v.1=true ∧
  Route.compatible (s := pieceSource p) (t := pieceTarget p) (p 5).castSucc.castSucc 7 v.2=true ∧
  ((p 0).castSucc.castSucc :: v.1.map (fun ed ↦ target (pieceSource p) (pieceTarget p) ed.1 ed.2)).Nodup ∧
  ((p 5).castSucc.castSucc :: v.2.map (fun ed ↦ target (pieceSource p) (pieceTarget p) ed.1 ed.2)).Nodup ∧
  (∀ e : Fin 13, e ∈ v.1.map Prod.fst → e ∉ v.2.map Prod.fst) ∧
  ∀ e : Fin 13, e ∈ v.1.map Prod.fst ∨ e ∈ v.2.map Prod.fst

instance (p : Fin 6 → Fin 6) (v : Steps × Steps) : Decidable (Valid p v) := by
  unfold Valid
  infer_instance

def certificates : List (ℕ × (Steps × Steps)) := [
  (30710,([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])),
  (24830,([(2,true),(12,false),(0,false),(6,false),(5,false),(4,false),(8,true)],[(3,true),(7,false),(1,false),(11,false),(10,false),(9,false)])),
  (21825,([(2,false),(12,false),(4,true),(5,true),(6,true),(0,true),(8,true)],[(1,false),(7,false),(3,true),(11,false),(10,false),(9,false)])),
  (15945,([(2,false),(1,false),(0,false),(6,false),(5,false),(4,false),(9,false)],[(12,false),(11,false),(10,false),(3,false),(7,true),(8,true)]))]

def choice (p : Fin 6 → Fin 6) : Steps × Steps := (certificates.lookup (code p)).getD ([],[])

lemma finite_certificate_orders : ∀ l ∈ ([0,1,2,3,4,5] : List (Fin 6)).permutations',
    Exceptional (fromList l) →
    adjacent (fromList l 1) (fromList l 2) ∧ Valid (fromList l) (choice (fromList l)) := by
  decide

lemma finite_certificate (p : Fin 6 → Fin 6) (hp : Function.Injective p)
    (hex : Exceptional p) : adjacent (p 1) (p 2) ∧ Valid p (choice p) := by
  have he : fromList (List.ofFn p)=p := by
    funext i
    fin_cases i <;> rfl
  have hmem : List.ofFn p ∈ ([0,1,2,3,4,5] : List (Fin 6)).permutations' := by
    apply List.mem_permutations'.mpr
    apply (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr hp) (by decide)).mpr
    intro x
    constructor
    · intro _; fin_cases x <;> decide
    · intro _
      exact List.mem_ofFn.mpr ((Finite.injective_iff_surjective.mp hp) x)
  have hh := finite_certificate_orders (List.ofFn p) hmem
  rw [he] at hh
  exact hh hex

lemma exists_routes (p : Fin 6 → Fin 6) (hp : Function.Injective p) (hex : Exceptional p) :
    ∃ X : Route (pieceSource p) (pieceTarget p) (p 0).castSucc.castSucc 7,
    ∃ Y : Route (pieceSource p) (pieceTarget p) (p 5).castSucc.castSucc 7,
      X.support.Nodup ∧ Y.support.Nodup ∧ X.pieces.Disjoint Y.pieces ∧
        ∀ e, e ∈ X.pieces ∨ e ∈ Y.pieces := by
  obtain ⟨_,ha,hb,hnX,hnY,hd,hc⟩ := finite_certificate p hp hex
  obtain ⟨X,hXs,hXp⟩ := Route.of_compatible (choice p).1 ha
  obtain ⟨Y,hYs,hYp⟩ := Route.of_compatible (choice p).2 hb
  exact ⟨X,Y,hXs.symm ▸ hnX,hYs.symm ▸ hnY,by simpa only [hXp,hYp] using hd,
    by simpa only [hXp,hYp] using hc⟩

end HeptagonSplitRoutes

/- Expansion and coordinates for the exceptional split-gap certificates. -/
namespace HeptagonSplitRoutes
open SimpleGraph PieceRoutes
open _root_.Erdos583Work.HeptagonRoutes (Exceptional)
set_option maxHeartbeats 2000000

lemma extended_zero (p : Fin 6 → Fin 6) : extended p 0=(p 0).castSucc.castSucc := by
  simp [extended]

lemma extended_last (p : Fin 6 → Fin 6) : extended p 6=(p 5).castSucc.castSucc := by
  simp [extended]

lemma extended_injective (p : Fin 6 → Fin 6) (hp : Function.Injective p) :
    Function.Injective (extended p) := by
  intro i j he
  have hh := congrArg Fin.val he
  unfold extended at hh
  split_ifs at hh <;> simp only [Fin.val_castSucc] at hh
  all_goals first
    | exact Fin.ext (by omega)
    | have h := congrArg Fin.val (hp (Fin.ext hh)); exact Fin.ext (by dsimp at h; omega)

lemma extended_visit (p : Fin 6 → Fin 6) (hp : Function.Injective p) (x : Fin 8) (hx : x ≠ 6) :
    ∃ i, extended p i=x := by
  by_cases h7 : x=7
  · exact ⟨2, by simp [extended,h7]⟩
  have hlt : x.val < 6 := by
    have h6 : x.val ≠ 6 := fun he ↦ hx (Fin.ext he)
    have h7' : x.val ≠ 7 := fun he ↦ h7 (Fin.ext he)
    omega
  obtain ⟨j,hj⟩ := (Finite.injective_iff_surjective.mp hp) ⟨x.val,hlt⟩
  by_cases hj1 : j.val ≤ 1
  · refine ⟨⟨j.val,by omega⟩,?_⟩
    simp only [extended,hj1,↓reduceDIte]
    exact Fin.ext (congrArg (fun y : Fin 6 ↦ y.val) hj)
  · refine ⟨⟨j.val+1,by omega⟩,?_⟩
    simp only [extended,show ¬j.val+1 ≤ 1 by omega,show j.val+1 ≠ 2 by omega,↓reduceDIte,
      ↓reduceIte,Nat.add_sub_cancel]
    exact Fin.ext (congrArg (fun y : Fin 6 ↦ y.val) hj)

lemma cycle_source (p : Fin 6 → Fin 6) (i : Fin 7) :
    pieceSource p (Fin.castAdd 6 i)=i.castSucc := by simp [pieceSource,i.isLt]

lemma cycle_target (p : Fin 6 → Fin 6) (i : Fin 7) :
    pieceTarget p (Fin.castAdd 6 i)=(⟨(i.val+1)%7,Nat.mod_lt _ (by decide)⟩ : Fin 7).castSucc := by
  simp [pieceTarget,i.isLt]

lemma path_source (p : Fin 6 → Fin 6) (i : Fin 6) :
    pieceSource p (Fin.natAdd 7 i)=extended p i.castSucc := by
  simp [pieceSource,Fin.natAdd,Nat.add_comm]
  rfl

lemma path_target (p : Fin 6 → Fin 6) (i : Fin 6) :
    pieceTarget p (Fin.natAdd 7 i)=extended p i.succ := by
  simp [pieceTarget,Fin.natAdd,Nat.add_comm]
  rfl

lemma expand_certificate {V : Type*} {G : SimpleGraph V}
    (p : Fin 6 → Fin 6) (hp : Function.Injective p) (hex : Exceptional p)
    (f : Fin 8 → V) (hf : Function.Injective f)
    (R : ∀ e : Fin 13, G.Walk (f (pieceSource p e)) (f (pieceTarget p e)))
    (hpath : ∀ e, (R e).IsPath)
    (hcore : ∀ e x, f x ∈ (R e).support → x=pieceSource p e ∨ x=pieceTarget p e)
    (hinter : ∀ e j, e ≠ j → ∀ x ∈ (R e).support, x ∈ (R j).support → ∃ a, x=f a)
    (hdis : ∀ e j, e ≠ j → Disjoint (R e).toSubgraph.edgeSet (R j).toSubgraph.edgeSet) :
    ∃ X : G.Walk (f (p 0).castSucc.castSucc) (f 7),
    ∃ Y : G.Walk (f (p 5).castSucc.castSucc) (f 7),
      X.IsPath ∧ Y.IsPath ∧ Disjoint X.toSubgraph.edgeSet Y.toSubgraph.edgeSet ∧
        X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=⋃ e, (R e).toSubgraph.edgeSet := by
  obtain ⟨X,Y,hX,hY,hd,hc⟩ := exists_routes p hp hex
  exact ⟨X.expand f R,Y.expand f R,Route.expand_two_cover f R hf hpath hcore hinter hdis X Y hX hY hd hc⟩

lemma extend_injective {V : Type*} {n : ℕ} (c : Fin n → V) (hc : Function.Injective c)
    (z : V) (hz : ∀ i, z ≠ c i) :
    Function.Injective (Fin.lastCases z c : Fin (n+1) → V) := by
  intro i j he
  revert he
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · intro _; rfl
    · intro he; exact (hz j (by simpa using he)).elim
  · refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · intro he; exact (hz i (by simpa using he.symm)).elim
    · intro he
      exact congrArg Fin.castSucc (hc (by simpa using he))

lemma inserted_coordinates {V : Type*} {G : SimpleGraph V} {a b : V}
    (P : G.Walk a b) (c : Fin 7 → V) (h : Fin 6 → ℕ) (p : Fin 6 → Fin 6)
    (hc : ∀ i, P.getVert (h i)=c (p i).castSucc) (m : ℕ) (z : V) (hz : P.getVert m=z) :
    ∀ i : Fin 7, P.getVert (HexagonExcursionCoordinates.insertCut h 1 m i)=
      (Fin.lastCases z c : Fin 8 → V) (extended p i) := by
  intro i
  unfold HexagonExcursionCoordinates.insertCut extended
  simp only [Fin.val_one]
  split_ifs <;> simp [hz,hc]
  rfl

end HeptagonSplitRoutes

/- Realizing the finite heptagon certificates on consecutive subpaths. -/
namespace HeptagonSplitPieceSystem
open SimpleGraph PieceRoutes
open HeptagonSplitRoutes PathIntervals OrderedPathPieces
set_option maxHeartbeats 2000000
variable {V : Type*} {G : SimpleGraph V} {a b : V}

def next (i : Fin 7) : Fin 7 := ⟨(i.val+1)%7,Nat.mod_lt _ (by decide)⟩

variable (p : Fin 6 → Fin 6) (f : Fin 8 → V)
variable (P : G.Walk a b) (h : Fin 7 → ℕ) (hh : StrictMono h)
variable (hc : ∀ i, P.getVert (h i)=f (extended p i))
variable (ha : ∀ i : Fin 7, G.Adj (f i.castSucc) (f (next i).castSucc))

def pieces (e : Fin 13) : G.Walk (f (pieceSource p e)) (f (pieceTarget p e)) :=
  Fin.addCases (motive := fun e : Fin 13 ↦ G.Walk (f (pieceSource p e)) (f (pieceTarget p e)))
    (fun i : Fin 7 ↦ (Walk.cons (ha i) Walk.nil).copy
      (congrArg f (cycle_source p i).symm) (congrArg f (cycle_target p i).symm))
    (fun i : Fin 6 ↦ (gap P h hh i).copy
      ((hc i.castSucc).trans (congrArg f (path_source p i).symm))
      ((hc i.succ).trans (congrArg f (path_target p i).symm))) e

lemma cycle_support (i : Fin 7) :
    (pieces p f P h hh hc ha (Fin.castAdd 6 i)).support=[f i.castSucc,f (next i).castSucc] := by
  simp [pieces]

lemma path_support (i : Fin 6) :
    (pieces p f P h hh hc ha (Fin.natAdd 7 i)).support=(gap P h hh i).support := by
  simp [pieces]

lemma cycle_edges (i : Fin 7) :
    (pieces p f P h hh hc ha (Fin.castAdd 6 i)).toSubgraph.edgeSet={s(f i.castSucc,f (next i).castSucc)} := by
  ext e
  simp [pieces]

lemma path_edges (i : Fin 6) :
    (pieces p f P h hh hc ha (Fin.natAdd 7 i)).toSubgraph.edgeSet=(gap P h hh i).toSubgraph.edgeSet := by
  ext e
  simp [pieces]

lemma pieces_isPath (hp : P.IsPath) : ∀ e, (pieces p f P h hh hc ha e).IsPath := by
  refine Fin.addCases (m := 7) (n := 6) ?_ ?_
  · intro i
    simp [pieces,(ha i).ne]
  · intro i
    simpa [pieces] using gap_isPath P hp h hh i

lemma pieces_core (hmiss : f 6 ∉ P.support) (hpinj : Function.Injective p) (hf : Function.Injective f) (hp : P.IsPath)
    (hb : ∀ i, h i ≤ P.length) :
    ∀ e x, f x ∈ (pieces p f P h hh hc ha e).support →
      x=pieceSource p e ∨ x=pieceTarget p e := by
  refine Fin.addCases (m := 7) (n := 6) ?_ ?_
  · intro i x hx
    rw [cycle_support] at hx
    rcases (show f x=f i.castSucc ∨ f x=f (next i).castSucc by simpa using hx) with hx|hx
    · exact Or.inl ((hf hx).trans (cycle_source p i).symm)
    · exact Or.inr ((hf hx).trans (cycle_target p i).symm)
  · intro i x hx
    rw [path_support] at hx
    have hxn : x ≠ 6 := by
      intro he
      subst x
      obtain ⟨m,_,_,he'⟩ := (interval_support P _ (hb i.succ) (f 6)).mp hx
      exact hmiss (he' ▸ P.getVert_mem_support m)
    obtain ⟨j,hj⟩ := extended_visit p hpinj x hxn
    have hx' : P.getVert (h j) ∈ (gap P h hh i).support := by rw [hc j,hj]; exact hx
    rcases (gap_core P hp h hh hb i j).mp hx' with rfl|rfl
    · exact Or.inl (hj.symm.trans (path_source p i).symm)
    · exact Or.inr (hj.symm.trans (path_target p i).symm)

lemma pieces_intersection (hp : P.IsPath) (hb : ∀ i, h i ≤ P.length) :
    ∀ e j, e ≠ j → ∀ x ∈ (pieces p f P h hh hc ha e).support,
      x ∈ (pieces p f P h hh hc ha j).support → ∃ z, x=f z := by
  refine Fin.addCases (m := 7) (n := 6) ?_ ?_
  · intro i j hij x hx hy
    rw [cycle_support] at hx
    rcases (show x=f i.castSucc ∨ x=f (next i).castSucc by simpa using hx) with hx|hx
    · exact ⟨_,hx⟩
    · exact ⟨_,hx⟩
  · intro i
    refine Fin.addCases (m := 7) (n := 6) ?_ ?_
    · intro j hij x hx hy
      rw [cycle_support] at hy
      rcases (show x=f j.castSucc ∨ x=f (next j).castSucc by simpa using hy) with hy|hy
      · exact ⟨_,hy⟩
      · exact ⟨_,hy⟩
    · intro j hij x hx hy
      rw [path_support] at hx hy
      have hne : i ≠ j := fun he ↦ hij (congrArg (Fin.natAdd 7) he)
      obtain ⟨z,hz⟩ := gap_intersection P hp h hh hb i j hne hx hy
      exact ⟨extended p z,hz.trans (hc z)⟩

lemma cycle_edge_injective (hf : Function.Injective f) :
    Function.Injective (fun i : Fin 7 ↦ s(f i.castSucc,f (next i).castSucc)) := by
  intro i j he
  rcases Sym2.eq_iff.mp he with ⟨he,_⟩|⟨he,he'⟩
  · have hv : i.val=j.val := congrArg (fun x : Fin 8 ↦ x.val) (hf he)
    exact Fin.ext hv
  · have h1 := congrArg Fin.val (hf he)
    have h2 := congrArg Fin.val (hf he')
    dsimp [next] at h1 h2
    omega

lemma pieces_disjoint (hf : Function.Injective f) (hp : P.IsPath) (hb : ∀ i, h i ≤ P.length)
    (havoid : ∀ i : Fin 7, s(f i.castSucc,f (next i).castSucc) ∉ P.edges) :
    ∀ e j, e ≠ j → Disjoint (pieces p f P h hh hc ha e).toSubgraph.edgeSet
      (pieces p f P h hh hc ha j).toSubgraph.edgeSet := by
  refine Fin.addCases (m := 7) (n := 6) ?_ ?_
  · intro i
    refine Fin.addCases (m := 7) (n := 6) ?_ ?_
    · intro j hij
      rw [cycle_edges,cycle_edges]
      apply Set.disjoint_singleton_left.mpr
      intro he
      have he' := cycle_edge_injective f hf he
      exact hij (congrArg (Fin.castAdd 6) he')
    · intro j hij
      rw [cycle_edges,path_edges]
      apply Set.disjoint_singleton_left.mpr
      intro he
      exact havoid i (P.mem_edges_toSubgraph.mp (gap_edges_subset P h hh hb j he))
  · intro i
    refine Fin.addCases (m := 7) (n := 6) ?_ ?_
    · intro j hij
      rw [path_edges,cycle_edges]
      apply Disjoint.symm
      apply Set.disjoint_singleton_left.mpr
      intro he
      exact havoid j (P.mem_edges_toSubgraph.mp (gap_edges_subset P h hh hb i he))
    · intro j hij
      rw [path_edges,path_edges]
      exact gap_edges_disjoint P hp h hh hb i j (fun he ↦ hij (congrArg (Fin.natAdd 7) he))

def cycleEdges : Set (Sym2 V) := ⋃ i : Fin 7, ({s(f i.castSucc,f (next i).castSucc)} : Set (Sym2 V))

lemma pieces_cover (hb : ∀ i, h i ≤ P.length) :
    (⋃ e, (pieces p f P h hh hc ha e).toSubgraph.edgeSet)=cycleEdges f ∪
      (interval P (h 0) (h 6) (hh.monotone (Fin.zero_le _))).toSubgraph.edgeSet := by
  rw [show (6 : Fin 7)=Fin.last 6 from rfl,←gap_cover P h hh hb]
  ext e
  simp only [cycleEdges,Set.mem_union,Set.mem_iUnion]
  constructor
  · rintro ⟨j,hj⟩
    have haux : ∀ j : Fin 13, e ∈ (pieces p f P h hh hc ha j).toSubgraph.edgeSet →
        (∃ i : Fin 7, e ∈ ({s(f i.castSucc,f (next i).castSucc)} : Set (Sym2 V))) ∨
        ∃ i : Fin 6, e ∈ (gap P h hh i).toSubgraph.edgeSet := by
      refine Fin.addCases (m := 7) (n := 6) ?_ ?_
      · intro i hi
        exact Or.inl ⟨i,(cycle_edges p f P h hh hc ha i) ▸ hi⟩
      · intro i hi
        exact Or.inr ⟨i,(path_edges p f P h hh hc ha i) ▸ hi⟩
    exact haux j hj
  · rintro (⟨i,hi⟩|⟨i,hi⟩)
    · exact ⟨Fin.castAdd 6 i,(cycle_edges p f P h hh hc ha i).symm ▸ hi⟩
    · exact ⟨Fin.natAdd 7 i,(path_edges p f P h hh hc ha i).symm ▸ hi⟩

include hc in
lemma core_in_middle (hpinj : Function.Injective p) (hb : ∀ i, h i ≤ P.length) (x : Fin 8) (hx : x ≠ 6) :
    f x ∈ (interval P (h 0) (h 6) (hh.monotone (Fin.zero_le _))).support := by
  obtain ⟨j,hj⟩ := extended_visit p hpinj x hx
  rw [interval_support P _ (hb 6)]
  exact ⟨h j,hh.monotone (Fin.zero_le _),hh.monotone (Fin.le_last _),(congrArg f hj).symm.trans (hc j).symm⟩

lemma pieces_in_middle (hmiss : f 6 ∉ P.support) (hpinj : Function.Injective p) (hb : ∀ i, h i ≤ P.length) :
    ∀ e x, x ∈ (pieces p f P h hh hc ha e).support → x ∈ P.support →
      x ∈ (interval P (h 0) (h 6) (hh.monotone (Fin.zero_le _))).support := by
  refine Fin.addCases (m := 7) (n := 6) ?_ ?_
  · intro i x hx hxP
    rw [cycle_support] at hx
    rcases (show x=f i.castSucc ∨ x=f (next i).castSucc by simpa using hx) with rfl|rfl
    · apply core_in_middle p f P h hh hc hpinj hb _
      intro he
      exact hmiss (he ▸ hxP)
    · apply core_in_middle p f P h hh hc hpinj hb _
      intro he
      exact hmiss (he ▸ hxP)
  · intro i x hx hxP
    rw [path_support, gap,interval_support P _ (hb i.succ)] at hx
    obtain ⟨m,him,hmi,hxm⟩ := hx
    rw [interval_support P _ (hb 6)]
    exact ⟨m,(hh.monotone (Fin.zero_le _)).trans him,hmi.trans (hh.monotone (Fin.le_last _)),hxm⟩

include hc ha in
lemma ordered_absorption (hex : HeptagonRoutes.Exceptional p) (hmiss : f 6 ∉ P.support) (hpinj : Function.Injective p) (hf : Function.Injective f) (hp : P.IsPath)
    (hb : ∀ i, h i ≤ P.length)
    (havoid : ∀ i : Fin 7, s(f i.castSucc,f (next i).castSucc) ∉ P.edges) :
    ∃ X : G.Walk (f (p 0).castSucc.castSucc) (f 7), ∃ Y : G.Walk (f (p 5).castSucc.castSucc) (f 7),
      X.IsPath ∧ Y.IsPath ∧ Disjoint X.toSubgraph.edgeSet Y.toSubgraph.edgeSet ∧
        X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=cycleEdges f ∪
          (interval P (h 0) (h 6) (hh.monotone (Fin.zero_le _))).toSubgraph.edgeSet ∧
      (∀ x ∈ X.support, x ∈ P.support → x ∈ (interval P (h 0) (h 6) (hh.monotone (Fin.zero_le _))).support) ∧
      (∀ x ∈ Y.support, x ∈ P.support → x ∈ (interval P (h 0) (h 6) (hh.monotone (Fin.zero_le _))).support) := by
  obtain ⟨X,Y,hX,hY,hd,he⟩ := expand_certificate p hpinj hex f hf (pieces p f P h hh hc ha)
    (pieces_isPath p f P h hh hc ha hp) (pieces_core p f P h hh hc ha hmiss hpinj hf hp hb)
    (pieces_intersection p f P h hh hc ha hp hb) (pieces_disjoint p f P h hh hc ha hf hp hb havoid)
  have hnX : ¬X.Nil := Walk.not_nil_of_ne (by
    intro hh
    have hv := congrArg (fun z : Fin 8 ↦ z.val) (hf hh)
    have hp0 := (p 0).isLt
    simp only [Fin.val_castSucc] at hv
    omega)
  have hnY : ¬Y.Nil := Walk.not_nil_of_ne (by
    intro hh
    have hv := congrArg (fun z : Fin 8 ↦ z.val) (hf hh)
    have hp4 := (p 5).isLt
    simp only [Fin.val_castSucc] at hv
    omega)
  have hsupport {u v : V} (W : G.Walk u v) (hn : ¬W.Nil)
      (hw : W.toSubgraph.edgeSet ⊆ ⋃ e, (pieces p f P h hh hc ha e).toSubgraph.edgeSet) :
      ∀ x ∈ W.support, x ∈ P.support → x ∈ (interval P (h 0) (h 6) (hh.monotone (Fin.zero_le _))).support := by
    intro x hx hxP
    obtain ⟨y,hy⟩ := VertexTracking.walk_vertex_has_subgraph_neighbor W hn (W.mem_verts_toSubgraph.mpr hx)
    obtain ⟨e,he⟩ := Set.mem_iUnion.mp (hw (show s(x,y) ∈ W.toSubgraph.edgeSet from hy))
    exact pieces_in_middle p f P h hh hc ha hmiss hpinj hb e x (Walk.mem_support_of_adj_toSubgraph he) hxP
  exact ⟨X,Y,hX,hY,hd,he.trans (pieces_cover p f P h hh hc ha hb),
    hsupport X hnX (fun e hx ↦ he ▸ Or.inl hx),hsupport Y hnY (fun e hy ↦ he ▸ Or.inr hy)⟩

end HeptagonSplitPieceSystem

/- Absorbing the exceptional seven-cycle orders using a forced outside path vertex. -/
namespace HeptagonExceptional
open SimpleGraph TriangleAbsorption
open PathIntervals PathRestoreIntersection
open _root_.Erdos583Work.HeptagonRoutes (Exceptional)
open HeptagonCoordinates
open HeptagonSplitRoutes HeptagonSplitPieceSystem
open _root_.Erdos583Work.HexagonExcursionCoordinates (insertCut insertCut_strictMono insertCut_bound insertCut_zero insertCut_last)
open scoped Classical
set_option maxHeartbeats 2200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {r a b : V}

lemma exceptional_absorption (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath) (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hmiss : r ∉ P.support)
    (h : Fin 6 → ℕ) (p : Fin 6 → Fin 6) (hh : StrictMono h) (hpinj : Function.Injective p)
    (hb : ∀ i, h i ≤ P.length) (hc : ∀ i, P.getVert (h i)=coordinates C (p i).castSucc)
    (hex : Exceptional p) : TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  have hgap := (finite_certificate p hpinj hex).1
  have hlt : h 1 < h 2 := hh (by decide)
  have hne : h 1+1 ≠ h 2 := by
    intro he
    have heC : C.toSubgraph.Adj (P.getVert (h 1)) (P.getVert (h 2)) := by
      rw [hc 1,hc 2]
      exact coordinates_cycle_adj C hl _ _ hgap
    have heP : s(P.getVert (h 1),P.getVert (h 2)) ∈ P.toSubgraph.edgeSet := by
      rw [Walk.mem_edges_toSubgraph,edges_positions]
      exact ⟨h 1,hlt.trans_le (hb 2),by rw [he]⟩
    exact Set.disjoint_left.mp hd heC heP
  let m := h 1+1
  have hmlo : h 1 < m := by omega
  have hmhi : m < h 2 := by omega
  have hmout : P.getVert m ∉ C.support := by
    intro hx
    obtain ⟨j,hj⟩ := ordered_visit_position C hl P hp hmiss h p hpinj hb hc
      (hmhi.le.trans (hb 2)) hx
    have hlo : (1 : Fin 6) < j := hh.lt_iff_lt.mp (by omega)
    have hhi : j < (2 : Fin 6) := hh.lt_iff_lt.mp (by omega)
    have h1 : 1 < j.val := hlo
    have h2 : j.val < 2 := hhi
    omega
  let z := P.getVert m
  let h' := insertCut h 1 m
  let f : Fin 8 → V := Fin.lastCases z (coordinates C)
  have hh' : StrictMono h' := insertCut_strictMono h hh 1 m hmlo hmhi
  have hb' : ∀ i, h' i ≤ P.length := insertCut_bound h 1 m P.length hb (hmhi.le.trans (hb 2))
  have hc' : ∀ i, P.getVert (h' i)=f (extended p i) :=
    inserted_coordinates P (coordinates C) h p hc m z rfl
  have hf : Function.Injective f := extend_injective (coordinates C) (coordinates_injective C hC hl) z
    (fun i he ↦ hmout (by change z ∈ C.support; rw [he]; exact C.getVert_mem_support _))
  have hmiss' : f 6 ∉ P.support := by
    change coordinates C 6 ∉ P.support
    rwa [coordinates_last C hl]
  have ha : ∀ i : Fin 7, G.Adj (f i.castSucc) (f (next i).castSucc) := by
    intro i
    simpa only [f,Fin.lastCases_castSucc,next,HeptagonRoutes.next] using coordinates_adj C hl i
  have hCe : cycleEdges f=C.toSubgraph.edgeSet := by
    rw [coordinates_edges C hl]
    simp only [cycleEdges,f,Fin.lastCases_castSucc,next,HeptagonRoutes.next]
  have havoid (i : Fin 7) : s(f i.castSucc,f (next i).castSucc) ∉ P.edges := by
    intro he
    have hCedge : s(f i.castSucc,f (next i).castSucc) ∈ C.toSubgraph.edgeSet := by
      rw [←hCe]
      exact Set.mem_iUnion.mpr ⟨i,rfl⟩
    exact Set.disjoint_left.mp hd hCedge (P.mem_edges_toSubgraph.mpr he)
  obtain ⟨X,Y,hX,hY,hdXY,heXY,hsX,hsY⟩ := ordered_absorption p f P h' hh' hc' ha
    hex hmiss' hpinj hf hp hb' havoid
  have hstart : f (p 0).castSucc.castSucc=P.getVert (h 0) := by
    simpa only [f,Fin.lastCases_castSucc] using (hc 0).symm
  have hfinish : f (p 5).castSucc.castSucc=P.getVert (h 5) := by
    simpa only [f,Fin.lastCases_castSucc] using (hc 5).symm
  let X' := X.copy hstart rfl
  let Y' := Y.copy hfinish rfl
  have hXe : X'.toSubgraph=X.toSubgraph := NormalTrailSystem.walk_copy_subgraph X _ _
  have hYe : Y'.toSubgraph=Y.toSubgraph := NormalTrailSystem.walk_copy_subgraph Y _ _
  have hmidE := interval_edges_congr P (hh'.monotone (Fin.zero_le (6 : Fin 7)))
    (hh.monotone (Fin.zero_le (5 : Fin 6))) (insertCut_zero h 1 m) (insertCut_last h 1 m)
  have hmidS := interval_support_congr P (hh'.monotone (Fin.zero_le (6 : Fin 7)))
    (hh.monotone (Fin.zero_le (5 : Fin 6))) (insertCut_zero h 1 m) (insertCut_last h 1 m)
  rw [hmidE,hCe] at heXY
  rw [hmidS] at hsX hsY
  apply restore_two_on_path P hp (hh.monotone (Fin.zero_le _)) (hb 5) X' Y'
    (by simpa only [X',Walk.isPath_copy] using hX) (by simpa only [Y',Walk.isPath_copy] using hY)
    (by simpa only [hXe,hYe] using hdXY) C.toSubgraph.edgeSet hd
    (by simpa only [hXe,hYe] using heXY)
  · simpa only [X',Walk.support_copy] using hsX
  · simpa only [Y',Walk.support_copy] using hsY

end HeptagonExceptional

/- A seven-cycle and an intersecting path are absorbable if a cycle vertex is missing. -/
namespace HeptagonMissing
open SimpleGraph TriangleAbsorption
open PathIntervals OrderedPathPieces
open HeptagonRoutes HeptagonCoordinates
open HeptagonPieceSystem PathRestoreIntersection
open scoped Classical
set_option maxHeartbeats 2200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {r a b : V}

lemma ordered_first_absorption (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath) (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hmiss : r ∉ P.support)
    (h : Fin 6 → ℕ) (p : Fin 6 → Fin 6) (hh : StrictMono h) (hpinj : Function.Injective p)
    (hb : ∀ i, h i ≤ P.length) (hc : ∀ i, P.getVert (h i)=coordinates C (p i).castSucc)
    (hfirst : adjacent (p 0) (p 1)) : TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  have h01 : h 0 ≤ h 1 := hh.monotone (by decide)
  have hform := split_interval P h01 (hb 1)
  have hA : ∀ x ∈ (P.take (h 0)).support, x ∈ C.support → x=P.getVert (h 0) := by
    intro x hx hxC
    obtain ⟨m,hm,hxm⟩ := (take_support P (hb 0) x).mp hx
    obtain ⟨j,hj⟩ := ordered_visit_position C hl P hp hmiss h p hpinj hb hc
      (hm.trans (hb 0)) (hxm ▸ hxC)
    have hlo := hh.monotone (Fin.zero_le j)
    have hm0 : m=h 0 := by omega
    exact hm0 ▸ hxm
  have hB : ∀ x ∈ (interval P (h 0) (h 1) h01).support, x ∈ C.support →
      x=P.getVert (h 0) ∨ x=P.getVert (h 1) := by
    intro x hx hxC
    obtain ⟨m,hm0,hm1,hxm⟩ := (interval_support P h01 (hb 1) x).mp hx
    obtain ⟨j,hj⟩ := ordered_visit_position C hl P hp hmiss h p hpinj hb hc
      (hm1.trans (hb 1)) (hxm ▸ hxC)
    have hj1 : j ≤ (1 : Fin 6) := hh.le_iff_le.mp (by omega)
    have hvj : j.val ≤ 1 := hj1
    by_cases hj0 : j.val=0
    · have he : j=0 := Fin.ext hj0
      exact Or.inl (by rwa [hj,he] at hxm)
    · have he : j=1 := Fin.ext (show j.val=1 by omega)
      exact Or.inr (by rwa [hj,he] at hxm)
  have hadj : C.toSubgraph.Adj (P.getVert (h 0)) (P.getVert (h 1)) := by
    rw [hc 0,hc 1]
    exact coordinates_cycle_adj C hl _ _ hfirst
  have hcover := CycleFirstVisits.cycle_adjacent_first_absorption C hC (P.take (h 0))
    (interval P (h 0) (h 1) h01) (P.drop (h 1)) (hform ▸ hp) hA hB hadj (hform ▸ hd.symm)
  simpa only [←hform,Set.union_comm] using hcover

lemma nonabsorbable_outer_chords (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath) (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hno : ¬TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet))
    (hmiss : r ∉ P.support)
    (h : Fin 6 → ℕ) (p : Fin 6 → Fin 6) (hh : StrictMono h) (hpinj : Function.Injective p)
    (hb : ∀ i, h i ≤ P.length) (hc : ∀ i, P.getVert (h i)=coordinates C (p i).castSucc) :
    ¬adjacent (p 0) (p 1) ∧ ¬adjacent (p 4) (p 5) := by
  constructor
  · exact fun ha ↦ hno (ordered_first_absorption C hC hl P hp hd hmiss h p hh hpinj hb hc ha)
  · intro ha
    let h' (i : Fin 6) := P.length-h i.rev
    let p' (i : Fin 6) := p i.rev
    have hh' : StrictMono h' := by
      intro i j hij
      have hlt := hh (Fin.rev_lt_rev.mpr hij)
      have hi := hb i.rev
      have hj := hb j.rev
      change P.length-h i.rev < P.length-h j.rev
      omega
    have hp' : Function.Injective p' := hpinj.comp Fin.rev_injective
    have hb' (i : Fin 6) : h' i ≤ P.reverse.length := by simp only [h',Walk.length_reverse]; omega
    have hc' (i : Fin 6) : P.reverse.getVert (h' i)=coordinates C (p' i).castSucc := by
      rw [Walk.getVert_reverse]
      have he : P.length-h' i=h i.rev := by dsimp [h']; have hi := hb i.rev; omega
      rw [he]
      exact hc i.rev
    have ha' : adjacent (p' 0) (p' 1) := by
      change adjacent (p 5) (p 4)
      exact ha.elim Or.inr Or.inl
    have he := ordered_first_absorption C hC hl P.reverse hp.reverse (by simpa using hd) (by simpa using hmiss)
      h' p' hh' hp' hb' hc' ha'
    exact hno (by simpa using he)

lemma six_visit_absorption (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath) (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hmiss : r ∉ P.support) (hvisit : ∀ i : Fin 6, coordinates C i.castSucc ∈ P.support) :
    TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  by_contra hno
  have hf := coordinates_injective C hC hl
  obtain ⟨h,p,hh,hpinj,hb,hc⟩ := HexagonExcursionCoordinates.ordered_vertices P
    (fun i : Fin 6 ↦ coordinates C i.castSucc) (hf.comp (Fin.castSucc_injective 6)) hvisit
  obtain ⟨hfirst,hlast⟩ := nonabsorbable_outer_chords C hC hl P hp hd hno hmiss h p hh hpinj hb hc
  by_cases hex : Exceptional p
  · exact (hno (HeptagonExceptional.exceptional_absorption C hC hl P hp hd hmiss
      h p hh hpinj hb hc hex)).elim
  have ha := coordinates_adj C hl
  have hmiss' : coordinates C 6 ∉ P.support := by rwa [coordinates_last C hl]
  have havoid (i : Fin 7) : s(coordinates C i,coordinates C (next i)) ∉ P.edges := by
    intro he
    have heC : s(coordinates C i,coordinates C (next i)) ∈ C.toSubgraph.edgeSet := by
      rw [coordinates_edges C hl]
      exact Set.mem_iUnion.mpr ⟨i,rfl⟩
    exact Set.disjoint_left.mp hd heC (P.mem_edges_toSubgraph.mpr he)
  obtain ⟨X,Y,hX,hY,hXY,hE,hXs,hYs⟩ := ordered_absorption p (coordinates C) P h hh hc ha
    hmiss' hpinj hf hp hfirst hlast hex hb havoid
  have hCe : cycleEdges (coordinates C)=C.toSubgraph.edgeSet := (coordinates_edges C hl).symm
  rw [hCe] at hE
  let X' := X.copy (hc 0).symm rfl
  let Y' := Y.copy (hc 5).symm rfl
  have hXe : X'.toSubgraph=X.toSubgraph := NormalTrailSystem.walk_copy_subgraph X _ _
  have hYe : Y'.toSubgraph=Y.toSubgraph := NormalTrailSystem.walk_copy_subgraph Y _ _
  apply hno
  apply restore_two_on_path P hp (hh.monotone (Fin.zero_le _)) (hb 5) X' Y'
    (by simpa only [X',Walk.isPath_copy] using hX) (by simpa only [Y',Walk.isPath_copy] using hY)
    (by simpa only [hXe,hYe] using hXY) C.toSubgraph.edgeSet hd
    (by simpa only [hXe,hYe] using hE)
  · simpa only [X',Walk.support_copy] using hXs
  · simpa only [Y',Walk.support_copy] using hYs

lemma missing_start_absorption (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath) (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hmiss : r ∉ P.support) (hinter : ∃ x ∈ P.support, x ∈ C.support) :
    TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  by_cases hsmall : (C.toSubgraph.verts ∩ P.toSubgraph.verts).ncard ≤ 5
  · exact CycleIntersectionSix.five_intersection_absorption C hC (by omega) P hp hsmall hinter hd
  apply six_visit_absorption C hC hl P hp hd hmiss
  intro i
  by_contra himiss
  have hir : coordinates C i.castSucc ≠ r := by
    intro he
    have hh := coordinates_injective C hC hl (he.trans (coordinates_last C hl).symm)
    have hv := congrArg Fin.val hh
    norm_num at hv
    omega
  have hd' : Disjoint (C.toSubgraph.verts ∩ P.toSubgraph.verts) {r,coordinates C i.castSucc} := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases (show x=r ∨ x=coordinates C i.castSucc by simpa using hy) with rfl|rfl
    · exact hmiss (P.mem_verts_toSubgraph.mp hx.2)
    · exact himiss (P.mem_verts_toSubgraph.mp hx.2)
  have hsub : (C.toSubgraph.verts ∩ P.toSubgraph.verts) ∪ {r,coordinates C i.castSucc} ⊆ C.toSubgraph.verts := by
    intro x hx
    rcases hx with hx|hx
    · exact hx.1
    · rcases (show x=r ∨ x=coordinates C i.castSucc by simpa using hx) with rfl|rfl
      · exact C.start_mem_verts_toSubgraph
      · exact C.mem_verts_toSubgraph.mpr (C.getVert_mem_support _)
  have hc := Set.ncard_mono hsub
  rw [Set.ncard_union_eq hd',Set.ncard_pair hir.symm,Walk.verts_toSubgraph,cycle_support_ncard hC,hl] at hc
  simp only [Walk.verts_toSubgraph] at hsmall hc
  omega

lemma missing_vertex_absorption (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath)
    (hmiss : ∃ x ∈ C.support, x ∉ P.support) (hinter : ∃ x ∈ P.support, x ∈ C.support)
    (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet) :
    TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  obtain ⟨x,hxC,hxP⟩ := hmiss
  let D := C.rotate hxC
  have hD : D.toSubgraph=C.toSubgraph := C.toSubgraph_rotate hxC
  have hDl : D.length=7 := by
    have hh := congrArg Walk.length (C.take_spec hxC)
    simpa only [D,Walk.rotate,Walk.length_append,hl,Nat.add_comm] using hh
  have hint : ∃ y ∈ P.support, y ∈ D.support := by
    obtain ⟨y,hyP,hyC⟩ := hinter
    exact ⟨y,hyP,by rwa [←Walk.mem_verts_toSubgraph,hD,Walk.mem_verts_toSubgraph]⟩
  have hh := missing_start_absorption D (hC.rotate hxC) hDl P hp (by rw [hD]; exact hd) hxP hint
  simpa only [hD] using hh

lemma small_intersection_absorption (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (P : G.Walk a b) (hp : P.IsPath)
    (hsmall : (C.toSubgraph.verts ∩ P.toSubgraph.verts).ncard ≤ 6)
    (hinter : ∃ x ∈ P.support, x ∈ C.support)
    (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet) :
    TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  apply missing_vertex_absorption C hC hl P hp _ hinter hd
  by_contra! hall
  have hsub : C.toSubgraph.verts ⊆ P.toSubgraph.verts := by
    intro x hx
    exact P.mem_verts_toSubgraph.mpr (hall x (C.mem_verts_toSubgraph.mp hx))
  rw [Set.inter_eq_left.mpr hsub,Walk.verts_toSubgraph,cycle_support_ncard hC,hl] at hsmall
  omega

end HeptagonMissing

/- Six shared vertices suffice for absorption on cycles of length at least seven. -/
namespace CycleIntersectionSeven
open SimpleGraph
open QuotaTrails QuotaSurgery TriangleAbsorption
open BridgeGlue PentagonIntersection
open scoped Classical
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma missing_ear_reduction {a b r u v : V} (hru : G.Adj r u) (hvr : G.Adj v r)
    (R : G.Walk u v) (hRlen : 6 ≤ R.length)
    (hc : (Walk.cons hru (R.concat hvr)).IsCycle)
    (P : G.Walk a b) (hp : P.IsPath) (hrP : r ∉ P.support)
    (hinter : ∃ x ∈ P.support, x ∈ (Walk.cons hru (R.concat hvr)).support)
    (hd : Disjoint (Walk.cons hru (R.concat hvr)).toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hsmall : ((Walk.cons hru (R.concat hvr)).toSubgraph.verts ∩ P.toSubgraph.verts).ncard ≤ 6)
    (ih : ∀ (H : SimpleGraph V) {s a' b' : V} (C' : H.Walk s s) (P' : H.Walk a' b'),
      C'.IsCycle → P'.IsPath → 7 ≤ C'.length → C'.length < R.length+2 →
      (C'.toSubgraph.verts ∩ P'.toSubgraph.verts).ncard ≤ 6 →
      (∃ x ∈ P'.support, x ∈ C'.support) →
      Disjoint C'.toSubgraph.edgeSet P'.toSubgraph.edgeSet →
      TwoPathCover (G := H) (C'.toSubgraph.edgeSet ∪ P'.toSubgraph.edgeSet)) :
    TwoPathCover (G := G)
      ((Walk.cons hru (R.concat hvr)).toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  classical
  let C := Walk.cons hru (R.concat hvr)
  have hRc : (R.concat hvr).IsPath := (Walk.cons_isCycle_iff _ hru).mp hc |>.1
  have hRp : R.IsPath := (Walk.concat_isPath_iff hvr).mp hRc |>.1
  have hrR : r ∉ R.support := (Walk.concat_isPath_iff hvr).mp hRc |>.2
  have huv : u ≠ v := by
    intro hh
    subst v
    have hnil := (Walk.isPath_iff_eq_nil R).mp hRp
    simp [hnil] at hRlen
  have heR : s(u,v) ∉ R.edges := fun hh ↦ by
    have hh' := endpoint_edge_forces_length_one R hRp hh
    omega
  have hdR : Disjoint R.toSubgraph.edgeSet P.toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hf
    apply Set.disjoint_left.mp hd _ hf
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_concat,List.mem_cons,
      List.concat_eq_append,List.mem_append]
    exact Or.inr (Or.inl (R.mem_edges_toSubgraph.mp he))
  have hCe : C.toSubgraph.edgeSet={s(u,r),s(r,v)} ∪ R.toSubgraph.edgeSet := by
    ext e
    simp only [C,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_concat,List.mem_cons,
      List.concat_eq_append,List.mem_append,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,
      Sym2.eq_swap (a := r) (b := u),Sym2.eq_swap (a := v) (b := r)]
    tauto
  by_cases heP : s(u,v) ∈ P.edges
  · have huvG : G.Adj u v := P.edges_subset_edgeSet heP
    obtain ⟨hc',Q,hQ,hsep,hcover,hlen⟩ :=
      CycleEar.cycle_ear_exchange hru hvr R hc P hp huvG heP hrP hd
    have hrC' : r ∉ (Walk.cons huvG R.reverse).support := by
      simp only [Walk.support_cons,Walk.support_reverse,List.mem_cons,List.mem_reverse,not_or]
      exact ⟨hru.ne,hrR⟩
    have huQ : u ∈ Q.support := by
      have he : s(r,u) ∈ (Walk.cons huvG R.reverse).toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet := by
        rw [hcover]
        left
        simp
      rcases he with he|he
      · exact (hrC' (Walk.mem_support_of_mem_edges
          ((Walk.cons huvG R.reverse).mem_edges_toSubgraph.mp he) (by simp))).elim
      · exact Walk.mem_support_of_mem_edges (Q.mem_edges_toSubgraph.mp he) (by simp)
    have hsmall' : ((Walk.cons huvG R.reverse).toSubgraph.verts ∩ Q.toSubgraph.verts).ncard ≤ 6 := by
      apply (Set.ncard_le_ncard (s := (Walk.cons huvG R.reverse).toSubgraph.verts ∩ Q.toSubgraph.verts)
        (t := C.toSubgraph.verts ∩ P.toSubgraph.verts) ?_).trans hsmall
      intro z hz
      have hzC' : z ∈ (Walk.cons huvG R.reverse).support := by simpa only [Walk.mem_verts_toSubgraph] using hz.1
      have hzQ : z ∈ Q.support := by simpa only [Walk.mem_verts_toSubgraph] using hz.2
      have hzr : z ≠ r := fun hh ↦ hrC' (hh ▸ hzC')
      have hzR : z ∈ R.support := by
        rcases (show z=u ∨ z ∈ R.support by simpa only [Walk.support_cons,Walk.support_reverse,List.mem_cons,List.mem_reverse] using hzC') with rfl|hz
        · exact R.start_mem_support
        · exact hz
      have hzC : z ∈ C.toSubgraph.verts := by
        simp only [C,Walk.mem_verts_toSubgraph,Walk.support_cons,Walk.support_concat,
          List.mem_cons,List.concat_eq_append,List.mem_append]
        exact Or.inr (Or.inl hzR)
      refine ⟨hzC,?_⟩
      rw [Walk.mem_verts_toSubgraph]
      rcases Walk.mem_support_iff_exists_mem_edges.mp hzQ with rfl|⟨e,heQ,hze⟩
      · exact P.end_mem_support
      · have hE : e ∈ C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet := by
          rw [←hcover]; exact Or.inr (Q.mem_edges_toSubgraph.mpr heQ)
        rcases hE with hEC|hEP
        · rw [hCe] at hEC
          rcases hEC with hEar|hER
          · rcases (show e=s(u,r) ∨ e=s(r,v) by simpa using hEar) with rfl|rfl
            · have hzu : z=u := (Sym2.mem_iff.mp hze).resolve_right hzr
              subst z
              exact P.fst_mem_support_of_mem_edges heP
            · have hzv : z=v := (Sym2.mem_iff.mp hze).resolve_left hzr
              subst z
              exact P.snd_mem_support_of_mem_edges heP
          · apply False.elim
            apply Set.disjoint_left.mp hsep _ (Q.mem_edges_toSubgraph.mpr heQ)
            simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_reverse,List.mem_cons,List.mem_reverse]
            exact Or.inr (R.mem_edges_toSubgraph.mp hER)
        · exact Walk.mem_support_of_mem_edges (P.mem_edges_toSubgraph.mp hEP) hze
    have hh := ih G (Walk.cons huvG R.reverse) Q hc' hQ
      (by simp only [Walk.length_cons,Walk.length_reverse]; omega)
      (by simp only [Walk.length_cons,Walk.length_reverse]; omega) hsmall'
      ⟨u,huQ,(Walk.cons huvG R.reverse).start_mem_support⟩ hsep
    simpa only [hcover] using hh
  · let H := within G ({r}ᶜ : Set V) ⊔ edge u v
    have hRle : R.toSubgraph.spanningCoe ≤ H := by
      intro x y hxy
      apply Or.inl
      refine ⟨R.toSubgraph.adj_sub hxy,?_,?_⟩
      · rintro rfl
        exact hrR (Walk.mem_support_of_adj_toSubgraph hxy)
      · rintro rfl
        exact hrR (Walk.mem_support_of_adj_toSubgraph hxy.symm)
    have hPle : P.toSubgraph.spanningCoe ≤ H := by
      intro x y hxy
      apply Or.inl
      refine ⟨P.toSubgraph.adj_sub hxy,?_,?_⟩
      · rintro rfl
        exact hrP (Walk.mem_support_of_adj_toSubgraph hxy)
      · rintro rfl
        exact hrP (Walk.mem_support_of_adj_toSubgraph hxy.symm)
    have hRE : ∀ e ∈ R.edges, e ∈ H.edgeSet := fun e he ↦
      edgeSet_mono hRle (R.mem_edges_toSubgraph.mpr he)
    have hPE : ∀ e ∈ P.edges, e ∈ H.edgeSet := fun e he ↦
      edgeSet_mono hPle (P.mem_edges_toSubgraph.mpr he)
    let R' := R.transfer H hRE
    let P' := P.transfer H hPE
    have huvH : H.Adj u v := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,huv⟩)
    let C' := Walk.cons huvH R'.reverse
    have hc' : C'.IsCycle := (Walk.cons_isCycle_iff _ huvH).mpr
      ⟨(hRp.transfer hRE).reverse,by simpa only [R',Walk.edges_reverse,Walk.edges_transfer,List.mem_reverse] using heR⟩
    have hC'e : C'.toSubgraph.edgeSet={s(u,v)} ∪ R.toSubgraph.edgeSet := by
      ext e
      simp only [C',R',Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_reverse,
        Walk.edges_transfer,List.mem_cons,List.mem_reverse,Set.mem_union,Set.mem_singleton_iff]
    have hP'e : P'.toSubgraph.edgeSet=P.toSubgraph.edgeSet := by
      ext e
      simp only [P',Walk.mem_edges_toSubgraph,Walk.edges_transfer]
    have hsep : Disjoint C'.toSubgraph.edgeSet P'.toSubgraph.edgeSet := by
      rw [hC'e,hP'e]
      apply disjoint_sup_left.mpr
      refine ⟨Set.disjoint_left.mpr ?_,hdR⟩
      rintro e rfl he
      exact heP (P.mem_edges_toSubgraph.mp he)
    have hint : ∃ x ∈ P'.support, x ∈ C'.support := by
      obtain ⟨x,hxP,hxC⟩ := hinter
      have hxr : x ≠ r := fun hh ↦ hrP (hh ▸ hxP)
      have hxR : x ∈ R.support := by
        simpa only [Walk.support_cons,Walk.support_concat,List.concat_eq_append,
          List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,hxr,false_or,or_false] using hxC
      refine ⟨x,by simpa only [P',Walk.support_transfer] using hxP,?_⟩
      simp only [C',R',Walk.support_cons,Walk.support_reverse,Walk.support_transfer,
        List.mem_cons,List.mem_reverse]
      exact Or.inr hxR
    have hsmall' : (C'.toSubgraph.verts ∩ P'.toSubgraph.verts).ncard ≤ 6 := by
      apply (Set.ncard_le_ncard (s := C'.toSubgraph.verts ∩ P'.toSubgraph.verts)
        (t := C.toSubgraph.verts ∩ P.toSubgraph.verts) ?_).trans hsmall
      intro z hz
      have hzC' : z=u ∨ z ∈ R.support := by
        simpa only [C',R',Walk.mem_verts_toSubgraph,Walk.support_cons,
          Walk.support_reverse,Walk.support_transfer,List.mem_cons,List.mem_reverse] using hz.1
      have hzC : z ∈ C.toSubgraph.verts := by
        simp only [C,Walk.mem_verts_toSubgraph,Walk.support_cons,Walk.support_concat,
          List.mem_cons,List.concat_eq_append,List.mem_append]
        rcases hzC' with rfl|hzR
        · exact Or.inr (Or.inl R.start_mem_support)
        · exact Or.inr (Or.inl hzR)
      exact ⟨hzC,by simpa only [P',Walk.mem_verts_toSubgraph,Walk.support_transfer] using hz.2⟩
    have hcover := ih H C' P' hc' (hp.transfer hPE)
      (by simp only [C',R',Walk.length_cons,Walk.length_reverse,Walk.length_transfer]; omega)
      (by simp only [C',R',Walk.length_cons,Walk.length_reverse,Walk.length_transfer]; omega)
      hsmall' hint hsep
    let ear : G.Walk u v := .cons hru.symm (.cons hvr.symm .nil)
    have hEar : ear.IsPath := by simp [ear,Walk.cons_isPath_iff,hru.ne.symm,hvr.ne.symm,huv]
    have hrest : H.deleteEdges {s(u,v)} ≤ G := by
      intro x y hxy
      have hh : H.Adj x y ∧ s(x,y) ≠ s(u,v) := by simpa only [deleteEdges_adj,Set.mem_singleton_iff] using hxy
      rcases hh.1 with hh'|hh'
      · exact hh'.1
      · exact (hh.2 ((adj_edge ..).mp hh').1.symm).elim
    have hrH : r ∉ H.support := by
      intro hh
      obtain ⟨x,hx⟩ := (H.mem_support).mp hh
      rcases hx with hx|hx
      · exact hx.2.1 rfl
      · have hx' := (edge_adj ..).mp hx
        exact hx'.1.elim (fun hh ↦ hru.ne hh.1) (fun hh ↦ hvr.ne hh.1.symm)
    have hf : ∀ x ∈ ear.support, x ≠ u → x ≠ v → x ∉ H.support := by
      intro x hx hxu hxv
      have hxr : x=r := by simpa [ear,Walk.support,hxu,hxv] using hx
      subst x
      exact hrH
    have he0 : s(u,v) ∈ C'.toSubgraph.edgeSet ∪ P'.toSubgraph.edgeSet := by
      rw [hC'e]; exact Or.inl (Or.inl rfl)
    have hh := expand_pair ear hEar hrest hf _ he0 hcover
    have hEarE : ear.toSubgraph.edgeSet=({s(u,r),s(r,v)} : Set (Sym2 V)) := by
      ext e
      simp only [ear,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,
        List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff]
    have heR' : s(u,v) ∉ R.toSubgraph.edgeSet := by simpa only [Walk.mem_edges_toSubgraph] using heR
    have heP' : s(u,v) ∉ P.toSubgraph.edgeSet := by simpa only [Walk.mem_edges_toSubgraph] using heP
    have heEar : s(u,v) ∉ ear.toSubgraph.edgeSet := fun he ↦ by
      have hl := endpoint_edge_forces_length_one ear hEar (ear.mem_edges_toSubgraph.mp he)
      simp [ear] at hl
    have hEq : ((C'.toSubgraph.edgeSet ∪ P'.toSubgraph.edgeSet) \ {s(u,v)}) ∪ ear.toSubgraph.edgeSet =
        C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet := by
      rw [hC'e,hP'e,hCe,←hEarE]
      ext e
      by_cases he : e=s(u,v)
      · subst e
        simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff,not_true_eq_false,
          and_false,heR',heP',heEar,or_false]
      · simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff,he,not_false_eq_true,and_true,false_or]
        tauto
    simpa only [hEq] using hh


lemma six_intersection_absorption {G : SimpleGraph V} {a b r : V} (C : G.Walk r r) (hc : C.IsCycle)
    (hlarge : 7 ≤ C.length) (P : G.Walk a b) (hp : P.IsPath)
    (hsmall : (C.toSubgraph.verts ∩ P.toSubgraph.verts).ncard ≤ 6)
    (hinter : ∃ x ∈ P.support, x ∈ C.support)
    (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet) :
    TwoPathCover (G := G) (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  classical
  by_cases hl : C.length=7
  · exact HeptagonMissing.small_intersection_absorption C hc hl P hp hsmall hinter hd
  have hmiss : ∃ x ∈ C.support, x ∉ P.support := by
    by_contra! hall
    have hsub : C.toSubgraph.verts ⊆ P.toSubgraph.verts := by
      intro x hx
      rw [Walk.mem_verts_toSubgraph] at hx ⊢
      exact hall x hx
    have he : C.toSubgraph.verts ∩ P.toSubgraph.verts=C.toSubgraph.verts := Set.inter_eq_left.mpr hsub
    rw [he,Walk.verts_toSubgraph,cycle_support_ncard hc] at hsmall
    omega
  obtain ⟨x,hxC,hxP⟩ := hmiss
  let D := C.rotate hxC
  have hD : D.toSubgraph=C.toSubgraph := C.toSubgraph_rotate hxC
  have hDl : D.length=C.length := by
    have hh := congrArg Walk.length (C.take_spec hxC)
    simpa only [D,Walk.rotate,Walk.length_append,Nat.add_comm] using hh
  obtain ⟨u,v,hxu,hvx,R,hform⟩ := CycleEar.cycle_two_spokes D (hc.rotate hxC)
  have hRtot : R.length+2=C.length := by
    rw [hform] at hDl
    simp only [Walk.length_cons,Walk.length_concat] at hDl
    omega
  have hsmallD : (D.toSubgraph.verts ∩ P.toSubgraph.verts).ncard ≤ 6 := by rwa [hD]
  have hinterD : ∃ z ∈ P.support, z ∈ D.support := by
    obtain ⟨z,hzP,hzC⟩ := hinter
    refine ⟨z,hzP,?_⟩
    rwa [←Walk.mem_verts_toSubgraph,hD,Walk.mem_verts_toSubgraph]
  have hdD : Disjoint D.toSubgraph.edgeSet P.toSubgraph.edgeSet := by rwa [hD]
  have hh := missing_ear_reduction hxu hvx R (by omega) (hform ▸ hc.rotate hxC) P hp hxP
    (by simpa only [hform] using hinterD) (hform ▸ hdD) (hform ▸ hsmallD) (by
      intro H s a' b' C' P' hC' hP' hlarge' hlen' hsmall' hint' hdis'
      exact six_intersection_absorption (G := H) C' hC' hlarge' P' hP' hsmall' hint' hdis')
  simpa only [←hform,hD] using hh
termination_by C.length

decreasing_by
  omega

lemma maximal_cycle_intersection_ge_seven {k : ℕ} (T : TrailFamily G k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (i j : Fin k) (hij : i ≠ j)
    {r : V} (C : G.Walk r r) (hC : C.IsCycle) (hl : 7 ≤ C.length)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (hj : (T.walk j).IsPath)
    (hinter : ∃ x ∈ (T.walk j).support, x ∈ C.support) :
    7 ≤ (C.toSubgraph.verts ∩ (T.walk j).toSubgraph.verts).ncard := by
  by_contra! hn
  apply maximal_cycle_not_absorbable T hm i j hij C hC hi hj
  exact six_intersection_absorption C hC hl (T.walk j) hj (by omega) hinter
    (by rw [←hi]; exact T.disjoint hij)

lemma single_defect_cycle_intersection_ge_seven {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (i j : Fin k) (hij : i ≠ j)
    {r : V} (C : G.Walk r r) (hC : C.IsCycle) (hl : 7 ≤ C.length)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hinter : ∃ x ∈ (T.walk j).support, x ∈ C.support) :
    7 ≤ (C.toSubgraph.verts ∩ (T.walk j).toSubgraph.verts).ncard := by
  have hj := (T.one_defect_other_paths hs i (CycleEar.cycle_member_not_path T i C hC hi)).2 j hij.symm
  exact maximal_cycle_intersection_ge_seven T hm i j hij C hC hl hi hj hinter

lemma maximum_heptagon_carrier_contains {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (i j : Fin k) (hij : i ≠ j)
    {r : V} (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hinter : ∃ x ∈ (T.walk j).support, x ∈ C.support) :
    ∀ x ∈ C.support, x ∈ (T.walk j).support := by
  have hb := single_defect_cycle_intersection_ge_seven T hs hm i j hij C hC (by omega) hi hinter
  have he : C.toSubgraph.verts ∩ (T.walk j).toSubgraph.verts=C.toSubgraph.verts := by
    apply Set.eq_of_subset_of_ncard_le Set.inter_subset_left
    rw [Walk.verts_toSubgraph,cycle_support_ncard hC,hl]
    simpa only [Walk.verts_toSubgraph] using hb
  intro x hx
  have hh : x ∈ C.toSubgraph.verts ∩ (T.walk j).toSubgraph.verts := by
    rw [he]; exact C.mem_verts_toSubgraph.mpr hx
  exact (T.walk j).mem_verts_toSubgraph.mp hh.2

lemma failure_cycle_intersection_ge_seven {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (i j : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hij : i ≠ j) {r : Fin n}
    (C : G.Walk r r) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hinter : ∃ x ∈ (T.walk j).support, x ∈ C.support) :
    7 ≤ (C.toSubgraph.verts ∩ (T.walk j).toSubgraph.verts).ncard := by
  have hl := HexagonExclusion.whole_cycle_length_ge_seven hsmall hG hfail T hs hm i C hC hi
  exact single_defect_cycle_intersection_ge_seven T hs hm i j hij C hC hl hi hinter

end CycleIntersectionSeven


end Erdos583Work
