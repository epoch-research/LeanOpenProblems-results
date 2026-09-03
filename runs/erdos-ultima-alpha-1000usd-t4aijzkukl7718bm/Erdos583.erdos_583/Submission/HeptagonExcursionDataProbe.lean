import Submission.Work

/-! Finite certificates for a heptagon with a selected split path link. -/
namespace Erdos583HeptagonExcursionRoutesDevelopment
open SimpleGraph Erdos583Work Erdos583Work.PieceRoutes
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option Elab.async false

def extended (p : Fin 7 → Fin 7) (d : Fin 6) (i : Fin 8) : Fin 8 :=
  if h : i.val ≤ d.val then (p ⟨i.val,by omega⟩).castSucc
  else if i.val=d.val+1 then 7 else (p ⟨i.val-1,by omega⟩).castSucc

def pieceSource (p : Fin 7 → Fin 7) (d : Fin 6) (e : Fin 14) : Fin 8 :=
  if h : e.val < 7 then (⟨e.val,h⟩ : Fin 7).castSucc
  else extended p d ⟨e.val-7,by omega⟩

def pieceTarget (p : Fin 7 → Fin 7) (d : Fin 6) (e : Fin 14) : Fin 8 :=
  if e.val < 7 then (⟨(e.val+1)%7,Nat.mod_lt _ (by decide)⟩ : Fin 7).castSucc
  else extended p d ⟨e.val-6,by omega⟩

def adjacent (a b : Fin 7) : Prop := (a.val+1)%7=b.val ∨ (b.val+1)%7=a.val
instance (a b : Fin 7) : Decidable (adjacent a b) := inferInstanceAs (Decidable (_ ∨ _))

abbrev Steps := List (Fin 14 × Bool)

def Valid (p : Fin 7 → Fin 7) (d : Fin 6) (v : Steps × Steps) : Prop :=
  Route.compatible (s := pieceSource p d) (t := pieceTarget p d) (p 0).castSucc 7 v.1=true ∧
  Route.compatible (s := pieceSource p d) (t := pieceTarget p d) (p 6).castSucc 7 v.2=true ∧
  ((p 0).castSucc :: v.1.map (fun ed ↦ target (pieceSource p d) (pieceTarget p d) ed.1 ed.2)).Nodup ∧
  ((p 6).castSucc :: v.2.map (fun ed ↦ target (pieceSource p d) (pieceTarget p d) ed.1 ed.2)).Nodup ∧
  (∀ e : Fin 14, e ∈ v.1.map Prod.fst → e ∉ v.2.map Prod.fst) ∧
  ∀ e : Fin 14, e ∈ v.1.map Prod.fst ∨ e ∈ v.2.map Prod.fst

instance (p : Fin 7 → Fin 7) (d : Fin 6) (v : Steps × Steps) : Decidable (Valid p d v) := by
  unfold Valid
  infer_instance

def code (p : Fin 7 → Fin 7) (d : Fin 6) : ℕ :=
  (p 0).val+7*(p 1).val+49*(p 2).val+343*(p 3).val+2401*(p 4).val+16807*(p 5).val+
    117649*(p 6).val+823543*d.val

def chosenGap (p : Fin 7 → Fin 7) (d : Fin 6) : Fin 6 :=
  if adjacent (p 1) (p 2) then 1 else if adjacent (p 2) (p 3) then 2
  else if adjacent (p 3) (p 4) then 3 else if adjacent (p 4) (p 5) then 4 else d

def GoodGap (p : Fin 7 → Fin 7) (d : Fin 6) : Prop := chosenGap p d=d
instance (p : Fin 7 → Fin 7) (d : Fin 6) : Decidable (GoodGap p d) := inferInstanceAs (Decidable (_ = _))

lemma chosenGap_good (p : Fin 7 → Fin 7) (d : Fin 6) : GoodGap p (chosenGap p d) := by
  unfold GoodGap chosenGap
  split_ifs <;> rfl

lemma chosenGap_spec (p : Fin 7 → Fin 7) (d : Fin 6) :
    chosenGap p d=d ∨ adjacent (p (chosenGap p d).castSucc) (p (chosenGap p d).succ) := by
  unfold chosenGap
  split_ifs with h1 h2 h3 h4
  · exact Or.inr h1
  · exact Or.inr h2
  · exact Or.inr h3
  · exact Or.inr h4
  · exact Or.inl rfl

inductive CertificateTree where
  | empty : CertificateTree
  | node (key : ℕ) (value : Steps × Steps) (left right : CertificateTree) : CertificateTree

def CertificateTree.lookup (t : CertificateTree) (key : ℕ) : Option (Steps × Steps) :=
  match t with
  | .empty => none
  | .node k v l r => if key=k then some v else if key<k then l.lookup key else r.lookup key

noncomputable def certificates : CertificateTree := (.node 2113643 ([(0,true),(8,false),(4,true),(5,true),(13,true),(2,false),(10,false)],[(3,true),(7,false),(6,false),(12,false),(11,false),(1,false),(9,true)])
  (.node 1280008 ([(2,true),(13,false),(12,false),(0,false),(10,false),(4,false),(8,true)],[(3,true),(7,false),(1,false),(11,false),(6,false),(5,false),(9,false)])
    (.node 898648 ([(7,true),(4,false),(3,false),(11,false),(0,false),(6,false),(9,false)],[(13,false),(12,false),(2,false),(1,false),(10,false),(5,false),(8,true)])
      (.node 500745 ([(0,true),(12,false),(4,false),(3,false),(10,false),(9,false),(8,false)],[(13,false),(1,true),(2,true),(11,true),(5,true),(6,true),(7,true)])
        (.node 248637 ([(4,true),(5,true),(10,true),(2,false),(13,false),(0,true),(8,false)],[(1,false),(9,true),(6,true),(12,false),(11,false),(3,true),(7,true)])
          (.node 180315 ([(1,false),(13,false),(3,true),(4,true),(11,false),(6,false),(8,false)],[(0,false),(10,false),(9,false),(5,false),(12,true),(2,false),(7,true)])
            (.node 71535 ([(2,true),(3,true),(13,true),(0,true),(11,false),(5,true),(8,false)],[(6,false),(9,true),(10,true),(4,false),(12,false),(1,true),(7,true)])
              (.node 55095 ([(5,true),(6,true),(0,true),(12,true),(3,true),(9,false),(8,false)],[(13,false),(2,false),(1,false),(11,false),(10,false),(4,true),(7,true)])
                (.node 46743 ([(4,true),(11,false),(2,false),(1,false),(0,false),(6,false),(8,false)],[(13,false),(12,false),(5,true),(9,true),(10,true),(3,true),(7,true)])
                  (.node 45435 ([(5,true),(6,true),(13,false),(12,false),(3,false),(9,false),(8,false)],[(0,true),(1,true),(2,true),(10,true),(11,true),(4,true),(7,true)])
                    (.node 45351 ([(5,true),(6,true),(0,true),(1,true),(12,false),(3,false),(8,false)],[(13,false),(2,true),(9,true),(10,true),(11,true),(4,true),(7,true)])
                      (.node 43881 ([(5,true),(6,true),(0,true),(1,true),(12,false),(3,false),(8,false)],[(13,false),(2,true),(9,true),(10,true),(11,true),(4,true),(7,true)])
                        (.node 43833 ([(6,true),(0,true),(1,true),(12,false),(4,true),(9,false),(8,false)],[(13,false),(2,true),(3,true),(11,false),(10,false),(5,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 45363 ([(3,true),(11,false),(6,true),(13,false),(1,false),(9,false),(8,false)],[(0,true),(10,true),(5,false),(4,false),(12,true),(2,true),(7,true)])
                        .empty
                        .empty))
                    (.node 46203 ([(3,true),(4,true),(11,false),(1,true),(13,true),(6,false),(8,false)],[(0,true),(10,false),(9,false),(5,false),(12,true),(2,true),(7,true)])
                      (.node 46155 ([(4,true),(11,false),(0,false),(13,false),(2,true),(9,false),(8,false)],[(6,false),(5,false),(12,true),(1,false),(10,false),(3,true),(7,true)])
                        (.node 45459 ([(0,false),(13,false),(2,true),(3,true),(11,false),(5,false),(8,false)],[(6,false),(10,false),(9,false),(4,false),(12,true),(1,false),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 46731 ([(6,true),(0,true),(1,true),(12,false),(11,false),(3,true),(8,false)],[(13,false),(2,true),(10,false),(9,false),(4,true),(5,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 49479 ([(3,true),(10,false),(0,false),(13,false),(12,false),(5,false),(8,false)],[(6,false),(11,false),(4,true),(9,true),(1,true),(2,true),(7,true)])
                    (.node 49305 ([(4,true),(5,true),(11,false),(2,false),(13,true),(0,true),(8,false)],[(6,false),(12,true),(1,false),(9,true),(10,true),(3,true),(7,true)])
                      (.node 46971 ([(0,false),(13,false),(2,true),(10,false),(5,false),(4,false),(8,false)],[(6,false),(9,false),(3,false),(11,true),(12,true),(1,false),(7,true)])
                        (.node 46953 ([(4,true),(5,true),(10,true),(2,false),(13,true),(0,true),(8,false)],[(6,false),(9,false),(1,true),(12,false),(11,false),(3,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 49467 ([(5,true),(6,true),(13,false),(1,false),(10,true),(3,false),(8,false)],[(0,true),(9,false),(2,false),(12,false),(11,false),(4,true),(7,true)])
                        .empty
                        .empty))
                    (.node 54669 ([(6,true),(0,true),(11,false),(10,false),(2,true),(3,true),(8,false)],[(13,false),(12,false),(1,true),(9,false),(4,true),(5,true),(7,true)])
                      (.node 54507 ([(5,true),(6,true),(0,true),(11,false),(3,false),(2,false),(8,false)],[(13,false),(12,false),(1,true),(9,true),(10,true),(4,true),(7,true)])
                        .empty
                        .empty)
                      (.node 54681 ([(4,true),(10,false),(1,false),(12,true),(13,true),(6,false),(8,false)],[(0,true),(11,false),(5,true),(9,true),(2,true),(3,true),(7,true)])
                        .empty
                        .empty))))
                (.node 65385 ([(5,true),(6,true),(0,true),(10,false),(3,false),(2,false),(8,false)],[(13,false),(12,false),(11,false),(1,true),(9,true),(4,true),(7,true)])
                  (.node 63321 ([(6,true),(13,false),(2,false),(11,true),(4,false),(9,false),(8,false)],[(0,true),(1,true),(10,false),(3,false),(12,false),(5,true),(7,true)])
                    (.node 63081 ([(4,true),(5,true),(10,true),(0,false),(13,false),(2,false),(8,false)],[(6,false),(9,false),(1,false),(11,true),(12,true),(3,true),(7,true)])
                      (.node 63009 ([(2,true),(3,true),(4,true),(11,false),(0,false),(6,false),(8,false)],[(13,false),(12,false),(5,true),(9,true),(10,true),(1,true),(7,true)])
                        (.node 62985 ([(6,true),(0,true),(10,false),(4,true),(12,true),(2,false),(8,false)],[(13,false),(3,true),(9,false),(1,false),(11,true),(5,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 63093 ([(2,true),(12,false),(11,false),(0,false),(6,false),(9,false),(8,false)],[(13,false),(3,true),(4,true),(5,true),(10,true),(1,true),(7,true)])
                        .empty
                        .empty))
                    (.node 63417 ([(4,true),(5,true),(6,true),(13,false),(2,false),(1,false),(8,false)],[(0,true),(9,true),(10,true),(11,true),(12,true),(3,true),(7,true)])
                      (.node 63351 ([(0,false),(13,false),(2,false),(10,false),(4,true),(5,true),(8,false)],[(6,false),(9,true),(3,false),(12,false),(11,false),(1,false),(7,true)])
                        .empty
                        .empty)
                      (.node 63435 ([(0,false),(6,false),(5,false),(11,false),(2,true),(3,true),(8,false)],[(13,false),(12,false),(4,false),(9,true),(10,true),(1,false),(7,true)])
                        .empty
                        .empty)))
                  (.node 66333 ([(0,false),(6,false),(11,false),(3,false),(2,false),(9,false),(8,false)],[(13,false),(12,false),(5,false),(4,false),(10,false),(1,false),(7,true)])
                    (.node 65769 ([(4,true),(5,true),(6,true),(13,false),(2,false),(1,false),(8,false)],[(0,true),(9,true),(10,true),(11,true),(12,true),(3,true),(7,true)])
                      (.node 65721 ([(5,true),(6,true),(13,false),(2,false),(10,false),(9,false),(8,false)],[(0,true),(1,true),(11,true),(12,true),(3,true),(4,true),(7,true)])
                        (.node 65433 ([(4,true),(5,true),(12,true),(13,true),(0,true),(1,true),(8,false)],[(6,false),(11,false),(10,false),(9,false),(2,true),(3,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 66285 ([(2,true),(3,true),(10,false),(0,false),(6,false),(5,false),(8,false)],[(13,false),(12,false),(11,false),(4,true),(9,true),(1,true),(7,true)])
                        .empty
                        .empty))
                    (.node 70971 ([(5,true),(6,true),(13,false),(12,false),(11,false),(2,false),(8,false)],[(0,true),(1,true),(9,true),(10,true),(3,true),(4,true),(7,true)])
                      (.node 70923 ([(6,true),(0,true),(11,false),(3,true),(4,true),(9,false),(8,false)],[(13,false),(12,false),(1,true),(2,true),(10,false),(5,true),(7,true)])
                        .empty
                        .empty)
                      (.node 71487 ([(3,true),(4,true),(10,false),(1,false),(0,false),(6,false),(8,false)],[(13,false),(12,false),(11,false),(5,true),(9,true),(2,true),(7,true)])
                        .empty
                        .empty)))))
              (.node 90285 ([(6,true),(13,false),(4,false),(10,false),(1,true),(2,true),(8,false)],[(0,true),(9,false),(3,true),(11,true),(12,true),(5,true),(7,true)])
                (.node 74247 ([(5,true),(6,true),(13,false),(3,false),(2,false),(1,false),(8,false)],[(0,true),(9,true),(10,true),(11,true),(12,true),(4,true),(7,true)])
                  (.node 73905 ([(6,true),(13,false),(3,false),(10,true),(11,true),(1,false),(8,false)],[(0,true),(9,true),(2,false),(12,true),(4,true),(5,true),(7,true)])
                    (.node 73821 ([(6,true),(0,true),(1,true),(11,false),(4,false),(3,false),(8,false)],[(13,false),(12,false),(2,true),(9,true),(10,true),(5,true),(7,true)])
                      (.node 71871 ([(2,true),(3,true),(12,false),(0,false),(6,false),(5,false),(8,false)],[(13,false),(4,true),(9,true),(10,true),(11,true),(1,true),(7,true)])
                        (.node 71823 ([(3,true),(12,false),(0,false),(6,false),(10,false),(9,false),(8,false)],[(13,false),(4,true),(5,true),(11,true),(1,true),(2,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 73839 ([(3,true),(12,false),(11,false),(10,false),(0,false),(6,false),(8,false)],[(13,false),(4,true),(5,true),(9,true),(1,true),(2,true),(7,true)])
                        .empty
                        .empty))
                    (.node 74163 ([(5,true),(6,true),(13,false),(12,false),(1,false),(9,false),(8,false)],[(0,true),(10,true),(11,true),(2,true),(3,true),(4,true),(7,true)])
                      (.node 73935 ([(0,false),(13,false),(3,false),(2,false),(11,false),(5,true),(8,false)],[(6,false),(9,true),(10,true),(4,false),(12,false),(1,false),(7,true)])
                        .empty
                        .empty)
                      (.node 74175 ([(3,true),(12,false),(1,false),(0,false),(6,false),(5,false),(8,false)],[(13,false),(4,true),(9,true),(10,true),(11,true),(2,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 82749 ([(2,true),(3,true),(12,false),(6,true),(0,true),(9,false),(8,false)],[(13,false),(4,true),(5,true),(11,false),(10,false),(1,true),(7,true)])
                    (.node 82575 ([(3,true),(4,true),(10,true),(11,true),(6,true),(0,true),(8,false)],[(13,false),(12,false),(5,false),(9,false),(1,true),(2,true),(7,true)])
                      (.node 82161 ([(2,true),(3,true),(13,true),(0,true),(11,true),(5,false),(8,false)],[(6,false),(12,true),(4,true),(9,true),(10,true),(1,true),(7,true)])
                        (.node 74271 ([(0,false),(6,false),(10,false),(2,false),(12,true),(4,true),(8,false)],[(13,false),(3,false),(9,false),(5,true),(11,true),(1,false),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 82587 ([(0,false),(6,false),(11,false),(10,false),(4,false),(3,false),(8,false)],[(13,false),(12,false),(5,false),(9,false),(2,false),(1,false),(7,true)])
                        .empty
                        .empty))
                    (.node 87789 ([(2,true),(10,false),(6,true),(0,true),(12,true),(4,false),(8,false)],[(13,false),(5,true),(9,false),(3,false),(11,true),(1,true),(7,true)])
                      (.node 87777 ([(4,true),(5,true),(6,true),(0,true),(11,false),(2,false),(8,false)],[(13,false),(12,false),(1,true),(9,true),(10,true),(3,true),(7,true)])
                        .empty
                        .empty)
                      (.node 87951 ([(3,true),(4,true),(13,true),(0,true),(1,true),(9,false),(8,false)],[(6,false),(5,false),(12,false),(11,false),(10,false),(2,true),(7,true)])
                        .empty
                        .empty))))
                (.node 91905 ([(2,true),(11,false),(0,false),(6,false),(5,false),(4,false),(8,false)],[(13,false),(12,false),(3,true),(9,true),(10,true),(1,true),(7,true)])
                  (.node 91101 ([(3,true),(4,true),(12,false),(11,false),(6,true),(0,true),(8,false)],[(13,false),(5,true),(10,false),(9,false),(1,true),(2,true),(7,true)])
                    (.node 90525 ([(0,false),(6,false),(5,false),(12,false),(11,false),(3,false),(8,false)],[(13,false),(4,false),(10,false),(9,false),(2,false),(1,false),(7,true)])
                      (.node 90513 ([(3,true),(10,false),(6,true),(13,false),(12,false),(1,false),(8,false)],[(0,true),(9,true),(5,false),(4,false),(11,true),(2,true),(7,true)])
                        (.node 90303 ([(3,true),(4,true),(12,false),(1,false),(0,false),(6,false),(8,false)],[(13,false),(5,true),(9,true),(10,true),(11,true),(2,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 91053 ([(4,true),(12,false),(2,true),(10,true),(6,true),(0,true),(8,false)],[(13,false),(5,true),(11,true),(1,false),(9,true),(3,true),(7,true)])
                        .empty
                        .empty))
                    (.node 91821 ([(2,true),(3,true),(10,true),(0,false),(13,false),(5,true),(8,false)],[(6,false),(9,true),(4,true),(12,false),(11,false),(1,true),(7,true)])
                      (.node 91797 ([(6,true),(13,false),(4,false),(3,false),(11,false),(1,true),(8,false)],[(0,true),(10,false),(9,false),(2,true),(12,true),(5,true),(7,true)])
                        .empty
                        .empty)
                      (.node 91893 ([(4,true),(12,false),(11,false),(0,false),(6,false),(9,false),(8,false)],[(13,false),(5,true),(10,true),(1,true),(2,true),(3,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 169929 ([(4,true),(10,false),(1,false),(13,false),(12,false),(6,false),(8,false)],[(0,false),(11,false),(5,true),(9,true),(2,true),(3,true),(7,true)])
                    (.node 169755 ([(5,true),(6,true),(11,false),(3,false),(13,true),(1,true),(8,false)],[(0,false),(12,true),(2,false),(9,true),(10,true),(4,true),(7,true)])
                      (.node 93423 ([(0,false),(6,false),(5,false),(12,false),(2,false),(9,false),(8,false)],[(13,false),(4,false),(3,false),(11,false),(10,false),(1,false),(7,true)])
                        (.node 93375 ([(2,true),(11,false),(10,false),(0,false),(13,false),(4,false),(8,false)],[(6,false),(5,false),(12,false),(3,true),(9,true),(1,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 169917 ([(6,true),(0,true),(13,false),(2,false),(10,true),(4,false),(8,false)],[(1,true),(9,false),(3,false),(12,false),(11,false),(5,true),(7,true)])
                        .empty
                        .empty))
                    (.node 180219 ([(4,true),(11,false),(0,true),(13,false),(2,false),(9,false),(8,false)],[(1,true),(10,true),(6,false),(5,false),(12,true),(3,true),(7,true)])
                      (.node 180207 ([(6,true),(0,true),(1,true),(2,true),(12,false),(4,false),(8,false)],[(13,false),(3,true),(9,true),(10,true),(11,true),(5,true),(7,true)])
                        .empty
                        .empty)
                      (.node 180291 ([(6,true),(0,true),(13,false),(12,false),(4,false),(9,false),(8,false)],[(1,true),(2,true),(3,true),(10,true),(11,true),(5,true),(7,true)])
                        .empty
                        .empty))))))
            (.node 209019 ([(6,true),(0,true),(13,false),(12,false),(2,false),(9,false),(8,false)],[(1,true),(10,true),(11,true),(3,true),(4,true),(5,true),(7,true)])
              (.node 199995 ([(5,true),(6,true),(10,true),(1,false),(13,false),(3,false),(8,false)],[(0,false),(9,false),(2,false),(11,true),(12,true),(4,true),(7,true)])
                (.node 185883 ([(5,true),(6,true),(12,true),(13,true),(1,true),(2,true),(8,false)],[(0,false),(11,false),(10,false),(9,false),(3,true),(4,true),(7,true)])
                  (.node 183867 ([(5,true),(6,true),(10,true),(3,false),(13,true),(1,true),(8,false)],[(0,false),(9,false),(2,true),(12,false),(11,false),(4,true),(7,true)])
                    (.node 183363 ([(5,true),(11,false),(1,false),(13,false),(3,true),(9,false),(8,false)],[(0,false),(6,false),(12,true),(2,false),(10,false),(4,true),(7,true)])
                      (.node 181083 ([(0,true),(1,true),(2,true),(12,false),(5,true),(9,false),(8,false)],[(13,false),(3,true),(4,true),(11,false),(10,false),(6,true),(7,true)])
                        (.node 180795 ([(6,true),(0,true),(1,true),(2,true),(12,false),(4,false),(8,false)],[(13,false),(3,true),(9,true),(10,true),(11,true),(5,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 183411 ([(4,true),(5,true),(11,false),(2,true),(13,true),(0,false),(8,false)],[(1,true),(10,false),(9,false),(6,false),(12,true),(3,true),(7,true)])
                        .empty
                        .empty))
                    (.node 183981 ([(0,true),(1,true),(2,true),(12,false),(11,false),(4,true),(8,false)],[(13,false),(3,true),(10,false),(9,false),(5,true),(6,true),(7,true)])
                      (.node 183951 ([(5,true),(11,false),(3,false),(2,false),(1,false),(0,false),(8,false)],[(13,false),(12,false),(6,true),(9,true),(10,true),(4,true),(7,true)])
                        (.node 183885 ([(1,false),(13,false),(3,true),(10,false),(6,false),(5,false),(8,false)],[(0,false),(9,false),(4,false),(11,true),(12,true),(2,false),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 185835 ([(6,true),(0,true),(1,true),(10,false),(4,false),(3,false),(8,false)],[(13,false),(12,false),(11,false),(2,true),(9,true),(5,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 189951 ([(6,true),(0,true),(1,true),(12,true),(4,true),(9,false),(8,false)],[(13,false),(3,false),(2,false),(11,false),(10,false),(5,true),(7,true)])
                    (.node 186735 ([(3,true),(4,true),(10,false),(1,false),(0,false),(6,false),(8,false)],[(13,false),(12,false),(11,false),(5,true),(9,true),(2,true),(7,true)])
                      (.node 186219 ([(5,true),(6,true),(0,true),(13,false),(3,false),(2,false),(8,false)],[(1,true),(9,true),(10,true),(11,true),(12,true),(4,true),(7,true)])
                        (.node 186171 ([(6,true),(0,true),(13,false),(3,false),(10,false),(9,false),(8,false)],[(1,true),(2,true),(11,true),(12,true),(4,true),(5,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 186783 ([(1,false),(0,false),(11,false),(4,false),(3,false),(9,false),(8,false)],[(13,false),(12,false),(6,false),(5,false),(10,false),(2,false),(7,true)])
                        .empty
                        .empty))
                    (.node 191889 ([(5,true),(10,false),(2,false),(12,true),(13,true),(0,false),(8,false)],[(1,true),(11,false),(6,true),(9,true),(3,true),(4,true),(7,true)])
                      (.node 191421 ([(6,true),(0,true),(1,true),(11,false),(4,false),(3,false),(8,false)],[(13,false),(12,false),(2,true),(9,true),(10,true),(5,true),(7,true)])
                        .empty
                        .empty)
                      (.node 191919 ([(0,true),(1,true),(11,false),(10,false),(3,true),(4,true),(8,false)],[(13,false),(12,false),(2,true),(9,false),(5,true),(6,true),(7,true)])
                        .empty
                        .empty))))
                (.node 203025 ([(4,true),(5,true),(10,true),(11,true),(0,true),(1,true),(8,false)],[(13,false),(12,false),(6,false),(9,false),(2,true),(3,true),(7,true)])
                  (.node 200349 ([(1,false),(0,false),(6,false),(11,false),(3,true),(4,true),(8,false)],[(13,false),(12,false),(5,false),(9,true),(10,true),(2,false),(7,true)])
                    (.node 200235 ([(0,true),(1,true),(10,false),(5,true),(12,true),(3,false),(8,false)],[(13,false),(4,true),(9,false),(2,false),(11,true),(6,true),(7,true)])
                      (.node 200217 ([(3,true),(4,true),(5,true),(11,false),(1,false),(0,false),(8,false)],[(13,false),(12,false),(6,true),(9,true),(10,true),(2,true),(7,true)])
                        (.node 200007 ([(3,true),(12,false),(11,false),(1,false),(0,false),(9,false),(8,false)],[(13,false),(4,true),(5,true),(6,true),(10,true),(2,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 200331 ([(5,true),(6,true),(0,true),(13,false),(3,false),(2,false),(8,false)],[(1,true),(9,true),(10,true),(11,true),(12,true),(4,true),(7,true)])
                        .empty
                        .empty))
                    (.node 200571 ([(0,true),(13,false),(3,false),(11,true),(5,false),(9,false),(8,false)],[(1,true),(2,true),(10,false),(4,false),(12,false),(6,true),(7,true)])
                      (.node 200559 ([(1,false),(13,false),(3,false),(10,false),(5,true),(6,true),(8,false)],[(0,false),(9,true),(4,false),(12,false),(11,false),(2,false),(7,true)])
                        .empty
                        .empty)
                      (.node 202611 ([(3,true),(4,true),(13,true),(1,true),(11,true),(6,false),(8,false)],[(0,false),(12,true),(5,true),(9,true),(10,true),(2,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 207885 ([(6,true),(0,true),(13,false),(12,false),(11,false),(3,false),(8,false)],[(1,true),(2,true),(9,true),(10,true),(4,true),(5,true),(7,true)])
                    (.node 206679 ([(4,true),(12,false),(1,false),(0,false),(10,false),(9,false),(8,false)],[(13,false),(5,true),(6,true),(11,true),(2,true),(3,true),(7,true)])
                      (.node 203199 ([(3,true),(4,true),(12,false),(0,true),(1,true),(9,false),(8,false)],[(13,false),(5,true),(6,true),(11,false),(10,false),(2,true),(7,true)])
                        (.node 203037 ([(1,false),(0,false),(11,false),(10,false),(5,false),(4,false),(8,false)],[(13,false),(12,false),(6,false),(9,false),(3,false),(2,false),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 206727 ([(3,true),(4,true),(12,false),(1,false),(0,false),(6,false),(8,false)],[(13,false),(5,true),(9,true),(10,true),(11,true),(2,true),(7,true)])
                        .empty
                        .empty))
                    (.node 208695 ([(4,true),(5,true),(10,false),(2,false),(1,false),(0,false),(8,false)],[(13,false),(12,false),(11,false),(6,true),(9,true),(3,true),(7,true)])
                      (.node 208173 ([(0,true),(1,true),(11,false),(4,true),(5,true),(9,false),(8,false)],[(13,false),(12,false),(2,true),(3,true),(10,false),(6,true),(7,true)])
                        .empty
                        .empty)
                      (.node 208743 ([(3,true),(4,true),(13,true),(1,true),(11,false),(6,true),(8,false)],[(0,false),(9,true),(10,true),(5,false),(12,false),(2,true),(7,true)])
                        .empty
                        .empty)))))
              (.node 228279 ([(1,false),(0,false),(6,false),(12,false),(3,false),(9,false),(8,false)],[(13,false),(5,false),(4,false),(11,false),(10,false),(2,false),(7,true)])
                (.node 224703 ([(3,true),(10,false),(0,true),(1,true),(12,true),(5,false),(8,false)],[(13,false),(6,true),(9,false),(4,false),(11,true),(2,true),(7,true)])
                  (.node 211071 ([(0,true),(1,true),(2,true),(11,false),(5,false),(4,false),(8,false)],[(13,false),(12,false),(3,true),(9,true),(10,true),(6,true),(7,true)])
                    (.node 209127 ([(1,false),(0,false),(10,false),(3,false),(12,true),(5,true),(8,false)],[(13,false),(4,false),(9,false),(6,true),(11,true),(2,false),(7,true)])
                      (.node 209103 ([(6,true),(0,true),(13,false),(4,false),(3,false),(2,false),(8,false)],[(1,true),(9,true),(10,true),(11,true),(12,true),(5,true),(7,true)])
                        (.node 209031 ([(4,true),(12,false),(2,false),(1,false),(0,false),(6,false),(8,false)],[(13,false),(5,true),(9,true),(10,true),(11,true),(3,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 211047 ([(4,true),(12,false),(11,false),(10,false),(1,false),(0,false),(8,false)],[(13,false),(5,true),(6,true),(9,true),(2,true),(3,true),(7,true)])
                        .empty
                        .empty))
                    (.node 211155 ([(0,true),(13,false),(4,false),(10,true),(11,true),(2,false),(8,false)],[(1,true),(9,true),(3,false),(12,true),(5,true),(6,true),(7,true)])
                      (.node 211143 ([(1,false),(13,false),(4,false),(3,false),(11,false),(6,true),(8,false)],[(0,false),(9,true),(10,true),(5,false),(12,false),(2,false),(7,true)])
                        .empty
                        .empty)
                      (.node 224691 ([(5,true),(6,true),(0,true),(1,true),(11,false),(3,false),(8,false)],[(13,false),(12,false),(2,true),(9,true),(10,true),(4,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 227439 ([(1,false),(0,false),(6,false),(12,false),(11,false),(4,false),(8,false)],[(13,false),(5,false),(10,false),(9,false),(3,false),(2,false),(7,true)])
                    (.node 225957 ([(4,true),(5,true),(12,false),(11,false),(0,true),(1,true),(8,false)],[(13,false),(6,true),(10,false),(9,false),(2,true),(3,true),(7,true)])
                      (.node 225909 ([(5,true),(12,false),(3,true),(10,true),(0,true),(1,true),(8,false)],[(13,false),(6,true),(11,true),(2,false),(9,true),(4,true),(7,true)])
                        (.node 225159 ([(4,true),(5,true),(13,true),(1,true),(2,true),(9,false),(8,false)],[(0,false),(6,false),(12,false),(11,false),(10,false),(3,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 227427 ([(4,true),(10,false),(0,true),(13,false),(12,false),(2,false),(8,false)],[(1,true),(9,true),(6,false),(5,false),(11,true),(3,true),(7,true)])
                        .empty
                        .empty))
                    (.node 227535 ([(0,true),(13,false),(5,false),(10,false),(2,true),(3,true),(8,false)],[(1,true),(9,false),(4,true),(11,true),(12,true),(6,true),(7,true)])
                      (.node 227511 ([(4,true),(5,true),(12,false),(2,false),(1,false),(0,false),(8,false)],[(13,false),(6,true),(9,true),(10,true),(11,true),(3,true),(7,true)])
                        .empty
                        .empty)
                      (.node 228231 ([(3,true),(11,false),(10,false),(1,false),(13,false),(5,false),(8,false)],[(0,false),(6,false),(12,false),(4,true),(9,true),(2,true),(7,true)])
                        .empty
                        .empty))))
                (.node 245565 ([(5,true),(6,true),(12,false),(11,false),(1,true),(2,true),(8,false)],[(13,false),(0,true),(10,false),(9,false),(3,true),(4,true),(7,true)])
                  (.node 244299 ([(6,true),(0,true),(1,true),(2,true),(11,false),(4,false),(8,false)],[(13,false),(12,false),(3,true),(9,true),(10,true),(5,true),(7,true)])
                    (.node 229029 ([(3,true),(4,true),(10,true),(1,false),(13,false),(6,true),(8,false)],[(0,false),(9,true),(5,true),(12,false),(11,false),(2,true),(7,true)])
                      (.node 228819 ([(3,true),(11,false),(1,false),(0,false),(6,false),(5,false),(8,false)],[(13,false),(12,false),(4,true),(9,true),(10,true),(2,true),(7,true)])
                        (.node 228807 ([(5,true),(12,false),(11,false),(1,false),(0,false),(9,false),(8,false)],[(13,false),(6,true),(10,true),(2,true),(3,true),(4,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 229047 ([(0,true),(13,false),(5,false),(4,false),(11,false),(2,true),(8,false)],[(1,true),(10,false),(9,false),(3,true),(12,true),(6,true),(7,true)])
                        .empty
                        .empty))
                    (.node 244767 ([(5,true),(6,true),(13,true),(2,true),(3,true),(9,false),(8,false)],[(1,false),(0,false),(12,false),(11,false),(10,false),(4,true),(7,true)])
                      (.node 244311 ([(4,true),(10,false),(1,true),(2,true),(12,true),(6,false),(8,false)],[(13,false),(0,true),(9,false),(5,false),(11,true),(3,true),(7,true)])
                        .empty
                        .empty)
                      (.node 245517 ([(6,true),(12,false),(4,true),(10,true),(1,true),(2,true),(8,false)],[(13,false),(0,true),(11,true),(3,false),(9,true),(5,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 247839 ([(4,true),(11,false),(10,false),(2,false),(13,false),(6,false),(8,false)],[(1,false),(0,false),(12,false),(5,true),(9,true),(3,true),(7,true)])
                    (.node 247119 ([(5,true),(6,true),(12,false),(3,false),(2,false),(1,false),(8,false)],[(13,false),(0,true),(9,true),(10,true),(11,true),(4,true),(7,true)])
                      (.node 247047 ([(2,false),(1,false),(0,false),(12,false),(11,false),(5,false),(8,false)],[(13,false),(6,false),(10,false),(9,false),(4,false),(3,false),(7,true)])
                        (.node 247035 ([(5,true),(10,false),(1,true),(13,false),(12,false),(3,false),(8,false)],[(2,true),(9,true),(0,false),(6,false),(11,true),(4,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 247143 ([(1,true),(13,false),(6,false),(10,false),(3,true),(4,true),(8,false)],[(2,true),(9,false),(5,true),(11,true),(12,true),(0,true),(7,true)])
                        .empty
                        .empty))
                    (.node 248415 ([(6,true),(12,false),(11,false),(2,false),(1,false),(9,false),(8,false)],[(13,false),(0,true),(10,true),(3,true),(4,true),(5,true),(7,true)])
                      (.node 247887 ([(2,false),(1,false),(0,false),(12,false),(4,false),(9,false),(8,false)],[(13,false),(6,false),(5,false),(11,false),(10,false),(3,false),(7,true)])
                        .empty
                        .empty)
                      (.node 248427 ([(4,true),(11,false),(2,false),(1,false),(0,false),(6,false),(8,false)],[(13,false),(12,false),(5,true),(9,true),(10,true),(3,true),(7,true)])
                        .empty
                        .empty)))))))
          (.node 381549 ([(0,true),(1,true),(2,true),(3,true),(11,false),(5,false),(8,false)],[(13,false),(12,false),(4,true),(9,true),(10,true),(6,true),(7,true)])
            (.node 339951 ([(2,false),(1,false),(11,false),(10,false),(6,false),(5,false),(8,false)],[(13,false),(12,false),(0,false),(9,false),(4,false),(3,false),(7,true)])
              (.node 320667 ([(4,true),(5,true),(6,true),(11,false),(2,false),(1,false),(8,false)],[(13,false),(12,false),(0,true),(9,true),(10,true),(3,true),(7,true)])
                (.node 307167 ([(0,true),(1,true),(13,false),(3,false),(10,true),(5,false),(8,false)],[(2,true),(9,false),(4,false),(12,false),(11,false),(6,true),(7,true)])
                  (.node 304335 ([(2,false),(13,false),(4,true),(10,false),(0,false),(6,false),(8,false)],[(1,false),(9,false),(5,false),(11,true),(12,true),(3,false),(7,true)])
                    (.node 303861 ([(5,true),(6,true),(11,false),(3,true),(13,true),(1,false),(8,false)],[(2,true),(10,false),(9,false),(0,false),(12,true),(4,true),(7,true)])
                      (.node 303813 ([(6,true),(11,false),(2,false),(13,false),(4,true),(9,false),(8,false)],[(1,false),(0,false),(12,true),(3,false),(10,false),(5,true),(7,true)])
                        (.node 248655 ([(1,true),(13,false),(6,false),(5,false),(11,false),(3,true),(8,false)],[(2,true),(10,false),(9,false),(4,true),(12,true),(0,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 304317 ([(6,true),(0,true),(10,true),(4,false),(13,true),(2,true),(8,false)],[(1,false),(9,false),(3,true),(12,false),(11,false),(5,true),(7,true)])
                        .empty
                        .empty))
                    (.node 306669 ([(6,true),(0,true),(11,false),(4,false),(13,true),(2,true),(8,false)],[(1,false),(12,true),(3,false),(9,true),(10,true),(5,true),(7,true)])
                      (.node 304431 ([(1,true),(2,true),(3,true),(12,false),(11,false),(5,true),(8,false)],[(13,false),(4,true),(10,false),(9,false),(6,true),(0,true),(7,true)])
                        (.node 304401 ([(6,true),(11,false),(4,false),(3,false),(2,false),(1,false),(8,false)],[(13,false),(12,false),(0,true),(9,true),(10,true),(5,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 307137 ([(5,true),(10,false),(2,false),(13,false),(12,false),(0,false),(8,false)],[(1,false),(11,false),(6,true),(9,true),(3,true),(4,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 317997 ([(1,true),(2,true),(3,true),(12,false),(6,true),(9,false),(8,false)],[(13,false),(4,true),(5,true),(11,false),(10,false),(0,true),(7,true)])
                    (.node 317523 ([(2,false),(13,false),(4,true),(5,true),(11,false),(0,false),(8,false)],[(1,false),(10,false),(9,false),(6,false),(12,true),(3,false),(7,true)])
                      (.node 317457 ([(0,true),(1,true),(2,true),(3,true),(12,false),(5,false),(8,false)],[(13,false),(4,true),(9,true),(10,true),(11,true),(6,true),(7,true)])
                        (.node 317427 ([(5,true),(11,false),(1,true),(13,false),(3,false),(9,false),(8,false)],[(2,true),(10,true),(0,false),(6,false),(12,true),(4,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 317541 ([(0,true),(1,true),(13,false),(12,false),(5,false),(9,false),(8,false)],[(2,true),(3,true),(4,true),(10,true),(11,true),(6,true),(7,true)])
                        .empty
                        .empty))
                    (.node 320445 ([(6,true),(0,true),(10,true),(2,false),(13,false),(4,false),(8,false)],[(1,false),(9,false),(3,false),(11,true),(12,true),(5,true),(7,true)])
                      (.node 318045 ([(0,true),(1,true),(2,true),(3,true),(12,false),(5,false),(8,false)],[(13,false),(4,true),(9,true),(10,true),(11,true),(6,true),(7,true)])
                        .empty
                        .empty)
                      (.node 320457 ([(4,true),(12,false),(11,false),(2,false),(1,false),(9,false),(8,false)],[(13,false),(5,true),(6,true),(0,true),(10,true),(3,true),(7,true)])
                        .empty
                        .empty))))
                (.node 323421 ([(0,true),(1,true),(13,false),(4,false),(10,false),(9,false),(8,false)],[(2,true),(3,true),(11,true),(12,true),(5,true),(6,true),(7,true)])
                  (.node 321021 ([(1,true),(13,false),(4,false),(11,true),(6,false),(9,false),(8,false)],[(2,true),(3,true),(10,false),(5,false),(12,false),(0,true),(7,true)])
                    (.node 320799 ([(2,false),(1,false),(0,false),(11,false),(4,true),(5,true),(8,false)],[(13,false),(12,false),(6,false),(9,true),(10,true),(3,false),(7,true)])
                      (.node 320781 ([(6,true),(0,true),(1,true),(13,false),(4,false),(3,false),(8,false)],[(2,true),(9,true),(10,true),(11,true),(12,true),(5,true),(7,true)])
                        (.node 320685 ([(1,true),(2,true),(10,false),(6,true),(12,true),(4,false),(8,false)],[(13,false),(5,true),(9,false),(3,false),(11,true),(0,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 321009 ([(2,false),(13,false),(4,false),(10,false),(6,true),(0,true),(8,false)],[(1,false),(9,true),(5,false),(12,false),(11,false),(3,false),(7,true)])
                        .empty
                        .empty))
                    (.node 323085 ([(0,true),(1,true),(2,true),(10,false),(5,false),(4,false),(8,false)],[(13,false),(12,false),(11,false),(3,true),(9,true),(6,true),(7,true)])
                      (.node 322797 ([(6,true),(0,true),(12,true),(13,true),(2,true),(3,true),(8,false)],[(1,false),(11,false),(10,false),(9,false),(4,true),(5,true),(7,true)])
                        .empty
                        .empty)
                      (.node 323133 ([(6,true),(0,true),(1,true),(13,false),(4,false),(3,false),(8,false)],[(2,true),(9,true),(10,true),(11,true),(12,true),(5,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 327201 ([(0,true),(1,true),(2,true),(12,true),(5,true),(9,false),(8,false)],[(13,false),(4,false),(3,false),(11,false),(10,false),(6,true),(7,true)])
                    (.node 326745 ([(6,true),(10,false),(3,false),(12,true),(13,true),(1,false),(8,false)],[(2,true),(11,false),(0,true),(9,true),(4,true),(5,true),(7,true)])
                      (.node 323991 ([(2,false),(1,false),(11,false),(5,false),(4,false),(9,false),(8,false)],[(13,false),(12,false),(0,false),(6,false),(10,false),(3,false),(7,true)])
                        (.node 323943 ([(4,true),(5,true),(10,false),(2,false),(1,false),(0,false),(8,false)],[(13,false),(12,false),(11,false),(6,true),(9,true),(3,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 326775 ([(1,true),(2,true),(11,false),(10,false),(4,true),(5,true),(8,false)],[(13,false),(12,false),(3,true),(9,false),(6,true),(0,true),(7,true)])
                        .empty
                        .empty))
                    (.node 339819 ([(4,true),(5,true),(13,true),(2,true),(11,true),(0,false),(8,false)],[(1,false),(12,true),(6,true),(9,true),(10,true),(3,true),(7,true)])
                      (.node 328671 ([(0,true),(1,true),(2,true),(11,false),(5,false),(4,false),(8,false)],[(13,false),(12,false),(3,true),(9,true),(10,true),(6,true),(7,true)])
                        .empty
                        .empty)
                      (.node 339939 ([(5,true),(6,true),(10,true),(11,true),(1,true),(2,true),(8,false)],[(13,false),(12,false),(0,false),(9,false),(3,true),(4,true),(7,true)])
                        .empty
                        .empty)))))
              (.node 359559 ([(3,false),(2,false),(11,false),(10,false),(0,false),(6,false),(8,false)],[(13,false),(12,false),(1,false),(9,false),(5,false),(4,false),(7,true)])
                (.node 345927 ([(1,true),(2,true),(3,true),(11,false),(6,false),(5,false),(8,false)],[(13,false),(12,false),(4,true),(9,true),(10,true),(0,true),(7,true)])
                  (.node 343935 ([(4,true),(5,true),(12,false),(2,false),(1,false),(0,false),(8,false)],[(13,false),(6,true),(9,true),(10,true),(11,true),(3,true),(7,true)])
                    (.node 343599 ([(4,true),(5,true),(13,true),(2,true),(11,false),(0,true),(8,false)],[(1,false),(9,true),(10,true),(6,false),(12,false),(3,true),(7,true)])
                      (.node 343551 ([(5,true),(6,true),(10,false),(3,false),(2,false),(1,false),(8,false)],[(13,false),(12,false),(11,false),(0,true),(9,true),(4,true),(7,true)])
                        (.node 340407 ([(4,true),(5,true),(12,false),(1,true),(2,true),(9,false),(8,false)],[(13,false),(6,true),(0,true),(11,false),(10,false),(3,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 343887 ([(5,true),(12,false),(2,false),(1,false),(10,false),(9,false),(8,false)],[(13,false),(6,true),(0,true),(11,true),(3,true),(4,true),(7,true)])
                        .empty
                        .empty))
                    (.node 345135 ([(0,true),(1,true),(13,false),(12,false),(11,false),(4,false),(8,false)],[(2,true),(3,true),(9,true),(10,true),(5,true),(6,true),(7,true)])
                      (.node 345087 ([(1,true),(2,true),(11,false),(5,true),(6,true),(9,false),(8,false)],[(13,false),(12,false),(3,true),(4,true),(10,false),(0,true),(7,true)])
                        .empty
                        .empty)
                      (.node 345903 ([(5,true),(12,false),(11,false),(10,false),(2,false),(1,false),(8,false)],[(13,false),(6,true),(0,true),(9,true),(3,true),(4,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 346335 ([(2,false),(1,false),(10,false),(4,false),(12,true),(6,true),(8,false)],[(13,false),(5,false),(9,false),(0,true),(11,true),(3,false),(7,true)])
                    (.node 346239 ([(5,true),(12,false),(3,false),(2,false),(1,false),(0,false),(8,false)],[(13,false),(6,true),(9,true),(10,true),(11,true),(4,true),(7,true)])
                      (.node 346011 ([(1,true),(13,false),(5,false),(10,true),(11,true),(3,false),(8,false)],[(2,true),(9,true),(4,false),(12,true),(6,true),(0,true),(7,true)])
                        (.node 345999 ([(2,false),(13,false),(5,false),(4,false),(11,false),(0,true),(8,false)],[(1,false),(9,true),(10,true),(6,false),(12,false),(3,false),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 346269 ([(0,true),(1,true),(13,false),(12,false),(3,false),(9,false),(8,false)],[(2,true),(10,true),(11,true),(4,true),(5,true),(6,true),(7,true)])
                        .empty
                        .empty))
                    (.node 359427 ([(5,true),(6,true),(13,true),(3,true),(11,true),(1,false),(8,false)],[(2,false),(12,true),(0,true),(9,true),(10,true),(4,true),(7,true)])
                      (.node 346353 ([(0,true),(1,true),(13,false),(5,false),(4,false),(3,false),(8,false)],[(2,true),(9,true),(10,true),(11,true),(12,true),(6,true),(7,true)])
                        .empty
                        .empty)
                      (.node 359547 ([(6,true),(0,true),(10,true),(11,true),(2,true),(3,true),(8,false)],[(13,false),(12,false),(1,false),(9,false),(4,true),(5,true),(7,true)])
                        .empty
                        .empty))))
                (.node 365535 ([(2,true),(3,true),(4,true),(11,false),(0,false),(6,false),(8,false)],[(13,false),(12,false),(5,true),(9,true),(10,true),(1,true),(7,true)])
                  (.node 363543 ([(5,true),(6,true),(12,false),(3,false),(2,false),(1,false),(8,false)],[(13,false),(0,true),(9,true),(10,true),(11,true),(4,true),(7,true)])
                    (.node 363207 ([(5,true),(6,true),(13,true),(3,true),(11,false),(1,true),(8,false)],[(2,false),(9,true),(10,true),(0,false),(12,false),(4,true),(7,true)])
                      (.node 363159 ([(6,true),(0,true),(10,false),(4,false),(3,false),(2,false),(8,false)],[(13,false),(12,false),(11,false),(1,true),(9,true),(5,true),(7,true)])
                        (.node 360015 ([(5,true),(6,true),(12,false),(2,true),(3,true),(9,false),(8,false)],[(13,false),(0,true),(1,true),(11,false),(10,false),(4,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 363495 ([(6,true),(12,false),(3,false),(2,false),(10,false),(9,false),(8,false)],[(13,false),(0,true),(1,true),(11,true),(4,true),(5,true),(7,true)])
                        .empty
                        .empty))
                    (.node 364743 ([(1,true),(2,true),(13,false),(12,false),(11,false),(5,false),(8,false)],[(3,true),(4,true),(9,true),(10,true),(6,true),(0,true),(7,true)])
                      (.node 364695 ([(2,true),(3,true),(11,false),(6,true),(0,true),(9,false),(8,false)],[(13,false),(12,false),(4,true),(5,true),(10,false),(1,true),(7,true)])
                        .empty
                        .empty)
                      (.node 365511 ([(6,true),(12,false),(11,false),(10,false),(3,false),(2,false),(8,false)],[(13,false),(0,true),(1,true),(9,true),(4,true),(5,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 365943 ([(3,false),(2,false),(10,false),(5,false),(12,true),(0,true),(8,false)],[(13,false),(6,false),(9,false),(1,true),(11,true),(4,false),(7,true)])
                    (.node 365847 ([(6,true),(12,false),(4,false),(3,false),(2,false),(1,false),(8,false)],[(13,false),(0,true),(9,true),(10,true),(11,true),(5,true),(7,true)])
                      (.node 365619 ([(2,true),(13,false),(6,false),(10,true),(11,true),(4,false),(8,false)],[(3,true),(9,true),(5,false),(12,true),(0,true),(1,true),(7,true)])
                        (.node 365607 ([(3,false),(13,false),(6,false),(5,false),(11,false),(1,true),(8,false)],[(2,false),(9,true),(10,true),(0,false),(12,false),(4,false),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 365877 ([(1,true),(2,true),(13,false),(12,false),(4,false),(9,false),(8,false)],[(3,true),(10,true),(11,true),(5,true),(6,true),(0,true),(7,true)])
                        .empty
                        .empty))
                    (.node 379623 ([(6,true),(0,true),(13,true),(3,true),(4,true),(9,false),(8,false)],[(2,false),(1,false),(12,false),(11,false),(10,false),(5,true),(7,true)])
                      (.node 365961 ([(1,true),(2,true),(13,false),(6,false),(5,false),(4,false),(8,false)],[(3,true),(9,true),(10,true),(11,true),(12,true),(0,true),(7,true)])
                        .empty
                        .empty)
                      (.node 381519 ([(5,true),(10,false),(2,true),(3,true),(12,true),(0,false),(8,false)],[(13,false),(1,true),(9,false),(6,false),(11,true),(4,true),(7,true)])
                        .empty
                        .empty))))))
            (.node 458847 ([(3,false),(2,false),(11,false),(6,false),(5,false),(9,false),(8,false)],[(13,false),(12,false),(1,false),(0,false),(10,false),(4,false),(7,true)])
              (.node 440775 ([(6,true),(0,true),(11,false),(4,true),(13,true),(2,false),(8,false)],[(3,true),(10,false),(9,false),(1,false),(12,true),(5,true),(7,true)])
                (.node 385569 ([(2,true),(13,false),(0,false),(6,false),(11,false),(4,true),(8,false)],[(3,true),(10,false),(9,false),(5,true),(12,true),(1,true),(7,true)])
                  (.node 382479 ([(6,true),(0,true),(12,false),(11,false),(2,true),(3,true),(8,false)],[(13,false),(1,true),(10,false),(9,false),(4,true),(5,true),(7,true)])
                    (.node 381975 ([(6,true),(0,true),(12,false),(4,false),(3,false),(2,false),(8,false)],[(13,false),(1,true),(9,true),(10,true),(11,true),(5,true),(7,true)])
                      (.node 381903 ([(3,false),(2,false),(1,false),(12,false),(11,false),(6,false),(8,false)],[(13,false),(0,false),(10,false),(9,false),(5,false),(4,false),(7,true)])
                        (.node 381891 ([(6,true),(10,false),(2,true),(13,false),(12,false),(4,false),(8,false)],[(3,true),(9,true),(1,false),(0,false),(11,true),(5,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 381999 ([(2,true),(13,false),(0,false),(10,false),(4,true),(5,true),(8,false)],[(3,true),(9,false),(6,true),(11,true),(12,true),(1,true),(7,true)])
                        .empty
                        .empty))
                    (.node 385095 ([(3,false),(2,false),(1,false),(12,false),(5,false),(9,false),(8,false)],[(13,false),(0,false),(6,false),(11,false),(10,false),(4,false),(7,true)])
                      (.node 385047 ([(5,true),(11,false),(10,false),(3,false),(13,false),(0,false),(8,false)],[(2,false),(1,false),(12,false),(6,true),(9,true),(4,true),(7,true)])
                        (.node 382767 ([(0,true),(12,false),(5,true),(10,true),(2,true),(3,true),(8,false)],[(13,false),(1,true),(11,true),(4,false),(9,true),(6,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 385551 ([(5,true),(6,true),(10,true),(3,false),(13,false),(1,true),(8,false)],[(2,false),(9,true),(0,true),(12,false),(11,false),(4,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 437973 ([(3,false),(13,false),(5,true),(6,true),(11,false),(1,false),(8,false)],[(2,false),(10,false),(9,false),(0,false),(12,true),(4,false),(7,true)])
                    (.node 437877 ([(6,true),(11,false),(2,true),(13,false),(4,false),(9,false),(8,false)],[(3,true),(10,true),(1,false),(0,false),(12,true),(5,true),(7,true)])
                      (.node 385665 ([(0,true),(12,false),(11,false),(3,false),(2,false),(9,false),(8,false)],[(13,false),(1,true),(10,true),(4,true),(5,true),(6,true),(7,true)])
                        (.node 385635 ([(5,true),(11,false),(3,false),(2,false),(1,false),(0,false),(8,false)],[(13,false),(12,false),(6,true),(9,true),(10,true),(4,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 437907 ([(1,true),(2,true),(3,true),(4,true),(12,false),(6,false),(8,false)],[(13,false),(5,true),(9,true),(10,true),(11,true),(0,true),(7,true)])
                        .empty
                        .empty))
                    (.node 438447 ([(2,true),(3,true),(4,true),(12,false),(0,true),(9,false),(8,false)],[(13,false),(5,true),(6,true),(11,false),(10,false),(1,true),(7,true)])
                      (.node 437991 ([(1,true),(2,true),(13,false),(12,false),(6,false),(9,false),(8,false)],[(3,true),(4,true),(5,true),(10,true),(11,true),(0,true),(7,true)])
                        .empty
                        .empty)
                      (.node 438495 ([(1,true),(2,true),(3,true),(4,true),(12,false),(6,false),(8,false)],[(13,false),(5,true),(9,true),(10,true),(11,true),(0,true),(7,true)])
                        .empty
                        .empty))))
                (.node 457581 ([(5,true),(6,true),(0,true),(11,false),(3,false),(2,false),(8,false)],[(13,false),(12,false),(1,true),(9,true),(10,true),(4,true),(7,true)])
                  (.node 441651 ([(0,true),(11,false),(5,false),(4,false),(3,false),(2,false),(8,false)],[(13,false),(12,false),(1,true),(9,true),(10,true),(6,true),(7,true)])
                    (.node 441567 ([(0,true),(1,true),(10,true),(5,false),(13,true),(3,true),(8,false)],[(2,false),(9,false),(4,true),(12,false),(11,false),(6,true),(7,true)])
                      (.node 441543 ([(3,false),(13,false),(5,true),(10,false),(1,false),(0,false),(8,false)],[(2,false),(9,false),(6,false),(11,true),(12,true),(4,false),(7,true)])
                        (.node 441063 ([(0,true),(11,false),(3,false),(13,false),(5,true),(9,false),(8,false)],[(2,false),(1,false),(12,true),(4,false),(10,false),(6,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 441639 ([(2,true),(3,true),(4,true),(12,false),(11,false),(6,true),(8,false)],[(13,false),(5,true),(10,false),(9,false),(0,true),(1,true),(7,true)])
                        .empty
                        .empty))
                    (.node 442023 ([(1,true),(2,true),(13,false),(4,false),(10,true),(6,false),(8,false)],[(3,true),(9,false),(5,false),(12,false),(11,false),(0,true),(7,true)])
                      (.node 441993 ([(6,true),(10,false),(3,false),(13,false),(12,false),(1,false),(8,false)],[(2,false),(11,false),(0,true),(9,true),(4,true),(5,true),(7,true)])
                        .empty
                        .empty)
                      (.node 443919 ([(0,true),(1,true),(11,false),(5,false),(13,true),(3,true),(8,false)],[(2,false),(12,true),(4,false),(9,true),(10,true),(6,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 457935 ([(2,true),(13,false),(5,false),(11,true),(0,false),(9,false),(8,false)],[(3,true),(4,true),(10,false),(6,false),(12,false),(1,true),(7,true)])
                    (.node 457695 ([(0,true),(1,true),(10,true),(3,false),(13,false),(5,false),(8,false)],[(2,false),(9,false),(4,false),(11,true),(12,true),(6,true),(7,true)])
                      (.node 457665 ([(5,true),(12,false),(11,false),(3,false),(2,false),(9,false),(8,false)],[(13,false),(6,true),(0,true),(1,true),(10,true),(4,true),(7,true)])
                        (.node 457599 ([(2,true),(3,true),(10,false),(0,true),(12,true),(5,false),(8,false)],[(13,false),(6,true),(9,false),(4,false),(11,true),(1,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 457923 ([(3,false),(13,false),(5,false),(10,false),(0,true),(1,true),(8,false)],[(2,false),(9,true),(6,false),(12,false),(11,false),(4,false),(7,true)])
                        .empty
                        .empty))
                    (.node 458031 ([(0,true),(1,true),(2,true),(13,false),(5,false),(4,false),(8,false)],[(3,true),(9,true),(10,true),(11,true),(12,true),(6,true),(7,true)])
                      (.node 458007 ([(3,false),(2,false),(1,false),(11,false),(5,true),(6,true),(8,false)],[(13,false),(12,false),(0,false),(9,true),(10,true),(4,false),(7,true)])
                        .empty
                        .empty)
                      (.node 458799 ([(5,true),(6,true),(10,false),(3,false),(2,false),(1,false),(8,false)],[(13,false),(12,false),(11,false),(0,true),(9,true),(4,true),(7,true)])
                        .empty
                        .empty)))))
              (.node 478455 ([(4,false),(3,false),(11,false),(0,false),(6,false),(9,false),(8,false)],[(13,false),(12,false),(2,false),(1,false),(10,false),(5,false),(7,true)])
                (.node 477189 ([(6,true),(0,true),(1,true),(11,false),(4,false),(3,false),(8,false)],[(13,false),(12,false),(2,true),(9,true),(10,true),(5,true),(7,true)])
                  (.node 463527 ([(1,true),(2,true),(3,true),(11,false),(6,false),(5,false),(8,false)],[(13,false),(12,false),(4,true),(9,true),(10,true),(0,true),(7,true)])
                    (.node 460335 ([(1,true),(2,true),(13,false),(5,false),(10,false),(9,false),(8,false)],[(3,true),(4,true),(11,true),(12,true),(6,true),(0,true),(7,true)])
                      (.node 460047 ([(0,true),(1,true),(12,true),(13,true),(3,true),(4,true),(8,false)],[(2,false),(11,false),(10,false),(9,false),(5,true),(6,true),(7,true)])
                        (.node 459999 ([(1,true),(2,true),(3,true),(10,false),(6,false),(5,false),(8,false)],[(13,false),(12,false),(11,false),(4,true),(9,true),(0,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 460383 ([(0,true),(1,true),(2,true),(13,false),(5,false),(4,false),(8,false)],[(3,true),(9,true),(10,true),(11,true),(12,true),(6,true),(7,true)])
                        .empty
                        .empty))
                    (.node 463995 ([(0,true),(10,false),(4,false),(12,true),(13,true),(2,false),(8,false)],[(3,true),(11,false),(1,true),(9,true),(5,true),(6,true),(7,true)])
                      (.node 463983 ([(2,true),(3,true),(11,false),(10,false),(5,true),(6,true),(8,false)],[(13,false),(12,false),(4,true),(9,false),(0,true),(1,true),(7,true)])
                        .empty
                        .empty)
                      (.node 464115 ([(1,true),(2,true),(3,true),(12,true),(6,true),(9,false),(8,false)],[(13,false),(5,false),(4,false),(11,false),(10,false),(0,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 477543 ([(3,true),(13,false),(6,false),(11,true),(1,false),(9,false),(8,false)],[(4,true),(5,true),(10,false),(0,false),(12,false),(2,true),(7,true)])
                    (.node 477303 ([(1,true),(2,true),(10,true),(4,false),(13,false),(6,false),(8,false)],[(3,false),(9,false),(5,false),(11,true),(12,true),(0,true),(7,true)])
                      (.node 477273 ([(6,true),(12,false),(11,false),(4,false),(3,false),(9,false),(8,false)],[(13,false),(0,true),(1,true),(2,true),(10,true),(5,true),(7,true)])
                        (.node 477207 ([(3,true),(4,true),(10,false),(1,true),(12,true),(6,false),(8,false)],[(13,false),(0,true),(9,false),(5,false),(11,true),(2,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 477531 ([(4,false),(13,false),(6,false),(10,false),(1,true),(2,true),(8,false)],[(3,false),(9,true),(0,false),(12,false),(11,false),(5,false),(7,true)])
                        .empty
                        .empty))
                    (.node 477639 ([(1,true),(2,true),(3,true),(13,false),(6,false),(5,false),(8,false)],[(4,true),(9,true),(10,true),(11,true),(12,true),(0,true),(7,true)])
                      (.node 477615 ([(4,false),(3,false),(2,false),(11,false),(6,true),(0,true),(8,false)],[(13,false),(12,false),(1,false),(9,true),(10,true),(5,false),(7,true)])
                        .empty
                        .empty)
                      (.node 478407 ([(6,true),(0,true),(10,false),(4,false),(3,false),(2,false),(8,false)],[(13,false),(12,false),(11,false),(1,true),(9,true),(5,true),(7,true)])
                        .empty
                        .empty))))
                (.node 494871 ([(6,true),(0,true),(12,false),(3,true),(4,true),(9,false),(8,false)],[(13,false),(1,true),(2,true),(11,false),(10,false),(5,true),(7,true)])
                  (.node 483135 ([(2,true),(3,true),(4,true),(11,false),(0,false),(6,false),(8,false)],[(13,false),(12,false),(5,true),(9,true),(10,true),(1,true),(7,true)])
                    (.node 479943 ([(2,true),(3,true),(13,false),(6,false),(10,false),(9,false),(8,false)],[(4,true),(5,true),(11,true),(12,true),(0,true),(1,true),(7,true)])
                      (.node 479655 ([(1,true),(2,true),(12,true),(13,true),(4,true),(5,true),(8,false)],[(3,false),(11,false),(10,false),(9,false),(6,true),(0,true),(7,true)])
                        (.node 479607 ([(2,true),(3,true),(4,true),(10,false),(0,false),(6,false),(8,false)],[(13,false),(12,false),(11,false),(5,true),(9,true),(1,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 479991 ([(1,true),(2,true),(3,true),(13,false),(6,false),(5,false),(8,false)],[(4,true),(9,true),(10,true),(11,true),(12,true),(0,true),(7,true)])
                        .empty
                        .empty))
                    (.node 483603 ([(1,true),(10,false),(5,false),(12,true),(13,true),(3,false),(8,false)],[(4,true),(11,false),(2,true),(9,true),(6,true),(0,true),(7,true)])
                      (.node 483591 ([(3,true),(4,true),(11,false),(10,false),(6,true),(0,true),(8,false)],[(13,false),(12,false),(5,true),(9,false),(1,true),(2,true),(7,true)])
                        .empty
                        .empty)
                      (.node 483723 ([(2,true),(3,true),(4,true),(12,true),(0,true),(9,false),(8,false)],[(13,false),(6,false),(5,false),(11,false),(10,false),(1,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 499599 ([(2,true),(3,true),(13,false),(12,false),(11,false),(6,false),(8,false)],[(4,true),(5,true),(9,true),(10,true),(0,true),(1,true),(7,true)])
                    (.node 496797 ([(0,true),(1,true),(10,true),(11,true),(3,true),(4,true),(8,false)],[(13,false),(12,false),(2,false),(9,false),(5,true),(6,true),(7,true)])
                      (.node 496767 ([(4,false),(3,false),(11,false),(10,false),(1,false),(0,false),(8,false)],[(13,false),(12,false),(2,false),(9,false),(6,false),(5,false),(7,true)])
                        (.node 496341 ([(6,true),(0,true),(13,true),(4,true),(11,true),(2,false),(8,false)],[(3,false),(12,true),(1,true),(9,true),(10,true),(5,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 499551 ([(3,true),(4,true),(11,false),(0,true),(1,true),(9,false),(8,false)],[(13,false),(12,false),(5,true),(6,true),(10,false),(2,true),(7,true)])
                        .empty
                        .empty))
                    (.node 500409 ([(0,true),(1,true),(10,false),(5,false),(4,false),(3,false),(8,false)],[(13,false),(12,false),(11,false),(2,true),(9,true),(6,true),(7,true)])
                      (.node 500121 ([(6,true),(0,true),(13,true),(4,true),(11,false),(2,true),(8,false)],[(3,false),(9,true),(10,true),(1,false),(12,false),(5,true),(7,true)])
                        .empty
                        .empty)
                      (.node 500457 ([(6,true),(0,true),(12,false),(4,false),(3,false),(2,false),(8,false)],[(13,false),(1,true),(9,true),(10,true),(11,true),(5,true),(7,true)])
                        .empty
                        .empty))))))))
        (.node 760191 ([(5,true),(13,false),(2,false),(10,true),(11,true),(0,false),(8,false)],[(6,true),(9,true),(1,false),(12,true),(3,true),(4,true),(7,true)])
          (.node 622983 ([(4,true),(13,false),(1,false),(10,true),(11,true),(6,false),(8,false)],[(5,true),(9,true),(0,false),(12,true),(2,true),(3,true),(7,true)])
            (.node 579231 ([(2,true),(3,true),(13,false),(5,false),(10,true),(0,false),(8,false)],[(4,true),(9,false),(6,false),(12,false),(11,false),(1,true),(7,true)])
              (.node 519141 ([(0,true),(10,false),(3,true),(13,false),(12,false),(5,false),(8,false)],[(4,true),(9,true),(2,false),(1,false),(11,true),(6,true),(7,true)])
                (.node 505545 ([(4,false),(3,false),(2,false),(12,false),(6,false),(9,false),(8,false)],[(13,false),(1,false),(0,false),(11,false),(10,false),(5,false),(7,true)])
                  (.node 502857 ([(4,false),(3,false),(10,false),(6,false),(12,true),(1,true),(8,false)],[(13,false),(0,false),(9,false),(2,true),(11,true),(5,false),(7,true)])
                    (.node 502743 ([(3,true),(4,true),(5,true),(11,false),(1,false),(0,false),(8,false)],[(13,false),(12,false),(6,true),(9,true),(10,true),(2,true),(7,true)])
                      (.node 502533 ([(3,true),(13,false),(0,false),(10,true),(11,true),(5,false),(8,false)],[(4,true),(9,true),(6,false),(12,true),(1,true),(2,true),(7,true)])
                        (.node 502521 ([(4,false),(13,false),(0,false),(6,false),(11,false),(2,true),(8,false)],[(3,false),(9,true),(10,true),(1,false),(12,false),(5,false),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 502761 ([(0,true),(12,false),(11,false),(10,false),(4,false),(3,false),(8,false)],[(13,false),(1,true),(2,true),(9,true),(5,true),(6,true),(7,true)])
                        .empty
                        .empty))
                    (.node 503097 ([(0,true),(12,false),(5,false),(4,false),(3,false),(2,false),(8,false)],[(13,false),(1,true),(9,true),(10,true),(11,true),(6,true),(7,true)])
                      (.node 503085 ([(2,true),(3,true),(13,false),(12,false),(5,false),(9,false),(8,false)],[(4,true),(10,true),(11,true),(6,true),(0,true),(1,true),(7,true)])
                        (.node 502875 ([(2,true),(3,true),(13,false),(0,false),(6,false),(5,false),(8,false)],[(4,true),(9,true),(10,true),(11,true),(12,true),(1,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 505497 ([(6,true),(11,false),(10,false),(4,false),(13,false),(1,false),(8,false)],[(3,false),(2,false),(12,false),(0,true),(9,true),(5,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 516375 ([(6,true),(10,false),(3,true),(4,true),(12,true),(1,false),(8,false)],[(13,false),(2,true),(9,false),(0,false),(11,true),(5,true),(7,true)])
                    (.node 506085 ([(6,true),(11,false),(4,false),(3,false),(2,false),(1,false),(8,false)],[(13,false),(12,false),(0,true),(9,true),(10,true),(5,true),(7,true)])
                      (.node 506019 ([(3,true),(13,false),(1,false),(0,false),(11,false),(5,true),(8,false)],[(4,true),(10,false),(9,false),(6,true),(12,true),(2,true),(7,true)])
                        (.node 506001 ([(6,true),(0,true),(10,true),(4,false),(13,false),(2,true),(8,false)],[(3,false),(9,true),(1,true),(12,false),(11,false),(5,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 506115 ([(1,true),(12,false),(11,false),(4,false),(3,false),(9,false),(8,false)],[(13,false),(2,true),(10,true),(5,true),(6,true),(0,true),(7,true)])
                        .empty
                        .empty))
                    (.node 516873 ([(0,true),(1,true),(13,true),(4,true),(5,true),(9,false),(8,false)],[(3,false),(2,false),(12,false),(11,false),(10,false),(6,true),(7,true)])
                      (.node 516405 ([(1,true),(2,true),(3,true),(4,true),(11,false),(6,false),(8,false)],[(13,false),(12,false),(5,true),(9,true),(10,true),(0,true),(7,true)])
                        .empty
                        .empty)
                      (.node 519111 ([(4,false),(3,false),(2,false),(12,false),(11,false),(0,false),(8,false)],[(13,false),(1,false),(10,false),(9,false),(6,false),(5,false),(7,true)])
                        .empty
                        .empty))))
                (.node 575655 ([(3,true),(4,true),(5,true),(12,false),(1,true),(9,false),(8,false)],[(13,false),(6,true),(0,true),(11,false),(10,false),(2,true),(7,true)])
                  (.node 574887 ([(4,false),(13,false),(6,true),(0,true),(11,false),(2,false),(8,false)],[(3,false),(10,false),(9,false),(1,false),(12,true),(5,false),(7,true)])
                    (.node 519681 ([(1,true),(12,false),(6,true),(10,true),(3,true),(4,true),(8,false)],[(13,false),(2,true),(11,true),(5,false),(9,true),(0,true),(7,true)])
                      (.node 519225 ([(0,true),(1,true),(12,false),(5,false),(4,false),(3,false),(8,false)],[(13,false),(2,true),(9,true),(10,true),(11,true),(6,true),(7,true)])
                        (.node 519207 ([(3,true),(13,false),(1,false),(10,false),(5,true),(6,true),(8,false)],[(4,true),(9,false),(0,true),(11,true),(12,true),(2,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 519729 ([(0,true),(1,true),(12,false),(11,false),(3,true),(4,true),(8,false)],[(13,false),(2,true),(10,false),(9,false),(5,true),(6,true),(7,true)])
                        .empty
                        .empty))
                    (.node 575115 ([(2,true),(3,true),(4,true),(5,true),(12,false),(0,false),(8,false)],[(13,false),(6,true),(9,true),(10,true),(11,true),(1,true),(7,true)])
                      (.node 574905 ([(2,true),(3,true),(13,false),(12,false),(0,false),(9,false),(8,false)],[(4,true),(5,true),(6,true),(10,true),(11,true),(1,true),(7,true)])
                        .empty
                        .empty)
                      (.node 575127 ([(0,true),(11,false),(3,true),(13,false),(5,false),(9,false),(8,false)],[(4,true),(10,true),(2,false),(1,false),(12,true),(6,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 576507 ([(1,true),(11,false),(6,false),(5,false),(4,false),(3,false),(8,false)],[(13,false),(12,false),(2,true),(9,true),(10,true),(0,true),(7,true)])
                    (.node 576423 ([(1,true),(2,true),(10,true),(6,false),(13,true),(4,true),(8,false)],[(3,false),(9,false),(5,true),(12,false),(11,false),(0,true),(7,true)])
                      (.node 576399 ([(4,false),(13,false),(6,true),(10,false),(2,false),(1,false),(8,false)],[(3,false),(9,false),(0,false),(11,true),(12,true),(5,false),(7,true)])
                        (.node 575703 ([(2,true),(3,true),(4,true),(5,true),(12,false),(0,false),(8,false)],[(13,false),(6,true),(9,true),(10,true),(11,true),(1,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 576495 ([(3,true),(4,true),(5,true),(12,false),(11,false),(0,true),(8,false)],[(13,false),(6,true),(10,false),(9,false),(1,true),(2,true),(7,true)])
                        .empty
                        .empty))
                    (.node 578025 ([(0,true),(1,true),(11,false),(5,true),(13,true),(3,false),(8,false)],[(4,true),(10,false),(9,false),(2,false),(12,true),(6,true),(7,true)])
                      (.node 577977 ([(1,true),(11,false),(4,false),(13,false),(6,true),(9,false),(8,false)],[(3,false),(2,false),(12,true),(5,false),(10,false),(0,true),(7,true)])
                        .empty
                        .empty)
                      (.node 578775 ([(1,true),(2,true),(11,false),(6,false),(13,true),(4,true),(8,false)],[(3,false),(12,true),(5,false),(9,true),(10,true),(0,true),(7,true)])
                        .empty
                        .empty)))))
              (.node 612399 ([(4,true),(13,false),(0,false),(11,true),(2,false),(9,false),(8,false)],[(5,true),(6,true),(10,false),(1,false),(12,false),(3,true),(7,true)])
                (.node 596031 ([(2,true),(3,true),(10,true),(0,false),(13,true),(5,true),(8,false)],[(4,false),(9,false),(6,true),(12,false),(11,false),(1,true),(7,true)])
                  (.node 594735 ([(1,true),(11,false),(4,true),(13,false),(6,false),(9,false),(8,false)],[(5,true),(10,true),(3,false),(2,false),(12,true),(0,true),(7,true)])
                    (.node 594513 ([(3,true),(4,true),(13,false),(12,false),(1,false),(9,false),(8,false)],[(5,true),(6,true),(0,true),(10,true),(11,true),(2,true),(7,true)])
                      (.node 594495 ([(5,false),(13,false),(0,true),(1,true),(11,false),(3,false),(8,false)],[(4,false),(10,false),(9,false),(2,false),(12,true),(6,false),(7,true)])
                        (.node 579243 ([(0,true),(10,false),(4,false),(13,false),(12,false),(2,false),(8,false)],[(3,false),(11,false),(1,true),(9,true),(5,true),(6,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 594723 ([(3,true),(4,true),(5,true),(6,true),(12,false),(1,false),(8,false)],[(13,false),(0,true),(9,true),(10,true),(11,true),(2,true),(7,true)])
                        .empty
                        .empty))
                    (.node 595311 ([(3,true),(4,true),(5,true),(6,true),(12,false),(1,false),(8,false)],[(13,false),(0,true),(9,true),(10,true),(11,true),(2,true),(7,true)])
                      (.node 595263 ([(4,true),(5,true),(6,true),(12,false),(2,true),(9,false),(8,false)],[(13,false),(0,true),(1,true),(11,false),(10,false),(3,true),(7,true)])
                        .empty
                        .empty)
                      (.node 596007 ([(5,false),(13,false),(0,true),(10,false),(3,false),(2,false),(8,false)],[(4,false),(9,false),(1,false),(11,true),(12,true),(6,false),(7,true)])
                        .empty
                        .empty)))
                  (.node 598383 ([(2,true),(3,true),(11,false),(0,false),(13,true),(5,true),(8,false)],[(4,false),(12,true),(6,false),(9,true),(10,true),(1,true),(7,true)])
                    (.node 597585 ([(2,true),(11,false),(5,false),(13,false),(0,true),(9,false),(8,false)],[(4,false),(3,false),(12,true),(6,false),(10,false),(1,true),(7,true)])
                      (.node 596115 ([(2,true),(11,false),(0,false),(6,false),(5,false),(4,false),(8,false)],[(13,false),(12,false),(3,true),(9,true),(10,true),(1,true),(7,true)])
                        (.node 596103 ([(4,true),(5,true),(6,true),(12,false),(11,false),(1,true),(8,false)],[(13,false),(0,true),(10,false),(9,false),(2,true),(3,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 597633 ([(1,true),(2,true),(11,false),(6,true),(13,true),(4,false),(8,false)],[(5,true),(10,false),(9,false),(3,false),(12,true),(0,true),(7,true)])
                        .empty
                        .empty))
                    (.node 598851 ([(1,true),(10,false),(5,false),(13,false),(12,false),(3,false),(8,false)],[(4,false),(11,false),(2,true),(9,true),(6,true),(0,true),(7,true)])
                      (.node 598839 ([(3,true),(4,true),(13,false),(6,false),(10,true),(1,false),(8,false)],[(5,true),(9,false),(0,false),(12,false),(11,false),(2,true),(7,true)])
                        .empty
                        .empty)
                      (.node 612387 ([(5,false),(13,false),(0,false),(10,false),(2,true),(3,true),(8,false)],[(4,false),(9,true),(1,false),(12,false),(11,false),(6,false),(7,true)])
                        .empty
                        .empty))))
                (.node 615369 ([(5,false),(4,false),(11,false),(1,false),(0,false),(9,false),(8,false)],[(13,false),(12,false),(3,false),(2,false),(10,false),(6,false),(7,true)])
                  (.node 614511 ([(2,true),(3,true),(10,true),(5,false),(13,false),(0,false),(8,false)],[(4,false),(9,false),(6,false),(11,true),(12,true),(1,true),(7,true)])
                    (.node 614415 ([(4,true),(5,true),(10,false),(2,true),(12,true),(0,false),(8,false)],[(13,false),(1,true),(9,false),(6,false),(11,true),(3,true),(7,true)])
                      (.node 612495 ([(2,true),(3,true),(4,true),(13,false),(0,false),(6,false),(8,false)],[(5,true),(9,true),(10,true),(11,true),(12,true),(1,true),(7,true)])
                        (.node 612471 ([(5,false),(4,false),(3,false),(11,false),(0,true),(1,true),(8,false)],[(13,false),(12,false),(2,false),(9,true),(10,true),(6,false),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 614439 ([(0,true),(1,true),(2,true),(11,false),(5,false),(4,false),(8,false)],[(13,false),(12,false),(3,true),(9,true),(10,true),(6,true),(7,true)])
                        .empty
                        .empty))
                    (.node 614799 ([(3,true),(4,true),(13,false),(0,false),(10,false),(9,false),(8,false)],[(5,true),(6,true),(11,true),(12,true),(1,true),(2,true),(7,true)])
                      (.node 614523 ([(0,true),(12,false),(11,false),(5,false),(4,false),(9,false),(8,false)],[(13,false),(1,true),(2,true),(3,true),(10,true),(6,true),(7,true)])
                        .empty
                        .empty)
                      (.node 614847 ([(2,true),(3,true),(4,true),(13,false),(0,false),(6,false),(8,false)],[(5,true),(9,true),(10,true),(11,true),(12,true),(1,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 620505 ([(4,true),(5,true),(11,false),(10,false),(0,true),(1,true),(8,false)],[(13,false),(12,false),(6,true),(9,false),(2,true),(3,true),(7,true)])
                    (.node 616863 ([(2,true),(3,true),(12,true),(13,true),(5,true),(6,true),(8,false)],[(4,false),(11,false),(10,false),(9,false),(0,true),(1,true),(7,true)])
                      (.node 616815 ([(3,true),(4,true),(5,true),(10,false),(1,false),(0,false),(8,false)],[(13,false),(12,false),(11,false),(6,true),(9,true),(2,true),(7,true)])
                        (.node 615657 ([(0,true),(1,true),(10,false),(5,false),(4,false),(3,false),(8,false)],[(13,false),(12,false),(11,false),(2,true),(9,true),(6,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 620343 ([(3,true),(4,true),(5,true),(11,false),(1,false),(0,false),(8,false)],[(13,false),(12,false),(6,true),(9,true),(10,true),(2,true),(7,true)])
                        .empty
                        .empty))
                    (.node 620931 ([(3,true),(4,true),(5,true),(12,true),(1,true),(9,false),(8,false)],[(13,false),(0,false),(6,false),(11,false),(10,false),(2,true),(7,true)])
                      (.node 620517 ([(2,true),(10,false),(6,false),(12,true),(13,true),(4,false),(8,false)],[(5,true),(11,false),(3,true),(9,true),(0,true),(1,true),(7,true)])
                        .empty
                        .empty)
                      (.node 622971 ([(5,false),(13,false),(1,false),(0,false),(11,false),(3,true),(8,false)],[(4,false),(9,true),(10,true),(2,false),(12,false),(6,false),(7,true)])
                        .empty
                        .empty))))))
            (.node 731745 ([(6,false),(13,false),(1,true),(2,true),(11,false),(4,false),(8,false)],[(5,false),(10,false),(9,false),(3,false),(12,true),(0,false),(7,true)])
              (.node 639657 ([(4,true),(13,false),(2,false),(10,false),(6,true),(0,true),(8,false)],[(5,true),(9,false),(1,true),(11,true),(12,true),(3,true),(7,true)])
                (.node 633591 ([(0,true),(1,true),(13,true),(5,true),(11,true),(3,false),(8,false)],[(4,false),(12,true),(2,true),(9,true),(10,true),(6,true),(7,true)])
                  (.node 623535 ([(3,true),(4,true),(13,false),(12,false),(6,false),(9,false),(8,false)],[(5,true),(10,true),(11,true),(0,true),(1,true),(2,true),(7,true)])
                    (.node 623307 ([(5,false),(4,false),(10,false),(0,false),(12,true),(2,true),(8,false)],[(13,false),(1,false),(9,false),(3,true),(11,true),(6,false),(7,true)])
                      (.node 623211 ([(1,true),(12,false),(11,false),(10,false),(5,false),(4,false),(8,false)],[(13,false),(2,true),(3,true),(9,true),(6,true),(0,true),(7,true)])
                        (.node 623193 ([(4,true),(5,true),(6,true),(11,false),(2,false),(1,false),(8,false)],[(13,false),(12,false),(0,true),(9,true),(10,true),(3,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 623325 ([(3,true),(4,true),(13,false),(1,false),(0,false),(6,false),(8,false)],[(5,true),(9,true),(10,true),(11,true),(12,true),(2,true),(7,true)])
                        .empty
                        .empty))
                    (.node 631653 ([(1,true),(2,true),(10,true),(11,true),(4,true),(5,true),(8,false)],[(13,false),(12,false),(3,false),(9,false),(6,true),(0,true),(7,true)])
                      (.node 631623 ([(5,false),(4,false),(11,false),(10,false),(2,false),(1,false),(8,false)],[(13,false),(12,false),(3,false),(9,false),(0,false),(6,false),(7,true)])
                        (.node 623547 ([(1,true),(12,false),(6,false),(5,false),(4,false),(3,false),(8,false)],[(13,false),(2,true),(9,true),(10,true),(11,true),(0,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 632121 ([(0,true),(1,true),(12,false),(4,true),(5,true),(9,false),(8,false)],[(13,false),(2,true),(3,true),(11,false),(10,false),(6,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 637659 ([(1,true),(12,false),(5,false),(4,false),(10,false),(9,false),(8,false)],[(13,false),(2,true),(3,true),(11,true),(6,true),(0,true),(7,true)])
                    (.node 637323 ([(1,true),(2,true),(10,false),(6,false),(5,false),(4,false),(8,false)],[(13,false),(12,false),(11,false),(3,true),(9,true),(0,true),(7,true)])
                      (.node 636807 ([(3,true),(4,true),(13,false),(12,false),(11,false),(0,false),(8,false)],[(5,true),(6,true),(9,true),(10,true),(1,true),(2,true),(7,true)])
                        (.node 636759 ([(4,true),(5,true),(11,false),(1,true),(2,true),(9,false),(8,false)],[(13,false),(12,false),(6,true),(0,true),(10,false),(3,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 637371 ([(0,true),(1,true),(13,true),(5,true),(11,false),(3,true),(8,false)],[(4,false),(9,true),(10,true),(2,false),(12,false),(6,true),(7,true)])
                        .empty
                        .empty))
                    (.node 639561 ([(5,false),(4,false),(3,false),(12,false),(11,false),(1,false),(8,false)],[(13,false),(2,false),(10,false),(9,false),(0,false),(6,false),(7,true)])
                      (.node 637707 ([(0,true),(1,true),(12,false),(5,false),(4,false),(3,false),(8,false)],[(13,false),(2,true),(9,true),(10,true),(11,true),(6,true),(7,true)])
                        .empty
                        .empty)
                      (.node 639591 ([(1,true),(10,false),(4,true),(13,false),(12,false),(6,false),(8,false)],[(5,true),(9,true),(3,false),(2,false),(11,true),(0,true),(7,true)])
                        .empty
                        .empty))))
                (.node 643335 ([(0,true),(11,false),(5,false),(4,false),(3,false),(2,false),(8,false)],[(13,false),(12,false),(1,true),(9,true),(10,true),(6,true),(7,true)])
                  (.node 642747 ([(0,true),(11,false),(10,false),(5,false),(13,false),(2,false),(8,false)],[(4,false),(3,false),(12,false),(1,true),(9,true),(6,true),(7,true)])
                    (.node 640179 ([(1,true),(2,true),(12,false),(11,false),(4,true),(5,true),(8,false)],[(13,false),(3,true),(10,false),(9,false),(6,true),(0,true),(7,true)])
                      (.node 640131 ([(2,true),(12,false),(0,true),(10,true),(4,true),(5,true),(8,false)],[(13,false),(3,true),(11,true),(6,false),(9,true),(1,true),(7,true)])
                        (.node 639675 ([(1,true),(2,true),(12,false),(6,false),(5,false),(4,false),(8,false)],[(13,false),(3,true),(9,true),(10,true),(11,true),(0,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 642459 ([(5,false),(4,false),(3,false),(12,false),(0,false),(9,false),(8,false)],[(13,false),(2,false),(1,false),(11,false),(10,false),(6,false),(7,true)])
                        .empty
                        .empty))
                    (.node 643251 ([(0,true),(1,true),(10,true),(5,false),(13,false),(3,true),(8,false)],[(4,false),(9,true),(2,true),(12,false),(11,false),(6,true),(7,true)])
                      (.node 643227 ([(4,true),(13,false),(2,false),(1,false),(11,false),(6,true),(8,false)],[(5,true),(10,false),(9,false),(0,true),(12,true),(3,true),(7,true)])
                        .empty
                        .empty)
                      (.node 643323 ([(2,true),(12,false),(11,false),(5,false),(4,false),(9,false),(8,false)],[(13,false),(3,true),(10,true),(6,true),(0,true),(1,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 730167 ([(4,true),(5,true),(6,true),(0,true),(12,false),(2,false),(8,false)],[(13,false),(1,true),(9,true),(10,true),(11,true),(3,true),(7,true)])
                    (.node 653787 ([(1,true),(2,true),(13,true),(5,true),(6,true),(9,false),(8,false)],[(4,false),(3,false),(12,false),(11,false),(10,false),(0,true),(7,true)])
                      (.node 653625 ([(0,true),(10,false),(4,true),(5,true),(12,true),(2,false),(8,false)],[(13,false),(3,true),(9,false),(1,false),(11,true),(6,true),(7,true)])
                        (.node 653613 ([(2,true),(3,true),(4,true),(5,true),(11,false),(0,false),(8,false)],[(13,false),(12,false),(6,true),(9,true),(10,true),(1,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 730119 ([(5,true),(6,true),(0,true),(12,false),(3,true),(9,false),(8,false)],[(13,false),(1,true),(2,true),(11,false),(10,false),(4,true),(7,true)])
                        .empty
                        .empty))
                    (.node 731649 ([(2,true),(11,false),(5,true),(13,false),(0,false),(9,false),(8,false)],[(6,true),(10,true),(4,false),(3,false),(12,true),(1,true),(7,true)])
                      (.node 731637 ([(4,true),(5,true),(6,true),(0,true),(12,false),(2,false),(8,false)],[(13,false),(1,true),(9,true),(10,true),(11,true),(3,true),(7,true)])
                        .empty
                        .empty)
                      (.node 731721 ([(4,true),(5,true),(13,false),(12,false),(2,false),(9,false),(8,false)],[(6,true),(0,true),(1,true),(10,true),(11,true),(3,true),(7,true)])
                        .empty
                        .empty)))))
              (.node 749607 ([(5,true),(13,false),(1,false),(11,true),(3,false),(9,false),(8,false)],[(6,true),(0,true),(10,false),(2,false),(12,false),(4,true),(7,true)])
                (.node 735765 ([(2,true),(10,false),(6,false),(13,false),(12,false),(4,false),(8,false)],[(5,false),(11,false),(3,true),(9,true),(0,true),(1,true),(7,true)])
                  (.node 733239 ([(3,true),(4,true),(10,true),(1,false),(13,true),(6,true),(8,false)],[(5,false),(9,false),(0,true),(12,false),(11,false),(2,true),(7,true)])
                    (.node 733017 ([(5,true),(6,true),(0,true),(12,false),(11,false),(2,true),(8,false)],[(13,false),(1,true),(10,false),(9,false),(3,true),(4,true),(7,true)])
                      (.node 732489 ([(2,true),(3,true),(11,false),(0,true),(13,true),(5,false),(8,false)],[(6,true),(10,false),(9,false),(4,false),(12,true),(1,true),(7,true)])
                        (.node 732441 ([(3,true),(11,false),(6,false),(13,false),(1,true),(9,false),(8,false)],[(5,false),(4,false),(12,true),(0,false),(10,false),(2,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 733029 ([(3,true),(11,false),(1,false),(0,false),(6,false),(5,false),(8,false)],[(13,false),(12,false),(4,true),(9,true),(10,true),(2,true),(7,true)])
                        .empty
                        .empty))
                    (.node 735591 ([(3,true),(4,true),(11,false),(1,false),(13,true),(6,true),(8,false)],[(5,false),(12,true),(0,false),(9,true),(10,true),(2,true),(7,true)])
                      (.node 733257 ([(6,false),(13,false),(1,true),(10,false),(4,false),(3,false),(8,false)],[(5,false),(9,false),(2,false),(11,true),(12,true),(0,false),(7,true)])
                        .empty
                        .empty)
                      (.node 735753 ([(4,true),(5,true),(13,false),(0,false),(10,true),(2,false),(8,false)],[(6,true),(9,false),(1,false),(12,false),(11,false),(3,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 749271 ([(5,true),(6,true),(10,false),(3,true),(12,true),(1,false),(8,false)],[(13,false),(2,true),(9,false),(0,false),(11,true),(4,true),(7,true)])
                    (.node 740967 ([(3,true),(10,false),(0,false),(12,true),(13,true),(5,false),(8,false)],[(6,true),(11,false),(4,true),(9,true),(1,true),(2,true),(7,true)])
                      (.node 740955 ([(5,true),(6,true),(11,false),(10,false),(1,true),(2,true),(8,false)],[(13,false),(12,false),(0,true),(9,false),(3,true),(4,true),(7,true)])
                        (.node 740793 ([(4,true),(5,true),(6,true),(11,false),(2,false),(1,false),(8,false)],[(13,false),(12,false),(0,true),(9,true),(10,true),(3,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 741381 ([(4,true),(5,true),(6,true),(12,true),(2,true),(9,false),(8,false)],[(13,false),(1,false),(0,false),(11,false),(10,false),(3,true),(7,true)])
                        .empty
                        .empty))
                    (.node 749367 ([(3,true),(4,true),(10,true),(6,false),(13,false),(1,false),(8,false)],[(5,false),(9,false),(0,false),(11,true),(12,true),(2,true),(7,true)])
                      (.node 749295 ([(1,true),(2,true),(3,true),(11,false),(6,false),(5,false),(8,false)],[(13,false),(12,false),(4,true),(9,true),(10,true),(0,true),(7,true)])
                        .empty
                        .empty)
                      (.node 749379 ([(1,true),(12,false),(11,false),(6,false),(5,false),(9,false),(8,false)],[(13,false),(2,true),(3,true),(4,true),(10,true),(0,true),(7,true)])
                        .empty
                        .empty))))
                (.node 752619 ([(6,false),(5,false),(11,false),(2,false),(1,false),(9,false),(8,false)],[(13,false),(12,false),(4,false),(3,false),(10,false),(0,false),(7,true)])
                  (.node 751719 ([(3,true),(4,true),(12,true),(13,true),(6,true),(0,true),(8,false)],[(5,false),(11,false),(10,false),(9,false),(1,true),(2,true),(7,true)])
                    (.node 749721 ([(6,false),(5,false),(4,false),(11,false),(1,true),(2,true),(8,false)],[(13,false),(12,false),(3,false),(9,true),(10,true),(0,false),(7,true)])
                      (.node 749703 ([(3,true),(4,true),(5,true),(13,false),(1,false),(0,false),(8,false)],[(6,true),(9,true),(10,true),(11,true),(12,true),(2,true),(7,true)])
                        (.node 749637 ([(6,false),(13,false),(1,false),(10,false),(3,true),(4,true),(8,false)],[(5,false),(9,true),(2,false),(12,false),(11,false),(0,false),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 751671 ([(4,true),(5,true),(6,true),(10,false),(2,false),(1,false),(8,false)],[(13,false),(12,false),(11,false),(0,true),(9,true),(3,true),(7,true)])
                        .empty
                        .empty))
                    (.node 752055 ([(3,true),(4,true),(5,true),(13,false),(1,false),(0,false),(8,false)],[(6,true),(9,true),(10,true),(11,true),(12,true),(2,true),(7,true)])
                      (.node 752007 ([(4,true),(5,true),(13,false),(1,false),(10,false),(9,false),(8,false)],[(6,true),(0,true),(11,true),(12,true),(2,true),(3,true),(7,true)])
                        .empty
                        .empty)
                      (.node 752571 ([(1,true),(2,true),(10,false),(6,false),(5,false),(4,false),(8,false)],[(13,false),(12,false),(11,false),(3,true),(9,true),(0,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 758109 ([(2,true),(12,false),(6,false),(5,false),(10,false),(9,false),(8,false)],[(13,false),(3,true),(4,true),(11,true),(0,true),(1,true),(7,true)])
                    (.node 757773 ([(2,true),(3,true),(10,false),(0,false),(6,false),(5,false),(8,false)],[(13,false),(12,false),(11,false),(4,true),(9,true),(1,true),(7,true)])
                      (.node 757257 ([(4,true),(5,true),(13,false),(12,false),(11,false),(1,false),(8,false)],[(6,true),(0,true),(9,true),(10,true),(2,true),(3,true),(7,true)])
                        (.node 757209 ([(5,true),(6,true),(11,false),(2,true),(3,true),(9,false),(8,false)],[(13,false),(12,false),(0,true),(1,true),(10,false),(4,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 757821 ([(1,true),(2,true),(13,true),(6,true),(11,false),(4,true),(8,false)],[(5,false),(9,true),(10,true),(3,false),(12,false),(0,true),(7,true)])
                        .empty
                        .empty))
                    (.node 760107 ([(5,true),(6,true),(0,true),(11,false),(3,false),(2,false),(8,false)],[(13,false),(12,false),(1,true),(9,true),(10,true),(4,true),(7,true)])
                      (.node 758157 ([(1,true),(2,true),(12,false),(6,false),(5,false),(4,false),(8,false)],[(13,false),(3,true),(9,true),(10,true),(11,true),(0,true),(7,true)])
                        .empty
                        .empty)
                      (.node 760125 ([(2,true),(12,false),(11,false),(10,false),(6,false),(5,false),(8,false)],[(13,false),(3,true),(4,true),(9,true),(0,true),(1,true),(7,true)])
                        .empty
                        .empty)))))))
          (.node 878212 ([(6,true),(0,true),(11,false),(4,false),(3,false),(2,false),(9,false)],[(13,false),(12,false),(1,true),(10,true),(5,true),(7,true),(8,true)])
            (.node 866650 ([(0,false),(13,false),(2,true),(3,true),(10,true),(5,false),(8,true)],[(6,false),(11,true),(12,true),(1,false),(7,true),(4,false),(9,false)])
              (.node 778083 ([(5,true),(13,false),(3,false),(2,false),(11,false),(0,true),(8,false)],[(6,true),(10,false),(9,false),(1,true),(12,true),(4,true),(7,true)])
                (.node 774063 ([(3,true),(4,true),(5,true),(6,true),(11,false),(1,false),(8,false)],[(13,false),(12,false),(0,true),(9,true),(10,true),(2,true),(7,true)])
                  (.node 760557 ([(6,false),(5,false),(10,false),(1,false),(12,true),(3,true),(8,false)],[(13,false),(2,false),(9,false),(4,true),(11,true),(0,false),(7,true)])
                    (.node 760461 ([(2,true),(12,false),(0,false),(6,false),(5,false),(4,false),(8,false)],[(13,false),(3,true),(9,true),(10,true),(11,true),(1,true),(7,true)])
                      (.node 760449 ([(4,true),(5,true),(13,false),(12,false),(0,false),(9,false),(8,false)],[(6,true),(10,true),(11,true),(1,true),(2,true),(3,true),(7,true)])
                        (.node 760221 ([(6,false),(13,false),(2,false),(1,false),(11,false),(4,true),(8,false)],[(5,false),(9,true),(10,true),(3,false),(12,false),(0,false),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 760533 ([(4,true),(5,true),(13,false),(2,false),(1,false),(0,false),(8,false)],[(6,true),(9,true),(10,true),(11,true),(12,true),(3,true),(7,true)])
                        .empty
                        .empty))
                    (.node 768873 ([(6,false),(5,false),(11,false),(10,false),(3,false),(2,false),(8,false)],[(13,false),(12,false),(4,false),(9,false),(1,false),(0,false),(7,true)])
                      (.node 768861 ([(2,true),(3,true),(10,true),(11,true),(5,true),(6,true),(8,false)],[(13,false),(12,false),(4,false),(9,false),(0,true),(1,true),(7,true)])
                        (.node 768447 ([(1,true),(2,true),(13,true),(6,true),(11,true),(4,false),(8,false)],[(5,false),(12,true),(3,true),(9,true),(10,true),(0,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 769035 ([(1,true),(2,true),(12,false),(5,true),(6,true),(9,false),(8,false)],[(13,false),(3,true),(4,true),(11,false),(10,false),(0,true),(7,true)])
                        .empty
                        .empty)))
                  (.node 776799 ([(2,true),(10,false),(5,true),(13,false),(12,false),(0,false),(8,false)],[(6,true),(9,true),(4,false),(3,false),(11,true),(1,true),(7,true)])
                    (.node 776571 ([(5,true),(13,false),(3,false),(10,false),(0,true),(1,true),(8,false)],[(6,true),(9,false),(2,true),(11,true),(12,true),(4,true),(7,true)])
                      (.node 774237 ([(2,true),(3,true),(13,true),(6,true),(0,true),(9,false),(8,false)],[(5,false),(4,false),(12,false),(11,false),(10,false),(1,true),(7,true)])
                        (.node 774075 ([(1,true),(10,false),(5,true),(6,true),(12,true),(3,false),(8,false)],[(13,false),(4,true),(9,false),(2,false),(11,true),(0,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 776589 ([(2,true),(3,true),(12,false),(0,false),(6,false),(5,false),(8,false)],[(13,false),(4,true),(9,true),(10,true),(11,true),(1,true),(7,true)])
                        .empty
                        .empty))
                    (.node 777339 ([(3,true),(12,false),(1,true),(10,true),(5,true),(6,true),(8,false)],[(13,false),(4,true),(11,true),(0,false),(9,true),(2,true),(7,true)])
                      (.node 776811 ([(6,false),(5,false),(4,false),(12,false),(11,false),(2,false),(8,false)],[(13,false),(3,false),(10,false),(9,false),(1,false),(0,false),(7,true)])
                        .empty
                        .empty)
                      (.node 777387 ([(2,true),(3,true),(12,false),(11,false),(5,true),(6,true),(8,false)],[(13,false),(4,true),(10,false),(9,false),(0,true),(1,true),(7,true)])
                        .empty
                        .empty))))
                (.node 861262 ([(3,true),(11,true),(1,true),(13,true),(6,false),(5,false),(8,true)],[(0,true),(12,true),(2,true),(7,true),(4,false),(10,false),(9,false)])
                  (.node 779709 ([(6,false),(5,false),(4,false),(12,false),(1,false),(9,false),(8,false)],[(13,false),(3,false),(2,false),(11,false),(10,false),(0,false),(7,true)])
                    (.node 778191 ([(1,true),(11,false),(6,false),(5,false),(4,false),(3,false),(8,false)],[(13,false),(12,false),(2,true),(9,true),(10,true),(0,true),(7,true)])
                      (.node 778179 ([(3,true),(12,false),(11,false),(6,false),(5,false),(9,false),(8,false)],[(13,false),(4,true),(10,true),(0,true),(1,true),(2,true),(7,true)])
                        (.node 778107 ([(1,true),(2,true),(10,true),(6,false),(13,false),(4,true),(8,false)],[(5,false),(9,true),(3,true),(12,false),(11,false),(0,true),(7,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 779661 ([(1,true),(11,false),(10,false),(6,false),(13,false),(3,false),(8,false)],[(5,false),(4,false),(12,false),(2,true),(9,true),(0,true),(7,true)])
                        .empty
                        .empty))
                    (.node 860878 ([(4,true),(10,true),(2,false),(1,false),(0,false),(6,false),(8,true)],[(13,false),(12,false),(11,false),(3,true),(7,true),(5,false),(9,false)])
                      (.node 860866 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 861220 ([(7,true),(6,true),(13,false),(1,false),(11,false),(4,true),(9,false)],[(0,true),(12,true),(2,true),(3,true),(10,false),(5,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 864982 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                    (.node 861838 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                      (.node 861496 ([(6,true),(13,false),(1,false),(11,false),(4,false),(3,false),(8,true)],[(0,true),(12,true),(2,true),(7,false),(5,false),(10,false),(9,false)])
                        (.node 861454 ([(6,true),(0,true),(1,true),(2,true),(10,true),(4,false),(8,true)],[(13,false),(12,false),(11,false),(5,true),(7,true),(3,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 861850 ([(2,false),(1,false),(0,false),(6,false),(5,false),(4,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,false),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 866020 ([(0,false),(13,false),(2,true),(3,true),(4,true),(5,true),(8,true)],[(6,false),(7,false),(1,true),(12,false),(11,false),(10,false),(9,false)])
                      (.node 864994 ([(4,true),(10,true),(11,true),(2,false),(13,true),(6,false),(8,true)],[(0,true),(1,true),(12,false),(3,true),(7,true),(5,false),(9,false)])
                        .empty
                        .empty)
                      (.node 866062 ([(0,false),(13,false),(2,true),(3,true),(4,true),(5,true),(9,false)],[(6,false),(10,true),(11,true),(12,true),(1,false),(7,true),(8,true)])
                        .empty
                        .empty)))))
              (.node 870496 ([(4,true),(11,false),(2,false),(1,false),(0,false),(6,false),(9,false)],[(13,false),(12,false),(5,true),(10,true),(3,true),(7,true),(8,true)])
                (.node 868906 ([(3,true),(4,true),(5,true),(6,true),(13,false),(1,false),(9,false)],[(0,true),(10,true),(11,true),(12,true),(2,true),(7,true),(8,true)])
                  (.node 867436 ([(3,true),(12,true),(1,false),(0,false),(6,false),(5,false),(8,true)],[(13,false),(2,true),(7,true),(4,false),(11,false),(10,false),(9,false)])
                    (.node 867394 ([(3,true),(4,true),(10,true),(1,true),(13,true),(6,false),(8,true)],[(0,true),(11,true),(12,true),(2,true),(7,true),(5,false),(9,false)])
                      (.node 867376 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                        (.node 866692 ([(7,true),(3,false),(2,false),(13,true),(6,false),(5,false),(9,false)],[(0,true),(1,true),(12,false),(11,false),(10,false),(4,false),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 867424 ([(5,true),(6,true),(0,true),(1,true),(12,false),(3,false),(8,true)],[(13,false),(2,true),(7,false),(4,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 868120 ([(0,false),(13,false),(2,true),(3,true),(4,true),(5,true),(9,false)],[(6,false),(10,true),(11,true),(12,true),(1,false),(7,true),(8,true)])
                      (.node 868078 ([(0,false),(13,false),(2,true),(3,true),(4,true),(5,true),(8,true)],[(6,false),(7,false),(1,true),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 868894 ([(5,true),(6,true),(0,true),(1,true),(12,false),(3,false),(8,true)],[(13,false),(2,true),(7,false),(4,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 869728 ([(6,true),(0,true),(1,true),(12,false),(4,false),(3,false),(8,true)],[(13,false),(2,true),(7,false),(5,false),(11,false),(10,false),(9,false)])
                    (.node 869686 ([(6,true),(0,true),(1,true),(12,false),(4,false),(3,false),(9,false)],[(13,false),(2,true),(10,true),(11,true),(5,true),(7,true),(8,true)])
                      (.node 869002 ([(1,true),(13,true),(6,false),(10,false),(3,true),(4,true),(8,true)],[(0,true),(7,true),(5,true),(11,true),(12,true),(2,true),(9,false)])
                        (.node 868978 ([(5,true),(6,true),(0,true),(1,true),(12,false),(3,false),(9,false)],[(13,false),(2,true),(10,true),(11,true),(4,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 869698 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 870274 ([(6,true),(0,true),(1,true),(2,true),(11,true),(4,false),(8,true)],[(13,false),(12,false),(5,true),(7,true),(3,false),(10,false),(9,false)])
                      (.node 869746 ([(3,true),(4,true),(12,true),(1,false),(0,false),(6,false),(8,true)],[(13,false),(2,true),(7,true),(5,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 870286 ([(4,true),(5,true),(6,true),(13,false),(2,true),(10,false),(9,false)],[(0,true),(1,true),(12,false),(11,false),(3,true),(7,true),(8,true)])
                        .empty
                        .empty))))
                (.node 873010 ([(5,true),(6,true),(13,false),(2,true),(3,true),(10,false),(9,false)],[(0,true),(1,true),(12,false),(11,false),(4,true),(7,true),(8,true)])
                  (.node 872140 ([(3,true),(10,true),(0,false),(13,false),(12,false),(5,false),(8,true)],[(6,false),(11,false),(1,true),(2,true),(7,true),(4,false),(9,false)])
                    (.node 871438 ([(1,true),(13,true),(6,false),(5,false),(4,false),(3,false),(8,true)],[(0,true),(7,true),(2,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 871396 ([(0,false),(6,false),(5,false),(12,true),(2,true),(3,true),(8,true)],[(13,false),(1,false),(7,true),(4,true),(11,false),(10,false),(9,false)])
                        (.node 870514 ([(1,true),(13,true),(6,false),(5,false),(11,false),(3,true),(8,true)],[(0,true),(7,true),(4,true),(12,true),(2,true),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 872128 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 872848 ([(4,true),(5,true),(11,false),(2,false),(13,true),(0,true),(8,true)],[(6,false),(12,true),(1,false),(7,false),(3,false),(10,false),(9,false)])
                      (.node 872824 ([(1,true),(13,true),(6,false),(11,false),(3,true),(4,true),(8,true)],[(0,true),(7,true),(5,true),(12,true),(2,true),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 872866 ([(1,true),(13,true),(6,false),(11,false),(10,false),(4,false),(8,true)],[(0,true),(7,true),(3,false),(2,false),(12,false),(5,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 877342 ([(4,true),(10,true),(1,false),(12,true),(13,true),(6,false),(8,true)],[(0,true),(11,false),(2,true),(3,true),(7,true),(5,false),(9,false)])
                    (.node 873496 ([(1,true),(13,true),(6,false),(5,false),(4,false),(3,false),(8,true)],[(0,true),(7,true),(2,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 873454 ([(1,true),(13,true),(6,false),(5,false),(10,false),(3,true),(8,true)],[(0,true),(7,true),(4,true),(11,true),(12,true),(2,true),(9,false)])
                        (.node 873022 ([(3,true),(4,true),(5,true),(6,true),(13,false),(1,false),(9,false)],[(0,true),(10,true),(11,true),(12,true),(2,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 877330 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 878050 ([(5,true),(6,true),(0,true),(11,false),(3,false),(2,false),(8,true)],[(13,false),(12,false),(1,true),(7,false),(4,false),(10,false),(9,false)])
                      (.node 878026 ([(2,true),(13,true),(0,true),(11,false),(4,true),(5,true),(8,true)],[(6,false),(7,false),(1,false),(12,true),(3,true),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 878068 ([(2,true),(3,true),(11,true),(0,false),(6,false),(5,false),(8,true)],[(13,false),(12,false),(1,true),(7,true),(4,false),(10,false),(9,false)])
                        .empty
                        .empty))))))
            (.node 889288 ([(1,true),(11,true),(6,true),(13,false),(3,true),(4,true),(8,true)],[(0,true),(7,true),(5,true),(12,true),(2,false),(10,false),(9,false)])
              (.node 885736 ([(5,true),(11,true),(3,false),(13,true),(0,true),(1,true),(9,false)],[(6,false),(10,false),(2,true),(12,false),(4,true),(7,true),(8,true)])
                (.node 881056 ([(1,true),(2,true),(13,true),(6,false),(10,false),(4,true),(8,true)],[(0,true),(7,true),(5,true),(11,true),(12,true),(3,true),(9,false)])
                  (.node 879388 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                    (.node 878656 ([(2,true),(12,false),(0,false),(6,false),(5,false),(4,false),(9,false)],[(13,false),(3,true),(10,true),(11,true),(1,true),(7,true),(8,true)])
                      (.node 878638 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                        (.node 878224 ([(4,true),(5,true),(6,true),(13,false),(12,false),(1,true),(9,false)],[(0,true),(11,false),(10,false),(2,true),(3,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 878698 ([(2,true),(12,false),(0,false),(6,false),(5,false),(4,false),(8,true)],[(13,false),(3,true),(7,false),(1,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 880426 ([(0,false),(13,false),(2,false),(11,false),(4,true),(5,true),(8,true)],[(6,false),(7,false),(1,true),(12,true),(3,true),(10,false),(9,false)])
                      (.node 879400 ([(4,true),(10,true),(1,true),(2,true),(13,true),(6,false),(8,true)],[(0,true),(11,true),(12,true),(3,true),(7,true),(5,false),(9,false)])
                        .empty
                        .empty)
                      (.node 880468 ([(0,false),(13,false),(2,false),(11,false),(4,true),(5,true),(9,false)],[(6,false),(10,true),(3,false),(12,false),(1,false),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 884584 ([(1,true),(11,true),(3,false),(13,true),(6,false),(5,false),(8,true)],[(0,true),(7,true),(4,false),(12,true),(2,false),(10,false),(9,false)])
                    (.node 884242 ([(2,true),(3,true),(11,false),(0,false),(6,false),(5,false),(8,true)],[(13,false),(12,false),(4,true),(7,false),(1,false),(10,false),(9,false)])
                      (.node 884200 ([(2,true),(3,true),(4,true),(10,true),(0,false),(6,false),(8,true)],[(13,false),(12,false),(11,false),(1,true),(7,true),(5,false),(9,false)])
                        (.node 881098 ([(1,true),(2,true),(13,true),(6,false),(5,false),(4,false),(8,true)],[(0,true),(7,true),(3,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 884542 ([(0,false),(13,false),(3,true),(11,false),(10,false),(5,true),(8,true)],[(6,false),(7,false),(1,true),(2,true),(12,false),(4,true),(9,false)])
                        .empty
                        .empty))
                    (.node 885394 ([(6,true),(13,false),(3,true),(4,true),(10,false),(1,false),(8,true)],[(0,true),(7,false),(5,false),(11,true),(12,true),(2,false),(9,false)])
                      (.node 885352 ([(6,true),(0,true),(10,true),(4,false),(3,false),(2,false),(8,true)],[(13,false),(12,false),(11,false),(5,true),(7,true),(1,false),(9,false)])
                        .empty
                        .empty)
                      (.node 885694 ([(7,true),(2,true),(3,true),(11,false),(6,true),(0,true),(9,false)],[(13,false),(12,false),(4,true),(5,true),(10,false),(1,true),(8,true)])
                        .empty
                        .empty))))
                (.node 887410 ([(6,true),(0,true),(10,true),(4,true),(12,true),(2,false),(8,true)],[(13,false),(3,true),(11,true),(5,true),(7,true),(1,false),(9,false)])
                  (.node 886864 ([(6,true),(0,true),(1,true),(2,true),(12,false),(4,false),(9,false)],[(13,false),(3,true),(10,true),(11,true),(5,true),(7,true),(8,true)])
                    (.node 886624 ([(4,true),(11,false),(1,true),(2,true),(13,true),(6,false),(9,false)],[(0,true),(10,false),(5,false),(12,true),(3,true),(7,true),(8,true)])
                      (.node 886552 ([(2,true),(3,true),(4,true),(11,false),(0,false),(6,false),(8,true)],[(13,false),(12,false),(5,true),(7,false),(1,false),(10,false),(9,false)])
                        (.node 886528 ([(6,true),(0,true),(1,true),(2,true),(12,false),(4,false),(9,false)],[(13,false),(3,true),(10,true),(11,true),(5,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 886636 ([(2,true),(3,true),(4,true),(11,false),(0,false),(6,false),(9,false)],[(13,false),(12,false),(5,true),(10,true),(1,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 886960 ([(4,true),(5,true),(6,true),(13,false),(2,false),(1,false),(8,true)],[(0,true),(7,false),(3,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 886894 ([(1,true),(10,false),(4,true),(12,true),(13,true),(6,false),(8,true)],[(0,true),(7,true),(5,false),(11,false),(2,true),(3,true),(9,false)])
                        .empty
                        .empty)
                      (.node 886978 ([(1,true),(2,true),(13,true),(6,false),(5,false),(4,false),(8,true)],[(0,true),(7,true),(3,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 888946 ([(2,true),(3,true),(10,true),(0,false),(6,false),(5,false),(8,true)],[(13,false),(12,false),(11,false),(1,true),(7,true),(4,false),(9,false)])
                    (.node 888136 ([(4,true),(5,true),(6,true),(13,false),(2,false),(1,false),(8,true)],[(0,true),(7,false),(3,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 888094 ([(4,true),(5,true),(6,true),(13,false),(2,false),(1,false),(9,false)],[(0,true),(10,true),(11,true),(12,true),(3,true),(7,true),(8,true)])
                        (.node 887452 ([(6,true),(13,false),(12,false),(4,false),(10,false),(1,false),(8,true)],[(0,true),(7,false),(5,false),(11,false),(3,false),(2,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 888928 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 888988 ([(2,true),(12,false),(6,true),(0,true),(10,false),(4,false),(8,true)],[(13,false),(3,true),(7,false),(1,false),(11,true),(5,false),(9,false)])
                      (.node 888976 ([(4,true),(5,true),(11,false),(0,false),(13,false),(2,false),(8,true)],[(6,false),(12,true),(3,true),(7,true),(1,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 889264 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                        .empty
                        .empty)))))
              (.node 895078 ([(2,true),(3,true),(4,true),(11,true),(0,false),(6,false),(8,true)],[(13,false),(12,false),(1,true),(7,true),(5,false),(10,false),(9,false)])
                (.node 894148 ([(3,true),(4,true),(10,true),(1,false),(0,false),(6,false),(8,true)],[(13,false),(12,false),(11,false),(2,true),(7,true),(5,false),(9,false)])
                  (.node 889852 ([(5,true),(6,true),(13,false),(3,true),(10,false),(1,false),(8,true)],[(0,true),(7,false),(4,false),(11,true),(12,true),(2,false),(9,false)])
                    (.node 889810 ([(5,true),(6,true),(0,true),(10,true),(3,false),(2,false),(8,true)],[(13,false),(12,false),(11,false),(4,true),(7,true),(1,false),(9,false)])
                      (.node 889330 ([(1,true),(2,true),(13,true),(6,false),(5,false),(4,false),(8,true)],[(0,true),(7,true),(3,false),(12,false),(11,false),(10,false),(9,false)])
                        (.node 889312 ([(4,true),(5,true),(6,true),(13,false),(2,false),(1,false),(8,true)],[(0,true),(7,false),(3,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 889828 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 890152 ([(4,true),(5,true),(6,true),(13,false),(2,false),(1,false),(9,false)],[(0,true),(10,true),(11,true),(12,true),(3,true),(7,true),(8,true)])
                      (.node 889876 ([(1,true),(2,true),(13,true),(6,false),(11,false),(4,true),(8,true)],[(0,true),(7,true),(5,true),(12,true),(3,true),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 890194 ([(4,true),(5,true),(6,true),(13,false),(2,false),(1,false),(8,true)],[(0,true),(7,false),(3,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 894532 ([(2,true),(3,true),(12,false),(0,false),(6,false),(5,false),(8,true)],[(13,false),(4,true),(7,false),(1,false),(11,false),(10,false),(9,false)])
                    (.node 894490 ([(2,true),(3,true),(12,false),(0,false),(6,false),(5,false),(9,false)],[(13,false),(4,true),(10,true),(11,true),(1,true),(7,true),(8,true)])
                      (.node 894466 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                        (.node 894190 ([(2,false),(1,false),(0,false),(13,false),(4,true),(5,true),(9,false)],[(6,false),(10,true),(11,true),(12,true),(3,false),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 894514 ([(5,true),(6,true),(0,true),(12,true),(3,false),(2,false),(8,true)],[(13,false),(4,true),(7,true),(1,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 895030 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                      (.node 895012 ([(6,true),(0,true),(1,true),(10,true),(4,false),(3,false),(8,true)],[(13,false),(12,false),(11,false),(5,true),(7,true),(2,false),(9,false)])
                        .empty
                        .empty)
                      (.node 895054 ([(6,true),(0,true),(11,false),(4,false),(3,false),(2,false),(8,true)],[(13,false),(12,false),(1,true),(7,false),(5,false),(10,false),(9,false)])
                        .empty
                        .empty))))
                (.node 897364 ([(6,true),(0,true),(1,true),(11,false),(4,false),(3,false),(8,true)],[(13,false),(12,false),(2,true),(7,false),(5,false),(10,false),(9,false)])
                  (.node 896206 ([(3,true),(12,false),(1,false),(0,false),(6,false),(5,false),(9,false)],[(13,false),(4,true),(10,true),(11,true),(2,true),(7,true),(8,true)])
                    (.node 895396 ([(5,true),(6,true),(0,true),(12,true),(3,false),(2,false),(8,true)],[(13,false),(4,true),(7,true),(1,false),(11,false),(10,false),(9,false)])
                      (.node 895366 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                        (.node 895354 ([(5,true),(10,false),(1,false),(0,false),(13,false),(3,false),(8,true)],[(6,false),(11,true),(12,true),(4,true),(7,true),(2,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 895414 ([(2,true),(3,true),(12,false),(0,false),(6,false),(5,false),(8,true)],[(13,false),(4,true),(7,false),(1,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 896890 ([(0,false),(13,false),(12,false),(2,true),(10,false),(5,true),(8,true)],[(6,false),(7,false),(1,true),(11,false),(3,true),(4,true),(9,false)])
                      (.node 896248 ([(3,true),(12,false),(1,false),(0,false),(6,false),(5,false),(8,true)],[(13,false),(4,true),(7,false),(2,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 896932 ([(1,true),(2,true),(3,true),(13,true),(6,false),(5,false),(8,true)],[(0,true),(7,true),(4,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 897718 ([(3,true),(12,false),(1,false),(0,false),(6,false),(5,false),(8,true)],[(13,false),(4,true),(7,false),(2,false),(11,false),(10,false),(9,false)])
                    (.node 897478 ([(1,true),(2,true),(10,true),(4,false),(13,true),(6,false),(8,true)],[(0,true),(7,true),(5,false),(11,true),(12,true),(3,false),(9,false)])
                      (.node 897448 ([(6,true),(0,true),(1,true),(11,false),(4,false),(3,false),(9,false)],[(13,false),(12,false),(2,true),(10,true),(5,true),(7,true),(8,true)])
                        (.node 897382 ([(3,true),(4,true),(11,true),(1,false),(0,false),(6,false),(8,true)],[(13,false),(12,false),(2,true),(7,true),(5,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 897706 ([(5,true),(6,true),(0,true),(1,true),(12,true),(3,false),(8,true)],[(13,false),(4,true),(7,true),(2,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 897814 ([(1,true),(2,true),(3,true),(13,true),(6,false),(5,false),(8,true)],[(0,true),(7,true),(4,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 897790 ([(5,true),(6,true),(13,false),(3,false),(2,false),(1,false),(8,true)],[(0,true),(7,false),(4,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 898606 ([(2,true),(3,true),(4,true),(10,true),(0,false),(6,false),(8,true)],[(13,false),(12,false),(11,false),(1,true),(7,true),(5,false),(9,false)])
                        .empty
                        .empty)))))))))
      (.node 1074550 ([(1,true),(13,false),(6,false),(5,false),(10,true),(3,true),(8,true)],[(2,true),(11,true),(12,true),(0,true),(7,true),(4,true),(9,false)])
        (.node 1022644 ([(0,true),(13,false),(4,true),(5,true),(10,false),(2,false),(8,true)],[(1,true),(7,false),(6,false),(11,true),(12,true),(3,false),(9,false)])
          (.node 993904 ([(2,true),(13,true),(0,false),(6,false),(10,false),(4,true),(8,true)],[(1,true),(7,true),(5,true),(11,true),(12,true),(3,true),(9,false)])
            (.node 914068 ([(1,true),(12,true),(13,true),(6,false),(10,true),(3,false),(8,true)],[(0,true),(7,true),(2,false),(11,false),(4,true),(5,true),(9,false)])
              (.node 906292 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                (.node 903916 ([(6,true),(13,false),(4,true),(11,false),(2,false),(1,false),(8,true)],[(0,true),(7,false),(5,false),(12,true),(3,false),(10,false),(9,false)])
                  (.node 900100 ([(5,true),(6,true),(13,false),(3,false),(2,false),(1,false),(9,false)],[(0,true),(10,true),(11,true),(12,true),(4,true),(7,true),(8,true)])
                    (.node 899758 ([(6,true),(0,true),(10,true),(4,false),(3,false),(2,false),(8,true)],[(13,false),(12,false),(11,false),(5,true),(7,true),(1,false),(9,false)])
                      (.node 898990 ([(1,true),(2,true),(3,true),(13,true),(6,false),(5,false),(8,true)],[(0,true),(7,true),(4,false),(12,false),(11,false),(10,false),(9,false)])
                        (.node 898948 ([(0,false),(13,false),(3,false),(2,false),(10,false),(5,true),(8,true)],[(6,false),(7,false),(1,true),(11,true),(12,true),(4,true),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 899800 ([(6,true),(13,false),(3,false),(11,false),(10,false),(1,false),(8,true)],[(0,true),(7,false),(5,false),(4,false),(12,false),(2,false),(9,false)])
                        .empty
                        .empty))
                    (.node 903286 ([(6,true),(0,true),(11,true),(4,false),(3,false),(2,false),(8,true)],[(13,false),(12,false),(5,true),(7,true),(1,false),(10,false),(9,false)])
                      (.node 903244 ([(5,false),(4,false),(13,true),(0,true),(1,true),(2,true),(8,true)],[(6,false),(7,true),(3,true),(12,false),(11,false),(10,false),(9,false)])
                        (.node 900142 ([(5,true),(6,true),(13,false),(3,false),(2,false),(1,false),(8,true)],[(0,true),(7,false),(4,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 903874 ([(6,true),(13,false),(4,true),(11,false),(2,false),(1,false),(9,false)],[(0,true),(10,true),(3,true),(12,false),(5,true),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 905704 ([(2,true),(3,true),(13,true),(0,true),(11,true),(5,false),(8,true)],[(6,false),(12,true),(4,true),(7,false),(1,false),(10,false),(9,false)])
                    (.node 905644 ([(4,false),(12,false),(6,true),(0,true),(1,true),(2,true),(8,true)],[(13,false),(3,false),(7,false),(5,true),(11,false),(10,false),(9,false)])
                      (.node 904954 ([(0,false),(6,false),(5,false),(4,false),(3,false),(2,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,false),(7,true),(8,true)])
                        (.node 904942 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 905686 ([(5,true),(6,true),(13,false),(3,false),(10,true),(1,true),(8,true)],[(0,true),(11,true),(12,true),(4,true),(7,true),(2,true),(9,false)])
                        .empty
                        .empty))
                    (.node 906130 ([(1,true),(10,false),(5,true),(6,true),(13,false),(3,false),(8,true)],[(0,true),(7,true),(2,false),(11,true),(12,true),(4,true),(9,false)])
                      (.node 906118 ([(3,true),(12,false),(6,true),(0,true),(1,true),(10,false),(9,false)],[(13,false),(4,true),(5,true),(11,false),(2,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 906274 ([(5,true),(6,true),(13,false),(3,false),(2,false),(1,false),(9,false)],[(0,true),(10,true),(11,true),(12,true),(4,true),(7,true),(8,true)])
                        .empty
                        .empty))))
                (.node 911494 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                  (.node 910888 ([(6,true),(13,false),(12,false),(1,true),(2,true),(3,true),(9,false)],[(0,true),(11,false),(10,false),(4,true),(5,true),(7,true),(8,true)])
                    (.node 907012 ([(0,false),(6,false),(5,false),(4,false),(3,false),(2,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,false),(7,true),(8,true)])
                      (.node 907000 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                        (.node 906316 ([(5,true),(6,true),(13,false),(3,false),(2,false),(1,false),(8,true)],[(0,true),(7,false),(4,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 910846 ([(5,false),(13,true),(0,true),(1,true),(2,true),(3,true),(8,true)],[(6,false),(7,true),(4,true),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 911332 ([(2,true),(3,true),(4,true),(12,false),(0,false),(6,false),(9,false)],[(13,false),(5,true),(10,true),(11,true),(1,true),(7,true),(8,true)])
                      (.node 911320 ([(4,true),(5,true),(6,true),(0,true),(11,false),(2,false),(8,true)],[(13,false),(12,false),(1,true),(7,false),(3,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 911476 ([(6,true),(0,true),(12,true),(4,false),(10,false),(2,true),(8,true)],[(13,false),(5,true),(7,true),(3,true),(11,true),(1,true),(9,false)])
                        .empty
                        .empty)))
                  (.node 912946 ([(6,true),(0,true),(1,true),(12,true),(4,false),(3,false),(8,true)],[(13,false),(5,true),(7,true),(2,false),(11,false),(10,false),(9,false)])
                    (.node 912214 ([(2,true),(10,true),(6,true),(0,true),(12,true),(4,false),(8,true)],[(13,false),(5,true),(11,true),(1,true),(7,true),(3,false),(9,false)])
                      (.node 912202 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                        (.node 911518 ([(6,true),(0,true),(12,true),(4,false),(3,false),(2,false),(8,true)],[(13,false),(5,true),(7,true),(1,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 912904 ([(5,false),(13,true),(0,true),(1,true),(2,true),(3,true),(8,true)],[(6,false),(7,true),(4,true),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 913846 ([(3,true),(4,true),(12,false),(1,false),(0,false),(6,false),(8,true)],[(13,false),(5,true),(7,false),(2,false),(11,false),(10,false),(9,false)])
                      (.node 913828 ([(6,true),(0,true),(1,true),(12,true),(4,false),(3,false),(8,true)],[(13,false),(5,true),(7,true),(2,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 914056 ([(3,true),(4,true),(12,false),(1,false),(0,false),(6,false),(9,false)],[(13,false),(5,true),(10,true),(11,true),(2,true),(7,true),(8,true)])
                        .empty
                        .empty)))))
              (.node 918322 ([(6,true),(13,false),(4,false),(3,false),(2,false),(1,false),(8,true)],[(0,true),(7,false),(5,false),(12,false),(11,false),(10,false),(9,false)])
                (.node 916222 ([(6,true),(13,false),(4,false),(3,false),(2,false),(1,false),(9,false)],[(0,true),(10,true),(11,true),(12,true),(5,true),(7,true),(8,true)])
                  (.node 915340 ([(6,true),(0,true),(10,false),(4,true),(12,false),(2,false),(8,true)],[(13,false),(5,true),(7,true),(1,false),(11,true),(3,true),(9,false)])
                    (.node 914644 ([(3,true),(4,true),(13,true),(6,false),(11,true),(1,false),(8,true)],[(0,true),(7,false),(2,false),(12,true),(5,true),(10,false),(9,false)])
                      (.node 914614 ([(1,true),(12,true),(13,true),(6,false),(10,false),(3,true),(8,true)],[(0,true),(7,true),(4,true),(5,true),(11,true),(2,true),(9,false)])
                        (.node 914596 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 914656 ([(1,true),(11,false),(6,true),(13,false),(4,false),(3,false),(8,true)],[(0,true),(7,true),(2,false),(12,true),(5,true),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 915436 ([(4,true),(5,true),(6,true),(0,true),(11,true),(2,false),(8,true)],[(13,false),(12,false),(3,true),(7,true),(1,false),(10,false),(9,false)])
                      (.node 915364 ([(2,true),(3,true),(10,true),(0,false),(13,false),(5,true),(8,true)],[(6,false),(7,false),(1,false),(11,true),(12,true),(4,false),(9,false)])
                        .empty
                        .empty)
                      (.node 915448 ([(2,true),(3,true),(4,true),(13,true),(0,true),(10,false),(9,false)],[(6,false),(5,false),(12,false),(11,false),(1,true),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 916966 ([(1,true),(2,true),(11,false),(6,true),(13,false),(4,false),(8,true)],[(0,true),(7,true),(3,false),(12,true),(5,true),(10,false),(9,false)])
                    (.node 916918 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                      (.node 916906 ([(4,true),(13,true),(6,false),(11,true),(2,false),(1,false),(9,false)],[(0,true),(10,true),(5,false),(12,false),(3,true),(7,true),(8,true)])
                        (.node 916264 ([(6,true),(13,false),(4,false),(3,false),(2,false),(1,false),(8,true)],[(0,true),(7,false),(5,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 916948 ([(4,true),(12,false),(2,false),(10,true),(6,true),(0,true),(8,true)],[(13,false),(5,true),(11,true),(3,true),(7,true),(1,true),(9,false)])
                        .empty
                        .empty))
                    (.node 917692 ([(6,true),(13,false),(4,false),(3,false),(10,true),(1,true),(8,true)],[(0,true),(11,true),(12,true),(5,true),(7,true),(2,true),(9,false)])
                      (.node 917650 ([(7,true),(3,true),(4,true),(13,true),(0,true),(1,true),(9,false)],[(6,false),(5,false),(12,false),(11,false),(10,false),(2,true),(8,true)])
                        .empty
                        .empty)
                      (.node 918280 ([(6,true),(13,false),(4,false),(3,false),(2,false),(1,false),(9,false)],[(0,true),(10,true),(11,true),(12,true),(5,true),(7,true),(8,true)])
                        .empty
                        .empty))))
                (.node 923464 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                  (.node 922846 ([(0,false),(13,false),(5,true),(11,false),(2,true),(3,true),(8,true)],[(6,false),(12,true),(4,false),(7,false),(1,true),(10,false),(9,false)])
                    (.node 922492 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                      (.node 919360 ([(0,false),(6,false),(5,false),(4,false),(3,false),(2,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,false),(7,true),(8,true)])
                        (.node 919348 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 922504 ([(2,true),(10,true),(0,false),(6,false),(5,false),(4,false),(8,true)],[(13,false),(12,false),(11,false),(1,true),(7,true),(3,false),(9,false)])
                        .empty
                        .empty))
                    (.node 923080 ([(4,true),(5,true),(6,true),(0,true),(10,true),(2,false),(8,true)],[(13,false),(12,false),(11,false),(3,true),(7,true),(1,false),(9,false)])
                      (.node 922888 ([(0,false),(6,false),(5,false),(4,false),(10,true),(2,true),(8,true)],[(13,false),(12,false),(11,false),(1,false),(7,true),(3,true),(9,false)])
                        .empty
                        .empty)
                      (.node 923122 ([(7,true),(0,false),(13,false),(5,true),(11,false),(2,false),(9,false)],[(6,false),(12,true),(4,false),(3,false),(10,false),(1,false),(8,true)])
                        .empty
                        .empty)))
                  (.node 993298 ([(5,true),(6,true),(11,false),(3,false),(13,true),(1,true),(8,true)],[(0,false),(12,true),(2,false),(7,false),(4,false),(10,false),(9,false)])
                    (.node 992590 ([(4,true),(10,true),(1,false),(13,false),(12,false),(6,false),(8,true)],[(0,false),(11,false),(2,true),(3,true),(7,true),(5,false),(9,false)])
                      (.node 992578 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                        (.node 923476 ([(0,false),(6,false),(5,false),(4,false),(3,false),(2,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,false),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 993274 ([(2,true),(13,true),(0,false),(11,false),(4,true),(5,true),(8,true)],[(1,true),(7,true),(6,true),(12,true),(3,true),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 993460 ([(6,true),(0,true),(13,false),(3,true),(4,true),(10,false),(9,false)],[(1,true),(2,true),(12,false),(11,false),(5,true),(7,true),(8,true)])
                      (.node 993316 ([(2,true),(13,true),(0,false),(11,false),(10,false),(5,false),(8,true)],[(1,true),(7,true),(4,false),(3,false),(12,false),(6,false),(9,false)])
                        .empty
                        .empty)
                      (.node 993472 ([(4,true),(5,true),(6,true),(0,true),(13,false),(2,false),(9,false)],[(1,true),(10,true),(11,true),(12,true),(3,true),(7,true),(8,true)])
                        .empty
                        .empty))))))
            (.node 1009396 ([(3,true),(4,true),(10,true),(1,false),(0,false),(6,false),(8,true)],[(13,false),(12,false),(11,false),(2,true),(7,true),(5,false),(9,false)])
              (.node 1003858 ([(2,true),(13,true),(0,false),(10,false),(4,true),(5,true),(8,true)],[(1,true),(7,true),(6,true),(11,true),(12,true),(3,true),(9,false)])
                (.node 1001506 ([(1,false),(13,false),(3,true),(4,true),(10,true),(6,false),(8,true)],[(0,false),(11,true),(12,true),(2,false),(7,true),(5,false),(9,false)])
                  (.node 998116 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                    (.node 996706 ([(3,false),(2,false),(1,false),(0,false),(6,false),(5,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,false),(7,true),(8,true)])
                      (.node 996694 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                        (.node 993946 ([(2,true),(13,true),(0,false),(6,false),(5,false),(4,false),(8,true)],[(1,true),(7,true),(3,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 998086 ([(5,true),(10,true),(3,false),(2,false),(1,false),(0,false),(8,true)],[(13,false),(12,false),(11,false),(4,true),(7,true),(6,false),(9,false)])
                        .empty
                        .empty))
                    (.node 998704 ([(0,true),(1,true),(2,true),(3,true),(10,true),(5,false),(8,true)],[(13,false),(12,false),(11,false),(6,true),(7,true),(4,false),(9,false)])
                      (.node 998428 ([(7,true),(0,true),(13,false),(2,false),(11,false),(5,true),(9,false)],[(1,true),(12,true),(3,true),(4,true),(10,false),(6,true),(8,true)])
                        (.node 998176 ([(4,true),(11,true),(2,true),(13,true),(0,false),(6,false),(8,true)],[(1,true),(12,true),(3,true),(7,true),(5,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 998746 ([(0,true),(13,false),(2,false),(11,false),(5,false),(4,false),(8,true)],[(1,true),(12,true),(3,true),(7,false),(6,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1003228 ([(1,false),(13,false),(3,true),(4,true),(5,true),(6,true),(8,true)],[(0,false),(7,false),(2,true),(12,false),(11,false),(10,false),(9,false)])
                    (.node 1002232 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                      (.node 1002202 ([(5,true),(10,true),(11,true),(3,false),(13,true),(0,false),(8,true)],[(1,true),(2,true),(12,false),(4,true),(7,true),(6,false),(9,false)])
                        (.node 1001548 ([(7,true),(4,false),(3,false),(13,true),(0,false),(6,false),(9,false)],[(1,true),(2,true),(12,false),(11,false),(10,false),(5,false),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1002976 ([(1,false),(13,false),(3,true),(4,true),(5,true),(6,true),(9,false)],[(0,false),(10,true),(11,true),(12,true),(2,false),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1003762 ([(4,true),(5,true),(6,true),(0,true),(13,false),(2,false),(9,false)],[(1,true),(10,true),(11,true),(12,true),(3,true),(7,true),(8,true)])
                      (.node 1003750 ([(6,true),(0,true),(1,true),(2,true),(12,false),(4,false),(8,true)],[(13,false),(3,true),(7,false),(5,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1003834 ([(6,true),(0,true),(1,true),(2,true),(12,false),(4,false),(9,false)],[(13,false),(3,true),(10,true),(11,true),(5,true),(7,true),(8,true)])
                        .empty
                        .empty))))
                (.node 1006906 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                  (.node 1005034 ([(1,false),(13,false),(3,true),(4,true),(5,true),(6,true),(9,false)],[(0,false),(10,true),(11,true),(12,true),(2,false),(7,true),(8,true)])
                    (.node 1004602 ([(4,true),(5,true),(10,true),(2,true),(13,true),(0,false),(8,true)],[(1,true),(11,true),(12,true),(3,true),(7,true),(6,false),(9,false)])
                      (.node 1004350 ([(4,true),(12,true),(2,false),(1,false),(0,false),(6,false),(8,true)],[(13,false),(3,true),(7,true),(5,false),(11,false),(10,false),(9,false)])
                        (.node 1004338 ([(6,true),(0,true),(1,true),(2,true),(12,false),(4,false),(8,true)],[(13,false),(3,true),(7,false),(5,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1004626 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1006252 ([(1,false),(0,false),(6,false),(12,true),(3,true),(4,true),(8,true)],[(13,false),(2,false),(7,true),(5,true),(11,false),(10,false),(9,false)])
                      (.node 1005286 ([(1,false),(13,false),(3,true),(4,true),(5,true),(6,true),(8,true)],[(0,false),(7,false),(2,true),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1006294 ([(2,true),(13,true),(0,false),(6,false),(5,false),(4,false),(8,true)],[(1,true),(7,true),(3,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1007428 ([(2,true),(13,true),(0,false),(6,false),(11,false),(4,true),(8,true)],[(1,true),(7,true),(5,true),(12,true),(3,true),(10,false),(9,false)])
                    (.node 1006978 ([(0,true),(1,true),(2,true),(12,false),(5,false),(4,false),(8,true)],[(13,false),(3,true),(7,false),(6,false),(11,false),(10,false),(9,false)])
                      (.node 1006954 ([(4,true),(5,true),(12,true),(2,false),(1,false),(0,false),(8,true)],[(13,false),(3,true),(7,true),(6,false),(11,false),(10,false),(9,false)])
                        (.node 1006936 ([(0,true),(1,true),(2,true),(12,false),(5,false),(4,false),(9,false)],[(13,false),(3,true),(10,true),(11,true),(6,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1007410 ([(5,true),(11,false),(3,false),(2,false),(1,false),(0,false),(9,false)],[(13,false),(12,false),(6,true),(10,true),(4,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1007524 ([(0,true),(1,true),(2,true),(3,true),(11,true),(5,false),(8,true)],[(13,false),(12,false),(6,true),(7,true),(4,false),(10,false),(9,false)])
                      (.node 1007494 ([(5,true),(6,true),(0,true),(13,false),(3,true),(10,false),(9,false)],[(1,true),(2,true),(12,false),(11,false),(4,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1009378 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                        .empty
                        .empty)))))
              (.node 1014964 ([(6,true),(0,true),(1,true),(11,false),(4,false),(3,false),(8,true)],[(13,false),(12,false),(2,true),(7,false),(5,false),(10,false),(9,false)])
                (.node 1010302 ([(6,true),(0,true),(13,false),(4,true),(10,false),(2,false),(8,true)],[(1,true),(7,false),(5,false),(11,true),(12,true),(3,false),(9,false)])
                  (.node 1009762 ([(5,true),(6,true),(0,true),(13,false),(3,false),(2,false),(8,true)],[(1,true),(7,false),(4,false),(12,false),(11,false),(10,false),(9,false)])
                    (.node 1009714 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                      (.node 1009438 ([(3,true),(12,false),(0,true),(1,true),(10,false),(5,false),(8,true)],[(13,false),(4,true),(7,false),(2,false),(11,true),(6,false),(9,false)])
                        (.node 1009426 ([(5,true),(6,true),(11,false),(1,false),(13,false),(3,false),(8,true)],[(0,false),(12,true),(4,true),(7,true),(2,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1009738 ([(2,true),(11,true),(0,true),(13,false),(4,true),(5,true),(8,true)],[(1,true),(7,true),(6,true),(12,true),(3,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1010260 ([(6,true),(0,true),(1,true),(10,true),(4,false),(3,false),(8,true)],[(13,false),(12,false),(11,false),(5,true),(7,true),(2,false),(9,false)])
                      (.node 1009780 ([(2,true),(3,true),(13,true),(0,false),(6,false),(5,false),(8,true)],[(1,true),(7,true),(4,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1010278 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1013512 ([(3,true),(12,false),(1,false),(0,false),(6,false),(5,false),(9,false)],[(13,false),(4,true),(10,true),(11,true),(2,true),(7,true),(8,true)])
                    (.node 1010644 ([(5,true),(6,true),(0,true),(13,false),(3,false),(2,false),(8,true)],[(1,true),(7,false),(4,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1010602 ([(5,true),(6,true),(0,true),(13,false),(3,false),(2,false),(9,false)],[(1,true),(10,true),(11,true),(12,true),(4,true),(7,true),(8,true)])
                        (.node 1010326 ([(2,true),(3,true),(13,true),(0,false),(11,false),(5,true),(8,true)],[(1,true),(7,true),(6,true),(12,true),(4,true),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1013494 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1014550 ([(5,true),(10,true),(2,false),(12,true),(13,true),(0,false),(8,true)],[(1,true),(11,false),(3,true),(4,true),(7,true),(6,false),(9,false)])
                      (.node 1013554 ([(3,true),(12,false),(1,false),(0,false),(6,false),(5,false),(8,true)],[(13,false),(4,true),(7,false),(2,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1014580 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                        .empty
                        .empty))))
                (.node 1017382 ([(1,false),(13,false),(3,false),(11,false),(5,true),(6,true),(9,false)],[(0,false),(10,true),(4,false),(12,false),(2,false),(7,true),(8,true)])
                  (.node 1015912 ([(2,true),(3,true),(13,true),(0,false),(10,false),(5,true),(8,true)],[(1,true),(7,true),(6,true),(11,true),(12,true),(4,true),(9,false)])
                    (.node 1015432 ([(5,true),(6,true),(0,true),(13,false),(12,false),(2,true),(9,false)],[(1,true),(11,false),(10,false),(3,true),(4,true),(7,true),(8,true)])
                      (.node 1015234 ([(3,true),(13,true),(1,true),(11,false),(5,true),(6,true),(8,true)],[(0,false),(7,false),(2,false),(12,true),(4,true),(10,false),(9,false)])
                        (.node 1014982 ([(3,true),(4,true),(11,true),(1,false),(0,false),(6,false),(8,true)],[(13,false),(12,false),(2,true),(7,true),(5,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1015462 ([(0,true),(1,true),(11,false),(5,false),(4,false),(3,false),(9,false)],[(13,false),(12,false),(2,true),(10,true),(6,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1016608 ([(5,true),(10,true),(2,true),(3,true),(13,true),(0,false),(8,true)],[(1,true),(11,true),(12,true),(4,true),(7,true),(6,false),(9,false)])
                      (.node 1015954 ([(2,true),(3,true),(13,true),(0,false),(6,false),(5,false),(8,true)],[(1,true),(7,true),(4,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1016638 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1021408 ([(3,true),(4,true),(5,true),(10,true),(1,false),(0,false),(8,true)],[(13,false),(12,false),(11,false),(2,true),(7,true),(6,false),(9,false)])
                    (.node 1020592 ([(6,true),(11,true),(4,false),(13,true),(1,true),(2,true),(9,false)],[(0,false),(10,false),(3,true),(12,false),(5,true),(7,true),(8,true)])
                      (.node 1020550 ([(7,true),(3,true),(4,true),(11,false),(0,true),(1,true),(9,false)],[(13,false),(12,false),(5,true),(6,true),(10,false),(2,true),(8,true)])
                        (.node 1017634 ([(1,false),(13,false),(3,false),(11,false),(5,true),(6,true),(8,true)],[(0,false),(7,false),(2,true),(12,true),(4,true),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1021156 ([(3,true),(4,true),(11,false),(1,false),(0,false),(6,false),(8,true)],[(13,false),(12,false),(5,true),(7,false),(2,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1021750 ([(1,false),(13,false),(4,true),(11,false),(10,false),(6,true),(8,true)],[(0,false),(7,false),(2,true),(3,true),(12,false),(5,true),(9,false)])
                      (.node 1021498 ([(2,true),(11,true),(4,false),(13,true),(0,false),(6,false),(8,true)],[(1,true),(7,true),(5,false),(12,true),(3,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1022602 ([(0,true),(1,true),(10,true),(5,false),(4,false),(3,false),(8,true)],[(13,false),(12,false),(11,false),(6,true),(7,true),(2,false),(9,false)])
                        .empty
                        .empty)))))))
          (.node 1048096 ([(6,false),(13,true),(1,true),(2,true),(3,true),(4,true),(8,true)],[(0,false),(7,true),(5,true),(12,false),(11,false),(10,false),(9,false)])
            (.node 1032562 ([(6,true),(0,true),(1,true),(2,true),(12,true),(4,false),(8,true)],[(13,false),(5,true),(7,true),(3,false),(11,false),(10,false),(9,false)])
              (.node 1026742 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                (.node 1024114 ([(0,true),(1,true),(2,true),(3,true),(12,false),(5,false),(9,false)],[(13,false),(4,true),(10,true),(11,true),(6,true),(7,true),(8,true)])
                  (.node 1023760 ([(3,true),(4,true),(5,true),(11,false),(1,false),(0,false),(8,true)],[(13,false),(12,false),(6,true),(7,false),(2,false),(10,false),(9,false)])
                    (.node 1023538 ([(5,true),(11,false),(2,true),(3,true),(13,true),(0,false),(9,false)],[(1,true),(10,false),(6,false),(12,true),(4,true),(7,true),(8,true)])
                      (.node 1022992 ([(5,true),(6,true),(0,true),(13,false),(3,false),(2,false),(8,true)],[(1,true),(7,false),(4,false),(12,false),(11,false),(10,false),(9,false)])
                        (.node 1022950 ([(5,true),(6,true),(0,true),(13,false),(3,false),(2,false),(9,false)],[(1,true),(10,true),(11,true),(12,true),(4,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1023550 ([(3,true),(4,true),(5,true),(11,false),(1,false),(0,false),(9,false)],[(13,false),(12,false),(6,true),(10,true),(2,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1023892 ([(2,true),(3,true),(13,true),(0,false),(6,false),(5,false),(8,true)],[(1,true),(7,true),(4,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1023874 ([(5,true),(6,true),(0,true),(13,false),(3,false),(2,false),(8,true)],[(1,true),(7,false),(4,false),(12,false),(11,false),(10,false),(9,false)])
                        (.node 1023778 ([(0,true),(1,true),(2,true),(3,true),(12,false),(5,false),(9,false)],[(13,false),(4,true),(10,true),(11,true),(6,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1024102 ([(2,true),(10,false),(5,true),(12,true),(13,true),(0,false),(8,true)],[(1,true),(7,true),(6,false),(11,false),(3,true),(4,true),(9,false)])
                        .empty
                        .empty)))
                  (.node 1026154 ([(3,true),(4,true),(13,true),(1,true),(11,true),(6,false),(8,true)],[(0,false),(12,true),(5,true),(7,false),(2,false),(10,false),(9,false)])
                    (.node 1026094 ([(5,false),(12,false),(0,true),(1,true),(2,true),(3,true),(8,true)],[(13,false),(4,false),(7,false),(6,true),(11,false),(10,false),(9,false)])
                      (.node 1024702 ([(0,true),(13,false),(12,false),(5,false),(10,false),(2,false),(8,true)],[(1,true),(7,false),(6,false),(11,false),(4,false),(3,false),(9,false)])
                        (.node 1024660 ([(0,true),(1,true),(10,true),(5,true),(12,true),(3,false),(8,true)],[(13,false),(4,true),(11,true),(6,true),(7,true),(2,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1026136 ([(6,true),(0,true),(13,false),(4,false),(10,true),(2,true),(8,true)],[(1,true),(11,true),(12,true),(5,true),(7,true),(3,true),(9,false)])
                        .empty
                        .empty))
                    (.node 1026580 ([(2,true),(10,false),(6,true),(0,true),(13,false),(4,false),(8,true)],[(1,true),(7,true),(3,false),(11,true),(12,true),(5,true),(9,false)])
                      (.node 1026568 ([(4,true),(12,false),(0,true),(1,true),(2,true),(10,false),(9,false)],[(13,false),(5,true),(6,true),(11,false),(3,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1026724 ([(6,true),(0,true),(13,false),(4,false),(3,false),(2,false),(9,false)],[(1,true),(10,true),(11,true),(12,true),(5,true),(7,true),(8,true)])
                        .empty
                        .empty))))
                (.node 1031356 ([(4,true),(5,true),(10,true),(2,false),(1,false),(0,false),(8,true)],[(13,false),(12,false),(11,false),(3,true),(7,true),(6,false),(9,false)])
                  (.node 1030222 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                    (.node 1027462 ([(1,false),(0,false),(6,false),(5,false),(4,false),(3,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,false),(7,true),(8,true)])
                      (.node 1027450 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                        (.node 1026766 ([(6,true),(0,true),(13,false),(4,false),(3,false),(2,false),(8,true)],[(1,true),(7,false),(5,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1030210 ([(6,true),(10,false),(2,false),(1,false),(13,false),(4,false),(8,true)],[(0,false),(11,true),(12,true),(5,true),(7,true),(3,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1030270 ([(3,true),(4,true),(12,false),(1,false),(0,false),(6,false),(8,true)],[(13,false),(5,true),(7,false),(2,false),(11,false),(10,false),(9,false)])
                      (.node 1030252 ([(6,true),(0,true),(1,true),(12,true),(4,false),(3,false),(8,true)],[(13,false),(5,true),(7,true),(2,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1031104 ([(3,false),(2,false),(1,false),(13,false),(5,true),(6,true),(9,false)],[(0,false),(10,true),(11,true),(12,true),(4,false),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1032238 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                    (.node 1031698 ([(3,true),(4,true),(12,false),(1,false),(0,false),(6,false),(9,false)],[(13,false),(5,true),(10,true),(11,true),(2,true),(7,true),(8,true)])
                      (.node 1031446 ([(3,true),(4,true),(12,false),(1,false),(0,false),(6,false),(8,true)],[(13,false),(5,true),(7,false),(2,false),(11,false),(10,false),(9,false)])
                        (.node 1031428 ([(6,true),(0,true),(1,true),(12,true),(4,false),(3,false),(8,true)],[(13,false),(5,true),(7,true),(2,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1031716 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1032286 ([(3,true),(4,true),(5,true),(11,true),(1,false),(0,false),(8,true)],[(13,false),(12,false),(2,true),(7,true),(6,false),(10,false),(9,false)])
                      (.node 1032262 ([(0,true),(1,true),(2,true),(10,true),(5,false),(4,false),(8,true)],[(13,false),(12,false),(11,false),(6,true),(7,true),(3,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1032304 ([(0,true),(1,true),(11,false),(5,false),(4,false),(3,false),(8,true)],[(13,false),(12,false),(2,true),(7,false),(6,false),(10,false),(9,false)])
                        .empty
                        .empty)))))
              (.node 1037008 ([(0,true),(1,true),(10,true),(5,false),(4,false),(3,false),(8,true)],[(13,false),(12,false),(11,false),(6,true),(7,true),(2,false),(9,false)])
                (.node 1034614 ([(0,true),(1,true),(2,true),(11,false),(5,false),(4,false),(8,true)],[(13,false),(12,false),(3,true),(7,false),(6,false),(10,false),(9,false)])
                  (.node 1033414 ([(4,true),(12,false),(2,false),(1,false),(0,false),(6,false),(9,false)],[(13,false),(5,true),(10,true),(11,true),(3,true),(7,true),(8,true)])
                    (.node 1032670 ([(2,true),(3,true),(4,true),(13,true),(0,false),(6,false),(8,true)],[(1,true),(7,true),(5,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1032646 ([(6,true),(0,true),(13,false),(4,false),(3,false),(2,false),(8,true)],[(1,true),(7,false),(5,false),(12,false),(11,false),(10,false),(9,false)])
                        (.node 1032574 ([(4,true),(12,false),(2,false),(1,false),(0,false),(6,false),(8,true)],[(13,false),(5,true),(7,false),(3,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1033162 ([(4,true),(12,false),(2,false),(1,false),(0,false),(6,false),(8,true)],[(13,false),(5,true),(7,false),(3,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1034098 ([(1,false),(13,false),(12,false),(3,true),(10,false),(6,true),(8,true)],[(0,false),(7,false),(2,true),(11,false),(4,true),(5,true),(9,false)])
                      (.node 1033846 ([(2,true),(3,true),(4,true),(13,true),(0,false),(6,false),(8,true)],[(1,true),(7,true),(5,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1034590 ([(4,true),(5,true),(11,true),(2,false),(1,false),(0,false),(8,true)],[(13,false),(12,false),(3,true),(7,true),(6,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1035562 ([(7,true),(5,false),(4,false),(11,false),(1,false),(0,false),(9,false)],[(13,false),(12,false),(3,false),(2,false),(10,false),(6,false),(8,true)])
                    (.node 1034956 ([(6,true),(0,true),(13,false),(4,false),(3,false),(2,false),(9,false)],[(1,true),(10,true),(11,true),(12,true),(5,true),(7,true),(8,true)])
                      (.node 1034698 ([(0,true),(1,true),(2,true),(11,false),(5,false),(4,false),(9,false)],[(13,false),(12,false),(3,true),(10,true),(6,true),(7,true),(8,true)])
                        (.node 1034686 ([(2,true),(3,true),(10,true),(5,false),(13,true),(0,false),(8,true)],[(1,true),(7,true),(6,false),(11,true),(12,true),(4,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1034998 ([(6,true),(0,true),(13,false),(4,false),(3,false),(2,false),(8,true)],[(1,true),(7,false),(5,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1035904 ([(2,true),(3,true),(4,true),(13,true),(0,false),(6,false),(8,true)],[(1,true),(7,true),(5,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1035814 ([(3,true),(4,true),(5,true),(10,true),(1,false),(0,false),(8,true)],[(13,false),(12,false),(11,false),(2,true),(7,true),(6,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1036156 ([(1,false),(13,false),(4,false),(3,false),(10,false),(6,true),(8,true)],[(0,false),(7,false),(2,true),(11,true),(12,true),(5,true),(9,false)])
                        .empty
                        .empty))))
                (.node 1042954 ([(3,true),(10,true),(1,false),(0,false),(6,false),(5,false),(8,true)],[(13,false),(12,false),(11,false),(2,true),(7,true),(4,false),(9,false)])
                  (.node 1040536 ([(0,true),(1,true),(11,true),(5,false),(4,false),(3,false),(8,true)],[(13,false),(12,false),(6,true),(7,true),(2,false),(10,false),(9,false)])
                    (.node 1039810 ([(1,false),(0,false),(6,false),(5,false),(4,false),(3,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,false),(7,true),(8,true)])
                      (.node 1039798 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                        (.node 1037050 ([(0,true),(13,false),(4,false),(11,false),(10,false),(2,false),(8,true)],[(1,true),(7,false),(6,false),(5,false),(12,false),(3,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1040494 ([(6,false),(5,false),(13,true),(1,true),(2,true),(3,true),(8,true)],[(0,false),(7,true),(4,true),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1041166 ([(0,true),(13,false),(5,true),(11,false),(3,false),(2,false),(8,true)],[(1,true),(7,false),(6,false),(12,true),(4,false),(10,false),(9,false)])
                      (.node 1041124 ([(0,true),(13,false),(5,true),(11,false),(3,false),(2,false),(9,false)],[(1,true),(10,true),(4,true),(12,false),(6,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1042942 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1043914 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                    (.node 1043530 ([(5,true),(6,true),(0,true),(1,true),(10,true),(3,false),(8,true)],[(13,false),(12,false),(11,false),(4,true),(7,true),(2,false),(9,false)])
                      (.node 1043338 ([(1,false),(0,false),(6,false),(5,false),(10,true),(3,true),(8,true)],[(13,false),(12,false),(11,false),(2,false),(7,true),(4,true),(9,false)])
                        (.node 1043296 ([(1,false),(13,false),(6,true),(11,false),(3,true),(4,true),(8,true)],[(0,false),(12,true),(5,false),(7,false),(2,true),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1043572 ([(7,true),(1,false),(13,false),(6,true),(11,false),(3,false),(9,false)],[(0,false),(12,true),(5,false),(4,false),(10,false),(2,false),(8,true)])
                        .empty
                        .empty))
                    (.node 1047058 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                      (.node 1043926 ([(1,false),(0,false),(6,false),(5,false),(4,false),(3,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,false),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1047070 ([(3,true),(10,true),(0,true),(1,true),(12,true),(5,false),(8,true)],[(13,false),(6,true),(11,true),(2,true),(7,true),(4,false),(9,false)])
                        .empty
                        .empty))))))
            (.node 1063138 ([(6,true),(0,true),(1,true),(2,true),(10,true),(4,false),(8,true)],[(13,false),(12,false),(11,false),(5,true),(7,true),(3,false),(9,false)])
              (.node 1051804 ([(5,true),(12,false),(3,false),(10,true),(0,true),(1,true),(8,true)],[(13,false),(6,true),(11,true),(4,true),(7,true),(2,true),(9,false)])
                (.node 1049512 ([(2,true),(11,false),(0,true),(13,false),(5,false),(4,false),(8,true)],[(1,true),(7,true),(3,false),(12,true),(6,true),(10,false),(9,false)])
                  (.node 1048726 ([(0,true),(1,true),(12,true),(5,false),(10,false),(3,true),(8,true)],[(13,false),(6,true),(7,true),(4,true),(11,true),(2,true),(9,false)])
                    (.node 1048246 ([(3,true),(4,true),(5,true),(12,false),(1,false),(0,false),(9,false)],[(13,false),(6,true),(10,true),(11,true),(2,true),(7,true),(8,true)])
                      (.node 1048234 ([(5,true),(6,true),(0,true),(1,true),(11,false),(3,false),(8,true)],[(13,false),(12,false),(2,true),(7,false),(4,false),(10,false),(9,false)])
                        (.node 1048138 ([(0,true),(13,false),(12,false),(2,true),(3,true),(4,true),(9,false)],[(1,true),(11,false),(10,false),(5,true),(6,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1048702 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1049470 ([(2,true),(12,true),(13,true),(0,false),(10,false),(4,true),(8,true)],[(1,true),(7,true),(5,true),(6,true),(11,true),(3,true),(9,false)])
                      (.node 1049452 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                        (.node 1048768 ([(0,true),(1,true),(12,true),(5,false),(4,false),(3,false),(8,true)],[(13,false),(6,true),(7,true),(2,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1049500 ([(4,true),(5,true),(13,true),(0,false),(11,true),(2,false),(8,true)],[(1,true),(7,false),(3,false),(12,true),(6,true),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1051054 ([(4,true),(5,true),(12,false),(2,false),(1,false),(0,false),(8,true)],[(13,false),(6,true),(7,false),(3,false),(11,false),(10,false),(9,false)])
                    (.node 1050970 ([(4,true),(5,true),(12,false),(2,false),(1,false),(0,false),(9,false)],[(13,false),(6,true),(10,true),(11,true),(3,true),(7,true),(8,true)])
                      (.node 1050196 ([(0,true),(1,true),(2,true),(12,true),(5,false),(4,false),(8,true)],[(13,false),(6,true),(7,true),(3,false),(11,false),(10,false),(9,false)])
                        (.node 1050154 ([(6,false),(13,true),(1,true),(2,true),(3,true),(4,true),(8,true)],[(0,false),(7,true),(5,true),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1050982 ([(2,true),(12,true),(13,true),(0,false),(10,true),(4,false),(8,true)],[(1,true),(7,true),(3,false),(11,false),(5,true),(6,true),(9,false)])
                        .empty
                        .empty))
                    (.node 1051762 ([(5,true),(13,true),(0,false),(11,true),(3,false),(2,false),(9,false)],[(1,true),(10,true),(6,false),(12,false),(4,true),(7,true),(8,true)])
                      (.node 1051078 ([(0,true),(1,true),(2,true),(12,true),(5,false),(4,false),(8,true)],[(13,false),(6,true),(7,true),(3,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1051774 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                        .empty
                        .empty))))
                (.node 1054216 ([(1,false),(0,false),(6,false),(5,false),(4,false),(3,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,false),(7,true),(8,true)])
                  (.node 1052590 ([(0,true),(1,true),(10,false),(5,true),(12,false),(3,false),(8,true)],[(13,false),(6,true),(7,true),(2,false),(11,true),(4,true),(9,false)])
                    (.node 1052362 ([(3,true),(4,true),(5,true),(13,true),(1,true),(10,false),(9,false)],[(0,false),(6,false),(12,false),(11,false),(2,true),(7,true),(8,true)])
                      (.node 1052350 ([(5,true),(6,true),(0,true),(1,true),(11,true),(3,false),(8,true)],[(13,false),(12,false),(4,true),(7,true),(2,false),(10,false),(9,false)])
                        (.node 1051822 ([(2,true),(3,true),(11,false),(0,true),(13,false),(5,false),(8,true)],[(1,true),(7,true),(4,false),(12,true),(6,true),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1052572 ([(3,true),(4,true),(10,true),(1,false),(13,false),(6,true),(8,true)],[(0,false),(7,false),(2,false),(11,true),(12,true),(5,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1053514 ([(0,true),(13,false),(5,false),(4,false),(3,false),(2,false),(8,true)],[(1,true),(7,false),(6,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1053472 ([(0,true),(13,false),(5,false),(4,false),(3,false),(2,false),(9,false)],[(1,true),(10,true),(11,true),(12,true),(6,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1054204 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1062550 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                    (.node 1055530 ([(0,true),(13,false),(5,false),(4,false),(3,false),(2,false),(9,false)],[(1,true),(10,true),(11,true),(12,true),(6,true),(7,true),(8,true)])
                      (.node 1054942 ([(0,true),(13,false),(5,false),(4,false),(10,true),(2,true),(8,true)],[(1,true),(11,true),(12,true),(6,true),(7,true),(3,true),(9,false)])
                        (.node 1054900 ([(7,true),(4,true),(5,true),(13,true),(1,true),(2,true),(9,false)],[(0,false),(6,false),(12,false),(11,false),(10,false),(3,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1055572 ([(0,true),(13,false),(5,false),(4,false),(3,false),(2,false),(8,true)],[(1,true),(7,false),(6,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1062904 ([(2,false),(13,false),(0,true),(11,false),(4,true),(5,true),(8,true)],[(1,false),(12,true),(6,false),(7,false),(3,true),(10,false),(9,false)])
                      (.node 1062562 ([(4,true),(10,true),(2,false),(1,false),(0,false),(6,false),(8,true)],[(13,false),(12,false),(11,false),(3,true),(7,true),(5,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1062946 ([(2,false),(1,false),(0,false),(6,false),(10,true),(4,true),(8,true)],[(13,false),(12,false),(11,false),(3,false),(7,true),(5,true),(9,false)])
                        .empty
                        .empty)))))
              (.node 1069804 ([(1,true),(2,true),(3,true),(12,true),(6,false),(5,false),(8,true)],[(13,false),(0,true),(7,true),(4,false),(11,false),(10,false),(9,false)])
                (.node 1067854 ([(4,true),(5,true),(6,true),(12,false),(2,false),(1,false),(9,false)],[(13,false),(0,true),(10,true),(11,true),(3,true),(7,true),(8,true)])
                  (.node 1066678 ([(4,true),(10,true),(1,true),(2,true),(12,true),(6,false),(8,true)],[(13,false),(0,true),(11,true),(3,true),(7,true),(5,false),(9,false)])
                    (.node 1063534 ([(2,false),(1,false),(0,false),(6,false),(5,false),(4,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,false),(7,true),(8,true)])
                      (.node 1063522 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                        (.node 1063180 ([(7,true),(2,false),(13,false),(0,true),(11,false),(4,false),(9,false)],[(1,false),(12,true),(6,false),(5,false),(10,false),(3,false),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1066666 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1067746 ([(1,true),(13,false),(12,false),(3,true),(4,true),(5,true),(9,false)],[(2,true),(11,false),(10,false),(6,true),(0,true),(7,true),(8,true)])
                      (.node 1067704 ([(0,false),(13,true),(2,true),(3,true),(4,true),(5,true),(8,true)],[(1,false),(7,true),(6,true),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1067842 ([(6,true),(0,true),(1,true),(2,true),(11,false),(4,false),(8,true)],[(13,false),(12,false),(3,true),(7,false),(5,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1069078 ([(3,true),(12,true),(13,true),(1,false),(10,false),(5,true),(8,true)],[(2,true),(7,true),(6,true),(0,true),(11,true),(4,true),(9,false)])
                    (.node 1068376 ([(1,true),(2,true),(12,true),(6,false),(5,false),(4,false),(8,true)],[(13,false),(0,true),(7,true),(3,false),(11,false),(10,false),(9,false)])
                      (.node 1068334 ([(1,true),(2,true),(12,true),(6,false),(10,false),(4,true),(8,true)],[(13,false),(0,true),(7,true),(5,true),(11,true),(3,true),(9,false)])
                        (.node 1068310 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1069060 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1069120 ([(3,true),(11,false),(1,true),(13,false),(6,false),(5,false),(8,true)],[(2,true),(7,true),(4,false),(12,true),(0,true),(10,false),(9,false)])
                      (.node 1069108 ([(5,true),(6,true),(13,true),(1,false),(11,true),(3,false),(8,true)],[(2,true),(7,false),(4,false),(12,true),(0,true),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1069762 ([(0,false),(13,true),(2,true),(3,true),(4,true),(5,true),(8,true)],[(1,false),(7,true),(6,true),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))))
                (.node 1071958 ([(6,true),(0,true),(1,true),(2,true),(11,true),(4,false),(8,true)],[(13,false),(12,false),(5,true),(7,true),(3,false),(10,false),(9,false)])
                  (.node 1071370 ([(6,true),(13,true),(1,false),(11,true),(4,false),(3,false),(9,false)],[(2,true),(10,true),(0,false),(12,false),(5,true),(7,true),(8,true)])
                    (.node 1070662 ([(5,true),(6,true),(12,false),(3,false),(2,false),(1,false),(8,true)],[(13,false),(0,true),(7,false),(4,false),(11,false),(10,false),(9,false)])
                      (.node 1070590 ([(3,true),(12,true),(13,true),(1,false),(10,true),(5,false),(8,true)],[(2,true),(7,true),(4,false),(11,false),(6,true),(0,true),(9,false)])
                        (.node 1070578 ([(5,true),(6,true),(12,false),(3,false),(2,false),(1,false),(9,false)],[(13,false),(0,true),(10,true),(11,true),(4,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1070686 ([(1,true),(2,true),(3,true),(12,true),(6,false),(5,false),(8,true)],[(13,false),(0,true),(7,true),(4,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1071412 ([(6,true),(12,false),(4,false),(10,true),(1,true),(2,true),(8,true)],[(13,false),(0,true),(11,true),(5,true),(7,true),(3,true),(9,false)])
                      (.node 1071382 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1071430 ([(3,true),(4,true),(11,false),(1,true),(13,false),(6,false),(8,true)],[(2,true),(7,true),(5,false),(12,true),(0,true),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1073122 ([(1,true),(13,false),(6,false),(5,false),(4,false),(3,false),(8,true)],[(2,true),(7,false),(0,false),(12,false),(11,false),(10,false),(9,false)])
                    (.node 1072198 ([(1,true),(2,true),(10,false),(6,true),(12,false),(4,false),(8,true)],[(13,false),(0,true),(7,true),(3,false),(11,true),(5,true),(9,false)])
                      (.node 1072180 ([(4,true),(5,true),(10,true),(2,false),(13,false),(0,true),(8,true)],[(1,false),(7,false),(3,false),(11,true),(12,true),(6,false),(9,false)])
                        (.node 1071970 ([(4,true),(5,true),(6,true),(13,true),(2,true),(10,false),(9,false)],[(1,false),(0,false),(12,false),(11,false),(3,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1073080 ([(1,true),(13,false),(6,false),(5,false),(4,false),(3,false),(9,false)],[(2,true),(10,true),(11,true),(12,true),(0,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1073824 ([(2,false),(1,false),(0,false),(6,false),(5,false),(4,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,false),(7,true),(8,true)])
                      (.node 1073812 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1074508 ([(7,true),(5,true),(6,true),(13,true),(2,true),(3,true),(9,false)],[(1,false),(0,false),(12,false),(11,false),(10,false),(4,true),(8,true)])
                        .empty
                        .empty))))))))
        (.node 1179856 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
          (.node 1150318 ([(1,true),(2,true),(11,false),(6,false),(5,false),(4,false),(9,false)],[(13,false),(12,false),(3,true),(10,true),(0,true),(7,true),(8,true)])
            (.node 1141000 ([(0,true),(1,true),(2,true),(3,true),(12,false),(5,false),(8,true)],[(13,false),(4,true),(7,false),(6,false),(11,false),(10,false),(9,false)])
              (.node 1130482 ([(3,true),(13,true),(1,false),(11,false),(5,true),(6,true),(8,true)],[(2,true),(7,true),(0,true),(12,true),(4,true),(10,false),(9,false)])
                (.node 1127878 ([(3,true),(13,true),(1,false),(0,false),(11,false),(5,true),(8,true)],[(2,true),(7,true),(6,true),(12,true),(4,true),(10,false),(9,false)])
                  (.node 1127356 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                    (.node 1126702 ([(2,false),(1,false),(0,false),(12,true),(4,true),(5,true),(8,true)],[(13,false),(3,false),(7,true),(6,true),(11,false),(10,false),(9,false)])
                      (.node 1075180 ([(1,true),(13,false),(6,false),(5,false),(4,false),(3,false),(8,true)],[(2,true),(7,false),(0,false),(12,false),(11,false),(10,false),(9,false)])
                        (.node 1075138 ([(1,true),(13,false),(6,false),(5,false),(4,false),(3,false),(9,false)],[(2,true),(10,true),(11,true),(12,true),(0,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1126744 ([(3,true),(13,true),(1,false),(0,false),(6,false),(5,false),(8,true)],[(2,true),(7,true),(4,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1127428 ([(1,true),(2,true),(3,true),(12,false),(6,false),(5,false),(8,true)],[(13,false),(4,true),(7,false),(0,false),(11,false),(10,false),(9,false)])
                      (.node 1127404 ([(5,true),(6,true),(12,true),(3,false),(2,false),(1,false),(8,true)],[(13,false),(4,true),(7,true),(0,false),(11,false),(10,false),(9,false)])
                        (.node 1127386 ([(1,true),(2,true),(3,true),(12,false),(6,false),(5,false),(9,false)],[(13,false),(4,true),(10,true),(11,true),(0,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1127860 ([(6,true),(11,false),(4,false),(3,false),(2,false),(1,false),(9,false)],[(13,false),(12,false),(0,true),(10,true),(5,true),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1129798 ([(5,true),(10,true),(2,false),(13,false),(12,false),(0,false),(8,true)],[(1,false),(11,false),(3,true),(4,true),(7,true),(6,false),(9,false)])
                    (.node 1128760 ([(3,true),(13,true),(1,false),(0,false),(10,false),(5,true),(8,true)],[(2,true),(7,true),(6,true),(11,true),(12,true),(4,true),(9,false)])
                      (.node 1127974 ([(1,true),(2,true),(3,true),(4,true),(11,true),(6,false),(8,true)],[(13,false),(12,false),(0,true),(7,true),(5,false),(10,false),(9,false)])
                        (.node 1127944 ([(6,true),(0,true),(1,true),(13,false),(4,true),(10,false),(9,false)],[(2,true),(3,true),(12,false),(11,false),(5,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1128802 ([(3,true),(13,true),(1,false),(0,false),(6,false),(5,false),(8,true)],[(2,true),(7,true),(4,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1130212 ([(6,true),(0,true),(11,false),(4,false),(13,true),(2,true),(8,true)],[(1,false),(12,true),(3,false),(7,false),(5,false),(10,false),(9,false)])
                      (.node 1129828 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1130230 ([(3,true),(13,true),(1,false),(11,false),(10,false),(6,false),(8,true)],[(2,true),(7,true),(5,false),(4,false),(12,false),(0,false),(9,false)])
                        .empty
                        .empty))))
                (.node 1135342 ([(7,true),(1,true),(13,false),(3,false),(11,false),(6,true),(9,false)],[(2,true),(12,true),(4,true),(5,true),(10,false),(0,true),(8,true)])
                  (.node 1133914 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,false),(7,true),(8,true)])
                    (.node 1133560 ([(1,true),(2,true),(3,true),(4,true),(10,true),(6,false),(8,true)],[(13,false),(12,false),(11,false),(0,true),(7,true),(5,false),(9,false)])
                      (.node 1130710 ([(0,true),(1,true),(13,false),(4,true),(5,true),(10,false),(9,false)],[(2,true),(3,true),(12,false),(11,false),(6,true),(7,true),(8,true)])
                        (.node 1130680 ([(5,true),(6,true),(0,true),(1,true),(13,false),(3,false),(9,false)],[(2,true),(10,true),(11,true),(12,true),(4,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1133602 ([(1,true),(13,false),(3,false),(11,false),(6,false),(5,false),(8,true)],[(2,true),(12,true),(4,true),(7,false),(0,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1135000 ([(6,true),(10,true),(4,false),(3,false),(2,false),(1,false),(8,true)],[(13,false),(12,false),(11,false),(5,true),(7,true),(0,false),(9,false)])
                      (.node 1133944 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1135030 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1139146 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                    (.node 1138714 ([(2,false),(13,false),(4,true),(5,true),(10,true),(0,false),(8,true)],[(1,false),(11,true),(12,true),(3,false),(7,true),(6,false),(9,false)])
                      (.node 1138462 ([(7,true),(5,false),(4,false),(13,true),(1,false),(0,false),(9,false)],[(2,true),(3,true),(12,false),(11,false),(10,false),(6,false),(8,true)])
                        (.node 1135384 ([(5,true),(11,true),(3,true),(13,true),(1,false),(0,false),(8,true)],[(2,true),(12,true),(4,true),(7,true),(6,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1139116 ([(6,true),(10,true),(11,true),(4,false),(13,true),(1,false),(8,true)],[(2,true),(3,true),(12,false),(5,true),(7,true),(0,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1140184 ([(2,false),(13,false),(4,true),(5,true),(6,true),(0,true),(9,false)],[(1,false),(10,true),(11,true),(12,true),(3,false),(7,true),(8,true)])
                      (.node 1140142 ([(2,false),(13,false),(4,true),(5,true),(6,true),(0,true),(8,true)],[(1,false),(7,false),(3,true),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1140970 ([(5,true),(6,true),(0,true),(1,true),(13,false),(3,false),(9,false)],[(2,true),(10,true),(11,true),(12,true),(4,true),(7,true),(8,true)])
                        .empty
                        .empty)))))
              (.node 1144564 ([(1,true),(2,true),(3,true),(4,true),(12,false),(6,false),(9,false)],[(13,false),(5,true),(10,true),(11,true),(0,true),(7,true),(8,true)])
                (.node 1143400 ([(6,true),(0,true),(1,true),(13,false),(4,false),(3,false),(9,false)],[(2,true),(10,true),(11,true),(12,true),(5,true),(7,true),(8,true)])
                  (.node 1141558 ([(5,true),(12,true),(3,false),(2,false),(1,false),(0,false),(8,true)],[(13,false),(4,true),(7,true),(6,false),(11,false),(10,false),(9,false)])
                    (.node 1141516 ([(5,true),(6,true),(10,true),(3,true),(13,true),(1,false),(8,true)],[(2,true),(11,true),(12,true),(4,true),(7,true),(0,false),(9,false)])
                      (.node 1141084 ([(0,true),(1,true),(2,true),(3,true),(12,false),(5,false),(9,false)],[(13,false),(4,true),(10,true),(11,true),(6,true),(7,true),(8,true)])
                        (.node 1141066 ([(3,true),(13,true),(1,false),(10,false),(5,true),(6,true),(8,true)],[(2,true),(7,true),(0,true),(11,true),(12,true),(4,true),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1141540 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1142200 ([(2,false),(13,false),(4,true),(5,true),(6,true),(0,true),(8,true)],[(1,false),(7,false),(3,true),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1141588 ([(0,true),(1,true),(2,true),(3,true),(12,false),(5,false),(8,true)],[(13,false),(4,true),(7,false),(6,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1142242 ([(2,false),(13,false),(4,true),(5,true),(6,true),(0,true),(9,false)],[(1,false),(10,true),(11,true),(12,true),(3,false),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1144228 ([(1,true),(2,true),(3,true),(4,true),(12,false),(6,false),(9,false)],[(13,false),(5,true),(10,true),(11,true),(0,true),(7,true),(8,true)])
                    (.node 1144000 ([(4,true),(5,true),(6,true),(11,false),(2,false),(1,false),(9,false)],[(13,false),(12,false),(0,true),(10,true),(3,true),(7,true),(8,true)])
                      (.node 1143988 ([(6,true),(11,false),(3,true),(4,true),(13,true),(1,false),(9,false)],[(2,true),(10,false),(0,false),(12,true),(5,true),(7,true),(8,true)])
                        (.node 1143442 ([(6,true),(0,true),(1,true),(13,false),(4,false),(3,false),(8,true)],[(2,true),(7,false),(5,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1144210 ([(4,true),(5,true),(6,true),(11,false),(2,false),(1,false),(8,true)],[(13,false),(12,false),(0,true),(7,false),(3,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1144342 ([(3,true),(4,true),(13,true),(1,false),(0,false),(6,false),(8,true)],[(2,true),(7,true),(5,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1144324 ([(6,true),(0,true),(1,true),(13,false),(4,false),(3,false),(8,true)],[(2,true),(7,false),(5,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1144552 ([(3,true),(10,false),(6,true),(12,true),(13,true),(1,false),(8,true)],[(2,true),(7,true),(0,false),(11,false),(4,true),(5,true),(9,false)])
                        .empty
                        .empty))))
                (.node 1146676 ([(6,true),(0,true),(1,true),(13,false),(4,false),(3,false),(8,true)],[(2,true),(7,false),(5,false),(12,false),(11,false),(10,false),(9,false)])
                  (.node 1146340 ([(6,true),(0,true),(11,false),(2,false),(13,false),(4,false),(8,true)],[(1,false),(12,true),(5,true),(7,true),(3,false),(10,false),(9,false)])
                    (.node 1145458 ([(6,true),(0,true),(1,true),(13,false),(4,false),(3,false),(9,false)],[(2,true),(10,true),(11,true),(12,true),(5,true),(7,true),(8,true)])
                      (.node 1145152 ([(1,true),(13,false),(12,false),(6,false),(10,false),(3,false),(8,true)],[(2,true),(7,false),(0,false),(11,false),(5,false),(4,false),(9,false)])
                        (.node 1145110 ([(1,true),(2,true),(10,true),(6,true),(12,true),(4,false),(8,true)],[(13,false),(5,true),(11,true),(0,true),(7,true),(3,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1145500 ([(6,true),(0,true),(1,true),(13,false),(4,false),(3,false),(8,true)],[(2,true),(7,false),(5,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1146604 ([(4,true),(5,true),(10,true),(2,false),(1,false),(0,false),(8,true)],[(13,false),(12,false),(11,false),(3,true),(7,true),(6,false),(9,false)])
                      (.node 1146352 ([(4,true),(12,false),(1,true),(2,true),(10,false),(6,false),(8,true)],[(13,false),(5,true),(7,false),(3,false),(11,true),(0,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1146628 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1147510 ([(0,true),(1,true),(2,true),(10,true),(5,false),(4,false),(8,true)],[(13,false),(12,false),(11,false),(6,true),(7,true),(3,false),(9,false)])
                    (.node 1146964 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                      (.node 1146946 ([(3,true),(11,true),(1,true),(13,false),(5,true),(6,true),(8,true)],[(2,true),(7,true),(0,true),(12,true),(4,false),(10,false),(9,false)])
                        (.node 1146694 ([(3,true),(4,true),(13,true),(1,false),(0,false),(6,false),(8,true)],[(2,true),(7,true),(5,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1147486 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1147552 ([(0,true),(1,true),(13,false),(5,true),(10,false),(3,false),(8,true)],[(2,true),(7,false),(6,false),(11,true),(12,true),(4,false),(9,false)])
                      (.node 1147534 ([(3,true),(4,true),(13,true),(1,false),(11,false),(6,true),(8,true)],[(2,true),(7,true),(0,true),(12,true),(5,true),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1150288 ([(6,true),(0,true),(1,true),(13,false),(12,false),(3,true),(9,false)],[(2,true),(11,false),(10,false),(4,true),(5,true),(7,true),(8,true)])
                        .empty
                        .empty))))))
            (.node 1163974 ([(0,true),(1,true),(13,false),(5,false),(4,false),(3,false),(9,false)],[(2,true),(10,true),(11,true),(12,true),(6,true),(7,true),(8,true)])
              (.node 1158322 ([(4,true),(5,true),(6,true),(10,true),(2,false),(1,false),(8,true)],[(13,false),(12,false),(11,false),(3,true),(7,true),(0,false),(9,false)])
                (.node 1153120 ([(3,true),(4,true),(13,true),(1,false),(10,false),(6,true),(8,true)],[(2,true),(7,true),(0,true),(11,true),(12,true),(5,true),(9,false)])
                  (.node 1151494 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                    (.node 1150744 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                      (.node 1150720 ([(4,true),(12,false),(2,false),(1,false),(0,false),(6,false),(9,false)],[(13,false),(5,true),(10,true),(11,true),(3,true),(7,true),(8,true)])
                        (.node 1150468 ([(4,true),(12,false),(2,false),(1,false),(0,false),(6,false),(8,true)],[(13,false),(5,true),(7,false),(3,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1151464 ([(6,true),(10,true),(3,false),(12,true),(13,true),(1,false),(8,true)],[(2,true),(11,false),(4,true),(5,true),(7,true),(0,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1152214 ([(0,true),(1,true),(2,true),(11,false),(5,false),(4,false),(8,true)],[(13,false),(12,false),(3,true),(7,false),(6,false),(10,false),(9,false)])
                      (.node 1152190 ([(4,true),(5,true),(11,true),(2,false),(1,false),(0,false),(8,true)],[(13,false),(12,false),(3,true),(7,true),(6,false),(10,false),(9,false)])
                        (.node 1152148 ([(4,true),(13,true),(2,true),(11,false),(6,true),(0,true),(8,true)],[(1,false),(7,false),(3,false),(12,true),(5,true),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1152868 ([(3,true),(4,true),(13,true),(1,false),(0,false),(6,false),(8,true)],[(2,true),(7,true),(5,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1157458 ([(1,true),(2,true),(10,true),(6,false),(5,false),(4,false),(8,true)],[(13,false),(12,false),(11,false),(0,true),(7,true),(3,false),(9,false)])
                    (.node 1154548 ([(2,false),(13,false),(4,false),(11,false),(6,true),(0,true),(8,true)],[(1,false),(7,false),(3,true),(12,true),(5,true),(10,false),(9,false)])
                      (.node 1153552 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                        (.node 1153522 ([(6,true),(10,true),(3,true),(4,true),(13,true),(1,false),(8,true)],[(2,true),(11,true),(12,true),(5,true),(7,true),(0,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1154590 ([(2,false),(13,false),(4,false),(11,false),(6,true),(0,true),(9,false)],[(1,false),(10,true),(5,false),(12,false),(3,false),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1157800 ([(7,true),(4,true),(5,true),(11,false),(1,true),(2,true),(9,false)],[(13,false),(12,false),(6,true),(0,true),(10,false),(3,true),(8,true)])
                      (.node 1157500 ([(1,true),(13,false),(5,true),(6,true),(10,false),(3,false),(8,true)],[(2,true),(7,false),(0,false),(11,true),(12,true),(4,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1157842 ([(0,true),(11,true),(5,false),(13,true),(2,true),(3,true),(9,false)],[(1,false),(10,false),(4,true),(12,false),(6,true),(7,true),(8,true)])
                        .empty
                        .empty))))
                (.node 1161616 ([(1,true),(13,false),(6,true),(11,false),(4,false),(3,false),(8,true)],[(2,true),(7,false),(0,false),(12,true),(5,false),(10,false),(9,false)])
                  (.node 1160260 ([(2,false),(1,false),(0,false),(6,false),(5,false),(4,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,false),(7,true),(8,true)])
                    (.node 1158706 ([(3,true),(11,true),(5,false),(13,true),(1,false),(0,false),(8,true)],[(2,true),(7,true),(6,false),(12,true),(4,false),(10,false),(9,false)])
                      (.node 1158664 ([(2,false),(13,false),(5,true),(11,false),(10,false),(0,true),(8,true)],[(1,false),(7,false),(3,true),(4,true),(12,false),(6,true),(9,false)])
                        (.node 1158364 ([(4,true),(5,true),(11,false),(2,false),(1,false),(0,false),(8,true)],[(13,false),(12,false),(6,true),(7,false),(3,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1160248 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1160986 ([(1,true),(2,true),(11,true),(6,false),(5,false),(4,false),(8,true)],[(13,false),(12,false),(0,true),(7,true),(3,false),(10,false),(9,false)])
                      (.node 1160944 ([(0,false),(6,false),(13,true),(2,true),(3,true),(4,true),(8,true)],[(1,false),(7,true),(5,true),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1161574 ([(1,true),(13,false),(6,true),(11,false),(4,false),(3,false),(9,false)],[(2,true),(10,true),(5,true),(12,false),(0,true),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1163386 ([(0,true),(1,true),(13,false),(5,false),(10,true),(3,true),(8,true)],[(2,true),(11,true),(12,true),(6,true),(7,true),(4,true),(9,false)])
                    (.node 1163344 ([(6,false),(12,false),(1,true),(2,true),(3,true),(4,true),(8,true)],[(13,false),(5,false),(7,false),(0,true),(11,false),(10,false),(9,false)])
                      (.node 1162318 ([(2,false),(1,false),(0,false),(6,false),(5,false),(4,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,false),(7,true),(8,true)])
                        (.node 1162306 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1163362 ([(4,true),(5,true),(13,true),(2,true),(11,true),(0,false),(8,true)],[(1,false),(12,true),(6,true),(7,false),(3,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1163494 ([(3,true),(10,false),(0,true),(1,true),(13,false),(5,false),(8,true)],[(2,true),(7,true),(4,false),(11,true),(12,true),(6,true),(9,false)])
                      (.node 1163482 ([(5,true),(12,false),(1,true),(2,true),(3,true),(10,false),(9,false)],[(13,false),(6,true),(0,true),(11,false),(4,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1163950 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                        .empty
                        .empty)))))
              (.node 1169542 ([(3,true),(4,true),(10,true),(6,false),(13,true),(1,false),(8,true)],[(2,true),(7,true),(0,false),(11,true),(12,true),(5,false),(9,false)])
                (.node 1167502 ([(0,true),(1,true),(2,true),(12,true),(5,false),(4,false),(8,true)],[(13,false),(6,true),(7,true),(3,false),(11,false),(10,false),(9,false)])
                  (.node 1167160 ([(1,true),(2,true),(11,false),(6,false),(5,false),(4,false),(8,true)],[(13,false),(12,false),(3,true),(7,false),(0,false),(10,false),(9,false)])
                    (.node 1167118 ([(1,true),(2,true),(3,true),(10,true),(6,false),(5,false),(8,true)],[(13,false),(12,false),(11,false),(0,true),(7,true),(4,false),(9,false)])
                      (.node 1167094 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                        (.node 1164016 ([(0,true),(1,true),(13,false),(5,false),(4,false),(3,false),(8,true)],[(2,true),(7,false),(6,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1167142 ([(4,true),(5,true),(6,true),(11,true),(2,false),(1,false),(8,true)],[(13,false),(12,false),(3,true),(7,true),(0,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1167460 ([(0,true),(10,false),(3,false),(2,false),(13,false),(5,false),(8,true)],[(1,false),(11,true),(12,true),(6,true),(7,true),(4,false),(9,false)])
                      (.node 1167430 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1167478 ([(4,true),(5,true),(12,false),(2,false),(1,false),(0,false),(8,true)],[(13,false),(6,true),(7,false),(3,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1168654 ([(4,true),(5,true),(12,false),(2,false),(1,false),(0,false),(8,true)],[(13,false),(6,true),(7,false),(3,false),(11,false),(10,false),(9,false)])
                    (.node 1168612 ([(4,true),(5,true),(12,false),(2,false),(1,false),(0,false),(9,false)],[(13,false),(6,true),(10,true),(11,true),(3,true),(7,true),(8,true)])
                      (.node 1168312 ([(4,false),(3,false),(2,false),(13,false),(6,true),(0,true),(9,false)],[(1,false),(10,true),(11,true),(12,true),(5,false),(7,true),(8,true)])
                        (.node 1168270 ([(5,true),(6,true),(10,true),(3,false),(2,false),(1,false),(8,true)],[(13,false),(12,false),(11,false),(4,true),(7,true),(0,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1168630 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1169446 ([(5,true),(6,true),(11,true),(3,false),(2,false),(1,false),(8,true)],[(13,false),(12,false),(4,true),(7,true),(0,false),(10,false),(9,false)])
                      (.node 1168678 ([(0,true),(1,true),(2,true),(12,true),(5,false),(4,false),(8,true)],[(13,false),(6,true),(7,true),(3,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1169470 ([(1,true),(2,true),(3,true),(11,false),(6,false),(5,false),(8,true)],[(13,false),(12,false),(4,true),(7,false),(0,false),(10,false),(9,false)])
                        .empty
                        .empty))))
                (.node 1171054 ([(3,true),(4,true),(5,true),(13,true),(1,false),(0,false),(8,true)],[(2,true),(7,true),(6,false),(12,false),(11,false),(10,false),(9,false)])
                  (.node 1169896 ([(0,true),(1,true),(13,false),(5,false),(4,false),(3,false),(8,true)],[(2,true),(7,false),(6,false),(12,false),(11,false),(10,false),(9,false)])
                    (.node 1169812 ([(0,true),(1,true),(2,true),(3,true),(12,true),(5,false),(8,true)],[(13,false),(6,true),(7,true),(4,false),(11,false),(10,false),(9,false)])
                      (.node 1169782 ([(5,true),(12,false),(3,false),(2,false),(1,false),(0,false),(8,true)],[(13,false),(6,true),(7,false),(4,false),(11,false),(10,false),(9,false)])
                        (.node 1169554 ([(1,true),(2,true),(3,true),(11,false),(6,false),(5,false),(9,false)],[(13,false),(12,false),(4,true),(10,true),(0,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1169878 ([(3,true),(4,true),(5,true),(13,true),(1,false),(0,false),(8,true)],[(2,true),(7,true),(6,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1170370 ([(5,true),(12,false),(3,false),(2,false),(1,false),(0,false),(8,true)],[(13,false),(6,true),(7,false),(4,false),(11,false),(10,false),(9,false)])
                      (.node 1170328 ([(5,true),(12,false),(3,false),(2,false),(1,false),(0,false),(9,false)],[(13,false),(6,true),(10,true),(11,true),(4,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1171012 ([(2,false),(13,false),(12,false),(4,true),(10,false),(0,true),(8,true)],[(1,false),(7,false),(3,true),(11,false),(5,true),(6,true),(9,false)])
                        .empty
                        .empty)))
                  (.node 1172728 ([(4,true),(5,true),(6,true),(10,true),(2,false),(1,false),(8,true)],[(13,false),(12,false),(11,false),(3,true),(7,true),(0,false),(9,false)])
                    (.node 1172206 ([(0,true),(1,true),(13,false),(5,false),(4,false),(3,false),(9,false)],[(2,true),(10,true),(11,true),(12,true),(6,true),(7,true),(8,true)])
                      (.node 1171906 ([(1,true),(13,false),(5,false),(11,false),(10,false),(3,false),(8,true)],[(2,true),(7,false),(0,false),(6,false),(12,false),(4,false),(9,false)])
                        (.node 1171864 ([(1,true),(2,true),(10,true),(6,false),(5,false),(4,false),(8,true)],[(13,false),(12,false),(11,false),(0,true),(7,true),(3,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1172248 ([(0,true),(1,true),(13,false),(5,false),(4,false),(3,false),(8,true)],[(2,true),(7,false),(6,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1173070 ([(2,false),(13,false),(5,false),(4,false),(10,false),(0,true),(8,true)],[(1,false),(7,false),(3,true),(11,true),(12,true),(6,true),(9,false)])
                      (.node 1172770 ([(7,true),(6,false),(5,false),(11,false),(2,false),(1,false),(9,false)],[(13,false),(12,false),(4,false),(3,false),(10,false),(0,false),(8,true)])
                        .empty
                        .empty)
                      (.node 1173112 ([(3,true),(4,true),(5,true),(13,true),(1,false),(0,false),(8,true)],[(2,true),(7,true),(6,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))))))
          (.node 1205434 ([(6,true),(0,true),(12,false),(4,false),(3,false),(2,false),(9,false)],[(13,false),(1,true),(10,true),(11,true),(5,true),(7,true),(8,true)])
            (.node 1189504 ([(1,true),(2,true),(13,false),(6,false),(5,false),(4,false),(8,true)],[(3,true),(7,false),(0,false),(12,false),(11,false),(10,false),(9,false)])
              (.node 1186768 ([(2,true),(3,true),(11,false),(0,false),(6,false),(5,false),(8,true)],[(13,false),(12,false),(4,true),(7,false),(1,false),(10,false),(9,false)])
                (.node 1182994 ([(1,true),(2,true),(13,false),(6,false),(10,true),(4,true),(8,true)],[(3,true),(11,true),(12,true),(0,true),(7,true),(5,true),(9,false)])
                  (.node 1181224 ([(2,true),(13,false),(0,true),(11,false),(5,false),(4,false),(8,true)],[(3,true),(7,false),(1,false),(12,true),(6,false),(10,false),(9,false)])
                    (.node 1180594 ([(2,true),(3,true),(11,true),(0,false),(6,false),(5,false),(8,true)],[(13,false),(12,false),(1,true),(7,true),(4,false),(10,false),(9,false)])
                      (.node 1180552 ([(1,false),(0,false),(13,true),(3,true),(4,true),(5,true),(8,true)],[(2,false),(7,true),(6,true),(12,false),(11,false),(10,false),(9,false)])
                        (.node 1179868 ([(3,false),(2,false),(1,false),(0,false),(6,false),(5,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,false),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1181182 ([(2,true),(13,false),(0,true),(11,false),(5,false),(4,false),(9,false)],[(3,true),(10,true),(6,true),(12,false),(1,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1182952 ([(0,false),(12,false),(2,true),(3,true),(4,true),(5,true),(8,true)],[(13,false),(6,false),(7,false),(1,true),(11,false),(10,false),(9,false)])
                      (.node 1181926 ([(3,false),(2,false),(1,false),(0,false),(6,false),(5,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,false),(7,true),(8,true)])
                        (.node 1181914 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1182970 ([(5,true),(6,true),(13,true),(3,true),(11,true),(1,false),(8,true)],[(2,false),(12,true),(0,true),(7,false),(4,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1183624 ([(1,true),(2,true),(13,false),(6,false),(5,false),(4,false),(8,true)],[(3,true),(7,false),(0,false),(12,false),(11,false),(10,false),(9,false)])
                    (.node 1183558 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                      (.node 1183102 ([(4,true),(10,false),(1,true),(2,true),(13,false),(6,false),(8,true)],[(3,true),(7,true),(5,false),(11,true),(12,true),(0,true),(9,false)])
                        (.node 1183090 ([(6,true),(12,false),(2,true),(3,true),(4,true),(10,false),(9,false)],[(13,false),(0,true),(1,true),(11,false),(5,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1183582 ([(1,true),(2,true),(13,false),(6,false),(5,false),(4,false),(9,false)],[(3,true),(10,true),(11,true),(12,true),(0,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1186726 ([(2,true),(3,true),(4,true),(10,true),(0,false),(6,false),(8,true)],[(13,false),(12,false),(11,false),(1,true),(7,true),(5,false),(9,false)])
                      (.node 1186702 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1186750 ([(5,true),(6,true),(0,true),(11,true),(3,false),(2,false),(8,true)],[(13,false),(12,false),(4,true),(7,true),(1,false),(10,false),(9,false)])
                        .empty
                        .empty))))
                (.node 1188262 ([(5,true),(6,true),(12,false),(3,false),(2,false),(1,false),(8,true)],[(13,false),(0,true),(7,false),(4,false),(11,false),(10,false),(9,false)])
                  (.node 1187878 ([(6,true),(0,true),(10,true),(4,false),(3,false),(2,false),(8,true)],[(13,false),(12,false),(11,false),(5,true),(7,true),(1,false),(9,false)])
                    (.node 1187086 ([(5,true),(6,true),(12,false),(3,false),(2,false),(1,false),(8,true)],[(13,false),(0,true),(7,false),(4,false),(11,false),(10,false),(9,false)])
                      (.node 1187068 ([(1,true),(10,false),(4,false),(3,false),(13,false),(6,false),(8,true)],[(2,false),(11,true),(12,true),(0,true),(7,true),(5,false),(9,false)])
                        (.node 1187038 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1187110 ([(1,true),(2,true),(3,true),(12,true),(6,false),(5,false),(8,true)],[(13,false),(0,true),(7,true),(4,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1188220 ([(5,true),(6,true),(12,false),(3,false),(2,false),(1,false),(9,false)],[(13,false),(0,true),(10,true),(11,true),(4,true),(7,true),(8,true)])
                      (.node 1187920 ([(5,false),(4,false),(3,false),(13,false),(0,true),(1,true),(9,false)],[(2,false),(10,true),(11,true),(12,true),(6,false),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1188238 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1189162 ([(2,true),(3,true),(4,true),(11,false),(0,false),(6,false),(9,false)],[(13,false),(12,false),(5,true),(10,true),(1,true),(7,true),(8,true)])
                    (.node 1189078 ([(2,true),(3,true),(4,true),(11,false),(0,false),(6,false),(8,true)],[(13,false),(12,false),(5,true),(7,false),(1,false),(10,false),(9,false)])
                      (.node 1189054 ([(6,true),(0,true),(11,true),(4,false),(3,false),(2,false),(8,true)],[(13,false),(12,false),(5,true),(7,true),(1,false),(10,false),(9,false)])
                        (.node 1188286 ([(1,true),(2,true),(3,true),(12,true),(6,false),(5,false),(8,true)],[(13,false),(0,true),(7,true),(4,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1189150 ([(4,true),(5,true),(10,true),(0,false),(13,true),(2,false),(8,true)],[(3,true),(7,true),(1,false),(11,true),(12,true),(6,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1189420 ([(1,true),(2,true),(3,true),(4,true),(12,true),(6,false),(8,true)],[(13,false),(0,true),(7,true),(5,false),(11,false),(10,false),(9,false)])
                      (.node 1189390 ([(6,true),(12,false),(4,false),(3,false),(2,false),(1,false),(8,true)],[(13,false),(0,true),(7,false),(5,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1189486 ([(4,true),(5,true),(6,true),(13,true),(2,false),(1,false),(8,true)],[(3,true),(7,true),(0,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))))
              (.node 1195630 ([(2,true),(13,false),(0,false),(6,false),(5,false),(4,false),(8,true)],[(3,true),(7,false),(1,false),(12,false),(11,false),(10,false),(9,false)])
                (.node 1192336 ([(5,true),(6,true),(0,true),(10,true),(3,false),(2,false),(8,true)],[(13,false),(12,false),(11,false),(4,true),(7,true),(1,false),(9,false)])
                  (.node 1191472 ([(2,true),(3,true),(10,true),(0,false),(6,false),(5,false),(8,true)],[(13,false),(12,false),(11,false),(1,true),(7,true),(4,false),(9,false)])
                    (.node 1190620 ([(3,false),(13,false),(12,false),(5,true),(10,false),(1,true),(8,true)],[(2,false),(7,false),(4,true),(11,false),(6,true),(0,true),(9,false)])
                      (.node 1189978 ([(6,true),(12,false),(4,false),(3,false),(2,false),(1,false),(8,true)],[(13,false),(0,true),(7,false),(5,false),(11,false),(10,false),(9,false)])
                        (.node 1189936 ([(6,true),(12,false),(4,false),(3,false),(2,false),(1,false),(9,false)],[(13,false),(0,true),(10,true),(11,true),(5,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1190662 ([(4,true),(5,true),(6,true),(13,true),(2,false),(1,false),(8,true)],[(3,true),(7,true),(0,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1191814 ([(1,true),(2,true),(13,false),(6,false),(5,false),(4,false),(9,false)],[(3,true),(10,true),(11,true),(12,true),(0,true),(7,true),(8,true)])
                      (.node 1191514 ([(2,true),(13,false),(6,false),(11,false),(10,false),(4,false),(8,true)],[(3,true),(7,false),(1,false),(0,false),(12,false),(5,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1191856 ([(1,true),(2,true),(13,false),(6,false),(5,false),(4,false),(8,true)],[(3,true),(7,false),(0,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1194274 ([(3,false),(2,false),(1,false),(0,false),(6,false),(5,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,false),(7,true),(8,true)])
                    (.node 1192720 ([(4,true),(5,true),(6,true),(13,true),(2,false),(1,false),(8,true)],[(3,true),(7,true),(0,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1192678 ([(3,false),(13,false),(6,false),(5,false),(10,false),(1,true),(8,true)],[(2,false),(7,false),(4,true),(11,true),(12,true),(0,true),(9,false)])
                        (.node 1192378 ([(7,true),(0,false),(6,false),(11,false),(3,false),(2,false),(9,false)],[(13,false),(12,false),(5,false),(4,false),(10,false),(1,false),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1194262 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1195000 ([(2,true),(13,false),(0,false),(6,false),(10,true),(4,true),(8,true)],[(3,true),(11,true),(12,true),(1,true),(7,true),(5,true),(9,false)])
                      (.node 1194958 ([(7,true),(6,true),(0,true),(13,true),(3,true),(4,true),(9,false)],[(2,false),(1,false),(12,false),(11,false),(10,false),(5,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1195588 ([(2,true),(13,false),(0,false),(6,false),(5,false),(4,false),(9,false)],[(3,true),(10,true),(11,true),(12,true),(1,true),(7,true),(8,true)])
                        .empty
                        .empty))))
                (.node 1203166 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                  (.node 1199860 ([(3,false),(2,false),(1,false),(0,false),(10,true),(5,true),(8,true)],[(13,false),(12,false),(11,false),(4,false),(7,true),(6,true),(9,false)])
                    (.node 1199770 ([(5,true),(10,true),(3,false),(2,false),(1,false),(0,false),(8,true)],[(13,false),(12,false),(11,false),(4,true),(7,true),(6,false),(9,false)])
                      (.node 1198390 ([(3,false),(2,false),(1,false),(0,false),(6,false),(5,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,false),(7,true),(8,true)])
                        (.node 1198378 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1199800 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1200388 ([(0,true),(1,true),(2,true),(3,true),(10,true),(5,false),(8,true)],[(13,false),(12,false),(11,false),(6,true),(7,true),(4,false),(9,false)])
                      (.node 1200112 ([(3,false),(13,false),(1,true),(11,false),(5,true),(6,true),(8,true)],[(2,false),(12,true),(0,false),(7,false),(4,true),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1200430 ([(7,true),(3,false),(13,false),(1,true),(11,false),(5,false),(9,false)],[(2,false),(12,true),(0,false),(6,false),(10,false),(4,false),(8,true)])
                        .empty
                        .empty)))
                  (.node 1204660 ([(2,true),(13,false),(12,false),(4,true),(5,true),(6,true),(9,false)],[(3,true),(11,false),(10,false),(0,true),(1,true),(7,true),(8,true)])
                    (.node 1203886 ([(5,true),(10,true),(2,true),(3,true),(12,true),(0,false),(8,true)],[(13,false),(1,true),(11,true),(4,true),(7,true),(6,false),(9,false)])
                      (.node 1203232 ([(2,true),(3,true),(12,true),(0,false),(6,false),(5,false),(8,true)],[(13,false),(1,true),(7,true),(4,false),(11,false),(10,false),(9,false)])
                        (.node 1203190 ([(2,true),(3,true),(12,true),(0,false),(10,false),(5,true),(8,true)],[(13,false),(1,true),(7,true),(6,true),(11,true),(4,true),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1203916 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1205062 ([(5,true),(6,true),(0,true),(12,false),(3,false),(2,false),(9,false)],[(13,false),(1,true),(10,true),(11,true),(4,true),(7,true),(8,true)])
                      (.node 1204912 ([(1,false),(13,true),(3,true),(4,true),(5,true),(6,true),(8,true)],[(2,false),(7,true),(0,true),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1205092 ([(0,true),(1,true),(2,true),(3,true),(11,false),(5,false),(8,true)],[(13,false),(12,false),(4,true),(7,false),(6,false),(10,false),(9,false)])
                        .empty
                        .empty))))))
            (.node 1265086 ([(4,true),(13,true),(2,false),(1,false),(11,false),(6,true),(8,true)],[(3,true),(7,true),(0,true),(12,true),(5,true),(10,false),(9,false)])
              (.node 1209178 ([(5,true),(6,true),(0,true),(13,true),(3,true),(10,false),(9,false)],[(2,false),(1,false),(12,false),(11,false),(4,true),(7,true),(8,true)])
                (.node 1206970 ([(1,false),(13,true),(3,true),(4,true),(5,true),(6,true),(8,true)],[(2,false),(7,true),(0,true),(12,false),(11,false),(10,false),(9,false)])
                  (.node 1206034 ([(4,true),(11,false),(2,true),(13,false),(0,false),(6,false),(8,true)],[(3,true),(7,true),(5,false),(12,true),(1,true),(10,false),(9,false)])
                    (.node 1205542 ([(2,true),(3,true),(4,true),(12,true),(0,false),(6,false),(8,true)],[(13,false),(1,true),(7,true),(5,false),(11,false),(10,false),(9,false)])
                      (.node 1205518 ([(6,true),(0,true),(12,false),(4,false),(3,false),(2,false),(8,true)],[(13,false),(1,true),(7,false),(5,false),(11,false),(10,false),(9,false)])
                        (.node 1205446 ([(4,true),(12,true),(13,true),(2,false),(10,true),(6,false),(8,true)],[(3,true),(7,true),(5,false),(11,false),(0,true),(1,true),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1206022 ([(6,true),(0,true),(13,true),(2,false),(11,true),(4,false),(8,true)],[(3,true),(7,false),(5,false),(12,true),(1,true),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1206310 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                      (.node 1206286 ([(4,true),(12,true),(13,true),(2,false),(10,false),(6,true),(8,true)],[(3,true),(7,true),(0,true),(1,true),(11,true),(5,true),(9,false)])
                        .empty
                        .empty)
                      (.node 1206718 ([(2,true),(3,true),(4,true),(12,true),(0,false),(6,false),(8,true)],[(13,false),(1,true),(7,true),(5,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1208638 ([(4,true),(5,true),(11,false),(2,true),(13,false),(0,false),(8,true)],[(3,true),(7,true),(6,false),(12,true),(1,true),(10,false),(9,false)])
                    (.node 1208590 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                      (.node 1207978 ([(2,true),(13,false),(0,false),(6,false),(5,false),(4,false),(8,true)],[(3,true),(7,false),(1,false),(12,false),(11,false),(10,false),(9,false)])
                        (.node 1207936 ([(2,true),(13,false),(0,false),(6,false),(5,false),(4,false),(9,false)],[(3,true),(10,true),(11,true),(12,true),(1,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1208620 ([(0,true),(13,true),(2,false),(11,true),(5,false),(4,false),(9,false)],[(3,true),(10,true),(1,false),(12,false),(6,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1209094 ([(5,true),(6,true),(10,true),(3,false),(13,false),(1,true),(8,true)],[(2,false),(7,false),(4,false),(11,true),(12,true),(0,false),(9,false)])
                      (.node 1208662 ([(0,true),(12,false),(5,false),(10,true),(2,true),(3,true),(8,true)],[(13,false),(1,true),(11,true),(6,true),(7,true),(4,true),(9,false)])
                        .empty
                        .empty)
                      (.node 1209112 ([(2,true),(3,true),(10,false),(0,true),(12,false),(5,false),(8,true)],[(13,false),(1,true),(7,true),(4,false),(11,true),(6,true),(9,false)])
                        .empty
                        .empty))))
                (.node 1262038 ([(1,true),(2,true),(3,true),(4,true),(12,false),(6,false),(8,true)],[(13,false),(5,true),(7,false),(0,false),(11,false),(10,false),(9,false)])
                  (.node 1261534 ([(1,true),(2,true),(3,true),(4,true),(12,false),(6,false),(9,false)],[(13,false),(5,true),(10,true),(11,true),(0,true),(7,true),(8,true)])
                    (.node 1261450 ([(1,true),(2,true),(3,true),(4,true),(12,false),(6,false),(8,true)],[(13,false),(5,true),(7,false),(0,false),(11,false),(10,false),(9,false)])
                      (.node 1261420 ([(6,true),(0,true),(1,true),(2,true),(13,false),(4,false),(9,false)],[(3,true),(10,true),(11,true),(12,true),(5,true),(7,true),(8,true)])
                        (.node 1209208 ([(0,true),(1,true),(2,true),(3,true),(11,true),(5,false),(8,true)],[(13,false),(12,false),(6,true),(7,true),(4,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1261516 ([(4,true),(13,true),(2,false),(10,false),(6,true),(0,true),(8,true)],[(3,true),(7,true),(1,true),(11,true),(12,true),(5,true),(9,false)])
                        .empty
                        .empty))
                    (.node 1261990 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                      (.node 1261966 ([(6,true),(0,true),(10,true),(4,true),(13,true),(2,false),(8,true)],[(3,true),(11,true),(12,true),(5,true),(7,true),(1,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1262008 ([(6,true),(12,true),(4,false),(3,false),(2,false),(1,false),(8,true)],[(13,false),(5,true),(7,true),(0,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1264318 ([(6,true),(0,true),(12,true),(4,false),(3,false),(2,false),(8,true)],[(13,false),(5,true),(7,true),(1,false),(11,false),(10,false),(9,false)])
                    (.node 1263658 ([(4,true),(13,true),(2,false),(1,false),(0,false),(6,false),(8,true)],[(3,true),(7,true),(5,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1262692 ([(3,false),(13,false),(5,true),(6,true),(0,true),(1,true),(9,false)],[(2,false),(10,true),(11,true),(12,true),(4,false),(7,true),(8,true)])
                        (.node 1262650 ([(3,false),(13,false),(5,true),(6,true),(0,true),(1,true),(8,true)],[(2,false),(7,false),(4,true),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1263910 ([(3,false),(2,false),(1,false),(12,true),(5,true),(6,true),(8,true)],[(13,false),(4,false),(7,true),(0,true),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1264594 ([(2,true),(3,true),(4,true),(12,false),(0,false),(6,false),(9,false)],[(13,false),(5,true),(10,true),(11,true),(1,true),(7,true),(8,true)])
                      (.node 1264342 ([(2,true),(3,true),(4,true),(12,false),(0,false),(6,false),(8,true)],[(13,false),(5,true),(7,false),(1,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1264606 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                        .empty
                        .empty)))))
              (.node 1270858 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                (.node 1266742 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                  (.node 1265566 ([(1,true),(2,true),(13,false),(5,true),(6,true),(10,false),(9,false)],[(3,true),(4,true),(12,false),(11,false),(0,true),(7,true),(8,true)])
                    (.node 1265194 ([(0,true),(1,true),(2,true),(13,false),(5,true),(10,false),(9,false)],[(3,true),(4,true),(12,false),(11,false),(6,true),(7,true),(8,true)])
                      (.node 1265182 ([(2,true),(3,true),(4,true),(5,true),(11,true),(0,false),(8,true)],[(13,false),(12,false),(1,true),(7,true),(6,false),(10,false),(9,false)])
                        (.node 1265110 ([(0,true),(11,false),(5,false),(4,false),(3,false),(2,false),(9,false)],[(13,false),(12,false),(1,true),(10,true),(6,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1265536 ([(6,true),(0,true),(1,true),(2,true),(13,false),(4,false),(9,false)],[(3,true),(10,true),(11,true),(12,true),(5,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1265968 ([(4,true),(13,true),(2,false),(1,false),(10,false),(6,true),(8,true)],[(3,true),(7,true),(0,true),(11,true),(12,true),(5,true),(9,false)])
                      (.node 1265716 ([(4,true),(13,true),(2,false),(1,false),(0,false),(6,false),(8,true)],[(3,true),(7,true),(5,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1266712 ([(6,true),(10,true),(3,false),(13,false),(12,false),(1,false),(8,true)],[(2,false),(11,false),(4,true),(5,true),(7,true),(0,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1270240 ([(6,true),(11,true),(4,true),(13,true),(2,false),(1,false),(8,true)],[(3,true),(12,true),(5,true),(7,true),(0,false),(10,false),(9,false)])
                    (.node 1267462 ([(0,true),(1,true),(11,false),(5,false),(13,true),(3,true),(8,true)],[(2,false),(12,true),(4,false),(7,false),(6,false),(10,false),(9,false)])
                      (.node 1267438 ([(4,true),(13,true),(2,false),(11,false),(10,false),(0,false),(8,true)],[(3,true),(7,true),(6,false),(5,false),(12,false),(1,false),(9,false)])
                        (.node 1267396 ([(4,true),(13,true),(2,false),(11,false),(6,true),(0,true),(8,true)],[(3,true),(7,true),(1,true),(12,true),(5,true),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1270198 ([(7,true),(2,true),(13,false),(4,false),(11,false),(0,true),(9,false)],[(3,true),(12,true),(5,true),(6,true),(10,false),(1,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1270768 ([(2,true),(3,true),(4,true),(5,true),(10,true),(0,false),(8,true)],[(13,false),(12,false),(11,false),(1,true),(7,true),(6,false),(9,false)])
                      (.node 1270516 ([(2,true),(13,false),(4,false),(11,false),(0,false),(6,false),(8,true)],[(3,true),(12,true),(5,true),(7,false),(1,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1270828 ([(5,false),(4,false),(3,false),(2,false),(1,false),(0,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,false),(7,true),(8,true)])
                        .empty
                        .empty))))
                (.node 1277908 ([(2,true),(3,true),(10,true),(0,false),(6,false),(5,false),(8,true)],[(13,false),(12,false),(11,false),(1,true),(7,true),(4,false),(9,false)])
                  (.node 1275628 ([(3,false),(13,false),(5,true),(6,true),(10,true),(1,false),(8,true)],[(2,false),(11,true),(12,true),(4,false),(7,true),(0,false),(9,false)])
                    (.node 1274998 ([(3,false),(13,false),(5,true),(6,true),(0,true),(1,true),(8,true)],[(2,false),(7,false),(4,true),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1272250 ([(0,true),(10,true),(5,false),(4,false),(3,false),(2,false),(8,true)],[(13,false),(12,false),(11,false),(6,true),(7,true),(1,false),(9,false)])
                        (.node 1272238 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1275040 ([(3,false),(13,false),(5,true),(6,true),(0,true),(1,true),(9,false)],[(2,false),(10,true),(11,true),(12,true),(4,false),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1276354 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                      (.node 1275670 ([(7,true),(6,false),(5,false),(13,true),(2,false),(1,false),(9,false)],[(3,true),(4,true),(12,false),(11,false),(10,false),(0,false),(8,true)])
                        .empty
                        .empty)
                      (.node 1276366 ([(0,true),(10,true),(11,true),(5,false),(13,true),(2,false),(8,true)],[(3,true),(4,true),(12,false),(6,true),(7,true),(1,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1278814 ([(5,true),(6,true),(11,false),(3,false),(2,false),(1,false),(8,true)],[(13,false),(12,false),(0,true),(7,false),(4,false),(10,false),(9,false)])
                    (.node 1278292 ([(1,true),(11,true),(6,false),(13,true),(3,true),(4,true),(9,false)],[(2,false),(10,false),(5,true),(12,false),(0,true),(7,true),(8,true)])
                      (.node 1278250 ([(7,true),(5,true),(6,true),(11,false),(2,true),(3,true),(9,false)],[(13,false),(12,false),(0,true),(1,true),(10,false),(4,true),(8,true)])
                        (.node 1277950 ([(2,true),(13,false),(6,true),(0,true),(10,false),(4,false),(8,true)],[(3,true),(7,false),(1,false),(11,true),(12,true),(5,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1278772 ([(5,true),(6,true),(0,true),(10,true),(3,false),(2,false),(8,true)],[(13,false),(12,false),(11,false),(4,true),(7,true),(1,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1279156 ([(4,true),(11,true),(6,false),(13,true),(2,false),(1,false),(8,true)],[(3,true),(7,true),(0,false),(12,true),(5,false),(10,false),(9,false)])
                      (.node 1279114 ([(3,false),(13,false),(6,true),(11,false),(10,false),(1,true),(8,true)],[(2,false),(7,false),(4,true),(5,true),(12,false),(0,true),(9,false)])
                        .empty
                        .empty)
                      (.node 1279966 ([(2,true),(3,true),(10,true),(0,true),(12,true),(5,false),(8,true)],[(13,false),(6,true),(11,true),(1,true),(7,true),(4,false),(9,false)])
                        .empty
                        .empty))))))))))
    (.node 1603234 ([(3,true),(12,false),(1,false),(10,true),(5,true),(6,true),(8,true)],[(13,false),(4,true),(11,true),(2,true),(7,true),(0,true),(9,false)])
      (.node 1437958 ([(4,true),(5,true),(6,true),(0,true),(12,false),(2,false),(9,false)],[(13,false),(1,true),(10,true),(11,true),(3,true),(7,true),(8,true)])
        (.node 1329112 ([(1,true),(12,false),(6,false),(10,true),(3,true),(4,true),(8,true)],[(13,false),(2,true),(11,true),(0,true),(7,true),(5,true),(9,false)])
          (.node 1303510 ([(5,true),(6,true),(13,true),(3,false),(2,false),(1,false),(8,true)],[(4,true),(7,true),(0,false),(12,false),(11,false),(10,false),(9,false)])
            (.node 1290034 ([(4,true),(5,true),(13,true),(2,false),(10,false),(0,true),(8,true)],[(3,true),(7,true),(1,true),(11,true),(12,true),(6,true),(9,false)])
              (.node 1283560 ([(5,true),(12,false),(2,true),(3,true),(10,false),(0,false),(8,true)],[(13,false),(6,true),(7,false),(4,false),(11,true),(1,false),(9,false)])
                (.node 1281574 ([(0,true),(1,true),(2,true),(13,false),(5,false),(4,false),(8,true)],[(3,true),(7,false),(6,false),(12,false),(11,false),(10,false),(9,false)])
                  (.node 1281208 ([(5,true),(6,true),(0,true),(11,false),(3,false),(2,false),(9,false)],[(13,false),(12,false),(1,true),(10,true),(4,true),(7,true),(8,true)])
                    (.node 1281124 ([(5,true),(6,true),(0,true),(11,false),(3,false),(2,false),(8,true)],[(13,false),(12,false),(1,true),(7,false),(4,false),(10,false),(9,false)])
                      (.node 1280692 ([(0,true),(1,true),(2,true),(13,false),(5,false),(4,false),(8,true)],[(3,true),(7,false),(6,false),(12,false),(11,false),(10,false),(9,false)])
                        (.node 1280650 ([(0,true),(1,true),(2,true),(13,false),(5,false),(4,false),(9,false)],[(3,true),(10,true),(11,true),(12,true),(6,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1281142 ([(2,true),(3,true),(4,true),(5,true),(12,false),(0,false),(9,false)],[(13,false),(6,true),(10,true),(11,true),(1,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1281478 ([(2,true),(3,true),(4,true),(5,true),(12,false),(0,false),(9,false)],[(13,false),(6,true),(10,true),(11,true),(1,true),(7,true),(8,true)])
                      (.node 1281466 ([(4,true),(10,false),(0,true),(12,true),(13,true),(2,false),(8,true)],[(3,true),(7,true),(1,false),(11,false),(5,true),(6,true),(9,false)])
                        (.node 1281238 ([(0,true),(11,false),(4,true),(5,true),(13,true),(2,false),(9,false)],[(3,true),(10,false),(1,false),(12,true),(6,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1281550 ([(4,true),(5,true),(13,true),(2,false),(1,false),(0,false),(8,true)],[(3,true),(7,true),(6,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1282708 ([(0,true),(1,true),(2,true),(13,false),(5,false),(4,false),(9,false)],[(3,true),(10,true),(11,true),(12,true),(6,true),(7,true),(8,true)])
                    (.node 1282390 ([(4,true),(5,true),(13,true),(2,false),(11,false),(0,true),(8,true)],[(3,true),(7,true),(1,true),(12,true),(6,true),(10,false),(9,false)])
                      (.node 1282366 ([(1,true),(2,true),(3,true),(10,true),(6,false),(5,false),(8,true)],[(13,false),(12,false),(11,false),(0,true),(7,true),(4,false),(9,false)])
                        (.node 1282342 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1282408 ([(1,true),(2,true),(13,false),(6,true),(10,false),(4,false),(8,true)],[(3,true),(7,false),(0,false),(11,true),(12,true),(5,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1283518 ([(5,true),(6,true),(10,true),(3,false),(2,false),(1,false),(8,true)],[(13,false),(12,false),(11,false),(4,true),(7,true),(0,false),(9,false)])
                      (.node 1282750 ([(0,true),(1,true),(2,true),(13,false),(5,false),(4,false),(8,true)],[(3,true),(7,false),(6,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1283542 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                        .empty
                        .empty))))
                (.node 1287526 ([(2,true),(3,true),(11,false),(0,false),(6,false),(5,false),(9,false)],[(13,false),(12,false),(4,true),(10,true),(1,true),(7,true),(8,true)])
                  (.node 1283926 ([(0,true),(1,true),(2,true),(13,false),(5,false),(4,false),(8,true)],[(3,true),(7,false),(6,false),(12,false),(11,false),(10,false),(9,false)])
                    (.node 1283878 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                      (.node 1283860 ([(4,true),(11,true),(2,true),(13,false),(6,true),(0,true),(8,true)],[(3,true),(7,true),(1,true),(12,true),(5,false),(10,false),(9,false)])
                        (.node 1283590 ([(0,true),(1,true),(11,false),(3,false),(13,false),(5,false),(8,true)],[(2,false),(12,true),(6,true),(7,true),(4,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1283902 ([(4,true),(5,true),(13,true),(2,false),(1,false),(0,false),(8,true)],[(3,true),(7,true),(6,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1287046 ([(5,true),(6,true),(11,true),(3,false),(2,false),(1,false),(8,true)],[(13,false),(12,false),(4,true),(7,true),(0,false),(10,false),(9,false)])
                      (.node 1287004 ([(5,true),(13,true),(3,true),(11,false),(0,true),(1,true),(8,true)],[(2,false),(7,false),(4,false),(12,true),(6,true),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1287070 ([(1,true),(2,true),(3,true),(11,false),(6,false),(5,false),(8,true)],[(13,false),(12,false),(4,true),(7,false),(0,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1288702 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                    (.node 1287658 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                      (.node 1287634 ([(5,true),(12,false),(3,false),(2,false),(1,false),(0,false),(9,false)],[(13,false),(6,true),(10,true),(11,true),(4,true),(7,true),(8,true)])
                        (.node 1287538 ([(0,true),(1,true),(2,true),(13,false),(12,false),(4,true),(9,false)],[(3,true),(11,false),(10,false),(5,true),(6,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1287676 ([(5,true),(12,false),(3,false),(2,false),(1,false),(0,false),(8,true)],[(13,false),(6,true),(7,false),(4,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1289404 ([(3,false),(13,false),(5,false),(11,false),(0,true),(1,true),(8,true)],[(2,false),(7,false),(4,true),(12,true),(6,true),(10,false),(9,false)])
                      (.node 1288714 ([(0,true),(10,true),(4,false),(12,true),(13,true),(2,false),(8,true)],[(3,true),(11,false),(5,true),(6,true),(7,true),(1,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1289446 ([(3,false),(13,false),(5,false),(11,false),(0,true),(1,true),(9,false)],[(2,false),(10,true),(6,false),(12,false),(4,false),(7,true),(8,true)])
                        .empty
                        .empty)))))
              (.node 1300816 ([(6,true),(0,true),(1,true),(11,false),(4,false),(3,false),(9,false)],[(13,false),(12,false),(2,true),(10,true),(5,true),(7,true),(8,true)])
                (.node 1298422 ([(6,true),(0,true),(11,false),(4,false),(3,false),(2,false),(8,true)],[(13,false),(12,false),(1,true),(7,false),(5,false),(10,false),(9,false)])
                  (.node 1297558 ([(3,true),(13,false),(0,true),(1,true),(10,false),(5,false),(8,true)],[(4,true),(7,false),(2,false),(11,true),(12,true),(6,false),(9,false)])
                    (.node 1290772 ([(0,true),(10,true),(4,true),(5,true),(13,true),(2,false),(8,true)],[(3,true),(11,true),(12,true),(6,true),(7,true),(1,false),(9,false)])
                      (.node 1290760 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                        (.node 1290076 ([(4,true),(5,true),(13,true),(2,false),(1,false),(0,false),(8,true)],[(3,true),(7,true),(6,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1297516 ([(3,true),(4,true),(10,true),(1,false),(0,false),(6,false),(8,true)],[(13,false),(12,false),(11,false),(2,true),(7,true),(5,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1297900 ([(2,true),(11,true),(0,false),(13,true),(4,true),(5,true),(9,false)],[(3,false),(10,false),(6,true),(12,false),(1,true),(7,true),(8,true)])
                      (.node 1297858 ([(7,true),(6,true),(0,true),(11,false),(3,true),(4,true),(9,false)],[(13,false),(12,false),(1,true),(2,true),(10,false),(5,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1298380 ([(6,true),(0,true),(1,true),(10,true),(4,false),(3,false),(8,true)],[(13,false),(12,false),(11,false),(5,true),(7,true),(2,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1300258 ([(1,true),(2,true),(3,true),(13,false),(6,false),(5,false),(9,false)],[(4,true),(10,true),(11,true),(12,true),(0,true),(7,true),(8,true)])
                    (.node 1299574 ([(3,true),(4,true),(10,true),(1,true),(12,true),(6,false),(8,true)],[(13,false),(0,true),(11,true),(2,true),(7,true),(5,false),(9,false)])
                      (.node 1298764 ([(5,true),(11,true),(0,false),(13,true),(3,false),(2,false),(8,true)],[(4,true),(7,true),(1,false),(12,true),(6,false),(10,false),(9,false)])
                        (.node 1298722 ([(4,false),(13,false),(0,true),(11,false),(10,false),(2,true),(8,true)],[(3,false),(7,false),(5,true),(6,true),(12,false),(1,true),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1299616 ([(3,true),(13,false),(12,false),(1,false),(10,false),(5,false),(8,true)],[(4,true),(7,false),(2,false),(11,false),(0,false),(6,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1300732 ([(6,true),(0,true),(1,true),(11,false),(4,false),(3,false),(8,true)],[(13,false),(12,false),(2,true),(7,false),(5,false),(10,false),(9,false)])
                      (.node 1300300 ([(1,true),(2,true),(3,true),(13,false),(6,false),(5,false),(8,true)],[(4,true),(7,false),(0,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1300750 ([(3,true),(4,true),(5,true),(6,true),(12,false),(1,false),(9,false)],[(13,false),(0,true),(10,true),(11,true),(2,true),(7,true),(8,true)])
                        .empty
                        .empty))))
                (.node 1302016 ([(2,true),(3,true),(13,false),(0,true),(10,false),(5,false),(8,true)],[(4,true),(7,false),(1,false),(11,true),(12,true),(6,false),(9,false)])
                  (.node 1301182 ([(1,true),(2,true),(3,true),(13,false),(6,false),(5,false),(8,true)],[(4,true),(7,false),(0,false),(12,false),(11,false),(10,false),(9,false)])
                    (.node 1301086 ([(3,true),(4,true),(5,true),(6,true),(12,false),(1,false),(9,false)],[(13,false),(0,true),(10,true),(11,true),(2,true),(7,true),(8,true)])
                      (.node 1301074 ([(5,true),(10,false),(1,true),(12,true),(13,true),(3,false),(8,true)],[(4,true),(7,true),(2,false),(11,false),(6,true),(0,true),(9,false)])
                        (.node 1300846 ([(1,true),(11,false),(5,true),(6,true),(13,true),(3,false),(9,false)],[(4,true),(10,false),(2,false),(12,true),(0,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1301158 ([(5,true),(6,true),(13,true),(3,false),(2,false),(1,false),(8,true)],[(4,true),(7,true),(0,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1301974 ([(2,true),(3,true),(4,true),(10,true),(0,false),(6,false),(8,true)],[(13,false),(12,false),(11,false),(1,true),(7,true),(5,false),(9,false)])
                      (.node 1301950 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1301998 ([(5,true),(6,true),(13,true),(3,false),(11,false),(1,true),(8,true)],[(4,true),(7,true),(2,true),(12,true),(0,true),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1303168 ([(6,true),(12,false),(3,true),(4,true),(10,false),(1,false),(8,true)],[(13,false),(0,true),(7,false),(5,false),(11,true),(2,false),(9,false)])
                    (.node 1303126 ([(6,true),(0,true),(10,true),(4,false),(3,false),(2,false),(8,true)],[(13,false),(12,false),(11,false),(5,true),(7,true),(1,false),(9,false)])
                      (.node 1302358 ([(1,true),(2,true),(3,true),(13,false),(6,false),(5,false),(8,true)],[(4,true),(7,false),(0,false),(12,false),(11,false),(10,false),(9,false)])
                        (.node 1302316 ([(1,true),(2,true),(3,true),(13,false),(6,false),(5,false),(9,false)],[(4,true),(10,true),(11,true),(12,true),(0,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1303150 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1303468 ([(5,true),(11,true),(3,true),(13,false),(0,true),(1,true),(8,true)],[(4,true),(7,true),(2,true),(12,true),(6,false),(10,false),(9,false)])
                      (.node 1303198 ([(1,true),(2,true),(11,false),(4,false),(13,false),(6,false),(8,true)],[(3,false),(12,true),(0,true),(7,true),(5,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1303486 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                        .empty
                        .empty))))))
            (.node 1319884 ([(6,true),(0,true),(13,true),(4,true),(11,true),(2,false),(8,true)],[(3,false),(12,true),(1,true),(7,false),(5,false),(10,false),(9,false)])
              (.node 1311964 ([(3,true),(13,false),(0,false),(11,false),(10,false),(5,false),(8,true)],[(4,true),(7,false),(2,false),(1,false),(12,false),(6,false),(9,false)])
                (.node 1308310 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                  (.node 1307134 ([(3,true),(4,true),(11,false),(1,false),(0,false),(6,false),(9,false)],[(13,false),(12,false),(5,true),(10,true),(2,true),(7,true),(8,true)])
                    (.node 1306654 ([(6,true),(0,true),(11,true),(4,false),(3,false),(2,false),(8,true)],[(13,false),(12,false),(5,true),(7,true),(1,false),(10,false),(9,false)])
                      (.node 1306612 ([(6,true),(13,true),(4,true),(11,false),(1,true),(2,true),(8,true)],[(3,false),(7,false),(5,false),(12,true),(0,true),(10,false),(9,false)])
                        (.node 1303534 ([(1,true),(2,true),(3,true),(13,false),(6,false),(5,false),(8,true)],[(4,true),(7,false),(0,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1306678 ([(2,true),(3,true),(4,true),(11,false),(0,false),(6,false),(8,true)],[(13,false),(12,false),(5,true),(7,false),(1,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1307266 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                      (.node 1307242 ([(6,true),(12,false),(4,false),(3,false),(2,false),(1,false),(9,false)],[(13,false),(0,true),(10,true),(11,true),(5,true),(7,true),(8,true)])
                        (.node 1307146 ([(1,true),(2,true),(3,true),(13,false),(12,false),(5,true),(9,false)],[(4,true),(11,false),(10,false),(6,true),(0,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1307284 ([(6,true),(12,false),(4,false),(3,false),(2,false),(1,false),(8,true)],[(13,false),(0,true),(7,false),(5,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1309684 ([(5,true),(6,true),(13,true),(3,false),(2,false),(1,false),(8,true)],[(4,true),(7,true),(0,false),(12,false),(11,false),(10,false),(9,false)])
                    (.node 1309054 ([(4,false),(13,false),(6,false),(11,false),(1,true),(2,true),(9,false)],[(3,false),(10,true),(0,false),(12,false),(5,false),(7,true),(8,true)])
                      (.node 1309012 ([(4,false),(13,false),(6,false),(11,false),(1,true),(2,true),(8,true)],[(3,false),(7,false),(5,true),(12,true),(0,true),(10,false),(9,false)])
                        (.node 1308322 ([(1,true),(10,true),(5,false),(12,true),(13,true),(3,false),(8,true)],[(4,true),(11,false),(6,true),(0,true),(7,true),(2,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1309642 ([(5,true),(6,true),(13,true),(3,false),(10,false),(1,true),(8,true)],[(4,true),(7,true),(2,true),(11,true),(12,true),(0,true),(9,false)])
                        .empty
                        .empty))
                    (.node 1310380 ([(1,true),(10,true),(5,true),(6,true),(13,true),(3,false),(8,true)],[(4,true),(11,true),(12,true),(0,true),(7,true),(2,false),(9,false)])
                      (.node 1310368 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1311922 ([(3,true),(4,true),(10,true),(1,false),(0,false),(6,false),(8,true)],[(13,false),(12,false),(11,false),(2,true),(7,true),(5,false),(9,false)])
                        .empty
                        .empty))))
                (.node 1317076 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,false),(7,true),(8,true)])
                  (.node 1313128 ([(4,false),(13,false),(0,false),(6,false),(10,false),(2,true),(8,true)],[(3,false),(7,false),(5,true),(11,true),(12,true),(1,true),(9,false)])
                    (.node 1312786 ([(6,true),(0,true),(1,true),(10,true),(4,false),(3,false),(8,true)],[(13,false),(12,false),(11,false),(5,true),(7,true),(2,false),(9,false)])
                      (.node 1312306 ([(2,true),(3,true),(13,false),(0,false),(6,false),(5,false),(8,true)],[(4,true),(7,false),(1,false),(12,false),(11,false),(10,false),(9,false)])
                        (.node 1312264 ([(2,true),(3,true),(13,false),(0,false),(6,false),(5,false),(9,false)],[(4,true),(10,true),(11,true),(12,true),(1,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1312828 ([(7,true),(1,false),(0,false),(11,false),(4,false),(3,false),(9,false)],[(13,false),(12,false),(6,false),(5,false),(10,false),(2,false),(8,true)])
                        .empty
                        .empty))
                    (.node 1316038 ([(3,true),(13,false),(1,true),(11,false),(6,false),(5,false),(9,false)],[(4,true),(10,true),(0,true),(12,false),(2,true),(7,true),(8,true)])
                      (.node 1313170 ([(5,true),(6,true),(0,true),(13,true),(3,false),(2,false),(8,true)],[(4,true),(7,true),(1,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1316080 ([(3,true),(13,false),(1,true),(11,false),(6,false),(5,false),(8,true)],[(4,true),(7,false),(2,false),(12,true),(0,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1318438 ([(2,true),(3,true),(13,false),(0,false),(6,false),(5,false),(9,false)],[(4,true),(10,true),(11,true),(12,true),(1,true),(7,true),(8,true)])
                    (.node 1317760 ([(2,false),(1,false),(13,true),(4,true),(5,true),(6,true),(8,true)],[(3,false),(7,true),(0,true),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1317508 ([(3,true),(4,true),(11,true),(1,false),(0,false),(6,false),(8,true)],[(13,false),(12,false),(2,true),(7,true),(5,false),(10,false),(9,false)])
                        (.node 1317106 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1318414 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1319134 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,false),(7,true),(8,true)])
                      (.node 1318480 ([(2,true),(3,true),(13,false),(0,false),(6,false),(5,false),(8,true)],[(4,true),(7,false),(1,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1319164 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                        .empty
                        .empty)))))
              (.node 1325170 ([(6,false),(5,false),(4,false),(13,false),(1,true),(2,true),(9,false)],[(3,false),(10,true),(11,true),(12,true),(0,false),(7,true),(8,true)])
                (.node 1323664 ([(6,true),(0,true),(1,true),(11,true),(4,false),(3,false),(8,true)],[(13,false),(12,false),(5,true),(7,true),(2,false),(10,false),(9,false)])
                  (.node 1323076 ([(6,true),(0,true),(12,false),(4,false),(3,false),(2,false),(9,false)],[(13,false),(1,true),(10,true),(11,true),(5,true),(7,true),(8,true)])
                    (.node 1320310 ([(5,true),(10,false),(2,true),(3,true),(13,false),(0,false),(8,true)],[(4,true),(7,true),(6,false),(11,true),(12,true),(1,true),(9,false)])
                      (.node 1320160 ([(1,false),(12,false),(3,true),(4,true),(5,true),(6,true),(8,true)],[(13,false),(0,false),(7,false),(2,true),(11,false),(10,false),(9,false)])
                        (.node 1319908 ([(2,true),(3,true),(13,false),(0,false),(10,true),(5,true),(8,true)],[(4,true),(11,true),(12,true),(1,true),(7,true),(6,true),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1320340 ([(0,true),(12,false),(3,true),(4,true),(5,true),(10,false),(9,false)],[(13,false),(1,true),(2,true),(11,false),(6,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1323118 ([(6,true),(0,true),(12,false),(4,false),(3,false),(2,false),(8,true)],[(13,false),(1,true),(7,false),(5,false),(11,false),(10,false),(9,false)])
                      (.node 1323094 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1323142 ([(2,true),(3,true),(4,true),(12,true),(0,false),(6,false),(8,true)],[(13,false),(1,true),(7,true),(5,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1324024 ([(2,true),(3,true),(4,true),(12,true),(0,false),(6,false),(8,true)],[(13,false),(1,true),(7,true),(5,false),(11,false),(10,false),(9,false)])
                    (.node 1323952 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                      (.node 1323934 ([(3,true),(4,true),(5,true),(10,true),(1,false),(0,false),(8,true)],[(13,false),(12,false),(11,false),(2,true),(7,true),(6,false),(9,false)])
                        (.node 1323682 ([(3,true),(4,true),(11,false),(1,false),(0,false),(6,false),(8,true)],[(13,false),(12,false),(5,true),(7,false),(2,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1324000 ([(6,true),(0,true),(12,false),(4,false),(3,false),(2,false),(8,true)],[(13,false),(1,true),(7,false),(5,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1324288 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                      (.node 1324276 ([(2,true),(10,false),(5,false),(4,false),(13,false),(0,false),(8,true)],[(3,false),(11,true),(12,true),(1,true),(7,true),(6,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1325128 ([(0,true),(1,true),(10,true),(5,false),(4,false),(3,false),(8,true)],[(13,false),(12,false),(11,false),(6,true),(7,true),(2,false),(9,false)])
                        .empty
                        .empty))))
                (.node 1326628 ([(2,true),(3,true),(4,true),(5,true),(12,true),(0,false),(8,true)],[(13,false),(1,true),(7,true),(6,false),(11,false),(10,false),(9,false)])
                  (.node 1326286 ([(3,true),(4,true),(5,true),(11,false),(1,false),(0,false),(8,true)],[(13,false),(12,false),(6,true),(7,false),(2,false),(10,false),(9,false)])
                    (.node 1326064 ([(5,true),(6,true),(10,true),(1,false),(13,true),(3,false),(8,true)],[(4,true),(7,true),(2,false),(11,true),(12,true),(0,false),(9,false)])
                      (.node 1325518 ([(5,true),(6,true),(0,true),(13,true),(3,false),(2,false),(8,true)],[(4,true),(7,true),(1,false),(12,false),(11,false),(10,false),(9,false)])
                        (.node 1325476 ([(4,false),(13,false),(12,false),(6,true),(10,false),(2,true),(8,true)],[(3,false),(7,false),(5,true),(11,false),(0,true),(1,true),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1326076 ([(3,true),(4,true),(5,true),(11,false),(1,false),(0,false),(9,false)],[(13,false),(12,false),(6,true),(10,true),(2,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1326400 ([(5,true),(6,true),(0,true),(13,true),(3,false),(2,false),(8,true)],[(4,true),(7,true),(1,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1326304 ([(0,true),(1,true),(11,true),(5,false),(4,false),(3,false),(8,true)],[(13,false),(12,false),(6,true),(7,true),(2,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1326418 ([(2,true),(3,true),(13,false),(0,false),(6,false),(5,false),(8,true)],[(4,true),(7,false),(1,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1328428 ([(3,true),(13,false),(1,false),(0,false),(6,false),(5,false),(8,true)],[(4,true),(7,false),(2,false),(12,false),(11,false),(10,false),(9,false)])
                    (.node 1327228 ([(0,true),(12,false),(5,false),(4,false),(3,false),(2,false),(8,true)],[(13,false),(1,true),(7,false),(6,false),(11,false),(10,false),(9,false)])
                      (.node 1327186 ([(0,true),(12,false),(5,false),(4,false),(3,false),(2,false),(9,false)],[(13,false),(1,true),(10,true),(11,true),(6,true),(7,true),(8,true)])
                        (.node 1326640 ([(0,true),(12,false),(5,false),(4,false),(3,false),(2,false),(8,true)],[(13,false),(1,true),(7,false),(6,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1328386 ([(3,true),(13,false),(1,false),(0,false),(6,false),(5,false),(9,false)],[(4,true),(10,true),(11,true),(12,true),(2,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1329070 ([(1,true),(13,true),(3,false),(11,true),(6,false),(5,false),(9,false)],[(4,true),(10,true),(2,false),(12,false),(0,true),(7,true),(8,true)])
                      (.node 1329040 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1329088 ([(5,true),(6,true),(11,false),(3,true),(13,false),(1,false),(8,true)],[(4,true),(7,true),(0,false),(12,true),(2,true),(10,false),(9,false)])
                        .empty
                        .empty)))))))
          (.node 1407094 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
            (.node 1343926 ([(3,true),(4,true),(5,true),(12,true),(1,false),(0,false),(8,true)],[(13,false),(2,true),(7,true),(6,false),(11,false),(10,false),(9,false)])
              (.node 1339918 ([(6,true),(0,true),(1,true),(12,false),(4,false),(3,false),(9,false)],[(13,false),(2,true),(10,true),(11,true),(5,true),(7,true),(8,true)])
                (.node 1332166 ([(7,true),(0,true),(1,true),(13,true),(4,true),(5,true),(9,false)],[(3,false),(2,false),(12,false),(11,false),(10,false),(6,true),(8,true)])
                  (.node 1330444 ([(3,true),(13,false),(1,false),(0,false),(6,false),(5,false),(9,false)],[(4,true),(10,true),(11,true),(12,true),(2,true),(7,true),(8,true)])
                    (.node 1329628 ([(6,true),(0,true),(1,true),(13,true),(4,true),(10,false),(9,false)],[(3,false),(2,false),(12,false),(11,false),(5,true),(7,true),(8,true)])
                      (.node 1329562 ([(3,true),(4,true),(10,false),(1,true),(12,false),(6,false),(8,true)],[(13,false),(2,true),(7,true),(5,false),(11,true),(0,true),(9,false)])
                        (.node 1329544 ([(6,true),(0,true),(10,true),(4,false),(13,false),(2,true),(8,true)],[(3,false),(7,false),(5,false),(11,true),(12,true),(1,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1329658 ([(1,true),(2,true),(3,true),(4,true),(11,true),(6,false),(8,true)],[(13,false),(12,false),(0,true),(7,true),(5,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1331512 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                      (.node 1331482 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,false),(7,true),(8,true)])
                        (.node 1330486 ([(3,true),(13,false),(1,false),(0,false),(6,false),(5,false),(8,true)],[(4,true),(7,false),(2,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1331914 ([(3,true),(13,false),(1,false),(0,false),(10,true),(5,true),(8,true)],[(4,true),(11,true),(12,true),(2,true),(7,true),(6,true),(9,false)])
                        .empty
                        .empty)))
                  (.node 1336684 ([(6,true),(10,true),(4,false),(3,false),(2,false),(1,false),(8,true)],[(13,false),(12,false),(11,false),(5,true),(7,true),(0,false),(9,false)])
                    (.node 1335598 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(5,false),(7,true),(8,true)])
                      (.node 1335286 ([(7,true),(4,false),(13,false),(2,true),(11,false),(6,false),(9,false)],[(3,false),(12,true),(1,false),(0,false),(10,false),(5,false),(8,true)])
                        (.node 1335244 ([(1,true),(2,true),(3,true),(4,true),(10,true),(6,false),(8,true)],[(13,false),(12,false),(11,false),(0,true),(7,true),(5,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1335628 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1337026 ([(4,false),(13,false),(2,true),(11,false),(6,true),(0,true),(8,true)],[(3,false),(12,true),(1,false),(7,false),(5,true),(10,false),(9,false)])
                      (.node 1336714 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1337068 ([(4,false),(3,false),(2,false),(1,false),(10,true),(6,true),(8,true)],[(13,false),(12,false),(11,false),(5,false),(7,true),(0,true),(9,false)])
                        .empty
                        .empty))))
                (.node 1342654 ([(5,true),(12,true),(13,true),(3,false),(10,true),(0,false),(8,true)],[(4,true),(7,true),(6,false),(11,false),(1,true),(2,true),(9,false)])
                  (.node 1340800 ([(6,true),(10,true),(3,true),(4,true),(12,true),(1,false),(8,true)],[(13,false),(2,true),(11,true),(5,true),(7,true),(0,false),(9,false)])
                    (.node 1340398 ([(3,true),(4,true),(12,true),(1,false),(10,false),(6,true),(8,true)],[(13,false),(2,true),(7,true),(0,true),(11,true),(5,true),(9,false)])
                      (.node 1340146 ([(3,true),(4,true),(12,true),(1,false),(0,false),(6,false),(8,true)],[(13,false),(2,true),(7,true),(5,false),(11,false),(10,false),(9,false)])
                        (.node 1339948 ([(1,true),(2,true),(3,true),(4,true),(11,false),(6,false),(8,true)],[(13,false),(12,false),(5,true),(7,false),(0,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1340416 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1341826 ([(2,false),(13,true),(4,true),(5,true),(6,true),(0,true),(8,true)],[(3,false),(7,true),(1,true),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1340830 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1341868 ([(3,true),(13,false),(12,false),(5,true),(6,true),(0,true),(9,false)],[(4,true),(11,false),(10,false),(1,true),(2,true),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1343224 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                    (.node 1342768 ([(0,true),(1,true),(12,false),(5,false),(4,false),(3,false),(8,true)],[(13,false),(2,true),(7,false),(6,false),(11,false),(10,false),(9,false)])
                      (.node 1342750 ([(3,true),(4,true),(5,true),(12,true),(1,false),(0,false),(8,true)],[(13,false),(2,true),(7,true),(6,false),(11,false),(10,false),(9,false)])
                        (.node 1342684 ([(0,true),(1,true),(12,false),(5,false),(4,false),(3,false),(9,false)],[(13,false),(2,true),(10,true),(11,true),(6,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1343200 ([(5,true),(12,true),(13,true),(3,false),(10,false),(0,true),(8,true)],[(4,true),(7,true),(1,true),(2,true),(11,true),(6,true),(9,false)])
                        .empty
                        .empty))
                    (.node 1343272 ([(0,true),(1,true),(13,true),(3,false),(11,true),(5,false),(8,true)],[(4,true),(7,false),(6,false),(12,true),(2,true),(10,false),(9,false)])
                      (.node 1343242 ([(5,true),(11,false),(3,true),(13,false),(1,false),(0,false),(8,true)],[(4,true),(7,true),(6,false),(12,true),(2,true),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1343884 ([(2,false),(13,true),(4,true),(5,true),(6,true),(0,true),(8,true)],[(3,false),(7,true),(1,true),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))))
              (.node 1399966 ([(1,true),(11,false),(6,false),(5,false),(4,false),(3,false),(9,false)],[(13,false),(12,false),(2,true),(10,true),(0,true),(7,true),(8,true)])
                (.node 1398430 ([(5,true),(13,true),(3,false),(10,false),(0,true),(1,true),(8,true)],[(4,true),(7,true),(2,true),(11,true),(12,true),(6,true),(9,false)])
                  (.node 1396804 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                    (.node 1396078 ([(4,false),(13,false),(6,true),(0,true),(10,true),(2,false),(8,true)],[(3,false),(11,true),(12,true),(5,false),(7,true),(1,false),(9,false)])
                      (.node 1395490 ([(4,false),(13,false),(6,true),(0,true),(1,true),(2,true),(9,false)],[(3,false),(10,true),(11,true),(12,true),(5,false),(7,true),(8,true)])
                        (.node 1395448 ([(4,false),(13,false),(6,true),(0,true),(1,true),(2,true),(8,true)],[(3,false),(7,false),(5,true),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1396120 ([(7,true),(0,false),(6,false),(13,true),(3,false),(2,false),(9,false)],[(4,true),(5,true),(12,false),(11,false),(10,false),(1,false),(8,true)])
                        .empty
                        .empty))
                    (.node 1397506 ([(4,false),(13,false),(6,true),(0,true),(1,true),(2,true),(8,true)],[(3,false),(7,false),(5,true),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1396816 ([(1,true),(10,true),(11,true),(6,false),(13,true),(3,false),(8,true)],[(4,true),(5,true),(12,false),(0,true),(7,true),(2,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1397548 ([(4,false),(13,false),(6,true),(0,true),(1,true),(2,true),(9,false)],[(3,false),(10,true),(11,true),(12,true),(5,false),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1399216 ([(0,true),(1,true),(10,true),(5,true),(13,true),(3,false),(8,true)],[(4,true),(11,true),(12,true),(6,true),(7,true),(2,false),(9,false)])
                    (.node 1398670 ([(0,true),(1,true),(2,true),(3,true),(13,false),(5,false),(9,false)],[(4,true),(10,true),(11,true),(12,true),(6,true),(7,true),(8,true)])
                      (.node 1398658 ([(2,true),(3,true),(4,true),(5,true),(12,false),(0,false),(8,true)],[(13,false),(6,true),(7,false),(1,false),(11,false),(10,false),(9,false)])
                        (.node 1398448 ([(2,true),(3,true),(4,true),(5,true),(12,false),(0,false),(9,false)],[(13,false),(6,true),(10,true),(11,true),(1,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1399198 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1399258 ([(0,true),(12,true),(5,false),(4,false),(3,false),(2,false),(8,true)],[(13,false),(6,true),(7,true),(1,false),(11,false),(10,false),(9,false)])
                      (.node 1399246 ([(2,true),(3,true),(4,true),(5,true),(12,false),(0,false),(8,true)],[(13,false),(6,true),(7,false),(1,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1399942 ([(5,true),(13,true),(3,false),(2,false),(11,false),(0,true),(8,true)],[(4,true),(7,true),(1,true),(12,true),(6,true),(10,false),(9,false)])
                        .empty
                        .empty))))
                (.node 1402252 ([(5,true),(13,true),(3,false),(11,false),(0,true),(1,true),(8,true)],[(4,true),(7,true),(2,true),(12,true),(6,true),(10,false),(9,false)])
                  (.node 1401508 ([(3,true),(4,true),(5,true),(12,false),(1,false),(0,false),(9,false)],[(13,false),(6,true),(10,true),(11,true),(2,true),(7,true),(8,true)])
                    (.node 1400824 ([(4,false),(3,false),(2,false),(12,true),(6,true),(0,true),(8,true)],[(13,false),(5,false),(7,true),(1,true),(11,false),(10,false),(9,false)])
                      (.node 1400050 ([(1,true),(2,true),(3,true),(13,false),(6,true),(10,false),(9,false)],[(4,true),(5,true),(12,false),(11,false),(0,true),(7,true),(8,true)])
                        (.node 1400038 ([(3,true),(4,true),(5,true),(6,true),(11,true),(1,false),(8,true)],[(13,false),(12,false),(2,true),(7,true),(0,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1400866 ([(5,true),(13,true),(3,false),(2,false),(1,false),(0,false),(8,true)],[(4,true),(7,true),(6,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1401550 ([(3,true),(4,true),(5,true),(12,false),(1,false),(0,false),(8,true)],[(13,false),(6,true),(7,false),(2,false),(11,false),(10,false),(9,false)])
                      (.node 1401520 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1401568 ([(0,true),(1,true),(12,true),(5,false),(4,false),(3,false),(8,true)],[(13,false),(6,true),(7,true),(2,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1402882 ([(5,true),(13,true),(3,false),(2,false),(10,false),(0,true),(8,true)],[(4,true),(7,true),(1,true),(11,true),(12,true),(6,true),(9,false)])
                    (.node 1402774 ([(2,true),(3,true),(13,false),(6,true),(0,true),(10,false),(9,false)],[(4,true),(5,true),(12,false),(11,false),(1,true),(7,true),(8,true)])
                      (.node 1402318 ([(1,true),(2,true),(11,false),(6,false),(13,true),(4,true),(8,true)],[(3,false),(12,true),(5,false),(7,false),(0,false),(10,false),(9,false)])
                        (.node 1402294 ([(5,true),(13,true),(3,false),(11,false),(10,false),(1,false),(8,true)],[(4,true),(7,true),(0,false),(6,false),(12,false),(2,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1402786 ([(0,true),(1,true),(2,true),(3,true),(13,false),(5,false),(9,false)],[(4,true),(10,true),(11,true),(12,true),(6,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1403950 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                      (.node 1402924 ([(5,true),(13,true),(3,false),(2,false),(1,false),(0,false),(8,true)],[(4,true),(7,true),(6,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1403962 ([(0,true),(10,true),(4,false),(13,false),(12,false),(2,false),(8,true)],[(3,false),(11,false),(5,true),(6,true),(7,true),(1,false),(9,false)])
                        .empty
                        .empty))))))
            (.node 1422382 ([(3,true),(4,true),(13,false),(0,true),(1,true),(10,false),(9,false)],[(5,true),(6,true),(12,false),(11,false),(2,true),(7,true),(8,true)])
              (.node 1418278 ([(1,true),(2,true),(3,true),(4,true),(13,false),(6,false),(9,false)],[(5,true),(10,true),(11,true),(12,true),(0,true),(7,true),(8,true)])
                (.node 1415686 ([(5,false),(13,false),(0,true),(1,true),(10,true),(3,false),(8,true)],[(4,false),(11,true),(12,true),(6,false),(7,true),(2,false),(9,false)])
                  (.node 1407724 ([(3,true),(13,false),(5,false),(11,false),(1,false),(0,false),(8,true)],[(4,true),(12,true),(6,true),(7,false),(2,false),(10,false),(9,false)])
                    (.node 1407490 ([(0,true),(11,true),(5,true),(13,true),(3,false),(2,false),(8,true)],[(4,true),(12,true),(6,true),(7,true),(1,false),(10,false),(9,false)])
                      (.node 1407448 ([(7,true),(3,true),(13,false),(5,false),(11,false),(1,true),(9,false)],[(4,true),(12,true),(6,true),(0,true),(10,false),(2,true),(8,true)])
                        (.node 1407106 ([(1,true),(10,true),(6,false),(5,false),(4,false),(3,false),(8,true)],[(13,false),(12,false),(11,false),(0,true),(7,true),(2,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1407682 ([(3,true),(4,true),(5,true),(6,true),(10,true),(1,false),(8,true)],[(13,false),(12,false),(11,false),(2,true),(7,true),(0,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1415056 ([(5,false),(13,false),(0,true),(1,true),(2,true),(3,true),(8,true)],[(4,false),(7,false),(6,true),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1408078 ([(6,false),(5,false),(4,false),(3,false),(2,false),(1,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,false),(7,true),(8,true)])
                        (.node 1408066 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1415098 ([(5,false),(13,false),(0,true),(1,true),(2,true),(3,true),(9,false)],[(4,false),(10,true),(11,true),(12,true),(6,false),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1417156 ([(5,false),(13,false),(0,true),(1,true),(2,true),(3,true),(9,false)],[(4,false),(10,true),(11,true),(12,true),(6,false),(7,true),(8,true)])
                    (.node 1416424 ([(2,true),(10,true),(11,true),(0,false),(13,true),(4,false),(8,true)],[(5,true),(6,true),(12,false),(1,true),(7,true),(3,false),(9,false)])
                      (.node 1416412 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                        (.node 1415728 ([(7,true),(1,false),(0,false),(13,true),(4,false),(3,false),(9,false)],[(5,true),(6,true),(12,false),(11,false),(10,false),(2,false),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1417114 ([(5,false),(13,false),(0,true),(1,true),(2,true),(3,true),(8,true)],[(4,false),(7,false),(6,true),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1418056 ([(3,true),(4,true),(5,true),(6,true),(12,false),(1,false),(9,false)],[(13,false),(0,true),(10,true),(11,true),(2,true),(7,true),(8,true)])
                      (.node 1418038 ([(6,true),(13,true),(4,false),(10,false),(1,true),(2,true),(8,true)],[(5,true),(7,true),(3,true),(11,true),(12,true),(0,true),(9,false)])
                        .empty
                        .empty)
                      (.node 1418266 ([(3,true),(4,true),(5,true),(6,true),(12,false),(1,false),(8,true)],[(13,false),(0,true),(7,false),(2,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))))
                (.node 1420432 ([(5,false),(4,false),(3,false),(12,true),(0,true),(1,true),(8,true)],[(13,false),(6,false),(7,true),(2,true),(11,false),(10,false),(9,false)])
                  (.node 1419550 ([(6,true),(13,true),(4,false),(3,false),(11,false),(1,true),(8,true)],[(5,true),(7,true),(2,true),(12,true),(0,true),(10,false),(9,false)])
                    (.node 1418854 ([(3,true),(4,true),(5,true),(6,true),(12,false),(1,false),(8,true)],[(13,false),(0,true),(7,false),(2,false),(11,false),(10,false),(9,false)])
                      (.node 1418824 ([(1,true),(2,true),(10,true),(6,true),(13,true),(4,false),(8,true)],[(5,true),(11,true),(12,true),(0,true),(7,true),(3,false),(9,false)])
                        (.node 1418806 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1418866 ([(1,true),(12,true),(6,false),(5,false),(4,false),(3,false),(8,true)],[(13,false),(0,true),(7,true),(2,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1419646 ([(4,true),(5,true),(6,true),(0,true),(11,true),(2,false),(8,true)],[(13,false),(12,false),(3,true),(7,true),(1,false),(10,false),(9,false)])
                      (.node 1419574 ([(2,true),(11,false),(0,false),(6,false),(5,false),(4,false),(9,false)],[(13,false),(12,false),(3,true),(10,true),(1,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1419658 ([(2,true),(3,true),(4,true),(13,false),(0,true),(10,false),(9,false)],[(5,true),(6,true),(12,false),(11,false),(1,true),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1421176 ([(1,true),(2,true),(12,true),(6,false),(5,false),(4,false),(8,true)],[(13,false),(0,true),(7,true),(3,false),(11,false),(10,false),(9,false)])
                    (.node 1421128 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                      (.node 1421116 ([(4,true),(5,true),(6,true),(12,false),(2,false),(1,false),(9,false)],[(13,false),(0,true),(10,true),(11,true),(3,true),(7,true),(8,true)])
                        (.node 1420474 ([(6,true),(13,true),(4,false),(3,false),(2,false),(1,false),(8,true)],[(5,true),(7,true),(0,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1421158 ([(4,true),(5,true),(6,true),(12,false),(2,false),(1,false),(8,true)],[(13,false),(0,true),(7,false),(3,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1421902 ([(6,true),(13,true),(4,false),(11,false),(10,false),(2,false),(8,true)],[(5,true),(7,true),(1,false),(0,false),(12,false),(3,false),(9,false)])
                      (.node 1421860 ([(6,true),(13,true),(4,false),(11,false),(1,true),(2,true),(8,true)],[(5,true),(7,true),(3,true),(12,true),(0,true),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1421926 ([(2,true),(3,true),(11,false),(0,false),(13,true),(5,true),(8,true)],[(4,false),(12,true),(6,false),(7,false),(1,false),(10,false),(9,false)])
                        .empty
                        .empty)))))
              (.node 1430818 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                (.node 1427098 ([(1,true),(11,true),(6,true),(13,true),(4,false),(3,false),(8,true)],[(5,true),(12,true),(0,true),(7,true),(2,false),(10,false),(9,false)])
                  (.node 1423570 ([(1,true),(10,true),(5,false),(13,false),(12,false),(3,false),(8,true)],[(4,false),(11,false),(6,true),(0,true),(7,true),(2,false),(9,false)])
                    (.node 1422532 ([(6,true),(13,true),(4,false),(3,false),(2,false),(1,false),(8,true)],[(5,true),(7,true),(0,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1422490 ([(6,true),(13,true),(4,false),(3,false),(10,false),(1,true),(8,true)],[(5,true),(7,true),(2,true),(11,true),(12,true),(0,true),(9,false)])
                        (.node 1422394 ([(1,true),(2,true),(3,true),(4,true),(13,false),(6,false),(9,false)],[(5,true),(10,true),(11,true),(12,true),(0,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1423558 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1426714 ([(2,true),(10,true),(0,false),(6,false),(5,false),(4,false),(8,true)],[(13,false),(12,false),(11,false),(1,true),(7,true),(3,false),(9,false)])
                      (.node 1426702 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1427056 ([(7,true),(4,true),(13,false),(6,false),(11,false),(2,true),(9,false)],[(5,true),(12,true),(0,true),(1,true),(10,false),(3,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1429462 ([(5,false),(13,false),(0,false),(11,false),(2,true),(3,true),(8,true)],[(4,false),(7,false),(6,true),(12,true),(1,true),(10,false),(9,false)])
                    (.node 1427674 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                      (.node 1427332 ([(4,true),(13,false),(6,false),(11,false),(2,false),(1,false),(8,true)],[(5,true),(12,true),(0,true),(7,false),(3,false),(10,false),(9,false)])
                        (.node 1427290 ([(4,true),(5,true),(6,true),(0,true),(10,true),(2,false),(8,true)],[(13,false),(12,false),(11,false),(3,true),(7,true),(1,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1427686 ([(0,false),(6,false),(5,false),(4,false),(3,false),(2,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,false),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1430092 ([(6,true),(0,true),(13,true),(4,false),(10,false),(2,true),(8,true)],[(5,true),(7,true),(3,true),(11,true),(12,true),(1,true),(9,false)])
                      (.node 1429504 ([(5,false),(13,false),(0,false),(11,false),(2,true),(3,true),(9,false)],[(4,false),(10,true),(1,false),(12,false),(6,false),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1430134 ([(6,true),(0,true),(13,true),(4,false),(3,false),(2,false),(8,true)],[(5,true),(7,true),(1,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))))
                (.node 1435672 ([(0,true),(1,true),(11,false),(5,false),(4,false),(3,false),(8,true)],[(13,false),(12,false),(2,true),(7,false),(6,false),(10,false),(9,false)])
                  (.node 1434724 ([(4,true),(5,true),(10,true),(2,false),(1,false),(0,false),(8,true)],[(13,false),(12,false),(11,false),(3,true),(7,true),(6,false),(9,false)])
                    (.node 1433620 ([(6,true),(11,true),(1,false),(13,true),(4,false),(3,false),(8,true)],[(5,true),(7,true),(2,false),(12,true),(0,false),(10,false),(9,false)])
                      (.node 1433578 ([(5,false),(13,false),(1,true),(11,false),(10,false),(3,true),(8,true)],[(4,false),(7,false),(6,true),(0,true),(12,false),(2,true),(9,false)])
                        (.node 1430830 ([(2,true),(10,true),(6,true),(0,true),(13,true),(4,false),(8,true)],[(5,true),(11,true),(12,true),(1,true),(7,true),(3,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1434472 ([(4,true),(13,false),(1,true),(2,true),(10,false),(6,false),(8,true)],[(5,true),(7,false),(3,false),(11,true),(12,true),(0,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1435066 ([(7,true),(0,true),(1,true),(11,false),(4,true),(5,true),(9,false)],[(13,false),(12,false),(2,true),(3,true),(10,false),(6,true),(8,true)])
                      (.node 1434814 ([(3,true),(11,true),(1,false),(13,true),(5,true),(6,true),(9,false)],[(4,false),(10,false),(0,true),(12,false),(2,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1435630 ([(0,true),(1,true),(2,true),(10,true),(5,false),(4,false),(8,true)],[(13,false),(12,false),(11,false),(6,true),(7,true),(3,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1436530 ([(4,true),(13,false),(12,false),(2,false),(10,false),(6,false),(8,true)],[(5,true),(7,false),(3,false),(11,false),(1,false),(0,false),(9,false)])
                    (.node 1436014 ([(6,true),(0,true),(13,true),(4,false),(3,false),(2,false),(8,true)],[(5,true),(7,true),(1,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1435942 ([(4,true),(5,true),(6,true),(0,true),(12,false),(2,false),(9,false)],[(13,false),(1,true),(10,true),(11,true),(3,true),(7,true),(8,true)])
                        (.node 1435930 ([(6,true),(10,false),(2,true),(12,true),(13,true),(4,false),(8,true)],[(5,true),(7,true),(3,false),(11,false),(0,true),(1,true),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1436038 ([(2,true),(3,true),(4,true),(13,false),(0,false),(6,false),(8,true)],[(5,true),(7,false),(1,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1437214 ([(2,true),(3,true),(4,true),(13,false),(0,false),(6,false),(8,true)],[(5,true),(7,false),(1,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1436782 ([(4,true),(5,true),(10,true),(2,true),(12,true),(0,false),(8,true)],[(13,false),(1,true),(11,true),(3,true),(7,true),(6,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1437466 ([(2,true),(3,true),(4,true),(13,false),(0,false),(6,false),(9,false)],[(5,true),(10,true),(11,true),(12,true),(1,true),(7,true),(8,true)])
                        .empty
                        .empty))))))))
        (.node 1555984 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
          (.node 1460914 ([(0,true),(1,true),(2,true),(11,true),(5,false),(4,false),(8,true)],[(13,false),(12,false),(6,true),(7,true),(3,false),(10,false),(9,false)])
            (.node 1447090 ([(1,true),(12,false),(6,false),(5,false),(4,false),(3,false),(8,true)],[(13,false),(2,true),(7,false),(0,false),(11,false),(10,false),(9,false)])
              (.node 1443178 ([(2,true),(10,true),(6,false),(12,true),(13,true),(4,false),(8,true)],[(5,true),(11,false),(0,true),(1,true),(7,true),(3,false),(9,false)])
                (.node 1439182 ([(3,true),(4,true),(5,true),(10,true),(1,false),(0,false),(8,true)],[(13,false),(12,false),(11,false),(2,true),(7,true),(6,false),(9,false)])
                  (.node 1438342 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                    (.node 1438066 ([(0,true),(1,true),(2,true),(11,false),(5,false),(4,false),(9,false)],[(13,false),(12,false),(3,true),(10,true),(6,true),(7,true),(8,true)])
                      (.node 1438054 ([(2,true),(11,false),(6,true),(0,true),(13,true),(4,false),(9,false)],[(5,true),(10,false),(3,false),(12,true),(1,true),(7,true),(8,true)])
                        (.node 1437982 ([(0,true),(1,true),(2,true),(11,false),(5,false),(4,false),(8,true)],[(13,false),(12,false),(3,true),(7,false),(6,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1438324 ([(6,true),(11,true),(4,true),(13,false),(1,true),(2,true),(8,true)],[(5,true),(7,true),(3,true),(12,true),(0,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1438912 ([(6,true),(0,true),(13,true),(4,false),(11,false),(2,true),(8,true)],[(5,true),(7,true),(3,true),(12,true),(1,true),(10,false),(9,false)])
                      (.node 1438390 ([(2,true),(3,true),(4,true),(13,false),(0,false),(6,false),(8,true)],[(5,true),(7,false),(1,false),(12,false),(11,false),(10,false),(9,false)])
                        (.node 1438366 ([(6,true),(0,true),(13,true),(4,false),(3,false),(2,false),(8,true)],[(5,true),(7,true),(1,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1438930 ([(3,true),(4,true),(13,false),(1,true),(10,false),(6,false),(8,true)],[(5,true),(7,false),(2,false),(11,true),(12,true),(0,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1440376 ([(0,true),(1,true),(10,true),(5,false),(4,false),(3,false),(8,true)],[(13,false),(12,false),(11,false),(6,true),(7,true),(2,false),(9,false)])
                    (.node 1439524 ([(2,true),(3,true),(4,true),(13,false),(0,false),(6,false),(9,false)],[(5,true),(10,true),(11,true),(12,true),(1,true),(7,true),(8,true)])
                      (.node 1439272 ([(2,true),(3,true),(4,true),(13,false),(0,false),(6,false),(8,true)],[(5,true),(7,false),(1,false),(12,false),(11,false),(10,false),(9,false)])
                        (.node 1439200 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1440358 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1440418 ([(0,true),(12,false),(4,true),(5,true),(10,false),(2,false),(8,true)],[(13,false),(1,true),(7,false),(6,false),(11,true),(3,false),(9,false)])
                      (.node 1440406 ([(2,true),(3,true),(11,false),(5,false),(13,false),(0,false),(8,true)],[(4,false),(12,true),(1,true),(7,true),(6,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1443166 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                        .empty
                        .empty))))
                (.node 1445926 ([(5,false),(13,false),(12,false),(0,true),(10,false),(3,true),(8,true)],[(4,false),(7,false),(6,true),(11,false),(1,true),(2,true),(9,false)])
                  (.node 1444060 ([(2,true),(3,true),(4,true),(13,false),(12,false),(6,true),(9,false)],[(5,true),(11,false),(10,false),(0,true),(1,true),(7,true),(8,true)])
                    (.node 1443904 ([(0,true),(1,true),(11,true),(5,false),(4,false),(3,false),(8,true)],[(13,false),(12,false),(6,true),(7,true),(2,false),(10,false),(9,false)])
                      (.node 1443886 ([(3,true),(4,true),(5,true),(11,false),(1,false),(0,false),(8,true)],[(13,false),(12,false),(6,true),(7,false),(2,false),(10,false),(9,false)])
                        (.node 1443862 ([(0,true),(13,true),(5,true),(11,false),(2,true),(3,true),(8,true)],[(4,false),(7,false),(6,false),(12,true),(1,true),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1444048 ([(4,true),(5,true),(11,false),(2,false),(1,false),(0,false),(9,false)],[(13,false),(12,false),(6,true),(10,true),(3,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1444492 ([(0,true),(12,false),(5,false),(4,false),(3,false),(2,false),(9,false)],[(13,false),(1,true),(10,true),(11,true),(6,true),(7,true),(8,true)])
                      (.node 1444474 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1444534 ([(0,true),(12,false),(5,false),(4,false),(3,false),(2,false),(8,true)],[(13,false),(1,true),(7,false),(6,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1446754 ([(1,true),(2,true),(11,true),(6,false),(5,false),(4,false),(8,true)],[(13,false),(12,false),(0,true),(7,true),(3,false),(10,false),(9,false)])
                    (.node 1446526 ([(4,true),(5,true),(6,true),(11,false),(2,false),(1,false),(9,false)],[(13,false),(12,false),(0,true),(10,true),(3,true),(7,true),(8,true)])
                      (.node 1446514 ([(6,true),(0,true),(10,true),(2,false),(13,true),(4,false),(8,true)],[(5,true),(7,true),(3,false),(11,true),(12,true),(1,false),(9,false)])
                        (.node 1445968 ([(6,true),(0,true),(1,true),(13,true),(4,false),(3,false),(8,true)],[(5,true),(7,true),(2,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1446736 ([(4,true),(5,true),(6,true),(11,false),(2,false),(1,false),(8,true)],[(13,false),(12,false),(0,true),(7,false),(3,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1446868 ([(3,true),(4,true),(13,false),(1,false),(0,false),(6,false),(8,true)],[(5,true),(7,false),(2,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1446850 ([(6,true),(0,true),(1,true),(13,true),(4,false),(3,false),(8,true)],[(5,true),(7,true),(2,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1447078 ([(3,true),(4,true),(5,true),(6,true),(12,true),(1,false),(8,true)],[(13,false),(2,true),(7,true),(0,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))))
              (.node 1455196 ([(1,true),(12,false),(4,true),(5,true),(6,true),(10,false),(9,false)],[(13,false),(2,true),(3,true),(11,false),(0,true),(7,true),(8,true)])
                (.node 1450036 ([(0,true),(1,true),(2,true),(10,true),(5,false),(4,false),(8,true)],[(13,false),(12,false),(11,false),(6,true),(7,true),(3,false),(9,false)])
                  (.node 1448878 ([(4,true),(13,false),(1,false),(11,false),(10,false),(6,false),(8,true)],[(5,true),(7,false),(3,false),(2,false),(12,false),(0,false),(9,false)])
                    (.node 1447984 ([(5,false),(13,false),(1,false),(0,false),(10,false),(3,true),(8,true)],[(4,false),(7,false),(6,true),(11,true),(12,true),(2,true),(9,false)])
                      (.node 1447678 ([(1,true),(12,false),(6,false),(5,false),(4,false),(3,false),(8,true)],[(13,false),(2,true),(7,false),(0,false),(11,false),(10,false),(9,false)])
                        (.node 1447636 ([(1,true),(12,false),(6,false),(5,false),(4,false),(3,false),(9,false)],[(13,false),(2,true),(10,true),(11,true),(0,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1448026 ([(6,true),(0,true),(1,true),(13,true),(4,false),(3,false),(8,true)],[(5,true),(7,true),(2,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1449220 ([(3,true),(4,true),(13,false),(1,false),(0,false),(6,false),(8,true)],[(5,true),(7,false),(2,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1449130 ([(4,true),(5,true),(10,true),(2,false),(1,false),(0,false),(8,true)],[(13,false),(12,false),(11,false),(3,true),(7,true),(6,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1449472 ([(3,true),(4,true),(13,false),(1,false),(0,false),(6,false),(9,false)],[(5,true),(10,true),(11,true),(12,true),(2,true),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1454020 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                    (.node 1453246 ([(4,true),(13,false),(2,true),(11,false),(0,false),(6,false),(9,false)],[(5,true),(10,true),(1,true),(12,false),(3,true),(7,true),(8,true)])
                      (.node 1452994 ([(4,true),(13,false),(2,true),(11,false),(0,false),(6,false),(8,true)],[(5,true),(7,false),(3,false),(12,true),(1,false),(10,false),(9,false)])
                        (.node 1450078 ([(7,true),(2,false),(1,false),(11,false),(5,false),(4,false),(9,false)],[(13,false),(12,false),(0,false),(6,false),(10,false),(3,false),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1453990 ([(5,false),(4,false),(3,false),(2,false),(1,false),(0,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,false),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1454716 ([(4,true),(5,true),(11,true),(2,false),(1,false),(0,false),(8,true)],[(13,false),(12,false),(3,true),(7,true),(6,false),(10,false),(9,false)])
                      (.node 1454674 ([(3,false),(2,false),(13,true),(5,true),(6,true),(0,true),(8,true)],[(4,false),(7,true),(1,true),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1455166 ([(6,true),(10,false),(3,true),(4,true),(13,false),(1,false),(8,true)],[(5,true),(7,true),(0,false),(11,true),(12,true),(2,true),(9,false)])
                        .empty
                        .empty))))
                (.node 1459984 ([(1,true),(2,true),(10,true),(6,false),(5,false),(4,false),(8,true)],[(13,false),(12,false),(11,false),(0,true),(7,true),(3,false),(9,false)])
                  (.node 1456078 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                    (.node 1455664 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                      (.node 1455646 ([(3,true),(4,true),(13,false),(1,false),(0,false),(6,false),(9,false)],[(5,true),(10,true),(11,true),(12,true),(2,true),(7,true),(8,true)])
                        (.node 1455394 ([(3,true),(4,true),(13,false),(1,false),(0,false),(6,false),(8,true)],[(5,true),(7,false),(2,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1456048 ([(5,false),(4,false),(3,false),(2,false),(1,false),(0,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,false),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1457116 ([(3,true),(4,true),(13,false),(1,false),(10,true),(6,true),(8,true)],[(5,true),(11,true),(12,true),(2,true),(7,true),(0,true),(9,false)])
                      (.node 1457074 ([(2,false),(12,false),(4,true),(5,true),(6,true),(0,true),(8,true)],[(13,false),(1,false),(7,false),(3,true),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1457134 ([(0,true),(1,true),(13,true),(5,true),(11,true),(3,false),(8,true)],[(4,false),(12,true),(2,true),(7,false),(6,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1460368 ([(0,true),(1,true),(12,false),(5,false),(4,false),(3,false),(8,true)],[(13,false),(2,true),(7,false),(6,false),(11,false),(10,false),(9,false)])
                    (.node 1460326 ([(0,true),(1,true),(12,false),(5,false),(4,false),(3,false),(9,false)],[(13,false),(2,true),(10,true),(11,true),(6,true),(7,true),(8,true)])
                      (.node 1460302 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                        (.node 1460026 ([(0,false),(6,false),(5,false),(13,false),(2,true),(3,true),(9,false)],[(4,false),(10,true),(11,true),(12,true),(1,false),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1460350 ([(3,true),(4,true),(5,true),(12,true),(1,false),(0,false),(8,true)],[(13,false),(2,true),(7,true),(6,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1460866 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                      (.node 1460848 ([(4,true),(5,true),(6,true),(10,true),(2,false),(1,false),(8,true)],[(13,false),(12,false),(11,false),(3,true),(7,true),(0,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1460890 ([(4,true),(5,true),(11,false),(2,false),(1,false),(0,false),(8,true)],[(13,false),(12,false),(6,true),(7,false),(3,false),(10,false),(9,false)])
                        .empty
                        .empty))))))
            (.node 1473922 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
              (.node 1466278 ([(2,true),(13,true),(4,false),(11,true),(0,false),(6,false),(9,false)],[(5,true),(10,true),(3,false),(12,false),(1,true),(7,true),(8,true)])
                (.node 1463674 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                  (.node 1463104 ([(6,true),(12,true),(13,true),(4,false),(10,true),(1,false),(8,true)],[(5,true),(7,true),(0,false),(11,false),(2,true),(3,true),(9,false)])
                    (.node 1461232 ([(3,true),(4,true),(5,true),(12,true),(1,false),(0,false),(8,true)],[(13,false),(2,true),(7,true),(6,false),(11,false),(10,false),(9,false)])
                      (.node 1461202 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                        (.node 1461190 ([(3,true),(10,false),(6,false),(5,false),(13,false),(1,false),(8,true)],[(4,false),(11,true),(12,true),(2,true),(7,true),(0,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1461250 ([(0,true),(1,true),(12,false),(5,false),(4,false),(3,false),(8,true)],[(13,false),(2,true),(7,false),(6,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1463218 ([(1,true),(2,true),(12,false),(6,false),(5,false),(4,false),(8,true)],[(13,false),(3,true),(7,false),(0,false),(11,false),(10,false),(9,false)])
                      (.node 1463200 ([(4,true),(5,true),(6,true),(12,true),(2,false),(1,false),(8,true)],[(13,false),(3,true),(7,true),(0,false),(11,false),(10,false),(9,false)])
                        (.node 1463134 ([(1,true),(2,true),(12,false),(6,false),(5,false),(4,false),(9,false)],[(13,false),(3,true),(10,true),(11,true),(0,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1463650 ([(6,true),(12,true),(13,true),(4,false),(10,false),(1,true),(8,true)],[(5,true),(7,true),(2,true),(3,true),(11,true),(0,true),(9,false)])
                        .empty
                        .empty)))
                  (.node 1465342 ([(4,true),(13,false),(2,false),(1,false),(0,false),(6,false),(8,true)],[(5,true),(7,false),(3,false),(12,false),(11,false),(10,false),(9,false)])
                    (.node 1464334 ([(3,false),(13,true),(5,true),(6,true),(0,true),(1,true),(8,true)],[(4,false),(7,true),(2,true),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1463722 ([(1,true),(2,true),(13,true),(4,false),(11,true),(6,false),(8,true)],[(5,true),(7,false),(0,false),(12,true),(3,true),(10,false),(9,false)])
                        (.node 1463692 ([(6,true),(11,false),(4,true),(13,false),(2,false),(1,false),(8,true)],[(5,true),(7,true),(0,false),(12,true),(3,true),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1464376 ([(4,true),(5,true),(6,true),(12,true),(2,false),(1,false),(8,true)],[(13,false),(3,true),(7,true),(0,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1466002 ([(6,true),(0,true),(11,false),(4,true),(13,false),(2,false),(8,true)],[(5,true),(7,true),(1,false),(12,true),(3,true),(10,false),(9,false)])
                      (.node 1465594 ([(4,true),(13,false),(2,false),(1,false),(0,false),(6,false),(9,false)],[(5,true),(10,true),(11,true),(12,true),(3,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1466026 ([(2,true),(12,false),(0,false),(10,true),(4,true),(5,true),(8,true)],[(13,false),(3,true),(11,true),(1,true),(7,true),(6,true),(9,false)])
                        .empty
                        .empty))))
                (.node 1468426 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                  (.node 1466878 ([(0,true),(1,true),(2,true),(13,true),(5,true),(10,false),(9,false)],[(4,false),(3,false),(12,false),(11,false),(6,true),(7,true),(8,true)])
                    (.node 1466794 ([(0,true),(1,true),(10,true),(5,false),(13,false),(3,true),(8,true)],[(4,false),(7,false),(6,false),(11,true),(12,true),(2,false),(9,false)])
                      (.node 1466770 ([(4,true),(5,true),(10,false),(2,true),(12,false),(0,false),(8,true)],[(13,false),(3,true),(7,true),(6,false),(11,true),(1,true),(9,false)])
                        (.node 1466290 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1466866 ([(2,true),(3,true),(4,true),(5,true),(11,true),(0,false),(8,true)],[(13,false),(12,false),(1,true),(7,true),(6,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1467652 ([(4,true),(13,false),(2,false),(1,false),(0,false),(6,false),(9,false)],[(5,true),(10,true),(11,true),(12,true),(3,true),(7,true),(8,true)])
                      (.node 1467400 ([(4,true),(13,false),(2,false),(1,false),(0,false),(6,false),(8,true)],[(5,true),(7,false),(3,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1468396 ([(5,false),(4,false),(3,false),(2,false),(1,false),(0,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,false),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1472200 ([(7,true),(5,false),(13,false),(3,true),(11,false),(0,false),(9,false)],[(4,false),(12,true),(2,false),(1,false),(10,false),(6,false),(8,true)])
                    (.node 1471882 ([(5,false),(13,false),(3,true),(11,false),(0,true),(1,true),(8,true)],[(4,false),(12,true),(2,false),(7,false),(6,true),(10,false),(9,false)])
                      (.node 1469122 ([(4,true),(13,false),(2,false),(1,false),(10,true),(6,true),(8,true)],[(5,true),(11,true),(12,true),(3,true),(7,true),(0,true),(9,false)])
                        (.node 1469080 ([(7,true),(1,true),(2,true),(13,true),(5,true),(6,true),(9,false)],[(4,false),(3,false),(12,false),(11,false),(10,false),(0,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1471924 ([(5,false),(4,false),(3,false),(2,false),(10,true),(0,true),(8,true)],[(13,false),(12,false),(11,false),(6,false),(7,true),(1,true),(9,false)])
                        .empty
                        .empty))
                    (.node 1472512 ([(5,false),(4,false),(3,false),(2,false),(1,false),(0,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(6,false),(7,true),(8,true)])
                      (.node 1472452 ([(2,true),(3,true),(4,true),(5,true),(10,true),(0,false),(8,true)],[(13,false),(12,false),(11,false),(1,true),(7,true),(6,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1472542 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                        .empty
                        .empty)))))
              (.node 1548136 ([(1,false),(0,false),(6,false),(5,false),(4,false),(3,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,false),(7,true),(8,true)])
                (.node 1478038 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                  (.node 1477168 ([(0,true),(1,true),(2,true),(12,false),(5,false),(4,false),(9,false)],[(13,false),(3,true),(10,true),(11,true),(6,true),(7,true),(8,true)])
                    (.node 1476724 ([(4,true),(13,false),(12,false),(6,true),(0,true),(1,true),(9,false)],[(5,true),(11,false),(10,false),(2,true),(3,true),(7,true),(8,true)])
                      (.node 1476682 ([(3,false),(13,true),(5,true),(6,true),(0,true),(1,true),(8,true)],[(4,false),(7,true),(2,true),(12,false),(11,false),(10,false),(9,false)])
                        (.node 1473934 ([(0,true),(10,true),(5,false),(4,false),(3,false),(2,false),(8,true)],[(13,false),(12,false),(11,false),(6,true),(7,true),(1,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1477156 ([(2,true),(3,true),(4,true),(5,true),(11,false),(0,false),(8,true)],[(13,false),(12,false),(6,true),(7,false),(1,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1477330 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                      (.node 1477312 ([(4,true),(5,true),(12,true),(2,false),(10,false),(0,true),(8,true)],[(13,false),(3,true),(7,true),(1,true),(11,true),(6,true),(9,false)])
                        .empty
                        .empty)
                      (.node 1477354 ([(4,true),(5,true),(12,true),(2,false),(1,false),(0,false),(8,true)],[(13,false),(3,true),(7,true),(6,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1547548 ([(2,true),(11,true),(0,true),(13,true),(5,false),(4,false),(8,true)],[(6,true),(12,true),(1,true),(7,true),(3,false),(10,false),(9,false)])
                    (.node 1547164 ([(3,true),(10,true),(1,false),(0,false),(6,false),(5,false),(8,true)],[(13,false),(12,false),(11,false),(2,true),(7,true),(4,false),(9,false)])
                      (.node 1547152 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                        (.node 1478050 ([(0,true),(10,true),(4,true),(5,true),(12,true),(2,false),(8,true)],[(13,false),(3,true),(11,true),(6,true),(7,true),(1,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1547506 ([(7,true),(5,true),(13,false),(0,false),(11,false),(3,true),(9,false)],[(6,true),(12,true),(1,true),(2,true),(10,false),(4,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1547782 ([(5,true),(13,false),(0,false),(11,false),(3,false),(2,false),(8,true)],[(6,true),(12,true),(1,true),(7,false),(4,false),(10,false),(9,false)])
                      (.node 1547740 ([(5,true),(6,true),(0,true),(1,true),(10,true),(3,false),(8,true)],[(13,false),(12,false),(11,false),(4,true),(7,true),(2,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1548124 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                        .empty
                        .empty))))
                (.node 1553710 ([(4,true),(5,true),(6,true),(0,true),(12,false),(2,false),(8,true)],[(13,false),(1,true),(7,false),(3,false),(11,false),(10,false),(9,false)])
                  (.node 1552936 ([(6,false),(13,false),(1,true),(2,true),(10,true),(4,false),(8,true)],[(5,false),(11,true),(12,true),(0,false),(7,true),(3,false),(9,false)])
                    (.node 1552306 ([(6,false),(13,false),(1,true),(2,true),(3,true),(4,true),(8,true)],[(5,false),(7,false),(0,true),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1551280 ([(3,true),(10,true),(11,true),(1,false),(13,true),(5,false),(8,true)],[(6,true),(0,true),(12,false),(2,true),(7,true),(4,false),(9,false)])
                        (.node 1551268 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1552348 ([(6,false),(13,false),(1,true),(2,true),(3,true),(4,true),(9,false)],[(5,false),(10,true),(11,true),(12,true),(0,false),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1553662 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                      (.node 1552978 ([(7,true),(2,false),(1,false),(13,true),(5,false),(4,false),(9,false)],[(6,true),(0,true),(12,false),(11,false),(10,false),(3,false),(8,true)])
                        .empty
                        .empty)
                      (.node 1553680 ([(2,true),(3,true),(10,true),(0,true),(13,true),(5,false),(8,true)],[(6,true),(11,true),(12,true),(1,true),(7,true),(4,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1555192 ([(2,true),(3,true),(4,true),(5,true),(13,false),(0,false),(9,false)],[(6,true),(10,true),(11,true),(12,true),(1,true),(7,true),(8,true)])
                    (.node 1554406 ([(6,false),(13,false),(1,true),(2,true),(3,true),(4,true),(9,false)],[(5,false),(10,true),(11,true),(12,true),(0,false),(7,true),(8,true)])
                      (.node 1554364 ([(6,false),(13,false),(1,true),(2,true),(3,true),(4,true),(8,true)],[(5,false),(7,false),(0,true),(12,false),(11,false),(10,false),(9,false)])
                        (.node 1553722 ([(2,true),(12,true),(0,false),(6,false),(5,false),(4,false),(8,true)],[(13,false),(1,true),(7,true),(3,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1555180 ([(4,true),(5,true),(6,true),(0,true),(12,false),(2,false),(8,true)],[(13,false),(1,true),(7,false),(3,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1555288 ([(0,true),(13,true),(5,false),(10,false),(2,true),(3,true),(8,true)],[(6,true),(7,true),(4,true),(11,true),(12,true),(1,true),(9,false)])
                      (.node 1555264 ([(4,true),(5,true),(6,true),(0,true),(12,false),(2,false),(9,false)],[(13,false),(1,true),(10,true),(11,true),(3,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1555972 ([(5,true),(6,true),(0,true),(12,false),(3,false),(2,false),(9,false)],[(13,false),(1,true),(10,true),(11,true),(4,true),(7,true),(8,true)])
                        .empty
                        .empty)))))))
          (.node 1580818 ([(1,true),(2,true),(12,false),(6,false),(5,false),(4,false),(8,true)],[(13,false),(3,true),(7,false),(0,false),(11,false),(10,false),(9,false)])
            (.node 1570870 ([(0,true),(11,true),(2,false),(13,true),(5,false),(4,false),(8,true)],[(6,true),(7,true),(3,false),(12,true),(1,false),(10,false),(9,false)])
              (.node 1563628 ([(3,true),(10,true),(0,false),(12,true),(13,true),(5,false),(8,true)],[(6,true),(11,false),(1,true),(2,true),(7,true),(4,false),(9,false)])
                (.node 1558426 ([(2,true),(10,true),(6,false),(13,false),(12,false),(4,false),(8,true)],[(5,false),(11,false),(0,true),(1,true),(7,true),(3,false),(9,false)])
                  (.node 1556782 ([(3,true),(11,false),(1,false),(0,false),(6,false),(5,false),(9,false)],[(13,false),(12,false),(4,true),(10,true),(2,true),(7,true),(8,true)])
                    (.node 1556560 ([(5,true),(6,true),(0,true),(1,true),(11,true),(3,false),(8,true)],[(13,false),(12,false),(4,true),(7,true),(2,false),(10,false),(9,false)])
                      (.node 1556032 ([(2,true),(3,true),(12,true),(0,false),(6,false),(5,false),(8,true)],[(13,false),(1,true),(7,true),(4,false),(11,false),(10,false),(9,false)])
                        (.node 1556014 ([(5,true),(6,true),(0,true),(12,false),(3,false),(2,false),(8,true)],[(13,false),(1,true),(7,false),(4,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1556572 ([(3,true),(4,true),(5,true),(13,false),(1,true),(10,false),(9,false)],[(6,true),(0,true),(12,false),(11,false),(2,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1557724 ([(0,true),(13,true),(5,false),(4,false),(3,false),(2,false),(8,true)],[(6,true),(7,true),(1,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1557682 ([(6,false),(5,false),(4,false),(12,true),(1,true),(2,true),(8,true)],[(13,false),(0,false),(7,true),(3,true),(11,false),(10,false),(9,false)])
                        (.node 1556800 ([(0,true),(13,true),(5,false),(4,false),(11,false),(2,true),(8,true)],[(6,true),(7,true),(3,true),(12,true),(1,true),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1558414 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1559308 ([(2,true),(3,true),(4,true),(5,true),(13,false),(0,false),(9,false)],[(6,true),(10,true),(11,true),(12,true),(1,true),(7,true),(8,true)])
                    (.node 1559152 ([(0,true),(13,true),(5,false),(11,false),(10,false),(3,false),(8,true)],[(6,true),(7,true),(2,false),(1,false),(12,false),(4,false),(9,false)])
                      (.node 1559134 ([(3,true),(4,true),(11,false),(1,false),(13,true),(6,true),(8,true)],[(5,false),(12,true),(0,false),(7,false),(2,false),(10,false),(9,false)])
                        (.node 1559110 ([(0,true),(13,true),(5,false),(11,false),(2,true),(3,true),(8,true)],[(6,true),(7,true),(4,true),(12,true),(1,true),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1559296 ([(4,true),(5,true),(13,false),(1,true),(2,true),(10,false),(9,false)],[(6,true),(0,true),(12,false),(11,false),(3,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1559782 ([(0,true),(13,true),(5,false),(4,false),(3,false),(2,false),(8,true)],[(6,true),(7,true),(1,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1559740 ([(0,true),(13,true),(5,false),(4,false),(10,false),(2,true),(8,true)],[(6,true),(7,true),(3,true),(11,true),(12,true),(1,true),(9,false)])
                        .empty
                        .empty)
                      (.node 1563616 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                        .empty
                        .empty))))
                (.node 1565674 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                  (.node 1564510 ([(3,true),(4,true),(5,true),(13,false),(12,false),(0,true),(9,false)],[(6,true),(11,false),(10,false),(1,true),(2,true),(7,true),(8,true)])
                    (.node 1564354 ([(1,true),(2,true),(11,true),(6,false),(5,false),(4,false),(8,true)],[(13,false),(12,false),(0,true),(7,true),(3,false),(10,false),(9,false)])
                      (.node 1564336 ([(4,true),(5,true),(6,true),(11,false),(2,false),(1,false),(8,true)],[(13,false),(12,false),(0,true),(7,false),(3,false),(10,false),(9,false)])
                        (.node 1564312 ([(1,true),(13,true),(6,true),(11,false),(3,true),(4,true),(8,true)],[(5,false),(7,false),(0,false),(12,true),(2,true),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1564498 ([(5,true),(6,true),(11,false),(3,false),(2,false),(1,false),(9,false)],[(13,false),(12,false),(0,true),(10,true),(4,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1564942 ([(1,true),(12,false),(6,false),(5,false),(4,false),(3,false),(9,false)],[(13,false),(2,true),(10,true),(11,true),(0,true),(7,true),(8,true)])
                      (.node 1564924 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1564984 ([(1,true),(12,false),(6,false),(5,false),(4,false),(3,false),(8,true)],[(13,false),(2,true),(7,false),(0,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1567384 ([(0,true),(1,true),(13,true),(5,false),(4,false),(3,false),(8,true)],[(6,true),(7,true),(2,false),(12,false),(11,false),(10,false),(9,false)])
                    (.node 1566754 ([(6,false),(13,false),(1,false),(11,false),(3,true),(4,true),(9,false)],[(5,false),(10,true),(2,false),(12,false),(0,false),(7,true),(8,true)])
                      (.node 1566712 ([(6,false),(13,false),(1,false),(11,false),(3,true),(4,true),(8,true)],[(5,false),(7,false),(0,true),(12,true),(2,true),(10,false),(9,false)])
                        (.node 1565686 ([(3,true),(10,true),(0,true),(1,true),(13,true),(5,false),(8,true)],[(6,true),(11,true),(12,true),(2,true),(7,true),(4,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1567342 ([(0,true),(1,true),(13,true),(5,false),(10,false),(3,true),(8,true)],[(6,true),(7,true),(4,true),(11,true),(12,true),(2,true),(9,false)])
                        .empty
                        .empty))
                    (.node 1570528 ([(1,true),(2,true),(11,false),(6,false),(5,false),(4,false),(8,true)],[(13,false),(12,false),(3,true),(7,false),(0,false),(10,false),(9,false)])
                      (.node 1570486 ([(1,true),(2,true),(3,true),(10,true),(6,false),(5,false),(8,true)],[(13,false),(12,false),(11,false),(0,true),(7,true),(4,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1570828 ([(6,false),(13,false),(2,true),(11,false),(10,false),(4,true),(8,true)],[(5,false),(7,false),(0,true),(1,true),(12,false),(3,true),(9,false)])
                        .empty
                        .empty)))))
              (.node 1575232 ([(1,true),(2,true),(10,true),(6,false),(5,false),(4,false),(8,true)],[(13,false),(12,false),(11,false),(0,true),(7,true),(3,false),(9,false)])
                (.node 1573150 ([(5,true),(6,true),(0,true),(1,true),(12,false),(3,false),(9,false)],[(13,false),(2,true),(10,true),(11,true),(4,true),(7,true),(8,true)])
                  (.node 1572814 ([(5,true),(6,true),(0,true),(1,true),(12,false),(3,false),(9,false)],[(13,false),(2,true),(10,true),(11,true),(4,true),(7,true),(8,true)])
                    (.node 1571980 ([(7,true),(1,true),(2,true),(11,false),(5,true),(6,true),(9,false)],[(13,false),(12,false),(3,true),(4,true),(10,false),(0,true),(8,true)])
                      (.node 1571680 ([(5,true),(13,false),(2,true),(3,true),(10,false),(0,false),(8,true)],[(6,true),(7,false),(4,false),(11,true),(12,true),(1,false),(9,false)])
                        (.node 1571638 ([(5,true),(6,true),(10,true),(3,false),(2,false),(1,false),(8,true)],[(13,false),(12,false),(11,false),(4,true),(7,true),(0,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1572022 ([(4,true),(11,true),(2,false),(13,true),(6,true),(0,true),(9,false)],[(5,false),(10,false),(1,true),(12,false),(3,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1572910 ([(3,true),(11,false),(0,true),(1,true),(13,true),(5,false),(9,false)],[(6,true),(10,false),(4,false),(12,true),(2,true),(7,true),(8,true)])
                      (.node 1572838 ([(1,true),(2,true),(3,true),(11,false),(6,false),(5,false),(8,true)],[(13,false),(12,false),(4,true),(7,false),(0,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1572922 ([(1,true),(2,true),(3,true),(11,false),(6,false),(5,false),(9,false)],[(13,false),(12,false),(4,true),(10,true),(0,true),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1573738 ([(5,true),(13,false),(12,false),(3,false),(10,false),(0,false),(8,true)],[(6,true),(7,false),(4,false),(11,false),(2,false),(1,false),(9,false)])
                    (.node 1573264 ([(0,true),(1,true),(13,true),(5,false),(4,false),(3,false),(8,true)],[(6,true),(7,true),(2,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1573246 ([(3,true),(4,true),(5,true),(13,false),(1,false),(0,false),(8,true)],[(6,true),(7,false),(2,false),(12,false),(11,false),(10,false),(9,false)])
                        (.node 1573180 ([(0,true),(10,false),(3,true),(12,true),(13,true),(5,false),(8,true)],[(6,true),(7,true),(4,false),(11,false),(1,true),(2,true),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1573696 ([(5,true),(6,true),(10,true),(3,true),(12,true),(1,false),(8,true)],[(13,false),(2,true),(11,true),(4,true),(7,true),(0,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1574422 ([(3,true),(4,true),(5,true),(13,false),(1,false),(0,false),(8,true)],[(6,true),(7,false),(2,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1574380 ([(3,true),(4,true),(5,true),(13,false),(1,false),(0,false),(9,false)],[(6,true),(10,true),(11,true),(12,true),(2,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1575214 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                        .empty
                        .empty))))
                (.node 1576138 ([(4,true),(5,true),(13,false),(2,true),(10,false),(0,false),(8,true)],[(6,true),(7,false),(3,false),(11,true),(12,true),(1,false),(9,false)])
                  (.node 1575598 ([(3,true),(4,true),(5,true),(13,false),(1,false),(0,false),(8,true)],[(6,true),(7,false),(2,false),(12,false),(11,false),(10,false),(9,false)])
                    (.node 1575550 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(3,true),(7,true),(8,true)])
                      (.node 1575274 ([(1,true),(12,false),(5,true),(6,true),(10,false),(3,false),(8,true)],[(13,false),(2,true),(7,false),(0,false),(11,true),(4,false),(9,false)])
                        (.node 1575262 ([(3,true),(4,true),(11,false),(6,false),(13,false),(1,false),(8,true)],[(5,false),(12,true),(2,true),(7,true),(0,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1575574 ([(0,true),(11,true),(5,true),(13,false),(2,true),(3,true),(8,true)],[(6,true),(7,true),(4,true),(12,true),(1,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1576096 ([(4,true),(5,true),(6,true),(10,true),(2,false),(1,false),(8,true)],[(13,false),(12,false),(11,false),(3,true),(7,true),(0,false),(9,false)])
                      (.node 1575616 ([(0,true),(1,true),(13,true),(5,false),(4,false),(3,false),(8,true)],[(6,true),(7,true),(2,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1576114 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1580476 ([(1,false),(0,false),(6,false),(13,false),(3,true),(4,true),(9,false)],[(5,false),(10,true),(11,true),(12,true),(2,false),(7,true),(8,true)])
                    (.node 1576480 ([(3,true),(4,true),(5,true),(13,false),(1,false),(0,false),(8,true)],[(6,true),(7,false),(2,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1576438 ([(3,true),(4,true),(5,true),(13,false),(1,false),(0,false),(9,false)],[(6,true),(10,true),(11,true),(12,true),(2,true),(7,true),(8,true)])
                        (.node 1576162 ([(0,true),(1,true),(13,true),(5,false),(11,false),(3,true),(8,true)],[(6,true),(7,true),(4,true),(12,true),(2,true),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1580434 ([(2,true),(3,true),(10,true),(0,false),(6,false),(5,false),(8,true)],[(13,false),(12,false),(11,false),(1,true),(7,true),(4,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1580776 ([(1,true),(2,true),(12,false),(6,false),(5,false),(4,false),(9,false)],[(13,false),(3,true),(10,true),(11,true),(0,true),(7,true),(8,true)])
                      (.node 1580752 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(4,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1580800 ([(4,true),(5,true),(6,true),(12,true),(2,false),(1,false),(8,true)],[(13,false),(3,true),(7,true),(0,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))))))
            (.node 1591972 ([(4,true),(5,true),(13,false),(2,false),(10,true),(0,true),(8,true)],[(6,true),(11,true),(12,true),(3,true),(7,true),(1,true),(9,false)])
              (.node 1584004 ([(2,true),(12,false),(0,false),(6,false),(5,false),(4,false),(8,true)],[(13,false),(3,true),(7,false),(1,false),(11,false),(10,false),(9,false)])
                (.node 1582492 ([(2,true),(12,false),(0,false),(6,false),(5,false),(4,false),(9,false)],[(13,false),(3,true),(10,true),(11,true),(1,true),(7,true),(8,true)])
                  (.node 1581640 ([(4,true),(10,false),(0,false),(6,false),(13,false),(2,false),(8,true)],[(5,false),(11,true),(12,true),(3,true),(7,true),(1,false),(9,false)])
                    (.node 1581340 ([(5,true),(6,true),(11,false),(3,false),(2,false),(1,false),(8,true)],[(13,false),(12,false),(0,true),(7,false),(4,false),(10,false),(9,false)])
                      (.node 1581316 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                        (.node 1581298 ([(5,true),(6,true),(0,true),(10,true),(3,false),(2,false),(8,true)],[(13,false),(12,false),(11,false),(4,true),(7,true),(1,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1581364 ([(1,true),(2,true),(3,true),(11,true),(6,false),(5,false),(8,true)],[(13,false),(12,false),(0,true),(7,true),(4,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1581682 ([(4,true),(5,true),(6,true),(12,true),(2,false),(1,false),(8,true)],[(13,false),(3,true),(7,true),(0,false),(11,false),(10,false),(9,false)])
                      (.node 1581652 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1581700 ([(1,true),(2,true),(12,false),(6,false),(5,false),(4,false),(8,true)],[(13,false),(3,true),(7,false),(0,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1583668 ([(2,true),(3,true),(11,true),(0,false),(6,false),(5,false),(8,true)],[(13,false),(12,false),(1,true),(7,true),(4,false),(10,false),(9,false)])
                    (.node 1583218 ([(0,true),(1,true),(2,true),(13,true),(5,false),(4,false),(8,true)],[(6,true),(7,true),(3,false),(12,false),(11,false),(10,false),(9,false)])
                      (.node 1583176 ([(6,false),(13,false),(12,false),(1,true),(10,false),(4,true),(8,true)],[(5,false),(7,false),(0,true),(11,false),(2,true),(3,true),(9,false)])
                        (.node 1582534 ([(2,true),(12,false),(0,false),(6,false),(5,false),(4,false),(8,true)],[(13,false),(3,true),(7,false),(1,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1583650 ([(5,true),(6,true),(0,true),(11,false),(3,false),(2,false),(8,true)],[(13,false),(12,false),(1,true),(7,false),(4,false),(10,false),(9,false)])
                        .empty
                        .empty))
                    (.node 1583764 ([(0,true),(1,true),(10,true),(3,false),(13,true),(5,false),(8,true)],[(6,true),(7,true),(4,false),(11,true),(12,true),(2,false),(9,false)])
                      (.node 1583734 ([(5,true),(6,true),(0,true),(11,false),(3,false),(2,false),(9,false)],[(13,false),(12,false),(1,true),(10,true),(4,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1583992 ([(4,true),(5,true),(6,true),(0,true),(12,true),(2,false),(8,true)],[(13,false),(3,true),(7,true),(1,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty))))
                (.node 1586386 ([(4,true),(5,true),(13,false),(2,false),(1,false),(0,false),(9,false)],[(6,true),(10,true),(11,true),(12,true),(3,true),(7,true),(8,true)])
                  (.node 1585234 ([(6,false),(13,false),(2,false),(1,false),(10,false),(4,true),(8,true)],[(5,false),(7,false),(0,true),(11,true),(12,true),(3,true),(9,false)])
                    (.node 1584892 ([(1,true),(2,true),(3,true),(10,true),(6,false),(5,false),(8,true)],[(13,false),(12,false),(11,false),(0,true),(7,true),(4,false),(9,false)])
                      (.node 1584100 ([(0,true),(1,true),(2,true),(13,true),(5,false),(4,false),(8,true)],[(6,true),(7,true),(3,false),(12,false),(11,false),(10,false),(9,false)])
                        (.node 1584076 ([(4,true),(5,true),(13,false),(2,false),(1,false),(0,false),(8,true)],[(6,true),(7,false),(3,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1584934 ([(7,true),(3,false),(2,false),(11,false),(6,false),(5,false),(9,false)],[(13,false),(12,false),(1,false),(0,false),(10,false),(4,false),(8,true)])
                        .empty
                        .empty))
                    (.node 1586044 ([(5,true),(6,true),(10,true),(3,false),(2,false),(1,false),(8,true)],[(13,false),(12,false),(11,false),(4,true),(7,true),(0,false),(9,false)])
                      (.node 1585276 ([(0,true),(1,true),(2,true),(13,true),(5,false),(4,false),(8,true)],[(6,true),(7,true),(3,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1586086 ([(5,true),(13,false),(2,false),(11,false),(10,false),(0,false),(8,true)],[(6,true),(7,false),(4,false),(3,false),(12,false),(1,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1590202 ([(5,true),(13,false),(3,true),(11,false),(1,false),(0,false),(8,true)],[(6,true),(7,false),(4,false),(12,true),(2,false),(10,false),(9,false)])
                    (.node 1589572 ([(5,true),(6,true),(11,true),(3,false),(2,false),(1,false),(8,true)],[(13,false),(12,false),(4,true),(7,true),(0,false),(10,false),(9,false)])
                      (.node 1589530 ([(4,false),(3,false),(13,true),(6,true),(0,true),(1,true),(8,true)],[(5,false),(7,true),(2,true),(12,false),(11,false),(10,false),(9,false)])
                        (.node 1586428 ([(4,true),(5,true),(13,false),(2,false),(1,false),(0,false),(8,true)],[(6,true),(7,false),(3,false),(12,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1590160 ([(5,true),(13,false),(3,true),(11,false),(1,false),(0,false),(9,false)],[(6,true),(10,true),(2,true),(12,false),(4,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1591240 ([(6,false),(5,false),(4,false),(3,false),(2,false),(1,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,false),(7,true),(8,true)])
                      (.node 1591228 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1591930 ([(3,false),(12,false),(5,true),(6,true),(0,true),(1,true),(8,true)],[(13,false),(2,false),(7,false),(4,true),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)))))
              (.node 1599190 ([(4,false),(13,true),(6,true),(0,true),(1,true),(2,true),(8,true)],[(5,false),(7,true),(3,true),(12,false),(11,false),(10,false),(9,false)])
                (.node 1597132 ([(4,false),(13,true),(6,true),(0,true),(1,true),(2,true),(8,true)],[(5,false),(7,true),(3,true),(12,false),(11,false),(10,false),(9,false)])
                  (.node 1592578 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                    (.node 1592416 ([(0,true),(10,false),(4,true),(5,true),(13,false),(2,false),(8,true)],[(6,true),(7,true),(1,false),(11,true),(12,true),(3,true),(9,false)])
                      (.node 1592404 ([(2,true),(12,false),(5,true),(6,true),(0,true),(10,false),(9,false)],[(13,false),(3,true),(4,true),(11,false),(1,true),(7,true),(8,true)])
                        (.node 1591990 ([(1,true),(2,true),(13,true),(6,true),(11,true),(4,false),(8,true)],[(5,false),(12,true),(3,true),(7,false),(0,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1592560 ([(4,true),(5,true),(13,false),(2,false),(1,false),(0,false),(9,false)],[(6,true),(10,true),(11,true),(12,true),(3,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1593286 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                      (.node 1592602 ([(4,true),(5,true),(13,false),(2,false),(1,false),(0,false),(8,true)],[(6,true),(7,false),(3,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1593298 ([(6,false),(5,false),(4,false),(3,false),(2,false),(1,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,false),(7,true),(8,true)])
                        .empty
                        .empty)))
                  (.node 1597780 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                    (.node 1597618 ([(1,true),(2,true),(3,true),(12,false),(6,false),(5,false),(9,false)],[(13,false),(4,true),(10,true),(11,true),(0,true),(7,true),(8,true)])
                      (.node 1597606 ([(3,true),(4,true),(5,true),(6,true),(11,false),(1,false),(8,true)],[(13,false),(12,false),(0,true),(7,false),(2,false),(10,false),(9,false)])
                        (.node 1597174 ([(5,true),(13,false),(12,false),(0,true),(1,true),(2,true),(9,false)],[(6,true),(11,false),(10,false),(3,true),(4,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1597762 ([(5,true),(6,true),(12,true),(3,false),(10,false),(1,true),(8,true)],[(13,false),(4,true),(7,true),(2,true),(11,true),(0,true),(9,false)])
                        .empty
                        .empty))
                    (.node 1598488 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                      (.node 1597804 ([(5,true),(6,true),(12,true),(3,false),(2,false),(1,false),(8,true)],[(13,false),(4,true),(7,true),(0,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1598500 ([(1,true),(10,true),(5,true),(6,true),(12,true),(3,false),(8,true)],[(13,false),(4,true),(11,true),(0,true),(7,true),(2,false),(9,false)])
                        .empty
                        .empty))))
                (.node 1600942 ([(0,true),(11,false),(5,true),(13,false),(3,false),(2,false),(8,true)],[(6,true),(7,true),(1,false),(12,true),(4,true),(10,false),(9,false)])
                  (.node 1600354 ([(0,true),(12,true),(13,true),(5,false),(10,true),(2,false),(8,true)],[(6,true),(7,true),(1,false),(11,false),(3,true),(4,true),(9,false)])
                    (.node 1600132 ([(2,true),(3,true),(12,false),(0,false),(6,false),(5,false),(8,true)],[(13,false),(4,true),(7,false),(1,false),(11,false),(10,false),(9,false)])
                      (.node 1600114 ([(5,true),(6,true),(0,true),(12,true),(3,false),(2,false),(8,true)],[(13,false),(4,true),(7,true),(1,false),(11,false),(10,false),(9,false)])
                        (.node 1599232 ([(5,true),(6,true),(0,true),(12,true),(3,false),(2,false),(8,true)],[(13,false),(4,true),(7,true),(1,false),(11,false),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1600342 ([(2,true),(3,true),(12,false),(0,false),(6,false),(5,false),(9,false)],[(13,false),(4,true),(10,true),(11,true),(1,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1600900 ([(0,true),(12,true),(13,true),(5,false),(10,false),(2,true),(8,true)],[(6,true),(7,true),(3,true),(4,true),(11,true),(1,true),(9,false)])
                      (.node 1600882 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                        .empty
                        .empty)
                      (.node 1600930 ([(2,true),(3,true),(13,true),(5,false),(11,true),(0,false),(8,true)],[(6,true),(7,false),(1,false),(12,true),(4,true),(10,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1602508 ([(5,true),(13,false),(3,false),(2,false),(1,false),(0,false),(9,false)],[(6,true),(10,true),(11,true),(12,true),(4,true),(7,true),(8,true)])
                    (.node 1601722 ([(3,true),(4,true),(5,true),(6,true),(11,true),(1,false),(8,true)],[(13,false),(12,false),(2,true),(7,true),(0,false),(10,false),(9,false)])
                      (.node 1601650 ([(1,true),(2,true),(10,true),(6,false),(13,false),(4,true),(8,true)],[(5,false),(7,false),(0,false),(11,true),(12,true),(3,false),(9,false)])
                        (.node 1601626 ([(5,true),(6,true),(10,false),(3,true),(12,false),(1,false),(8,true)],[(13,false),(4,true),(7,true),(0,false),(11,true),(2,true),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1601734 ([(1,true),(2,true),(3,true),(13,true),(6,true),(10,false),(9,false)],[(5,false),(4,false),(12,false),(11,false),(0,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1603192 ([(3,true),(13,true),(5,false),(11,true),(1,false),(0,false),(9,false)],[(6,true),(10,true),(4,false),(12,false),(2,true),(7,true),(8,true)])
                      (.node 1602550 ([(5,true),(13,false),(3,false),(2,false),(1,false),(0,false),(8,true)],[(6,true),(7,false),(4,false),(12,false),(11,false),(10,false),(9,false)])
                        .empty
                        .empty)
                      (.node 1603204 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,true),(7,true),(8,true)])
                        .empty
                        .empty)))))))))
      (.node 1876313 ([(7,true),(0,true),(13,false),(12,false),(3,false),(2,false),(9,true)],[(1,true),(8,false),(6,false),(5,false),(4,false),(11,false),(10,false)])
        (.node 1739093 ([(6,true),(0,true),(8,false),(4,true),(12,false),(2,false),(10,false)],[(13,false),(5,true),(7,true),(3,false),(11,false),(1,false),(9,true)])
          (.node 1710167 ([(4,true),(5,true),(6,true),(13,false),(2,false),(1,false),(10,false)],[(0,true),(11,true),(12,true),(3,true),(7,true),(8,true),(9,true)])
            (.node 1693829 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
              (.node 1689827 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                (.node 1609132 ([(6,false),(13,false),(4,true),(11,false),(1,true),(2,true),(8,true)],[(5,false),(12,true),(3,false),(7,false),(0,true),(10,false),(9,false)])
                  (.node 1604608 ([(5,true),(13,false),(3,false),(2,false),(1,false),(0,false),(8,true)],[(6,true),(7,false),(4,false),(12,false),(11,false),(10,false),(9,false)])
                    (.node 1603978 ([(5,true),(13,false),(3,false),(2,false),(10,true),(0,true),(8,true)],[(6,true),(11,true),(12,true),(4,true),(7,true),(1,true),(9,false)])
                      (.node 1603936 ([(7,true),(2,true),(3,true),(13,true),(6,true),(0,true),(9,false)],[(5,false),(4,false),(12,false),(11,false),(10,false),(1,true),(8,true)])
                        (.node 1603252 ([(0,true),(1,true),(11,false),(5,true),(13,false),(3,false),(8,true)],[(6,true),(7,true),(2,false),(12,true),(4,true),(10,false),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1604566 ([(5,true),(13,false),(3,false),(2,false),(1,false),(0,false),(9,false)],[(6,true),(10,true),(11,true),(12,true),(4,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1608778 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(2,true),(7,true),(8,true)])
                      (.node 1605646 ([(6,false),(5,false),(4,false),(3,false),(2,false),(1,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,false),(7,true),(8,true)])
                        (.node 1605634 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1608790 ([(1,true),(10,true),(6,false),(5,false),(4,false),(3,false),(8,true)],[(13,false),(12,false),(11,false),(0,true),(7,true),(2,false),(9,false)])
                        .empty
                        .empty)))
                  (.node 1609762 ([(6,false),(5,false),(4,false),(3,false),(2,false),(1,false),(9,false)],[(13,false),(12,false),(11,false),(10,false),(0,false),(7,true),(8,true)])
                    (.node 1609408 ([(7,true),(6,false),(13,false),(4,true),(11,false),(1,false),(9,false)],[(5,false),(12,true),(3,false),(2,false),(10,false),(0,false),(8,true)])
                      (.node 1609366 ([(3,true),(4,true),(5,true),(6,true),(10,true),(1,false),(8,true)],[(13,false),(12,false),(11,false),(2,true),(7,true),(0,false),(9,false)])
                        (.node 1609174 ([(6,false),(5,false),(4,false),(3,false),(10,true),(1,true),(8,true)],[(13,false),(12,false),(11,false),(0,false),(7,true),(2,true),(9,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1609750 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(9,false)],[(13,false),(12,false),(11,false),(10,false),(1,true),(7,true),(8,true)])
                        .empty
                        .empty))
                    (.node 1685057 ([(3,true),(8,false),(6,true),(13,false),(1,false),(11,false),(10,false)],[(0,true),(12,true),(2,true),(7,true),(5,false),(4,false),(9,true)])
                      (.node 1684745 ([(6,true),(0,true),(1,true),(2,true),(8,true),(4,false),(10,false)],[(13,false),(12,false),(11,false),(3,false),(7,false),(5,false),(9,true)])
                        .empty
                        .empty)
                      (.node 1689533 ([(5,false),(8,false),(0,false),(13,false),(2,true),(3,true),(10,false)],[(6,false),(7,true),(1,true),(12,false),(11,false),(4,true),(9,true)])
                        .empty
                        .empty))))
                (.node 1692437 ([(5,true),(6,true),(13,false),(12,false),(3,false),(8,true),(9,true)],[(0,true),(1,true),(2,true),(7,false),(4,false),(11,false),(10,false)])
                  (.node 1690919 ([(6,true),(0,true),(1,true),(12,false),(3,false),(8,true),(9,true)],[(13,false),(2,true),(7,false),(5,false),(4,false),(11,false),(10,false)])
                    (.node 1689941 ([(0,false),(13,false),(2,true),(3,true),(4,true),(5,true),(9,true)],[(6,false),(8,false),(7,false),(1,true),(12,false),(11,false),(10,false)])
                      (.node 1689923 ([(4,true),(11,true),(2,false),(1,false),(0,false),(6,false),(9,true)],[(13,false),(12,false),(3,true),(7,true),(8,true),(5,false),(10,false)])
                        (.node 1689857 ([(0,false),(13,false),(2,true),(3,true),(8,false),(5,false),(10,false)],[(6,false),(7,false),(1,true),(12,false),(11,false),(4,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1690217 ([(3,false),(2,false),(13,true),(0,true),(8,true),(5,true),(10,false)],[(6,false),(11,true),(12,true),(1,false),(7,false),(4,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1692323 ([(7,true),(0,false),(13,false),(12,false),(4,true),(5,true),(9,true)],[(6,false),(8,false),(1,true),(2,true),(3,true),(11,false),(10,false)])
                      (.node 1690967 ([(5,true),(6,true),(13,false),(2,true),(3,true),(11,false),(10,false)],[(0,true),(1,true),(12,false),(4,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1692335 ([(1,true),(13,true),(6,false),(8,false),(3,true),(4,true),(10,false)],[(0,true),(7,true),(2,false),(12,false),(11,false),(5,true),(9,true)])
                        .empty
                        .empty)))
                  (.node 1692629 ([(1,true),(13,true),(6,false),(11,true),(3,false),(8,true),(9,true)],[(0,true),(7,true),(2,false),(12,false),(4,true),(5,true),(10,false)])
                    (.node 1692545 ([(1,true),(13,true),(6,false),(5,false),(4,false),(3,false),(9,true)],[(0,true),(7,true),(8,true),(2,false),(12,false),(11,false),(10,false)])
                      (.node 1692521 ([(5,true),(6,true),(0,true),(1,true),(12,false),(3,false),(9,true)],[(13,false),(2,true),(8,false),(7,false),(4,false),(11,false),(10,false)])
                        (.node 1692449 ([(3,true),(4,true),(5,true),(6,true),(13,false),(1,false),(9,true)],[(0,true),(8,false),(7,false),(2,false),(12,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1692617 ([(3,true),(4,true),(8,false),(1,true),(13,true),(6,false),(10,false)],[(0,true),(7,false),(2,false),(12,false),(11,false),(5,false),(9,true)])
                        .empty
                        .empty))
                    (.node 1693289 ([(3,true),(4,true),(5,true),(6,true),(13,false),(1,false),(10,false)],[(0,true),(11,true),(12,true),(2,true),(7,true),(8,true),(9,true)])
                      (.node 1693241 ([(4,true),(12,true),(1,false),(0,false),(6,false),(8,true),(9,true)],[(13,false),(2,true),(3,true),(7,true),(5,false),(11,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1693817 ([(6,true),(0,true),(1,true),(12,false),(4,false),(3,false),(10,false)],[(13,false),(2,true),(11,true),(5,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)))))
              (.node 1701755 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                (.node 1696553 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                  (.node 1694237 ([(6,true),(0,true),(1,true),(12,false),(4,false),(3,false),(9,true)],[(13,false),(2,true),(8,false),(7,false),(5,false),(11,false),(10,false)])
                    (.node 1694039 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                      (.node 1693973 ([(1,true),(13,true),(6,false),(5,false),(11,false),(3,true),(9,true)],[(0,true),(7,true),(8,true),(4,true),(12,true),(2,true),(10,false)])
                        (.node 1693943 ([(6,true),(0,true),(1,true),(2,true),(11,true),(4,false),(9,true)],[(13,false),(12,false),(5,true),(7,true),(8,true),(3,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1694057 ([(1,true),(13,true),(6,false),(8,false),(4,true),(11,false),(10,false)],[(0,true),(7,true),(3,false),(2,false),(12,false),(5,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1696343 ([(5,true),(11,false),(2,false),(13,true),(0,true),(8,true),(9,true)],[(6,false),(12,true),(1,false),(7,false),(4,false),(3,false),(10,false)])
                      (.node 1694267 ([(1,true),(13,true),(6,false),(5,false),(4,false),(3,false),(9,true)],[(0,true),(7,true),(8,true),(2,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1696391 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)))
                  (.node 1696745 ([(1,true),(13,true),(6,false),(5,false),(8,false),(3,true),(10,false)],[(0,true),(7,true),(2,false),(12,false),(11,false),(4,true),(9,true)])
                    (.node 1696661 ([(1,true),(13,true),(6,false),(5,false),(4,false),(3,false),(9,true)],[(0,true),(7,true),(8,true),(2,false),(12,false),(11,false),(10,false)])
                      (.node 1696637 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                        (.node 1696565 ([(3,true),(4,true),(5,true),(6,true),(13,false),(1,false),(9,true)],[(0,true),(8,false),(7,false),(2,false),(12,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1696733 ([(3,true),(11,true),(6,true),(13,false),(1,false),(8,true),(9,true)],[(0,true),(7,false),(2,false),(12,false),(5,false),(4,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1701545 ([(6,true),(0,true),(11,false),(3,false),(2,false),(8,true),(9,true)],[(13,false),(12,false),(1,true),(7,false),(5,false),(4,false),(10,false)])
                      (.node 1697027 ([(3,true),(8,false),(1,true),(13,true),(6,false),(5,false),(10,false)],[(0,true),(7,false),(2,false),(12,false),(11,false),(4,false),(9,true)])
                        .empty
                        .empty)
                      (.node 1701593 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))))
                (.node 1704233 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                  (.node 1701947 ([(2,true),(3,true),(4,true),(11,true),(0,false),(6,false),(9,true)],[(13,false),(12,false),(1,true),(7,true),(8,true),(5,false),(10,false)])
                    (.node 1701863 ([(2,true),(3,true),(8,false),(6,true),(0,true),(11,false),(10,false)],[(13,false),(12,false),(1,true),(7,true),(5,false),(4,false),(9,true)])
                      (.node 1701839 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                        (.node 1701767 ([(4,true),(5,true),(6,true),(0,true),(12,true),(2,false),(9,true)],[(13,false),(3,true),(7,true),(8,true),(1,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1701935 ([(4,true),(11,true),(1,true),(2,true),(13,true),(6,false),(9,true)],[(0,true),(12,true),(3,true),(7,true),(8,true),(5,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1702229 ([(4,true),(8,false),(2,true),(12,false),(0,false),(6,false),(10,false)],[(13,false),(3,true),(7,true),(1,false),(11,false),(5,false),(9,true)])
                      (.node 1702181 ([(5,true),(6,true),(0,true),(12,true),(2,false),(8,true),(9,true)],[(13,false),(3,true),(4,true),(7,true),(1,false),(11,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1703939 ([(5,false),(8,false),(0,false),(13,false),(2,false),(11,false),(10,false)],[(6,false),(7,true),(1,true),(12,true),(3,true),(4,true),(9,true)])
                        .empty
                        .empty)))
                  (.node 1709987 ([(6,true),(0,true),(11,true),(4,false),(3,false),(2,false),(9,true)],[(13,false),(12,false),(5,true),(7,true),(8,true),(1,false),(10,false)])
                    (.node 1704347 ([(1,true),(2,true),(13,true),(6,false),(8,false),(4,true),(10,false)],[(0,true),(7,true),(3,false),(12,false),(11,false),(5,true),(9,true)])
                      (.node 1704329 ([(3,false),(2,false),(1,false),(0,false),(6,false),(5,false),(10,false)],[(13,false),(12,false),(11,false),(4,false),(7,true),(8,true),(9,true)])
                        (.node 1704263 ([(1,true),(2,true),(13,true),(6,false),(5,false),(4,false),(9,true)],[(0,true),(7,true),(8,true),(3,false),(12,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1704623 ([(4,true),(8,false),(1,true),(2,true),(13,true),(6,false),(10,false)],[(0,true),(7,false),(3,false),(12,false),(11,false),(5,false),(9,true)])
                        .empty
                        .empty))
                    (.node 1710071 ([(6,true),(0,true),(1,true),(2,true),(12,false),(4,false),(9,true)],[(13,false),(3,true),(8,false),(7,false),(5,false),(11,false),(10,false)])
                      (.node 1709999 ([(4,true),(5,true),(6,true),(13,false),(2,false),(1,false),(10,false)],[(0,true),(11,true),(12,true),(3,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1710095 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))))))
            (.node 1727489 ([(1,true),(8,false),(6,true),(13,false),(4,true),(11,false),(10,false)],[(0,true),(7,true),(5,false),(12,true),(3,false),(2,false),(9,true)])
              (.node 1718957 ([(2,true),(8,false),(4,false),(13,true),(0,true),(11,false),(10,false)],[(6,false),(5,false),(7,false),(1,false),(12,true),(3,false),(9,true)])
                (.node 1712807 ([(5,true),(6,true),(0,true),(8,true),(3,false),(2,false),(10,false)],[(13,false),(12,false),(11,false),(1,false),(7,false),(4,false),(9,true)])
                  (.node 1710437 ([(1,true),(2,true),(13,true),(6,false),(5,false),(4,false),(9,true)],[(0,true),(7,true),(8,true),(3,false),(12,false),(11,false),(10,false)])
                    (.node 1710293 ([(4,true),(5,true),(6,true),(13,false),(2,false),(1,false),(9,true)],[(0,true),(8,false),(7,false),(3,false),(12,false),(11,false),(10,false)])
                      (.node 1710281 ([(6,true),(0,true),(8,false),(4,true),(12,true),(2,false),(10,false)],[(13,false),(3,true),(7,false),(5,false),(11,false),(1,false),(9,true)])
                        (.node 1710179 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1710407 ([(6,true),(0,true),(1,true),(2,true),(12,false),(4,false),(9,true)],[(13,false),(3,true),(8,false),(7,false),(5,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1712471 ([(5,true),(6,true),(13,false),(3,true),(8,false),(1,false),(10,false)],[(0,true),(11,true),(12,true),(2,false),(7,false),(4,false),(9,true)])
                      (.node 1710521 ([(1,true),(11,true),(4,false),(3,false),(13,true),(6,false),(9,true)],[(0,true),(7,true),(8,true),(5,false),(12,true),(2,false),(10,false)])
                        (.node 1710503 ([(4,true),(11,false),(2,true),(13,true),(0,true),(8,true),(9,true)],[(6,false),(5,false),(12,true),(3,true),(7,true),(1,true),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1712519 ([(4,true),(5,true),(6,true),(13,false),(2,false),(1,false),(10,false)],[(0,true),(11,true),(12,true),(3,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)))
                  (.node 1718057 ([(5,true),(6,true),(13,false),(12,false),(1,true),(2,true),(10,false)],[(0,true),(11,false),(3,true),(4,true),(7,true),(8,true),(9,true)])
                    (.node 1713419 ([(1,true),(8,false),(5,true),(6,true),(13,false),(3,true),(10,false)],[(0,true),(7,true),(4,false),(11,true),(12,true),(2,false),(9,true)])
                      (.node 1713371 ([(2,true),(12,false),(6,true),(0,true),(8,false),(4,false),(10,false)],[(13,false),(3,true),(11,true),(5,false),(7,false),(1,false),(9,true)])
                        (.node 1712855 ([(4,true),(5,true),(12,true),(13,true),(0,true),(1,true),(10,false)],[(6,false),(11,false),(2,true),(3,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1718009 ([(6,true),(0,true),(1,true),(8,true),(4,false),(3,false),(10,false)],[(13,false),(12,false),(11,false),(2,false),(7,false),(5,false),(9,true)])
                        .empty
                        .empty))
                    (.node 1718621 ([(2,true),(3,true),(12,false),(0,false),(6,false),(5,false),(10,false)],[(13,false),(4,true),(11,true),(1,true),(7,true),(8,true),(9,true)])
                      (.node 1718573 ([(3,true),(4,true),(11,true),(0,false),(6,false),(8,true),(9,true)],[(13,false),(12,false),(1,true),(2,true),(7,true),(5,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1718909 ([(3,true),(4,true),(8,true),(1,false),(0,false),(6,false),(10,false)],[(13,false),(12,false),(11,false),(5,false),(7,false),(2,false),(9,true)])
                        .empty
                        .empty))))
                (.node 1721333 ([(5,true),(6,true),(0,true),(1,true),(12,true),(3,false),(9,true)],[(13,false),(4,true),(7,true),(8,true),(2,false),(11,false),(10,false)])
                  (.node 1721135 ([(3,true),(4,true),(11,true),(1,false),(0,false),(6,false),(9,true)],[(13,false),(12,false),(2,true),(7,true),(8,true),(5,false),(10,false)])
                    (.node 1720991 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                      (.node 1720925 ([(3,true),(12,false),(1,false),(0,false),(6,false),(5,false),(10,false)],[(13,false),(4,true),(11,true),(2,true),(7,true),(8,true),(9,true)])
                        (.node 1720907 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1721021 ([(1,true),(2,true),(8,false),(6,true),(13,false),(4,true),(10,false)],[(0,true),(7,true),(5,false),(11,true),(12,true),(3,false),(9,true)])
                        .empty
                        .empty))
                    (.node 1721249 ([(5,true),(6,true),(13,false),(3,false),(2,false),(1,false),(9,true)],[(0,true),(8,false),(7,false),(4,false),(12,false),(11,false),(10,false)])
                      (.node 1721147 ([(1,true),(2,true),(8,true),(6,true),(13,false),(4,true),(10,false)],[(0,true),(7,true),(3,true),(12,false),(11,false),(5,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1721261 ([(2,false),(1,false),(0,false),(13,false),(4,true),(5,true),(10,false)],[(6,false),(11,true),(12,true),(3,false),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)))
                  (.node 1727081 ([(6,true),(0,true),(8,false),(3,true),(4,true),(11,false),(10,false)],[(13,false),(12,false),(5,true),(7,true),(2,false),(1,false),(9,true)])
                    (.node 1721441 ([(1,true),(2,true),(3,true),(13,true),(6,false),(5,false),(9,true)],[(0,true),(7,true),(8,true),(4,false),(12,false),(11,false),(10,false)])
                      (.node 1721429 ([(3,true),(12,false),(1,false),(0,false),(6,false),(5,false),(9,true)],[(13,false),(4,true),(8,false),(7,false),(2,false),(11,false),(10,false)])
                        (.node 1721357 ([(1,true),(2,true),(8,false),(4,false),(13,true),(6,false),(10,false)],[(0,true),(7,true),(5,true),(11,true),(12,true),(3,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1726805 ([(3,true),(4,true),(11,false),(0,false),(6,false),(8,true),(9,true)],[(13,false),(12,false),(5,true),(7,false),(2,false),(1,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1727165 ([(6,true),(0,true),(1,true),(11,true),(4,false),(3,false),(9,true)],[(13,false),(12,false),(5,true),(7,true),(8,true),(2,false),(10,false)])
                      (.node 1727099 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1727195 ([(1,true),(11,true),(4,false),(13,true),(6,false),(8,true),(9,true)],[(0,true),(7,true),(5,false),(12,true),(3,false),(2,false),(10,false)])
                        .empty
                        .empty)))))
              (.node 1735037 ([(3,true),(4,true),(12,false),(0,false),(6,false),(8,true),(9,true)],[(13,false),(5,true),(7,false),(2,false),(1,false),(11,false),(10,false)])
                (.node 1729835 ([(2,true),(3,true),(13,true),(6,false),(5,false),(8,true),(9,true)],[(0,true),(1,true),(7,true),(4,false),(12,false),(11,false),(10,false)])
                  (.node 1729565 ([(5,true),(6,true),(13,false),(3,false),(8,false),(1,true),(10,false)],[(0,true),(7,false),(4,false),(12,false),(11,false),(2,true),(9,true)])
                    (.node 1729481 ([(5,true),(6,true),(13,false),(3,false),(2,false),(1,false),(9,true)],[(0,true),(8,false),(7,false),(4,false),(12,false),(11,false),(10,false)])
                      (.node 1729247 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                        (.node 1729199 ([(3,true),(13,true),(6,false),(5,false),(8,true),(1,false),(10,false)],[(0,true),(11,true),(12,true),(4,true),(7,false),(2,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1729493 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1729661 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                      (.node 1729589 ([(1,true),(11,true),(6,true),(13,false),(4,true),(8,true),(9,true)],[(0,true),(7,true),(5,true),(12,true),(3,false),(2,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1729673 ([(1,true),(2,true),(3,true),(13,true),(6,false),(5,false),(9,true)],[(0,true),(7,true),(8,true),(4,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 1734767 ([(6,true),(0,true),(12,true),(4,false),(8,false),(2,true),(10,false)],[(13,false),(5,true),(7,true),(1,false),(11,false),(3,true),(9,true)])
                    (.node 1734683 ([(6,true),(0,true),(12,true),(4,false),(3,false),(2,false),(9,true)],[(13,false),(5,true),(7,true),(8,true),(1,false),(11,false),(10,false)])
                      (.node 1734401 ([(3,false),(8,false),(5,false),(13,true),(0,true),(1,true),(10,false)],[(6,false),(7,false),(4,true),(12,false),(11,false),(2,true),(9,true)])
                        (.node 1729883 ([(1,true),(8,false),(4,false),(13,true),(6,false),(11,false),(10,false)],[(0,true),(7,true),(5,true),(12,true),(3,false),(2,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1734695 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1734863 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                      (.node 1734791 ([(2,true),(11,true),(0,false),(6,false),(5,false),(4,false),(9,true)],[(13,false),(12,false),(1,true),(7,true),(8,true),(3,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1734875 ([(2,true),(3,true),(4,true),(12,false),(0,false),(6,false),(9,true)],[(13,false),(5,true),(8,false),(7,false),(1,false),(11,false),(10,false)])
                        .empty
                        .empty))))
                (.node 1737611 ([(1,true),(2,true),(3,true),(4,true),(13,true),(6,false),(9,true)],[(0,true),(7,true),(8,true),(5,false),(12,false),(11,false),(10,false)])
                  (.node 1737389 ([(3,true),(11,true),(12,true),(13,true),(6,false),(8,true),(9,true)],[(0,true),(1,true),(2,true),(7,true),(5,false),(4,false),(10,false)])
                    (.node 1737191 ([(0,false),(6,false),(5,false),(12,false),(2,true),(3,true),(9,true)],[(13,false),(4,false),(8,false),(7,false),(1,true),(11,false),(10,false)])
                      (.node 1737161 ([(6,true),(0,true),(8,true),(4,true),(12,false),(2,true),(10,false)],[(13,false),(5,true),(7,true),(1,true),(11,false),(3,true),(9,true)])
                        (.node 1735085 ([(2,true),(8,false),(5,false),(13,true),(0,true),(11,false),(10,false)],[(6,false),(7,false),(1,false),(12,true),(4,false),(3,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1737371 ([(6,true),(0,true),(8,false),(2,false),(12,true),(4,false),(10,false)],[(13,false),(5,true),(7,true),(3,true),(11,true),(1,false),(9,true)])
                        .empty
                        .empty))
                    (.node 1737485 ([(1,true),(2,true),(8,false),(6,true),(13,false),(4,false),(10,false)],[(0,true),(7,true),(5,false),(12,false),(11,false),(3,false),(9,true)])
                      (.node 1737455 ([(6,true),(0,true),(1,true),(12,true),(4,false),(3,false),(9,true)],[(13,false),(5,true),(7,true),(8,true),(2,false),(11,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1737599 ([(3,true),(4,true),(12,false),(1,false),(0,false),(6,false),(9,true)],[(13,false),(5,true),(8,false),(7,false),(2,false),(11,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 1738883 ([(6,true),(0,true),(1,true),(2,true),(12,true),(4,false),(9,true)],[(13,false),(5,true),(7,true),(8,true),(3,false),(11,false),(10,false)])
                    (.node 1738799 ([(6,true),(0,true),(11,true),(12,true),(4,false),(8,true),(9,true)],[(13,false),(5,true),(7,true),(3,false),(2,false),(1,false),(10,false)])
                      (.node 1738187 ([(3,true),(4,true),(12,false),(1,false),(0,false),(6,false),(10,false)],[(13,false),(5,true),(11,true),(2,true),(7,true),(8,true),(9,true)])
                        (.node 1738139 ([(4,true),(12,false),(2,true),(8,false),(0,false),(6,false),(10,false)],[(13,false),(5,true),(11,true),(1,false),(7,false),(3,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1738811 ([(4,true),(5,true),(6,true),(0,true),(11,true),(2,false),(9,true)],[(13,false),(12,false),(3,true),(7,true),(8,true),(1,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1738979 ([(4,true),(12,false),(2,false),(1,false),(0,false),(6,false),(9,true)],[(13,false),(5,true),(8,false),(7,false),(3,false),(11,false),(10,false)])
                      (.node 1738907 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1738991 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)))))))
          (.node 1847207 ([(5,true),(6,true),(0,true),(13,false),(3,false),(2,false),(10,false)],[(1,true),(11,true),(12,true),(4,true),(7,true),(8,true),(9,true)])
            (.node 1829237 ([(7,true),(1,false),(13,false),(12,false),(5,true),(6,true),(9,true)],[(0,false),(8,false),(2,true),(3,true),(4,true),(11,false),(10,false)])
              (.node 1817195 ([(2,true),(13,true),(0,false),(6,false),(8,false),(4,true),(10,false)],[(1,true),(7,true),(3,false),(12,false),(11,false),(5,true),(9,true)])
                (.node 1746371 ([(4,true),(5,true),(6,true),(0,true),(8,true),(2,false),(10,false)],[(13,false),(12,false),(11,false),(1,false),(7,false),(3,false),(9,true)])
                  (.node 1741487 ([(6,true),(13,false),(4,false),(3,false),(2,false),(1,false),(9,true)],[(0,true),(8,false),(7,false),(5,false),(12,false),(11,false),(10,false)])
                    (.node 1740509 ([(1,true),(8,false),(3,false),(12,true),(13,true),(6,false),(10,false)],[(0,true),(7,true),(4,true),(5,true),(11,true),(2,false),(9,true)])
                      (.node 1740461 ([(2,true),(3,true),(8,true),(0,false),(13,false),(5,true),(10,false)],[(6,false),(11,true),(12,true),(4,false),(7,false),(1,false),(9,true)])
                        (.node 1739105 ([(7,true),(6,true),(13,false),(12,false),(2,false),(1,false),(9,true)],[(0,true),(8,false),(5,false),(4,false),(3,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1741211 ([(3,true),(4,true),(13,true),(6,false),(8,true),(1,false),(10,false)],[(0,true),(11,true),(12,true),(5,true),(7,false),(2,false),(9,true)])
                        .empty
                        .empty))
                    (.node 1741601 ([(1,true),(11,true),(4,true),(13,true),(6,false),(8,true),(9,true)],[(0,true),(7,true),(5,false),(12,false),(3,false),(2,false),(10,false)])
                      (.node 1741571 ([(6,true),(13,false),(4,false),(3,false),(8,false),(1,true),(10,false)],[(0,true),(7,false),(5,false),(12,false),(11,false),(2,true),(9,true)])
                        (.node 1741505 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1741895 ([(1,true),(8,false),(6,true),(13,false),(4,false),(3,false),(10,false)],[(0,true),(7,true),(5,false),(12,false),(11,false),(2,false),(9,true)])
                        .empty
                        .empty)))
                  (.node 1817015 ([(4,true),(5,true),(6,true),(0,true),(13,false),(2,false),(9,true)],[(1,true),(8,false),(7,false),(3,false),(12,false),(11,false),(10,false)])
                    (.node 1816841 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                      (.node 1816793 ([(6,true),(11,false),(3,false),(13,true),(1,true),(8,true),(9,true)],[(0,false),(12,true),(2,false),(7,false),(5,false),(4,false),(10,false)])
                        (.node 1746683 ([(0,false),(6,false),(5,false),(4,false),(8,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,false),(1,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1817003 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1817111 ([(2,true),(13,true),(0,false),(6,false),(5,false),(4,false),(9,true)],[(1,true),(7,true),(8,true),(3,false),(12,false),(11,false),(10,false)])
                      (.node 1817087 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1817183 ([(4,true),(11,true),(0,true),(13,false),(2,false),(8,true),(9,true)],[(1,true),(7,false),(3,false),(12,false),(6,false),(5,false),(10,false)])
                        .empty
                        .empty))))
                (.node 1827077 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                  (.node 1826783 ([(6,false),(8,false),(1,false),(13,false),(3,true),(4,true),(10,false)],[(0,false),(7,true),(2,true),(12,false),(11,false),(5,true),(9,true)])
                    (.node 1822265 ([(4,true),(8,false),(0,true),(13,false),(2,false),(11,false),(10,false)],[(1,true),(12,true),(3,true),(7,true),(6,false),(5,false),(9,true)])
                      (.node 1821995 ([(0,true),(1,true),(2,true),(3,true),(8,true),(5,false),(10,false)],[(13,false),(12,false),(11,false),(4,false),(7,false),(6,false),(9,true)])
                        (.node 1817477 ([(4,true),(8,false),(2,true),(13,true),(0,false),(6,false),(10,false)],[(1,true),(7,false),(3,false),(12,false),(11,false),(5,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1825073 ([(4,false),(3,false),(13,true),(1,true),(8,true),(6,true),(10,false)],[(0,false),(11,true),(12,true),(2,false),(7,false),(5,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1826855 ([(1,false),(13,false),(3,true),(4,true),(5,true),(6,true),(9,true)],[(0,false),(8,false),(7,false),(2,true),(12,false),(11,false),(10,false)])
                      (.node 1826837 ([(5,true),(11,true),(3,false),(2,false),(1,false),(0,false),(9,true)],[(13,false),(12,false),(4,true),(7,true),(8,true),(6,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1827065 ([(1,false),(13,false),(3,true),(4,true),(8,false),(6,false),(10,false)],[(0,false),(7,false),(2,true),(12,false),(11,false),(5,false),(9,true)])
                        .empty
                        .empty)))
                  (.node 1827473 ([(4,true),(5,true),(8,false),(2,true),(13,true),(0,false),(10,false)],[(1,true),(7,false),(3,false),(12,false),(11,false),(6,false),(9,true)])
                    (.node 1827377 ([(6,true),(0,true),(1,true),(2,true),(12,false),(4,false),(9,true)],[(13,false),(3,true),(8,false),(7,false),(5,false),(11,false),(10,false)])
                      (.node 1827305 ([(4,true),(5,true),(6,true),(0,true),(13,false),(2,false),(9,true)],[(1,true),(8,false),(7,false),(3,false),(12,false),(11,false),(10,false)])
                        (.node 1827293 ([(6,true),(0,true),(13,false),(12,false),(4,false),(8,true),(9,true)],[(1,true),(2,true),(3,true),(7,false),(5,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1827401 ([(2,true),(13,true),(0,false),(6,false),(5,false),(4,false),(9,true)],[(1,true),(7,true),(8,true),(3,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1827881 ([(6,true),(0,true),(13,false),(3,true),(4,true),(11,false),(10,false)],[(1,true),(2,true),(12,false),(5,true),(7,true),(8,true),(9,true)])
                      (.node 1827485 ([(2,true),(13,true),(0,false),(11,true),(4,false),(8,true),(9,true)],[(1,true),(7,true),(3,false),(12,false),(5,true),(6,true),(10,false)])
                        .empty
                        .empty)
                      (.node 1828169 ([(0,true),(1,true),(2,true),(12,false),(4,false),(8,true),(9,true)],[(13,false),(3,true),(7,false),(6,false),(5,false),(11,false),(10,false)])
                        .empty
                        .empty)))))
              (.node 1837037 ([(6,true),(0,true),(1,true),(12,true),(3,false),(8,true),(9,true)],[(13,false),(4,true),(5,true),(7,true),(2,false),(11,false),(10,false)])
                (.node 1831193 ([(0,true),(1,true),(2,true),(3,true),(11,true),(5,false),(9,true)],[(13,false),(12,false),(6,true),(7,true),(8,true),(4,false),(10,false)])
                  (.node 1830971 ([(2,true),(13,true),(0,false),(8,false),(5,true),(11,false),(10,false)],[(1,true),(7,true),(4,false),(3,false),(12,false),(6,true),(9,true)])
                    (.node 1830497 ([(4,true),(5,true),(6,true),(0,true),(13,false),(2,false),(10,false)],[(1,true),(11,true),(12,true),(3,true),(7,true),(8,true),(9,true)])
                      (.node 1830449 ([(5,true),(12,true),(2,false),(1,false),(0,false),(8,true),(9,true)],[(13,false),(3,true),(4,true),(7,true),(6,false),(11,false),(10,false)])
                        (.node 1829249 ([(2,true),(13,true),(0,false),(8,false),(4,true),(5,true),(10,false)],[(1,true),(7,true),(3,false),(12,false),(11,false),(6,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1830953 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1831067 ([(0,true),(1,true),(2,true),(12,false),(5,false),(4,false),(10,false)],[(13,false),(3,true),(11,true),(6,true),(7,true),(8,true),(9,true)])
                      (.node 1831037 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1831181 ([(2,true),(13,true),(0,false),(6,false),(11,false),(4,true),(9,true)],[(1,true),(7,true),(8,true),(5,true),(12,true),(3,true),(10,false)])
                        .empty
                        .empty)))
                  (.node 1833257 ([(6,true),(0,true),(1,true),(8,true),(4,false),(3,false),(10,false)],[(13,false),(12,false),(11,false),(2,false),(7,false),(5,false),(9,true)])
                    (.node 1832921 ([(6,true),(0,true),(13,false),(4,true),(8,false),(2,false),(10,false)],[(1,true),(11,true),(12,true),(3,false),(7,false),(5,false),(9,true)])
                      (.node 1831487 ([(0,true),(1,true),(2,true),(12,false),(5,false),(4,false),(9,true)],[(13,false),(3,true),(8,false),(7,false),(6,false),(11,false),(10,false)])
                        (.node 1831475 ([(2,true),(13,true),(0,false),(6,false),(5,false),(4,false),(9,true)],[(1,true),(7,true),(8,true),(3,false),(12,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1832969 ([(5,true),(6,true),(0,true),(13,false),(3,false),(2,false),(10,false)],[(1,true),(11,true),(12,true),(4,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1833821 ([(3,true),(12,false),(0,true),(1,true),(8,false),(5,false),(10,false)],[(13,false),(4,true),(11,true),(6,false),(7,false),(2,false),(9,true)])
                      (.node 1833305 ([(5,true),(6,true),(12,true),(13,true),(1,true),(2,true),(10,false)],[(0,false),(11,false),(3,true),(4,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1833869 ([(2,true),(8,false),(6,true),(0,true),(13,false),(4,true),(10,false)],[(1,true),(7,true),(5,false),(11,true),(12,true),(3,false),(9,true)])
                        .empty
                        .empty))))
                (.node 1839089 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                  (.node 1838861 ([(3,true),(4,true),(5,true),(11,true),(1,false),(0,false),(9,true)],[(13,false),(12,false),(2,true),(7,true),(8,true),(6,false),(10,false)])
                    (.node 1838795 ([(0,true),(1,true),(11,false),(4,false),(3,false),(8,true),(9,true)],[(13,false),(12,false),(2,true),(7,false),(6,false),(5,false),(10,false)])
                      (.node 1838507 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                        (.node 1837085 ([(5,true),(8,false),(3,true),(12,false),(1,false),(0,false),(10,false)],[(13,false),(4,true),(7,true),(2,false),(11,false),(6,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1838849 ([(5,true),(11,true),(2,true),(3,true),(13,true),(0,false),(9,true)],[(1,true),(12,true),(4,true),(7,true),(8,true),(6,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1839005 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                      (.node 1838975 ([(5,true),(6,true),(0,true),(1,true),(12,true),(3,false),(9,true)],[(13,false),(4,true),(7,true),(8,true),(2,false),(11,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1839071 ([(3,true),(4,true),(8,false),(0,true),(1,true),(11,false),(10,false)],[(13,false),(12,false),(2,true),(7,true),(6,false),(5,false),(9,true)])
                        .empty
                        .empty)))
                  (.node 1841471 ([(2,true),(3,true),(13,true),(0,false),(6,false),(5,false),(9,true)],[(1,true),(7,true),(8,true),(4,false),(12,false),(11,false),(10,false)])
                    (.node 1841243 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false),(10,false)],[(13,false),(12,false),(11,false),(5,false),(7,true),(8,true),(9,true)])
                      (.node 1841189 ([(6,false),(8,false),(1,false),(13,false),(3,false),(11,false),(10,false)],[(0,false),(7,true),(2,true),(12,true),(4,true),(5,true),(9,true)])
                        (.node 1839479 ([(5,true),(8,false),(2,true),(3,true),(13,true),(0,false),(10,false)],[(1,true),(7,false),(4,false),(12,false),(11,false),(6,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1841261 ([(2,true),(3,true),(13,true),(0,false),(8,false),(5,true),(10,false)],[(1,true),(7,true),(4,false),(12,false),(11,false),(6,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1847081 ([(5,true),(6,true),(0,true),(13,false),(3,false),(2,false),(10,false)],[(1,true),(11,true),(12,true),(4,true),(7,true),(8,true),(9,true)])
                      (.node 1841483 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1847093 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))))))
            (.node 1858241 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
              (.node 1850333 ([(2,true),(8,false),(5,false),(13,true),(0,false),(11,false),(10,false)],[(1,true),(7,true),(6,true),(12,true),(4,false),(3,false),(9,true)])
                (.node 1849649 ([(4,true),(13,true),(0,false),(6,false),(8,true),(2,false),(10,false)],[(1,true),(11,true),(12,true),(5,true),(7,false),(3,false),(9,true)])
                  (.node 1847435 ([(2,true),(11,true),(5,false),(4,false),(13,true),(0,false),(9,true)],[(1,true),(7,true),(8,true),(6,false),(12,true),(3,false),(10,false)])
                    (.node 1847321 ([(0,true),(1,true),(2,true),(3,true),(12,false),(5,false),(9,true)],[(13,false),(4,true),(8,false),(7,false),(6,false),(11,false),(10,false)])
                      (.node 1847303 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                        (.node 1847237 ([(0,true),(1,true),(11,true),(5,false),(4,false),(3,false),(9,true)],[(13,false),(12,false),(6,true),(7,true),(8,true),(2,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1847417 ([(5,true),(11,false),(3,true),(13,true),(1,true),(8,true),(9,true)],[(0,false),(6,false),(12,true),(4,true),(7,true),(2,true),(10,false)])
                        .empty
                        .empty))
                    (.node 1847645 ([(2,true),(3,true),(13,true),(0,false),(6,false),(5,false),(9,true)],[(1,true),(7,true),(8,true),(4,false),(12,false),(11,false),(10,false)])
                      (.node 1847531 ([(0,true),(1,true),(8,false),(5,true),(12,true),(3,false),(10,false)],[(13,false),(4,true),(7,false),(6,false),(11,false),(2,false),(9,true)])
                        (.node 1847501 ([(5,true),(6,true),(0,true),(13,false),(3,false),(2,false),(9,true)],[(1,true),(8,false),(7,false),(4,false),(12,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1847657 ([(0,true),(1,true),(2,true),(3,true),(12,false),(5,false),(9,true)],[(13,false),(4,true),(8,false),(7,false),(6,false),(11,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 1850039 ([(2,true),(11,true),(0,true),(13,false),(5,true),(8,true),(9,true)],[(1,true),(7,true),(6,true),(12,true),(4,false),(3,false),(10,false)])
                    (.node 1849943 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                      (.node 1849931 ([(6,true),(0,true),(13,false),(4,false),(3,false),(2,false),(9,true)],[(1,true),(8,false),(7,false),(5,false),(12,false),(11,false),(10,false)])
                        (.node 1849697 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1850015 ([(6,true),(0,true),(13,false),(4,false),(8,false),(2,true),(10,false)],[(1,true),(7,false),(5,false),(12,false),(11,false),(3,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1850123 ([(2,true),(3,true),(4,true),(13,true),(0,false),(6,false),(9,true)],[(1,true),(7,true),(8,true),(5,false),(12,false),(11,false),(10,false)])
                      (.node 1850111 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1850285 ([(3,true),(4,true),(13,true),(0,false),(6,false),(8,true),(9,true)],[(1,true),(2,true),(7,true),(5,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty))))
                (.node 1856189 ([(6,true),(0,true),(1,true),(2,true),(12,true),(4,false),(9,true)],[(13,false),(5,true),(7,true),(8,true),(3,false),(11,false),(10,false)])
                  (.node 1855781 ([(4,true),(5,true),(11,true),(1,false),(0,false),(8,true),(9,true)],[(13,false),(12,false),(2,true),(3,true),(7,true),(6,false),(10,false)])
                    (.node 1854971 ([(6,true),(0,true),(13,false),(12,false),(2,true),(3,true),(10,false)],[(1,true),(11,false),(4,true),(5,true),(7,true),(8,true),(9,true)])
                      (.node 1853813 ([(3,true),(8,false),(5,false),(13,true),(1,true),(11,false),(10,false)],[(0,false),(6,false),(7,false),(2,false),(12,true),(4,false),(9,true)])
                        (.node 1853765 ([(4,true),(5,true),(8,true),(2,false),(1,false),(0,false),(10,false)],[(13,false),(12,false),(11,false),(6,false),(7,false),(3,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1855259 ([(0,true),(1,true),(2,true),(8,true),(5,false),(4,false),(10,false)],[(13,false),(12,false),(11,false),(3,false),(7,false),(6,false),(9,true)])
                        .empty
                        .empty))
                    (.node 1856105 ([(6,true),(0,true),(13,false),(4,false),(3,false),(2,false),(9,true)],[(1,true),(8,false),(7,false),(5,false),(12,false),(11,false),(10,false)])
                      (.node 1855829 ([(3,true),(4,true),(12,false),(1,false),(0,false),(6,false),(10,false)],[(13,false),(5,true),(11,true),(2,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1856117 ([(3,false),(2,false),(1,false),(13,false),(5,true),(6,true),(10,false)],[(0,false),(11,true),(12,true),(4,false),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)))
                  (.node 1858061 ([(2,true),(3,true),(8,true),(0,true),(13,false),(5,true),(10,false)],[(1,true),(7,true),(4,true),(12,false),(11,false),(6,true),(9,true)])
                    (.node 1856297 ([(2,true),(3,true),(4,true),(13,true),(0,false),(6,false),(9,true)],[(1,true),(7,true),(8,true),(5,false),(12,false),(11,false),(10,false)])
                      (.node 1856285 ([(4,true),(12,false),(2,false),(1,false),(0,false),(6,false),(9,true)],[(13,false),(5,true),(8,false),(7,false),(3,false),(11,false),(10,false)])
                        (.node 1856213 ([(2,true),(3,true),(8,false),(5,false),(13,true),(0,false),(10,false)],[(1,true),(7,true),(6,true),(11,true),(12,true),(4,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1858049 ([(4,true),(5,true),(11,true),(2,false),(1,false),(0,false),(9,true)],[(13,false),(12,false),(3,true),(7,true),(8,true),(6,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1858157 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                      (.node 1858133 ([(4,true),(12,false),(2,false),(1,false),(0,false),(6,false),(10,false)],[(13,false),(5,true),(11,true),(3,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1858229 ([(2,true),(3,true),(8,false),(0,true),(13,false),(5,true),(10,false)],[(1,true),(7,true),(6,false),(11,true),(12,true),(4,false),(9,true)])
                        .empty
                        .empty)))))
              (.node 1872995 ([(5,true),(12,false),(3,true),(8,false),(1,false),(0,false),(10,false)],[(13,false),(6,true),(11,true),(2,false),(7,false),(4,false),(9,true)])
                (.node 1871609 ([(4,false),(8,false),(6,false),(13,true),(1,true),(2,true),(10,false)],[(0,false),(7,false),(5,true),(12,false),(11,false),(3,true),(9,true)])
                  (.node 1864415 ([(0,true),(1,true),(2,true),(11,true),(5,false),(4,false),(9,true)],[(13,false),(12,false),(6,true),(7,true),(8,true),(3,false),(10,false)])
                    (.node 1864331 ([(0,true),(1,true),(8,false),(4,true),(5,true),(11,false),(10,false)],[(13,false),(12,false),(6,true),(7,true),(3,false),(2,false),(9,true)])
                      (.node 1864307 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                        (.node 1864013 ([(4,true),(5,true),(11,false),(1,false),(0,false),(8,true),(9,true)],[(13,false),(12,false),(6,true),(7,false),(3,false),(2,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1864403 ([(2,true),(11,true),(5,false),(13,true),(0,false),(8,true),(9,true)],[(1,true),(7,true),(6,false),(12,true),(4,false),(3,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1866821 ([(5,true),(6,true),(0,true),(1,true),(8,true),(3,false),(10,false)],[(13,false),(12,false),(11,false),(2,false),(7,false),(4,false),(9,true)])
                      (.node 1864697 ([(2,true),(8,false),(0,true),(13,false),(5,true),(11,false),(10,false)],[(1,true),(7,true),(6,false),(12,true),(4,false),(3,false),(9,true)])
                        .empty
                        .empty)
                      (.node 1867133 ([(1,false),(0,false),(6,false),(5,false),(8,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,false),(2,true),(9,true)])
                        .empty
                        .empty)))
                  (.node 1871999 ([(3,true),(11,true),(1,false),(0,false),(6,false),(5,false),(9,true)],[(13,false),(12,false),(2,true),(7,true),(8,true),(4,false),(10,false)])
                    (.node 1871903 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                      (.node 1871789 ([(3,true),(4,true),(5,true),(12,false),(1,false),(0,false),(9,true)],[(13,false),(6,true),(8,false),(7,false),(2,false),(11,false),(10,false)])
                        (.node 1871777 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1871933 ([(0,true),(1,true),(12,true),(5,false),(4,false),(3,false),(9,true)],[(13,false),(6,true),(7,true),(8,true),(2,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1872245 ([(4,true),(5,true),(12,false),(1,false),(0,false),(8,true),(9,true)],[(13,false),(6,true),(7,false),(3,false),(2,false),(11,false),(10,false)])
                      (.node 1872017 ([(0,true),(1,true),(12,true),(5,false),(8,false),(3,true),(10,false)],[(13,false),(6,true),(7,true),(2,false),(11,false),(4,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1872293 ([(3,true),(8,false),(6,false),(13,true),(1,true),(11,false),(10,false)],[(0,false),(7,false),(2,false),(12,true),(5,false),(4,false),(9,true)])
                        .empty
                        .empty))))
                (.node 1874705 ([(0,true),(1,true),(2,true),(12,true),(5,false),(4,false),(9,true)],[(13,false),(6,true),(7,true),(8,true),(3,false),(11,false),(10,false)])
                  (.node 1874525 ([(2,true),(3,true),(4,true),(5,true),(13,true),(0,false),(9,true)],[(1,true),(7,true),(8,true),(6,false),(12,false),(11,false),(10,false)])
                    (.node 1874411 ([(0,true),(1,true),(8,true),(5,true),(12,false),(3,true),(10,false)],[(13,false),(6,true),(7,true),(2,true),(11,false),(4,true),(9,true)])
                      (.node 1874399 ([(1,false),(0,false),(6,false),(12,false),(3,true),(4,true),(9,true)],[(13,false),(5,false),(8,false),(7,false),(2,true),(11,false),(10,false)])
                        (.node 1873043 ([(4,true),(5,true),(12,false),(2,false),(1,false),(0,false),(10,false)],[(13,false),(6,true),(11,true),(3,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1874513 ([(4,true),(5,true),(12,false),(2,false),(1,false),(0,false),(9,true)],[(13,false),(6,true),(8,false),(7,false),(3,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1874621 ([(0,true),(1,true),(8,false),(3,false),(12,true),(5,false),(10,false)],[(13,false),(6,true),(7,true),(4,true),(11,true),(2,false),(9,true)])
                      (.node 1874597 ([(4,true),(11,true),(12,true),(13,true),(0,false),(8,true),(9,true)],[(1,true),(2,true),(3,true),(7,true),(6,false),(5,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1874693 ([(2,true),(3,true),(8,false),(0,true),(13,false),(5,false),(10,false)],[(1,true),(7,true),(6,false),(12,false),(11,false),(4,false),(9,true)])
                        .empty
                        .empty)))
                  (.node 1876019 ([(5,true),(6,true),(0,true),(1,true),(11,true),(3,false),(9,true)],[(13,false),(12,false),(4,true),(7,true),(8,true),(2,false),(10,false)])
                    (.node 1875893 ([(5,true),(12,false),(3,false),(2,false),(1,false),(0,false),(9,true)],[(13,false),(6,true),(8,false),(7,false),(4,false),(11,false),(10,false)])
                      (.node 1875365 ([(2,true),(8,false),(4,false),(12,true),(13,true),(0,false),(10,false)],[(1,true),(7,true),(5,true),(6,true),(11,true),(3,false),(9,true)])
                        (.node 1875317 ([(3,true),(4,true),(8,true),(1,false),(13,false),(6,true),(10,false)],[(0,false),(11,true),(12,true),(5,false),(7,false),(2,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1875905 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1876115 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                      (.node 1876049 ([(0,true),(1,true),(11,true),(12,true),(5,false),(8,true),(9,true)],[(13,false),(6,true),(7,true),(4,false),(3,false),(2,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1876133 ([(0,true),(1,true),(2,true),(3,true),(12,true),(5,false),(9,true)],[(13,false),(6,true),(7,true),(8,true),(4,false),(11,false),(10,false)])
                        .empty
                        .empty))))))))
        (.node 1993325 ([(4,false),(3,false),(2,false),(13,false),(6,true),(0,true),(10,false)],[(1,false),(11,true),(12,true),(5,false),(7,true),(8,true),(9,true)])
          (.node 1964105 ([(3,true),(13,true),(1,false),(8,false),(5,true),(6,true),(10,false)],[(2,true),(7,true),(4,false),(12,false),(11,false),(0,true),(9,true)])
            (.node 1895921 ([(7,true),(1,true),(13,false),(12,false),(4,false),(3,false),(9,true)],[(2,true),(8,false),(0,false),(6,false),(5,false),(11,false),(10,false)])
              (.node 1892603 ([(6,true),(12,false),(4,true),(8,false),(2,false),(1,false),(10,false)],[(13,false),(0,true),(11,true),(3,false),(7,false),(5,false),(9,true)])
                (.node 1891217 ([(5,false),(8,false),(0,false),(13,true),(2,true),(3,true),(10,false)],[(1,false),(7,false),(6,true),(12,false),(11,false),(4,true),(9,true)])
                  (.node 1878809 ([(2,true),(11,true),(5,true),(13,true),(0,false),(8,true),(9,true)],[(1,true),(7,true),(6,false),(12,false),(4,false),(3,false),(10,false)])
                    (.node 1878713 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                      (.node 1878419 ([(4,true),(5,true),(13,true),(0,false),(8,true),(2,false),(10,false)],[(1,true),(11,true),(12,true),(6,true),(7,false),(3,false),(9,true)])
                        (.node 1876343 ([(0,true),(1,true),(8,false),(5,true),(12,false),(3,false),(10,false)],[(13,false),(6,true),(7,true),(4,false),(11,false),(2,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1878737 ([(0,true),(13,false),(5,false),(4,false),(3,false),(2,false),(9,true)],[(1,true),(8,false),(7,false),(6,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1886429 ([(6,true),(0,true),(1,true),(2,true),(8,true),(4,false),(10,false)],[(13,false),(12,false),(11,false),(3,false),(7,false),(5,false),(9,true)])
                      (.node 1879103 ([(2,true),(8,false),(0,true),(13,false),(5,false),(4,false),(10,false)],[(1,true),(7,true),(6,false),(12,false),(11,false),(3,false),(9,true)])
                        (.node 1878821 ([(0,true),(13,false),(5,false),(4,false),(8,false),(2,true),(10,false)],[(1,true),(7,false),(6,false),(12,false),(11,false),(3,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1886741 ([(2,false),(1,false),(0,false),(6,false),(8,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,false),(3,true),(9,true)])
                        .empty
                        .empty)))
                  (.node 1891607 ([(4,true),(11,true),(2,false),(1,false),(0,false),(6,false),(9,true)],[(13,false),(12,false),(3,true),(7,true),(8,true),(5,false),(10,false)])
                    (.node 1891511 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                      (.node 1891397 ([(4,true),(5,true),(6,true),(12,false),(2,false),(1,false),(9,true)],[(13,false),(0,true),(8,false),(7,false),(3,false),(11,false),(10,false)])
                        (.node 1891385 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1891541 ([(1,true),(2,true),(12,true),(6,false),(5,false),(4,false),(9,true)],[(13,false),(0,true),(7,true),(8,true),(3,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1891853 ([(5,true),(6,true),(12,false),(2,false),(1,false),(8,true),(9,true)],[(13,false),(0,true),(7,false),(4,false),(3,false),(11,false),(10,false)])
                      (.node 1891625 ([(1,true),(2,true),(12,true),(6,false),(8,false),(4,true),(10,false)],[(13,false),(0,true),(7,true),(3,false),(11,false),(5,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1891901 ([(4,true),(8,false),(0,false),(13,true),(2,true),(11,false),(10,false)],[(1,false),(7,false),(3,false),(12,true),(6,false),(5,false),(9,true)])
                        .empty
                        .empty))))
                (.node 1894313 ([(1,true),(2,true),(3,true),(12,true),(6,false),(5,false),(9,true)],[(13,false),(0,true),(7,true),(8,true),(4,false),(11,false),(10,false)])
                  (.node 1894133 ([(3,true),(4,true),(5,true),(6,true),(13,true),(1,false),(9,true)],[(2,true),(7,true),(8,true),(0,false),(12,false),(11,false),(10,false)])
                    (.node 1894019 ([(1,true),(2,true),(8,true),(6,true),(12,false),(4,true),(10,false)],[(13,false),(0,true),(7,true),(3,true),(11,false),(5,true),(9,true)])
                      (.node 1894007 ([(2,false),(1,false),(0,false),(12,false),(4,true),(5,true),(9,true)],[(13,false),(6,false),(8,false),(7,false),(3,true),(11,false),(10,false)])
                        (.node 1892651 ([(5,true),(6,true),(12,false),(3,false),(2,false),(1,false),(10,false)],[(13,false),(0,true),(11,true),(4,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1894121 ([(5,true),(6,true),(12,false),(3,false),(2,false),(1,false),(9,true)],[(13,false),(0,true),(8,false),(7,false),(4,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1894229 ([(1,true),(2,true),(8,false),(4,false),(12,true),(6,false),(10,false)],[(13,false),(0,true),(7,true),(5,true),(11,true),(3,false),(9,true)])
                      (.node 1894205 ([(5,true),(11,true),(12,true),(13,true),(1,false),(8,true),(9,true)],[(2,true),(3,true),(4,true),(7,true),(0,false),(6,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1894301 ([(3,true),(4,true),(8,false),(1,true),(13,false),(6,false),(10,false)],[(2,true),(7,true),(0,false),(12,false),(11,false),(5,false),(9,true)])
                        .empty
                        .empty)))
                  (.node 1895627 ([(6,true),(0,true),(1,true),(2,true),(11,true),(4,false),(9,true)],[(13,false),(12,false),(5,true),(7,true),(8,true),(3,false),(10,false)])
                    (.node 1895501 ([(6,true),(12,false),(4,false),(3,false),(2,false),(1,false),(9,true)],[(13,false),(0,true),(8,false),(7,false),(5,false),(11,false),(10,false)])
                      (.node 1894973 ([(3,true),(8,false),(5,false),(12,true),(13,true),(1,false),(10,false)],[(2,true),(7,true),(6,true),(0,true),(11,true),(4,false),(9,true)])
                        (.node 1894925 ([(4,true),(5,true),(8,true),(2,false),(13,false),(0,true),(10,false)],[(1,false),(11,true),(12,true),(6,false),(7,false),(3,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1895513 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1895723 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                      (.node 1895657 ([(1,true),(2,true),(11,true),(12,true),(6,false),(8,true),(9,true)],[(13,false),(0,true),(7,true),(5,false),(4,false),(3,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1895741 ([(1,true),(2,true),(3,true),(4,true),(12,true),(6,false),(9,true)],[(13,false),(0,true),(7,true),(8,true),(5,false),(11,false),(10,false)])
                        .empty
                        .empty)))))
              (.node 1952333 ([(5,true),(8,false),(3,true),(13,true),(1,false),(0,false),(10,false)],[(2,true),(7,false),(4,false),(12,false),(11,false),(6,false),(9,true)])
                (.node 1950947 ([(5,true),(6,true),(0,true),(1,true),(13,false),(3,false),(10,false)],[(2,true),(11,true),(12,true),(4,true),(7,true),(8,true),(9,true)])
                  (.node 1898417 ([(3,true),(11,true),(6,true),(13,true),(1,false),(8,true),(9,true)],[(2,true),(7,true),(0,false),(12,false),(5,false),(4,false),(10,false)])
                    (.node 1898321 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                      (.node 1898027 ([(5,true),(6,true),(13,true),(1,false),(8,true),(3,false),(10,false)],[(2,true),(11,true),(12,true),(0,true),(7,false),(4,false),(9,true)])
                        (.node 1895951 ([(1,true),(2,true),(8,false),(6,true),(12,false),(4,false),(10,false)],[(13,false),(0,true),(7,true),(5,false),(11,false),(3,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1898345 ([(1,true),(13,false),(6,false),(5,false),(4,false),(3,false),(9,true)],[(2,true),(8,false),(7,false),(0,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1898711 ([(3,true),(8,false),(1,true),(13,false),(6,false),(5,false),(10,false)],[(2,true),(7,true),(0,false),(12,false),(11,false),(4,false),(9,true)])
                      (.node 1898429 ([(1,true),(13,false),(6,false),(5,false),(8,false),(3,true),(10,false)],[(2,true),(7,false),(0,false),(12,false),(11,false),(4,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1950899 ([(6,true),(12,true),(3,false),(2,false),(1,false),(8,true),(9,true)],[(13,false),(4,true),(5,true),(7,true),(0,false),(11,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 1951631 ([(3,true),(13,true),(1,false),(0,false),(11,false),(5,true),(9,true)],[(2,true),(7,true),(8,true),(6,true),(12,true),(4,true),(10,false)])
                    (.node 1951487 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                      (.node 1951421 ([(3,true),(13,true),(1,false),(8,false),(6,true),(11,false),(10,false)],[(2,true),(7,true),(5,false),(4,false),(12,false),(0,true),(9,true)])
                        (.node 1951403 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1951517 ([(1,true),(2,true),(3,true),(12,false),(6,false),(5,false),(10,false)],[(13,false),(4,true),(11,true),(0,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1951925 ([(3,true),(13,true),(1,false),(0,false),(6,false),(5,false),(9,true)],[(2,true),(7,true),(8,true),(4,false),(12,false),(11,false),(10,false)])
                      (.node 1951643 ([(1,true),(2,true),(3,true),(4,true),(11,true),(6,false),(9,true)],[(13,false),(12,false),(0,true),(7,true),(8,true),(5,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1951937 ([(1,true),(2,true),(3,true),(12,false),(6,false),(5,false),(9,true)],[(13,false),(4,true),(8,false),(7,false),(0,false),(11,false),(10,false)])
                        .empty
                        .empty))))
                (.node 1957121 ([(5,true),(8,false),(1,true),(13,false),(3,false),(11,false),(10,false)],[(2,true),(12,true),(4,true),(7,true),(0,false),(6,false),(9,true)])
                  (.node 1954223 ([(5,true),(6,true),(0,true),(1,true),(13,false),(3,false),(9,true)],[(2,true),(8,false),(7,false),(4,false),(12,false),(11,false),(10,false)])
                    (.node 1954097 ([(5,true),(11,true),(1,true),(13,false),(3,false),(8,true),(9,true)],[(2,true),(7,false),(4,false),(12,false),(0,false),(6,false),(10,false)])
                      (.node 1954043 ([(0,true),(11,false),(4,false),(13,true),(2,true),(8,true),(9,true)],[(1,false),(12,true),(3,false),(7,false),(6,false),(5,false),(10,false)])
                        (.node 1953755 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1954109 ([(3,true),(13,true),(1,false),(0,false),(8,false),(5,true),(10,false)],[(2,true),(7,true),(4,false),(12,false),(11,false),(6,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1954319 ([(3,true),(13,true),(1,false),(0,false),(6,false),(5,false),(9,true)],[(2,true),(7,true),(8,true),(4,false),(12,false),(11,false),(10,false)])
                      (.node 1954253 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1954337 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)))
                  (.node 1961933 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                    (.node 1961711 ([(2,false),(13,false),(4,true),(5,true),(6,true),(0,true),(9,true)],[(1,false),(8,false),(7,false),(3,true),(12,false),(11,false),(10,false)])
                      (.node 1961693 ([(6,true),(11,true),(4,false),(3,false),(2,false),(1,false),(9,true)],[(13,false),(12,false),(5,true),(7,true),(8,true),(0,false),(10,false)])
                        (.node 1958909 ([(1,true),(2,true),(3,true),(4,true),(8,true),(6,false),(10,false)],[(13,false),(12,false),(11,false),(5,false),(7,false),(0,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1961921 ([(2,false),(13,false),(4,true),(5,true),(8,false),(0,false),(10,false)],[(1,false),(7,false),(3,true),(12,false),(11,false),(6,false),(9,true)])
                        .empty
                        .empty))
                    (.node 1963697 ([(0,false),(8,false),(2,false),(13,false),(4,true),(5,true),(10,false)],[(1,false),(7,true),(3,true),(12,false),(11,false),(6,true),(9,true)])
                      (.node 1961987 ([(5,false),(4,false),(13,true),(2,true),(8,true),(0,true),(10,false)],[(1,false),(11,true),(12,true),(3,false),(7,false),(6,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1964093 ([(7,true),(2,false),(13,false),(12,false),(6,true),(0,true),(9,true)],[(1,false),(8,false),(3,true),(4,true),(5,true),(11,false),(10,false)])
                        .empty
                        .empty))))))
            (.node 1976099 ([(5,false),(4,false),(3,false),(2,false),(1,false),(0,false),(10,false)],[(13,false),(12,false),(11,false),(6,false),(7,true),(8,true),(9,true)])
              (.node 1968095 ([(3,true),(4,true),(13,true),(1,false),(0,false),(6,false),(9,true)],[(2,true),(7,true),(8,true),(5,false),(12,false),(11,false),(10,false)])
                (.node 1967543 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                  (.node 1964609 ([(3,true),(13,true),(1,false),(0,false),(6,false),(5,false),(9,true)],[(2,true),(7,true),(8,true),(4,false),(12,false),(11,false),(10,false)])
                    (.node 1964513 ([(5,true),(6,true),(0,true),(1,true),(13,false),(3,false),(9,true)],[(2,true),(8,false),(7,false),(4,false),(12,false),(11,false),(10,false)])
                      (.node 1964399 ([(3,true),(13,true),(1,false),(11,true),(5,false),(8,true),(9,true)],[(2,true),(7,true),(4,false),(12,false),(6,true),(0,true),(10,false)])
                        (.node 1964387 ([(5,true),(6,true),(8,false),(3,true),(13,true),(1,false),(10,false)],[(2,true),(7,false),(4,false),(12,false),(11,false),(0,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1964543 ([(0,true),(1,true),(13,false),(12,false),(5,false),(8,true),(9,true)],[(2,true),(3,true),(4,true),(7,false),(6,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1965131 ([(0,true),(1,true),(13,false),(4,true),(5,true),(11,false),(10,false)],[(2,true),(3,true),(12,false),(6,true),(7,true),(8,true),(9,true)])
                      (.node 1965083 ([(1,true),(2,true),(3,true),(12,false),(5,false),(8,true),(9,true)],[(13,false),(4,true),(7,false),(0,false),(6,false),(11,false),(10,false)])
                        (.node 1964627 ([(0,true),(1,true),(2,true),(3,true),(12,false),(5,false),(9,true)],[(13,false),(4,true),(8,false),(7,false),(6,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1967531 ([(6,true),(0,true),(1,true),(13,false),(4,false),(3,false),(10,false)],[(2,true),(11,true),(12,true),(5,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)))
                  (.node 1967867 ([(6,true),(11,false),(4,true),(13,true),(2,true),(8,true),(9,true)],[(1,false),(0,false),(12,true),(5,true),(7,true),(3,true),(10,false)])
                    (.node 1967753 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                      (.node 1967687 ([(1,true),(2,true),(11,true),(6,false),(5,false),(4,false),(9,true)],[(13,false),(12,false),(0,true),(7,true),(8,true),(3,false),(10,false)])
                        (.node 1967657 ([(6,true),(0,true),(1,true),(13,false),(4,false),(3,false),(10,false)],[(2,true),(11,true),(12,true),(5,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1967771 ([(1,true),(2,true),(3,true),(4,true),(12,false),(6,false),(9,true)],[(13,false),(5,true),(8,false),(7,false),(0,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1967951 ([(6,true),(0,true),(1,true),(13,false),(4,false),(3,false),(9,true)],[(2,true),(8,false),(7,false),(5,false),(12,false),(11,false),(10,false)])
                      (.node 1967885 ([(3,true),(11,true),(6,false),(5,false),(13,true),(1,false),(9,true)],[(2,true),(7,true),(8,true),(0,false),(12,true),(4,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1967981 ([(1,true),(2,true),(8,false),(6,true),(12,true),(4,false),(10,false)],[(13,false),(5,true),(7,false),(0,false),(11,false),(3,false),(9,true)])
                        .empty
                        .empty))))
                (.node 1973717 ([(4,true),(5,true),(6,true),(11,true),(2,false),(1,false),(9,true)],[(13,false),(12,false),(3,true),(7,true),(8,true),(0,false),(10,false)])
                  (.node 1970507 ([(0,true),(1,true),(2,true),(8,true),(5,false),(4,false),(10,false)],[(13,false),(12,false),(11,false),(3,false),(7,false),(6,false),(9,true)])
                    (.node 1970171 ([(0,true),(1,true),(13,false),(5,true),(8,false),(3,false),(10,false)],[(2,true),(11,true),(12,true),(4,false),(7,false),(6,false),(9,true)])
                      (.node 1969883 ([(6,true),(0,true),(1,true),(13,false),(4,false),(3,false),(10,false)],[(2,true),(11,true),(12,true),(5,true),(7,true),(8,true),(9,true)])
                        (.node 1968107 ([(1,true),(2,true),(3,true),(4,true),(12,false),(6,false),(9,true)],[(13,false),(5,true),(8,false),(7,false),(0,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1970219 ([(6,true),(0,true),(12,true),(13,true),(2,true),(3,true),(10,false)],[(1,false),(11,false),(4,true),(5,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1971077 ([(3,true),(8,false),(0,true),(1,true),(13,false),(5,true),(10,false)],[(2,true),(7,true),(6,false),(11,true),(12,true),(4,false),(9,true)])
                      (.node 1971029 ([(4,true),(12,false),(1,true),(2,true),(8,false),(6,false),(10,false)],[(13,false),(5,true),(11,true),(0,false),(7,false),(3,false),(9,true)])
                        .empty
                        .empty)
                      (.node 1973705 ([(6,true),(11,true),(3,true),(4,true),(13,true),(1,false),(9,true)],[(2,true),(12,true),(5,true),(7,true),(8,true),(0,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 1973999 ([(6,true),(8,false),(4,true),(12,false),(2,false),(1,false),(10,false)],[(13,false),(5,true),(7,true),(3,false),(11,false),(0,false),(9,true)])
                    (.node 1973927 ([(4,true),(5,true),(8,false),(1,true),(2,true),(11,false),(10,false)],[(13,false),(12,false),(3,true),(7,true),(0,false),(6,false),(9,true)])
                      (.node 1973861 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                        (.node 1973831 ([(6,true),(0,true),(1,true),(2,true),(12,true),(4,false),(9,true)],[(13,false),(5,true),(7,true),(8,true),(3,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1973945 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1975709 ([(1,true),(2,true),(11,false),(5,false),(4,false),(8,true),(9,true)],[(13,false),(12,false),(3,true),(7,false),(0,false),(6,false),(10,false)])
                      (.node 1974287 ([(0,true),(1,true),(2,true),(12,true),(4,false),(8,true),(9,true)],[(13,false),(5,true),(6,true),(7,true),(3,false),(11,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1975757 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)))))
              (.node 1987247 ([(3,true),(11,true),(1,true),(13,false),(6,true),(8,true),(9,true)],[(2,true),(7,true),(0,true),(12,true),(5,false),(4,false),(10,false)])
                (.node 1984853 ([(3,true),(11,true),(6,false),(13,true),(1,false),(8,true),(9,true)],[(2,true),(7,true),(0,false),(12,true),(5,false),(4,false),(10,false)])
                  (.node 1978103 ([(0,false),(8,false),(2,false),(13,false),(4,false),(11,false),(10,false)],[(1,false),(7,true),(3,true),(12,true),(5,true),(6,true),(9,true)])
                    (.node 1976339 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                      (.node 1976327 ([(3,true),(4,true),(13,true),(1,false),(0,false),(6,false),(9,true)],[(2,true),(7,true),(8,true),(5,false),(12,false),(11,false),(10,false)])
                        (.node 1976117 ([(3,true),(4,true),(13,true),(1,false),(8,false),(6,true),(10,false)],[(2,true),(7,true),(5,false),(12,false),(11,false),(0,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1976393 ([(6,true),(8,false),(3,true),(4,true),(13,true),(1,false),(10,false)],[(2,true),(7,false),(5,false),(12,false),(11,false),(0,false),(9,true)])
                        .empty
                        .empty))
                    (.node 1984757 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                      (.node 1984463 ([(5,true),(6,true),(11,false),(2,false),(1,false),(8,true),(9,true)],[(13,false),(12,false),(0,true),(7,false),(4,false),(3,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1984781 ([(1,true),(2,true),(8,false),(5,true),(6,true),(11,false),(10,false)],[(13,false),(12,false),(0,true),(7,true),(4,false),(3,false),(9,true)])
                        .empty
                        .empty)))
                  (.node 1987025 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                    (.node 1986857 ([(5,true),(13,true),(1,false),(0,false),(8,true),(3,false),(10,false)],[(2,true),(11,true),(12,true),(6,true),(7,false),(4,false),(9,true)])
                      (.node 1985147 ([(3,true),(8,false),(1,true),(13,false),(6,true),(11,false),(10,false)],[(2,true),(7,true),(0,false),(12,true),(5,false),(4,false),(9,true)])
                        (.node 1984865 ([(1,true),(2,true),(3,true),(11,true),(6,false),(5,false),(9,true)],[(13,false),(12,false),(0,true),(7,true),(8,true),(4,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1986905 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1987151 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                      (.node 1987037 ([(3,true),(4,true),(5,true),(13,true),(1,false),(0,false),(9,true)],[(2,true),(7,true),(8,true),(6,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty)
                      (.node 1987181 ([(0,true),(1,true),(13,false),(5,false),(4,false),(3,false),(9,true)],[(2,true),(8,false),(7,false),(6,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty))))
                (.node 1992221 ([(0,true),(1,true),(13,false),(12,false),(3,true),(4,true),(10,false)],[(2,true),(11,false),(5,true),(6,true),(7,true),(8,true),(9,true)])
                  (.node 1990685 ([(4,true),(5,true),(12,false),(2,false),(1,false),(0,false),(10,false)],[(13,false),(6,true),(11,true),(3,true),(7,true),(8,true),(9,true)])
                    (.node 1987541 ([(3,true),(8,false),(6,false),(13,true),(1,false),(11,false),(10,false)],[(2,true),(7,true),(0,true),(12,true),(5,false),(4,false),(9,true)])
                      (.node 1987493 ([(4,true),(5,true),(13,true),(1,false),(0,false),(8,true),(9,true)],[(2,true),(3,true),(7,true),(6,false),(12,false),(11,false),(10,false)])
                        (.node 1987265 ([(0,true),(1,true),(13,false),(5,false),(8,false),(3,true),(10,false)],[(2,true),(7,false),(6,false),(12,false),(11,false),(4,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1990637 ([(5,true),(6,true),(11,true),(2,false),(1,false),(8,true),(9,true)],[(13,false),(12,false),(3,true),(4,true),(7,true),(0,false),(10,false)])
                        .empty
                        .empty))
                    (.node 1991021 ([(4,true),(8,false),(6,false),(13,true),(2,true),(11,false),(10,false)],[(1,false),(0,false),(7,false),(3,false),(12,true),(5,false),(9,true)])
                      (.node 1990973 ([(5,true),(6,true),(8,true),(3,false),(2,false),(1,false),(10,false)],[(13,false),(12,false),(11,false),(0,false),(7,false),(4,false),(9,true)])
                        .empty
                        .empty)
                      (.node 1992173 ([(1,true),(2,true),(3,true),(8,true),(6,false),(5,false),(10,false)],[(13,false),(12,false),(11,false),(4,false),(7,false),(0,false),(9,true)])
                        .empty
                        .empty)))
                  (.node 1993085 ([(3,true),(4,true),(8,false),(1,true),(13,false),(6,true),(10,false)],[(2,true),(7,true),(0,false),(11,true),(12,true),(5,false),(9,true)])
                    (.node 1992989 ([(5,true),(12,false),(3,false),(2,false),(1,false),(0,false),(10,false)],[(13,false),(6,true),(11,true),(4,true),(7,true),(8,true),(9,true)])
                      (.node 1992917 ([(3,true),(4,true),(8,true),(1,true),(13,false),(6,true),(10,false)],[(2,true),(7,true),(5,true),(12,false),(11,false),(0,true),(9,true)])
                        (.node 1992905 ([(5,true),(6,true),(11,true),(3,false),(2,false),(1,false),(9,true)],[(13,false),(12,false),(4,true),(7,true),(8,true),(0,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 1993013 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 1993199 ([(5,true),(12,false),(3,false),(2,false),(1,false),(0,false),(9,true)],[(13,false),(6,true),(8,false),(7,false),(4,false),(11,false),(10,false)])
                      (.node 1993097 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 1993211 ([(3,true),(4,true),(5,true),(13,true),(1,false),(0,false),(9,true)],[(2,true),(7,true),(8,true),(6,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty)))))))
          (.node 2033159 ([(2,true),(3,true),(8,false),(0,true),(12,false),(5,false),(10,false)],[(13,false),(1,true),(7,true),(6,false),(11,false),(4,false),(9,true)])
            (.node 2013047 ([(1,true),(2,true),(3,true),(4,true),(12,true),(6,false),(9,true)],[(13,false),(0,true),(7,true),(8,true),(5,false),(11,false),(10,false)])
              (.node 2007149 ([(4,true),(8,false),(0,false),(13,true),(2,false),(11,false),(10,false)],[(3,true),(7,true),(1,true),(12,true),(6,false),(5,false),(9,true)])
                (.node 2006465 ([(6,true),(13,true),(2,false),(1,false),(8,true),(4,false),(10,false)],[(3,true),(11,true),(12,true),(0,true),(7,false),(5,false),(9,true)])
                  (.node 2004365 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                    (.node 1993439 ([(0,true),(1,true),(2,true),(3,true),(12,true),(5,false),(9,true)],[(13,false),(6,true),(7,true),(8,true),(4,false),(11,false),(10,false)])
                      (.node 1993421 ([(3,true),(4,true),(8,false),(6,false),(13,true),(1,false),(10,false)],[(2,true),(7,true),(0,true),(11,true),(12,true),(5,false),(9,true)])
                        (.node 1993355 ([(0,true),(1,true),(13,false),(5,false),(4,false),(3,false),(9,true)],[(2,true),(8,false),(7,false),(6,false),(12,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2004071 ([(6,true),(0,true),(11,false),(3,false),(2,false),(8,true),(9,true)],[(13,false),(12,false),(1,true),(7,false),(5,false),(4,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2004473 ([(2,true),(3,true),(4,true),(11,true),(0,false),(6,false),(9,true)],[(13,false),(12,false),(1,true),(7,true),(8,true),(5,false),(10,false)])
                      (.node 2004461 ([(4,true),(11,true),(0,false),(13,true),(2,false),(8,true),(9,true)],[(3,true),(7,true),(1,false),(12,true),(6,false),(5,false),(10,false)])
                        (.node 2004389 ([(2,true),(3,true),(8,false),(6,true),(0,true),(11,false),(10,false)],[(13,false),(12,false),(1,true),(7,true),(5,false),(4,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2004755 ([(4,true),(8,false),(2,true),(13,false),(0,true),(11,false),(10,false)],[(3,true),(7,true),(1,false),(12,true),(6,false),(5,false),(9,true)])
                        .empty
                        .empty)))
                  (.node 2006789 ([(1,true),(2,true),(13,false),(6,false),(5,false),(4,false),(9,true)],[(3,true),(8,false),(7,false),(0,false),(12,false),(11,false),(10,false)])
                    (.node 2006645 ([(4,true),(5,true),(6,true),(13,true),(2,false),(1,false),(9,true)],[(3,true),(7,true),(8,true),(0,false),(12,false),(11,false),(10,false)])
                      (.node 2006633 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                        (.node 2006513 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2006759 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2006873 ([(1,true),(2,true),(13,false),(6,false),(8,false),(4,true),(10,false)],[(3,true),(7,false),(0,false),(12,false),(11,false),(5,true),(9,true)])
                      (.node 2006855 ([(4,true),(11,true),(2,true),(13,false),(0,true),(8,true),(9,true)],[(3,true),(7,true),(1,true),(12,true),(6,false),(5,false),(10,false)])
                        .empty
                        .empty)
                      (.node 2007101 ([(5,true),(6,true),(13,true),(2,false),(1,false),(8,true),(9,true)],[(3,true),(4,true),(7,true),(0,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty))))
                (.node 2012597 ([(6,true),(12,false),(4,false),(3,false),(2,false),(1,false),(10,false)],[(13,false),(0,true),(11,true),(5,true),(7,true),(8,true),(9,true)])
                  (.node 2011781 ([(2,true),(3,true),(4,true),(8,true),(0,false),(6,false),(10,false)],[(13,false),(12,false),(11,false),(5,false),(7,false),(1,false),(9,true)])
                    (.node 2010581 ([(6,true),(0,true),(8,true),(4,false),(3,false),(2,false),(10,false)],[(13,false),(12,false),(11,false),(1,false),(7,false),(5,false),(9,true)])
                      (.node 2010293 ([(5,true),(6,true),(12,false),(3,false),(2,false),(1,false),(10,false)],[(13,false),(0,true),(11,true),(4,true),(7,true),(8,true),(9,true)])
                        (.node 2010245 ([(6,true),(0,true),(11,true),(3,false),(2,false),(8,true),(9,true)],[(13,false),(12,false),(4,true),(5,true),(7,true),(1,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2010629 ([(5,true),(8,false),(0,false),(13,true),(3,true),(11,false),(10,false)],[(2,false),(1,false),(7,false),(4,false),(12,true),(6,false),(9,true)])
                        .empty
                        .empty))
                    (.node 2012513 ([(6,true),(0,true),(11,true),(4,false),(3,false),(2,false),(9,true)],[(13,false),(12,false),(5,true),(7,true),(8,true),(1,false),(10,false)])
                      (.node 2011829 ([(1,true),(2,true),(13,false),(12,false),(4,true),(5,true),(10,false)],[(3,true),(11,false),(6,true),(0,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2012525 ([(4,true),(5,true),(8,true),(2,true),(13,false),(0,true),(10,false)],[(3,true),(7,true),(6,true),(12,false),(11,false),(1,true),(9,true)])
                        .empty
                        .empty)))
                  (.node 2012819 ([(4,true),(5,true),(6,true),(13,true),(2,false),(1,false),(9,true)],[(3,true),(7,true),(8,true),(0,false),(12,false),(11,false),(10,false)])
                    (.node 2012705 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                      (.node 2012693 ([(4,true),(5,true),(8,false),(2,true),(13,false),(0,true),(10,false)],[(3,true),(7,true),(1,false),(11,true),(12,true),(6,false),(9,true)])
                        (.node 2012621 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2012807 ([(6,true),(12,false),(4,false),(3,false),(2,false),(1,false),(9,true)],[(13,false),(0,true),(8,false),(7,false),(5,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2012963 ([(1,true),(2,true),(13,false),(6,false),(5,false),(4,false),(9,true)],[(3,true),(8,false),(7,false),(0,false),(12,false),(11,false),(10,false)])
                      (.node 2012933 ([(5,false),(4,false),(3,false),(13,false),(0,true),(1,true),(10,false)],[(2,false),(11,true),(12,true),(6,false),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2013029 ([(4,true),(5,true),(8,false),(0,false),(13,true),(2,false),(10,false)],[(3,true),(7,true),(1,true),(11,true),(12,true),(6,false),(9,true)])
                        .empty
                        .empty)))))
              (.node 2028977 ([(6,true),(0,true),(12,false),(4,false),(3,false),(2,false),(9,true)],[(13,false),(1,true),(8,false),(7,false),(5,false),(11,false),(10,false)])
                (.node 2026709 ([(6,true),(0,true),(12,false),(3,false),(2,false),(8,true),(9,true)],[(13,false),(1,true),(7,false),(5,false),(4,false),(11,false),(10,false)])
                  (.node 2018879 ([(2,true),(13,false),(0,false),(6,false),(8,false),(4,true),(10,false)],[(3,true),(7,false),(1,false),(12,false),(11,false),(5,true),(9,true)])
                    (.node 2018795 ([(2,true),(13,false),(0,false),(6,false),(5,false),(4,false),(9,true)],[(3,true),(8,false),(7,false),(1,false),(12,false),(11,false),(10,false)])
                      (.node 2018771 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                        (.node 2018477 ([(6,true),(0,true),(13,true),(2,false),(8,true),(4,false),(10,false)],[(3,true),(11,true),(12,true),(1,true),(7,false),(5,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2018867 ([(4,true),(11,true),(0,true),(13,true),(2,false),(8,true),(9,true)],[(3,true),(7,true),(1,false),(12,false),(6,false),(5,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2023679 ([(0,true),(1,true),(2,true),(3,true),(8,true),(5,false),(10,false)],[(13,false),(12,false),(11,false),(4,false),(7,false),(6,false),(9,true)])
                      (.node 2019161 ([(4,true),(8,false),(2,true),(13,false),(0,false),(6,false),(10,false)],[(3,true),(7,true),(1,false),(12,false),(11,false),(5,false),(9,true)])
                        .empty
                        .empty)
                      (.node 2023949 ([(3,false),(2,false),(1,false),(0,false),(8,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,false),(4,true),(9,true)])
                        .empty
                        .empty)))
                  (.node 2028605 ([(5,true),(6,true),(0,true),(12,false),(3,false),(2,false),(9,true)],[(13,false),(1,true),(8,false),(7,false),(4,false),(11,false),(10,false)])
                    (.node 2028521 ([(5,true),(11,true),(3,false),(2,false),(1,false),(0,false),(9,true)],[(13,false),(12,false),(4,true),(7,true),(8,true),(6,false),(10,false)])
                      (.node 2028467 ([(6,false),(8,false),(1,false),(13,true),(3,true),(4,true),(10,false)],[(2,false),(7,false),(0,true),(12,false),(11,false),(5,true),(9,true)])
                        (.node 2026757 ([(5,true),(8,false),(1,false),(13,true),(3,true),(11,false),(10,false)],[(2,false),(7,false),(4,false),(12,true),(0,false),(6,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2028539 ([(2,true),(3,true),(12,true),(0,false),(8,false),(5,true),(10,false)],[(13,false),(1,true),(7,true),(4,false),(11,false),(6,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2028749 ([(2,true),(3,true),(12,true),(0,false),(6,false),(5,false),(9,true)],[(13,false),(1,true),(7,true),(8,true),(4,false),(11,false),(10,false)])
                      (.node 2028635 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2028761 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))))
                (.node 2030933 ([(2,true),(3,true),(8,true),(0,true),(12,false),(5,true),(10,false)],[(13,false),(1,true),(7,true),(4,true),(11,false),(6,true),(9,true)])
                  (.node 2029169 ([(2,true),(3,true),(4,true),(12,true),(0,false),(6,false),(9,true)],[(13,false),(1,true),(7,true),(8,true),(5,false),(11,false),(10,false)])
                    (.node 2029085 ([(2,true),(3,true),(8,false),(5,false),(12,true),(0,false),(10,false)],[(13,false),(1,true),(7,true),(6,true),(11,true),(4,false),(9,true)])
                      (.node 2029061 ([(6,true),(11,true),(12,true),(13,true),(2,false),(8,true),(9,true)],[(3,true),(4,true),(5,true),(7,true),(1,false),(0,false),(10,false)])
                        (.node 2028989 ([(4,true),(5,true),(6,true),(0,true),(13,true),(2,false),(9,true)],[(3,true),(7,true),(8,true),(1,false),(12,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2029157 ([(4,true),(5,true),(8,false),(2,true),(13,false),(0,false),(10,false)],[(3,true),(7,true),(1,false),(12,false),(11,false),(6,false),(9,true)])
                        .empty
                        .empty))
                    (.node 2029853 ([(0,true),(12,false),(5,true),(8,false),(3,false),(2,false),(10,false)],[(13,false),(1,true),(11,true),(4,false),(7,false),(6,false),(9,true)])
                      (.node 2029565 ([(6,true),(0,true),(12,false),(4,false),(3,false),(2,false),(10,false)],[(13,false),(1,true),(11,true),(5,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2030921 ([(3,false),(2,false),(1,false),(12,false),(5,true),(6,true),(9,true)],[(13,false),(0,false),(8,false),(7,false),(4,true),(11,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 2032721 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                    (.node 2032637 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                      (.node 2032181 ([(4,true),(8,false),(6,false),(12,true),(13,true),(2,false),(10,false)],[(3,true),(7,true),(0,true),(1,true),(11,true),(5,false),(9,true)])
                        (.node 2032133 ([(5,true),(6,true),(8,true),(3,false),(13,false),(1,true),(10,false)],[(2,false),(11,true),(12,true),(0,false),(7,false),(4,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2032655 ([(2,true),(3,true),(4,true),(5,true),(12,true),(0,false),(9,true)],[(13,false),(1,true),(7,true),(8,true),(6,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2032865 ([(2,true),(3,true),(11,true),(12,true),(0,false),(8,true),(9,true)],[(13,false),(1,true),(7,true),(6,false),(5,false),(4,false),(10,false)])
                      (.node 2032751 ([(0,true),(12,false),(5,false),(4,false),(3,false),(2,false),(9,true)],[(13,false),(1,true),(8,false),(7,false),(6,false),(11,false),(10,false)])
                        .empty
                        .empty)
                      (.node 2032877 ([(0,true),(1,true),(2,true),(3,true),(11,true),(5,false),(9,true)],[(13,false),(12,false),(6,true),(7,true),(8,true),(4,false),(10,false)])
                        .empty
                        .empty))))))
            (.node 2098919 ([(3,false),(13,false),(5,true),(6,true),(0,true),(1,true),(9,true)],[(2,false),(8,false),(7,false),(4,true),(12,false),(11,false),(10,false)])
              (.node 2088629 ([(4,true),(13,true),(2,false),(8,false),(0,true),(11,false),(10,false)],[(3,true),(7,true),(6,false),(5,false),(12,false),(1,true),(9,true)])
                (.node 2085077 ([(1,true),(2,true),(3,true),(4,true),(12,false),(6,false),(9,true)],[(13,false),(5,true),(8,false),(7,false),(0,false),(11,false),(10,false)])
                  (.node 2084849 ([(4,true),(13,true),(2,false),(11,true),(6,false),(8,true),(9,true)],[(3,true),(7,true),(5,false),(12,false),(0,true),(1,true),(10,false)])
                    (.node 2084555 ([(4,true),(13,true),(2,false),(8,false),(6,true),(0,true),(10,false)],[(3,true),(7,true),(5,false),(12,false),(11,false),(1,true),(9,true)])
                      (.node 2084543 ([(7,true),(3,false),(13,false),(12,false),(0,true),(1,true),(9,true)],[(2,false),(8,false),(4,true),(5,true),(6,true),(11,false),(10,false)])
                        (.node 2033171 ([(7,true),(2,true),(13,false),(12,false),(5,false),(4,false),(9,true)],[(3,true),(8,false),(1,false),(0,false),(6,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2084837 ([(6,true),(0,true),(8,false),(4,true),(13,true),(2,false),(10,false)],[(3,true),(7,false),(5,false),(12,false),(11,false),(1,false),(9,true)])
                        .empty
                        .empty))
                    (.node 2084993 ([(1,true),(2,true),(13,false),(12,false),(6,false),(8,true),(9,true)],[(3,true),(4,true),(5,true),(7,false),(0,false),(11,false),(10,false)])
                      (.node 2084963 ([(6,true),(0,true),(1,true),(2,true),(13,false),(4,false),(9,true)],[(3,true),(8,false),(7,false),(5,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty)
                      (.node 2085059 ([(4,true),(13,true),(2,false),(1,false),(0,false),(6,false),(9,true)],[(3,true),(7,true),(8,true),(5,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 2087861 ([(6,true),(0,true),(1,true),(2,true),(13,false),(4,false),(10,false)],[(3,true),(11,true),(12,true),(5,true),(7,true),(8,true),(9,true)])
                    (.node 2086781 ([(4,true),(13,true),(2,false),(1,false),(0,false),(6,false),(9,true)],[(3,true),(7,true),(8,true),(5,false),(12,false),(11,false),(10,false)])
                      (.node 2085581 ([(1,true),(2,true),(13,false),(5,true),(6,true),(11,false),(10,false)],[(3,true),(4,true),(12,false),(0,true),(7,true),(8,true),(9,true)])
                        (.node 2085533 ([(2,true),(3,true),(4,true),(12,false),(6,false),(8,true),(9,true)],[(13,false),(5,true),(7,false),(1,false),(0,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2086793 ([(2,true),(3,true),(4,true),(12,false),(0,false),(6,false),(9,true)],[(13,false),(5,true),(8,false),(7,false),(1,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2088545 ([(4,true),(13,true),(2,false),(1,false),(11,false),(6,true),(9,true)],[(3,true),(7,true),(8,true),(0,true),(12,true),(5,true),(10,false)])
                      (.node 2088149 ([(0,true),(12,true),(4,false),(3,false),(2,false),(8,true),(9,true)],[(13,false),(5,true),(6,true),(7,true),(1,false),(11,false),(10,false)])
                        .empty
                        .empty)
                      (.node 2088557 ([(2,true),(3,true),(4,true),(5,true),(11,true),(0,false),(9,true)],[(13,false),(12,false),(1,true),(7,true),(8,true),(6,false),(10,false)])
                        .empty
                        .empty))))
                (.node 2089193 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                  (.node 2088965 ([(4,true),(13,true),(2,false),(1,false),(8,false),(6,true),(10,false)],[(3,true),(7,true),(5,false),(12,false),(11,false),(0,true),(9,true)])
                    (.node 2088737 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                      (.node 2088725 ([(2,true),(3,true),(4,true),(12,false),(0,false),(6,false),(10,false)],[(13,false),(5,true),(11,true),(1,true),(7,true),(8,true),(9,true)])
                        (.node 2088653 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2088953 ([(6,true),(11,true),(2,true),(13,false),(4,false),(8,true),(9,true)],[(3,true),(7,false),(5,false),(12,false),(1,false),(0,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2089109 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                      (.node 2089079 ([(6,true),(0,true),(1,true),(2,true),(13,false),(4,false),(9,true)],[(3,true),(8,false),(7,false),(5,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty)
                      (.node 2089175 ([(4,true),(13,true),(2,false),(1,false),(0,false),(6,false),(9,true)],[(3,true),(7,true),(8,true),(5,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 2094035 ([(6,true),(8,false),(2,true),(13,false),(4,false),(11,false),(10,false)],[(3,true),(12,true),(5,true),(7,true),(1,false),(0,false),(9,true)])
                    (.node 2091005 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                      (.node 2090957 ([(1,true),(11,false),(5,false),(13,true),(3,true),(8,true),(9,true)],[(2,false),(12,true),(4,false),(7,false),(0,false),(6,false),(10,false)])
                        (.node 2089247 ([(6,true),(8,false),(4,true),(13,true),(2,false),(1,false),(10,false)],[(3,true),(7,false),(5,false),(12,false),(11,false),(0,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2093765 ([(2,true),(3,true),(4,true),(5,true),(8,true),(0,false),(10,false)],[(13,false),(12,false),(11,false),(6,false),(7,false),(1,false),(9,true)])
                        .empty
                        .empty))
                    (.node 2098835 ([(3,false),(13,false),(5,true),(6,true),(8,false),(1,false),(10,false)],[(2,false),(7,false),(4,true),(12,false),(11,false),(0,false),(9,true)])
                      (.node 2098553 ([(1,false),(8,false),(3,false),(13,false),(5,true),(6,true),(10,false)],[(2,false),(7,true),(4,true),(12,false),(11,false),(0,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2098847 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)))))
              (.node 2107133 ([(0,true),(1,true),(2,true),(13,false),(5,false),(4,false),(10,false)],[(3,true),(11,true),(12,true),(6,true),(7,true),(8,true),(9,true)])
                (.node 2105009 ([(4,true),(5,true),(13,true),(2,false),(1,false),(0,false),(9,true)],[(3,true),(7,true),(8,true),(6,false),(12,false),(11,false),(10,false)])
                  (.node 2104751 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                    (.node 2104667 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                      (.node 2099237 ([(6,false),(5,false),(13,true),(3,true),(8,true),(1,true),(10,false)],[(2,false),(11,true),(12,true),(4,false),(7,false),(0,true),(9,true)])
                        (.node 2098943 ([(0,true),(11,true),(5,false),(4,false),(3,false),(2,false),(9,true)],[(13,false),(12,false),(6,true),(7,true),(8,true),(1,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2104685 ([(2,true),(3,true),(4,true),(5,true),(12,false),(0,false),(9,true)],[(13,false),(6,true),(8,false),(7,false),(1,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2104895 ([(2,true),(3,true),(11,true),(0,false),(6,false),(5,false),(9,true)],[(13,false),(12,false),(1,true),(7,true),(8,true),(4,false),(10,false)])
                      (.node 2104781 ([(0,true),(1,true),(2,true),(13,false),(5,false),(4,false),(10,false)],[(3,true),(11,true),(12,true),(6,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2104907 ([(0,true),(1,true),(2,true),(13,false),(5,false),(4,false),(10,false)],[(3,true),(11,true),(12,true),(6,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)))
                  (.node 2105201 ([(0,true),(1,true),(2,true),(13,false),(5,false),(4,false),(9,true)],[(3,true),(8,false),(7,false),(6,false),(12,false),(11,false),(10,false)])
                    (.node 2105117 ([(0,true),(11,false),(5,true),(13,true),(3,true),(8,true),(9,true)],[(2,false),(1,false),(12,true),(6,true),(7,true),(4,true),(10,false)])
                      (.node 2105093 ([(4,true),(11,true),(0,false),(6,false),(13,true),(2,false),(9,true)],[(3,true),(7,true),(8,true),(1,false),(12,true),(5,false),(10,false)])
                        (.node 2105021 ([(2,true),(3,true),(4,true),(5,true),(12,false),(0,false),(9,true)],[(13,false),(6,true),(8,false),(7,false),(1,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2105189 ([(2,true),(3,true),(8,false),(0,true),(12,true),(5,false),(10,false)],[(13,false),(6,true),(7,false),(1,false),(11,false),(4,false),(9,true)])
                        .empty
                        .empty))
                    (.node 2105933 ([(4,true),(8,false),(1,true),(2,true),(13,false),(6,true),(10,false)],[(3,true),(7,true),(0,false),(11,true),(12,true),(5,false),(9,true)])
                      (.node 2105885 ([(5,true),(12,false),(2,true),(3,true),(8,false),(0,false),(10,false)],[(13,false),(6,true),(11,true),(1,false),(7,false),(4,false),(9,true)])
                        .empty
                        .empty)
                      (.node 2107085 ([(1,true),(2,true),(13,false),(6,true),(8,false),(4,false),(10,false)],[(3,true),(11,true),(12,true),(5,false),(7,false),(0,false),(9,true)])
                        .empty
                        .empty))))
                (.node 2111069 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                  (.node 2110841 ([(5,true),(6,true),(8,false),(2,true),(3,true),(11,false),(10,false)],[(13,false),(12,false),(4,true),(7,true),(1,false),(0,false),(9,true)])
                    (.node 2110565 ([(2,true),(3,true),(11,false),(6,false),(5,false),(8,true),(9,true)],[(13,false),(12,false),(4,true),(7,false),(1,false),(0,false),(10,false)])
                      (.node 2107469 ([(0,true),(1,true),(12,true),(13,true),(3,true),(4,true),(10,false)],[(2,false),(11,false),(5,true),(6,true),(7,true),(8,true),(9,true)])
                        (.node 2107421 ([(1,true),(2,true),(3,true),(8,true),(6,false),(5,false),(10,false)],[(13,false),(12,false),(11,false),(4,false),(7,false),(0,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2110613 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2110925 ([(5,true),(6,true),(0,true),(11,true),(3,false),(2,false),(9,true)],[(13,false),(12,false),(4,true),(7,true),(8,true),(1,false),(10,false)])
                      (.node 2110859 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2110955 ([(0,true),(11,true),(4,true),(5,true),(13,true),(2,false),(9,true)],[(3,true),(12,true),(6,true),(7,true),(8,true),(1,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 2113241 ([(4,true),(5,true),(13,true),(2,false),(1,false),(0,false),(9,true)],[(3,true),(7,true),(8,true),(6,false),(12,false),(11,false),(10,false)])
                    (.node 2111249 ([(0,true),(8,false),(5,true),(12,false),(3,false),(2,false),(10,false)],[(13,false),(6,true),(7,true),(4,false),(11,false),(1,false),(9,true)])
                      (.node 2111201 ([(1,true),(2,true),(3,true),(12,true),(5,false),(8,true),(9,true)],[(13,false),(6,true),(0,true),(7,true),(4,false),(11,false),(10,false)])
                        (.node 2111081 ([(0,true),(1,true),(2,true),(3,true),(12,true),(5,false),(9,true)],[(13,false),(6,true),(7,true),(8,true),(4,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2112959 ([(1,false),(8,false),(3,false),(13,false),(5,false),(11,false),(10,false)],[(2,false),(7,true),(4,true),(12,true),(6,true),(0,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2113325 ([(4,true),(5,true),(13,true),(2,false),(8,false),(0,true),(10,false)],[(3,true),(7,true),(6,false),(12,false),(11,false),(1,true),(9,true)])
                      (.node 2113253 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2113349 ([(6,false),(5,false),(4,false),(3,false),(2,false),(1,false),(10,false)],[(13,false),(12,false),(11,false),(0,false),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)))))))))))
  (.node 3239502 ([(0,true),(1,true),(8,true),(3,false),(13,true),(5,false),(11,false)],[(6,true),(7,true),(2,true),(12,false),(4,false),(9,true),(10,true)])
    (.node 2670636 ([(3,true),(12,false),(5,false),(8,true),(0,true),(1,true),(10,true)],[(13,false),(4,true),(7,false),(2,false),(9,false),(6,false),(11,false)])
      (.node 2376503 ([(2,false),(1,false),(13,true),(6,true),(8,true),(4,true),(10,false)],[(5,false),(11,true),(12,true),(0,false),(7,false),(3,true),(9,true)])
        (.node 2238977 ([(5,false),(13,false),(0,true),(1,true),(2,true),(3,true),(9,true)],[(4,false),(8,false),(7,false),(6,true),(12,false),(11,false),(10,false)])
          (.node 2153171 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
            (.node 2141375 ([(5,true),(11,true),(1,false),(13,true),(3,false),(8,true),(9,true)],[(4,true),(7,true),(2,false),(12,true),(0,false),(6,false),(10,false)])
              (.node 2130173 ([(3,true),(4,true),(11,false),(0,false),(6,false),(8,true),(9,true)],[(13,false),(12,false),(5,true),(7,false),(2,false),(1,false),(10,false)])
                (.node 2124725 ([(1,true),(11,false),(6,true),(13,true),(4,true),(8,true),(9,true)],[(3,false),(2,false),(12,true),(0,true),(7,true),(5,true),(10,false)])
                  (.node 2124503 ([(3,true),(4,true),(11,true),(1,false),(0,false),(6,false),(9,true)],[(13,false),(12,false),(2,true),(7,true),(8,true),(5,false),(10,false)])
                    (.node 2124359 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                      (.node 2124293 ([(3,true),(4,true),(5,true),(6,true),(12,false),(1,false),(9,true)],[(13,false),(0,true),(8,false),(7,false),(2,false),(11,false),(10,false)])
                        (.node 2124275 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2124389 ([(1,true),(2,true),(3,true),(13,false),(6,false),(5,false),(10,false)],[(4,true),(11,true),(12,true),(0,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2124629 ([(3,true),(4,true),(5,true),(6,true),(12,false),(1,false),(9,true)],[(13,false),(0,true),(8,false),(7,false),(2,false),(11,false),(10,false)])
                      (.node 2124617 ([(5,true),(6,true),(13,true),(3,false),(2,false),(1,false),(9,true)],[(4,true),(7,true),(8,true),(0,false),(12,false),(11,false),(10,false)])
                        (.node 2124515 ([(1,true),(2,true),(3,true),(13,false),(6,false),(5,false),(10,false)],[(4,true),(11,true),(12,true),(0,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2124701 ([(5,true),(11,true),(1,false),(0,false),(13,true),(3,false),(9,true)],[(4,true),(7,true),(8,true),(2,false),(12,true),(6,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 2126693 ([(2,true),(3,true),(13,false),(0,true),(8,false),(5,false),(10,false)],[(4,true),(11,true),(12,true),(6,false),(7,false),(1,false),(9,true)])
                    (.node 2125493 ([(6,true),(12,false),(3,true),(4,true),(8,false),(1,false),(10,false)],[(13,false),(0,true),(11,true),(2,false),(7,false),(5,false),(9,true)])
                      (.node 2124809 ([(1,true),(2,true),(3,true),(13,false),(6,false),(5,false),(9,true)],[(4,true),(8,false),(7,false),(0,false),(12,false),(11,false),(10,false)])
                        (.node 2124797 ([(3,true),(4,true),(8,false),(1,true),(12,true),(6,false),(10,false)],[(13,false),(0,true),(7,false),(2,false),(11,false),(5,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2125541 ([(5,true),(8,false),(2,true),(3,true),(13,false),(0,true),(10,false)],[(4,true),(7,true),(1,false),(11,true),(12,true),(6,false),(9,true)])
                        .empty
                        .empty))
                    (.node 2127029 ([(2,true),(3,true),(4,true),(8,true),(0,false),(6,false),(10,false)],[(13,false),(12,false),(11,false),(5,false),(7,false),(1,false),(9,true)])
                      (.node 2126741 ([(1,true),(2,true),(3,true),(13,false),(6,false),(5,false),(10,false)],[(4,true),(11,true),(12,true),(0,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2127077 ([(1,true),(2,true),(12,true),(13,true),(4,true),(5,true),(10,false)],[(3,false),(11,false),(6,true),(0,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))))
                (.node 2130857 ([(1,true),(8,false),(6,true),(12,false),(4,false),(3,false),(10,false)],[(13,false),(0,true),(7,true),(5,false),(11,false),(2,false),(9,true)])
                  (.node 2130563 ([(1,true),(11,true),(5,true),(6,true),(13,true),(3,false),(9,true)],[(4,true),(12,true),(0,true),(7,true),(8,true),(2,false),(10,false)])
                    (.node 2130467 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                      (.node 2130449 ([(6,true),(0,true),(8,false),(3,true),(4,true),(11,false),(10,false)],[(13,false),(12,false),(5,true),(7,true),(2,false),(1,false),(9,true)])
                        (.node 2130221 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2130533 ([(6,true),(0,true),(1,true),(11,true),(4,false),(3,false),(9,true)],[(13,false),(12,false),(5,true),(7,true),(8,true),(2,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2130689 ([(1,true),(2,true),(3,true),(4,true),(12,true),(6,false),(9,true)],[(13,false),(0,true),(7,true),(8,true),(5,false),(11,false),(10,false)])
                      (.node 2130677 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2130809 ([(2,true),(3,true),(4,true),(12,true),(6,false),(8,true),(9,true)],[(13,false),(0,true),(1,true),(7,true),(5,false),(11,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 2132957 ([(0,false),(6,false),(5,false),(4,false),(3,false),(2,false),(10,false)],[(13,false),(12,false),(11,false),(1,false),(7,true),(8,true),(9,true)])
                    (.node 2132861 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                      (.node 2132849 ([(5,true),(6,true),(13,true),(3,false),(2,false),(1,false),(9,true)],[(4,true),(7,true),(8,true),(0,false),(12,false),(11,false),(10,false)])
                        (.node 2132567 ([(2,false),(8,false),(4,false),(13,false),(6,false),(11,false),(10,false)],[(3,false),(7,true),(5,true),(12,true),(0,true),(1,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2132933 ([(5,true),(6,true),(13,true),(3,false),(8,false),(1,true),(10,false)],[(4,true),(7,true),(0,false),(12,false),(11,false),(2,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2139611 ([(5,true),(8,false),(3,true),(13,false),(1,true),(11,false),(10,false)],[(4,true),(7,true),(2,false),(12,true),(0,false),(6,false),(9,true)])
                      (.node 2133251 ([(1,true),(8,false),(5,true),(6,true),(13,true),(3,false),(10,false)],[(4,true),(7,false),(0,false),(12,false),(11,false),(2,false),(9,true)])
                        .empty
                        .empty)
                      (.node 2141321 ([(0,true),(1,true),(11,false),(4,false),(3,false),(8,true),(9,true)],[(13,false),(12,false),(2,true),(7,false),(6,false),(5,false),(10,false)])
                        .empty
                        .empty)))))
              (.node 2147543 ([(6,true),(8,false),(1,false),(13,true),(4,true),(11,false),(10,false)],[(3,false),(2,false),(7,false),(5,false),(12,true),(0,false),(9,true)])
                (.node 2143787 ([(2,true),(3,true),(13,false),(0,false),(8,false),(5,true),(10,false)],[(4,true),(7,false),(1,false),(12,false),(11,false),(6,true),(9,true)])
                  (.node 2142005 ([(5,true),(8,false),(1,false),(13,true),(3,false),(11,false),(10,false)],[(4,true),(7,true),(2,true),(12,true),(0,false),(6,false),(9,true)])
                    (.node 2141615 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                      (.node 2141597 ([(3,true),(4,true),(8,false),(0,true),(1,true),(11,false),(10,false)],[(13,false),(12,false),(2,true),(7,true),(6,false),(5,false),(9,true)])
                        (.node 2141387 ([(3,true),(4,true),(5,true),(11,true),(1,false),(0,false),(9,true)],[(13,false),(12,false),(2,true),(7,true),(8,true),(6,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2141957 ([(6,true),(0,true),(13,true),(3,false),(2,false),(8,true),(9,true)],[(4,true),(5,true),(7,true),(1,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2143715 ([(0,true),(13,true),(3,false),(2,false),(8,true),(5,false),(10,false)],[(4,true),(11,true),(12,true),(1,true),(7,false),(6,false),(9,true)])
                      (.node 2143427 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2143769 ([(5,true),(11,true),(3,true),(13,false),(1,true),(8,true),(9,true)],[(4,true),(7,true),(2,true),(12,true),(0,false),(6,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 2146637 ([(3,true),(4,true),(5,true),(8,true),(1,false),(0,false),(10,false)],[(13,false),(12,false),(11,false),(6,false),(7,false),(2,false),(9,true)])
                    (.node 2143997 ([(2,true),(3,true),(13,false),(0,false),(6,false),(5,false),(9,true)],[(4,true),(8,false),(7,false),(1,false),(12,false),(11,false),(10,false)])
                      (.node 2143883 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                        (.node 2143853 ([(5,true),(6,true),(0,true),(13,true),(3,false),(2,false),(9,true)],[(4,true),(7,true),(8,true),(1,false),(12,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2144009 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2147207 ([(6,true),(0,true),(12,false),(4,false),(3,false),(2,false),(10,false)],[(13,false),(1,true),(11,true),(5,true),(7,true),(8,true),(9,true)])
                      (.node 2146685 ([(2,true),(3,true),(13,false),(12,false),(5,true),(6,true),(10,false)],[(4,true),(11,false),(0,true),(1,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2147495 ([(0,true),(1,true),(11,true),(4,false),(3,false),(8,true),(9,true)],[(13,false),(12,false),(5,true),(6,true),(7,true),(2,false),(10,false)])
                        .empty
                        .empty))))
                (.node 2149961 ([(2,true),(3,true),(4,true),(5,true),(12,true),(0,false),(9,true)],[(13,false),(1,true),(7,true),(8,true),(6,false),(11,false),(10,false)])
                  (.node 2149763 ([(0,true),(1,true),(11,true),(5,false),(4,false),(3,false),(9,true)],[(13,false),(12,false),(6,true),(7,true),(8,true),(2,false),(10,false)])
                    (.node 2149619 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                      (.node 2149607 ([(5,true),(6,true),(8,false),(3,true),(13,false),(1,true),(10,false)],[(4,true),(7,true),(2,false),(11,true),(12,true),(0,false),(9,true)])
                        (.node 2147831 ([(0,true),(1,true),(8,true),(5,false),(4,false),(3,false),(10,false)],[(13,false),(12,false),(11,false),(2,false),(7,false),(6,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2149733 ([(5,true),(6,true),(8,true),(3,true),(13,false),(1,true),(10,false)],[(4,true),(7,true),(0,true),(12,false),(11,false),(2,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2149847 ([(0,true),(12,false),(5,false),(4,false),(3,false),(2,false),(10,false)],[(13,false),(1,true),(11,true),(6,true),(7,true),(8,true),(9,true)])
                      (.node 2149829 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2149943 ([(5,true),(6,true),(8,false),(1,false),(13,true),(3,false),(10,false)],[(4,true),(7,true),(2,true),(11,true),(12,true),(0,false),(9,true)])
                        .empty
                        .empty)))
                  (.node 2152583 ([(6,true),(0,true),(8,true),(4,false),(13,false),(2,true),(10,false)],[(3,false),(11,true),(12,true),(1,false),(7,false),(5,false),(9,true)])
                    (.node 2150171 ([(2,true),(3,true),(13,false),(0,false),(6,false),(5,false),(9,true)],[(4,true),(8,false),(7,false),(1,false),(12,false),(11,false),(10,false)])
                      (.node 2150057 ([(0,true),(12,false),(5,false),(4,false),(3,false),(2,false),(9,true)],[(13,false),(1,true),(8,false),(7,false),(6,false),(11,false),(10,false)])
                        (.node 2150027 ([(5,true),(6,true),(0,true),(13,true),(3,false),(2,false),(9,true)],[(4,true),(7,true),(8,true),(1,false),(12,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2150183 ([(6,false),(5,false),(4,false),(13,false),(1,true),(2,true),(10,false)],[(3,false),(11,true),(12,true),(0,false),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2153087 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(10,false)],[(13,false),(12,false),(11,false),(5,true),(7,true),(8,true),(9,true)])
                      (.node 2152631 ([(5,true),(8,false),(0,false),(12,true),(13,true),(3,false),(10,false)],[(4,true),(7,true),(1,true),(2,true),(11,true),(6,false),(9,true)])
                        .empty
                        .empty)
                      (.node 2153105 ([(3,true),(4,true),(5,true),(6,true),(12,true),(1,false),(9,true)],[(13,false),(2,true),(7,true),(8,true),(0,false),(11,false),(10,false)])
                        .empty
                        .empty))))))
            (.node 2219393 ([(1,true),(11,true),(6,false),(5,false),(4,false),(3,false),(9,true)],[(13,false),(12,false),(0,true),(7,true),(8,true),(2,false),(10,false)])
              (.node 2163617 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                (.node 2156003 ([(3,true),(13,false),(1,false),(0,false),(6,false),(5,false),(9,true)],[(4,true),(8,false),(7,false),(2,false),(12,false),(11,false),(10,false)])
                  (.node 2153621 ([(7,true),(3,true),(13,false),(12,false),(6,false),(5,false),(9,true)],[(4,true),(8,false),(2,false),(1,false),(0,false),(11,false),(10,false)])
                    (.node 2153327 ([(1,true),(2,true),(3,true),(4,true),(11,true),(6,false),(9,true)],[(13,false),(12,false),(0,true),(7,true),(8,true),(5,false),(10,false)])
                      (.node 2153315 ([(3,true),(4,true),(11,true),(12,true),(1,false),(8,true),(9,true)],[(13,false),(2,true),(7,true),(0,false),(6,false),(5,false),(10,false)])
                        (.node 2153201 ([(1,true),(12,false),(6,false),(5,false),(4,false),(3,false),(9,true)],[(13,false),(2,true),(8,false),(7,false),(0,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2153609 ([(3,true),(4,true),(8,false),(1,true),(12,false),(6,false),(10,false)],[(13,false),(2,true),(7,true),(0,false),(11,false),(5,false),(9,true)])
                        .empty
                        .empty))
                    (.node 2155781 ([(5,true),(11,true),(1,true),(13,true),(3,false),(8,true),(9,true)],[(4,true),(7,true),(2,false),(12,false),(0,false),(6,false),(10,false)])
                      (.node 2155727 ([(0,true),(1,true),(13,true),(3,false),(8,true),(5,false),(10,false)],[(4,true),(11,true),(12,true),(2,true),(7,false),(6,false),(9,true)])
                        (.node 2154017 ([(5,true),(8,false),(3,true),(13,false),(1,false),(0,false),(10,false)],[(4,true),(7,true),(2,false),(12,false),(11,false),(6,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2155793 ([(3,true),(13,false),(1,false),(0,false),(8,false),(5,true),(10,false)],[(4,true),(7,false),(2,false),(12,false),(11,false),(6,true),(9,true)])
                        .empty
                        .empty)))
                  (.node 2163395 ([(3,true),(4,true),(12,true),(1,false),(8,false),(6,true),(10,false)],[(13,false),(2,true),(7,true),(5,false),(11,false),(0,true),(9,true)])
                    (.node 2160593 ([(1,true),(2,true),(3,true),(4,true),(8,true),(6,false),(10,false)],[(13,false),(12,false),(11,false),(5,false),(7,false),(0,false),(9,true)])
                      (.node 2158805 ([(4,false),(3,false),(2,false),(1,false),(8,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,false),(5,true),(9,true)])
                        (.node 2156021 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2163377 ([(6,true),(11,true),(4,false),(3,false),(2,false),(1,false),(9,true)],[(13,false),(12,false),(5,true),(7,true),(8,true),(0,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2163491 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                      (.node 2163461 ([(6,true),(0,true),(1,true),(12,false),(4,false),(3,false),(9,true)],[(13,false),(2,true),(8,false),(7,false),(5,false),(11,false),(10,false)])
                        .empty
                        .empty)
                      (.node 2163605 ([(3,true),(4,true),(12,true),(1,false),(0,false),(6,false),(9,true)],[(13,false),(2,true),(7,true),(8,true),(5,false),(11,false),(10,false)])
                        .empty
                        .empty))))
                (.node 2166227 ([(0,true),(1,true),(12,false),(5,false),(4,false),(3,false),(9,true)],[(13,false),(2,true),(8,false),(7,false),(6,false),(11,false),(10,false)])
                  (.node 2165789 ([(3,true),(4,true),(8,true),(1,true),(12,false),(6,true),(10,false)],[(13,false),(2,true),(7,true),(5,true),(11,false),(0,true),(9,true)])
                    (.node 2165381 ([(0,false),(8,false),(2,false),(13,true),(4,true),(5,true),(10,false)],[(3,false),(7,false),(1,true),(12,false),(11,false),(6,true),(9,true)])
                      (.node 2163959 ([(0,true),(1,true),(12,false),(4,false),(3,false),(8,true),(9,true)],[(13,false),(2,true),(7,false),(6,false),(5,false),(11,false),(10,false)])
                        (.node 2163671 ([(6,true),(8,false),(2,false),(13,true),(4,true),(11,false),(10,false)],[(3,false),(7,false),(5,false),(12,true),(1,false),(0,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2165777 ([(4,false),(3,false),(2,false),(12,false),(6,true),(0,true),(9,true)],[(13,false),(1,false),(8,false),(7,false),(5,true),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2166083 ([(3,true),(4,true),(5,true),(12,true),(1,false),(0,false),(9,true)],[(13,false),(2,true),(7,true),(8,true),(6,false),(11,false),(10,false)])
                      (.node 2166071 ([(5,true),(6,true),(8,false),(3,true),(13,false),(1,false),(10,false)],[(4,true),(7,true),(2,false),(12,false),(11,false),(0,false),(9,true)])
                        .empty
                        .empty)
                      (.node 2166197 ([(5,true),(6,true),(0,true),(1,true),(13,true),(3,false),(9,true)],[(4,true),(7,true),(8,true),(2,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 2219003 ([(2,false),(8,false),(4,false),(13,false),(6,true),(0,true),(10,false)],[(3,false),(7,true),(5,true),(12,false),(11,false),(1,true),(9,true)])
                    (.node 2166767 ([(1,true),(12,false),(6,true),(8,false),(4,false),(3,false),(10,false)],[(13,false),(2,true),(11,true),(5,false),(7,false),(0,false),(9,true)])
                      (.node 2166311 ([(0,true),(11,true),(12,true),(13,true),(3,false),(8,true),(9,true)],[(4,true),(5,true),(6,true),(7,true),(2,false),(1,false),(10,false)])
                        (.node 2166293 ([(3,true),(4,true),(8,false),(6,false),(12,true),(1,false),(10,false)],[(13,false),(2,true),(7,true),(0,true),(11,true),(5,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2166815 ([(0,true),(1,true),(12,false),(5,false),(4,false),(3,false),(10,false)],[(13,false),(2,true),(11,true),(6,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2219297 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                      (.node 2219285 ([(4,false),(13,false),(6,true),(0,true),(8,false),(2,false),(10,false)],[(3,false),(7,false),(5,true),(12,false),(11,false),(1,false),(9,true)])
                        .empty
                        .empty)
                      (.node 2219369 ([(4,false),(13,false),(6,true),(0,true),(1,true),(2,true),(9,true)],[(3,false),(8,false),(7,false),(5,true),(12,false),(11,false),(10,false)])
                        .empty
                        .empty)))))
              (.node 2223695 ([(5,true),(13,true),(3,false),(2,false),(1,false),(0,false),(9,true)],[(4,true),(7,true),(8,true),(6,false),(12,false),(11,false),(10,false)])
                (.node 2222213 ([(0,true),(1,true),(2,true),(3,true),(13,false),(5,false),(9,true)],[(4,true),(8,false),(7,false),(6,false),(12,false),(11,false),(10,false)])
                  (.node 2221991 ([(2,true),(3,true),(4,true),(5,true),(12,false),(0,false),(9,true)],[(13,false),(6,true),(8,false),(7,false),(1,false),(11,false),(10,false)])
                    (.node 2221793 ([(7,true),(4,false),(13,false),(12,false),(1,true),(2,true),(9,true)],[(3,false),(8,false),(5,true),(6,true),(0,true),(11,false),(10,false)])
                      (.node 2221763 ([(5,true),(13,true),(3,false),(8,false),(0,true),(1,true),(10,false)],[(4,true),(7,true),(6,false),(12,false),(11,false),(2,true),(9,true)])
                        (.node 2219687 ([(0,false),(6,false),(13,true),(4,true),(8,true),(2,true),(10,false)],[(3,false),(11,true),(12,true),(5,false),(7,false),(1,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2221973 ([(5,true),(13,true),(3,false),(2,false),(1,false),(0,false),(9,true)],[(4,true),(7,true),(8,true),(6,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2222087 ([(0,true),(1,true),(8,false),(5,true),(13,true),(3,false),(10,false)],[(4,true),(7,false),(6,false),(12,false),(11,false),(2,false),(9,true)])
                      (.node 2222057 ([(5,true),(13,true),(3,false),(11,true),(0,false),(8,true),(9,true)],[(4,true),(7,true),(6,false),(12,false),(1,true),(2,true),(10,false)])
                        .empty
                        .empty)
                      (.node 2222201 ([(2,true),(3,true),(13,false),(12,false),(0,false),(8,true),(9,true)],[(4,true),(5,true),(6,true),(7,false),(1,false),(11,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 2223485 ([(5,true),(13,true),(3,false),(8,false),(1,true),(11,false),(10,false)],[(4,true),(7,true),(0,false),(6,false),(12,false),(2,true),(9,true)])
                    (.node 2223401 ([(5,true),(13,true),(3,false),(2,false),(11,false),(0,true),(9,true)],[(4,true),(7,true),(8,true),(1,true),(12,true),(6,true),(10,false)])
                      (.node 2222789 ([(2,true),(3,true),(13,false),(6,true),(0,true),(11,false),(10,false)],[(4,true),(5,true),(12,false),(1,true),(7,true),(8,true),(9,true)])
                        (.node 2222741 ([(3,true),(4,true),(5,true),(12,false),(0,false),(8,true),(9,true)],[(13,false),(6,true),(7,false),(2,false),(1,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2223413 ([(3,true),(4,true),(5,true),(6,true),(11,true),(1,false),(9,true)],[(13,false),(12,false),(2,true),(7,true),(8,true),(0,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2223581 ([(3,true),(4,true),(5,true),(12,false),(1,false),(0,false),(10,false)],[(13,false),(6,true),(11,true),(2,true),(7,true),(8,true),(9,true)])
                      (.node 2223509 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2223593 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))))
                (.node 2226203 ([(0,true),(11,true),(3,true),(13,false),(5,false),(8,true),(9,true)],[(4,true),(7,false),(6,false),(12,false),(2,false),(1,false),(10,false)])
                  (.node 2225861 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                    (.node 2225111 ([(0,true),(1,true),(2,true),(3,true),(13,false),(5,false),(10,false)],[(4,true),(11,true),(12,true),(6,true),(7,true),(8,true),(9,true)])
                      (.node 2225063 ([(1,true),(12,true),(5,false),(4,false),(3,false),(8,true),(9,true)],[(13,false),(6,true),(0,true),(7,true),(2,false),(11,false),(10,false)])
                        (.node 2223707 ([(3,true),(4,true),(5,true),(12,false),(1,false),(0,false),(9,true)],[(13,false),(6,true),(8,false),(7,false),(2,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2225813 ([(2,true),(11,false),(6,false),(13,true),(4,true),(8,true),(9,true)],[(3,false),(12,true),(5,false),(7,false),(1,false),(0,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2226107 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                      (.node 2226089 ([(5,true),(13,true),(3,false),(2,false),(1,false),(0,false),(9,true)],[(4,true),(7,true),(8,true),(6,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty)
                      (.node 2226173 ([(5,true),(13,true),(3,false),(2,false),(8,false),(0,true),(10,false)],[(4,true),(7,true),(6,false),(12,false),(11,false),(1,true),(9,true)])
                        .empty
                        .empty)))
                  (.node 2231285 ([(0,true),(8,false),(3,true),(13,false),(5,false),(11,false),(10,false)],[(4,true),(12,true),(6,true),(7,true),(2,false),(1,false),(9,true)])
                    (.node 2226497 ([(0,true),(8,false),(5,true),(13,true),(3,false),(2,false),(10,false)],[(4,true),(7,false),(6,false),(12,false),(11,false),(1,false),(9,true)])
                      (.node 2226329 ([(0,true),(1,true),(2,true),(3,true),(13,false),(5,false),(9,true)],[(4,true),(8,false),(7,false),(6,false),(12,false),(11,false),(10,false)])
                        (.node 2226317 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2230973 ([(3,true),(4,true),(5,true),(6,true),(8,true),(1,false),(10,false)],[(13,false),(12,false),(11,false),(0,false),(7,false),(2,false),(9,true)])
                        .empty
                        .empty))
                    (.node 2238893 ([(5,false),(13,false),(0,true),(1,true),(8,false),(3,false),(10,false)],[(4,false),(7,false),(6,true),(12,false),(11,false),(2,false),(9,true)])
                      (.node 2238611 ([(3,false),(8,false),(5,false),(13,false),(0,true),(1,true),(10,false)],[(4,false),(7,true),(6,true),(12,false),(11,false),(2,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2238905 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)))))))
          (.node 2270297 ([(1,true),(12,false),(6,false),(5,false),(4,false),(3,false),(10,false)],[(13,false),(2,true),(11,true),(0,true),(7,true),(8,true),(9,true)])
            (.node 2253383 ([(6,true),(0,true),(13,true),(4,false),(8,false),(2,true),(10,false)],[(5,true),(7,true),(1,false),(12,false),(11,false),(3,true),(9,true)])
              (.node 2243303 ([(6,true),(13,true),(4,false),(3,false),(2,false),(1,false),(9,true)],[(5,true),(7,true),(8,true),(0,false),(12,false),(11,false),(10,false)])
                (.node 2241821 ([(1,true),(2,true),(3,true),(4,true),(13,false),(6,false),(9,true)],[(5,true),(8,false),(7,false),(0,false),(12,false),(11,false),(10,false)])
                  (.node 2241581 ([(6,true),(13,true),(4,false),(3,false),(2,false),(1,false),(9,true)],[(5,true),(7,true),(8,true),(0,false),(12,false),(11,false),(10,false)])
                    (.node 2241371 ([(6,true),(13,true),(4,false),(8,false),(1,true),(2,true),(10,false)],[(5,true),(7,true),(0,false),(12,false),(11,false),(3,true),(9,true)])
                      (.node 2239295 ([(1,false),(0,false),(13,true),(5,true),(8,true),(3,true),(10,false)],[(4,false),(11,true),(12,true),(6,false),(7,false),(2,true),(9,true)])
                        (.node 2239001 ([(2,true),(11,true),(0,false),(6,false),(5,false),(4,false),(9,true)],[(13,false),(12,false),(1,true),(7,true),(8,true),(3,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2241401 ([(7,true),(5,false),(13,false),(12,false),(2,true),(3,true),(9,true)],[(4,false),(8,false),(6,true),(0,true),(1,true),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2241695 ([(1,true),(2,true),(8,false),(6,true),(13,true),(4,false),(10,false)],[(5,true),(7,false),(0,false),(12,false),(11,false),(3,false),(9,true)])
                      (.node 2241665 ([(6,true),(13,true),(4,false),(11,true),(1,false),(8,true),(9,true)],[(5,true),(7,true),(0,false),(12,false),(2,true),(3,true),(10,false)])
                        (.node 2241599 ([(3,true),(4,true),(5,true),(6,true),(12,false),(1,false),(9,true)],[(13,false),(0,true),(8,false),(7,false),(2,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2241809 ([(3,true),(4,true),(13,false),(12,false),(1,false),(8,true),(9,true)],[(5,true),(6,true),(0,true),(7,false),(2,false),(11,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 2243093 ([(6,true),(13,true),(4,false),(8,false),(2,true),(11,false),(10,false)],[(5,true),(7,true),(1,false),(0,false),(12,false),(3,true),(9,true)])
                    (.node 2243009 ([(6,true),(13,true),(4,false),(3,false),(11,false),(1,true),(9,true)],[(5,true),(7,true),(8,true),(2,true),(12,true),(0,true),(10,false)])
                      (.node 2242397 ([(3,true),(4,true),(13,false),(0,true),(1,true),(11,false),(10,false)],[(5,true),(6,true),(12,false),(2,true),(7,true),(8,true),(9,true)])
                        (.node 2242349 ([(4,true),(5,true),(6,true),(12,false),(1,false),(8,true),(9,true)],[(13,false),(0,true),(7,false),(3,false),(2,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2243021 ([(4,true),(5,true),(6,true),(0,true),(11,true),(2,false),(9,true)],[(13,false),(12,false),(3,true),(7,true),(8,true),(1,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2243189 ([(4,true),(5,true),(6,true),(12,false),(2,false),(1,false),(10,false)],[(13,false),(0,true),(11,true),(3,true),(7,true),(8,true),(9,true)])
                      (.node 2243117 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2243201 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))))
                (.node 2245811 ([(1,true),(11,true),(4,true),(13,false),(6,false),(8,true),(9,true)],[(5,true),(7,false),(0,false),(12,false),(3,false),(2,false),(10,false)])
                  (.node 2245469 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                    (.node 2244719 ([(1,true),(2,true),(3,true),(4,true),(13,false),(6,false),(10,false)],[(5,true),(11,true),(12,true),(0,true),(7,true),(8,true),(9,true)])
                      (.node 2244671 ([(2,true),(12,true),(6,false),(5,false),(4,false),(8,true),(9,true)],[(13,false),(0,true),(1,true),(7,true),(3,false),(11,false),(10,false)])
                        (.node 2243315 ([(4,true),(5,true),(6,true),(12,false),(2,false),(1,false),(9,true)],[(13,false),(0,true),(8,false),(7,false),(3,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2245421 ([(3,true),(11,false),(0,false),(13,true),(5,true),(8,true),(9,true)],[(4,false),(12,true),(6,false),(7,false),(2,false),(1,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2245715 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                      (.node 2245697 ([(6,true),(13,true),(4,false),(3,false),(2,false),(1,false),(9,true)],[(5,true),(7,true),(8,true),(0,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty)
                      (.node 2245781 ([(6,true),(13,true),(4,false),(3,false),(8,false),(1,true),(10,false)],[(5,true),(7,true),(0,false),(12,false),(11,false),(2,true),(9,true)])
                        .empty
                        .empty)))
                  (.node 2250893 ([(1,true),(8,false),(4,true),(13,false),(6,false),(11,false),(10,false)],[(5,true),(12,true),(0,true),(7,true),(3,false),(2,false),(9,true)])
                    (.node 2246105 ([(1,true),(8,false),(6,true),(13,true),(4,false),(3,false),(10,false)],[(5,true),(7,false),(0,false),(12,false),(11,false),(2,false),(9,true)])
                      (.node 2245937 ([(1,true),(2,true),(3,true),(4,true),(13,false),(6,false),(9,true)],[(5,true),(8,false),(7,false),(0,false),(12,false),(11,false),(10,false)])
                        (.node 2245925 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2250581 ([(4,true),(5,true),(6,true),(0,true),(8,true),(2,false),(10,false)],[(13,false),(12,false),(11,false),(1,false),(7,false),(3,false),(9,true)])
                        .empty
                        .empty))
                    (.node 2253299 ([(6,true),(0,true),(13,true),(4,false),(3,false),(2,false),(9,true)],[(5,true),(7,true),(8,true),(1,false),(12,false),(11,false),(10,false)])
                      (.node 2253017 ([(3,false),(8,false),(5,false),(13,false),(0,false),(11,false),(10,false)],[(4,false),(7,true),(6,true),(12,true),(1,true),(2,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2253311 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)))))
              (.node 2262743 ([(0,true),(12,false),(4,true),(5,true),(8,false),(2,false),(10,false)],[(13,false),(1,true),(11,true),(3,false),(7,false),(6,false),(9,true)])
                (.node 2261417 ([(4,true),(5,true),(11,true),(2,false),(1,false),(0,false),(9,true)],[(13,false),(12,false),(3,true),(7,true),(8,true),(6,false),(10,false)])
                  (.node 2259557 ([(6,true),(11,true),(2,false),(1,false),(13,true),(4,false),(9,true)],[(5,true),(7,true),(8,true),(3,false),(12,true),(0,false),(10,false)])
                    (.node 2259473 ([(6,true),(0,true),(13,true),(4,false),(3,false),(2,false),(9,true)],[(5,true),(7,true),(8,true),(1,false),(12,false),(11,false),(10,false)])
                      (.node 2253701 ([(2,true),(8,false),(6,true),(0,true),(13,true),(4,false),(10,false)],[(5,true),(7,false),(1,false),(12,false),(11,false),(3,false),(9,true)])
                        (.node 2253407 ([(1,false),(0,false),(6,false),(5,false),(4,false),(3,false),(10,false)],[(13,false),(12,false),(11,false),(2,false),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2259485 ([(4,true),(5,true),(6,true),(0,true),(12,false),(2,false),(9,true)],[(13,false),(1,true),(8,false),(7,false),(3,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2259653 ([(4,true),(5,true),(8,false),(2,true),(12,true),(0,false),(10,false)],[(13,false),(1,true),(7,false),(3,false),(11,false),(6,false),(9,true)])
                      (.node 2259581 ([(2,true),(11,false),(0,true),(13,true),(5,true),(8,true),(9,true)],[(4,false),(3,false),(12,true),(1,true),(7,true),(6,true),(10,false)])
                        .empty
                        .empty)
                      (.node 2259665 ([(2,true),(3,true),(4,true),(13,false),(0,false),(6,false),(9,true)],[(5,true),(8,false),(7,false),(1,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 2261609 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                    (.node 2261525 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                      (.node 2261501 ([(4,true),(5,true),(6,true),(0,true),(12,false),(2,false),(9,true)],[(13,false),(1,true),(8,false),(7,false),(3,false),(11,false),(10,false)])
                        (.node 2261429 ([(2,true),(3,true),(4,true),(13,false),(0,false),(6,false),(10,false)],[(5,true),(11,true),(12,true),(1,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2261597 ([(2,true),(3,true),(4,true),(13,false),(0,false),(6,false),(10,false)],[(5,true),(11,true),(12,true),(1,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2261933 ([(2,true),(3,true),(12,true),(13,true),(5,true),(6,true),(10,false)],[(4,false),(11,false),(0,true),(1,true),(7,true),(8,true),(9,true)])
                      (.node 2261885 ([(3,true),(4,true),(5,true),(8,true),(1,false),(0,false),(10,false)],[(13,false),(12,false),(11,false),(6,false),(7,false),(2,false),(9,true)])
                        .empty
                        .empty)
                      (.node 2262455 ([(6,true),(8,false),(3,true),(4,true),(13,false),(1,true),(10,false)],[(5,true),(7,true),(2,false),(11,true),(12,true),(0,false),(9,true)])
                        .empty
                        .empty))))
                (.node 2267771 ([(2,true),(11,true),(6,true),(0,true),(13,true),(4,false),(9,true)],[(5,true),(12,true),(1,true),(7,true),(8,true),(3,false),(10,false)])
                  (.node 2267591 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                    (.node 2267381 ([(4,true),(5,true),(11,false),(1,false),(0,false),(8,true),(9,true)],[(13,false),(12,false),(6,true),(7,false),(3,false),(2,false),(10,false)])
                      (.node 2263949 ([(2,true),(3,true),(4,true),(13,false),(0,false),(6,false),(10,false)],[(5,true),(11,true),(12,true),(1,true),(7,true),(8,true),(9,true)])
                        (.node 2263901 ([(3,true),(4,true),(13,false),(1,true),(8,false),(6,false),(10,false)],[(5,true),(11,true),(12,true),(0,false),(7,false),(2,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2267429 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2267675 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                      (.node 2267603 ([(2,true),(3,true),(4,true),(5,true),(12,true),(0,false),(9,true)],[(13,false),(1,true),(7,true),(8,true),(6,false),(11,false),(10,false)])
                        .empty
                        .empty)
                      (.node 2267699 ([(0,true),(1,true),(8,false),(4,true),(5,true),(11,false),(10,false)],[(13,false),(12,false),(6,true),(7,true),(3,false),(2,false),(9,true)])
                        .empty
                        .empty)))
                  (.node 2270069 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                    (.node 2268065 ([(2,true),(8,false),(0,true),(12,false),(5,false),(4,false),(10,false)],[(13,false),(1,true),(7,true),(6,false),(11,false),(3,false),(9,true)])
                      (.node 2268017 ([(3,true),(4,true),(5,true),(12,true),(0,false),(8,true),(9,true)],[(13,false),(1,true),(2,true),(7,true),(6,false),(11,false),(10,false)])
                        (.node 2267783 ([(0,true),(1,true),(2,true),(11,true),(5,false),(4,false),(9,true)],[(13,false),(12,false),(6,true),(7,true),(8,true),(3,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2270057 ([(6,true),(0,true),(8,false),(4,true),(13,false),(2,true),(10,false)],[(5,true),(7,true),(3,false),(11,true),(12,true),(1,false),(9,true)])
                        .empty
                        .empty))
                    (.node 2270213 ([(1,true),(2,true),(11,true),(6,false),(5,false),(4,false),(9,true)],[(13,false),(12,false),(0,true),(7,true),(8,true),(3,false),(10,false)])
                      (.node 2270183 ([(6,true),(0,true),(8,true),(4,true),(13,false),(2,true),(10,false)],[(5,true),(7,true),(1,true),(12,false),(11,false),(3,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2270279 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))))))
            (.node 2287217 ([(2,true),(12,false),(0,true),(8,false),(5,false),(4,false),(10,false)],[(13,false),(3,true),(11,true),(6,false),(7,false),(1,false),(9,true)])
              (.node 2278919 ([(6,true),(8,false),(2,false),(13,true),(4,false),(11,false),(10,false)],[(5,true),(7,true),(3,true),(12,true),(1,false),(0,false),(9,true)])
                (.node 2276471 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                  (.node 2270621 ([(3,true),(4,true),(13,false),(1,false),(0,false),(6,false),(9,true)],[(5,true),(8,false),(7,false),(2,false),(12,false),(11,false),(10,false)])
                    (.node 2270477 ([(6,true),(0,true),(1,true),(13,true),(4,false),(3,false),(9,true)],[(5,true),(7,true),(8,true),(2,false),(12,false),(11,false),(10,false)])
                      (.node 2270411 ([(3,true),(4,true),(5,true),(6,true),(12,true),(1,false),(9,true)],[(13,false),(2,true),(7,true),(8,true),(0,false),(11,false),(10,false)])
                        (.node 2270393 ([(6,true),(0,true),(8,false),(2,false),(13,true),(4,false),(10,false)],[(5,true),(7,true),(3,true),(11,true),(12,true),(1,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2270507 ([(1,true),(12,false),(6,false),(5,false),(4,false),(3,false),(9,true)],[(13,false),(2,true),(8,false),(7,false),(0,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2276243 ([(4,true),(5,true),(6,true),(11,true),(2,false),(1,false),(9,true)],[(13,false),(12,false),(3,true),(7,true),(8,true),(0,false),(10,false)])
                      (.node 2276231 ([(6,true),(11,true),(2,false),(13,true),(4,false),(8,true),(9,true)],[(5,true),(7,true),(3,false),(12,true),(1,false),(0,false),(10,false)])
                        (.node 2270633 ([(0,false),(6,false),(5,false),(13,false),(2,true),(3,true),(10,false)],[(4,false),(11,true),(12,true),(1,false),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2276453 ([(4,true),(5,true),(8,false),(1,true),(2,true),(11,false),(10,false)],[(13,false),(12,false),(3,true),(7,true),(0,false),(6,false),(9,true)])
                        .empty
                        .empty)))
                  (.node 2278709 ([(6,true),(0,true),(1,true),(13,true),(4,false),(3,false),(9,true)],[(5,true),(7,true),(8,true),(2,false),(12,false),(11,false),(10,false)])
                    (.node 2278625 ([(6,true),(11,true),(4,true),(13,false),(2,true),(8,true),(9,true)],[(5,true),(7,true),(3,true),(12,true),(1,false),(0,false),(10,false)])
                      (.node 2278235 ([(1,true),(2,true),(11,false),(5,false),(4,false),(8,true),(9,true)],[(13,false),(12,false),(3,true),(7,false),(0,false),(6,false),(10,false)])
                        (.node 2276525 ([(6,true),(8,false),(4,true),(13,false),(2,true),(11,false),(10,false)],[(5,true),(7,true),(3,false),(12,true),(1,false),(0,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2278643 ([(3,true),(4,true),(13,false),(1,false),(8,false),(6,true),(10,false)],[(5,true),(7,false),(2,false),(12,false),(11,false),(0,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2278853 ([(3,true),(4,true),(13,false),(1,false),(0,false),(6,false),(9,true)],[(5,true),(8,false),(7,false),(2,false),(12,false),(11,false),(10,false)])
                      (.node 2278739 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2278865 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))))
                (.node 2284793 ([(0,true),(8,false),(2,false),(13,true),(5,true),(11,false),(10,false)],[(4,false),(3,false),(7,false),(6,false),(12,true),(1,false),(9,true)])
                  (.node 2283893 ([(3,true),(4,true),(13,false),(12,false),(6,true),(0,true),(10,false)],[(5,true),(11,false),(1,true),(2,true),(7,true),(8,true),(9,true)])
                    (.node 2280677 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                      (.node 2280629 ([(1,true),(13,true),(4,false),(3,false),(8,true),(6,false),(10,false)],[(5,true),(11,true),(12,true),(2,true),(7,false),(0,false),(9,true)])
                        (.node 2279207 ([(0,true),(1,true),(13,true),(4,false),(3,false),(8,true),(9,true)],[(5,true),(6,true),(7,true),(2,false),(12,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2283845 ([(4,true),(5,true),(6,true),(8,true),(2,false),(1,false),(10,false)],[(13,false),(12,false),(11,false),(0,false),(7,false),(3,false),(9,true)])
                        .empty
                        .empty))
                    (.node 2284457 ([(0,true),(1,true),(12,false),(5,false),(4,false),(3,false),(10,false)],[(13,false),(2,true),(11,true),(6,true),(7,true),(8,true),(9,true)])
                      (.node 2284409 ([(1,true),(2,true),(11,true),(5,false),(4,false),(8,true),(9,true)],[(13,false),(12,false),(6,true),(0,true),(7,true),(3,false),(10,false)])
                        .empty
                        .empty)
                      (.node 2284745 ([(1,true),(2,true),(8,true),(6,false),(5,false),(4,false),(10,false)],[(13,false),(12,false),(11,false),(3,false),(7,false),(0,false),(9,true)])
                        .empty
                        .empty)))
                  (.node 2286647 ([(6,true),(0,true),(1,true),(2,true),(13,true),(4,false),(9,true)],[(5,true),(7,true),(8,true),(3,false),(12,false),(11,false),(10,false)])
                    (.node 2286521 ([(6,true),(0,true),(8,false),(4,true),(13,false),(2,false),(10,false)],[(5,true),(7,true),(3,false),(12,false),(11,false),(1,false),(9,true)])
                      (.node 2286239 ([(4,true),(5,true),(8,true),(2,true),(12,false),(0,true),(10,false)],[(13,false),(3,true),(7,true),(6,true),(11,false),(1,true),(9,true)])
                        (.node 2286227 ([(5,false),(4,false),(3,false),(12,false),(0,true),(1,true),(9,true)],[(13,false),(2,false),(8,false),(7,false),(6,true),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2286533 ([(4,true),(5,true),(6,true),(12,true),(2,false),(1,false),(9,true)],[(13,false),(3,true),(7,true),(8,true),(0,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2286743 ([(4,true),(5,true),(8,false),(0,false),(12,true),(2,false),(10,false)],[(13,false),(3,true),(7,true),(1,true),(11,true),(6,false),(9,true)])
                      (.node 2286677 ([(1,true),(2,true),(12,false),(6,false),(5,false),(4,false),(9,true)],[(13,false),(3,true),(8,false),(7,false),(0,false),(11,false),(10,false)])
                        .empty
                        .empty)
                      (.node 2286761 ([(1,true),(11,true),(12,true),(13,true),(4,false),(8,true),(9,true)],[(5,true),(6,true),(0,true),(7,true),(3,false),(2,false),(10,false)])
                        .empty
                        .empty)))))
              (.node 2295449 ([(2,true),(3,true),(4,true),(5,true),(8,true),(0,false),(10,false)],[(13,false),(12,false),(11,false),(6,false),(7,false),(1,false),(9,true)])
                (.node 2290337 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                  (.node 2289833 ([(0,true),(1,true),(8,true),(5,false),(13,false),(3,true),(10,false)],[(4,false),(11,true),(12,true),(2,false),(7,false),(6,false),(9,true)])
                    (.node 2288477 ([(7,true),(4,true),(13,false),(12,false),(0,false),(6,false),(9,true)],[(5,true),(8,false),(3,false),(2,false),(1,false),(11,false),(10,false)])
                      (.node 2288465 ([(4,true),(5,true),(8,false),(2,true),(12,false),(0,false),(10,false)],[(13,false),(3,true),(7,true),(1,false),(11,false),(6,false),(9,true)])
                        (.node 2287265 ([(1,true),(2,true),(12,false),(6,false),(5,false),(4,false),(10,false)],[(13,false),(3,true),(11,true),(0,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2289545 ([(6,true),(8,false),(1,false),(12,true),(13,true),(4,false),(10,false)],[(5,true),(7,true),(2,true),(3,true),(11,true),(0,false),(9,true)])
                        .empty
                        .empty))
                    (.node 2290241 ([(2,true),(3,true),(4,true),(5,true),(11,true),(0,false),(9,true)],[(13,false),(12,false),(1,true),(7,true),(8,true),(6,false),(10,false)])
                      (.node 2290229 ([(4,true),(5,true),(11,true),(12,true),(2,false),(8,true),(9,true)],[(13,false),(3,true),(7,true),(1,false),(0,false),(6,false),(10,false)])
                        .empty
                        .empty)
                      (.node 2290313 ([(4,true),(5,true),(6,true),(0,true),(12,true),(2,false),(9,true)],[(13,false),(3,true),(7,true),(8,true),(1,false),(11,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 2290859 ([(4,true),(13,false),(2,false),(1,false),(0,false),(6,false),(9,true)],[(5,true),(8,false),(7,false),(3,false),(12,false),(11,false),(10,false)])
                    (.node 2290637 ([(6,true),(11,true),(2,true),(13,true),(4,false),(8,true),(9,true)],[(5,true),(7,true),(3,false),(12,false),(1,false),(0,false),(10,false)])
                      (.node 2290421 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(10,false)],[(13,false),(12,false),(11,false),(6,true),(7,true),(8,true),(9,true)])
                        (.node 2290409 ([(2,true),(12,false),(0,false),(6,false),(5,false),(4,false),(9,true)],[(13,false),(3,true),(8,false),(7,false),(1,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2290649 ([(4,true),(13,false),(2,false),(1,false),(8,false),(6,true),(10,false)],[(5,true),(7,false),(3,false),(12,false),(11,false),(0,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2290931 ([(6,true),(8,false),(4,true),(13,false),(2,false),(1,false),(10,false)],[(5,true),(7,true),(3,false),(12,false),(11,false),(0,false),(9,true)])
                      (.node 2290877 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2292641 ([(1,true),(2,true),(13,true),(4,false),(8,true),(6,false),(10,false)],[(5,true),(11,true),(12,true),(3,true),(7,false),(0,false),(9,true)])
                        .empty
                        .empty))))
                (.node 2300873 ([(1,true),(2,true),(12,false),(5,false),(4,false),(8,true),(9,true)],[(13,false),(3,true),(7,false),(0,false),(6,false),(11,false),(10,false)])
                  (.node 2300603 ([(4,true),(5,true),(12,true),(2,false),(8,false),(0,true),(10,false)],[(13,false),(3,true),(7,true),(6,false),(11,false),(1,true),(9,true)])
                    (.node 2300519 ([(4,true),(5,true),(12,true),(2,false),(1,false),(0,false),(9,true)],[(13,false),(3,true),(7,true),(8,true),(6,false),(11,false),(10,false)])
                      (.node 2300237 ([(1,false),(8,false),(3,false),(13,true),(5,true),(6,true),(10,false)],[(4,false),(7,false),(2,true),(12,false),(11,false),(0,true),(9,true)])
                        (.node 2295719 ([(5,false),(4,false),(3,false),(2,false),(8,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,false),(6,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2300531 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2300699 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                      (.node 2300627 ([(0,true),(11,true),(5,false),(4,false),(3,false),(2,false),(9,true)],[(13,false),(12,false),(6,true),(7,true),(8,true),(1,false),(10,false)])
                        .empty
                        .empty)
                      (.node 2300711 ([(0,true),(1,true),(2,true),(12,false),(5,false),(4,false),(9,true)],[(13,false),(3,true),(8,false),(7,false),(6,false),(11,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 2376113 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                    (.node 2371343 ([(2,true),(8,false),(5,true),(13,false),(0,false),(11,false),(10,false)],[(6,true),(12,true),(1,true),(7,true),(4,false),(3,false),(9,true)])
                      (.node 2371031 ([(5,true),(6,true),(0,true),(1,true),(8,true),(3,false),(10,false)],[(13,false),(12,false),(11,false),(2,false),(7,false),(4,false),(9,true)])
                        (.node 2300921 ([(0,true),(8,false),(3,false),(13,true),(5,true),(11,false),(10,false)],[(4,false),(7,false),(6,false),(12,true),(2,false),(1,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2375819 ([(4,false),(8,false),(6,false),(13,false),(1,true),(2,true),(10,false)],[(5,false),(7,true),(0,true),(12,false),(11,false),(3,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2376209 ([(3,true),(11,true),(1,false),(0,false),(6,false),(5,false),(9,true)],[(13,false),(12,false),(2,true),(7,true),(8,true),(4,false),(10,false)])
                      (.node 2376143 ([(6,false),(13,false),(1,true),(2,true),(8,false),(4,false),(10,false)],[(5,false),(7,false),(0,true),(12,false),(11,false),(3,false),(9,true)])
                        .empty
                        .empty)
                      (.node 2376227 ([(6,false),(13,false),(1,true),(2,true),(3,true),(4,true),(9,true)],[(5,false),(8,false),(7,false),(0,true),(12,false),(11,false),(10,false)])
                        .empty
                        .empty))))))))
        (.node 2516064 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
          (.node 2407307 ([(0,true),(1,true),(8,false),(5,true),(13,false),(3,true),(10,false)],[(6,true),(7,true),(4,false),(11,true),(12,true),(2,false),(9,true)])
            (.node 2388233 ([(1,true),(2,true),(3,true),(11,true),(6,false),(5,false),(9,true)],[(13,false),(12,false),(0,true),(7,true),(8,true),(4,false),(10,false)])
              (.node 2380523 ([(5,true),(6,true),(0,true),(12,false),(3,false),(2,false),(9,true)],[(13,false),(1,true),(8,false),(7,false),(4,false),(11,false),(10,false)])
                (.node 2378915 ([(0,true),(13,true),(5,false),(11,true),(2,false),(8,true),(9,true)],[(6,true),(7,true),(1,false),(12,false),(3,true),(4,true),(10,false)])
                  (.node 2378723 ([(4,true),(5,true),(13,false),(12,false),(2,false),(8,true),(9,true)],[(6,true),(0,true),(1,true),(7,false),(3,false),(11,false),(10,false)])
                    (.node 2378609 ([(7,true),(6,false),(13,false),(12,false),(3,true),(4,true),(9,true)],[(5,false),(8,false),(0,true),(1,true),(2,true),(11,false),(10,false)])
                      (.node 2377253 ([(4,true),(5,true),(13,false),(1,true),(2,true),(11,false),(10,false)],[(6,true),(0,true),(12,false),(3,true),(7,true),(8,true),(9,true)])
                        (.node 2377205 ([(5,true),(6,true),(0,true),(12,false),(2,false),(8,true),(9,true)],[(13,false),(1,true),(7,false),(4,false),(3,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2378621 ([(0,true),(13,true),(5,false),(8,false),(2,true),(3,true),(10,false)],[(6,true),(7,true),(1,false),(12,false),(11,false),(4,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2378831 ([(0,true),(13,true),(5,false),(4,false),(3,false),(2,false),(9,true)],[(6,true),(7,true),(8,true),(1,false),(12,false),(11,false),(10,false)])
                      (.node 2378807 ([(4,true),(5,true),(6,true),(0,true),(12,false),(2,false),(9,true)],[(13,false),(1,true),(8,false),(7,false),(3,false),(11,false),(10,false)])
                        (.node 2378735 ([(2,true),(3,true),(4,true),(5,true),(13,false),(0,false),(9,true)],[(6,true),(8,false),(7,false),(1,false),(12,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2378903 ([(2,true),(3,true),(8,false),(0,true),(13,true),(5,false),(10,false)],[(6,true),(7,false),(1,false),(12,false),(11,false),(4,false),(9,true)])
                        .empty
                        .empty)))
                  (.node 2380229 ([(5,true),(6,true),(0,true),(1,true),(11,true),(3,false),(9,true)],[(13,false),(12,false),(4,true),(7,true),(8,true),(2,false),(10,false)])
                    (.node 2380103 ([(5,true),(6,true),(0,true),(12,false),(3,false),(2,false),(10,false)],[(13,false),(1,true),(11,true),(4,true),(7,true),(8,true),(9,true)])
                      (.node 2379575 ([(2,true),(3,true),(4,true),(5,true),(13,false),(0,false),(10,false)],[(6,true),(11,true),(12,true),(1,true),(7,true),(8,true),(9,true)])
                        (.node 2379527 ([(3,true),(12,true),(0,false),(6,false),(5,false),(8,true),(9,true)],[(13,false),(1,true),(2,true),(7,true),(4,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2380115 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2380325 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                      (.node 2380259 ([(0,true),(13,true),(5,false),(4,false),(11,false),(2,true),(9,true)],[(6,true),(7,true),(8,true),(3,true),(12,true),(1,true),(10,false)])
                        .empty
                        .empty)
                      (.node 2380343 ([(0,true),(13,true),(5,false),(8,false),(3,true),(11,false),(10,false)],[(6,true),(7,true),(2,false),(1,false),(12,false),(4,true),(9,true)])
                        .empty
                        .empty))))
                (.node 2383031 ([(0,true),(13,true),(5,false),(4,false),(8,false),(2,true),(10,false)],[(6,true),(7,true),(1,false),(12,false),(11,false),(3,true),(9,true)])
                  (.node 2382851 ([(2,true),(3,true),(4,true),(5,true),(13,false),(0,false),(9,true)],[(6,true),(8,false),(7,false),(1,false),(12,false),(11,false),(10,false)])
                    (.node 2382677 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                      (.node 2382629 ([(4,true),(11,false),(1,false),(13,true),(6,true),(8,true),(9,true)],[(5,false),(12,true),(0,false),(7,false),(3,false),(2,false),(10,false)])
                        (.node 2380553 ([(0,true),(13,true),(5,false),(4,false),(3,false),(2,false),(9,true)],[(6,true),(7,true),(8,true),(1,false),(12,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2382839 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2382947 ([(0,true),(13,true),(5,false),(4,false),(3,false),(2,false),(9,true)],[(6,true),(7,true),(8,true),(1,false),(12,false),(11,false),(10,false)])
                      (.node 2382923 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2383019 ([(2,true),(11,true),(5,true),(13,false),(0,false),(8,true),(9,true)],[(6,true),(7,false),(1,false),(12,false),(4,false),(3,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 2388053 ([(3,true),(4,true),(5,true),(6,true),(12,true),(1,false),(9,true)],[(13,false),(2,true),(7,true),(8,true),(0,false),(11,false),(10,false)])
                    (.node 2387879 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(10,false)],[(13,false),(12,false),(11,false),(3,true),(7,true),(8,true),(9,true)])
                      (.node 2387831 ([(5,true),(6,true),(11,false),(2,false),(1,false),(8,true),(9,true)],[(13,false),(12,false),(0,true),(7,false),(4,false),(3,false),(10,false)])
                        (.node 2383313 ([(2,true),(8,false),(0,true),(13,true),(5,false),(4,false),(10,false)],[(6,true),(7,false),(1,false),(12,false),(11,false),(3,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2388041 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2388149 ([(1,true),(2,true),(8,false),(5,true),(6,true),(11,false),(10,false)],[(13,false),(12,false),(0,true),(7,true),(4,false),(3,false),(9,true)])
                      (.node 2388125 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2388221 ([(3,true),(11,true),(0,true),(1,true),(13,true),(5,false),(9,true)],[(6,true),(12,true),(2,true),(7,true),(8,true),(4,false),(10,false)])
                        .empty
                        .empty)))))
              (.node 2396723 ([(0,true),(1,true),(13,true),(5,false),(4,false),(3,false),(9,true)],[(6,true),(7,true),(8,true),(2,false),(12,false),(11,false),(10,false)])
                (.node 2396273 ([(5,true),(6,true),(11,true),(3,false),(2,false),(1,false),(9,true)],[(13,false),(12,false),(4,true),(7,true),(8,true),(0,false),(10,false)])
                  (.node 2390549 ([(0,true),(1,true),(13,true),(5,false),(4,false),(3,false),(9,true)],[(6,true),(7,true),(8,true),(2,false),(12,false),(11,false),(10,false)])
                    (.node 2390225 ([(4,false),(8,false),(6,false),(13,false),(1,false),(11,false),(10,false)],[(5,false),(7,true),(0,true),(12,true),(2,true),(3,true),(9,true)])
                      (.node 2388515 ([(3,true),(8,false),(1,true),(12,false),(6,false),(5,false),(10,false)],[(13,false),(2,true),(7,true),(0,false),(11,false),(4,false),(9,true)])
                        (.node 2388467 ([(4,true),(5,true),(6,true),(12,true),(1,false),(8,true),(9,true)],[(13,false),(2,true),(3,true),(7,true),(0,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2390519 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2390633 ([(0,true),(1,true),(13,true),(5,false),(8,false),(3,true),(10,false)],[(6,true),(7,true),(2,false),(12,false),(11,false),(4,true),(9,true)])
                      (.node 2390615 ([(2,false),(1,false),(0,false),(6,false),(5,false),(4,false),(10,false)],[(13,false),(12,false),(11,false),(3,false),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2390909 ([(3,true),(8,false),(0,true),(1,true),(13,true),(5,false),(10,false)],[(6,true),(7,false),(2,false),(12,false),(11,false),(4,false),(9,true)])
                        .empty
                        .empty)))
                  (.node 2396465 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                    (.node 2396381 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                      (.node 2396357 ([(5,true),(6,true),(0,true),(1,true),(12,false),(3,false),(9,true)],[(13,false),(2,true),(8,false),(7,false),(4,false),(11,false),(10,false)])
                        (.node 2396285 ([(3,true),(4,true),(5,true),(13,false),(1,false),(0,false),(10,false)],[(6,true),(11,true),(12,true),(2,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2396453 ([(3,true),(4,true),(5,true),(13,false),(1,false),(0,false),(10,false)],[(6,true),(11,true),(12,true),(2,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2396579 ([(3,true),(4,true),(5,true),(13,false),(1,false),(0,false),(9,true)],[(6,true),(8,false),(7,false),(2,false),(12,false),(11,false),(10,false)])
                      (.node 2396567 ([(5,true),(6,true),(8,false),(3,true),(12,true),(1,false),(10,false)],[(13,false),(2,true),(7,false),(4,false),(11,false),(0,false),(9,true)])
                        .empty
                        .empty)
                      (.node 2396693 ([(5,true),(6,true),(0,true),(1,true),(12,false),(3,false),(9,true)],[(13,false),(2,true),(8,false),(7,false),(4,false),(11,false),(10,false)])
                        .empty
                        .empty))))
                (.node 2404295 ([(5,true),(6,true),(0,true),(8,true),(3,false),(2,false),(10,false)],[(13,false),(12,false),(11,false),(1,false),(7,false),(4,false),(9,true)])
                  (.node 2399093 ([(4,true),(5,true),(6,true),(8,true),(2,false),(1,false),(10,false)],[(13,false),(12,false),(11,false),(0,false),(7,false),(3,false),(9,true)])
                    (.node 2398757 ([(4,true),(5,true),(13,false),(2,true),(8,false),(0,false),(10,false)],[(6,true),(11,true),(12,true),(1,false),(7,false),(3,false),(9,true)])
                      (.node 2396807 ([(0,true),(11,true),(3,false),(2,false),(13,true),(5,false),(9,true)],[(6,true),(7,true),(8,true),(4,false),(12,true),(1,false),(10,false)])
                        (.node 2396789 ([(3,true),(11,false),(1,true),(13,true),(6,true),(8,true),(9,true)],[(5,false),(4,false),(12,true),(2,true),(7,true),(0,true),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2398805 ([(3,true),(4,true),(5,true),(13,false),(1,false),(0,false),(10,false)],[(6,true),(11,true),(12,true),(2,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2399657 ([(1,true),(12,false),(5,true),(6,true),(8,false),(3,false),(10,false)],[(13,false),(2,true),(11,true),(4,false),(7,false),(0,false),(9,true)])
                      (.node 2399141 ([(3,true),(4,true),(12,true),(13,true),(6,true),(0,true),(10,false)],[(5,false),(11,false),(1,true),(2,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2399705 ([(0,true),(8,false),(4,true),(5,true),(13,false),(2,true),(10,false)],[(6,true),(7,true),(3,false),(11,true),(12,true),(1,false),(9,true)])
                        .empty
                        .empty)))
                  (.node 2405243 ([(1,true),(8,false),(3,false),(13,true),(6,true),(11,false),(10,false)],[(5,false),(4,false),(7,false),(0,false),(12,true),(2,false),(9,true)])
                    (.node 2404907 ([(1,true),(2,true),(12,false),(6,false),(5,false),(4,false),(10,false)],[(13,false),(3,true),(11,true),(0,true),(7,true),(8,true),(9,true)])
                      (.node 2404859 ([(2,true),(3,true),(11,true),(6,false),(5,false),(8,true),(9,true)],[(13,false),(12,false),(0,true),(1,true),(7,true),(4,false),(10,false)])
                        (.node 2404343 ([(4,true),(5,true),(13,false),(12,false),(0,true),(1,true),(10,false)],[(6,true),(11,false),(2,true),(3,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2405195 ([(2,true),(3,true),(8,true),(0,false),(6,false),(5,false),(10,false)],[(13,false),(12,false),(11,false),(4,false),(7,false),(1,false),(9,true)])
                        .empty
                        .empty))
                    (.node 2407211 ([(2,true),(12,false),(0,false),(6,false),(5,false),(4,false),(10,false)],[(13,false),(3,true),(11,true),(1,true),(7,true),(8,true),(9,true)])
                      (.node 2407193 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2407277 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(10,false)],[(13,false),(12,false),(11,false),(4,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))))))
            (.node 2423675 ([(2,true),(11,true),(12,true),(13,true),(5,false),(8,true),(9,true)],[(6,true),(0,true),(1,true),(7,true),(4,false),(3,false),(10,false)])
              (.node 2415851 ([(4,true),(5,true),(13,false),(2,false),(8,false),(0,true),(10,false)],[(6,true),(7,false),(3,false),(12,false),(11,false),(1,true),(9,true)])
                (.node 2413367 ([(5,true),(6,true),(8,false),(2,true),(3,true),(11,false),(10,false)],[(13,false),(12,false),(4,true),(7,true),(1,false),(0,false),(9,true)])
                  (.node 2407619 ([(4,true),(5,true),(6,true),(0,true),(12,true),(2,false),(9,true)],[(13,false),(3,true),(7,true),(8,true),(1,false),(11,false),(10,false)])
                    (.node 2407535 ([(4,true),(5,true),(13,false),(2,false),(1,false),(0,false),(9,true)],[(6,true),(8,false),(7,false),(3,false),(12,false),(11,false),(10,false)])
                      (.node 2407433 ([(0,true),(1,true),(8,true),(5,true),(13,false),(3,true),(10,false)],[(6,true),(7,true),(2,true),(12,false),(11,false),(4,true),(9,true)])
                        (.node 2407421 ([(2,true),(3,true),(11,true),(0,false),(6,false),(5,false),(9,true)],[(13,false),(12,false),(1,true),(7,true),(8,true),(4,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2407547 ([(1,false),(0,false),(6,false),(13,false),(3,true),(4,true),(10,false)],[(5,false),(11,true),(12,true),(2,false),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))
                    (.node 2407727 ([(0,true),(1,true),(2,true),(13,true),(5,false),(4,false),(9,true)],[(6,true),(7,true),(8,true),(3,false),(12,false),(11,false),(10,false)])
                      (.node 2407715 ([(2,true),(12,false),(0,false),(6,false),(5,false),(4,false),(9,true)],[(13,false),(3,true),(8,false),(7,false),(1,false),(11,false),(10,false)])
                        (.node 2407643 ([(0,true),(1,true),(8,false),(3,false),(13,true),(5,false),(10,false)],[(6,true),(7,true),(4,true),(11,true),(12,true),(2,false),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2413091 ([(2,true),(3,true),(11,false),(6,false),(5,false),(8,true),(9,true)],[(13,false),(12,false),(4,true),(7,false),(1,false),(0,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 2415485 ([(2,true),(13,true),(5,false),(4,false),(8,true),(0,false),(10,false)],[(6,true),(11,true),(12,true),(3,true),(7,false),(1,false),(9,true)])
                    (.node 2413481 ([(0,true),(11,true),(3,false),(13,true),(5,false),(8,true),(9,true)],[(6,true),(7,true),(4,false),(12,true),(2,false),(1,false),(10,false)])
                      (.node 2413451 ([(5,true),(6,true),(0,true),(11,true),(3,false),(2,false),(9,true)],[(13,false),(12,false),(4,true),(7,true),(8,true),(1,false),(10,false)])
                        (.node 2413385 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2413775 ([(0,true),(8,false),(5,true),(13,false),(3,true),(11,false),(10,false)],[(6,true),(7,true),(4,false),(12,true),(2,false),(1,false),(9,true)])
                        .empty
                        .empty))
                    (.node 2415767 ([(4,true),(5,true),(13,false),(2,false),(1,false),(0,false),(9,true)],[(6,true),(8,false),(7,false),(3,false),(12,false),(11,false),(10,false)])
                      (.node 2415533 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2415779 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty))))
                (.node 2421053 ([(5,true),(6,true),(12,true),(3,false),(8,false),(1,true),(10,false)],[(13,false),(4,true),(7,true),(0,false),(11,false),(2,true),(9,true)])
                  (.node 2416169 ([(0,true),(8,false),(3,false),(13,true),(5,false),(11,false),(10,false)],[(6,true),(7,true),(4,true),(12,true),(2,false),(1,false),(9,true)])
                    (.node 2415959 ([(0,true),(1,true),(2,true),(13,true),(5,false),(4,false),(9,true)],[(6,true),(7,true),(8,true),(3,false),(12,false),(11,false),(10,false)])
                      (.node 2415947 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                        (.node 2415875 ([(0,true),(11,true),(5,true),(13,false),(3,true),(8,true),(9,true)],[(6,true),(7,true),(4,true),(12,true),(2,false),(1,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2416121 ([(1,true),(2,true),(13,true),(5,false),(4,false),(8,true),(9,true)],[(6,true),(0,true),(7,true),(3,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2420969 ([(5,true),(6,true),(12,true),(3,false),(2,false),(1,false),(9,true)],[(13,false),(4,true),(7,true),(8,true),(0,false),(11,false),(10,false)])
                      (.node 2420687 ([(2,false),(8,false),(4,false),(13,true),(6,true),(0,true),(10,false)],[(5,false),(7,false),(3,true),(12,false),(11,false),(1,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2420981 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)))
                  (.node 2421371 ([(1,true),(8,false),(4,false),(13,true),(6,true),(11,false),(10,false)],[(5,false),(7,false),(0,false),(12,true),(3,false),(2,false),(9,true)])
                    (.node 2421161 ([(1,true),(2,true),(3,true),(12,false),(6,false),(5,false),(9,true)],[(13,false),(4,true),(8,false),(7,false),(0,false),(11,false),(10,false)])
                      (.node 2421149 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,true),(8,true),(9,true)])
                        (.node 2421077 ([(1,true),(11,true),(6,false),(5,false),(4,false),(3,false),(9,true)],[(13,false),(12,false),(0,true),(7,true),(8,true),(2,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2421323 ([(2,true),(3,true),(12,false),(6,false),(5,false),(8,true),(9,true)],[(13,false),(4,true),(7,false),(1,false),(0,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2423477 ([(6,false),(5,false),(4,false),(12,false),(1,true),(2,true),(9,true)],[(13,false),(3,false),(8,false),(7,false),(0,true),(11,false),(10,false)])
                      (.node 2423447 ([(5,true),(6,true),(8,true),(3,true),(12,false),(1,true),(10,false)],[(13,false),(4,true),(7,true),(0,true),(11,false),(2,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2423657 ([(5,true),(6,true),(8,false),(1,false),(12,true),(3,false),(10,false)],[(13,false),(4,true),(7,true),(2,true),(11,true),(0,false),(9,true)])
                        .empty
                        .empty)))))
              (.node 2427773 ([(5,true),(13,false),(3,false),(2,false),(1,false),(0,false),(9,true)],[(6,true),(8,false),(7,false),(4,false),(12,false),(11,false),(10,false)])
                (.node 2425169 ([(5,true),(6,true),(0,true),(1,true),(12,true),(3,false),(9,true)],[(13,false),(4,true),(7,true),(8,true),(2,false),(11,false),(10,false)])
                  (.node 2424425 ([(3,true),(12,false),(1,true),(8,false),(6,false),(5,false),(10,false)],[(13,false),(4,true),(11,true),(0,false),(7,false),(2,false),(9,true)])
                    (.node 2423885 ([(2,true),(3,true),(12,false),(0,false),(6,false),(5,false),(9,true)],[(13,false),(4,true),(8,false),(7,false),(1,false),(11,false),(10,false)])
                      (.node 2423771 ([(0,true),(1,true),(8,false),(5,true),(13,false),(3,false),(10,false)],[(6,true),(7,true),(4,false),(12,false),(11,false),(2,false),(9,true)])
                        (.node 2423741 ([(5,true),(6,true),(0,true),(12,true),(3,false),(2,false),(9,true)],[(13,false),(4,true),(7,true),(8,true),(1,false),(11,false),(10,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2423897 ([(0,true),(1,true),(2,true),(3,true),(13,true),(5,false),(9,true)],[(6,true),(7,true),(8,true),(4,false),(12,false),(11,false),(10,false)])
                        .empty
                        .empty))
                    (.node 2425085 ([(5,true),(6,true),(11,true),(12,true),(3,false),(8,true),(9,true)],[(13,false),(4,true),(7,true),(2,false),(1,false),(0,false),(10,false)])
                      (.node 2424473 ([(2,true),(3,true),(12,false),(0,false),(6,false),(5,false),(10,false)],[(13,false),(4,true),(11,true),(1,true),(7,true),(8,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2425097 ([(3,true),(4,true),(5,true),(6,true),(11,true),(1,false),(9,true)],[(13,false),(12,false),(2,true),(7,true),(8,true),(0,false),(10,false)])
                        .empty
                        .empty)))
                  (.node 2425391 ([(7,true),(5,true),(13,false),(12,false),(1,false),(0,false),(9,true)],[(6,true),(8,false),(4,false),(3,false),(2,false),(11,false),(10,false)])
                    (.node 2425277 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                      (.node 2425265 ([(3,true),(12,false),(1,false),(0,false),(6,false),(5,false),(9,true)],[(13,false),(4,true),(8,false),(7,false),(2,false),(11,false),(10,false)])
                        (.node 2425193 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(10,false)],[(13,false),(12,false),(11,false),(0,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2425379 ([(5,true),(6,true),(8,false),(3,true),(12,false),(1,false),(10,false)],[(13,false),(4,true),(7,true),(2,false),(11,false),(0,false),(9,true)])
                        .empty
                        .empty))
                    (.node 2426795 ([(0,true),(8,false),(2,false),(12,true),(13,true),(5,false),(10,false)],[(6,true),(7,true),(3,true),(4,true),(11,true),(1,false),(9,true)])
                      (.node 2426747 ([(1,true),(2,true),(8,true),(6,false),(13,false),(4,true),(10,false)],[(5,false),(11,true),(12,true),(3,false),(7,false),(0,false),(9,true)])
                        .empty
                        .empty)
                      (.node 2427497 ([(2,true),(3,true),(13,true),(5,false),(8,true),(0,false),(10,false)],[(6,true),(11,true),(12,true),(4,true),(7,false),(1,false),(9,true)])
                        .empty
                        .empty))))
                (.node 2514510 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 2432657 ([(3,true),(4,true),(5,true),(6,true),(8,true),(1,false),(10,false)],[(13,false),(12,false),(11,false),(0,false),(7,false),(2,false),(9,true)])
                    (.node 2427887 ([(0,true),(11,true),(3,true),(13,true),(5,false),(8,true),(9,true)],[(6,true),(7,true),(4,false),(12,false),(2,false),(1,false),(10,false)])
                      (.node 2427857 ([(5,true),(13,false),(3,false),(2,false),(8,false),(0,true),(10,false)],[(6,true),(7,false),(4,false),(12,false),(11,false),(1,true),(9,true)])
                        (.node 2427791 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(10,false)],[(13,false),(12,false),(11,false),(1,true),(7,true),(8,true),(9,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2428181 ([(0,true),(8,false),(5,true),(13,false),(3,false),(2,false),(10,false)],[(6,true),(7,true),(4,false),(12,false),(11,false),(1,false),(9,true)])
                        .empty
                        .empty))
                    (.node 2513124 ([(5,true),(8,false),(0,false),(13,false),(2,true),(3,true),(10,true)],[(6,false),(9,true),(4,true),(7,true),(1,true),(12,false),(11,false)])
                      (.node 2432969 ([(6,false),(5,false),(4,false),(3,false),(8,true),(1,true),(10,false)],[(13,false),(12,false),(11,false),(2,true),(7,false),(0,true),(9,true)])
                        .empty
                        .empty)
                      (.node 2514462 ([(6,true),(0,true),(1,true),(2,true),(8,true),(4,false),(11,false)],[(13,false),(12,false),(3,false),(7,false),(5,false),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 2515722 ([(6,true),(0,true),(1,true),(2,true),(9,true),(4,false),(11,false)],[(13,false),(12,false),(3,false),(8,false),(7,false),(5,false),(10,true)])
                    (.node 2515638 ([(6,true),(0,true),(8,false),(2,false),(12,false),(4,true),(10,true)],[(13,false),(1,false),(9,true),(5,true),(7,true),(3,true),(11,false)])
                      (.node 2515182 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 2515134 ([(6,true),(0,true),(8,true),(4,false),(12,true),(2,true),(10,true)],[(13,false),(1,false),(7,false),(5,false),(9,true),(3,true),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2515656 ([(3,true),(12,true),(1,false),(0,false),(6,false),(5,false),(10,true)],[(13,false),(2,true),(7,true),(8,true),(9,true),(4,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2515980 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2515752 ([(1,true),(13,true),(6,false),(5,false),(9,false),(3,true),(11,false)],[(0,true),(7,true),(8,true),(2,false),(12,false),(4,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2515992 ([(3,true),(4,true),(8,true),(1,true),(13,true),(6,false),(10,true)],[(0,true),(9,true),(5,false),(7,false),(2,false),(12,false),(11,false)])
                        .empty
                        .empty)))))))
          (.node 2558580 ([(3,true),(4,true),(13,true),(6,false),(8,true),(1,false),(11,false)],[(0,true),(12,true),(5,true),(7,false),(2,false),(9,true),(10,true)])
            (.node 2536062 ([(4,true),(5,true),(6,true),(13,false),(2,false),(1,false),(10,true)],[(0,true),(9,false),(8,false),(7,false),(3,false),(12,false),(11,false)])
              (.node 2525298 ([(6,true),(0,true),(12,true),(2,false),(8,false),(4,true),(10,true)],[(13,false),(3,true),(7,false),(5,false),(9,false),(1,false),(11,false)])
                (.node 2517924 ([(3,true),(9,false),(6,true),(0,true),(1,true),(12,false),(11,false)],[(13,false),(2,true),(7,true),(8,true),(5,false),(4,false),(10,true)])
                  (.node 2517372 ([(4,true),(5,true),(6,true),(13,false),(1,false),(9,true),(10,true)],[(0,true),(8,false),(7,false),(3,false),(2,false),(12,false),(11,false)])
                    (.node 2516832 ([(3,true),(4,true),(5,true),(6,true),(13,false),(1,false),(10,true)],[(0,true),(9,false),(8,false),(7,false),(2,false),(12,false),(11,false)])
                      (.node 2516784 ([(4,true),(5,true),(8,true),(2,false),(13,true),(0,true),(10,true)],[(6,false),(7,false),(3,false),(9,true),(1,true),(12,false),(11,false)])
                        (.node 2516088 ([(1,true),(13,true),(6,false),(5,false),(8,true),(3,true),(11,false)],[(0,true),(7,true),(4,false),(12,true),(2,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2517360 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2517696 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2517600 ([(1,true),(13,true),(6,false),(5,false),(4,false),(3,false),(10,true)],[(0,true),(7,true),(8,true),(9,true),(2,false),(12,false),(11,false)])
                        (.node 2517582 ([(4,true),(5,true),(8,false),(0,false),(13,false),(2,true),(10,true)],[(6,false),(9,true),(3,true),(7,true),(1,true),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2517714 ([(3,true),(9,false),(1,true),(13,true),(6,false),(5,false),(11,false)],[(0,true),(8,false),(7,false),(2,false),(12,false),(4,false),(10,true)])
                        .empty
                        .empty)))
                  (.node 2520096 ([(5,true),(6,true),(13,false),(1,false),(8,false),(3,true),(10,true)],[(0,true),(9,true),(4,true),(7,true),(2,false),(12,false),(11,false)])
                    (.node 2518512 ([(3,true),(4,true),(12,true),(1,false),(0,false),(6,false),(10,true)],[(13,false),(2,true),(7,true),(8,true),(9,true),(5,false),(11,false)])
                      (.node 2518464 ([(4,true),(12,true),(2,true),(8,false),(0,false),(6,false),(10,true)],[(13,false),(1,false),(7,false),(3,false),(9,true),(5,false),(11,false)])
                        (.node 2517936 ([(1,true),(13,true),(6,false),(8,false),(3,true),(4,true),(11,false)],[(0,true),(7,true),(2,false),(12,false),(5,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2519934 ([(4,true),(8,false),(0,false),(6,false),(12,true),(2,true),(10,true)],[(13,false),(1,false),(7,false),(3,false),(9,false),(5,true),(11,false)])
                        .empty
                        .empty))
                    (.node 2520522 ([(4,true),(9,false),(8,false),(1,true),(13,true),(6,false),(11,false)],[(0,true),(7,false),(3,false),(2,false),(12,false),(5,false),(10,true)])
                      (.node 2520108 ([(3,true),(4,true),(8,true),(0,false),(13,false),(12,false),(11,false)],[(6,false),(5,false),(7,false),(2,false),(1,false),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2525136 ([(5,true),(8,false),(1,false),(0,false),(13,false),(3,true),(10,true)],[(6,false),(9,true),(4,true),(7,true),(2,true),(12,false),(11,false)])
                        .empty
                        .empty))))
                (.node 2533950 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 2533614 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                    (.node 2532462 ([(1,false),(8,false),(6,true),(13,false),(3,true),(4,true),(10,true)],[(0,true),(9,true),(5,true),(7,false),(2,true),(12,false),(11,false)])
                      (.node 2525724 ([(5,true),(6,true),(13,false),(3,true),(8,false),(1,false),(11,false)],[(0,true),(12,true),(2,false),(7,false),(4,false),(9,true),(10,true)])
                        (.node 2525310 ([(4,true),(5,true),(6,true),(13,false),(2,false),(1,false),(11,false)],[(0,true),(12,true),(3,true),(7,true),(8,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2532510 ([(1,true),(8,false),(6,true),(13,false),(3,true),(4,true),(10,true)],[(0,true),(7,true),(5,false),(9,false),(2,true),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2533710 ([(4,true),(5,true),(6,true),(13,false),(2,false),(1,false),(10,true)],[(0,true),(9,false),(8,false),(7,false),(3,false),(12,false),(11,false)])
                      (.node 2533638 ([(2,true),(3,true),(9,true),(0,false),(6,false),(5,false),(11,false)],[(13,false),(12,false),(4,false),(8,false),(7,false),(1,false),(10,true)])
                        .empty
                        .empty)
                      (.node 2533722 ([(2,true),(12,false),(4,false),(8,true),(6,true),(0,true),(10,true)],[(13,false),(3,true),(7,false),(1,false),(9,false),(5,false),(11,false)])
                        .empty
                        .empty)))
                  (.node 2534568 ([(1,true),(2,true),(13,true),(6,false),(5,false),(4,false),(10,true)],[(0,true),(7,true),(8,true),(9,true),(3,false),(12,false),(11,false)])
                    (.node 2534064 ([(1,true),(2,true),(13,true),(6,false),(8,false),(4,true),(11,false)],[(0,true),(7,true),(3,false),(12,false),(5,true),(9,true),(10,true)])
                      (.node 2534046 ([(4,true),(5,true),(8,false),(0,false),(13,false),(2,false),(10,true)],[(6,false),(9,true),(1,false),(7,false),(3,false),(12,false),(11,false)])
                        (.node 2533980 ([(1,true),(2,true),(13,true),(6,false),(8,true),(4,true),(11,false)],[(0,true),(7,true),(5,false),(12,true),(3,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2534520 ([(2,true),(13,true),(6,false),(8,true),(9,true),(4,true),(11,false)],[(0,true),(1,true),(7,true),(5,false),(12,true),(3,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2535240 ([(1,true),(8,false),(3,false),(13,true),(6,false),(5,false),(11,false)],[(0,true),(7,true),(4,true),(12,true),(2,false),(9,true),(10,true)])
                      (.node 2535192 ([(2,true),(3,true),(8,true),(0,false),(6,false),(5,false),(11,false)],[(13,false),(12,false),(4,false),(7,false),(1,false),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2536014 ([(5,true),(6,true),(13,false),(2,false),(8,true),(9,true),(10,true)],[(0,true),(1,true),(7,false),(4,false),(3,false),(12,false),(11,false)])
                        .empty
                        .empty)))))
              (.node 2543994 ([(5,true),(6,true),(0,true),(1,true),(12,true),(3,false),(10,true)],[(13,false),(4,true),(7,true),(8,true),(9,true),(2,false),(11,false)])
                (.node 2541552 ([(6,true),(0,true),(12,true),(4,true),(8,false),(2,true),(10,true)],[(13,false),(3,false),(9,false),(5,true),(7,true),(1,false),(11,false)])
                  (.node 2537250 ([(2,true),(12,false),(6,true),(0,true),(8,false),(4,true),(10,true)],[(13,false),(3,true),(7,false),(1,false),(9,true),(5,true),(11,false)])
                    (.node 2536914 ([(2,true),(3,true),(4,true),(8,true),(0,false),(6,false),(11,false)],[(13,false),(12,false),(5,false),(7,false),(1,false),(9,true),(10,true)])
                      (.node 2536398 ([(4,true),(8,false),(0,false),(6,false),(12,true),(2,false),(10,true)],[(13,false),(3,true),(7,true),(1,true),(9,false),(5,true),(11,false)])
                        (.node 2536350 ([(5,true),(6,true),(13,false),(3,true),(8,false),(1,true),(10,true)],[(0,true),(7,false),(4,false),(9,true),(2,true),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2536962 ([(1,true),(2,true),(13,true),(6,false),(5,false),(4,false),(10,true)],[(0,true),(7,true),(8,true),(9,true),(3,false),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2541216 ([(6,true),(0,true),(12,true),(3,false),(8,true),(9,true),(10,true)],[(13,false),(4,true),(5,true),(7,true),(2,false),(1,false),(11,false)])
                      (.node 2537298 ([(1,true),(8,false),(3,false),(13,true),(6,false),(5,false),(10,true)],[(0,true),(7,true),(4,true),(9,false),(2,true),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2541264 ([(5,true),(6,true),(0,true),(12,true),(3,false),(2,false),(10,true)],[(13,false),(4,true),(7,true),(8,true),(9,true),(1,false),(11,false)])
                        .empty
                        .empty)))
                  (.node 2542500 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                    (.node 2542164 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2542116 ([(3,true),(4,true),(9,false),(8,false),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(2,true),(7,true),(5,false),(10,true)])
                        (.node 2541600 ([(5,true),(6,true),(13,false),(3,false),(2,false),(1,false),(11,false)],[(0,true),(12,true),(4,true),(7,true),(8,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2542452 ([(3,true),(4,true),(8,true),(9,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(2,true),(7,true),(5,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2543322 ([(5,true),(6,true),(13,false),(3,false),(2,false),(1,false),(10,true)],[(0,true),(9,false),(8,false),(7,false),(4,false),(12,false),(11,false)])
                      (.node 2543274 ([(6,true),(0,true),(9,false),(8,false),(3,true),(12,false),(11,false)],[(13,false),(4,true),(5,true),(7,true),(2,false),(1,false),(10,true)])
                        .empty
                        .empty)
                      (.node 2543946 ([(6,true),(0,true),(8,true),(4,false),(3,false),(2,false),(11,false)],[(13,false),(12,false),(1,false),(7,false),(5,false),(9,true),(10,true)])
                        .empty
                        .empty))))
                (.node 2546004 ([(5,false),(8,false),(0,false),(13,false),(3,false),(2,false),(10,true)],[(6,false),(7,true),(1,true),(9,false),(4,false),(12,false),(11,false)])
                  (.node 2544792 ([(5,true),(6,true),(0,true),(8,false),(3,true),(12,false),(11,false)],[(13,false),(4,true),(7,true),(2,false),(1,false),(9,true),(10,true)])
                    (.node 2544534 ([(6,true),(0,true),(1,true),(12,true),(3,false),(9,true),(10,true)],[(13,false),(4,true),(5,true),(7,true),(8,true),(2,false),(11,false)])
                      (.node 2544468 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 2544450 ([(6,true),(0,true),(8,false),(2,false),(12,true),(4,true),(10,true)],[(13,false),(3,false),(7,false),(5,false),(9,false),(1,true),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2544564 ([(1,true),(2,true),(3,true),(13,true),(6,false),(5,false),(10,true)],[(0,true),(7,true),(8,true),(9,true),(4,false),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2544876 ([(5,true),(6,true),(0,true),(8,true),(3,true),(12,false),(11,false)],[(13,false),(4,true),(7,true),(1,true),(2,true),(9,true),(10,true)])
                      (.node 2544804 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2544900 ([(1,true),(2,true),(8,false),(4,false),(13,true),(6,false),(10,true)],[(0,true),(7,true),(5,true),(9,false),(3,true),(12,false),(11,false)])
                        .empty
                        .empty)))
                  (.node 2553378 ([(2,true),(3,true),(4,true),(8,true),(0,false),(6,false),(11,false)],[(13,false),(12,false),(5,false),(7,false),(1,false),(9,true),(10,true)])
                    (.node 2553204 ([(3,true),(4,true),(9,true),(1,false),(0,false),(6,false),(11,false)],[(13,false),(12,false),(5,false),(8,false),(7,false),(2,false),(10,true)])
                      (.node 2552790 ([(2,true),(8,false),(4,false),(12,false),(6,true),(0,true),(10,true)],[(13,false),(3,false),(9,true),(1,true),(7,true),(5,true),(11,false)])
                        (.node 2546052 ([(5,true),(8,false),(0,false),(13,false),(3,false),(2,false),(10,true)],[(6,false),(9,true),(1,false),(7,false),(4,false),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2553216 ([(1,true),(2,true),(8,true),(4,false),(13,true),(6,false),(11,false)],[(0,true),(7,true),(3,true),(12,false),(5,false),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2558406 ([(4,true),(12,false),(0,false),(6,false),(8,false),(2,true),(10,true)],[(13,false),(5,true),(9,true),(3,true),(7,true),(1,false),(11,false)])
                      (.node 2557992 ([(3,true),(8,false),(5,false),(13,true),(0,true),(1,true),(10,true)],[(6,false),(7,false),(2,false),(9,false),(4,true),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2558418 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))))))
            (.node 2651712 ([(0,true),(1,true),(2,true),(3,true),(8,true),(5,false),(11,false)],[(13,false),(12,false),(4,false),(7,false),(6,false),(9,true),(10,true)])
              (.node 2562792 ([(1,true),(9,false),(8,false),(6,true),(13,false),(12,false),(11,false)],[(0,true),(7,true),(5,false),(4,false),(3,false),(2,false),(10,true)])
                (.node 2561142 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 2560800 ([(4,true),(12,false),(1,false),(0,false),(6,false),(9,true),(10,true)],[(13,false),(5,true),(8,false),(7,false),(3,false),(2,false),(11,false)])
                    (.node 2560578 ([(6,true),(0,true),(1,true),(12,true),(4,false),(3,false),(10,true)],[(13,false),(5,true),(7,true),(8,true),(9,true),(2,false),(11,false)])
                      (.node 2560050 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 2560002 ([(4,true),(12,false),(2,true),(8,false),(6,true),(0,true),(10,true)],[(13,false),(5,true),(7,false),(3,false),(9,true),(1,true),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2560590 ([(4,true),(5,true),(6,true),(0,true),(9,true),(2,false),(11,false)],[(13,false),(12,false),(1,false),(8,false),(7,false),(3,false),(10,true)])
                        .empty
                        .empty))
                    (.node 2560914 ([(6,true),(0,true),(8,false),(2,false),(12,true),(4,false),(10,true)],[(13,false),(5,true),(7,true),(3,true),(9,false),(1,true),(11,false)])
                      (.node 2560818 ([(1,true),(12,true),(13,true),(6,false),(8,false),(3,false),(10,true)],[(0,true),(7,true),(4,true),(5,true),(9,true),(2,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2560932 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 2562450 ([(2,true),(3,true),(8,false),(5,false),(13,true),(0,true),(10,true)],[(6,false),(7,false),(1,false),(9,false),(4,true),(12,false),(11,false)])
                    (.node 2561730 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2561682 ([(4,true),(5,true),(6,true),(0,true),(8,true),(2,false),(11,false)],[(13,false),(12,false),(1,false),(7,false),(3,false),(9,true),(10,true)])
                        (.node 2561154 ([(1,true),(2,true),(8,true),(6,true),(13,false),(4,false),(10,true)],[(0,true),(7,true),(3,true),(9,false),(5,false),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2562426 ([(6,true),(0,true),(1,true),(8,true),(4,true),(12,false),(11,false)],[(13,false),(5,true),(7,true),(2,true),(3,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2562534 ([(2,true),(3,true),(4,true),(13,true),(6,false),(9,true),(10,true)],[(0,true),(1,true),(7,true),(8,true),(5,false),(12,false),(11,false)])
                      (.node 2562522 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2562762 ([(6,true),(0,true),(1,true),(9,false),(4,true),(12,false),(11,false)],[(13,false),(5,true),(7,true),(8,true),(3,false),(2,false),(10,true)])
                        .empty
                        .empty))))
                (.node 2640546 ([(6,true),(0,true),(13,false),(2,false),(8,false),(4,true),(10,true)],[(1,true),(9,true),(5,true),(7,true),(3,false),(12,false),(11,false)])
                  (.node 2564004 ([(2,true),(3,true),(8,true),(0,false),(13,false),(5,true),(10,true)],[(6,false),(9,false),(1,true),(7,true),(4,true),(12,false),(11,false)])
                    (.node 2563332 ([(2,true),(12,true),(13,true),(6,false),(8,true),(9,true),(10,true)],[(0,true),(1,true),(7,true),(5,false),(4,false),(3,false),(11,false)])
                      (.node 2562876 ([(1,true),(9,false),(6,true),(13,false),(4,false),(3,false),(11,false)],[(0,true),(7,true),(8,true),(5,false),(12,false),(2,false),(10,true)])
                        (.node 2562858 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2563380 ([(1,true),(8,false),(6,true),(13,false),(4,false),(3,false),(11,false)],[(0,true),(7,true),(5,false),(12,false),(2,false),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2565390 ([(2,true),(9,false),(8,false),(6,true),(13,false),(4,false),(11,false)],[(0,true),(1,true),(7,true),(5,false),(12,false),(3,false),(10,true)])
                      (.node 2564052 ([(1,true),(2,true),(3,true),(4,true),(13,true),(6,false),(10,true)],[(0,true),(7,true),(8,true),(9,true),(5,false),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2640384 ([(5,true),(8,false),(1,false),(0,false),(12,true),(3,true),(10,true)],[(13,false),(2,false),(7,false),(4,false),(9,false),(6,true),(11,false)])
                        .empty
                        .empty)))
                  (.node 2650848 ([(4,true),(5,true),(8,true),(2,true),(13,true),(0,false),(10,true)],[(1,true),(9,true),(6,false),(7,false),(3,false),(12,false),(11,false)])
                    (.node 2650038 ([(6,true),(8,false),(1,false),(13,false),(3,true),(4,true),(10,true)],[(0,false),(9,true),(5,true),(7,true),(2,true),(12,false),(11,false)])
                      (.node 2640972 ([(5,true),(9,false),(8,false),(2,true),(13,true),(0,false),(11,false)],[(1,true),(7,false),(4,false),(3,false),(12,false),(6,false),(10,true)])
                        (.node 2640558 ([(4,true),(5,true),(8,true),(1,false),(13,false),(12,false),(11,false)],[(0,false),(6,false),(7,false),(3,false),(2,false),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2650836 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2650944 ([(2,true),(13,true),(0,false),(6,false),(8,true),(4,true),(11,false)],[(1,true),(7,true),(5,false),(12,true),(3,true),(9,true),(10,true)])
                      (.node 2650920 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2651424 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)))))
              (.node 2654946 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 2653992 ([(5,true),(6,true),(8,true),(3,false),(13,true),(1,true),(10,true)],[(0,false),(7,false),(4,false),(9,true),(2,true),(12,false),(11,false)])
                  (.node 2652960 ([(2,true),(13,true),(0,false),(6,false),(9,false),(4,true),(11,false)],[(1,true),(7,true),(8,true),(3,false),(12,false),(5,true),(10,true)])
                    (.node 2652864 ([(4,true),(12,true),(2,false),(1,false),(0,false),(6,false),(10,true)],[(13,false),(3,true),(7,true),(8,true),(9,true),(5,false),(11,false)])
                      (.node 2652384 ([(0,true),(1,true),(8,true),(5,false),(12,true),(3,true),(10,true)],[(13,false),(2,false),(7,false),(6,false),(9,true),(4,true),(11,false)])
                        (.node 2652096 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2652888 ([(0,true),(1,true),(8,false),(3,false),(12,false),(5,true),(10,true)],[(13,false),(2,false),(9,true),(6,true),(7,true),(4,true),(11,false)])
                        .empty
                        .empty))
                    (.node 2653320 ([(5,true),(12,true),(3,true),(8,false),(1,false),(0,false),(10,true)],[(13,false),(2,false),(7,false),(4,false),(9,true),(6,false),(11,false)])
                      (.node 2652972 ([(0,true),(1,true),(2,true),(3,true),(9,true),(5,false),(11,false)],[(13,false),(12,false),(4,false),(8,false),(7,false),(6,false),(10,true)])
                        .empty
                        .empty)
                      (.node 2653368 ([(4,true),(5,true),(12,true),(2,false),(1,false),(0,false),(10,true)],[(13,false),(3,true),(7,true),(8,true),(9,true),(6,false),(11,false)])
                        .empty
                        .empty)))
                  (.node 2654610 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    (.node 2654514 ([(2,true),(13,true),(0,false),(6,false),(5,false),(4,false),(10,true)],[(1,true),(7,true),(8,true),(9,true),(3,false),(12,false),(11,false)])
                      (.node 2654496 ([(5,true),(6,true),(8,false),(1,false),(13,false),(3,true),(10,true)],[(0,false),(9,true),(4,true),(7,true),(2,true),(12,false),(11,false)])
                        (.node 2654040 ([(4,true),(5,true),(6,true),(0,true),(13,false),(2,false),(10,true)],[(1,true),(9,false),(8,false),(7,false),(3,false),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2654580 ([(5,true),(6,true),(0,true),(13,false),(2,false),(9,true),(10,true)],[(1,true),(8,false),(7,false),(4,false),(3,false),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2654850 ([(2,true),(13,true),(0,false),(8,false),(4,true),(5,true),(11,false)],[(1,true),(7,true),(3,false),(12,false),(6,true),(9,true),(10,true)])
                      (.node 2654838 ([(4,true),(9,false),(0,true),(1,true),(2,true),(12,false),(11,false)],[(13,false),(3,true),(7,true),(8,true),(6,false),(5,false),(10,true)])
                        .empty
                        .empty)
                      (.node 2654922 ([(4,true),(9,false),(2,true),(13,true),(0,false),(6,false),(11,false)],[(1,true),(8,false),(7,false),(3,false),(12,false),(5,false),(10,true)])
                        .empty
                        .empty))))
                (.node 2660580 ([(6,true),(0,true),(13,false),(4,true),(8,false),(2,false),(11,false)],[(1,true),(12,true),(3,false),(7,false),(5,false),(9,true),(10,true)])
                  (.node 2657364 ([(3,true),(4,true),(5,true),(8,true),(1,false),(0,false),(11,false)],[(13,false),(12,false),(6,false),(7,false),(2,false),(9,true),(10,true)])
                    (.node 2656800 ([(6,true),(0,true),(13,false),(4,true),(8,false),(2,true),(10,true)],[(1,true),(7,false),(5,false),(9,true),(3,true),(12,false),(11,false)])
                      (.node 2656512 ([(5,true),(6,true),(0,true),(13,false),(3,false),(2,false),(10,true)],[(1,true),(9,false),(8,false),(7,false),(4,false),(12,false),(11,false)])
                        (.node 2656464 ([(6,true),(0,true),(13,false),(3,false),(8,true),(9,true),(10,true)],[(1,true),(2,true),(7,false),(5,false),(4,false),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2656848 ([(5,true),(8,false),(1,false),(0,false),(12,true),(3,false),(10,true)],[(13,false),(4,true),(7,true),(2,true),(9,false),(6,true),(11,false)])
                        .empty
                        .empty))
                    (.node 2657700 ([(3,true),(12,false),(0,true),(1,true),(8,false),(5,true),(10,true)],[(13,false),(4,true),(7,false),(2,false),(9,true),(6,true),(11,false)])
                      (.node 2657412 ([(2,true),(3,true),(13,true),(0,false),(6,false),(5,false),(10,true)],[(1,true),(7,true),(8,true),(9,true),(4,false),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2657748 ([(2,true),(8,false),(4,false),(13,true),(0,false),(6,false),(10,true)],[(1,true),(7,true),(5,true),(9,false),(3,true),(12,false),(11,false)])
                        .empty
                        .empty)))
                  (.node 2669718 ([(2,true),(8,false),(0,true),(13,false),(4,true),(5,true),(10,true)],[(1,true),(7,true),(6,false),(9,false),(3,true),(12,false),(11,false)])
                    (.node 2662548 ([(0,true),(1,true),(12,true),(3,false),(8,false),(5,true),(10,true)],[(13,false),(4,true),(7,false),(6,false),(9,false),(2,false),(11,false)])
                      (.node 2662518 ([(5,true),(6,true),(0,true),(13,false),(3,false),(2,false),(11,false)],[(1,true),(12,true),(4,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 2662050 ([(6,true),(8,false),(2,false),(1,false),(13,false),(4,true),(10,true)],[(0,false),(9,true),(5,true),(7,true),(3,true),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2669670 ([(2,false),(8,false),(0,true),(13,false),(4,true),(5,true),(10,true)],[(1,true),(9,true),(6,true),(7,false),(3,true),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2670096 ([(2,true),(8,false),(4,false),(13,true),(0,false),(6,false),(11,false)],[(1,true),(7,true),(5,true),(12,true),(3,false),(9,true),(10,true)])
                      (.node 2670048 ([(3,true),(4,true),(8,true),(1,false),(0,false),(6,false),(11,false)],[(13,false),(12,false),(5,false),(7,false),(2,false),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2670624 ([(5,true),(6,true),(0,true),(13,false),(3,false),(2,false),(10,true)],[(1,true),(9,false),(8,false),(7,false),(4,false),(12,false),(11,false)])
                        .empty
                        .empty)))))))))
      (.node 2947902 ([(6,true),(12,false),(1,false),(8,true),(3,true),(4,true),(10,true)],[(13,false),(0,true),(7,false),(5,false),(9,false),(2,false),(11,false)])
        (.node 2804526 ([(3,false),(8,false),(1,true),(13,false),(5,true),(6,true),(10,true)],[(2,true),(9,true),(0,true),(7,false),(4,true),(12,false),(11,false)])
          (.node 2717340 ([(3,true),(12,true),(13,true),(1,false),(8,false),(5,false),(10,true)],[(2,true),(7,true),(6,true),(0,true),(9,true),(4,false),(11,false)])
            (.node 2695332 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
              (.node 2679324 ([(4,true),(5,true),(9,false),(8,false),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(3,true),(7,true),(6,false),(10,true)])
                (.node 2673654 ([(4,true),(5,true),(9,true),(2,false),(1,false),(0,false),(11,false)],[(13,false),(12,false),(6,false),(8,false),(7,false),(3,false),(10,true)])
                  (.node 2671188 ([(2,true),(3,true),(13,true),(0,false),(8,true),(5,true),(11,false)],[(1,true),(7,true),(6,false),(12,true),(4,true),(9,true),(10,true)])
                    (.node 2670960 ([(5,true),(6,true),(8,false),(1,false),(13,false),(3,false),(10,true)],[(0,false),(9,true),(2,false),(7,false),(4,false),(12,false),(11,false)])
                      (.node 2670864 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 2670846 ([(3,true),(4,true),(9,true),(1,false),(0,false),(6,false),(11,false)],[(13,false),(12,false),(5,false),(8,false),(7,false),(2,false),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2670978 ([(2,true),(3,true),(13,true),(0,false),(8,false),(5,true),(11,false)],[(1,true),(7,true),(4,false),(12,false),(6,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2671776 ([(2,true),(3,true),(13,true),(0,false),(6,false),(5,false),(10,true)],[(1,true),(7,true),(8,true),(9,true),(4,false),(12,false),(11,false)])
                      (.node 2671728 ([(3,true),(13,true),(0,false),(8,true),(9,true),(5,true),(11,false)],[(1,true),(2,true),(7,true),(6,false),(12,true),(4,true),(10,true)])
                        (.node 2671200 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2673240 ([(3,true),(8,false),(5,false),(12,false),(0,true),(1,true),(10,true)],[(13,false),(4,false),(9,true),(2,true),(7,true),(6,true),(11,false)])
                        .empty
                        .empty)))
                  (.node 2678178 ([(6,true),(0,true),(1,true),(12,true),(4,false),(3,false),(10,true)],[(13,false),(5,true),(7,true),(8,true),(9,true),(2,false),(11,false)])
                    (.node 2677308 ([(4,true),(5,true),(8,true),(9,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(3,true),(7,true),(6,true),(10,true)])
                      (.node 2673828 ([(3,true),(4,true),(5,true),(8,true),(1,false),(0,false),(11,false)],[(13,false),(12,false),(6,false),(7,false),(2,false),(9,true),(10,true)])
                        (.node 2673666 ([(2,true),(3,true),(8,true),(5,false),(13,true),(0,false),(11,false)],[(1,true),(7,true),(4,true),(12,false),(6,false),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2677356 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2678514 ([(6,true),(0,true),(13,false),(4,false),(3,false),(2,false),(11,false)],[(1,true),(12,true),(5,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2678466 ([(0,true),(1,true),(12,true),(4,false),(8,true),(9,true),(10,true)],[(13,false),(5,true),(6,true),(7,true),(3,false),(2,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2678802 ([(0,true),(1,true),(12,true),(5,true),(8,false),(3,true),(10,true)],[(13,false),(4,false),(9,false),(6,true),(7,true),(2,false),(11,false)])
                        .empty
                        .empty))))
                (.node 2681196 ([(0,true),(1,true),(8,true),(5,false),(4,false),(3,false),(11,false)],[(13,false),(12,false),(2,false),(7,false),(6,false),(9,true),(10,true)])
                  (.node 2679756 ([(2,true),(3,true),(8,false),(5,false),(13,true),(0,false),(10,true)],[(1,true),(7,true),(6,true),(9,false),(4,true),(12,false),(11,false)])
                    (.node 2679660 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2679648 ([(6,true),(0,true),(1,true),(8,false),(4,true),(12,false),(11,false)],[(13,false),(5,true),(7,true),(3,false),(2,false),(9,true),(10,true)])
                        (.node 2679372 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2679732 ([(6,true),(0,true),(1,true),(8,true),(4,true),(12,false),(11,false)],[(13,false),(5,true),(7,true),(2,true),(3,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2680524 ([(0,true),(1,true),(9,false),(8,false),(4,true),(12,false),(11,false)],[(13,false),(5,true),(6,true),(7,true),(3,false),(2,false),(10,true)])
                      (.node 2680236 ([(6,true),(0,true),(13,false),(4,false),(3,false),(2,false),(10,true)],[(1,true),(9,false),(8,false),(7,false),(5,false),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2680908 ([(6,true),(0,true),(1,true),(2,true),(12,true),(4,false),(10,true)],[(13,false),(5,true),(7,true),(8,true),(9,true),(3,false),(11,false)])
                        .empty
                        .empty)))
                  (.node 2682966 ([(6,true),(8,false),(1,false),(13,false),(4,false),(3,false),(10,true)],[(0,false),(9,true),(2,false),(7,false),(5,false),(12,false),(11,false)])
                    (.node 2681772 ([(2,true),(3,true),(4,true),(13,true),(0,false),(6,false),(10,true)],[(1,true),(7,true),(8,true),(9,true),(5,false),(12,false),(11,false)])
                      (.node 2681700 ([(0,true),(1,true),(8,false),(3,false),(12,true),(5,true),(10,true)],[(13,false),(4,false),(7,false),(6,false),(9,false),(2,true),(11,false)])
                        (.node 2681676 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2681784 ([(0,true),(1,true),(2,true),(12,true),(4,false),(9,true),(10,true)],[(13,false),(5,true),(6,true),(7,true),(8,true),(3,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2695200 ([(4,true),(8,false),(6,false),(13,true),(1,true),(2,true),(10,true)],[(0,false),(7,false),(3,false),(9,false),(5,true),(12,false),(11,false)])
                      (.node 2683254 ([(6,false),(8,false),(1,false),(13,false),(4,false),(3,false),(10,true)],[(0,false),(7,true),(2,true),(9,false),(5,false),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2695320 ([(5,true),(12,false),(1,false),(0,false),(8,false),(3,true),(10,true)],[(13,false),(6,true),(9,true),(4,true),(7,true),(2,false),(11,false)])
                        .empty
                        .empty)))))
              (.node 2699658 ([(3,true),(4,true),(8,false),(6,false),(13,true),(1,true),(10,true)],[(0,false),(7,false),(2,false),(9,false),(5,true),(12,false),(11,false)])
                (.node 2697828 ([(0,true),(1,true),(2,true),(12,true),(5,false),(4,false),(10,true)],[(13,false),(6,true),(7,true),(8,true),(9,true),(3,false),(11,false)])
                  (.node 2697258 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                    (.node 2696586 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2696538 ([(5,true),(6,true),(0,true),(1,true),(8,true),(3,false),(11,false)],[(13,false),(12,false),(2,false),(7,false),(4,false),(9,true),(10,true)])
                        (.node 2695788 ([(4,true),(5,true),(13,true),(0,false),(8,true),(2,false),(11,false)],[(1,true),(12,true),(6,true),(7,false),(3,false),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2697210 ([(5,true),(12,false),(3,true),(8,false),(0,true),(1,true),(10,true)],[(13,false),(6,true),(7,false),(4,false),(9,true),(2,true),(11,false)])
                        .empty
                        .empty))
                    (.node 2697732 ([(2,true),(12,true),(13,true),(0,false),(8,false),(4,false),(10,true)],[(1,true),(7,true),(5,true),(6,true),(9,true),(3,false),(11,false)])
                      (.node 2697714 ([(5,true),(12,false),(2,false),(1,false),(0,false),(9,true),(10,true)],[(13,false),(6,true),(8,false),(7,false),(4,false),(3,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2697798 ([(5,true),(6,true),(0,true),(1,true),(9,true),(3,false),(11,false)],[(13,false),(12,false),(2,false),(8,false),(7,false),(4,false),(10,true)])
                        .empty
                        .empty)))
                  (.node 2698860 ([(3,true),(4,true),(8,true),(1,false),(13,false),(6,true),(10,true)],[(0,false),(9,false),(2,true),(7,true),(5,true),(12,false),(11,false)])
                    (.node 2698140 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2698068 ([(2,true),(3,true),(8,true),(0,true),(13,false),(5,false),(10,true)],[(1,true),(7,true),(4,true),(9,false),(6,false),(12,false),(11,false)])
                        (.node 2698056 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2698164 ([(0,true),(1,true),(8,false),(3,false),(12,true),(5,false),(10,true)],[(13,false),(6,true),(7,true),(4,true),(9,false),(2,true),(11,false)])
                        .empty
                        .empty))
                    (.node 2699436 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2698908 ([(2,true),(3,true),(4,true),(5,true),(13,true),(0,false),(10,true)],[(1,true),(7,true),(8,true),(9,true),(6,false),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2699448 ([(3,true),(4,true),(5,true),(13,true),(0,false),(9,true),(10,true)],[(1,true),(2,true),(7,true),(8,true),(6,false),(12,false),(11,false)])
                        .empty
                        .empty))))
                (.node 2714808 ([(5,true),(8,false),(0,false),(13,true),(2,true),(3,true),(10,true)],[(1,false),(7,false),(4,false),(9,false),(6,true),(12,false),(11,false)])
                  (.node 2700012 ([(0,true),(1,true),(2,true),(9,false),(5,true),(12,false),(11,false)],[(13,false),(6,true),(7,true),(8,true),(4,false),(3,false),(10,true)])
                    (.node 2699790 ([(2,true),(9,false),(0,true),(13,false),(5,false),(4,false),(11,false)],[(1,true),(7,true),(8,true),(6,false),(12,false),(3,false),(10,true)])
                      (.node 2699772 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 2699676 ([(0,true),(1,true),(2,true),(8,true),(5,true),(12,false),(11,false)],[(13,false),(6,true),(7,true),(3,true),(4,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2700000 ([(2,true),(9,false),(8,false),(0,true),(13,false),(12,false),(11,false)],[(1,true),(7,true),(6,false),(5,false),(4,false),(3,false),(10,true)])
                        .empty
                        .empty))
                    (.node 2700588 ([(2,true),(8,false),(0,true),(13,false),(5,false),(4,false),(11,false)],[(1,true),(7,true),(6,false),(12,false),(3,false),(9,true),(10,true)])
                      (.node 2700540 ([(3,true),(12,true),(13,true),(0,false),(8,true),(9,true),(10,true)],[(1,true),(2,true),(7,true),(6,false),(5,false),(4,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2702598 ([(3,true),(9,false),(8,false),(0,true),(13,false),(5,false),(11,false)],[(1,true),(2,true),(7,true),(6,false),(12,false),(4,false),(10,true)])
                        .empty
                        .empty)))
                  (.node 2716194 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                    (.node 2715396 ([(5,true),(6,true),(13,true),(1,false),(8,true),(3,false),(11,false)],[(2,true),(12,true),(0,true),(7,false),(4,false),(9,true),(10,true)])
                      (.node 2714940 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 2714928 ([(6,true),(12,false),(2,false),(1,false),(8,false),(4,true),(10,true)],[(13,false),(0,true),(9,true),(5,true),(7,true),(3,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2716146 ([(6,true),(0,true),(1,true),(2,true),(8,true),(4,false),(11,false)],[(13,false),(12,false),(3,false),(7,false),(5,false),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2716866 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2716818 ([(6,true),(12,false),(4,true),(8,false),(1,true),(2,true),(10,true)],[(13,false),(0,true),(7,false),(5,false),(9,true),(3,true),(11,false)])
                        .empty
                        .empty)
                      (.node 2717322 ([(6,true),(12,false),(3,false),(2,false),(1,false),(9,true),(10,true)],[(13,false),(0,true),(8,false),(7,false),(5,false),(4,false),(11,false)])
                        .empty
                        .empty))))))
            (.node 2787720 ([(5,true),(12,true),(3,false),(2,false),(1,false),(0,false),(10,true)],[(13,false),(4,true),(7,true),(8,true),(9,true),(6,false),(11,false)])
              (.node 2722206 ([(4,true),(9,false),(8,false),(1,true),(13,false),(6,false),(11,false)],[(2,true),(3,true),(7,true),(0,false),(12,false),(5,false),(10,true)])
                (.node 2719056 ([(4,true),(5,true),(6,true),(13,true),(1,false),(9,true),(10,true)],[(2,true),(3,true),(7,true),(8,true),(0,false),(12,false),(11,false)])
                  (.node 2717748 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                    (.node 2717664 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2717436 ([(1,true),(2,true),(3,true),(12,true),(6,false),(5,false),(10,true)],[(13,false),(0,true),(7,true),(8,true),(9,true),(4,false),(11,false)])
                        (.node 2717406 ([(6,true),(0,true),(1,true),(2,true),(9,true),(4,false),(11,false)],[(13,false),(12,false),(3,false),(8,false),(7,false),(5,false),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2717676 ([(3,true),(4,true),(8,true),(1,true),(13,false),(6,false),(10,true)],[(2,true),(7,true),(5,true),(9,false),(0,false),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2718516 ([(3,true),(4,true),(5,true),(6,true),(13,true),(1,false),(10,true)],[(2,true),(7,true),(8,true),(9,true),(0,false),(12,false),(11,false)])
                      (.node 2718468 ([(4,true),(5,true),(8,true),(2,false),(13,false),(0,true),(10,true)],[(1,false),(9,false),(3,true),(7,true),(6,true),(12,false),(11,false)])
                        (.node 2717772 ([(1,true),(2,true),(8,false),(4,false),(12,true),(6,false),(10,true)],[(13,false),(0,true),(7,true),(5,true),(9,false),(3,true),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2719044 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 2719608 ([(3,true),(9,false),(8,false),(1,true),(13,false),(12,false),(11,false)],[(2,true),(7,true),(0,false),(6,false),(5,false),(4,false),(10,true)])
                    (.node 2719380 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2719284 ([(1,true),(2,true),(3,true),(8,true),(6,true),(12,false),(11,false)],[(13,false),(0,true),(7,true),(4,true),(5,true),(9,true),(10,true)])
                        (.node 2719266 ([(4,true),(5,true),(8,false),(0,false),(13,true),(2,true),(10,true)],[(1,false),(7,false),(3,false),(9,false),(6,true),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2719398 ([(3,true),(9,false),(1,true),(13,false),(6,false),(5,false),(11,false)],[(2,true),(7,true),(8,true),(0,false),(12,false),(4,false),(10,true)])
                        .empty
                        .empty))
                    (.node 2720148 ([(4,true),(12,true),(13,true),(1,false),(8,true),(9,true),(10,true)],[(2,true),(3,true),(7,true),(0,false),(6,false),(5,false),(11,false)])
                      (.node 2719620 ([(1,true),(2,true),(3,true),(9,false),(6,true),(12,false),(11,false)],[(13,false),(0,true),(7,true),(8,true),(5,false),(4,false),(10,true)])
                        .empty
                        .empty)
                      (.node 2720196 ([(3,true),(8,false),(1,true),(13,false),(6,false),(5,false),(11,false)],[(2,true),(7,true),(0,false),(12,false),(4,false),(9,true),(10,true)])
                        .empty
                        .empty))))
                (.node 2775288 ([(5,true),(9,false),(1,true),(2,true),(3,true),(12,false),(11,false)],[(13,false),(4,true),(7,true),(8,true),(0,false),(6,false),(10,true)])
                  (.node 2774946 ([(6,true),(0,true),(8,false),(2,false),(13,false),(4,true),(10,true)],[(1,false),(9,true),(5,true),(7,true),(3,true),(12,false),(11,false)])
                    (.node 2774442 ([(6,true),(0,true),(8,true),(4,false),(13,true),(2,true),(10,true)],[(1,false),(7,false),(5,false),(9,true),(3,true),(12,false),(11,false)])
                      (.node 2773818 ([(5,true),(6,true),(12,true),(3,false),(2,false),(1,false),(10,true)],[(13,false),(4,true),(7,true),(8,true),(9,true),(0,false),(11,false)])
                        (.node 2773770 ([(6,true),(12,true),(4,true),(8,false),(2,false),(1,false),(10,true)],[(13,false),(3,false),(7,false),(5,false),(9,true),(0,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2774490 ([(5,true),(6,true),(0,true),(1,true),(13,false),(3,false),(10,true)],[(2,true),(9,false),(8,false),(7,false),(4,false),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2775030 ([(6,true),(0,true),(1,true),(13,false),(3,false),(9,true),(10,true)],[(2,true),(8,false),(7,false),(5,false),(4,false),(12,false),(11,false)])
                      (.node 2774964 ([(3,true),(13,true),(1,false),(0,false),(6,false),(5,false),(10,true)],[(2,true),(7,true),(8,true),(9,true),(4,false),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2775060 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 2777298 ([(6,true),(8,false),(2,false),(1,false),(12,true),(4,true),(10,true)],[(13,false),(3,false),(7,false),(5,false),(9,false),(0,true),(11,false)])
                    (.node 2775396 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2775372 ([(5,true),(9,false),(3,true),(13,true),(1,false),(0,false),(11,false)],[(2,true),(8,false),(7,false),(4,false),(12,false),(6,false),(10,true)])
                        (.node 2775300 ([(3,true),(13,true),(1,false),(8,false),(5,true),(6,true),(11,false)],[(2,true),(7,true),(4,false),(12,false),(0,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2775828 ([(6,true),(9,false),(8,false),(3,true),(13,true),(1,false),(11,false)],[(2,true),(7,false),(5,false),(4,false),(12,false),(0,false),(10,true)])
                        .empty
                        .empty))
                    (.node 2777796 ([(0,true),(1,true),(13,false),(3,false),(8,false),(5,true),(10,true)],[(2,true),(9,true),(6,true),(7,true),(4,false),(12,false),(11,false)])
                      (.node 2777766 ([(5,true),(6,true),(8,true),(2,false),(13,false),(12,false),(11,false)],[(1,false),(0,false),(7,false),(4,false),(3,false),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2787288 ([(0,true),(8,false),(2,false),(13,false),(4,true),(5,true),(10,true)],[(1,false),(9,true),(6,true),(7,true),(3,true),(12,false),(11,false)])
                        .empty
                        .empty)))))
              (.node 2791410 ([(6,true),(0,true),(8,false),(2,false),(13,false),(4,false),(10,true)],[(1,false),(9,true),(3,false),(7,false),(5,false),(12,false),(11,false)])
                (.node 2788674 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 2788086 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    (.node 2787828 ([(1,true),(2,true),(3,true),(4,true),(9,true),(6,false),(11,false)],[(13,false),(12,false),(5,false),(8,false),(7,false),(0,false),(10,true)])
                      (.node 2787816 ([(3,true),(13,true),(1,false),(0,false),(9,false),(5,true),(11,false)],[(2,true),(7,true),(8,true),(4,false),(12,false),(6,true),(10,true)])
                        (.node 2787744 ([(1,true),(2,true),(8,false),(4,false),(12,false),(6,true),(10,true)],[(13,false),(3,false),(9,true),(0,true),(7,true),(5,true),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2788056 ([(5,true),(6,true),(8,true),(3,true),(13,true),(1,false),(10,true)],[(2,true),(9,true),(0,false),(7,false),(4,false),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2788170 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2788152 ([(3,true),(13,true),(1,false),(0,false),(8,true),(5,true),(11,false)],[(2,true),(7,true),(6,false),(12,true),(4,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2788626 ([(1,true),(2,true),(3,true),(4,true),(8,true),(6,false),(11,false)],[(13,false),(12,false),(5,false),(7,false),(0,false),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 2791074 ([(6,true),(0,true),(1,true),(13,false),(4,false),(3,false),(10,true)],[(2,true),(9,false),(8,false),(7,false),(5,false),(12,false),(11,false)])
                    (.node 2790498 ([(4,true),(5,true),(8,true),(2,false),(1,false),(0,false),(11,false)],[(13,false),(12,false),(6,false),(7,false),(3,false),(9,true),(10,true)])
                      (.node 2789346 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 2789298 ([(1,true),(2,true),(8,true),(6,false),(12,true),(4,true),(10,true)],[(13,false),(3,false),(7,false),(0,false),(9,true),(5,true),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2790546 ([(3,true),(8,false),(5,false),(13,true),(1,false),(0,false),(11,false)],[(2,true),(7,true),(6,true),(12,true),(4,false),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2791296 ([(4,true),(5,true),(9,true),(2,false),(1,false),(0,false),(11,false)],[(13,false),(12,false),(6,false),(8,false),(7,false),(3,false),(10,true)])
                      (.node 2791086 ([(4,true),(12,false),(6,false),(8,true),(1,true),(2,true),(10,true)],[(13,false),(5,true),(7,false),(3,false),(9,false),(0,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2791314 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))))
                (.node 2793714 ([(0,true),(1,true),(13,false),(4,false),(8,true),(9,true),(10,true)],[(2,true),(3,true),(7,false),(6,false),(5,false),(12,false),(11,false)])
                  (.node 2792226 ([(3,true),(4,true),(13,true),(1,false),(0,false),(6,false),(10,true)],[(2,true),(7,true),(8,true),(9,true),(5,false),(12,false),(11,false)])
                    (.node 2791650 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2791638 ([(3,true),(4,true),(13,true),(1,false),(8,true),(6,true),(11,false)],[(2,true),(7,true),(0,false),(12,true),(5,true),(9,true),(10,true)])
                        (.node 2791428 ([(3,true),(4,true),(13,true),(1,false),(8,false),(6,true),(11,false)],[(2,true),(7,true),(5,false),(12,false),(0,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2792178 ([(4,true),(13,true),(1,false),(8,true),(9,true),(6,true),(11,false)],[(2,true),(3,true),(7,true),(0,false),(12,true),(5,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2792604 ([(3,true),(8,false),(5,false),(13,true),(1,false),(0,false),(10,true)],[(2,true),(7,true),(6,true),(9,false),(4,true),(12,false),(11,false)])
                      (.node 2792556 ([(4,true),(12,false),(1,true),(2,true),(8,false),(6,true),(10,true)],[(13,false),(5,true),(7,false),(3,false),(9,true),(0,true),(11,false)])
                        .empty
                        .empty)
                      (.node 2793426 ([(6,true),(0,true),(1,true),(13,false),(4,false),(3,false),(10,true)],[(2,true),(9,false),(8,false),(7,false),(5,false),(12,false),(11,false)])
                        .empty
                        .empty)))
                  (.node 2797374 ([(6,true),(0,true),(1,true),(13,false),(4,false),(3,false),(11,false)],[(2,true),(12,true),(5,true),(7,true),(8,true),(9,true),(10,true)])
                    (.node 2794572 ([(4,true),(5,true),(6,true),(8,true),(2,false),(1,false),(11,false)],[(13,false),(12,false),(0,false),(7,false),(3,false),(9,true),(10,true)])
                      (.node 2794050 ([(0,true),(1,true),(13,false),(5,true),(8,false),(3,true),(10,true)],[(2,true),(7,false),(6,false),(9,true),(4,true),(12,false),(11,false)])
                        (.node 2793762 ([(6,true),(8,false),(2,false),(1,false),(12,true),(4,false),(10,true)],[(13,false),(5,true),(7,true),(3,true),(9,false),(0,true),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2794620 ([(3,true),(4,true),(13,true),(1,false),(0,false),(6,false),(10,true)],[(2,true),(7,true),(8,true),(9,true),(5,false),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2797830 ([(0,true),(1,true),(13,false),(5,true),(8,false),(3,false),(11,false)],[(2,true),(12,true),(4,false),(7,false),(6,false),(9,true),(10,true)])
                      (.node 2797404 ([(1,true),(2,true),(12,true),(4,false),(8,false),(6,true),(10,true)],[(13,false),(5,true),(7,false),(0,false),(9,false),(3,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2799300 ([(0,true),(8,false),(3,false),(2,false),(13,false),(5,true),(10,true)],[(1,false),(9,true),(6,true),(7,true),(4,true),(12,false),(11,false)])
                        .empty
                        .empty)))))))
          (.node 2855676 ([(5,true),(6,true),(8,true),(3,false),(13,false),(1,true),(10,true)],[(2,false),(9,false),(4,true),(7,true),(0,true),(12,false),(11,false)])
            (.node 2835036 ([(1,true),(2,true),(3,true),(12,true),(6,false),(5,false),(10,true)],[(13,false),(0,true),(7,true),(8,true),(9,true),(4,false),(11,false)])
              (.node 2816898 ([(0,true),(1,true),(2,true),(8,false),(5,true),(12,false),(11,false)],[(13,false),(6,true),(7,true),(4,false),(3,false),(9,true),(10,true)])
                (.node 2815380 ([(1,true),(2,true),(12,true),(5,false),(8,true),(9,true),(10,true)],[(13,false),(6,true),(0,true),(7,true),(4,false),(3,false),(11,false)])
                  (.node 2811036 ([(4,true),(5,true),(6,true),(8,true),(2,false),(1,false),(11,false)],[(13,false),(12,false),(0,false),(7,false),(3,false),(9,true),(10,true)])
                    (.node 2810568 ([(5,true),(6,true),(9,true),(3,false),(2,false),(1,false),(11,false)],[(13,false),(12,false),(0,false),(8,false),(7,false),(4,false),(10,true)])
                      (.node 2810448 ([(4,true),(8,false),(6,false),(12,false),(1,true),(2,true),(10,true)],[(13,false),(5,false),(9,true),(3,true),(7,true),(0,true),(11,false)])
                        (.node 2804574 ([(3,true),(8,false),(1,true),(13,false),(5,true),(6,true),(10,true)],[(2,true),(7,true),(0,false),(9,false),(4,true),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2810580 ([(3,true),(4,true),(8,true),(6,false),(13,true),(1,false),(11,false)],[(2,true),(7,true),(5,true),(12,false),(0,false),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2814516 ([(5,true),(6,true),(8,true),(9,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(4,true),(7,true),(0,true),(10,true)])
                      (.node 2814228 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 2814180 ([(5,true),(6,true),(9,false),(8,false),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(4,true),(7,true),(0,false),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2814564 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 2816556 ([(1,true),(2,true),(8,false),(4,false),(12,true),(6,true),(10,true)],[(13,false),(5,false),(7,false),(0,false),(9,false),(3,true),(11,false)])
                    (.node 2815764 ([(0,true),(1,true),(13,false),(5,false),(4,false),(3,false),(11,false)],[(2,true),(12,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2815716 ([(1,true),(2,true),(12,true),(6,true),(8,false),(4,true),(10,true)],[(13,false),(5,false),(9,false),(0,true),(7,true),(3,false),(11,false)])
                        (.node 2815428 ([(0,true),(1,true),(2,true),(12,true),(5,false),(4,false),(10,true)],[(13,false),(6,true),(7,true),(8,true),(9,true),(3,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2816532 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2816640 ([(1,true),(2,true),(3,true),(12,true),(5,false),(9,true),(10,true)],[(13,false),(6,true),(0,true),(7,true),(8,true),(4,false),(11,false)])
                      (.node 2816628 ([(3,true),(4,true),(5,true),(13,true),(1,false),(0,false),(10,true)],[(2,true),(7,true),(8,true),(9,true),(6,false),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2816868 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))))
                (.node 2830056 ([(5,true),(8,false),(0,false),(12,false),(2,true),(3,true),(10,true)],[(13,false),(6,false),(9,true),(4,true),(7,true),(1,true),(11,false)])
                  (.node 2818110 ([(1,true),(2,true),(8,true),(6,false),(5,false),(4,false),(11,false)],[(13,false),(12,false),(3,false),(7,false),(0,false),(9,true),(10,true)])
                    (.node 2817438 ([(1,true),(2,true),(9,false),(8,false),(5,true),(12,false),(11,false)],[(13,false),(6,true),(0,true),(7,true),(4,false),(3,false),(10,true)])
                      (.node 2816982 ([(0,true),(1,true),(2,true),(8,true),(5,true),(12,false),(11,false)],[(13,false),(6,true),(7,true),(3,true),(4,true),(9,true),(10,true)])
                        (.node 2816964 ([(3,true),(4,true),(8,false),(6,false),(13,true),(1,false),(10,true)],[(2,true),(7,true),(0,true),(9,false),(5,true),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2817486 ([(0,true),(1,true),(13,false),(5,false),(4,false),(3,false),(10,true)],[(2,true),(9,false),(8,false),(7,false),(6,false),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2820168 ([(0,false),(8,false),(2,false),(13,false),(5,false),(4,false),(10,true)],[(1,false),(7,true),(3,true),(9,false),(6,false),(12,false),(11,false)])
                      (.node 2818158 ([(0,true),(1,true),(2,true),(3,true),(12,true),(5,false),(10,true)],[(13,false),(6,true),(7,true),(8,true),(9,true),(4,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2820216 ([(0,true),(8,false),(2,false),(13,false),(5,false),(4,false),(10,true)],[(1,false),(9,true),(3,false),(7,false),(6,false),(12,false),(11,false)])
                        .empty
                        .empty)))
                  (.node 2833836 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                    (.node 2830644 ([(5,true),(6,true),(0,true),(8,true),(3,false),(2,false),(11,false)],[(13,false),(12,false),(1,false),(7,false),(4,false),(9,true),(10,true)])
                      (.node 2830188 ([(4,true),(5,true),(8,true),(0,false),(13,true),(2,false),(11,false)],[(3,true),(7,true),(6,true),(12,false),(1,false),(9,true),(10,true)])
                        (.node 2830176 ([(6,true),(0,true),(9,true),(4,false),(3,false),(2,false),(11,false)],[(13,false),(12,false),(1,false),(8,false),(7,false),(5,false),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2833788 ([(6,true),(0,true),(9,false),(8,false),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(5,true),(7,true),(1,false),(10,true)])
                        .empty
                        .empty))
                    (.node 2834172 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2834124 ([(6,true),(0,true),(8,true),(9,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(5,true),(7,true),(1,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2834988 ([(2,true),(3,true),(12,true),(6,false),(8,true),(9,true),(10,true)],[(13,false),(0,true),(1,true),(7,true),(5,false),(4,false),(11,false)])
                        .empty
                        .empty)))))
              (.node 2850252 ([(6,true),(0,true),(13,true),(2,false),(8,true),(4,false),(11,false)],[(3,true),(12,true),(1,true),(7,false),(5,false),(9,true),(10,true)])
                (.node 2836572 ([(4,true),(5,true),(8,false),(0,false),(13,true),(2,false),(10,true)],[(3,true),(7,true),(1,true),(9,false),(6,true),(12,false),(11,false)])
                  (.node 2836236 ([(4,true),(5,true),(6,true),(13,true),(2,false),(1,false),(10,true)],[(3,true),(7,true),(8,true),(9,true),(0,false),(12,false),(11,false)])
                    (.node 2836140 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2835372 ([(1,true),(2,true),(13,false),(6,false),(5,false),(4,false),(11,false)],[(3,true),(12,true),(0,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 2835324 ([(2,true),(3,true),(12,true),(0,true),(8,false),(5,true),(10,true)],[(13,false),(6,false),(9,false),(1,true),(7,true),(4,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2836164 ([(2,true),(3,true),(8,false),(5,false),(12,true),(0,true),(10,true)],[(13,false),(6,false),(7,false),(1,false),(9,false),(4,true),(11,false)])
                        .empty
                        .empty))
                    (.node 2836476 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2836248 ([(2,true),(3,true),(4,true),(12,true),(6,false),(9,true),(10,true)],[(13,false),(0,true),(1,true),(7,true),(8,true),(5,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2836506 ([(1,true),(2,true),(3,true),(8,false),(6,true),(12,false),(11,false)],[(13,false),(0,true),(7,true),(5,false),(4,false),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 2837766 ([(1,true),(2,true),(3,true),(4,true),(12,true),(6,false),(10,true)],[(13,false),(0,true),(7,true),(8,true),(9,true),(5,false),(11,false)])
                    (.node 2837094 ([(1,true),(2,true),(13,false),(6,false),(5,false),(4,false),(10,true)],[(3,true),(9,false),(8,false),(7,false),(0,false),(12,false),(11,false)])
                      (.node 2837046 ([(2,true),(3,true),(9,false),(8,false),(6,true),(12,false),(11,false)],[(13,false),(0,true),(1,true),(7,true),(5,false),(4,false),(10,true)])
                        (.node 2836590 ([(1,true),(2,true),(3,true),(8,true),(6,true),(12,false),(11,false)],[(13,false),(0,true),(7,true),(4,true),(5,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2837718 ([(2,true),(3,true),(8,true),(0,false),(6,false),(5,false),(11,false)],[(13,false),(12,false),(4,false),(7,false),(1,false),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2839824 ([(1,true),(8,false),(3,false),(13,false),(6,false),(5,false),(10,true)],[(2,false),(9,true),(4,false),(7,false),(0,false),(12,false),(11,false)])
                      (.node 2839776 ([(1,false),(8,false),(3,false),(13,false),(6,false),(5,false),(10,true)],[(2,false),(7,true),(4,true),(9,false),(0,false),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2842656 ([(5,true),(9,false),(8,false),(2,true),(13,false),(0,false),(11,false)],[(3,true),(4,true),(7,true),(1,false),(12,false),(6,false),(10,true)])
                        .empty
                        .empty))))
                (.node 2853396 ([(0,true),(1,true),(2,true),(3,true),(8,true),(5,false),(11,false)],[(13,false),(12,false),(4,false),(7,false),(6,false),(9,true),(10,true)])
                  (.node 2852532 ([(4,true),(5,true),(8,true),(2,true),(13,false),(0,false),(10,true)],[(3,true),(7,true),(6,true),(9,false),(1,false),(12,false),(11,false)])
                    (.node 2852178 ([(0,true),(12,false),(3,false),(2,false),(8,false),(5,true),(10,true)],[(13,false),(1,true),(9,true),(6,true),(7,true),(4,false),(11,false)])
                      (.node 2852148 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 2851722 ([(6,true),(8,false),(1,false),(13,true),(3,true),(4,true),(10,true)],[(2,false),(7,false),(5,false),(9,false),(0,true),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2852520 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2852628 ([(2,true),(3,true),(8,false),(5,false),(12,true),(0,false),(10,true)],[(13,false),(1,true),(7,true),(6,true),(9,false),(4,true),(11,false)])
                      (.node 2852604 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2853108 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 2854644 ([(2,true),(3,true),(4,true),(12,true),(0,false),(6,false),(10,true)],[(13,false),(1,true),(7,true),(8,true),(9,true),(5,false),(11,false)])
                    (.node 2854548 ([(4,true),(12,true),(13,true),(2,false),(8,false),(6,false),(10,true)],[(3,true),(7,true),(0,true),(1,true),(9,true),(5,false),(11,false)])
                      (.node 2854068 ([(0,true),(12,false),(5,true),(8,false),(2,true),(3,true),(10,true)],[(13,false),(1,true),(7,false),(6,false),(9,true),(4,true),(11,false)])
                        (.node 2853780 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2854572 ([(0,true),(12,false),(4,false),(3,false),(2,false),(9,true),(10,true)],[(13,false),(1,true),(8,false),(7,false),(6,false),(5,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2855004 ([(5,true),(12,true),(13,true),(2,false),(8,true),(9,true),(10,true)],[(3,true),(4,true),(7,true),(1,false),(0,false),(6,false),(11,false)])
                      (.node 2854656 ([(0,true),(1,true),(2,true),(3,true),(9,true),(5,false),(11,false)],[(13,false),(12,false),(4,false),(8,false),(7,false),(6,false),(10,true)])
                        .empty
                        .empty)
                      (.node 2855052 ([(4,true),(8,false),(2,true),(13,false),(0,false),(6,false),(11,false)],[(3,true),(7,true),(1,false),(12,false),(5,false),(9,true),(10,true)])
                        .empty
                        .empty))))))
            (.node 2914548 ([(0,true),(8,false),(3,false),(2,false),(12,true),(5,true),(10,true)],[(13,false),(4,false),(7,false),(6,false),(9,false),(1,true),(11,false)])
              (.node 2909124 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 2908170 ([(6,true),(12,true),(4,false),(3,false),(2,false),(1,false),(10,true)],[(13,false),(5,true),(7,true),(8,true),(9,true),(0,false),(11,false)])
                  (.node 2856294 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                    (.node 2856198 ([(2,true),(3,true),(4,true),(8,true),(0,true),(12,false),(11,false)],[(13,false),(1,true),(7,true),(5,true),(6,true),(9,true),(10,true)])
                      (.node 2856180 ([(5,true),(6,true),(8,false),(1,false),(13,true),(3,true),(10,true)],[(2,false),(7,false),(4,false),(9,false),(0,true),(12,false),(11,false)])
                        (.node 2855724 ([(4,true),(5,true),(6,true),(0,true),(13,true),(2,false),(10,true)],[(3,true),(7,true),(8,true),(9,true),(1,false),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2856264 ([(5,true),(6,true),(0,true),(13,true),(2,false),(9,true),(10,true)],[(3,true),(4,true),(7,true),(8,true),(1,false),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2856606 ([(4,true),(9,false),(2,true),(13,false),(0,false),(6,false),(11,false)],[(3,true),(7,true),(8,true),(1,false),(12,false),(5,false),(10,true)])
                      (.node 2856534 ([(2,true),(3,true),(4,true),(9,false),(0,true),(12,false),(11,false)],[(13,false),(1,true),(7,true),(8,true),(6,false),(5,false),(10,true)])
                        (.node 2856522 ([(4,true),(9,false),(8,false),(2,true),(13,false),(12,false),(11,false)],[(3,true),(7,true),(1,false),(0,false),(6,false),(5,false),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2856630 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 2908536 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                    (.node 2908278 ([(2,true),(3,true),(4,true),(5,true),(9,true),(0,false),(11,false)],[(13,false),(12,false),(6,false),(8,false),(7,false),(1,false),(10,true)])
                      (.node 2908266 ([(4,true),(13,true),(2,false),(1,false),(9,false),(6,true),(11,false)],[(3,true),(7,true),(8,true),(5,false),(12,false),(0,true),(10,true)])
                        (.node 2908194 ([(2,true),(3,true),(8,false),(5,false),(12,false),(0,true),(10,true)],[(13,false),(4,false),(9,true),(1,true),(7,true),(6,true),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2908506 ([(6,true),(0,true),(8,true),(4,true),(13,true),(2,false),(10,true)],[(3,true),(9,true),(1,false),(7,false),(5,false),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2908620 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2908602 ([(4,true),(13,true),(2,false),(1,false),(8,true),(6,true),(11,false)],[(3,true),(7,true),(0,false),(12,true),(5,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2909076 ([(2,true),(3,true),(4,true),(5,true),(8,true),(0,false),(11,false)],[(13,false),(12,false),(6,false),(7,false),(1,false),(9,true),(10,true)])
                        .empty
                        .empty))))
                (.node 2911404 ([(6,true),(0,true),(1,true),(2,true),(13,false),(4,false),(10,true)],[(3,true),(9,false),(8,false),(7,false),(5,false),(12,false),(11,false)])
                  (.node 2910228 ([(6,true),(9,false),(4,true),(13,true),(2,false),(1,false),(11,false)],[(3,true),(8,false),(7,false),(5,false),(12,false),(0,false),(10,true)])
                    (.node 2910144 ([(6,true),(9,false),(2,true),(3,true),(4,true),(12,false),(11,false)],[(13,false),(5,true),(7,true),(8,true),(1,false),(0,false),(10,true)])
                      (.node 2909796 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 2909748 ([(2,true),(3,true),(8,true),(0,false),(12,true),(5,true),(10,true)],[(13,false),(4,false),(7,false),(1,false),(9,true),(6,true),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2910156 ([(4,true),(13,true),(2,false),(8,false),(6,true),(0,true),(11,false)],[(3,true),(7,true),(5,false),(12,false),(1,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2910732 ([(6,true),(0,true),(12,true),(4,false),(3,false),(2,false),(10,true)],[(13,false),(5,true),(7,true),(8,true),(9,true),(1,false),(11,false)])
                      (.node 2910252 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2911020 ([(0,true),(12,true),(5,true),(8,false),(3,false),(2,false),(10,true)],[(13,false),(4,false),(7,false),(6,false),(9,true),(1,false),(11,false)])
                        .empty
                        .empty)))
                  (.node 2912280 ([(0,true),(1,true),(2,true),(13,false),(4,false),(9,true),(10,true)],[(3,true),(8,false),(7,false),(6,false),(5,false),(12,false),(11,false)])
                    (.node 2912196 ([(0,true),(1,true),(8,false),(3,false),(13,false),(5,true),(10,true)],[(2,false),(9,true),(6,true),(7,true),(4,true),(12,false),(11,false)])
                      (.node 2912172 ([(4,true),(13,true),(2,false),(1,false),(0,false),(6,false),(10,true)],[(3,true),(7,true),(8,true),(9,true),(5,false),(12,false),(11,false)])
                        (.node 2911692 ([(0,true),(1,true),(8,true),(5,false),(13,true),(3,true),(10,true)],[(2,false),(7,false),(6,false),(9,true),(4,true),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2912268 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2912652 ([(1,true),(2,true),(13,false),(4,false),(8,false),(6,true),(10,true)],[(3,true),(9,true),(0,true),(7,true),(5,false),(12,false),(11,false)])
                      (.node 2912622 ([(6,true),(0,true),(8,true),(3,false),(13,false),(12,false),(11,false)],[(2,false),(1,false),(7,false),(5,false),(4,false),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2913078 ([(0,true),(9,false),(8,false),(4,true),(13,true),(2,false),(11,false)],[(3,true),(7,false),(6,false),(5,false),(12,false),(1,false),(10,true)])
                        .empty
                        .empty)))))
              (.node 2929764 ([(5,true),(12,false),(2,true),(3,true),(8,false),(0,true),(10,true)],[(13,false),(6,true),(7,false),(4,false),(9,true),(1,true),(11,false)])
                (.node 2928228 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 2927082 ([(4,true),(5,true),(13,true),(2,false),(1,false),(0,false),(10,true)],[(3,true),(7,true),(8,true),(9,true),(6,false),(12,false),(11,false)])
                    (.node 2925024 ([(4,true),(8,false),(2,true),(13,false),(6,true),(0,true),(10,true)],[(3,true),(7,true),(1,false),(9,false),(5,true),(12,false),(11,false)])
                      (.node 2924976 ([(4,false),(8,false),(2,true),(13,false),(6,true),(0,true),(10,true)],[(3,true),(9,true),(1,true),(7,false),(5,true),(12,false),(11,false)])
                        (.node 2922144 ([(1,true),(8,false),(3,false),(13,false),(5,true),(6,true),(10,true)],[(2,false),(9,true),(0,true),(7,true),(4,true),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2927034 ([(5,true),(13,true),(2,false),(8,true),(9,true),(0,true),(11,false)],[(3,true),(4,true),(7,true),(1,false),(12,true),(6,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2927754 ([(4,true),(8,false),(6,false),(13,true),(2,false),(1,false),(11,false)],[(3,true),(7,true),(0,true),(12,true),(5,false),(9,true),(10,true)])
                      (.node 2927706 ([(5,true),(6,true),(8,true),(3,false),(2,false),(1,false),(11,false)],[(13,false),(12,false),(0,false),(7,false),(4,false),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2928210 ([(5,true),(6,true),(9,true),(3,false),(2,false),(1,false),(11,false)],[(13,false),(12,false),(0,false),(8,false),(7,false),(4,false),(10,true)])
                        .empty
                        .empty)))
                  (.node 2928636 ([(4,true),(5,true),(13,true),(2,false),(8,false),(0,true),(11,false)],[(3,true),(7,true),(6,false),(12,false),(1,true),(9,true),(10,true)])
                    (.node 2928552 ([(4,true),(5,true),(13,true),(2,false),(8,true),(0,true),(11,false)],[(3,true),(7,true),(1,false),(12,true),(6,true),(9,true),(10,true)])
                      (.node 2928324 ([(0,true),(1,true),(2,true),(13,false),(5,false),(4,false),(10,true)],[(3,true),(9,false),(8,false),(7,false),(6,false),(12,false),(11,false)])
                        (.node 2928294 ([(5,true),(12,false),(0,false),(8,true),(2,true),(3,true),(10,true)],[(13,false),(6,true),(7,false),(4,false),(9,false),(1,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2928564 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2929428 ([(5,true),(6,true),(0,true),(8,true),(3,false),(2,false),(11,false)],[(13,false),(12,false),(1,false),(7,false),(4,false),(9,true),(10,true)])
                      (.node 2928660 ([(0,true),(1,true),(8,false),(3,false),(13,false),(5,false),(10,true)],[(2,false),(9,true),(4,false),(7,false),(6,false),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2929476 ([(4,true),(5,true),(13,true),(2,false),(1,false),(0,false),(10,true)],[(3,true),(7,true),(8,true),(9,true),(6,false),(12,false),(11,false)])
                        .empty
                        .empty))))
                (.node 2934744 ([(1,true),(2,true),(13,false),(6,true),(8,false),(4,false),(11,false)],[(3,true),(12,true),(5,false),(7,false),(0,false),(9,true),(10,true)])
                  (.node 2931012 ([(0,true),(8,false),(3,false),(2,false),(12,true),(5,false),(10,true)],[(13,false),(6,true),(7,true),(4,true),(9,false),(1,true),(11,false)])
                    (.node 2930676 ([(0,true),(1,true),(2,true),(13,false),(5,false),(4,false),(10,true)],[(3,true),(9,false),(8,false),(7,false),(6,false),(12,false),(11,false)])
                      (.node 2930628 ([(1,true),(2,true),(13,false),(5,false),(8,true),(9,true),(10,true)],[(3,true),(4,true),(7,false),(0,false),(6,false),(12,false),(11,false)])
                        (.node 2929812 ([(4,true),(8,false),(6,false),(13,true),(2,false),(1,false),(10,true)],[(3,true),(7,true),(0,true),(9,false),(5,true),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2930964 ([(1,true),(2,true),(13,false),(6,true),(8,false),(4,true),(10,true)],[(3,true),(7,false),(0,false),(9,true),(5,true),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2934612 ([(2,true),(3,true),(12,true),(5,false),(8,false),(0,true),(10,true)],[(13,false),(6,true),(7,false),(1,false),(9,false),(4,false),(11,false)])
                      (.node 2934156 ([(1,true),(8,false),(4,false),(3,false),(13,false),(6,true),(10,true)],[(2,false),(9,true),(0,true),(7,true),(5,true),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2934624 ([(0,true),(1,true),(2,true),(13,false),(5,false),(4,false),(11,false)],[(3,true),(12,true),(6,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 2947314 ([(6,true),(0,true),(8,true),(4,false),(3,false),(2,false),(11,false)],[(13,false),(12,false),(1,false),(7,false),(5,false),(9,true),(10,true)])
                    (.node 2946642 ([(6,true),(13,true),(3,false),(8,true),(9,true),(1,true),(11,false)],[(4,true),(5,true),(7,true),(2,false),(12,true),(0,true),(10,true)])
                      (.node 2944632 ([(5,true),(8,false),(3,true),(13,false),(0,true),(1,true),(10,true)],[(4,true),(7,true),(2,false),(9,false),(6,true),(12,false),(11,false)])
                        (.node 2944584 ([(5,false),(8,false),(3,true),(13,false),(0,true),(1,true),(10,true)],[(4,true),(9,true),(2,true),(7,false),(6,true),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2946690 ([(5,true),(6,true),(13,true),(3,false),(2,false),(1,false),(10,true)],[(4,true),(7,true),(8,true),(9,true),(0,false),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2947818 ([(6,true),(0,true),(9,true),(4,false),(3,false),(2,false),(11,false)],[(13,false),(12,false),(1,false),(8,false),(7,false),(5,false),(10,true)])
                      (.node 2947362 ([(5,true),(8,false),(0,false),(13,true),(3,false),(2,false),(11,false)],[(4,true),(7,true),(1,true),(12,true),(6,false),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2947836 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))))))))
        (.node 3085476 ([(2,true),(8,false),(5,false),(4,false),(12,true),(0,false),(10,true)],[(13,false),(1,true),(7,true),(6,true),(9,false),(3,true),(11,false)])
          (.node 3042594 ([(2,true),(8,false),(4,false),(13,false),(6,true),(0,true),(10,true)],[(3,false),(9,true),(1,true),(7,true),(5,true),(12,false),(11,false)])
            (.node 2973390 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
              (.node 2960274 ([(2,true),(8,false),(4,false),(13,false),(0,false),(6,false),(10,true)],[(3,false),(9,true),(5,false),(7,false),(1,false),(12,false),(11,false)])
                (.node 2950236 ([(2,true),(3,true),(13,false),(6,false),(8,true),(9,true),(10,true)],[(4,true),(5,true),(7,false),(1,false),(0,false),(12,false),(11,false)])
                  (.node 2948268 ([(1,true),(2,true),(8,false),(4,false),(13,false),(6,false),(10,true)],[(3,false),(9,true),(5,false),(7,false),(0,false),(12,false),(11,false)])
                    (.node 2948172 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2948160 ([(5,true),(6,true),(13,true),(3,false),(8,true),(1,true),(11,false)],[(4,true),(7,true),(2,false),(12,true),(0,true),(9,true),(10,true)])
                        (.node 2947932 ([(1,true),(2,true),(3,true),(13,false),(6,false),(5,false),(10,true)],[(4,true),(9,false),(8,false),(7,false),(0,false),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2948244 ([(5,true),(6,true),(13,true),(3,false),(8,false),(1,true),(11,false)],[(4,true),(7,true),(0,false),(12,false),(2,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2949372 ([(6,true),(12,false),(3,true),(4,true),(8,false),(1,true),(10,true)],[(13,false),(0,true),(7,false),(5,false),(9,true),(2,true),(11,false)])
                      (.node 2949084 ([(5,true),(6,true),(13,true),(3,false),(2,false),(1,false),(10,true)],[(4,true),(7,true),(8,true),(9,true),(0,false),(12,false),(11,false)])
                        (.node 2949036 ([(6,true),(0,true),(1,true),(8,true),(4,false),(3,false),(11,false)],[(13,false),(12,false),(2,false),(7,false),(5,false),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2949420 ([(5,true),(8,false),(0,false),(13,true),(3,false),(2,false),(10,true)],[(4,true),(7,true),(1,true),(9,false),(6,true),(12,false),(11,false)])
                        .empty
                        .empty)))
                  (.node 2954220 ([(3,true),(4,true),(12,true),(6,false),(8,false),(1,true),(10,true)],[(13,false),(0,true),(7,false),(2,false),(9,false),(5,false),(11,false)])
                    (.node 2950620 ([(1,true),(8,false),(4,false),(3,false),(12,true),(6,false),(10,true)],[(13,false),(0,true),(7,true),(5,true),(9,false),(2,true),(11,false)])
                      (.node 2950572 ([(2,true),(3,true),(13,false),(0,true),(8,false),(5,true),(10,true)],[(4,true),(7,false),(1,false),(9,true),(6,true),(12,false),(11,false)])
                        (.node 2950284 ([(1,true),(2,true),(3,true),(13,false),(6,false),(5,false),(10,true)],[(4,true),(9,false),(8,false),(7,false),(0,false),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2953764 ([(2,true),(8,false),(5,false),(4,false),(13,false),(0,true),(10,true)],[(3,false),(9,true),(1,true),(7,true),(6,true),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2954352 ([(2,true),(3,true),(13,false),(0,true),(8,false),(5,false),(11,false)],[(4,true),(12,true),(6,false),(7,false),(1,false),(9,true),(10,true)])
                      (.node 2954232 ([(1,true),(2,true),(3,true),(13,false),(6,false),(5,false),(11,false)],[(4,true),(12,true),(0,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2960226 ([(2,false),(8,false),(4,false),(13,false),(0,false),(6,false),(10,true)],[(3,false),(7,true),(5,true),(9,false),(1,false),(12,false),(11,false)])
                        .empty
                        .empty))))
                (.node 2971086 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 2970180 ([(3,true),(4,true),(12,true),(1,true),(8,false),(6,true),(10,true)],[(13,false),(0,false),(9,false),(2,true),(7,true),(5,false),(11,false)])
                    (.node 2967396 ([(5,true),(6,true),(8,true),(1,false),(13,true),(3,false),(11,false)],[(4,true),(7,true),(0,true),(12,false),(2,false),(9,true),(10,true)])
                      (.node 2966970 ([(6,true),(8,false),(1,false),(12,false),(3,true),(4,true),(10,true)],[(13,false),(0,false),(9,true),(5,true),(7,true),(2,true),(11,false)])
                        (.node 2965500 ([(6,true),(0,true),(1,true),(8,true),(4,false),(3,false),(11,false)],[(13,false),(12,false),(2,false),(7,false),(5,false),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2967426 ([(0,true),(1,true),(9,true),(5,false),(4,false),(3,false),(11,false)],[(13,false),(12,false),(2,false),(8,false),(7,false),(6,false),(10,true)])
                        .empty
                        .empty))
                    (.node 2970750 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 2970228 ([(2,true),(3,true),(13,false),(0,false),(6,false),(5,false),(11,false)],[(4,true),(12,true),(1,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2971038 ([(0,true),(1,true),(9,false),(8,false),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(6,true),(7,true),(2,false),(10,true)])
                        .empty
                        .empty)))
                  (.node 2972622 ([(2,true),(3,true),(4,true),(5,true),(12,true),(0,false),(10,true)],[(13,false),(1,true),(7,true),(8,true),(9,true),(6,false),(11,false)])
                    (.node 2972244 ([(2,true),(3,true),(4,true),(12,true),(0,false),(6,false),(10,true)],[(13,false),(1,true),(7,true),(8,true),(9,true),(5,false),(11,false)])
                      (.node 2972196 ([(3,true),(4,true),(12,true),(0,false),(8,true),(9,true),(10,true)],[(13,false),(1,true),(2,true),(7,true),(6,false),(5,false),(11,false)])
                        (.node 2971374 ([(0,true),(1,true),(8,true),(9,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(6,true),(7,true),(2,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2972574 ([(3,true),(4,true),(8,true),(1,false),(0,false),(6,false),(11,false)],[(13,false),(12,false),(5,false),(7,false),(2,false),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2973162 ([(3,true),(4,true),(5,true),(12,true),(0,false),(9,true),(10,true)],[(13,false),(1,true),(2,true),(7,true),(8,true),(6,false),(11,false)])
                      (.node 2973150 ([(5,true),(6,true),(0,true),(13,true),(3,false),(2,false),(10,true)],[(4,true),(7,true),(8,true),(9,true),(1,false),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2973372 ([(3,true),(4,true),(8,false),(6,false),(12,true),(1,true),(10,true)],[(13,false),(0,false),(7,false),(2,false),(9,false),(5,true),(11,false)])
                        .empty
                        .empty)))))
              (.node 2977080 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 2976126 ([(6,true),(0,true),(8,true),(4,false),(13,false),(2,true),(10,true)],[(3,false),(9,false),(5,true),(7,true),(1,true),(12,false),(11,false)])
                  (.node 2974254 ([(3,true),(4,true),(9,false),(8,false),(0,true),(12,false),(11,false)],[(13,false),(1,true),(2,true),(7,true),(6,false),(5,false),(10,true)])
                    (.node 2973714 ([(2,true),(3,true),(4,true),(8,false),(0,true),(12,false),(11,false)],[(13,false),(1,true),(7,true),(6,false),(5,false),(9,true),(10,true)])
                      (.node 2973504 ([(2,true),(3,true),(4,true),(8,true),(0,true),(12,false),(11,false)],[(13,false),(1,true),(7,true),(5,true),(6,true),(9,true),(10,true)])
                        (.node 2973486 ([(5,true),(6,true),(8,false),(1,false),(13,true),(3,false),(10,true)],[(4,true),(7,true),(2,true),(9,false),(0,true),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2973726 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2975454 ([(6,true),(12,true),(13,true),(3,false),(8,true),(9,true),(10,true)],[(4,true),(5,true),(7,true),(2,false),(1,false),(0,false),(11,false)])
                      (.node 2974302 ([(2,true),(3,true),(13,false),(0,false),(6,false),(5,false),(10,true)],[(4,true),(9,false),(8,false),(7,false),(1,false),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2975502 ([(5,true),(8,false),(3,true),(13,false),(1,false),(0,false),(11,false)],[(4,true),(7,true),(2,false),(12,false),(6,false),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 2976744 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                    (.node 2976648 ([(3,true),(4,true),(5,true),(8,true),(1,true),(12,false),(11,false)],[(13,false),(2,true),(7,true),(6,true),(0,true),(9,true),(10,true)])
                      (.node 2976630 ([(6,true),(0,true),(8,false),(2,false),(13,true),(4,true),(10,true)],[(3,false),(7,false),(5,false),(9,false),(1,true),(12,false),(11,false)])
                        (.node 2976174 ([(5,true),(6,true),(0,true),(1,true),(13,true),(3,false),(10,true)],[(4,true),(7,true),(8,true),(9,true),(2,false),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2976714 ([(6,true),(0,true),(1,true),(13,true),(3,false),(9,true),(10,true)],[(4,true),(5,true),(7,true),(8,true),(2,false),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 2976984 ([(3,true),(4,true),(5,true),(9,false),(1,true),(12,false),(11,false)],[(13,false),(2,true),(7,true),(8,true),(0,false),(6,false),(10,true)])
                      (.node 2976972 ([(5,true),(9,false),(8,false),(3,true),(13,false),(12,false),(11,false)],[(4,true),(7,true),(2,false),(1,false),(0,false),(6,false),(10,true)])
                        .empty
                        .empty)
                      (.node 2977056 ([(5,true),(9,false),(3,true),(13,false),(1,false),(0,false),(11,false)],[(4,true),(7,true),(8,true),(2,false),(12,false),(6,false),(10,true)])
                        .empty
                        .empty))))
                (.node 2989512 ([(1,true),(2,true),(3,true),(4,true),(9,true),(6,false),(11,false)],[(13,false),(12,false),(5,false),(8,false),(7,false),(0,false),(10,true)])
                  (.node 2988972 ([(0,true),(8,false),(2,false),(13,true),(4,true),(5,true),(10,true)],[(3,false),(7,false),(6,false),(9,false),(1,true),(12,false),(11,false)])
                    (.node 2987034 ([(1,true),(12,false),(4,false),(3,false),(8,false),(6,true),(10,true)],[(13,false),(2,true),(9,true),(0,true),(7,true),(5,false),(11,false)])
                      (.node 2987004 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(11,false)],[(13,false),(12,false),(5,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 2977512 ([(6,true),(9,false),(8,false),(3,true),(13,false),(1,false),(11,false)],[(4,true),(5,true),(7,true),(2,false),(12,false),(0,false),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2987502 ([(0,true),(1,true),(13,true),(3,false),(8,true),(5,false),(11,false)],[(4,true),(12,true),(2,true),(7,false),(6,false),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2989428 ([(1,true),(12,false),(5,false),(4,false),(3,false),(9,true),(10,true)],[(13,false),(2,true),(8,false),(7,false),(0,false),(6,false),(11,false)])
                      (.node 2989404 ([(5,true),(12,true),(13,true),(3,false),(8,false),(0,false),(10,true)],[(4,true),(7,true),(1,true),(2,true),(9,true),(6,false),(11,false)])
                        .empty
                        .empty)
                      (.node 2989500 ([(3,true),(4,true),(5,true),(12,true),(1,false),(0,false),(10,true)],[(13,false),(2,true),(7,true),(8,true),(9,true),(6,false),(11,false)])
                        .empty
                        .empty)))
                  (.node 2990310 ([(1,true),(2,true),(3,true),(4,true),(8,true),(6,false),(11,false)],[(13,false),(12,false),(5,false),(7,false),(0,false),(9,true),(10,true)])
                    (.node 2989836 ([(3,true),(4,true),(8,false),(6,false),(12,true),(1,false),(10,true)],[(13,false),(2,true),(7,true),(0,true),(9,false),(5,true),(11,false)])
                      (.node 2989770 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 2989740 ([(5,true),(6,true),(8,true),(3,true),(13,false),(1,false),(10,true)],[(4,true),(7,true),(0,true),(9,false),(2,false),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 2989854 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 2990982 ([(1,true),(12,false),(6,true),(8,false),(3,true),(4,true),(10,true)],[(13,false),(2,true),(7,false),(0,false),(9,true),(5,true),(11,false)])
                      (.node 2990358 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 2991030 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))))))
            (.node 3065142 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
              (.node 3047460 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
                (.node 3045756 ([(0,true),(1,true),(8,true),(5,true),(13,true),(3,false),(10,true)],[(4,true),(9,true),(2,false),(7,false),(6,false),(12,false),(11,false)])
                  (.node 3045402 ([(3,true),(4,true),(8,false),(6,false),(12,false),(1,true),(10,true)],[(13,false),(5,false),(9,true),(2,true),(7,true),(0,true),(11,false)])
                    (.node 3045180 ([(5,true),(13,true),(3,false),(2,false),(9,false),(0,true),(11,false)],[(4,true),(7,true),(8,true),(6,false),(12,false),(1,true),(10,true)])
                      (.node 3044652 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 3044604 ([(3,true),(4,true),(8,true),(1,false),(12,true),(6,true),(10,true)],[(13,false),(5,false),(7,false),(2,false),(9,true),(0,true),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3045192 ([(3,true),(4,true),(5,true),(6,true),(9,true),(1,false),(11,false)],[(13,false),(12,false),(0,false),(8,false),(7,false),(2,false),(10,true)])
                        .empty
                        .empty))
                    (.node 3045534 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 3045516 ([(5,true),(13,true),(3,false),(2,false),(8,true),(0,true),(11,false)],[(4,true),(7,true),(1,false),(12,true),(6,true),(9,true),(10,true)])
                        (.node 3045420 ([(0,true),(12,true),(5,false),(4,false),(3,false),(2,false),(10,true)],[(13,false),(6,true),(7,true),(8,true),(9,true),(1,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3045744 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 3047124 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
                    (.node 3047028 ([(5,true),(13,true),(3,false),(2,false),(1,false),(0,false),(10,true)],[(4,true),(7,true),(8,true),(9,true),(6,false),(12,false),(11,false)])
                      (.node 3046332 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 3046284 ([(3,true),(4,true),(5,true),(6,true),(8,true),(1,false),(11,false)],[(13,false),(12,false),(0,false),(7,false),(2,false),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3047052 ([(1,true),(2,true),(8,false),(4,false),(13,false),(6,true),(10,true)],[(3,false),(9,true),(0,true),(7,true),(5,true),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 3047364 ([(5,true),(13,true),(3,false),(8,false),(0,true),(1,true),(11,false)],[(4,true),(7,true),(6,false),(12,false),(2,true),(9,true),(10,true)])
                      (.node 3047136 ([(1,true),(2,true),(3,true),(13,false),(5,false),(9,true),(10,true)],[(4,true),(8,false),(7,false),(0,false),(6,false),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 3047394 ([(0,true),(9,false),(3,true),(4,true),(5,true),(12,false),(11,false)],[(13,false),(6,true),(7,true),(8,true),(2,false),(1,false),(10,true)])
                        .empty
                        .empty))))
                (.node 3049992 ([(1,true),(9,false),(8,false),(5,true),(13,true),(3,false),(11,false)],[(4,true),(7,false),(0,false),(6,false),(12,false),(2,false),(10,true)])
                  (.node 3048654 ([(0,true),(1,true),(2,true),(3,true),(13,false),(5,false),(10,true)],[(4,true),(9,false),(8,false),(7,false),(6,false),(12,false),(11,false)])
                    (.node 3047982 ([(0,true),(1,true),(12,true),(5,false),(4,false),(3,false),(10,true)],[(13,false),(6,true),(7,true),(8,true),(9,true),(2,false),(11,false)])
                      (.node 3047934 ([(1,true),(12,true),(6,true),(8,false),(4,false),(3,false),(10,true)],[(13,false),(5,false),(7,false),(0,false),(9,true),(2,false),(11,false)])
                        (.node 3047478 ([(0,true),(9,false),(5,true),(13,true),(3,false),(2,false),(11,false)],[(4,true),(8,false),(7,false),(6,false),(12,false),(1,false),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3048606 ([(1,true),(2,true),(8,true),(6,false),(13,true),(4,true),(10,true)],[(3,false),(7,false),(0,false),(9,true),(5,true),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 3049860 ([(2,true),(3,true),(13,false),(5,false),(8,false),(0,true),(10,true)],[(4,true),(9,true),(1,true),(7,true),(6,false),(12,false),(11,false)])
                      (.node 3049404 ([(1,true),(8,false),(4,false),(3,false),(12,true),(6,true),(10,true)],[(13,false),(5,false),(7,false),(0,false),(9,false),(2,true),(11,false)])
                        .empty
                        .empty)
                      (.node 3049872 ([(0,true),(1,true),(8,true),(4,false),(13,false),(12,false),(11,false)],[(3,false),(2,false),(7,false),(6,false),(5,false),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 3064800 ([(4,true),(5,true),(6,true),(0,true),(9,true),(2,false),(11,false)],[(13,false),(12,false),(1,false),(8,false),(7,false),(3,false),(10,true)])
                    (.node 3064260 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 3064212 ([(4,true),(5,true),(8,true),(2,false),(12,true),(0,true),(10,true)],[(13,false),(6,false),(7,false),(3,false),(9,true),(1,true),(11,false)])
                        (.node 3062202 ([(3,true),(8,false),(5,false),(13,false),(0,true),(1,true),(10,true)],[(4,false),(9,true),(2,true),(7,true),(6,true),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3064788 ([(6,true),(13,true),(4,false),(3,false),(9,false),(1,true),(11,false)],[(5,true),(7,true),(8,true),(0,false),(12,false),(2,true),(10,true)])
                        .empty
                        .empty))
                    (.node 3065028 ([(1,true),(12,true),(6,false),(5,false),(4,false),(3,false),(10,true)],[(13,false),(0,true),(7,true),(8,true),(9,true),(2,false),(11,false)])
                      (.node 3065010 ([(4,true),(5,true),(8,false),(0,false),(12,false),(2,true),(10,true)],[(13,false),(6,false),(9,true),(3,true),(7,true),(1,true),(11,false)])
                        .empty
                        .empty)
                      (.node 3065124 ([(6,true),(13,true),(4,false),(3,false),(8,true),(1,true),(11,false)],[(5,true),(7,true),(2,false),(12,true),(0,true),(9,true),(10,true)])
                        .empty
                        .empty)))))
              (.node 3069468 ([(3,true),(4,true),(13,false),(6,false),(8,false),(1,true),(10,true)],[(5,true),(9,true),(2,true),(7,true),(0,false),(12,false),(11,false)])
                (.node 3066972 ([(6,true),(13,true),(4,false),(8,false),(1,true),(2,true),(11,false)],[(5,true),(7,true),(0,false),(12,false),(3,true),(9,true),(10,true)])
                  (.node 3066636 ([(6,true),(13,true),(4,false),(3,false),(2,false),(1,false),(10,true)],[(5,true),(7,true),(8,true),(9,true),(0,false),(12,false),(11,false)])
                    (.node 3065892 ([(4,true),(5,true),(6,true),(0,true),(8,true),(2,false),(11,false)],[(13,false),(12,false),(1,false),(7,false),(3,false),(9,true),(10,true)])
                      (.node 3065364 ([(1,true),(2,true),(8,true),(6,true),(13,true),(4,false),(10,true)],[(5,true),(9,true),(3,false),(7,false),(0,false),(12,false),(11,false)])
                        (.node 3065352 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3065940 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 3066732 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 3066660 ([(2,true),(3,true),(8,false),(5,false),(13,false),(0,true),(10,true)],[(4,false),(9,true),(1,true),(7,true),(6,true),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 3066744 ([(2,true),(3,true),(4,true),(13,false),(6,false),(9,true),(10,true)],[(5,true),(8,false),(7,false),(1,false),(0,false),(12,false),(11,false)])
                        .empty
                        .empty)))
                  (.node 3067590 ([(1,true),(2,true),(12,true),(6,false),(5,false),(4,false),(10,true)],[(13,false),(0,true),(7,true),(8,true),(9,true),(3,false),(11,false)])
                    (.node 3067086 ([(1,true),(9,false),(6,true),(13,true),(4,false),(3,false),(11,false)],[(5,true),(8,false),(7,false),(0,false),(12,false),(2,false),(10,true)])
                      (.node 3067068 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 3067002 ([(1,true),(9,false),(4,true),(5,true),(6,true),(12,false),(11,false)],[(13,false),(0,true),(7,true),(8,true),(3,false),(2,false),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3067542 ([(2,true),(12,true),(0,true),(8,false),(5,false),(4,false),(10,true)],[(13,false),(6,false),(7,false),(1,false),(9,true),(3,false),(11,false)])
                        .empty
                        .empty))
                    (.node 3068262 ([(1,true),(2,true),(3,true),(4,true),(13,false),(6,false),(10,true)],[(5,true),(9,false),(8,false),(7,false),(0,false),(12,false),(11,false)])
                      (.node 3068214 ([(2,true),(3,true),(8,true),(0,false),(13,true),(5,true),(10,true)],[(4,false),(7,false),(1,false),(9,true),(6,true),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 3069012 ([(2,true),(8,false),(5,false),(4,false),(12,true),(0,true),(10,true)],[(13,false),(6,false),(7,false),(1,false),(9,false),(3,true),(11,false)])
                        .empty
                        .empty))))
                (.node 3083604 ([(6,true),(0,true),(13,true),(4,false),(3,false),(2,false),(10,true)],[(5,true),(7,true),(8,true),(9,true),(1,false),(12,false),(11,false)])
                  (.node 3083016 ([(6,true),(0,true),(13,true),(4,false),(8,true),(2,true),(11,false)],[(5,true),(7,true),(3,false),(12,true),(1,true),(9,true),(10,true)])
                    (.node 3081546 ([(6,true),(8,false),(4,true),(13,false),(1,true),(2,true),(10,true)],[(5,true),(7,true),(3,false),(9,false),(0,true),(12,false),(11,false)])
                      (.node 3069600 ([(2,true),(9,false),(8,false),(6,true),(13,true),(4,false),(11,false)],[(5,true),(7,false),(1,false),(0,false),(12,false),(3,false),(10,true)])
                        (.node 3069480 ([(1,true),(2,true),(8,true),(5,false),(13,false),(12,false),(11,false)],[(4,false),(3,false),(7,false),(0,false),(6,false),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3081834 ([(6,false),(8,false),(4,true),(13,false),(1,true),(2,true),(10,true)],[(5,true),(9,true),(3,true),(7,false),(0,true),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 3083100 ([(6,true),(0,true),(13,true),(4,false),(8,false),(2,true),(11,false)],[(5,true),(7,true),(1,false),(12,false),(3,true),(9,true),(10,true)])
                      (.node 3083028 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 3083124 ([(2,true),(3,true),(8,false),(5,false),(13,false),(0,false),(10,true)],[(4,false),(9,true),(6,false),(7,false),(1,false),(12,false),(11,false)])
                        .empty
                        .empty)))
                  (.node 3085068 ([(0,true),(1,true),(9,true),(5,false),(4,false),(3,false),(11,false)],[(13,false),(12,false),(2,false),(8,false),(7,false),(6,false),(10,true)])
                    (.node 3084564 ([(0,true),(1,true),(8,true),(5,false),(4,false),(3,false),(11,false)],[(13,false),(12,false),(2,false),(7,false),(6,false),(9,true),(10,true)])
                      (.node 3084276 ([(6,true),(8,false),(1,false),(13,true),(4,false),(3,false),(11,false)],[(5,true),(7,true),(2,true),(12,true),(0,false),(9,true),(10,true)])
                        (.node 3083892 ([(0,true),(13,true),(4,false),(8,true),(9,true),(2,true),(11,false)],[(5,true),(6,true),(7,true),(3,false),(12,true),(1,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3085044 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 3085152 ([(0,true),(12,false),(2,false),(8,true),(4,true),(5,true),(10,true)],[(13,false),(1,true),(7,false),(6,false),(9,false),(3,false),(11,false)])
                      (.node 3085140 ([(2,true),(3,true),(4,true),(13,false),(0,false),(6,false),(10,true)],[(5,true),(9,false),(8,false),(7,false),(1,false),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 3085428 ([(3,true),(4,true),(13,false),(1,true),(8,false),(6,true),(10,true)],[(5,true),(7,false),(2,false),(9,true),(0,true),(12,false),(11,false)])
                        .empty
                        .empty)))))))
          (.node 3202008 ([(5,true),(6,true),(0,true),(1,true),(9,true),(3,false),(11,false)],[(13,false),(12,false),(2,false),(8,false),(7,false),(4,false),(10,true)])
            (.node 3109854 ([(6,true),(12,true),(13,true),(4,false),(8,false),(1,false),(10,true)],[(5,true),(7,true),(2,true),(3,true),(9,true),(0,false),(11,false)])
              (.node 3094164 ([(3,true),(4,true),(5,true),(8,false),(1,true),(12,false),(11,false)],[(13,false),(2,true),(7,true),(0,false),(6,false),(9,true),(10,true)])
                (.node 3091560 ([(3,true),(4,true),(13,false),(1,true),(8,false),(6,false),(11,false)],[(5,true),(12,true),(0,false),(7,false),(2,false),(9,true),(10,true)])
                  (.node 3087444 ([(3,true),(4,true),(13,false),(0,false),(8,true),(9,true),(10,true)],[(5,true),(6,true),(7,false),(2,false),(1,false),(12,false),(11,false)])
                    (.node 3086334 ([(6,true),(8,false),(1,false),(13,true),(4,false),(3,false),(10,true)],[(5,true),(7,true),(2,true),(9,false),(0,true),(12,false),(11,false)])
                      (.node 3086286 ([(0,true),(1,true),(2,true),(8,true),(5,false),(4,false),(11,false)],[(13,false),(12,false),(3,false),(7,false),(6,false),(9,true),(10,true)])
                        (.node 3085998 ([(6,true),(0,true),(13,true),(4,false),(3,false),(2,false),(10,true)],[(5,true),(7,true),(8,true),(9,true),(1,false),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3086622 ([(0,true),(12,false),(4,true),(5,true),(8,false),(2,true),(10,true)],[(13,false),(1,true),(7,false),(6,false),(9,true),(3,true),(11,false)])
                        .empty
                        .empty))
                    (.node 3091134 ([(4,true),(5,true),(12,true),(0,false),(8,false),(2,true),(10,true)],[(13,false),(1,true),(7,false),(3,false),(9,false),(6,false),(11,false)])
                      (.node 3090972 ([(3,true),(8,false),(6,false),(5,false),(13,false),(1,true),(10,true)],[(4,false),(9,true),(2,true),(7,true),(0,true),(12,false),(11,false)])
                        (.node 3087492 ([(2,true),(3,true),(4,true),(13,false),(0,false),(6,false),(10,true)],[(5,true),(9,false),(8,false),(7,false),(1,false),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3091146 ([(2,true),(3,true),(4,true),(13,false),(0,false),(6,false),(11,false)],[(5,true),(12,true),(1,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 3093822 ([(4,true),(5,true),(8,false),(0,false),(12,true),(2,true),(10,true)],[(13,false),(1,false),(7,false),(3,false),(9,false),(6,true),(11,false)])
                    (.node 3093600 ([(6,true),(0,true),(1,true),(13,true),(4,false),(3,false),(10,true)],[(5,true),(7,true),(8,true),(9,true),(2,false),(12,false),(11,false)])
                      (.node 3093072 ([(3,true),(4,true),(5,true),(6,true),(12,true),(1,false),(10,true)],[(13,false),(2,true),(7,true),(8,true),(9,true),(0,false),(11,false)])
                        (.node 3093024 ([(4,true),(5,true),(8,true),(2,false),(1,false),(0,false),(11,false)],[(13,false),(12,false),(6,false),(7,false),(3,false),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3093612 ([(4,true),(5,true),(6,true),(12,true),(1,false),(9,true),(10,true)],[(13,false),(2,true),(3,true),(7,true),(8,true),(0,false),(11,false)])
                        .empty
                        .empty))
                    (.node 3093936 ([(6,true),(0,true),(8,false),(2,false),(13,true),(4,false),(10,true)],[(5,true),(7,true),(3,true),(9,false),(1,true),(12,false),(11,false)])
                      (.node 3093840 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 3093954 ([(3,true),(4,true),(5,true),(8,true),(1,true),(12,false),(11,false)],[(13,false),(2,true),(7,true),(6,true),(0,true),(9,true),(10,true)])
                        .empty
                        .empty))))
                (.node 3104220 ([(0,true),(8,false),(2,false),(12,false),(4,true),(5,true),(10,true)],[(13,false),(1,false),(9,true),(6,true),(7,true),(3,true),(11,false)])
                  (.node 3095130 ([(3,true),(8,false),(5,false),(13,false),(1,false),(0,false),(10,true)],[(4,false),(9,true),(6,false),(7,false),(2,false),(12,false),(11,false)])
                    (.node 3094752 ([(3,true),(4,true),(13,false),(1,false),(0,false),(6,false),(10,true)],[(5,true),(9,false),(8,false),(7,false),(2,false),(12,false),(11,false)])
                      (.node 3094704 ([(4,true),(5,true),(9,false),(8,false),(1,true),(12,false),(11,false)],[(13,false),(2,true),(3,true),(7,true),(0,false),(6,false),(10,true)])
                        (.node 3094176 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3095082 ([(3,false),(8,false),(5,false),(13,false),(1,false),(0,false),(10,true)],[(4,false),(7,true),(6,true),(9,false),(2,false),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 3102282 ([(1,true),(2,true),(9,true),(6,false),(5,false),(4,false),(11,false)],[(13,false),(12,false),(3,false),(8,false),(7,false),(0,false),(10,true)])
                      (.node 3102252 ([(6,true),(0,true),(8,true),(2,false),(13,true),(4,false),(11,false)],[(5,true),(7,true),(1,true),(12,false),(3,false),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 3102750 ([(0,true),(1,true),(2,true),(8,true),(5,false),(4,false),(11,false)],[(13,false),(12,false),(3,false),(7,false),(6,false),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 3107952 ([(1,true),(2,true),(9,false),(8,false),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(0,true),(7,true),(3,false),(10,true)])
                    (.node 3107388 ([(4,true),(5,true),(12,true),(2,true),(8,false),(0,true),(10,true)],[(13,false),(1,false),(9,false),(3,true),(7,true),(6,false),(11,false)])
                      (.node 3107100 ([(3,true),(4,true),(5,true),(12,true),(1,false),(0,false),(10,true)],[(13,false),(2,true),(7,true),(8,true),(9,true),(6,false),(11,false)])
                        (.node 3107052 ([(4,true),(5,true),(12,true),(1,false),(8,true),(9,true),(10,true)],[(13,false),(2,true),(3,true),(7,true),(0,false),(6,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3107436 ([(3,true),(4,true),(13,false),(1,false),(0,false),(6,false),(11,false)],[(5,true),(12,true),(2,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 3108288 ([(1,true),(2,true),(8,true),(9,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(0,true),(7,true),(3,true),(10,true)])
                      (.node 3108000 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 3108336 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)))))
              (.node 3113088 ([(6,true),(0,true),(1,true),(2,true),(13,true),(4,false),(10,true)],[(5,true),(7,true),(8,true),(9,true),(3,false),(12,false),(11,false)])
                (.node 3110808 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 3110220 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                    (.node 3109962 ([(2,true),(3,true),(4,true),(5,true),(9,true),(0,false),(11,false)],[(13,false),(12,false),(6,false),(8,false),(7,false),(1,false),(10,true)])
                      (.node 3109950 ([(4,true),(5,true),(6,true),(12,true),(2,false),(1,false),(10,true)],[(13,false),(3,true),(7,true),(8,true),(9,true),(0,false),(11,false)])
                        (.node 3109878 ([(2,true),(12,false),(6,false),(5,false),(4,false),(9,true),(10,true)],[(13,false),(3,true),(8,false),(7,false),(1,false),(0,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3110190 ([(6,true),(0,true),(8,true),(4,true),(13,false),(2,false),(10,true)],[(5,true),(7,true),(1,true),(9,false),(3,false),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 3110304 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 3110286 ([(4,true),(5,true),(8,false),(0,false),(12,true),(2,false),(10,true)],[(13,false),(3,true),(7,true),(1,true),(9,false),(6,true),(11,false)])
                        .empty
                        .empty)
                      (.node 3110760 ([(2,true),(3,true),(4,true),(5,true),(8,true),(0,false),(11,false)],[(13,false),(12,false),(6,false),(7,false),(1,false),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 3111912 ([(6,true),(9,false),(4,true),(13,false),(2,false),(1,false),(11,false)],[(5,true),(7,true),(8,true),(3,false),(12,false),(0,false),(10,true)])
                    (.node 3111828 ([(6,true),(9,false),(8,false),(4,true),(13,false),(12,false),(11,false)],[(5,true),(7,true),(3,false),(2,false),(1,false),(0,false),(10,true)])
                      (.node 3111480 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 3111432 ([(2,true),(12,false),(0,true),(8,false),(4,true),(5,true),(10,true)],[(13,false),(3,true),(7,false),(1,false),(9,true),(6,true),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3111840 ([(4,true),(5,true),(6,true),(9,false),(2,true),(12,false),(11,false)],[(13,false),(3,true),(7,true),(8,true),(1,false),(0,false),(10,true)])
                        .empty
                        .empty))
                    (.node 3112416 ([(6,true),(8,false),(4,true),(13,false),(2,false),(1,false),(11,false)],[(5,true),(7,true),(3,false),(12,false),(0,false),(9,true),(10,true)])
                      (.node 3111936 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 3112704 ([(0,true),(12,true),(13,true),(4,false),(8,true),(9,true),(10,true)],[(5,true),(6,true),(7,true),(3,false),(2,false),(1,false),(11,false)])
                        .empty
                        .empty))))
                (.node 3124254 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(11,false)],[(13,false),(12,false),(6,true),(7,true),(8,true),(9,true),(10,true)])
                  (.node 3113964 ([(0,true),(1,true),(2,true),(13,true),(4,false),(9,true),(10,true)],[(5,true),(6,true),(7,true),(8,true),(3,false),(12,false),(11,false)])
                    (.node 3113880 ([(0,true),(1,true),(8,false),(3,false),(13,true),(5,true),(10,true)],[(4,false),(7,false),(6,false),(9,false),(2,true),(12,false),(11,false)])
                      (.node 3113856 ([(4,true),(5,true),(6,true),(8,true),(2,true),(12,false),(11,false)],[(13,false),(3,true),(7,true),(0,true),(1,true),(9,true),(10,true)])
                        (.node 3113376 ([(0,true),(1,true),(8,true),(5,false),(13,false),(3,true),(10,true)],[(4,false),(9,false),(6,true),(7,true),(2,true),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3113952 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 3123828 ([(1,true),(8,false),(3,false),(13,true),(5,true),(6,true),(10,true)],[(4,false),(7,false),(0,false),(9,false),(2,true),(12,false),(11,false)])
                      (.node 3114762 ([(0,true),(9,false),(8,false),(4,true),(13,false),(2,false),(11,false)],[(5,true),(6,true),(7,true),(3,false),(12,false),(1,false),(10,true)])
                        .empty
                        .empty)
                      (.node 3124242 ([(2,true),(12,false),(5,false),(4,false),(8,false),(0,true),(10,true)],[(13,false),(3,true),(9,true),(1,true),(7,true),(6,false),(11,false)])
                        .empty
                        .empty)))
                  (.node 3201420 ([(5,true),(6,true),(8,true),(3,false),(12,true),(1,true),(10,true)],[(13,false),(0,false),(7,false),(4,false),(9,true),(2,true),(11,false)])
                    (.node 3200748 ([(5,true),(6,true),(0,true),(1,true),(8,true),(3,false),(11,false)],[(13,false),(12,false),(2,false),(7,false),(4,false),(9,true),(10,true)])
                      (.node 3199410 ([(4,true),(8,false),(6,false),(13,false),(1,true),(2,true),(10,true)],[(5,false),(9,true),(3,true),(7,true),(0,true),(12,false),(11,false)])
                        (.node 3124416 ([(1,true),(2,true),(13,true),(4,false),(8,true),(6,false),(11,false)],[(5,true),(12,true),(3,true),(7,false),(0,false),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3200796 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 3201924 ([(5,true),(6,true),(8,false),(1,false),(12,false),(3,true),(10,true)],[(13,false),(0,false),(9,true),(4,true),(7,true),(2,true),(11,false)])
                      (.node 3201468 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 3201942 ([(2,true),(12,true),(0,false),(6,false),(5,false),(4,false),(10,true)],[(13,false),(1,true),(7,true),(8,true),(9,true),(3,false),(11,false)])
                        .empty
                        .empty))))))
            (.node 3220806 ([(1,true),(13,true),(5,false),(8,true),(9,true),(3,true),(11,false)],[(6,true),(0,true),(7,true),(4,false),(12,true),(2,true),(10,true)])
              (.node 3206220 ([(3,true),(8,false),(6,false),(5,false),(12,true),(1,true),(10,true)],[(13,false),(0,false),(7,false),(2,false),(9,false),(4,true),(11,false)])
                (.node 3203658 ([(3,true),(4,true),(5,true),(13,false),(0,false),(9,true),(10,true)],[(6,true),(8,false),(7,false),(2,false),(1,false),(12,false),(11,false)])
                  (.node 3202374 ([(0,true),(13,true),(5,false),(4,false),(8,true),(2,true),(11,false)],[(6,true),(7,true),(3,false),(12,true),(1,true),(9,true),(10,true)])
                    (.node 3202278 ([(2,true),(3,true),(8,true),(0,true),(13,true),(5,false),(10,true)],[(6,true),(9,true),(4,false),(7,false),(1,false),(12,false),(11,false)])
                      (.node 3202266 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 3202038 ([(0,true),(13,true),(5,false),(4,false),(9,false),(2,true),(11,false)],[(6,true),(7,true),(8,true),(1,false),(12,false),(3,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3202350 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(11,false)],[(13,false),(12,false),(3,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 3203118 ([(2,true),(3,true),(4,true),(5,true),(13,false),(0,false),(10,true)],[(6,true),(9,false),(8,false),(7,false),(1,false),(12,false),(11,false)])
                      (.node 3203070 ([(3,true),(4,true),(8,true),(1,false),(13,true),(6,true),(10,true)],[(5,false),(7,false),(2,false),(9,true),(0,true),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 3203646 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 3204210 ([(2,true),(9,false),(5,true),(6,true),(0,true),(12,false),(11,false)],[(13,false),(1,true),(7,true),(8,true),(4,false),(3,false),(10,true)])
                    (.node 3203982 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 3203886 ([(0,true),(13,true),(5,false),(4,false),(3,false),(2,false),(10,true)],[(6,true),(7,true),(8,true),(9,true),(1,false),(12,false),(11,false)])
                        (.node 3203868 ([(3,true),(4,true),(8,false),(6,false),(13,false),(1,true),(10,true)],[(5,false),(9,true),(2,true),(7,true),(0,true),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3204000 ([(2,true),(9,false),(0,true),(13,true),(5,false),(4,false),(11,false)],[(6,true),(8,false),(7,false),(1,false),(12,false),(3,false),(10,true)])
                        .empty
                        .empty))
                    (.node 3204750 ([(3,true),(12,true),(1,true),(8,false),(6,false),(5,false),(10,true)],[(13,false),(0,false),(7,false),(2,false),(9,true),(4,false),(11,false)])
                      (.node 3204222 ([(0,true),(13,true),(5,false),(8,false),(2,true),(3,true),(11,false)],[(6,true),(7,true),(1,false),(12,false),(4,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 3204798 ([(2,true),(3,true),(12,true),(0,false),(6,false),(5,false),(10,true)],[(13,false),(1,true),(7,true),(8,true),(9,true),(4,false),(11,false)])
                        .empty
                        .empty))))
                (.node 3218796 ([(0,true),(8,false),(5,true),(13,false),(2,true),(3,true),(10,true)],[(6,true),(7,true),(4,false),(9,false),(1,true),(12,false),(11,false)])
                  (.node 3211584 ([(5,true),(6,true),(12,true),(1,false),(8,false),(3,true),(10,true)],[(13,false),(2,true),(7,false),(4,false),(9,false),(0,false),(11,false)])
                    (.node 3206808 ([(3,true),(9,false),(8,false),(0,true),(13,true),(5,false),(11,false)],[(6,true),(7,false),(2,false),(1,false),(12,false),(4,false),(10,true)])
                      (.node 3206394 ([(2,true),(3,true),(8,true),(6,false),(13,false),(12,false),(11,false)],[(5,false),(4,false),(7,false),(1,false),(0,false),(9,true),(10,true)])
                        (.node 3206382 ([(4,true),(5,true),(13,false),(0,false),(8,false),(2,true),(10,true)],[(6,true),(9,true),(3,true),(7,true),(1,false),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3211422 ([(4,true),(8,false),(0,false),(6,false),(13,false),(2,true),(10,true)],[(5,false),(9,true),(3,true),(7,true),(1,true),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 3212010 ([(4,true),(5,true),(13,false),(2,true),(8,false),(0,false),(11,false)],[(6,true),(12,true),(1,false),(7,false),(3,false),(9,true),(10,true)])
                      (.node 3211596 ([(3,true),(4,true),(5,true),(13,false),(1,false),(0,false),(11,false)],[(6,true),(12,true),(2,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 3218748 ([(0,false),(8,false),(5,true),(13,false),(2,true),(3,true),(10,true)],[(6,true),(9,true),(4,true),(7,false),(1,true),(12,false),(11,false)])
                        .empty
                        .empty)))
                  (.node 3220236 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                    (.node 3219996 ([(3,true),(4,true),(5,true),(13,false),(1,false),(0,false),(10,true)],[(6,true),(9,false),(8,false),(7,false),(2,false),(12,false),(11,false)])
                      (.node 3219924 ([(1,true),(2,true),(9,true),(6,false),(5,false),(4,false),(11,false)],[(13,false),(12,false),(3,false),(8,false),(7,false),(0,false),(10,true)])
                        (.node 3219900 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(11,false)],[(13,false),(12,false),(4,true),(7,true),(8,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3220008 ([(1,true),(12,false),(3,false),(8,true),(5,true),(6,true),(10,true)],[(13,false),(2,true),(7,false),(0,false),(9,false),(4,false),(11,false)])
                        .empty
                        .empty))
                    (.node 3220332 ([(3,true),(4,true),(8,false),(6,false),(13,false),(1,false),(10,true)],[(5,false),(9,true),(0,false),(7,false),(2,false),(12,false),(11,false)])
                      (.node 3220266 ([(0,true),(1,true),(13,true),(5,false),(8,true),(3,true),(11,false)],[(6,true),(7,true),(4,false),(12,true),(2,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 3220350 ([(0,true),(1,true),(13,true),(5,false),(8,false),(3,true),(11,false)],[(6,true),(7,true),(2,false),(12,false),(4,true),(9,true),(10,true)])
                        .empty
                        .empty)))))
              (.node 3228738 ([(2,true),(3,true),(8,true),(9,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(1,true),(7,true),(4,true),(10,true)])
                (.node 3223248 ([(0,true),(1,true),(13,true),(5,false),(4,false),(3,false),(10,true)],[(6,true),(7,true),(8,true),(9,true),(2,false),(12,false),(11,false)])
                  (.node 3222348 ([(3,true),(4,true),(5,true),(13,false),(1,false),(0,false),(10,true)],[(6,true),(9,false),(8,false),(7,false),(2,false),(12,false),(11,false)])
                    (.node 3221526 ([(0,true),(8,false),(2,false),(13,true),(5,false),(4,false),(11,false)],[(6,true),(7,true),(3,true),(12,true),(1,false),(9,true),(10,true)])
                      (.node 3221478 ([(1,true),(2,true),(8,true),(6,false),(5,false),(4,false),(11,false)],[(13,false),(12,false),(3,false),(7,false),(0,false),(9,true),(10,true)])
                        (.node 3220854 ([(0,true),(1,true),(13,true),(5,false),(4,false),(3,false),(10,true)],[(6,true),(7,true),(8,true),(9,true),(2,false),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3222300 ([(4,true),(5,true),(13,false),(1,false),(8,true),(9,true),(10,true)],[(6,true),(0,true),(7,false),(3,false),(2,false),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 3222684 ([(3,true),(8,false),(6,false),(5,false),(12,true),(1,false),(10,true)],[(13,false),(2,true),(7,true),(0,true),(9,false),(4,true),(11,false)])
                      (.node 3222636 ([(4,true),(5,true),(13,false),(2,true),(8,false),(0,true),(10,true)],[(6,true),(7,false),(3,false),(9,true),(1,true),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 3223200 ([(1,true),(2,true),(3,true),(8,true),(6,false),(5,false),(11,false)],[(13,false),(12,false),(4,false),(7,false),(0,false),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 3227838 ([(5,true),(6,true),(12,true),(3,true),(8,false),(1,true),(10,true)],[(13,false),(2,false),(9,false),(4,true),(7,true),(0,false),(11,false)])
                    (.node 3227502 ([(5,true),(6,true),(12,true),(2,false),(8,true),(9,true),(10,true)],[(13,false),(3,true),(4,true),(7,true),(1,false),(0,false),(11,false)])
                      (.node 3223584 ([(0,true),(8,false),(2,false),(13,true),(5,false),(4,false),(10,true)],[(6,true),(7,true),(3,true),(9,false),(1,true),(12,false),(11,false)])
                        (.node 3223536 ([(1,true),(12,false),(5,true),(6,true),(8,false),(3,true),(10,true)],[(13,false),(2,true),(7,false),(0,false),(9,true),(4,true),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3227550 ([(4,true),(5,true),(6,true),(12,true),(2,false),(1,false),(10,true)],[(13,false),(3,true),(7,true),(8,true),(9,true),(0,false),(11,false)])
                        .empty
                        .empty))
                    (.node 3228402 ([(2,true),(3,true),(9,false),(8,false),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(1,true),(7,true),(4,false),(10,true)])
                      (.node 3227886 ([(4,true),(5,true),(13,false),(2,false),(1,false),(0,false),(11,false)],[(6,true),(12,true),(3,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 3228450 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))))
                (.node 3230850 ([(0,true),(1,true),(2,true),(13,true),(5,false),(4,false),(10,true)],[(6,true),(7,true),(8,true),(9,true),(3,false),(12,false),(11,false)])
                  (.node 3230280 ([(4,true),(5,true),(6,true),(0,true),(12,true),(2,false),(10,true)],[(13,false),(3,true),(7,true),(8,true),(9,true),(1,false),(11,false)])
                    (.node 3229608 ([(4,true),(5,true),(13,false),(2,false),(1,false),(0,false),(10,true)],[(6,true),(9,false),(8,false),(7,false),(3,false),(12,false),(11,false)])
                      (.node 3229560 ([(5,true),(6,true),(9,false),(8,false),(2,true),(12,false),(11,false)],[(13,false),(3,true),(4,true),(7,true),(1,false),(0,false),(10,true)])
                        (.node 3228786 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3230232 ([(5,true),(6,true),(8,true),(3,false),(2,false),(1,false),(11,false)],[(13,false),(12,false),(0,false),(7,false),(4,false),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 3230754 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 3230736 ([(5,true),(6,true),(8,false),(1,false),(12,true),(3,true),(10,true)],[(13,false),(2,false),(7,false),(4,false),(9,false),(0,true),(11,false)])
                        .empty
                        .empty)
                      (.node 3230820 ([(5,true),(6,true),(0,true),(12,true),(2,false),(9,true),(10,true)],[(13,false),(3,true),(4,true),(7,true),(8,true),(1,false),(11,false)])
                        .empty
                        .empty)))
                  (.node 3232290 ([(4,false),(8,false),(6,false),(13,false),(2,false),(1,false),(10,true)],[(5,false),(7,true),(0,true),(9,false),(3,false),(12,false),(11,false)])
                    (.node 3231162 ([(4,true),(5,true),(6,true),(8,true),(2,true),(12,false),(11,false)],[(13,false),(3,true),(7,true),(0,true),(1,true),(9,true),(10,true)])
                      (.node 3231090 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 3231078 ([(4,true),(5,true),(6,true),(8,false),(2,true),(12,false),(11,false)],[(13,false),(3,true),(7,true),(1,false),(0,false),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3231186 ([(0,true),(1,true),(8,false),(3,false),(13,true),(5,false),(10,true)],[(6,true),(7,true),(4,true),(9,false),(2,true),(12,false),(11,false)])
                        .empty
                        .empty))
                    (.node 3239076 ([(1,true),(8,false),(3,false),(12,false),(5,true),(6,true),(10,true)],[(13,false),(2,false),(9,true),(0,true),(7,true),(4,true),(11,false)])
                      (.node 3232338 ([(4,true),(8,false),(6,false),(13,false),(2,false),(1,false),(10,true)],[(5,false),(9,true),(0,false),(7,false),(3,false),(12,false),(11,false)])
                        .empty
                        .empty)
                      (.node 3239490 ([(2,true),(3,true),(9,true),(0,false),(6,false),(5,false),(11,false)],[(13,false),(12,false),(4,false),(8,false),(7,false),(1,false),(10,true)])
                        .empty
                        .empty))))))))))
    (.node 3931495 ([(1,true),(13,true),(4,false),(8,true),(9,true),(10,true),(11,true)],[(5,true),(6,true),(0,true),(7,true),(3,false),(2,false),(12,false)])
      (.node 3631759 ([(5,true),(13,true),(1,false),(8,false),(3,true),(10,true),(11,true)],[(2,true),(7,false),(4,false),(9,false),(0,false),(6,false),(12,false)])
        (.node 3478153 ([(0,true),(1,true),(8,false),(5,true),(10,false),(3,false),(12,false)],[(13,false),(2,false),(9,true),(4,true),(7,false),(6,false),(11,true)])
          (.node 3359557 ([(5,true),(6,true),(0,true),(1,true),(8,true),(3,false),(12,false)],[(13,false),(2,false),(7,false),(4,false),(9,true),(10,true),(11,true)])
            (.node 3338053 ([(5,true),(6,true),(0,true),(10,true),(3,false),(2,false),(12,false)],[(13,false),(1,false),(9,false),(8,false),(7,false),(4,false),(11,true)])
              (.node 3248736 ([(1,true),(2,true),(8,false),(4,false),(13,true),(6,true),(10,true)],[(5,false),(7,false),(0,false),(9,false),(3,true),(12,false),(11,false)])
                (.node 3247086 ([(3,true),(12,false),(0,false),(6,false),(5,false),(9,true),(10,true)],[(13,false),(4,true),(8,false),(7,false),(2,false),(1,false),(11,false)])
                  (.node 3244866 ([(2,true),(3,true),(13,true),(5,false),(8,true),(0,false),(11,false)],[(6,true),(12,true),(4,true),(7,false),(1,false),(9,true),(10,true)])
                    (.node 3244692 ([(3,true),(12,false),(6,false),(5,false),(8,false),(1,true),(10,true)],[(13,false),(4,true),(9,true),(2,true),(7,true),(0,false),(11,false)])
                      (.node 3244278 ([(2,true),(8,false),(4,false),(13,true),(6,true),(0,true),(10,true)],[(5,false),(7,false),(1,false),(9,false),(3,true),(12,false),(11,false)])
                        (.node 3239664 ([(1,true),(2,true),(3,true),(8,true),(6,false),(5,false),(11,false)],[(13,false),(12,false),(4,false),(7,false),(0,false),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3244704 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(11,false)],[(13,false),(12,false),(0,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 3246864 ([(5,true),(6,true),(0,true),(12,true),(3,false),(2,false),(10,true)],[(13,false),(4,true),(7,true),(8,true),(9,true),(1,false),(11,false)])
                      (.node 3246336 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                        (.node 3246288 ([(3,true),(12,false),(1,true),(8,false),(5,true),(6,true),(10,true)],[(13,false),(4,true),(7,false),(2,false),(9,true),(0,true),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3246876 ([(3,true),(4,true),(5,true),(6,true),(9,true),(1,false),(11,false)],[(13,false),(12,false),(0,false),(8,false),(7,false),(2,false),(10,true)])
                        .empty
                        .empty)))
                  (.node 3247440 ([(0,true),(1,true),(8,true),(5,true),(13,false),(3,false),(10,true)],[(6,true),(7,true),(2,true),(9,false),(4,false),(12,false),(11,false)])
                    (.node 3247218 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 3247200 ([(5,true),(6,true),(8,false),(1,false),(12,true),(3,false),(10,true)],[(13,false),(4,true),(7,true),(2,true),(9,false),(0,true),(11,false)])
                        (.node 3247104 ([(0,true),(12,true),(13,true),(5,false),(8,false),(2,false),(10,true)],[(6,true),(7,true),(3,true),(4,true),(9,true),(1,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3247428 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                        .empty
                        .empty))
                    (.node 3248016 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(11,false)],[(13,false),(12,false),(1,true),(7,true),(8,true),(9,true),(10,true)])
                      (.node 3247968 ([(3,true),(4,true),(5,true),(6,true),(8,true),(1,false),(11,false)],[(13,false),(12,false),(0,false),(7,false),(2,false),(9,true),(10,true)])
                        .empty
                        .empty)
                      (.node 3248712 ([(5,true),(6,true),(0,true),(8,true),(3,true),(12,false),(11,false)],[(13,false),(4,true),(7,true),(1,true),(2,true),(9,true),(10,true)])
                        .empty
                        .empty))))
                (.node 3250290 ([(1,true),(2,true),(8,true),(6,false),(13,false),(4,true),(10,true)],[(5,false),(9,false),(0,true),(7,true),(3,true),(12,false),(11,false)])
                  (.node 3249144 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
                    (.node 3249048 ([(5,true),(6,true),(0,true),(9,false),(3,true),(12,false),(11,false)],[(13,false),(4,true),(7,true),(8,true),(2,false),(1,false),(10,true)])
                      (.node 3248820 ([(1,true),(2,true),(3,true),(13,true),(5,false),(9,true),(10,true)],[(6,true),(0,true),(7,true),(8,true),(4,false),(12,false),(11,false)])
                        (.node 3248808 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(11,false)],[(13,false),(12,false),(2,true),(7,true),(8,true),(9,true),(10,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3249078 ([(0,true),(9,false),(8,false),(5,true),(13,false),(12,false),(11,false)],[(6,true),(7,true),(4,false),(3,false),(2,false),(1,false),(10,true)])
                        .empty
                        .empty))
                    (.node 3249618 ([(1,true),(12,true),(13,true),(5,false),(8,true),(9,true),(10,true)],[(6,true),(0,true),(7,true),(4,false),(3,false),(2,false),(11,false)])
                      (.node 3249162 ([(0,true),(9,false),(5,true),(13,false),(3,false),(2,false),(11,false)],[(6,true),(7,true),(8,true),(4,false),(12,false),(1,false),(10,true)])
                        .empty
                        .empty)
                      (.node 3249666 ([(0,true),(8,false),(5,true),(13,false),(3,false),(2,false),(11,false)],[(6,true),(7,true),(4,false),(12,false),(1,false),(9,true),(10,true)])
                        .empty
                        .empty)))
                  (.node 3336787 ([(6,true),(0,true),(8,false),(4,true),(10,true),(2,false),(12,false)],[(13,false),(1,false),(9,true),(5,true),(7,true),(3,false),(11,true)])
                    (.node 3331879 ([(5,true),(8,false),(3,true),(10,true),(0,false),(13,false),(12,false)],[(6,false),(9,true),(4,true),(7,true),(2,false),(1,false),(11,true)])
                      (.node 3251676 ([(1,true),(9,false),(8,false),(5,true),(13,false),(3,false),(11,false)],[(6,true),(0,true),(7,true),(4,false),(12,false),(2,false),(10,true)])
                        (.node 3250338 ([(0,true),(1,true),(2,true),(3,true),(13,true),(5,false),(10,true)],[(6,true),(7,true),(8,true),(9,true),(4,false),(12,false),(11,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3332095 ([(4,true),(5,true),(8,true),(2,false),(13,true),(0,true),(11,true)],[(6,false),(7,false),(3,false),(9,true),(10,true),(1,true),(12,false)])
                        .empty
                        .empty))
                    (.node 3337255 ([(5,true),(6,true),(0,true),(8,true),(3,false),(2,false),(12,false)],[(13,false),(1,false),(7,false),(4,false),(9,true),(10,true),(11,true)])
                      (.node 3336799 ([(4,true),(5,true),(8,true),(0,false),(13,false),(2,true),(11,true)],[(6,false),(7,false),(3,false),(10,false),(9,false),(1,true),(12,false)])
                        .empty
                        .empty)
                      (.node 3338005 ([(6,true),(0,true),(10,true),(4,true),(8,false),(2,false),(12,false)],[(13,false),(1,false),(9,false),(5,true),(7,true),(3,true),(11,true)])
                        .empty
                        .empty)))))
              (.node 3351073 ([(5,true),(8,false),(0,false),(13,false),(3,true),(10,true),(11,true)],[(6,false),(9,true),(4,true),(7,true),(1,true),(2,true),(12,false)])
                (.node 3341125 ([(4,true),(10,false),(9,false),(6,true),(0,true),(1,true),(12,false)],[(13,false),(2,true),(3,true),(7,true),(8,true),(5,false),(11,true)])
                  (.node 3340327 ([(4,true),(5,true),(8,true),(9,true),(0,false),(13,false),(12,false)],[(6,false),(7,false),(3,false),(2,false),(1,false),(10,true),(11,true)])
                    (.node 3339607 ([(5,true),(6,true),(13,false),(1,false),(8,true),(3,true),(11,true)],[(0,true),(7,false),(4,false),(10,false),(9,false),(2,false),(12,false)])
                      (.node 3339535 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(12,false)],[(13,false),(2,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        (.node 3339523 ([(5,true),(6,true),(13,false),(1,false),(8,false),(3,true),(11,true)],[(0,true),(9,true),(10,true),(4,true),(7,true),(2,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3339631 ([(1,true),(13,true),(6,false),(5,false),(8,true),(3,true),(11,true)],[(0,true),(7,true),(4,false),(10,false),(9,false),(2,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3340903 ([(6,true),(0,true),(8,false),(4,true),(10,false),(2,false),(12,false)],[(13,false),(1,false),(9,true),(3,true),(7,false),(5,false),(11,true)])
                      (.node 3340375 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(12,false)],[(13,false),(2,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3340915 ([(4,true),(5,true),(6,true),(0,true),(9,true),(2,false),(12,false)],[(13,false),(1,false),(8,false),(7,false),(3,false),(10,true),(11,true)])
                        .empty
                        .empty)))
                  (.node 3348679 ([(4,false),(3,false),(13,true),(6,false),(8,false),(1,false),(11,true)],[(0,true),(10,false),(9,false),(5,false),(7,true),(2,true),(12,false)])
                    (.node 3343639 ([(5,true),(6,true),(0,true),(9,true),(3,false),(2,false),(12,false)],[(13,false),(1,false),(8,false),(7,false),(4,false),(10,true),(11,true)])
                      (.node 3343477 ([(4,true),(8,false),(0,false),(6,false),(10,false),(2,false),(12,false)],[(13,false),(1,false),(7,false),(3,false),(9,false),(5,true),(11,true)])
                        (.node 3341143 ([(1,true),(13,true),(6,false),(8,false),(3,false),(10,true),(11,true)],[(0,true),(7,true),(4,true),(5,true),(9,true),(2,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3343651 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(12,false)],[(13,false),(2,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3348853 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(12,false)],[(13,false),(3,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3348841 ([(6,true),(0,true),(1,true),(9,true),(4,false),(3,false),(12,false)],[(13,false),(2,false),(8,false),(7,false),(5,false),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3349267 ([(5,true),(6,true),(0,true),(1,true),(8,true),(3,false),(12,false)],[(13,false),(2,false),(7,false),(4,false),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))))
                (.node 3356389 ([(1,true),(2,true),(13,true),(6,false),(5,false),(4,false),(11,true)],[(0,true),(7,true),(8,true),(9,true),(10,true),(3,false),(12,false)])
                  (.node 3354853 ([(5,true),(6,true),(13,false),(2,false),(1,false),(10,true),(11,true)],[(0,true),(9,false),(8,false),(7,false),(4,false),(3,false),(12,false)])
                    (.node 3351661 ([(5,true),(6,true),(13,false),(3,true),(8,false),(1,true),(11,true)],[(0,true),(7,false),(4,false),(9,true),(10,true),(2,true),(12,false)])
                      (.node 3351205 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(12,false)],[(13,false),(3,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        (.node 3351193 ([(6,true),(0,true),(8,false),(4,true),(10,true),(2,true),(12,false)],[(13,false),(3,true),(7,false),(5,false),(9,false),(1,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3354805 ([(6,true),(0,true),(1,true),(8,true),(4,false),(3,false),(12,false)],[(13,false),(2,false),(7,false),(5,false),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3355189 ([(5,true),(6,true),(0,true),(1,true),(10,true),(3,false),(12,false)],[(13,false),(2,false),(9,false),(8,false),(7,false),(4,false),(11,true)])
                      (.node 3355141 ([(6,true),(0,true),(8,true),(9,true),(10,true),(3,false),(12,false)],[(13,false),(2,false),(1,false),(7,false),(5,false),(4,false),(11,true)])
                        .empty
                        .empty)
                      (.node 3356341 ([(2,true),(13,true),(6,false),(9,false),(8,false),(4,false),(11,true)],[(0,true),(1,true),(7,true),(5,true),(10,true),(3,false),(12,false)])
                        .empty
                        .empty)))
                  (.node 3357493 ([(6,true),(0,true),(1,true),(10,true),(4,false),(3,false),(12,false)],[(13,false),(2,false),(9,false),(8,false),(7,false),(5,false),(11,true)])
                    (.node 3357253 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(12,false)],[(13,false),(3,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3357181 ([(2,true),(13,true),(6,false),(8,true),(9,true),(10,true),(11,true)],[(0,true),(1,true),(7,true),(5,false),(4,false),(3,false),(12,false)])
                        (.node 3357157 ([(6,true),(0,true),(10,true),(4,false),(8,false),(2,true),(12,false)],[(13,false),(3,true),(9,true),(1,true),(7,false),(5,false),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3357265 ([(2,true),(13,true),(0,true),(9,false),(8,false),(4,true),(11,true)],[(6,false),(5,false),(10,false),(1,true),(7,true),(3,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3357589 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(12,false)],[(13,false),(3,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3357523 ([(1,true),(2,true),(13,true),(6,false),(8,true),(4,true),(11,true)],[(0,true),(7,true),(5,false),(10,false),(9,false),(3,false),(12,false)])
                        .empty
                        .empty)
                      (.node 3357607 ([(1,true),(9,false),(6,true),(13,false),(3,true),(4,true),(11,true)],[(0,true),(7,true),(8,true),(5,false),(10,false),(2,true),(12,false)])
                        .empty
                        .empty))))))
            (.node 3384457 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(12,false)],[(13,false),(5,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
              (.node 3368443 ([(1,true),(2,true),(8,false),(5,true),(6,true),(13,false),(12,false)],[(0,true),(7,true),(4,false),(3,false),(9,true),(10,true),(11,true)])
                (.node 3365995 ([(3,true),(13,true),(6,false),(5,false),(8,true),(1,false),(11,true)],[(0,true),(10,false),(9,false),(2,true),(7,true),(4,false),(12,false)])
                  (.node 3360505 ([(1,true),(8,false),(4,false),(3,false),(13,true),(6,false),(11,true)],[(0,true),(7,true),(5,true),(10,false),(9,false),(2,true),(12,false)])
                    (.node 3359941 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(12,false)],[(13,false),(3,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3359893 ([(5,true),(6,true),(0,true),(8,true),(9,true),(2,true),(12,false)],[(13,false),(3,true),(4,true),(7,true),(1,true),(10,true),(11,true)])
                        (.node 3359605 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(12,false)],[(13,false),(3,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3360457 ([(2,true),(13,true),(0,true),(8,false),(4,false),(10,true),(11,true)],[(6,false),(5,false),(7,false),(1,false),(9,true),(3,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3365659 ([(3,true),(13,true),(6,false),(8,true),(9,true),(10,true),(11,true)],[(0,true),(1,true),(2,true),(7,true),(5,false),(4,false),(12,false)])
                      (.node 3365143 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(12,false)],[(13,false),(4,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        (.node 3365095 ([(6,true),(0,true),(1,true),(8,true),(9,true),(3,true),(12,false)],[(13,false),(4,true),(5,true),(7,true),(2,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3365707 ([(2,true),(3,true),(13,true),(6,false),(5,false),(10,true),(11,true)],[(0,true),(1,true),(7,true),(8,true),(9,true),(4,false),(12,false)])
                        .empty
                        .empty)))
                  (.node 3368107 ([(1,true),(2,true),(9,true),(5,true),(6,true),(13,false),(12,false)],[(0,true),(7,true),(8,true),(3,true),(4,true),(10,true),(11,true)])
                    (.node 3368011 ([(3,true),(13,true),(6,false),(5,false),(9,false),(1,true),(11,true)],[(0,true),(8,false),(7,false),(2,false),(10,false),(4,false),(12,false)])
                      (.node 3367993 ([(6,true),(0,true),(8,false),(2,false),(10,false),(4,false),(12,false)],[(13,false),(3,false),(7,false),(5,false),(9,false),(1,true),(11,true)])
                        (.node 3366043 ([(2,true),(8,false),(4,false),(13,true),(6,false),(10,true),(11,true)],[(0,true),(1,true),(7,true),(5,true),(9,false),(3,true),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3368077 ([(6,true),(0,true),(1,true),(2,true),(9,true),(4,false),(12,false)],[(13,false),(3,false),(8,false),(7,false),(5,false),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3368347 ([(3,true),(13,true),(6,false),(5,false),(8,true),(1,true),(11,true)],[(0,true),(9,true),(10,true),(2,true),(7,true),(4,false),(12,false)])
                      (.node 3368335 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(12,false)],[(13,false),(4,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3368419 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(12,false)],[(13,false),(4,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))))
                (.node 3374407 ([(1,true),(2,true),(3,true),(13,true),(6,false),(5,false),(11,true)],[(0,true),(7,true),(8,true),(9,true),(10,true),(4,false),(12,false)])
                  (.node 3370747 ([(2,true),(10,false),(5,false),(8,true),(0,false),(13,false),(12,false)],[(6,false),(9,false),(1,true),(7,true),(4,false),(3,false),(11,true)])
                    (.node 3370411 ([(2,true),(10,false),(5,true),(8,true),(0,false),(13,false),(12,false)],[(6,false),(7,false),(1,false),(9,true),(4,false),(3,false),(11,true)])
                      (.node 3369259 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(12,false)],[(13,false),(4,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        (.node 3369211 ([(6,true),(0,true),(9,false),(8,false),(2,true),(3,true),(12,false)],[(13,false),(4,true),(5,true),(7,true),(1,false),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3370459 ([(1,true),(2,true),(10,false),(5,true),(6,true),(13,false),(12,false)],[(0,true),(7,true),(8,true),(9,true),(4,false),(3,false),(11,true)])
                        .empty
                        .empty))
                    (.node 3373939 ([(2,true),(8,false),(5,false),(10,false),(0,false),(13,false),(12,false)],[(6,false),(7,false),(1,false),(9,false),(3,true),(4,true),(11,true)])
                      (.node 3370795 ([(1,true),(8,false),(4,false),(13,true),(6,false),(10,true),(11,true)],[(0,true),(7,true),(5,true),(9,false),(2,true),(3,true),(12,false)])
                        .empty
                        .empty)
                      (.node 3374395 ([(3,true),(13,true),(6,false),(8,false),(1,true),(10,true),(11,true)],[(0,true),(7,false),(2,false),(9,false),(5,false),(4,false),(12,false)])
                        .empty
                        .empty)))
                  (.node 3376921 ([(2,true),(3,true),(13,true),(0,true),(8,false),(5,true),(11,true)],[(6,false),(10,false),(9,false),(1,true),(7,true),(4,false),(12,false)])
                    (.node 3376747 ([(3,true),(13,true),(0,true),(1,true),(9,false),(5,true),(11,true)],[(6,false),(10,false),(2,true),(7,true),(8,true),(4,false),(12,false)])
                      (.node 3376333 ([(2,true),(8,false),(4,false),(13,true),(0,true),(10,true),(11,true)],[(6,false),(5,false),(7,false),(1,false),(9,false),(3,true),(12,false)])
                        (.node 3374527 ([(2,true),(3,true),(13,true),(0,true),(8,false),(5,false),(11,true)],[(6,false),(7,false),(1,false),(9,true),(10,true),(4,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3376759 ([(1,true),(2,true),(8,true),(5,true),(6,true),(13,false),(12,false)],[(0,true),(7,true),(3,true),(4,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3381961 ([(2,true),(3,true),(8,true),(5,false),(13,true),(0,true),(11,true)],[(6,false),(9,true),(10,true),(1,true),(7,true),(4,true),(12,false)])
                      (.node 3381949 ([(4,true),(13,true),(6,false),(8,false),(2,true),(10,true),(11,true)],[(0,true),(1,true),(7,false),(3,false),(9,false),(5,false),(12,false)])
                        .empty
                        .empty)
                      (.node 3382123 ([(3,true),(4,true),(13,true),(6,false),(8,true),(1,false),(11,true)],[(0,true),(10,false),(9,false),(2,true),(7,true),(5,false),(12,false)])
                        .empty
                        .empty)))))
              (.node 3464089 ([(6,true),(0,true),(1,true),(9,true),(4,false),(3,false),(12,false)],[(13,false),(2,false),(8,false),(7,false),(5,false),(10,true),(11,true)])
                (.node 3386077 ([(2,true),(3,true),(8,true),(9,true),(0,false),(13,false),(12,false)],[(6,false),(5,false),(4,false),(7,false),(1,false),(10,true),(11,true)])
                  (.node 3385273 ([(3,true),(9,true),(5,false),(13,true),(0,true),(1,true),(11,true)],[(6,false),(10,true),(2,true),(7,true),(8,true),(4,true),(12,false)])
                    (.node 3384697 ([(1,true),(2,true),(3,true),(9,false),(6,true),(13,false),(12,false)],[(0,true),(7,true),(8,true),(5,false),(4,false),(10,true),(11,true)])
                      (.node 3384685 ([(3,true),(4,true),(13,true),(6,false),(8,false),(1,true),(11,true)],[(0,true),(7,false),(2,false),(10,false),(9,false),(5,false),(12,false)])
                        (.node 3384475 ([(3,true),(4,true),(13,true),(6,false),(8,true),(1,true),(11,true)],[(0,true),(9,true),(10,true),(2,true),(7,true),(5,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3385225 ([(4,true),(13,true),(6,false),(9,false),(8,false),(1,true),(11,true)],[(0,true),(7,false),(3,false),(2,false),(10,false),(5,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3385993 ([(2,true),(3,true),(9,true),(0,false),(6,false),(5,false),(12,false)],[(13,false),(4,false),(8,false),(7,false),(1,false),(10,true),(11,true)])
                      (.node 3385969 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(12,false)],[(13,false),(5,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3386065 ([(4,true),(13,true),(6,false),(9,true),(1,true),(2,true),(11,true)],[(0,true),(10,true),(3,true),(7,true),(8,true),(5,false),(12,false)])
                        .empty
                        .empty)))
                  (.node 3388813 ([(1,true),(2,true),(8,true),(6,true),(13,false),(4,false),(11,true)],[(0,true),(7,true),(3,true),(10,false),(9,false),(5,false),(12,false)])
                    (.node 3388345 ([(2,true),(8,false),(5,false),(13,true),(0,true),(10,true),(11,true)],[(6,false),(7,false),(1,false),(9,false),(3,true),(4,true),(12,false)])
                      (.node 3387595 ([(1,true),(8,false),(3,false),(10,false),(6,true),(13,false),(12,false)],[(0,true),(7,true),(4,true),(5,true),(9,false),(2,true),(11,true)])
                        (.node 3387547 ([(2,true),(3,true),(8,true),(0,false),(6,false),(5,false),(12,false)],[(13,false),(4,false),(7,false),(1,false),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3388801 ([(3,true),(10,false),(1,false),(8,true),(6,true),(13,false),(12,false)],[(0,true),(7,false),(2,false),(9,false),(5,false),(4,false),(11,true)])
                        .empty
                        .empty))
                    (.node 3393721 ([(2,true),(3,true),(8,true),(0,false),(6,false),(5,false),(12,false)],[(13,false),(4,false),(7,false),(1,false),(9,true),(10,true),(11,true)])
                      (.node 3393505 ([(3,true),(8,false),(1,true),(10,true),(6,true),(13,false),(12,false)],[(0,true),(7,false),(2,false),(9,false),(4,true),(5,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3463927 ([(5,true),(8,false),(1,false),(0,false),(10,false),(3,false),(12,false)],[(13,false),(2,false),(7,false),(4,false),(9,false),(6,true),(11,true)])
                        .empty
                        .empty))))
                (.node 3474463 ([(6,true),(0,true),(13,false),(2,false),(8,true),(4,true),(11,true)],[(1,true),(7,false),(5,false),(10,false),(9,false),(3,false),(12,false)])
                  (.node 3474007 ([(5,true),(6,true),(8,true),(1,false),(13,false),(3,true),(11,true)],[(0,false),(7,false),(4,false),(10,false),(9,false),(2,true),(12,false)])
                    (.node 3469303 ([(5,true),(6,true),(8,true),(3,false),(13,true),(1,true),(11,true)],[(0,false),(7,false),(4,false),(9,true),(10,true),(2,true),(12,false)])
                      (.node 3468793 ([(6,true),(8,false),(4,true),(10,true),(1,false),(13,false),(12,false)],[(0,false),(9,true),(5,true),(7,true),(3,false),(2,false),(11,true)])
                        (.node 3464101 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(12,false)],[(13,false),(3,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3472111 ([(6,true),(0,true),(1,true),(8,true),(4,false),(3,false),(12,false)],[(13,false),(2,false),(7,false),(5,false),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3474379 ([(6,true),(0,true),(13,false),(2,false),(8,false),(4,true),(11,true)],[(1,true),(9,true),(10,true),(5,true),(7,true),(3,false),(12,false)])
                      (.node 3474037 ([(0,true),(1,true),(8,false),(5,true),(10,true),(3,false),(12,false)],[(13,false),(2,false),(9,true),(6,true),(7,true),(4,false),(11,true)])
                        .empty
                        .empty)
                      (.node 3474391 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(12,false)],[(13,false),(3,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)))
                  (.node 3477583 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(12,false)],[(13,false),(3,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                    (.node 3475255 ([(0,true),(1,true),(10,true),(5,true),(8,false),(3,false),(12,false)],[(13,false),(2,false),(9,false),(6,true),(7,true),(4,true),(11,true)])
                      (.node 3474967 ([(6,true),(0,true),(1,true),(10,true),(4,false),(3,false),(12,false)],[(13,false),(2,false),(9,false),(8,false),(7,false),(5,false),(11,true)])
                        (.node 3474487 ([(2,true),(13,true),(0,false),(6,false),(8,true),(4,true),(11,true)],[(1,true),(7,true),(5,false),(10,false),(9,false),(3,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3477535 ([(5,true),(6,true),(8,true),(9,true),(1,false),(13,false),(12,false)],[(0,false),(7,false),(4,false),(3,false),(2,false),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3478057 ([(2,true),(13,true),(0,false),(8,false),(4,false),(10,true),(11,true)],[(1,true),(7,true),(5,true),(6,true),(9,true),(3,false),(12,false)])
                      (.node 3478039 ([(5,true),(10,false),(9,false),(0,true),(1,true),(2,true),(12,false)],[(13,false),(3,true),(4,true),(7,true),(8,true),(6,false),(11,true)])
                        .empty
                        .empty)
                      (.node 3478123 ([(5,true),(6,true),(0,true),(1,true),(9,true),(3,false),(12,false)],[(13,false),(2,false),(8,false),(7,false),(4,false),(10,true),(11,true)])
                        .empty
                        .empty)))))))
          (.node 3523219 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(12,false)],[(13,false),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
            (.node 3502867 ([(4,true),(13,true),(0,false),(8,true),(9,true),(10,true),(11,true)],[(1,true),(2,true),(3,true),(7,true),(6,false),(5,false),(12,false)])
              (.node 3492103 ([(6,true),(0,true),(1,true),(2,true),(10,true),(4,false),(12,false)],[(13,false),(3,false),(9,false),(8,false),(7,false),(5,false),(11,true)])
                (.node 3486091 ([(0,true),(1,true),(2,true),(9,true),(5,false),(4,false),(12,false)],[(13,false),(3,false),(8,false),(7,false),(6,false),(10,true),(11,true)])
                  (.node 3480907 ([(3,true),(13,true),(1,true),(8,false),(5,false),(10,true),(11,true)],[(0,false),(6,false),(7,false),(2,false),(9,true),(4,false),(12,false)])
                    (.node 3480343 ([(6,true),(0,true),(1,true),(8,true),(9,true),(3,true),(12,false)],[(13,false),(4,true),(5,true),(7,true),(2,true),(10,true),(11,true)])
                      (.node 3480055 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(12,false)],[(13,false),(4,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        (.node 3480007 ([(6,true),(0,true),(1,true),(2,true),(8,true),(4,false),(12,false)],[(13,false),(3,false),(7,false),(5,false),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3480391 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(12,false)],[(13,false),(4,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3485593 ([(5,false),(4,false),(13,true),(0,false),(8,false),(2,false),(11,true)],[(1,true),(10,false),(9,false),(6,false),(7,true),(3,true),(12,false)])
                      (.node 3484123 ([(6,true),(0,true),(1,true),(2,true),(8,true),(4,false),(12,false)],[(13,false),(3,false),(7,false),(5,false),(9,true),(10,true),(11,true)])
                        (.node 3480955 ([(2,true),(8,false),(5,false),(4,false),(13,true),(0,false),(11,true)],[(1,true),(7,true),(6,true),(10,false),(9,false),(3,true),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3486061 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(12,false)],[(13,false),(4,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)))
                  (.node 3491197 ([(3,true),(13,true),(0,false),(9,false),(8,false),(5,false),(11,true)],[(1,true),(2,true),(7,true),(6,true),(10,true),(4,false),(12,false)])
                    (.node 3488413 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(12,false)],[(13,false),(4,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3487987 ([(6,true),(8,false),(1,false),(13,false),(4,true),(10,true),(11,true)],[(0,false),(9,true),(5,true),(7,true),(2,true),(3,true),(12,false)])
                        (.node 3486517 ([(6,true),(0,true),(13,false),(4,true),(8,false),(2,true),(11,true)],[(1,true),(7,false),(5,false),(9,true),(10,true),(3,true),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3488443 ([(0,true),(1,true),(8,false),(5,true),(10,true),(3,true),(12,false)],[(13,false),(4,true),(7,false),(6,false),(9,false),(2,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3491767 ([(6,true),(0,true),(13,false),(3,false),(2,false),(10,true),(11,true)],[(1,true),(9,false),(8,false),(7,false),(5,false),(4,false),(12,false)])
                      (.node 3491245 ([(2,true),(3,true),(13,true),(0,false),(6,false),(5,false),(11,true)],[(1,true),(7,true),(8,true),(9,true),(10,true),(4,false),(12,false)])
                        .empty
                        .empty)
                      (.node 3492055 ([(0,true),(1,true),(2,true),(8,true),(5,false),(4,false),(12,false)],[(13,false),(3,false),(7,false),(6,false),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))))
                (.node 3494743 ([(0,true),(1,true),(2,true),(10,true),(5,false),(4,false),(12,false)],[(13,false),(3,false),(9,false),(8,false),(7,false),(6,false),(11,true)])
                  (.node 3494407 ([(0,true),(1,true),(10,true),(5,false),(8,false),(3,true),(12,false)],[(13,false),(4,true),(9,true),(2,true),(7,false),(6,false),(11,true)])
                    (.node 3494179 ([(3,true),(13,true),(1,true),(9,false),(8,false),(5,true),(11,true)],[(0,false),(6,false),(10,false),(2,true),(7,true),(4,false),(12,false)])
                      (.node 3494167 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(12,false)],[(13,false),(4,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        (.node 3492391 ([(0,true),(1,true),(8,true),(9,true),(10,true),(4,false),(12,false)],[(13,false),(3,false),(2,false),(7,false),(6,false),(5,false),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3494389 ([(3,true),(13,true),(0,false),(8,true),(9,true),(10,true),(11,true)],[(1,true),(2,true),(7,true),(6,false),(5,false),(4,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3494521 ([(2,true),(9,false),(0,true),(13,false),(4,true),(5,true),(11,true)],[(1,true),(7,true),(8,true),(6,false),(10,false),(3,true),(12,false)])
                      (.node 3494503 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(12,false)],[(13,false),(4,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3494731 ([(2,true),(3,true),(13,true),(0,false),(8,true),(5,true),(11,true)],[(1,true),(7,true),(6,false),(10,false),(9,false),(4,false),(12,false)])
                        .empty
                        .empty)))
                  (.node 3500851 ([(4,true),(13,true),(0,false),(6,false),(8,true),(2,false),(11,true)],[(1,true),(10,false),(9,false),(3,true),(7,true),(5,false),(12,false)])
                    (.node 3497209 ([(2,true),(3,true),(8,true),(6,true),(0,true),(13,false),(12,false)],[(1,true),(7,true),(4,true),(5,true),(9,true),(10,true),(11,true)])
                      (.node 3497197 ([(4,true),(13,true),(1,true),(2,true),(9,false),(6,true),(11,true)],[(0,false),(10,false),(3,true),(7,true),(8,true),(5,false),(12,false)])
                        (.node 3496783 ([(3,true),(8,false),(5,false),(13,true),(1,true),(10,true),(11,true)],[(0,false),(6,false),(7,false),(2,false),(9,false),(4,true),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3497371 ([(3,true),(4,true),(13,true),(1,true),(8,false),(6,true),(11,true)],[(0,false),(10,false),(9,false),(2,true),(7,true),(5,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3502057 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(12,false)],[(13,false),(5,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3500899 ([(3,true),(8,false),(5,false),(13,true),(0,false),(10,true),(11,true)],[(1,true),(2,true),(7,true),(6,true),(9,false),(4,true),(12,false)])
                        .empty
                        .empty)
                      (.node 3502345 ([(0,true),(1,true),(2,true),(8,true),(9,true),(4,true),(12,false)],[(13,false),(5,true),(6,true),(7,true),(3,true),(10,true),(11,true)])
                        .empty
                        .empty)))))
              (.node 3511321 ([(2,true),(3,true),(4,true),(13,true),(0,false),(6,false),(11,true)],[(1,true),(7,true),(8,true),(9,true),(10,true),(5,false),(12,false)])
                (.node 3505327 ([(0,true),(1,true),(2,true),(3,true),(9,true),(5,false),(12,false)],[(13,false),(4,false),(8,false),(7,false),(6,false),(10,true),(11,true)])
                  (.node 3503299 ([(2,true),(3,true),(8,false),(6,true),(0,true),(13,false),(12,false)],[(1,true),(7,true),(5,false),(4,false),(9,true),(10,true),(11,true)])
                    (.node 3503203 ([(4,true),(13,true),(0,false),(6,false),(8,true),(2,true),(11,true)],[(1,true),(9,true),(10,true),(3,true),(7,true),(5,false),(12,false)])
                      (.node 3503191 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(12,false)],[(13,false),(5,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        (.node 3502915 ([(3,true),(4,true),(13,true),(0,false),(6,false),(10,true),(11,true)],[(1,true),(2,true),(7,true),(8,true),(9,true),(5,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3503275 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(12,false)],[(13,false),(5,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3505243 ([(0,true),(1,true),(8,false),(3,false),(10,false),(5,false),(12,false)],[(13,false),(4,false),(7,false),(6,false),(9,false),(2,true),(11,true)])
                      (.node 3505219 ([(4,true),(13,true),(0,false),(6,false),(9,false),(2,true),(11,true)],[(1,true),(8,false),(7,false),(3,false),(10,false),(5,false),(12,false)])
                        .empty
                        .empty)
                      (.node 3505315 ([(2,true),(3,true),(9,true),(6,true),(0,true),(13,false),(12,false)],[(1,true),(7,true),(8,true),(4,true),(5,true),(10,true),(11,true)])
                        .empty
                        .empty)))
                  (.node 3507619 ([(3,true),(10,false),(6,true),(8,true),(1,false),(13,false),(12,false)],[(0,false),(7,false),(2,false),(9,true),(5,false),(4,false),(11,true)])
                    (.node 3506173 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(12,false)],[(13,false),(5,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3505651 ([(2,true),(8,false),(5,false),(13,true),(0,false),(10,true),(11,true)],[(1,true),(7,true),(6,true),(9,false),(3,true),(4,true),(12,false)])
                        (.node 3505603 ([(3,true),(10,false),(6,false),(8,true),(1,false),(13,false),(12,false)],[(0,false),(9,false),(2,true),(7,true),(5,false),(4,false),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3506461 ([(0,true),(1,true),(9,false),(8,false),(3,true),(4,true),(12,false)],[(13,false),(5,true),(6,true),(7,true),(2,false),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3511147 ([(3,true),(8,false),(6,false),(10,false),(1,false),(13,false),(12,false)],[(0,false),(7,false),(2,false),(9,false),(4,true),(5,true),(11,true)])
                      (.node 3507667 ([(2,true),(3,true),(10,false),(6,true),(0,true),(13,false),(12,false)],[(1,true),(7,true),(8,true),(9,true),(5,false),(4,false),(11,true)])
                        .empty
                        .empty)
                      (.node 3511309 ([(4,true),(13,true),(0,false),(8,false),(2,true),(10,true),(11,true)],[(1,true),(7,false),(3,false),(9,false),(6,false),(5,false),(12,false)])
                        .empty
                        .empty))))
                (.node 3521599 ([(4,true),(5,true),(13,true),(0,false),(8,false),(2,true),(11,true)],[(1,true),(7,false),(3,false),(10,false),(9,false),(6,false),(12,false)])
                  (.node 3518875 ([(3,true),(4,true),(8,true),(6,false),(13,true),(1,true),(11,true)],[(0,false),(9,true),(10,true),(2,true),(7,true),(5,true),(12,false)])
                    (.node 3514171 ([(3,true),(4,true),(8,true),(1,false),(0,false),(6,false),(12,false)],[(13,false),(5,false),(7,false),(2,false),(9,true),(10,true),(11,true)])
                      (.node 3513955 ([(4,true),(8,false),(2,true),(10,true),(0,true),(13,false),(12,false)],[(1,true),(7,false),(3,false),(9,false),(5,true),(6,true),(11,true)])
                        (.node 3511735 ([(3,true),(4,true),(13,true),(1,true),(8,false),(6,false),(11,true)],[(0,false),(7,false),(2,false),(9,true),(10,true),(5,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3518863 ([(5,true),(13,true),(0,false),(8,false),(3,true),(10,true),(11,true)],[(1,true),(2,true),(7,false),(4,false),(9,false),(6,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3520081 ([(5,true),(13,true),(0,false),(9,false),(8,false),(2,true),(11,true)],[(1,true),(7,false),(4,false),(3,false),(10,false),(6,false),(12,false)])
                      (.node 3519331 ([(4,true),(5,true),(13,true),(0,false),(8,true),(2,false),(11,true)],[(1,true),(10,false),(9,false),(3,true),(7,true),(6,false),(12,false)])
                        .empty
                        .empty)
                      (.node 3520129 ([(4,true),(9,true),(6,false),(13,true),(1,true),(2,true),(11,true)],[(0,false),(10,true),(3,true),(7,true),(8,true),(5,true),(12,false)])
                        .empty
                        .empty)))
                  (.node 3522451 ([(2,true),(8,false),(4,false),(10,false),(0,true),(13,false),(12,false)],[(1,true),(7,true),(5,true),(6,true),(9,false),(3,true),(11,true)])
                    (.node 3521707 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(12,false)],[(13,false),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3521683 ([(4,true),(5,true),(13,true),(0,false),(8,true),(2,true),(11,true)],[(1,true),(9,true),(10,true),(3,true),(7,true),(6,false),(12,false)])
                        (.node 3521611 ([(2,true),(3,true),(4,true),(9,false),(0,true),(13,false),(12,false)],[(1,true),(7,true),(8,true),(6,false),(5,false),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3522403 ([(3,true),(4,true),(8,true),(1,false),(0,false),(6,false),(12,false)],[(13,false),(5,false),(7,false),(2,false),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3522991 ([(3,true),(4,true),(8,true),(9,true),(1,false),(13,false),(12,false)],[(0,false),(6,false),(5,false),(7,false),(2,false),(10,true),(11,true)])
                      (.node 3522979 ([(5,true),(13,true),(0,false),(9,true),(2,true),(3,true),(11,true)],[(1,true),(10,true),(4,true),(7,true),(8,true),(6,false),(12,false)])
                        .empty
                        .empty)
                      (.node 3523201 ([(3,true),(4,true),(9,true),(1,false),(0,false),(6,false),(12,false)],[(13,false),(5,false),(8,false),(7,false),(2,false),(10,true),(11,true)])
                        .empty
                        .empty))))))
            (.node 3609361 ([(0,true),(1,true),(2,true),(8,true),(5,false),(4,false),(12,false)],[(13,false),(3,false),(7,false),(6,false),(9,true),(10,true),(11,true)])
              (.node 3542809 ([(4,true),(5,true),(9,true),(2,false),(1,false),(0,false),(12,false)],[(13,false),(6,false),(8,false),(7,false),(3,false),(10,true),(11,true)])
                (.node 3539737 ([(5,true),(9,true),(0,false),(13,true),(2,true),(3,true),(11,true)],[(1,false),(10,true),(4,true),(7,true),(8,true),(6,true),(12,false)])
                  (.node 3533779 ([(4,true),(5,true),(8,true),(2,false),(1,false),(0,false),(12,false)],[(13,false),(6,false),(7,false),(3,false),(9,true),(10,true),(11,true)])
                    (.node 3525727 ([(2,true),(3,true),(8,true),(0,true),(13,false),(5,false),(11,true)],[(1,true),(7,true),(4,true),(10,false),(9,false),(6,false),(12,false)])
                      (.node 3525715 ([(4,true),(10,false),(2,false),(8,true),(0,true),(13,false),(12,false)],[(1,true),(7,false),(3,false),(9,false),(6,false),(5,false),(11,true)])
                        (.node 3525553 ([(3,true),(8,false),(6,false),(13,true),(1,true),(10,true),(11,true)],[(0,false),(7,false),(2,false),(9,false),(4,true),(5,true),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3533563 ([(5,true),(8,false),(3,true),(10,true),(1,true),(13,false),(12,false)],[(2,true),(7,false),(4,false),(9,false),(6,true),(0,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3538939 ([(5,true),(6,true),(13,true),(1,false),(8,true),(3,false),(11,true)],[(2,true),(10,false),(9,false),(4,true),(7,true),(0,false),(12,false)])
                      (.node 3538483 ([(4,true),(5,true),(8,true),(0,false),(13,true),(2,true),(11,true)],[(1,false),(9,true),(10,true),(3,true),(7,true),(6,true),(12,false)])
                        (.node 3538471 ([(6,true),(13,true),(1,false),(8,false),(4,true),(10,true),(11,true)],[(2,true),(3,true),(7,false),(5,false),(9,false),(0,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3539689 ([(6,true),(13,true),(1,false),(9,false),(8,false),(3,true),(11,true)],[(2,true),(7,false),(5,false),(4,false),(10,false),(0,false),(12,false)])
                        .empty
                        .empty)))
                  (.node 3542011 ([(4,true),(5,true),(8,true),(2,false),(1,false),(0,false),(12,false)],[(13,false),(6,false),(7,false),(3,false),(9,true),(10,true),(11,true)])
                    (.node 3541291 ([(5,true),(6,true),(13,true),(1,false),(8,true),(3,true),(11,true)],[(2,true),(9,true),(10,true),(4,true),(7,true),(0,false),(12,false)])
                      (.node 3541219 ([(3,true),(4,true),(5,true),(9,false),(1,true),(13,false),(12,false)],[(2,true),(7,true),(8,true),(0,false),(6,false),(10,true),(11,true)])
                        (.node 3541207 ([(5,true),(6,true),(13,true),(1,false),(8,false),(3,true),(11,true)],[(2,true),(7,false),(4,false),(10,false),(9,false),(0,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3541315 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(12,false)],[(13,false),(0,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3542587 ([(6,true),(13,true),(1,false),(9,true),(3,true),(4,true),(11,true)],[(2,true),(10,true),(5,true),(7,true),(8,true),(0,false),(12,false)])
                      (.node 3542059 ([(3,true),(8,false),(5,false),(10,false),(1,true),(13,false),(12,false)],[(2,true),(7,true),(6,true),(0,true),(9,false),(4,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3542599 ([(4,true),(5,true),(8,true),(9,true),(2,false),(13,false),(12,false)],[(1,false),(0,false),(6,false),(7,false),(3,false),(10,true),(11,true)])
                        .empty
                        .empty))))
                (.node 3598573 ([(6,true),(0,true),(1,true),(2,true),(9,true),(4,false),(12,false)],[(13,false),(3,false),(8,false),(7,false),(5,false),(10,true),(11,true)])
                  (.node 3597985 ([(6,true),(0,true),(8,true),(9,true),(2,false),(13,false),(12,false)],[(1,false),(7,false),(5,false),(4,false),(3,false),(10,true),(11,true)])
                    (.node 3545323 ([(5,true),(10,false),(3,false),(8,true),(1,true),(13,false),(12,false)],[(2,true),(7,false),(4,false),(9,false),(0,false),(6,false),(11,true)])
                      (.node 3545161 ([(4,true),(8,false),(0,false),(13,true),(2,true),(10,true),(11,true)],[(1,false),(7,false),(3,false),(9,false),(5,true),(6,true),(12,false)])
                        (.node 3542827 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(12,false)],[(13,false),(0,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3545335 ([(3,true),(4,true),(8,true),(1,true),(13,false),(6,false),(11,true)],[(2,true),(7,true),(5,true),(10,false),(9,false),(0,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3598489 ([(6,true),(10,false),(9,false),(1,true),(2,true),(3,true),(12,false)],[(13,false),(4,true),(5,true),(7,true),(8,true),(0,false),(11,true)])
                      (.node 3598033 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(12,false)],[(13,false),(4,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3598507 ([(3,true),(13,true),(1,false),(8,false),(5,false),(10,true),(11,true)],[(2,true),(7,true),(6,true),(0,true),(9,true),(4,false),(12,false)])
                        .empty
                        .empty)))
                  (.node 3604159 ([(6,true),(0,true),(8,true),(4,false),(13,true),(2,true),(11,true)],[(1,false),(7,false),(5,false),(9,true),(10,true),(3,true),(12,false)])
                    (.node 3601309 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(12,false)],[(13,false),(4,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3600841 ([(6,true),(8,false),(2,false),(1,false),(10,false),(4,false),(12,false)],[(13,false),(3,false),(7,false),(5,false),(9,false),(0,true),(11,true)])
                        (.node 3598603 ([(1,true),(2,true),(8,false),(6,true),(10,false),(4,false),(12,false)],[(13,false),(3,false),(9,true),(5,true),(7,false),(0,false),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3601339 ([(0,true),(1,true),(2,true),(9,true),(5,false),(4,false),(12,false)],[(13,false),(3,false),(8,false),(7,false),(6,false),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3608863 ([(6,true),(0,true),(8,true),(2,false),(13,false),(4,true),(11,true)],[(1,false),(7,false),(5,false),(10,false),(9,false),(3,true),(12,false)])
                      (.node 3606043 ([(0,true),(8,false),(5,true),(10,true),(2,false),(13,false),(12,false)],[(1,false),(9,true),(6,true),(7,true),(4,false),(3,false),(11,true)])
                        .empty
                        .empty)
                      (.node 3608893 ([(1,true),(2,true),(8,false),(6,true),(10,true),(4,false),(12,false)],[(13,false),(3,false),(9,true),(0,true),(7,true),(5,false),(11,true)])
                        .empty
                        .empty)))))
              (.node 3617593 ([(0,true),(1,true),(2,true),(8,true),(9,true),(4,true),(12,false)],[(13,false),(5,true),(6,true),(7,true),(3,true),(10,true),(11,true)])
                (.node 3614839 ([(4,true),(13,true),(1,false),(8,true),(9,true),(10,true),(11,true)],[(2,true),(3,true),(7,true),(0,false),(6,false),(5,false),(12,false)])
                  (.node 3612169 ([(1,true),(2,true),(10,true),(6,true),(8,false),(4,false),(12,false)],[(13,false),(3,false),(9,false),(0,true),(7,true),(5,true),(11,true)])
                    (.node 3611695 ([(3,true),(13,true),(1,false),(0,false),(8,true),(5,true),(11,true)],[(2,true),(7,true),(6,false),(10,false),(9,false),(4,false),(12,false)])
                      (.node 3611629 ([(0,true),(1,true),(13,false),(3,false),(8,false),(5,true),(11,true)],[(2,true),(9,true),(10,true),(6,true),(7,true),(4,false),(12,false)])
                        (.node 3611599 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(12,false)],[(13,false),(4,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3611713 ([(0,true),(1,true),(13,false),(3,false),(8,true),(5,true),(11,true)],[(2,true),(7,false),(6,false),(10,false),(9,false),(4,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3614617 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(12,false)],[(13,false),(5,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3612217 ([(0,true),(1,true),(2,true),(10,true),(5,false),(4,false),(12,false)],[(13,false),(3,false),(9,false),(8,false),(7,false),(6,false),(11,true)])
                        .empty
                        .empty)
                      (.node 3614629 ([(4,true),(13,true),(2,true),(9,false),(8,false),(6,true),(11,true)],[(1,false),(0,false),(10,false),(3,true),(7,true),(5,false),(12,false)])
                        .empty
                        .empty)))
                  (.node 3615193 ([(1,true),(2,true),(3,true),(10,true),(6,false),(5,false),(12,false)],[(13,false),(4,false),(9,false),(8,false),(7,false),(0,false),(11,true)])
                    (.node 3614971 ([(3,true),(9,false),(1,true),(13,false),(5,true),(6,true),(11,true)],[(2,true),(7,true),(8,true),(0,false),(10,false),(4,true),(12,false)])
                      (.node 3614953 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(12,false)],[(13,false),(5,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        (.node 3614857 ([(1,true),(2,true),(10,true),(6,false),(8,false),(4,true),(12,false)],[(13,false),(5,true),(9,true),(3,true),(7,false),(0,false),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3615181 ([(3,true),(4,true),(13,true),(1,false),(8,true),(6,true),(11,true)],[(2,true),(7,true),(0,false),(10,false),(9,false),(5,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3617257 ([(0,true),(1,true),(2,true),(3,true),(8,true),(5,false),(12,false)],[(13,false),(4,false),(7,false),(6,false),(9,true),(10,true),(11,true)])
                      (.node 3616969 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(12,false)],[(13,false),(5,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3617305 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(12,false)],[(13,false),(5,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))))
                (.node 3623767 ([(0,true),(1,true),(13,false),(5,true),(8,false),(3,true),(11,true)],[(2,true),(7,false),(6,false),(9,true),(10,true),(4,true),(12,false)])
                  (.node 3621373 ([(0,true),(1,true),(2,true),(3,true),(8,true),(5,false),(12,false)],[(13,false),(4,false),(7,false),(6,false),(9,true),(10,true),(11,true)])
                    (.node 3620917 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(12,false)],[(13,false),(5,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3618163 ([(3,true),(8,false),(6,false),(5,false),(13,true),(1,false),(11,true)],[(2,true),(7,true),(0,true),(10,false),(9,false),(4,true),(12,false)])
                        (.node 3618115 ([(4,true),(13,true),(2,true),(8,false),(6,false),(10,true),(11,true)],[(1,false),(0,false),(7,false),(3,false),(9,true),(5,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3620947 ([(1,true),(2,true),(3,true),(9,true),(6,false),(5,false),(12,false)],[(13,false),(4,false),(8,false),(7,false),(0,false),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3623269 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(12,false)],[(13,false),(5,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3622843 ([(6,false),(5,false),(13,true),(1,false),(8,false),(3,false),(11,true)],[(2,true),(10,false),(9,false),(0,false),(7,true),(4,true),(12,false)])
                        .empty
                        .empty)
                      (.node 3623299 ([(1,true),(2,true),(8,false),(6,true),(10,true),(4,true),(12,false)],[(13,false),(5,true),(7,false),(0,false),(9,false),(3,true),(11,true)])
                        .empty
                        .empty)))
                  (.node 3629017 ([(0,true),(1,true),(13,false),(4,false),(3,false),(10,true),(11,true)],[(2,true),(9,false),(8,false),(7,false),(6,false),(5,false),(12,false)])
                    (.node 3628453 ([(3,true),(4,true),(13,true),(1,false),(0,false),(6,false),(11,true)],[(2,true),(7,true),(8,true),(9,true),(10,true),(5,false),(12,false)])
                      (.node 3628405 ([(4,true),(13,true),(1,false),(9,false),(8,false),(6,false),(11,true)],[(2,true),(3,true),(7,true),(0,true),(10,true),(5,false),(12,false)])
                        (.node 3625237 ([(0,true),(8,false),(2,false),(13,false),(5,true),(10,true),(11,true)],[(1,false),(9,true),(6,true),(7,true),(3,true),(4,true),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3628969 ([(1,true),(2,true),(3,true),(8,true),(6,false),(5,false),(12,false)],[(13,false),(4,false),(7,false),(0,false),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3629353 ([(0,true),(1,true),(2,true),(3,true),(10,true),(5,false),(12,false)],[(13,false),(4,false),(9,false),(8,false),(7,false),(6,false),(11,true)])
                      (.node 3629305 ([(1,true),(2,true),(8,true),(9,true),(10,true),(5,false),(12,false)],[(13,false),(4,false),(3,false),(7,false),(0,false),(6,false),(11,true)])
                        .empty
                        .empty)
                      (.node 3631597 ([(4,true),(8,false),(0,false),(10,false),(2,false),(13,false),(12,false)],[(1,false),(7,false),(3,false),(9,false),(5,true),(6,true),(11,true)])
                        .empty
                        .empty))))))))
        (.node 3777895 ([(2,true),(3,true),(4,true),(5,true),(8,true),(0,false),(12,false)],[(13,false),(6,false),(7,false),(1,false),(9,true),(10,true),(11,true)])
          (.node 3679807 ([(5,true),(6,true),(8,true),(9,true),(3,false),(13,false),(12,false)],[(2,false),(1,false),(0,false),(7,false),(4,false),(10,true),(11,true)])
            (.node 3657667 ([(6,true),(13,true),(2,false),(1,false),(8,true),(4,false),(11,true)],[(3,true),(10,false),(9,false),(5,true),(7,true),(0,false),(12,false)])
              (.node 3640507 ([(3,true),(4,true),(8,false),(0,true),(1,true),(13,false),(12,false)],[(2,true),(7,true),(6,false),(5,false),(9,true),(10,true),(11,true)])
                (.node 3638107 ([(4,true),(8,false),(6,false),(13,true),(1,false),(10,true),(11,true)],[(2,true),(3,true),(7,true),(0,true),(9,false),(5,true),(12,false)])
                  (.node 3634123 ([(3,true),(4,true),(8,true),(0,true),(1,true),(13,false),(12,false)],[(2,true),(7,true),(5,true),(6,true),(9,true),(10,true),(11,true)])
                    (.node 3633991 ([(4,true),(8,false),(6,false),(13,true),(2,true),(10,true),(11,true)],[(1,false),(0,false),(7,false),(3,false),(9,false),(5,true),(12,false)])
                      (.node 3632185 ([(4,true),(5,true),(13,true),(2,true),(8,false),(0,false),(11,true)],[(1,false),(7,false),(3,false),(9,true),(10,true),(6,false),(12,false)])
                        (.node 3631771 ([(3,true),(4,true),(5,true),(13,true),(1,false),(0,false),(11,true)],[(2,true),(7,true),(8,true),(9,true),(10,true),(6,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3634111 ([(5,true),(13,true),(2,true),(3,true),(9,false),(0,true),(11,true)],[(1,false),(10,false),(4,true),(7,true),(8,true),(6,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3637771 ([(4,true),(5,true),(13,true),(1,false),(0,false),(10,true),(11,true)],[(2,true),(3,true),(7,true),(8,true),(9,true),(6,false),(12,false)])
                      (.node 3637723 ([(5,true),(13,true),(1,false),(8,true),(9,true),(10,true),(11,true)],[(2,true),(3,true),(4,true),(7,true),(0,false),(6,false),(12,false)])
                        (.node 3634579 ([(4,true),(5,true),(13,true),(2,true),(8,false),(0,true),(11,true)],[(1,false),(10,false),(9,false),(3,true),(7,true),(6,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3638059 ([(5,true),(13,true),(1,false),(0,false),(8,true),(3,false),(11,true)],[(2,true),(10,false),(9,false),(4,true),(7,true),(6,false),(12,false)])
                        .empty
                        .empty)))
                  (.node 3640171 ([(3,true),(4,true),(9,true),(0,true),(1,true),(13,false),(12,false)],[(2,true),(7,true),(8,true),(5,true),(6,true),(10,true),(11,true)])
                    (.node 3640075 ([(5,true),(13,true),(1,false),(0,false),(9,false),(3,true),(11,true)],[(2,true),(8,false),(7,false),(4,false),(10,false),(6,false),(12,false)])
                      (.node 3639307 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(12,false)],[(13,false),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        (.node 3639259 ([(1,true),(2,true),(3,true),(8,true),(9,true),(5,true),(12,false)],[(13,false),(6,true),(0,true),(7,true),(4,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3640099 ([(1,true),(2,true),(8,false),(4,false),(10,false),(6,false),(12,false)],[(13,false),(5,false),(7,false),(0,false),(9,false),(3,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3640411 ([(5,true),(13,true),(1,false),(0,false),(8,true),(3,true),(11,true)],[(2,true),(9,true),(10,true),(4,true),(7,true),(6,false),(12,false)])
                      (.node 3640183 ([(1,true),(2,true),(3,true),(4,true),(9,true),(6,false),(12,false)],[(13,false),(5,false),(8,false),(7,false),(0,false),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3640441 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(12,false)],[(13,false),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))))
                (.node 3651367 ([(6,true),(13,true),(2,false),(8,false),(4,true),(10,true),(11,true)],[(3,true),(7,false),(5,false),(9,false),(1,false),(0,false),(12,false)])
                  (.node 3642859 ([(3,true),(8,false),(6,false),(13,true),(1,false),(10,true),(11,true)],[(2,true),(7,true),(0,true),(9,false),(4,true),(5,true),(12,false)])
                    (.node 3642523 ([(3,true),(4,true),(10,false),(0,true),(1,true),(13,false),(12,false)],[(2,true),(7,true),(8,true),(9,true),(6,false),(5,false),(11,true)])
                      (.node 3642475 ([(4,true),(10,false),(0,true),(8,true),(2,false),(13,false),(12,false)],[(1,false),(7,false),(3,false),(9,true),(6,false),(5,false),(11,true)])
                        (.node 3640525 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(12,false)],[(13,false),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3642811 ([(4,true),(10,false),(0,false),(8,true),(2,false),(13,false),(12,false)],[(1,false),(9,false),(3,true),(7,true),(6,false),(5,false),(11,true)])
                        .empty
                        .empty))
                    (.node 3643423 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(12,false)],[(13,false),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3643375 ([(1,true),(2,true),(9,false),(8,false),(4,true),(5,true),(12,false)],[(13,false),(6,true),(0,true),(7,true),(3,false),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3651205 ([(5,true),(8,false),(1,false),(10,false),(3,false),(13,false),(12,false)],[(2,false),(7,false),(4,false),(9,false),(6,true),(0,true),(11,true)])
                        .empty
                        .empty)))
                  (.node 3653731 ([(4,true),(5,true),(8,true),(1,true),(2,true),(13,false),(12,false)],[(3,true),(7,true),(6,true),(0,true),(9,true),(10,true),(11,true)])
                    (.node 3653599 ([(5,true),(8,false),(0,false),(13,true),(3,true),(10,true),(11,true)],[(2,false),(1,false),(7,false),(4,false),(9,false),(6,true),(12,false)])
                      (.node 3651793 ([(5,true),(6,true),(13,true),(3,true),(8,false),(1,false),(11,true)],[(2,false),(7,false),(4,false),(9,true),(10,true),(0,false),(12,false)])
                        (.node 3651379 ([(4,true),(5,true),(6,true),(13,true),(2,false),(1,false),(11,true)],[(3,true),(7,true),(8,true),(9,true),(10,true),(0,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3653719 ([(6,true),(13,true),(3,true),(4,true),(9,false),(1,true),(11,true)],[(2,false),(10,false),(5,true),(7,true),(8,true),(0,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3657331 ([(6,true),(13,true),(2,false),(8,true),(9,true),(10,true),(11,true)],[(3,true),(4,true),(5,true),(7,true),(1,false),(0,false),(12,false)])
                      (.node 3654187 ([(5,true),(6,true),(13,true),(3,true),(8,false),(1,true),(11,true)],[(2,false),(10,false),(9,false),(4,true),(7,true),(0,false),(12,false)])
                        .empty
                        .empty)
                      (.node 3657379 ([(5,true),(6,true),(13,true),(2,false),(1,false),(10,true),(11,true)],[(3,true),(4,true),(7,true),(8,true),(9,true),(0,false),(12,false)])
                        .empty
                        .empty)))))
              (.node 3665611 ([(5,true),(8,false),(1,false),(13,true),(3,true),(10,true),(11,true)],[(2,false),(7,false),(4,false),(9,false),(6,true),(0,true),(12,false)])
                (.node 3660049 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(12,false)],[(13,false),(0,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                  (.node 3659707 ([(2,true),(3,true),(8,false),(5,false),(10,false),(0,false),(12,false)],[(13,false),(6,false),(7,false),(1,false),(9,false),(4,true),(11,true)])
                    (.node 3658915 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(12,false)],[(13,false),(0,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3658867 ([(2,true),(3,true),(4,true),(8,true),(9,true),(6,true),(12,false)],[(13,false),(0,true),(1,true),(7,true),(5,true),(10,true),(11,true)])
                        (.node 3657715 ([(5,true),(8,false),(0,false),(13,true),(2,false),(10,true),(11,true)],[(3,true),(4,true),(7,true),(1,true),(9,false),(6,true),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3659683 ([(6,true),(13,true),(2,false),(1,false),(9,false),(4,true),(11,true)],[(3,true),(8,false),(7,false),(5,false),(10,false),(0,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3659791 ([(2,true),(3,true),(4,true),(5,true),(9,true),(0,false),(12,false)],[(13,false),(6,false),(8,false),(7,false),(1,false),(10,true),(11,true)])
                      (.node 3659779 ([(4,true),(5,true),(9,true),(1,true),(2,true),(13,false),(12,false)],[(3,true),(7,true),(8,true),(6,true),(0,true),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3660019 ([(6,true),(13,true),(2,false),(1,false),(8,true),(4,true),(11,true)],[(3,true),(9,true),(10,true),(5,true),(7,true),(0,false),(12,false)])
                        .empty
                        .empty)))
                  (.node 3662419 ([(5,true),(10,false),(1,false),(8,true),(3,false),(13,false),(12,false)],[(2,false),(9,false),(4,true),(7,true),(0,false),(6,false),(11,true)])
                    (.node 3662083 ([(5,true),(10,false),(1,true),(8,true),(3,false),(13,false),(12,false)],[(2,false),(7,false),(4,false),(9,true),(0,false),(6,false),(11,true)])
                      (.node 3660133 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(12,false)],[(13,false),(0,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        (.node 3660115 ([(4,true),(5,true),(8,false),(1,true),(2,true),(13,false),(12,false)],[(3,true),(7,true),(0,false),(6,false),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3662131 ([(4,true),(5,true),(10,false),(1,true),(2,true),(13,false),(12,false)],[(3,true),(7,true),(8,true),(9,true),(0,false),(6,false),(11,true)])
                        .empty
                        .empty))
                    (.node 3662983 ([(2,true),(3,true),(9,false),(8,false),(5,true),(6,true),(12,false)],[(13,false),(0,true),(1,true),(7,true),(4,false),(10,true),(11,true)])
                      (.node 3662467 ([(4,true),(8,false),(0,false),(13,true),(2,false),(10,true),(11,true)],[(3,true),(7,true),(1,true),(9,false),(5,true),(6,true),(12,false)])
                        .empty
                        .empty)
                      (.node 3663031 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(12,false)],[(13,false),(0,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))))
                (.node 3676075 ([(4,true),(5,true),(6,true),(9,false),(2,true),(13,false),(12,false)],[(3,true),(7,true),(8,true),(1,false),(0,false),(10,true),(11,true)])
                  (.node 3673795 ([(6,true),(0,true),(13,true),(2,false),(8,true),(4,false),(11,true)],[(3,true),(10,false),(9,false),(5,true),(7,true),(1,false),(12,false)])
                    (.node 3670477 ([(6,true),(8,false),(4,true),(10,true),(2,true),(13,false),(12,false)],[(3,true),(7,false),(5,false),(9,false),(0,true),(1,true),(11,true)])
                      (.node 3665785 ([(4,true),(5,true),(8,true),(2,true),(13,false),(0,false),(11,true)],[(3,true),(7,true),(6,true),(10,false),(9,false),(1,false),(12,false)])
                        (.node 3665773 ([(6,true),(10,false),(4,false),(8,true),(2,true),(13,false),(12,false)],[(3,true),(7,false),(5,false),(9,false),(1,false),(0,false),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3670987 ([(5,true),(6,true),(8,true),(3,false),(2,false),(1,false),(12,false)],[(13,false),(0,false),(7,false),(4,false),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3675721 ([(0,true),(13,true),(2,false),(8,false),(5,true),(10,true),(11,true)],[(3,true),(4,true),(7,false),(6,false),(9,false),(1,false),(12,false)])
                      (.node 3675691 ([(5,true),(6,true),(8,true),(1,false),(13,true),(3,true),(11,true)],[(2,false),(9,true),(10,true),(4,true),(7,true),(0,true),(12,false)])
                        .empty
                        .empty)
                      (.node 3676063 ([(6,true),(0,true),(13,true),(2,false),(8,false),(4,true),(11,true)],[(3,true),(7,false),(5,false),(10,false),(9,false),(1,false),(12,false)])
                        .empty
                        .empty)))
                  (.node 3679219 ([(5,true),(6,true),(8,true),(3,false),(2,false),(1,false),(12,false)],[(13,false),(0,false),(7,false),(4,false),(9,true),(10,true),(11,true)])
                    (.node 3676651 ([(6,true),(9,true),(1,false),(13,true),(3,true),(4,true),(11,true)],[(2,false),(10,true),(5,true),(7,true),(8,true),(0,true),(12,false)])
                      (.node 3676171 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(12,false)],[(13,false),(1,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        (.node 3676147 ([(6,true),(0,true),(13,true),(2,false),(8,true),(4,true),(11,true)],[(3,true),(9,true),(10,true),(5,true),(7,true),(1,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3676939 ([(0,true),(13,true),(2,false),(9,false),(8,false),(4,true),(11,true)],[(3,true),(7,false),(6,false),(5,false),(10,false),(1,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3679723 ([(5,true),(6,true),(9,true),(3,false),(2,false),(1,false),(12,false)],[(13,false),(0,false),(8,false),(7,false),(4,false),(10,true),(11,true)])
                      (.node 3679267 ([(4,true),(8,false),(6,false),(10,false),(2,true),(13,false),(12,false)],[(3,true),(7,true),(0,true),(1,true),(9,false),(5,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3679741 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(12,false)],[(13,false),(1,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))))))
            (.node 3753019 ([(4,true),(8,false),(0,false),(6,false),(13,true),(2,false),(11,true)],[(3,true),(7,true),(1,true),(10,false),(9,false),(5,true),(12,false)])
              (.node 3746101 ([(2,true),(3,true),(8,false),(0,true),(10,true),(5,false),(12,false)],[(13,false),(4,false),(9,true),(1,true),(7,true),(6,false),(11,true)])
                (.node 3735715 ([(4,true),(13,true),(2,false),(8,false),(6,false),(10,true),(11,true)],[(3,true),(7,true),(0,true),(1,true),(9,true),(5,false),(12,false)])
                  (.node 3732163 ([(1,true),(2,true),(13,false),(4,false),(8,true),(6,true),(11,true)],[(3,true),(7,false),(0,false),(10,false),(9,false),(5,false),(12,false)])
                    (.node 3732079 ([(1,true),(2,true),(13,false),(4,false),(8,false),(6,true),(11,true)],[(3,true),(9,true),(10,true),(0,true),(7,true),(5,false),(12,false)])
                      (.node 3732049 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(12,false)],[(13,false),(5,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        (.node 3679837 ([(0,true),(13,true),(2,false),(9,true),(4,true),(5,true),(11,true)],[(3,true),(10,true),(6,true),(7,true),(8,true),(1,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3732145 ([(4,true),(13,true),(2,false),(1,false),(8,true),(6,true),(11,true)],[(3,true),(7,true),(0,false),(10,false),(9,false),(5,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3734947 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(12,false)],[(13,false),(5,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3732667 ([(1,true),(2,true),(3,true),(10,true),(6,false),(5,false),(12,false)],[(13,false),(4,false),(9,false),(8,false),(7,false),(0,false),(11,true)])
                        (.node 3732619 ([(2,true),(3,true),(10,true),(0,true),(8,false),(5,false),(12,false)],[(13,false),(4,false),(9,false),(1,true),(7,true),(6,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3735235 ([(0,true),(1,true),(8,true),(9,true),(3,false),(13,false),(12,false)],[(2,false),(7,false),(6,false),(5,false),(4,false),(10,true),(11,true)])
                        .empty
                        .empty)))
                  (.node 3736195 ([(1,true),(2,true),(3,true),(9,true),(6,false),(5,false),(12,false)],[(13,false),(4,false),(8,false),(7,false),(0,false),(10,true),(11,true)])
                    (.node 3735823 ([(0,true),(1,true),(2,true),(3,true),(9,true),(5,false),(12,false)],[(13,false),(4,false),(8,false),(7,false),(6,false),(10,true),(11,true)])
                      (.node 3735811 ([(2,true),(3,true),(8,false),(0,true),(10,false),(5,false),(12,false)],[(13,false),(4,false),(9,true),(6,true),(7,false),(1,false),(11,true)])
                        (.node 3735739 ([(0,true),(10,false),(9,false),(2,true),(3,true),(4,true),(12,false)],[(13,false),(5,true),(6,true),(7,true),(8,true),(1,false),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3736165 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(12,false)],[(13,false),(5,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3740899 ([(1,true),(8,false),(6,true),(10,true),(3,false),(13,false),(12,false)],[(2,false),(9,true),(0,true),(7,true),(5,false),(4,false),(11,true)])
                      (.node 3738091 ([(0,true),(8,false),(3,false),(2,false),(10,false),(5,false),(12,false)],[(13,false),(4,false),(7,false),(6,false),(9,false),(1,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3741409 ([(0,true),(1,true),(8,true),(5,false),(13,true),(3,true),(11,true)],[(2,false),(7,false),(6,false),(9,true),(10,true),(4,true),(12,false)])
                        .empty
                        .empty))))
                (.node 3751753 ([(5,true),(13,true),(2,false),(8,true),(9,true),(10,true),(11,true)],[(3,true),(4,true),(7,true),(1,false),(0,false),(6,false),(12,false)])
                  (.node 3749419 ([(2,true),(3,true),(4,true),(8,true),(0,false),(6,false),(12,false)],[(13,false),(5,false),(7,false),(1,false),(9,true),(10,true),(11,true)])
                    (.node 3748855 ([(5,true),(13,true),(2,false),(9,false),(8,false),(0,false),(11,true)],[(3,true),(4,true),(7,true),(1,true),(10,true),(6,false),(12,false)])
                      (.node 3746275 ([(1,true),(2,true),(3,true),(8,true),(6,false),(5,false),(12,false)],[(13,false),(4,false),(7,false),(0,false),(9,true),(10,true),(11,true)])
                        (.node 3746113 ([(0,true),(1,true),(8,true),(3,false),(13,false),(5,true),(11,true)],[(2,false),(7,false),(6,false),(10,false),(9,false),(4,true),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3748903 ([(4,true),(5,true),(13,true),(2,false),(1,false),(0,false),(11,true)],[(3,true),(7,true),(8,true),(9,true),(10,true),(6,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3749755 ([(2,true),(3,true),(8,true),(9,true),(10,true),(6,false),(12,false)],[(13,false),(5,false),(4,false),(7,false),(1,false),(0,false),(11,true)])
                      (.node 3749467 ([(1,true),(2,true),(13,false),(5,false),(4,false),(10,true),(11,true)],[(3,true),(9,false),(8,false),(7,false),(0,false),(6,false),(12,false)])
                        .empty
                        .empty)
                      (.node 3749803 ([(1,true),(2,true),(3,true),(4,true),(10,true),(6,false),(12,false)],[(13,false),(5,false),(9,false),(8,false),(7,false),(0,false),(11,true)])
                        .empty
                        .empty)))
                  (.node 3752107 ([(2,true),(3,true),(4,true),(10,true),(0,false),(6,false),(12,false)],[(13,false),(5,false),(9,false),(8,false),(7,false),(1,false),(11,true)])
                    (.node 3751867 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(12,false)],[(13,false),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3751837 ([(5,true),(13,true),(3,true),(9,false),(8,false),(0,true),(11,true)],[(2,false),(1,false),(10,false),(4,true),(7,true),(6,false),(12,false)])
                        (.node 3751771 ([(2,true),(3,true),(10,true),(0,false),(8,false),(5,true),(12,false)],[(13,false),(6,true),(9,true),(4,true),(7,false),(1,false),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3752095 ([(4,true),(5,true),(13,true),(2,false),(8,true),(0,true),(11,true)],[(3,true),(7,true),(1,false),(10,false),(9,false),(6,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3752203 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(12,false)],[(13,false),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3752179 ([(4,true),(9,false),(2,true),(13,false),(6,true),(0,true),(11,true)],[(3,true),(7,true),(8,true),(1,false),(10,false),(5,true),(12,false)])
                        .empty
                        .empty)
                      (.node 3752971 ([(5,true),(13,true),(3,true),(8,false),(0,false),(10,true),(11,true)],[(2,false),(1,false),(7,false),(4,false),(9,true),(6,false),(12,false)])
                        .empty
                        .empty)))))
              (.node 3769411 ([(2,true),(3,true),(4,true),(5,true),(10,true),(0,false),(12,false)],[(13,false),(6,false),(9,false),(8,false),(7,false),(1,false),(11,true)])
                (.node 3760093 ([(1,true),(8,false),(3,false),(13,false),(6,true),(10,true),(11,true)],[(2,false),(9,true),(0,true),(7,true),(4,true),(5,true),(12,false)])
                  (.node 3757699 ([(0,false),(6,false),(13,true),(2,false),(8,false),(4,false),(11,true)],[(3,true),(10,false),(9,false),(1,false),(7,true),(5,true),(12,false)])
                    (.node 3754507 ([(1,true),(2,true),(3,true),(8,true),(9,true),(5,true),(12,false)],[(13,false),(6,true),(0,true),(7,true),(4,true),(10,true),(11,true)])
                      (.node 3754219 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(12,false)],[(13,false),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        (.node 3754171 ([(1,true),(2,true),(3,true),(4,true),(8,true),(6,false),(12,false)],[(13,false),(5,false),(7,false),(0,false),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3754555 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(12,false)],[(13,false),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3758167 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(12,false)],[(13,false),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3758155 ([(2,true),(3,true),(4,true),(9,true),(0,false),(6,false),(12,false)],[(13,false),(5,false),(8,false),(7,false),(1,false),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3758287 ([(1,true),(2,true),(3,true),(4,true),(8,true),(6,false),(12,false)],[(13,false),(5,false),(7,false),(0,false),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)))
                  (.node 3768511 ([(5,true),(6,true),(13,true),(3,false),(2,false),(1,false),(11,true)],[(4,true),(7,true),(8,true),(9,true),(10,true),(0,false),(12,false)])
                    (.node 3760681 ([(1,true),(2,true),(13,false),(6,true),(8,false),(4,true),(11,true)],[(3,true),(7,false),(0,false),(9,true),(10,true),(5,true),(12,false)])
                      (.node 3760519 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(12,false)],[(13,false),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        (.node 3760507 ([(2,true),(3,true),(8,false),(0,true),(10,true),(5,true),(12,false)],[(13,false),(6,true),(7,false),(1,false),(9,false),(4,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3768463 ([(6,true),(13,true),(3,false),(9,false),(8,false),(1,false),(11,true)],[(4,true),(5,true),(7,true),(2,true),(10,true),(0,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3769075 ([(2,true),(3,true),(13,false),(6,false),(5,false),(10,true),(11,true)],[(4,true),(9,false),(8,false),(7,false),(1,false),(0,false),(12,false)])
                      (.node 3769027 ([(3,true),(4,true),(5,true),(8,true),(1,false),(0,false),(12,false)],[(13,false),(6,false),(7,false),(2,false),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3769363 ([(3,true),(4,true),(8,true),(9,true),(10,true),(0,false),(12,false)],[(13,false),(6,false),(5,false),(7,false),(2,false),(1,false),(11,true)])
                        .empty
                        .empty))))
                (.node 3772579 ([(6,true),(13,true),(4,true),(8,false),(1,false),(10,true),(11,true)],[(3,false),(2,false),(7,false),(5,false),(9,true),(0,false),(12,false)])
                  (.node 3771703 ([(5,true),(6,true),(13,true),(3,false),(8,true),(1,true),(11,true)],[(4,true),(7,true),(2,false),(10,false),(9,false),(0,false),(12,false)])
                    (.node 3771445 ([(6,true),(13,true),(4,true),(9,false),(8,false),(1,true),(11,true)],[(3,false),(2,false),(10,false),(5,true),(7,true),(0,false),(12,false)])
                      (.node 3771379 ([(3,true),(4,true),(10,true),(1,false),(8,false),(6,true),(12,false)],[(13,false),(0,true),(9,true),(5,true),(7,false),(2,false),(11,true)])
                        (.node 3771361 ([(6,true),(13,true),(3,false),(8,true),(9,true),(10,true),(11,true)],[(4,true),(5,true),(7,true),(2,false),(1,false),(0,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3771475 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(12,false)],[(13,false),(0,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3771787 ([(5,true),(9,false),(3,true),(13,false),(0,true),(1,true),(11,true)],[(4,true),(7,true),(8,true),(2,false),(10,false),(6,true),(12,false)])
                      (.node 3771715 ([(3,true),(4,true),(5,true),(10,true),(1,false),(0,false),(12,false)],[(13,false),(6,false),(9,false),(8,false),(7,false),(2,false),(11,true)])
                        .empty
                        .empty)
                      (.node 3771811 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(12,false)],[(13,false),(0,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)))
                  (.node 3774163 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(12,false)],[(13,false),(0,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                    (.node 3773827 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(12,false)],[(13,false),(0,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3773779 ([(2,true),(3,true),(4,true),(5,true),(8,true),(0,false),(12,false)],[(13,false),(6,false),(7,false),(1,false),(9,true),(10,true),(11,true)])
                        (.node 3772627 ([(5,true),(8,false),(1,false),(0,false),(13,true),(3,false),(11,true)],[(4,true),(7,true),(2,true),(10,false),(9,false),(6,true),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3774115 ([(2,true),(3,true),(4,true),(8,true),(9,true),(6,true),(12,false)],[(13,false),(0,true),(1,true),(7,true),(5,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3777763 ([(3,true),(4,true),(5,true),(9,true),(1,false),(0,false),(12,false)],[(13,false),(6,false),(8,false),(7,false),(2,false),(10,true),(11,true)])
                      (.node 3777307 ([(1,false),(0,false),(13,true),(3,false),(8,false),(5,false),(11,true)],[(4,true),(10,false),(9,false),(2,false),(7,true),(6,true),(12,false)])
                        .empty
                        .empty)
                      (.node 3777775 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(12,false)],[(13,false),(0,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)))))))
          (.node 3886159 ([(4,true),(5,true),(8,false),(2,true),(10,true),(0,false),(12,false)],[(13,false),(6,false),(9,true),(3,true),(7,true),(1,false),(11,true)])
            (.node 3800257 ([(6,true),(0,true),(8,true),(9,true),(4,false),(13,false),(12,false)],[(3,false),(2,false),(1,false),(7,false),(5,false),(10,true),(11,true)])
              (.node 3793723 ([(3,true),(4,true),(5,true),(8,true),(9,true),(0,true),(12,false)],[(13,false),(1,true),(2,true),(7,true),(6,true),(10,true),(11,true)])
                (.node 3783481 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(12,false)],[(13,false),(1,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                  (.node 3782533 ([(6,true),(10,false),(2,true),(8,true),(4,false),(13,false),(12,false)],[(3,false),(7,false),(5,false),(9,true),(1,false),(0,false),(11,true)])
                    (.node 3780127 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(12,false)],[(13,false),(0,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3780115 ([(3,true),(4,true),(8,false),(1,true),(10,true),(6,true),(12,false)],[(13,false),(0,true),(7,false),(2,false),(9,false),(5,true),(11,true)])
                        (.node 3779701 ([(2,true),(8,false),(4,false),(13,false),(0,true),(10,true),(11,true)],[(3,false),(9,true),(1,true),(7,true),(5,true),(6,true),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3780289 ([(2,true),(3,true),(13,false),(0,true),(8,false),(5,true),(11,true)],[(4,true),(7,false),(1,false),(9,true),(10,true),(6,true),(12,false)])
                        .empty
                        .empty))
                    (.node 3782917 ([(5,true),(8,false),(1,false),(13,true),(3,false),(10,true),(11,true)],[(4,true),(7,true),(2,true),(9,false),(6,true),(0,true),(12,false)])
                      (.node 3782869 ([(6,true),(10,false),(2,false),(8,true),(4,false),(13,false),(12,false)],[(3,false),(9,false),(5,true),(7,true),(1,false),(0,false),(11,true)])
                        (.node 3782581 ([(5,true),(6,true),(10,false),(2,true),(3,true),(13,false),(12,false)],[(4,true),(7,true),(8,true),(9,true),(1,false),(0,false),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3783433 ([(3,true),(4,true),(9,false),(8,false),(6,true),(0,true),(12,false)],[(13,false),(1,true),(2,true),(7,true),(5,false),(10,true),(11,true)])
                        .empty
                        .empty)))
                  (.node 3789043 ([(6,true),(0,true),(13,true),(4,true),(8,false),(2,true),(11,true)],[(3,false),(10,false),(9,false),(5,true),(7,true),(1,false),(12,false)])
                    (.node 3788587 ([(5,true),(6,true),(0,true),(13,true),(3,false),(2,false),(11,true)],[(4,true),(7,true),(8,true),(9,true),(10,true),(1,false),(12,false)])
                      (.node 3788119 ([(6,true),(8,false),(2,false),(10,false),(4,false),(13,false),(12,false)],[(3,false),(7,false),(5,false),(9,false),(0,true),(1,true),(11,true)])
                        (.node 3786649 ([(6,true),(0,true),(13,true),(4,true),(8,false),(2,false),(11,true)],[(3,false),(7,false),(5,false),(9,true),(10,true),(1,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3788617 ([(0,true),(13,true),(3,false),(8,false),(5,true),(10,true),(11,true)],[(4,true),(7,false),(6,false),(9,false),(2,false),(1,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3790939 ([(5,true),(6,true),(8,true),(2,true),(3,true),(13,false),(12,false)],[(4,true),(7,true),(0,true),(1,true),(9,true),(10,true),(11,true)])
                      (.node 3790513 ([(6,true),(8,false),(1,false),(13,true),(4,true),(10,true),(11,true)],[(3,false),(2,false),(7,false),(5,false),(9,false),(0,true),(12,false)])
                        .empty
                        .empty)
                      (.node 3790969 ([(0,true),(13,true),(4,true),(5,true),(9,false),(2,true),(11,true)],[(3,false),(10,false),(6,true),(7,true),(8,true),(1,false),(12,false)])
                        .empty
                        .empty))))
                (.node 3796933 ([(0,true),(13,true),(3,false),(2,false),(9,false),(5,true),(11,true)],[(4,true),(8,false),(7,false),(6,false),(10,false),(1,false),(12,false)])
                  (.node 3794917 ([(0,true),(13,true),(3,false),(2,false),(8,true),(5,false),(11,true)],[(4,true),(10,false),(9,false),(6,true),(7,true),(1,false),(12,false)])
                    (.node 3794581 ([(0,true),(13,true),(3,false),(8,true),(9,true),(10,true),(11,true)],[(4,true),(5,true),(6,true),(7,true),(2,false),(1,false),(12,false)])
                      (.node 3794293 ([(6,true),(0,true),(13,true),(3,false),(2,false),(10,true),(11,true)],[(4,true),(5,true),(7,true),(8,true),(9,true),(1,false),(12,false)])
                        (.node 3793771 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(12,false)],[(13,false),(1,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3794629 ([(6,true),(8,false),(1,false),(13,true),(3,false),(10,true),(11,true)],[(4,true),(5,true),(7,true),(2,true),(9,false),(0,true),(12,false)])
                        .empty
                        .empty))
                    (.node 3796705 ([(3,true),(4,true),(5,true),(6,true),(9,true),(1,false),(12,false)],[(13,false),(0,false),(8,false),(7,false),(2,false),(10,true),(11,true)])
                      (.node 3796693 ([(5,true),(6,true),(9,true),(2,true),(3,true),(13,false),(12,false)],[(4,true),(7,true),(8,true),(0,true),(1,true),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3796915 ([(3,true),(4,true),(8,false),(6,false),(10,false),(1,false),(12,false)],[(13,false),(0,false),(7,false),(2,false),(9,false),(5,true),(11,true)])
                        .empty
                        .empty)))
                  (.node 3799669 ([(6,true),(0,true),(8,true),(4,false),(3,false),(2,false),(12,false)],[(13,false),(1,false),(7,false),(5,false),(9,true),(10,true),(11,true)])
                    (.node 3797257 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(12,false)],[(13,false),(1,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3797047 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(12,false)],[(13,false),(1,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        (.node 3797029 ([(5,true),(6,true),(8,false),(2,true),(3,true),(13,false),(12,false)],[(4,true),(7,true),(1,false),(0,false),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3797269 ([(0,true),(13,true),(3,false),(2,false),(8,true),(5,true),(11,true)],[(4,true),(9,true),(10,true),(6,true),(7,true),(1,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3800173 ([(6,true),(0,true),(9,true),(4,false),(3,false),(2,false),(12,false)],[(13,false),(1,false),(8,false),(7,false),(5,false),(10,true),(11,true)])
                      (.node 3799717 ([(5,true),(8,false),(0,false),(10,false),(3,true),(13,false),(12,false)],[(4,true),(7,true),(1,true),(2,true),(9,false),(6,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3800191 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(12,false)],[(13,false),(2,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)))))
              (.node 3866725 ([(2,true),(3,true),(4,true),(8,true),(0,false),(6,false),(12,false)],[(13,false),(5,false),(7,false),(1,false),(9,true),(10,true),(11,true)])
                (.node 3811045 ([(0,true),(1,true),(13,true),(3,false),(8,true),(5,false),(11,true)],[(4,true),(10,false),(9,false),(6,true),(7,true),(2,false),(12,false)])
                  (.node 3805843 ([(6,true),(0,true),(8,true),(4,false),(3,false),(2,false),(12,false)],[(13,false),(1,false),(7,false),(5,false),(9,true),(10,true),(11,true)])
                    (.node 3802993 ([(5,true),(6,true),(8,true),(3,true),(13,false),(1,false),(11,true)],[(4,true),(7,true),(0,true),(10,false),(9,false),(2,false),(12,false)])
                      (.node 3802525 ([(6,true),(8,false),(2,false),(13,true),(4,true),(10,true),(11,true)],[(3,false),(7,false),(5,false),(9,false),(0,true),(1,true),(12,false)])
                        (.node 3800287 ([(1,true),(13,true),(3,false),(9,true),(5,true),(6,true),(11,true)],[(4,true),(10,true),(0,true),(7,true),(8,true),(2,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3803023 ([(0,true),(10,false),(5,false),(8,true),(3,true),(13,false),(12,false)],[(4,true),(7,false),(6,false),(9,false),(2,false),(1,false),(11,true)])
                        .empty
                        .empty))
                    (.node 3810547 ([(6,true),(0,true),(8,true),(2,false),(13,true),(4,true),(11,true)],[(3,false),(9,true),(10,true),(5,true),(7,true),(1,true),(12,false)])
                      (.node 3807727 ([(0,true),(8,false),(5,true),(10,true),(3,true),(13,false),(12,false)],[(4,true),(7,false),(6,false),(9,false),(1,true),(2,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3810577 ([(1,true),(13,true),(3,false),(8,false),(6,true),(10,true),(11,true)],[(4,true),(5,true),(7,false),(0,false),(9,false),(2,false),(12,false)])
                        .empty
                        .empty)))
                  (.node 3813853 ([(1,true),(13,true),(3,false),(9,false),(8,false),(5,true),(11,true)],[(4,true),(7,false),(0,false),(6,false),(10,false),(2,false),(12,false)])
                    (.node 3813379 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(12,false)],[(13,false),(2,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3813313 ([(0,true),(1,true),(13,true),(3,false),(8,false),(5,true),(11,true)],[(4,true),(7,false),(6,false),(10,false),(9,false),(2,false),(12,false)])
                        (.node 3813283 ([(5,true),(6,true),(0,true),(9,false),(3,true),(13,false),(12,false)],[(4,true),(7,true),(8,true),(2,false),(1,false),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3813397 ([(0,true),(1,true),(13,true),(3,false),(8,true),(5,true),(11,true)],[(4,true),(9,true),(10,true),(6,true),(7,true),(2,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3866551 ([(3,true),(4,true),(8,false),(1,true),(10,true),(6,false),(12,false)],[(13,false),(5,false),(9,true),(2,true),(7,true),(0,false),(11,true)])
                      (.node 3813901 ([(0,true),(9,true),(2,false),(13,true),(4,true),(5,true),(11,true)],[(3,false),(10,true),(6,true),(7,true),(8,true),(1,true),(12,false)])
                        .empty
                        .empty)
                      (.node 3866563 ([(1,true),(2,true),(8,true),(4,false),(13,false),(6,true),(11,true)],[(3,false),(7,false),(0,false),(10,false),(9,false),(5,true),(12,false)])
                        .empty
                        .empty))))
                (.node 3870667 ([(3,true),(4,true),(8,false),(1,true),(10,false),(6,false),(12,false)],[(13,false),(5,false),(9,true),(0,true),(7,false),(2,false),(11,true)])
                  (.node 3869827 ([(3,true),(4,true),(10,true),(1,true),(8,false),(6,false),(12,false)],[(13,false),(5,false),(9,false),(2,true),(7,true),(0,true),(11,true)])
                    (.node 3869287 ([(2,true),(3,true),(13,false),(5,false),(8,false),(0,true),(11,true)],[(4,true),(9,true),(10,true),(1,true),(7,true),(6,false),(12,false)])
                      (.node 3869077 ([(2,true),(3,true),(13,false),(5,false),(8,true),(0,true),(11,true)],[(4,true),(7,false),(1,false),(10,false),(9,false),(6,false),(12,false)])
                        (.node 3869059 ([(5,true),(13,true),(3,false),(2,false),(8,true),(0,true),(11,true)],[(4,true),(7,true),(1,false),(10,false),(9,false),(6,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3869299 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(12,false)],[(13,false),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3870571 ([(5,true),(13,true),(3,false),(8,false),(0,false),(10,true),(11,true)],[(4,true),(7,true),(1,true),(2,true),(9,true),(6,false),(12,false)])
                      (.node 3869875 ([(2,true),(3,true),(4,true),(10,true),(0,false),(6,false),(12,false)],[(13,false),(5,false),(9,false),(8,false),(7,false),(1,false),(11,true)])
                        .empty
                        .empty)
                      (.node 3870595 ([(1,true),(10,false),(9,false),(3,true),(4,true),(5,true),(12,false)],[(13,false),(6,true),(0,true),(7,true),(8,true),(2,false),(11,true)])
                        .empty
                        .empty)))
                  (.node 3873403 ([(2,true),(3,true),(4,true),(9,true),(0,false),(6,false),(12,false)],[(13,false),(5,false),(8,false),(7,false),(1,false),(10,true),(11,true)])
                    (.node 3872197 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(12,false)],[(13,false),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3872149 ([(1,true),(2,true),(8,true),(9,true),(4,false),(13,false),(12,false)],[(3,false),(7,false),(0,false),(6,false),(5,false),(10,true),(11,true)])
                        (.node 3870679 ([(1,true),(2,true),(3,true),(4,true),(9,true),(6,false),(12,false)],[(13,false),(5,false),(8,false),(7,false),(0,false),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3872947 ([(1,true),(8,false),(4,false),(3,false),(10,false),(6,false),(12,false)],[(13,false),(5,false),(7,false),(0,false),(9,false),(2,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3878107 ([(2,true),(8,false),(0,true),(10,true),(4,false),(13,false),(12,false)],[(3,false),(9,true),(1,true),(7,true),(6,false),(5,false),(11,true)])
                      (.node 3873415 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(12,false)],[(13,false),(6,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3878323 ([(1,true),(2,true),(8,true),(6,false),(13,true),(4,true),(11,true)],[(3,false),(7,false),(0,false),(9,true),(10,true),(5,true),(12,false)])
                        .empty
                        .empty))))))
            (.node 3908683 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(12,false)],[(13,false),(1,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
              (.node 3897715 ([(3,true),(8,false),(1,true),(10,true),(5,false),(13,false),(12,false)],[(4,false),(9,true),(2,true),(7,true),(0,false),(6,false),(11,true)])
                (.node 3890179 ([(6,true),(13,true),(4,false),(8,false),(1,false),(10,true),(11,true)],[(5,true),(7,true),(2,true),(3,true),(9,true),(0,false),(12,false)])
                  (.node 3888895 ([(3,true),(4,true),(13,false),(6,false),(8,false),(1,true),(11,true)],[(5,true),(9,true),(10,true),(2,true),(7,true),(0,false),(12,false)])
                    (.node 3888667 ([(6,true),(13,true),(4,false),(3,false),(8,true),(1,true),(11,true)],[(5,true),(7,true),(2,false),(10,false),(9,false),(0,false),(12,false)])
                      (.node 3886333 ([(3,true),(4,true),(5,true),(8,true),(1,false),(0,false),(12,false)],[(13,false),(6,false),(7,false),(2,false),(9,true),(10,true),(11,true)])
                        (.node 3886171 ([(2,true),(3,true),(8,true),(5,false),(13,false),(0,true),(11,true)],[(4,false),(7,false),(1,false),(10,false),(9,false),(6,true),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3888685 ([(3,true),(4,true),(13,false),(6,false),(8,true),(1,true),(11,true)],[(5,true),(7,false),(2,false),(10,false),(9,false),(0,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3889435 ([(4,true),(5,true),(10,true),(2,true),(8,false),(0,false),(12,false)],[(13,false),(6,false),(9,false),(3,true),(7,true),(1,true),(11,true)])
                      (.node 3888907 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(12,false)],[(13,false),(0,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3889483 ([(3,true),(4,true),(5,true),(10,true),(1,false),(0,false),(12,false)],[(13,false),(6,false),(9,false),(8,false),(7,false),(2,false),(11,true)])
                        .empty
                        .empty)))
                  (.node 3891805 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(12,false)],[(13,false),(0,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                    (.node 3890287 ([(2,true),(3,true),(4,true),(5,true),(9,true),(0,false),(12,false)],[(13,false),(6,false),(8,false),(7,false),(1,false),(10,true),(11,true)])
                      (.node 3890275 ([(4,true),(5,true),(8,false),(2,true),(10,false),(0,false),(12,false)],[(13,false),(6,false),(9,true),(1,true),(7,false),(3,false),(11,true)])
                        (.node 3890203 ([(2,true),(10,false),(9,false),(4,true),(5,true),(6,true),(12,false)],[(13,false),(0,true),(1,true),(7,true),(8,true),(3,false),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3891757 ([(2,true),(3,true),(8,true),(9,true),(5,false),(13,false),(12,false)],[(4,false),(7,false),(1,false),(0,false),(6,false),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3893011 ([(3,true),(4,true),(5,true),(9,true),(1,false),(0,false),(12,false)],[(13,false),(6,false),(8,false),(7,false),(2,false),(10,true),(11,true)])
                      (.node 3892555 ([(2,true),(8,false),(5,false),(4,false),(10,false),(0,false),(12,false)],[(13,false),(6,false),(7,false),(1,false),(9,false),(3,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3893023 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(12,false)],[(13,false),(0,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))))
                (.node 3905713 ([(0,true),(13,true),(4,false),(9,false),(8,false),(2,false),(11,true)],[(5,true),(6,true),(7,true),(3,true),(10,true),(1,false),(12,false)])
                  (.node 3900739 ([(3,true),(4,true),(13,false),(1,true),(8,false),(6,true),(11,true)],[(5,true),(7,false),(2,false),(9,true),(10,true),(0,true),(12,false)])
                    (.node 3900565 ([(4,true),(5,true),(8,false),(2,true),(10,true),(0,true),(12,false)],[(13,false),(1,true),(7,false),(3,false),(9,false),(6,true),(11,true)])
                      (.node 3900151 ([(3,true),(8,false),(5,false),(13,false),(1,true),(10,true),(11,true)],[(4,false),(9,true),(2,true),(7,true),(6,true),(0,true),(12,false)])
                        (.node 3897931 ([(2,true),(3,true),(8,true),(0,false),(13,true),(5,true),(11,true)],[(4,false),(7,false),(1,false),(9,true),(10,true),(6,true),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3900577 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(12,false)],[(13,false),(1,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3904267 ([(3,true),(4,true),(5,true),(6,true),(10,true),(1,false),(12,false)],[(13,false),(0,false),(9,false),(8,false),(7,false),(2,false),(11,true)])
                      (.node 3904219 ([(4,true),(5,true),(8,true),(9,true),(10,true),(1,false),(12,false)],[(13,false),(0,false),(6,false),(7,false),(3,false),(2,false),(11,true)])
                        .empty
                        .empty)
                      (.node 3905425 ([(6,true),(0,true),(13,true),(4,false),(3,false),(2,false),(11,true)],[(5,true),(7,true),(8,true),(9,true),(10,true),(1,false),(12,false)])
                        .empty
                        .empty)))
                  (.node 3906643 ([(6,true),(9,false),(4,true),(13,false),(1,true),(2,true),(11,true)],[(5,true),(7,true),(8,true),(3,false),(10,false),(0,true),(12,false)])
                    (.node 3906559 ([(6,true),(0,true),(13,true),(4,false),(8,true),(2,true),(11,true)],[(5,true),(7,true),(3,false),(10,false),(9,false),(1,false),(12,false)])
                      (.node 3906283 ([(3,true),(4,true),(13,false),(0,false),(6,false),(10,true),(11,true)],[(5,true),(9,false),(8,false),(7,false),(2,false),(1,false),(12,false)])
                        (.node 3906235 ([(4,true),(5,true),(6,true),(8,true),(2,false),(1,false),(12,false)],[(13,false),(0,false),(7,false),(3,false),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3906571 ([(4,true),(5,true),(6,true),(10,true),(2,false),(1,false),(12,false)],[(13,false),(0,false),(9,false),(8,false),(7,false),(3,false),(11,true)])
                        .empty
                        .empty))
                    (.node 3908587 ([(4,true),(5,true),(10,true),(2,false),(8,false),(0,true),(12,false)],[(13,false),(1,true),(9,true),(6,true),(7,false),(3,false),(11,true)])
                      (.node 3906667 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(12,false)],[(13,false),(1,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3908611 ([(0,true),(13,true),(4,false),(8,true),(9,true),(10,true),(11,true)],[(5,true),(6,true),(7,true),(3,false),(2,false),(1,false),(12,false)])
                        .empty
                        .empty)))))
              (.node 3917707 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(12,false)],[(13,false),(2,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                (.node 3914677 ([(4,true),(5,true),(6,true),(9,true),(2,false),(1,false),(12,false)],[(13,false),(0,false),(8,false),(7,false),(3,false),(10,true),(11,true)])
                  (.node 3909829 ([(0,true),(13,true),(5,true),(8,false),(2,false),(10,true),(11,true)],[(4,false),(3,false),(7,false),(6,false),(9,true),(1,false),(12,false)])
                    (.node 3909019 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(12,false)],[(13,false),(1,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3908971 ([(3,true),(4,true),(5,true),(8,true),(9,true),(0,true),(12,false)],[(13,false),(1,true),(2,true),(7,true),(6,true),(10,true),(11,true)])
                        (.node 3908695 ([(0,true),(13,true),(5,true),(9,false),(8,false),(2,true),(11,true)],[(4,false),(3,false),(10,false),(6,true),(7,true),(1,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3909541 ([(6,true),(8,false),(2,false),(1,false),(13,true),(4,false),(11,true)],[(5,true),(7,true),(3,true),(10,false),(9,false),(0,true),(12,false)])
                        .empty
                        .empty))
                    (.node 3911035 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(12,false)],[(13,false),(1,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3910987 ([(3,true),(4,true),(5,true),(6,true),(8,true),(1,false),(12,false)],[(13,false),(0,false),(7,false),(2,false),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3914515 ([(2,false),(1,false),(13,true),(4,false),(8,false),(6,false),(11,true)],[(5,true),(10,false),(9,false),(3,false),(7,true),(0,true),(12,false)])
                        .empty
                        .empty)))
                  (.node 3917365 ([(4,true),(5,true),(8,false),(0,false),(10,false),(2,false),(12,false)],[(13,false),(1,false),(7,false),(3,false),(9,false),(6,true),(11,true)])
                    (.node 3917143 ([(6,true),(0,true),(9,true),(3,true),(4,true),(13,false),(12,false)],[(5,true),(7,true),(8,true),(1,true),(2,true),(10,true),(11,true)])
                      (.node 3915103 ([(3,true),(4,true),(5,true),(6,true),(8,true),(1,false),(12,false)],[(13,false),(0,false),(7,false),(2,false),(9,true),(10,true),(11,true)])
                        (.node 3914689 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(12,false)],[(13,false),(1,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3917155 ([(4,true),(5,true),(6,true),(0,true),(9,true),(2,false),(12,false)],[(13,false),(1,false),(8,false),(7,false),(3,false),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3917479 ([(6,true),(0,true),(8,false),(3,true),(4,true),(13,false),(12,false)],[(5,true),(7,true),(2,false),(1,false),(9,true),(10,true),(11,true)])
                      (.node 3917383 ([(1,true),(13,true),(4,false),(3,false),(9,false),(6,true),(11,true)],[(5,true),(8,false),(7,false),(0,false),(10,false),(2,false),(12,false)])
                        .empty
                        .empty)
                      (.node 3917497 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(12,false)],[(13,false),(2,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))))
                (.node 3923473 ([(1,true),(13,true),(4,false),(8,false),(6,true),(10,true),(11,true)],[(5,true),(7,false),(0,false),(9,false),(3,false),(2,false),(12,false)])
                  (.node 3920119 ([(0,true),(10,false),(3,false),(8,true),(5,false),(13,false),(12,false)],[(4,false),(9,false),(6,true),(7,true),(2,false),(1,false),(11,true)])
                    (.node 3919783 ([(0,true),(10,false),(3,true),(8,true),(5,false),(13,false),(12,false)],[(4,false),(7,false),(6,false),(9,true),(2,false),(1,false),(11,true)])
                      (.node 3919495 ([(6,true),(0,true),(10,false),(3,true),(4,true),(13,false),(12,false)],[(5,true),(7,true),(8,true),(9,true),(2,false),(1,false),(11,true)])
                        (.node 3917719 ([(1,true),(13,true),(4,false),(3,false),(8,true),(6,true),(11,true)],[(5,true),(9,true),(10,true),(0,true),(7,true),(2,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3919831 ([(6,true),(8,false),(2,false),(13,true),(4,false),(10,true),(11,true)],[(5,true),(7,true),(3,true),(9,false),(0,true),(1,true),(12,false)])
                        .empty
                        .empty))
                    (.node 3920689 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(12,false)],[(13,false),(2,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 3920641 ([(4,true),(5,true),(9,false),(8,false),(0,true),(1,true),(12,false)],[(13,false),(2,true),(3,true),(7,true),(6,false),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 3923443 ([(6,true),(0,true),(1,true),(13,true),(4,false),(3,false),(11,true)],[(5,true),(7,true),(8,true),(9,true),(10,true),(2,false),(12,false)])
                        .empty
                        .empty)))
                  (.node 3926293 ([(0,true),(1,true),(13,true),(5,true),(8,false),(3,true),(11,true)],[(4,false),(10,false),(9,false),(6,true),(7,true),(2,false),(12,false)])
                    (.node 3925795 ([(6,true),(0,true),(8,true),(3,true),(4,true),(13,false),(12,false)],[(5,true),(7,true),(1,true),(2,true),(9,true),(10,true),(11,true)])
                      (.node 3925369 ([(0,true),(8,false),(3,false),(10,false),(5,false),(13,false),(12,false)],[(4,false),(7,false),(6,false),(9,false),(1,true),(2,true),(11,true)])
                        (.node 3923899 ([(0,true),(1,true),(13,true),(5,true),(8,false),(3,false),(11,true)],[(4,false),(7,false),(6,false),(9,true),(10,true),(2,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3925825 ([(1,true),(13,true),(5,true),(6,true),(9,false),(3,true),(11,true)],[(4,false),(10,false),(0,true),(7,true),(8,true),(2,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3930931 ([(4,true),(5,true),(6,true),(8,true),(9,true),(1,true),(12,false)],[(13,false),(2,true),(3,true),(7,true),(0,true),(10,true),(11,true)])
                      (.node 3927763 ([(0,true),(8,false),(2,false),(13,true),(5,true),(10,true),(11,true)],[(4,false),(3,false),(7,false),(6,false),(9,false),(1,true),(12,false)])
                        .empty
                        .empty)
                      (.node 3930979 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(12,false)],[(13,false),(2,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)))))))))
      (.node 4440800 ([(0,true),(11,true),(4,false),(8,true),(9,true),(2,false),(13,false)],[(1,false),(10,false),(3,true),(7,false),(6,false),(5,false),(12,true)])
        (.node 4181150 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(13,false)],[(0,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
          (.node 4051429 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(12,false)],[(13,false),(3,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
            (.node 4027189 ([(5,true),(6,true),(8,false),(3,true),(10,false),(1,false),(12,false)],[(13,false),(0,false),(9,true),(2,true),(7,false),(4,false),(11,true)])
              (.node 3942583 ([(1,true),(8,false),(6,true),(10,true),(4,true),(13,false),(12,false)],[(5,true),(7,false),(0,false),(9,false),(2,true),(3,true),(11,true)])
                (.node 3936631 ([(6,true),(8,false),(1,false),(10,false),(4,true),(13,false),(12,false)],[(5,true),(7,true),(2,true),(3,true),(9,false),(0,true),(11,true)])
                  (.node 3933763 ([(1,true),(2,true),(13,true),(4,false),(8,false),(6,true),(11,true)],[(5,true),(7,false),(0,false),(10,false),(9,false),(3,false),(12,false)])
                    (.node 3931879 ([(0,true),(8,false),(2,false),(13,true),(4,false),(10,true),(11,true)],[(5,true),(6,true),(7,true),(3,true),(9,false),(1,true),(12,false)])
                      (.node 3931831 ([(1,true),(13,true),(4,false),(3,false),(8,true),(6,false),(11,true)],[(5,true),(10,false),(9,false),(0,true),(7,true),(2,false),(12,false)])
                        (.node 3931543 ([(0,true),(1,true),(13,true),(4,false),(3,false),(10,true),(11,true)],[(5,true),(6,true),(7,true),(8,true),(9,true),(2,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3933733 ([(6,true),(0,true),(1,true),(9,false),(4,true),(13,false),(12,false)],[(5,true),(7,true),(8,true),(3,false),(2,false),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 3934303 ([(2,true),(13,true),(4,false),(9,false),(8,false),(6,true),(11,true)],[(5,true),(7,false),(1,false),(0,false),(10,false),(3,false),(12,false)])
                      (.node 3933847 ([(1,true),(2,true),(13,true),(4,false),(8,true),(6,true),(11,true)],[(5,true),(9,true),(10,true),(0,true),(7,true),(3,false),(12,false)])
                        (.node 3933829 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(12,false)],[(13,false),(3,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3934351 ([(1,true),(9,true),(3,false),(13,true),(5,true),(6,true),(11,true)],[(4,false),(10,true),(0,true),(7,true),(8,true),(2,true),(12,false)])
                        .empty
                        .empty)))
                  (.node 3937507 ([(0,true),(1,true),(8,true),(9,true),(5,false),(13,false),(12,false)],[(4,false),(3,false),(2,false),(7,false),(6,false),(10,true),(11,true)])
                    (.node 3937423 ([(0,true),(1,true),(9,true),(5,false),(4,false),(3,false),(12,false)],[(13,false),(2,false),(8,false),(7,false),(6,false),(10,true),(11,true)])
                      (.node 3937399 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(12,false)],[(13,false),(3,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        (.node 3936919 ([(0,true),(1,true),(8,true),(5,false),(4,false),(3,false),(12,false)],[(13,false),(2,false),(7,false),(6,false),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3937495 ([(2,true),(13,true),(4,false),(9,true),(6,true),(0,true),(11,true)],[(5,true),(10,true),(1,true),(7,true),(8,true),(3,false),(12,false)])
                        .empty
                        .empty))
                    (.node 3937879 ([(1,true),(10,false),(6,false),(8,true),(4,true),(13,false),(12,false)],[(5,true),(7,false),(0,false),(9,false),(3,false),(2,false),(11,true)])
                      (.node 3937849 ([(6,true),(0,true),(8,true),(4,true),(13,false),(2,false),(11,true)],[(5,true),(7,true),(1,true),(10,false),(9,false),(3,false),(12,false)])
                        .empty
                        .empty)
                      (.node 3939775 ([(0,true),(8,false),(3,false),(13,true),(5,true),(10,true),(11,true)],[(4,false),(7,false),(6,false),(9,false),(1,true),(2,true),(12,false)])
                        .empty
                        .empty))))
                (.node 4023541 ([(4,true),(5,true),(6,true),(8,true),(2,false),(1,false),(12,false)],[(13,false),(0,false),(7,false),(3,false),(9,true),(10,true),(11,true)])
                  (.node 4018165 ([(4,true),(8,false),(2,true),(10,true),(6,false),(13,false),(12,false)],[(5,false),(9,true),(3,true),(7,true),(1,false),(0,false),(11,true)])
                    (.node 3947797 ([(0,true),(1,true),(8,true),(3,false),(13,true),(5,true),(11,true)],[(4,false),(9,true),(10,true),(6,true),(7,true),(2,true),(12,false)])
                      (.node 3947785 ([(2,true),(13,true),(4,false),(8,false),(0,true),(10,true),(11,true)],[(5,true),(6,true),(7,false),(1,false),(9,false),(3,false),(12,false)])
                        (.node 3943093 ([(0,true),(1,true),(8,true),(5,false),(4,false),(3,false),(12,false)],[(13,false),(2,false),(7,false),(6,false),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 3947959 ([(1,true),(2,true),(13,true),(4,false),(8,true),(6,false),(11,true)],[(5,true),(10,false),(9,false),(0,true),(7,true),(3,false),(12,false)])
                        .empty
                        .empty))
                    (.node 4023073 ([(5,true),(6,true),(8,false),(3,true),(10,true),(1,false),(12,false)],[(13,false),(0,false),(9,true),(4,true),(7,true),(2,false),(11,true)])
                      (.node 4018381 ([(3,true),(4,true),(8,true),(1,false),(13,true),(6,true),(11,true)],[(5,false),(7,false),(2,false),(9,true),(10,true),(0,true),(12,false)])
                        .empty
                        .empty)
                      (.node 4023085 ([(3,true),(4,true),(8,true),(6,false),(13,false),(1,true),(11,true)],[(5,false),(7,false),(2,false),(10,false),(9,false),(0,true),(12,false)])
                        .empty
                        .empty)))
                  (.node 4025893 ([(4,true),(5,true),(13,false),(0,false),(8,true),(2,true),(11,true)],[(6,true),(7,false),(3,false),(10,false),(9,false),(1,false),(12,false)])
                    (.node 4025809 ([(4,true),(5,true),(13,false),(0,false),(8,false),(2,true),(11,true)],[(6,true),(9,true),(10,true),(3,true),(7,true),(1,false),(12,false)])
                      (.node 4024339 ([(4,true),(5,true),(6,true),(10,true),(2,false),(1,false),(12,false)],[(13,false),(0,false),(9,false),(8,false),(7,false),(3,false),(11,true)])
                        (.node 4024291 ([(5,true),(6,true),(10,true),(3,true),(8,false),(1,false),(12,false)],[(13,false),(0,false),(9,false),(4,true),(7,true),(2,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4025821 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(12,false)],[(13,false),(1,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 4026613 ([(3,true),(4,true),(8,true),(9,true),(6,false),(13,false),(12,false)],[(5,false),(7,false),(2,false),(1,false),(0,false),(10,true),(11,true)])
                      (.node 4025917 ([(0,true),(13,true),(5,false),(4,false),(8,true),(2,true),(11,true)],[(6,true),(7,true),(3,false),(10,false),(9,false),(1,false),(12,false)])
                        .empty
                        .empty)
                      (.node 4026661 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(12,false)],[(13,false),(1,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)))))
              (.node 4041475 ([(4,true),(5,true),(6,true),(0,true),(10,true),(2,false),(12,false)],[(13,false),(1,false),(9,false),(8,false),(7,false),(3,false),(11,true)])
                (.node 4035139 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(12,false)],[(13,false),(2,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                  (.node 4029925 ([(4,true),(5,true),(6,true),(9,true),(2,false),(1,false),(12,false)],[(13,false),(0,false),(8,false),(7,false),(3,false),(10,true),(11,true)])
                    (.node 4027429 ([(0,true),(13,true),(5,false),(8,false),(2,false),(10,true),(11,true)],[(6,true),(7,true),(3,true),(4,true),(9,true),(1,false),(12,false)])
                      (.node 4027411 ([(3,true),(10,false),(9,false),(5,true),(6,true),(0,true),(12,false)],[(13,false),(1,true),(2,true),(7,true),(8,true),(4,false),(11,true)])
                        (.node 4027201 ([(3,true),(4,true),(5,true),(6,true),(9,true),(1,false),(12,false)],[(13,false),(0,false),(8,false),(7,false),(2,false),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4029763 ([(3,true),(8,false),(6,false),(5,false),(10,false),(1,false),(12,false)],[(13,false),(0,false),(7,false),(2,false),(9,false),(4,true),(11,true)])
                        .empty
                        .empty))
                    (.node 4034965 ([(3,false),(2,false),(13,true),(5,false),(8,false),(0,false),(11,true)],[(6,true),(10,false),(9,false),(4,false),(7,true),(1,true),(12,false)])
                      (.node 4029937 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(12,false)],[(13,false),(1,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 4035127 ([(5,true),(6,true),(0,true),(9,true),(3,false),(2,false),(12,false)],[(13,false),(1,false),(8,false),(7,false),(4,false),(10,true),(11,true)])
                        .empty
                        .empty)))
                  (.node 4037947 ([(4,true),(5,true),(13,false),(2,true),(8,false),(0,true),(11,true)],[(6,true),(7,false),(3,false),(9,true),(10,true),(1,true),(12,false)])
                    (.node 4037479 ([(5,true),(6,true),(8,false),(3,true),(10,true),(1,true),(12,false)],[(13,false),(2,true),(7,false),(4,false),(9,false),(0,true),(11,true)])
                      (.node 4037359 ([(4,true),(8,false),(6,false),(13,false),(2,true),(10,true),(11,true)],[(5,false),(9,true),(3,true),(7,true),(0,true),(1,true),(12,false)])
                        (.node 4035553 ([(4,true),(5,true),(6,true),(0,true),(8,true),(2,false),(12,false)],[(13,false),(1,false),(7,false),(3,false),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4037491 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(12,false)],[(13,false),(2,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 4041139 ([(4,true),(5,true),(13,false),(1,false),(0,false),(10,true),(11,true)],[(6,true),(9,false),(8,false),(7,false),(3,false),(2,false),(12,false)])
                      (.node 4041091 ([(5,true),(6,true),(0,true),(8,true),(3,false),(2,false),(12,false)],[(13,false),(1,false),(7,false),(4,false),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 4041427 ([(5,true),(6,true),(8,true),(9,true),(10,true),(2,false),(12,false)],[(13,false),(1,false),(0,false),(7,false),(4,false),(3,false),(11,true)])
                        .empty
                        .empty))))
                (.node 4043875 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(12,false)],[(13,false),(2,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                  (.node 4043539 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(12,false)],[(13,false),(2,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                    (.node 4043443 ([(5,true),(6,true),(10,true),(3,false),(8,false),(1,true),(12,false)],[(13,false),(2,true),(9,true),(0,true),(7,false),(4,false),(11,true)])
                      (.node 4042675 ([(0,true),(1,true),(13,true),(5,false),(4,false),(3,false),(11,true)],[(6,true),(7,true),(8,true),(9,true),(10,true),(2,false),(12,false)])
                        (.node 4042627 ([(1,true),(13,true),(5,false),(9,false),(8,false),(3,false),(11,true)],[(6,true),(0,true),(7,true),(4,true),(10,true),(2,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4043467 ([(1,true),(13,true),(5,false),(8,true),(9,true),(10,true),(11,true)],[(6,true),(0,true),(7,true),(4,false),(3,false),(2,false),(12,false)])
                        .empty
                        .empty))
                    (.node 4043779 ([(5,true),(6,true),(0,true),(10,true),(3,false),(2,false),(12,false)],[(13,false),(1,false),(9,false),(8,false),(7,false),(4,false),(11,true)])
                      (.node 4043551 ([(1,true),(13,true),(6,true),(9,false),(8,false),(3,true),(11,true)],[(5,false),(4,false),(10,false),(0,true),(7,true),(2,false),(12,false)])
                        .empty
                        .empty)
                      (.node 4043809 ([(0,true),(1,true),(13,true),(5,false),(8,true),(3,true),(11,true)],[(6,true),(7,true),(4,false),(10,false),(9,false),(2,false),(12,false)])
                        .empty
                        .empty)))
                  (.node 4046227 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(12,false)],[(13,false),(2,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                    (.node 4045891 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(12,false)],[(13,false),(2,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                      (.node 4045843 ([(4,true),(5,true),(6,true),(0,true),(8,true),(2,false),(12,false)],[(13,false),(1,false),(7,false),(3,false),(9,true),(10,true),(11,true)])
                        (.node 4043893 ([(0,true),(9,false),(5,true),(13,false),(2,true),(3,true),(11,true)],[(6,true),(7,true),(8,true),(4,false),(10,false),(1,true),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4046179 ([(4,true),(5,true),(6,true),(8,true),(9,true),(1,true),(12,false)],[(13,false),(2,true),(3,true),(7,true),(0,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 4046791 ([(0,true),(8,false),(3,false),(2,false),(13,true),(5,false),(11,true)],[(6,true),(7,true),(4,true),(10,false),(9,false),(1,true),(12,false)])
                      (.node 4046743 ([(1,true),(13,true),(6,true),(8,false),(3,false),(10,true),(11,true)],[(5,false),(4,false),(7,false),(0,false),(9,true),(2,false),(12,false)])
                        .empty
                        .empty)
                      (.node 4051381 ([(5,true),(6,true),(0,true),(8,true),(9,true),(2,true),(12,false)],[(13,false),(3,true),(4,true),(7,true),(1,true),(10,true),(11,true)])
                        .empty
                        .empty))))))
            (.node 4072279 ([(1,true),(2,true),(9,true),(6,false),(5,false),(4,false),(12,false)],[(13,false),(3,false),(8,false),(7,false),(0,false),(10,true),(11,true)])
              (.node 4060225 ([(1,true),(8,false),(4,false),(10,false),(6,false),(13,false),(12,false)],[(5,false),(7,false),(0,false),(9,false),(2,true),(3,true),(11,true)])
                (.node 4054633 ([(2,true),(13,true),(5,false),(4,false),(8,true),(0,true),(11,true)],[(6,true),(9,true),(10,true),(1,true),(7,true),(3,false),(12,false)])
                  (.node 4054279 ([(5,true),(6,true),(8,false),(1,false),(10,false),(3,false),(12,false)],[(13,false),(2,false),(7,false),(4,false),(9,false),(0,true),(11,true)])
                    (.node 4052281 ([(2,true),(13,true),(5,false),(4,false),(8,true),(0,false),(11,true)],[(6,true),(10,false),(9,false),(1,true),(7,true),(3,false),(12,false)])
                      (.node 4051993 ([(1,true),(2,true),(13,true),(5,false),(4,false),(10,true),(11,true)],[(6,true),(0,true),(7,true),(8,true),(9,true),(3,false),(12,false)])
                        (.node 4051945 ([(2,true),(13,true),(5,false),(8,true),(9,true),(10,true),(11,true)],[(6,true),(0,true),(1,true),(7,true),(4,false),(3,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4052329 ([(1,true),(8,false),(3,false),(13,true),(5,false),(10,true),(11,true)],[(6,true),(0,true),(7,true),(4,true),(9,false),(2,true),(12,false)])
                        .empty
                        .empty))
                    (.node 4054393 ([(0,true),(1,true),(9,true),(4,true),(5,true),(13,false),(12,false)],[(6,true),(7,true),(8,true),(2,true),(3,true),(10,true),(11,true)])
                      (.node 4054363 ([(5,true),(6,true),(0,true),(1,true),(9,true),(3,false),(12,false)],[(13,false),(2,false),(8,false),(7,false),(4,false),(10,true),(11,true)])
                        (.node 4054297 ([(2,true),(13,true),(5,false),(4,false),(9,false),(0,true),(11,true)],[(6,true),(8,false),(7,false),(1,false),(10,false),(3,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4054621 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(12,false)],[(13,false),(3,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)))
                  (.node 4056697 ([(1,true),(10,false),(4,true),(8,true),(6,false),(13,false),(12,false)],[(5,false),(7,false),(0,false),(9,true),(3,false),(2,false),(11,true)])
                    (.node 4055497 ([(5,true),(6,true),(9,false),(8,false),(1,true),(2,true),(12,false)],[(13,false),(3,true),(4,true),(7,true),(0,false),(10,true),(11,true)])
                      (.node 4054729 ([(0,true),(1,true),(8,false),(4,true),(5,true),(13,false),(12,false)],[(6,true),(7,true),(3,false),(2,false),(9,true),(10,true),(11,true)])
                        (.node 4054705 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(12,false)],[(13,false),(3,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4055545 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(12,false)],[(13,false),(3,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty))
                    (.node 4057033 ([(1,true),(10,false),(4,false),(8,true),(6,false),(13,false),(12,false)],[(5,false),(9,false),(0,true),(7,true),(3,false),(2,false),(11,true)])
                      (.node 4056745 ([(0,true),(1,true),(10,false),(4,true),(5,true),(13,false),(12,false)],[(6,true),(7,true),(8,true),(9,true),(3,false),(2,false),(11,true)])
                        .empty
                        .empty)
                      (.node 4057081 ([(0,true),(8,false),(3,false),(13,true),(5,false),(10,true),(11,true)],[(6,true),(7,true),(4,true),(9,false),(1,true),(2,true),(12,false)])
                        .empty
                        .empty))))
                (.node 4068247 ([(1,true),(2,true),(8,true),(4,false),(13,true),(6,true),(11,true)],[(5,false),(9,true),(10,true),(0,true),(7,true),(3,true),(12,false)])
                  (.node 4063033 ([(2,true),(13,true),(6,true),(0,true),(9,false),(4,true),(11,true)],[(5,false),(10,false),(1,true),(7,true),(8,true),(3,false),(12,false)])
                    (.node 4060813 ([(1,true),(2,true),(13,true),(6,true),(8,false),(4,false),(11,true)],[(5,false),(7,false),(0,false),(9,true),(10,true),(3,false),(12,false)])
                      (.node 4060693 ([(0,true),(1,true),(2,true),(13,true),(5,false),(4,false),(11,true)],[(6,true),(7,true),(8,true),(9,true),(10,true),(3,false),(12,false)])
                        (.node 4060681 ([(2,true),(13,true),(5,false),(8,false),(0,true),(10,true),(11,true)],[(6,true),(7,false),(1,false),(9,false),(4,false),(3,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4062619 ([(1,true),(8,false),(3,false),(13,true),(6,true),(10,true),(11,true)],[(5,false),(4,false),(7,false),(0,false),(9,false),(2,true),(12,false)])
                        .empty
                        .empty))
                    (.node 4063207 ([(1,true),(2,true),(13,true),(6,true),(8,false),(4,true),(11,true)],[(5,false),(10,false),(9,false),(0,true),(7,true),(3,false),(12,false)])
                      (.node 4063045 ([(0,true),(1,true),(8,true),(4,true),(5,true),(13,false),(12,false)],[(6,true),(7,true),(2,true),(3,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)
                      (.node 4068235 ([(3,true),(13,true),(5,false),(8,false),(1,true),(10,true),(11,true)],[(6,true),(0,true),(7,false),(2,false),(9,false),(4,false),(12,false)])
                        .empty
                        .empty)))
                  (.node 4070983 ([(0,true),(1,true),(2,true),(9,false),(5,true),(13,false),(12,false)],[(6,true),(7,true),(8,true),(4,false),(3,false),(10,true),(11,true)])
                    (.node 4070761 ([(2,true),(3,true),(13,true),(5,false),(8,true),(0,true),(11,true)],[(6,true),(9,true),(10,true),(1,true),(7,true),(4,false),(12,false)])
                      (.node 4070743 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(12,false)],[(13,false),(4,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        (.node 4068409 ([(2,true),(3,true),(13,true),(5,false),(8,true),(0,false),(11,true)],[(6,true),(10,false),(9,false),(1,true),(7,true),(4,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4070971 ([(2,true),(3,true),(13,true),(5,false),(8,false),(0,true),(11,true)],[(6,true),(7,false),(1,false),(10,false),(9,false),(4,false),(12,false)])
                        .empty
                        .empty))
                    (.node 4071559 ([(2,true),(9,true),(4,false),(13,true),(6,true),(0,true),(11,true)],[(5,false),(10,true),(1,true),(7,true),(8,true),(3,true),(12,false)])
                      (.node 4071511 ([(3,true),(13,true),(5,false),(9,false),(8,false),(0,true),(11,true)],[(6,true),(7,false),(2,false),(1,false),(10,false),(4,false),(12,false)])
                        .empty
                        .empty)
                      (.node 4072255 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(12,false)],[(13,false),(4,true),(7,true),(8,true),(9,true),(10,true),(11,true)])
                        .empty
                        .empty)))))
              (.node 4164446 ([(5,false),(4,false),(3,false),(2,false),(1,false),(0,false),(13,false)],[(6,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                (.node 4080007 ([(1,true),(2,true),(8,true),(6,false),(5,false),(4,false),(12,false)],[(13,false),(3,false),(7,false),(0,false),(9,true),(10,true),(11,true)])
                  (.node 4074631 ([(1,true),(8,false),(4,false),(13,true),(6,true),(10,true),(11,true)],[(5,false),(7,false),(0,false),(9,false),(2,true),(3,true),(12,false)])
                    (.node 4073833 ([(1,true),(2,true),(8,true),(6,false),(5,false),(4,false),(12,false)],[(13,false),(3,false),(7,false),(0,false),(9,true),(10,true),(11,true)])
                      (.node 4072363 ([(1,true),(2,true),(8,true),(9,true),(6,false),(13,false),(12,false)],[(5,false),(4,false),(3,false),(7,false),(0,false),(10,true),(11,true)])
                        (.node 4072351 ([(3,true),(13,true),(5,false),(9,true),(0,true),(1,true),(11,true)],[(6,true),(10,true),(2,true),(7,true),(8,true),(4,false),(12,false)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4073881 ([(0,true),(8,false),(2,false),(10,false),(5,true),(13,false),(12,false)],[(6,true),(7,true),(3,true),(4,true),(9,false),(1,true),(11,true)])
                        .empty
                        .empty))
                    (.node 4075099 ([(0,true),(1,true),(8,true),(5,true),(13,false),(3,false),(11,true)],[(6,true),(7,true),(2,true),(10,false),(9,false),(4,false),(12,false)])
                      (.node 4075087 ([(2,true),(10,false),(0,false),(8,true),(5,true),(13,false),(12,false)],[(6,true),(7,false),(1,false),(9,false),(4,false),(3,false),(11,true)])
                        .empty
                        .empty)
                      (.node 4079791 ([(2,true),(8,false),(0,true),(10,true),(5,true),(13,false),(12,false)],[(6,true),(7,false),(1,false),(9,false),(3,true),(4,true),(11,true)])
                        .empty
                        .empty)))
                  (.node 4163150 ([(5,true),(9,false),(3,true),(11,true),(1,false),(0,false),(13,false)],[(6,false),(10,true),(4,true),(7,true),(8,true),(2,false),(12,true)])
                    (.node 4163066 ([(5,true),(10,true),(3,false),(2,false),(1,false),(0,false),(13,false)],[(6,false),(9,false),(8,false),(7,false),(4,false),(11,true),(12,true)])
                      (.node 4161596 ([(5,true),(8,false),(3,true),(11,true),(1,false),(0,false),(13,false)],[(6,false),(9,true),(10,true),(4,true),(7,true),(2,false),(12,true)])
                        (.node 4161548 ([(5,false),(4,false),(3,false),(2,false),(1,false),(0,false),(13,false)],[(6,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4163078 ([(3,true),(11,true),(1,false),(8,false),(5,true),(6,true),(13,false)],[(0,true),(9,true),(10,true),(4,true),(7,false),(2,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4163870 ([(4,true),(5,true),(8,true),(2,false),(1,false),(0,false),(13,false)],[(6,false),(7,false),(3,false),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4163174 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(13,false)],[(0,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4163918 ([(3,true),(9,true),(1,true),(11,false),(5,true),(6,true),(13,false)],[(0,true),(10,true),(4,false),(8,false),(7,false),(2,false),(12,true)])
                        .empty
                        .empty))))
                (.node 4172396 ([(4,true),(10,true),(11,true),(2,false),(8,false),(6,true),(13,false)],[(0,true),(1,true),(9,true),(5,true),(7,false),(3,false),(12,true)])
                  (.node 4167182 ([(5,true),(11,true),(2,true),(3,true),(9,false),(0,false),(13,false)],[(6,false),(10,false),(4,true),(7,true),(8,true),(1,true),(12,true)])
                    (.node 4164686 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(13,false)],[(0,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4164668 ([(4,true),(5,true),(9,true),(2,false),(1,false),(0,false),(13,false)],[(6,false),(8,false),(7,false),(3,false),(10,true),(11,true),(12,true)])
                        (.node 4164458 ([(4,true),(10,false),(2,false),(1,false),(8,false),(6,true),(13,false)],[(0,true),(9,true),(3,true),(7,true),(5,false),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4167020 ([(4,true),(8,false),(1,true),(2,true),(10,true),(6,true),(13,false)],[(0,true),(7,false),(3,false),(9,false),(5,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4172222 ([(5,true),(8,false),(2,true),(3,true),(10,true),(0,false),(13,false)],[(6,false),(9,true),(4,true),(7,true),(1,false),(11,true),(12,true)])
                      (.node 4167194 ([(3,true),(4,true),(5,true),(11,true),(1,false),(0,false),(13,false)],[(6,false),(10,false),(9,false),(8,false),(7,false),(2,false),(12,true)])
                        .empty
                        .empty)
                      (.node 4172384 ([(5,false),(4,false),(3,false),(2,false),(1,false),(0,false),(13,false)],[(6,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)))
                  (.node 4180808 ([(2,true),(3,true),(4,true),(5,true),(9,true),(0,false),(13,false)],[(6,false),(8,false),(7,false),(1,false),(10,true),(11,true),(12,true)])
                    (.node 4180724 ([(2,true),(3,true),(8,false),(5,false),(10,false),(0,false),(13,false)],[(6,false),(7,false),(1,false),(9,false),(4,true),(11,true),(12,true)])
                      (.node 4180700 ([(5,false),(4,false),(3,false),(2,false),(1,false),(0,false),(13,false)],[(6,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4172810 ([(5,true),(9,false),(8,false),(2,true),(11,false),(0,false),(13,false)],[(6,false),(10,true),(1,true),(7,false),(4,false),(3,false),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4180796 ([(4,true),(11,true),(2,false),(1,false),(9,false),(6,true),(13,false)],[(0,true),(10,true),(5,true),(8,false),(7,false),(3,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4181066 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(13,false)],[(0,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4181036 ([(5,false),(4,false),(3,false),(2,false),(1,false),(0,false),(13,false)],[(6,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4181132 ([(4,true),(11,true),(2,false),(9,false),(8,false),(0,false),(13,false)],[(6,false),(5,false),(10,false),(1,false),(7,false),(3,false),(12,true)])
                        .empty
                        .empty)))))))
          (.node 4320326 ([(3,true),(8,false),(5,false),(11,false),(10,false),(1,false),(13,false)],[(0,false),(6,false),(7,false),(2,false),(9,false),(4,true),(12,true)])
            (.node 4209620 ([(2,true),(3,true),(4,true),(5,true),(9,true),(0,false),(13,false)],[(6,false),(8,false),(7,false),(1,false),(10,true),(11,true),(12,true)])
              (.node 4191962 ([(5,true),(9,false),(3,true),(11,false),(1,false),(0,false),(13,false)],[(6,false),(10,true),(2,true),(8,false),(7,false),(4,false),(12,true)])
                (.node 4189250 ([(2,true),(3,true),(11,false),(10,false),(5,true),(6,true),(13,false)],[(0,true),(1,true),(7,true),(8,true),(9,true),(4,false),(12,true)])
                  (.node 4184000 ([(2,true),(3,true),(9,false),(8,false),(5,true),(6,true),(13,false)],[(0,true),(1,true),(7,true),(4,false),(10,true),(11,true),(12,true)])
                    (.node 4183436 ([(5,true),(11,true),(2,false),(9,false),(8,false),(0,false),(13,false)],[(6,false),(10,false),(1,false),(7,false),(4,false),(3,false),(12,true)])
                      (.node 4183148 ([(4,true),(5,true),(11,true),(2,false),(1,false),(0,false),(13,false)],[(6,false),(10,false),(9,false),(8,false),(7,false),(3,false),(12,true)])
                        (.node 4183100 ([(5,true),(11,true),(2,false),(8,true),(9,true),(0,false),(13,false)],[(6,false),(10,false),(1,true),(7,false),(4,false),(3,false),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4183484 ([(4,true),(5,true),(11,true),(2,false),(1,false),(0,false),(13,false)],[(6,false),(10,false),(9,false),(8,false),(7,false),(3,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4188686 ([(5,true),(8,false),(2,true),(3,true),(11,false),(0,false),(13,false)],[(6,false),(9,true),(10,true),(1,true),(7,false),(4,false),(12,true)])
                      (.node 4188638 ([(5,false),(4,false),(3,false),(2,false),(1,false),(0,false),(13,false)],[(6,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4184048 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(13,false)],[(0,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4189202 ([(3,true),(4,true),(5,true),(8,true),(1,false),(0,false),(13,false)],[(6,false),(7,false),(2,false),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)))
                  (.node 4191620 ([(5,false),(4,false),(3,false),(2,false),(1,false),(0,false),(13,false)],[(6,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                    (.node 4191536 ([(5,false),(4,false),(3,false),(2,false),(1,false),(0,false),(13,false)],[(6,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4189586 ([(2,true),(3,true),(4,true),(5,true),(10,true),(0,false),(13,false)],[(6,false),(9,false),(8,false),(7,false),(1,false),(11,true),(12,true)])
                        (.node 4189538 ([(3,true),(4,true),(8,true),(9,true),(10,true),(0,false),(13,false)],[(6,false),(5,false),(7,false),(2,false),(1,false),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4191554 ([(3,true),(4,true),(10,true),(1,false),(8,false),(6,true),(13,false)],[(0,true),(9,true),(5,true),(7,false),(2,false),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4191878 ([(5,true),(10,true),(11,true),(3,false),(8,true),(0,false),(13,false)],[(6,false),(9,false),(1,true),(2,true),(7,false),(4,false),(12,true)])
                      (.node 4191650 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(13,false)],[(0,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4191890 ([(3,true),(4,true),(5,true),(10,true),(1,false),(0,false),(13,false)],[(6,false),(9,false),(8,false),(7,false),(2,false),(11,true),(12,true)])
                        .empty
                        .empty))))
                (.node 4208000 ([(5,false),(4,false),(3,false),(2,false),(1,false),(0,false),(13,false)],[(6,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                  (.node 4200464 ([(2,true),(3,true),(11,false),(5,false),(8,true),(0,false),(13,false)],[(6,false),(10,false),(9,false),(1,true),(7,true),(4,false),(12,true)])
                    (.node 4200290 ([(3,true),(4,true),(8,false),(1,true),(10,true),(6,true),(13,false)],[(0,true),(7,false),(2,false),(9,false),(5,true),(11,true),(12,true)])
                      (.node 4199876 ([(2,true),(8,false),(4,false),(11,false),(10,false),(0,false),(13,false)],[(6,false),(5,false),(7,false),(1,false),(9,false),(3,true),(12,true)])
                        (.node 4191986 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(13,false)],[(0,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4200302 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(13,false)],[(0,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4205504 ([(2,true),(3,true),(8,true),(5,false),(11,false),(0,false),(13,false)],[(6,false),(9,true),(10,true),(1,true),(7,true),(4,true),(12,true)])
                      (.node 4205492 ([(4,true),(5,true),(8,false),(2,true),(10,true),(0,false),(13,false)],[(6,false),(9,true),(3,true),(7,true),(1,false),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4205666 ([(3,true),(4,true),(5,true),(8,true),(1,false),(0,false),(13,false)],[(6,false),(7,false),(2,false),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)))
                  (.node 4208816 ([(3,true),(4,true),(5,true),(10,true),(1,false),(0,false),(13,false)],[(6,false),(9,false),(8,false),(7,false),(2,false),(11,true),(12,true)])
                    (.node 4208240 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(13,false)],[(0,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4208228 ([(3,true),(4,true),(11,false),(1,false),(8,true),(6,true),(13,false)],[(0,true),(7,false),(2,false),(10,false),(9,false),(5,false),(12,true)])
                        (.node 4208018 ([(3,true),(4,true),(11,false),(1,false),(8,false),(6,true),(13,false)],[(0,true),(9,true),(10,true),(2,true),(7,true),(5,false),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4208768 ([(4,true),(5,true),(10,true),(2,true),(8,false),(0,false),(13,false)],[(6,false),(9,false),(3,true),(7,true),(1,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4209536 ([(2,true),(10,false),(9,false),(4,true),(5,true),(6,true),(13,false)],[(0,true),(1,true),(7,true),(8,true),(3,false),(11,true),(12,true)])
                      (.node 4209512 ([(5,false),(4,false),(3,false),(2,false),(1,false),(0,false),(13,false)],[(6,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4209608 ([(4,true),(5,true),(8,false),(2,true),(10,false),(0,false),(13,false)],[(6,false),(9,true),(1,true),(7,false),(3,false),(11,true),(12,true)])
                        .empty
                        .empty)))))
              (.node 4303550 ([(6,true),(11,true),(3,false),(8,true),(9,true),(1,false),(13,false)],[(0,false),(10,false),(2,true),(7,false),(5,false),(4,false),(12,true)])
                (.node 4298030 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(13,false)],[(1,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                  (.node 4287644 ([(4,true),(5,true),(6,true),(11,true),(2,false),(1,false),(13,false)],[(0,false),(10,false),(9,false),(8,false),(7,false),(3,false),(12,true)])
                    (.node 4287470 ([(5,true),(8,false),(2,true),(3,true),(10,true),(0,true),(13,false)],[(1,true),(7,false),(4,false),(9,false),(6,true),(11,true),(12,true)])
                      (.node 4211138 ([(1,true),(2,true),(3,true),(4,true),(5,true),(6,true),(13,false)],[(0,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4211090 ([(2,true),(10,false),(5,false),(4,false),(8,true),(0,false),(13,false)],[(6,false),(9,false),(1,true),(7,true),(3,false),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4287632 ([(6,true),(11,true),(3,true),(4,true),(9,false),(1,false),(13,false)],[(0,false),(10,false),(5,true),(7,true),(8,true),(2,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4297934 ([(4,true),(11,true),(2,false),(8,false),(6,true),(0,true),(13,false)],[(1,true),(9,true),(10,true),(5,true),(7,false),(3,false),(12,true)])
                      (.node 4297922 ([(6,true),(10,true),(4,false),(3,false),(2,false),(1,false),(13,false)],[(0,false),(9,false),(8,false),(7,false),(5,false),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4298006 ([(6,true),(9,false),(4,true),(11,true),(2,false),(1,false),(13,false)],[(0,false),(10,true),(5,true),(7,true),(8,true),(3,false),(12,true)])
                        .empty
                        .empty)))
                  (.node 4301582 ([(5,true),(6,true),(9,true),(3,false),(2,false),(1,false),(13,false)],[(0,false),(8,false),(7,false),(4,false),(10,true),(11,true),(12,true)])
                    (.node 4301078 ([(5,true),(6,true),(8,true),(3,false),(2,false),(1,false),(13,false)],[(0,false),(7,false),(4,false),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4298798 ([(6,false),(5,false),(4,false),(3,false),(2,false),(1,false),(13,false)],[(0,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4298510 ([(6,true),(8,false),(4,true),(11,true),(2,false),(1,false),(13,false)],[(0,false),(9,true),(10,true),(5,true),(7,true),(3,false),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4301126 ([(4,true),(9,true),(2,true),(11,false),(6,true),(0,true),(13,false)],[(1,true),(10,true),(5,false),(8,false),(7,false),(3,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4301666 ([(5,true),(10,false),(3,false),(2,false),(8,false),(0,true),(13,false)],[(1,true),(9,true),(4,true),(7,true),(6,false),(11,true),(12,true)])
                      (.node 4301600 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(13,false)],[(1,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4301696 ([(6,false),(5,false),(4,false),(3,false),(2,false),(1,false),(13,false)],[(0,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))))
                (.node 4309634 ([(6,false),(5,false),(4,false),(3,false),(2,false),(1,false),(13,false)],[(0,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                  (.node 4304498 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(13,false)],[(1,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                    (.node 4303934 ([(5,true),(6,true),(11,true),(3,false),(2,false),(1,false),(13,false)],[(0,false),(10,false),(9,false),(8,false),(7,false),(4,false),(12,true)])
                      (.node 4303886 ([(6,true),(11,true),(3,false),(9,false),(8,false),(1,false),(13,false)],[(0,false),(10,false),(2,false),(7,false),(5,false),(4,false),(12,true)])
                        (.node 4303598 ([(5,true),(6,true),(11,true),(3,false),(2,false),(1,false),(13,false)],[(0,false),(10,false),(9,false),(8,false),(7,false),(4,false),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4304450 ([(3,true),(4,true),(9,false),(8,false),(6,true),(0,true),(13,false)],[(1,true),(2,true),(7,true),(5,false),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4309136 ([(6,true),(8,false),(3,true),(4,true),(10,true),(1,false),(13,false)],[(0,false),(9,true),(5,true),(7,true),(2,false),(11,true),(12,true)])
                      (.node 4307666 ([(6,true),(9,false),(8,false),(3,true),(11,false),(1,false),(13,false)],[(0,false),(10,true),(2,true),(7,false),(5,false),(4,false),(12,true)])
                        .empty
                        .empty)
                      (.node 4309604 ([(5,true),(10,true),(11,true),(3,false),(8,false),(0,true),(13,false)],[(1,true),(2,true),(9,true),(6,true),(7,false),(4,false),(12,true)])
                        .empty
                        .empty)))
                  (.node 4318046 ([(5,true),(11,true),(3,false),(9,false),(8,false),(1,false),(13,false)],[(0,false),(6,false),(10,false),(2,false),(7,false),(4,false),(12,true)])
                    (.node 4317932 ([(3,true),(4,true),(8,false),(6,false),(10,false),(1,false),(13,false)],[(0,false),(7,false),(2,false),(9,false),(5,true),(11,true),(12,true)])
                      (.node 4317722 ([(3,true),(4,true),(5,true),(6,true),(9,true),(1,false),(13,false)],[(0,false),(8,false),(7,false),(2,false),(10,true),(11,true),(12,true)])
                        (.node 4317710 ([(5,true),(11,true),(3,false),(2,false),(9,false),(0,true),(13,false)],[(1,true),(10,true),(6,true),(8,false),(7,false),(4,false),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4317950 ([(6,false),(5,false),(4,false),(3,false),(2,false),(1,false),(13,false)],[(0,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4318274 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(13,false)],[(1,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4318064 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(13,false)],[(1,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4318286 ([(6,false),(5,false),(4,false),(3,false),(2,false),(1,false),(13,false)],[(0,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))))))
            (.node 4363232 ([(6,true),(0,true),(10,true),(4,true),(8,false),(2,false),(13,false)],[(1,false),(9,false),(5,true),(7,true),(3,true),(11,true),(12,true)])
              (.node 4342406 ([(5,true),(6,true),(8,false),(3,true),(10,true),(1,false),(13,false)],[(0,false),(9,true),(4,true),(7,true),(2,false),(11,true),(12,true)])
                (.node 4326458 ([(3,true),(4,true),(11,false),(10,false),(6,true),(0,true),(13,false)],[(1,true),(2,true),(7,true),(8,true),(9,true),(5,false),(12,true)])
                  (.node 4324442 ([(3,true),(4,true),(5,true),(6,true),(10,true),(1,false),(13,false)],[(0,false),(9,false),(8,false),(7,false),(2,false),(11,true),(12,true)])
                    (.node 4320914 ([(3,true),(4,true),(11,false),(6,false),(8,true),(1,false),(13,false)],[(0,false),(10,false),(9,false),(2,true),(7,true),(5,false),(12,true)])
                      (.node 4320752 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(13,false)],[(1,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4320740 ([(4,true),(5,true),(8,false),(2,true),(10,true),(0,true),(13,false)],[(1,true),(7,false),(3,false),(9,false),(6,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4324394 ([(4,true),(5,true),(8,true),(9,true),(10,true),(1,false),(13,false)],[(0,false),(6,false),(7,false),(3,false),(2,false),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4325888 ([(6,false),(5,false),(4,false),(3,false),(2,false),(1,false),(13,false)],[(0,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4325600 ([(6,true),(8,false),(3,true),(4,true),(11,false),(1,false),(13,false)],[(0,false),(9,true),(10,true),(2,true),(7,false),(5,false),(12,true)])
                        .empty
                        .empty)
                      (.node 4326410 ([(4,true),(5,true),(6,true),(8,true),(2,false),(1,false),(13,false)],[(0,false),(7,false),(3,false),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)))
                  (.node 4328762 ([(4,true),(5,true),(10,true),(2,false),(8,false),(0,true),(13,false)],[(1,true),(9,true),(6,true),(7,false),(3,false),(11,true),(12,true)])
                    (.node 4326818 ([(6,true),(9,false),(4,true),(11,false),(2,false),(1,false),(13,false)],[(0,false),(10,true),(3,true),(8,false),(7,false),(5,false),(12,true)])
                      (.node 4326746 ([(4,true),(5,true),(6,true),(10,true),(2,false),(1,false),(13,false)],[(0,false),(9,false),(8,false),(7,false),(3,false),(11,true),(12,true)])
                        (.node 4326734 ([(6,true),(10,true),(11,true),(4,false),(8,true),(1,false),(13,false)],[(0,false),(9,false),(2,true),(3,true),(7,false),(5,false),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4326842 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(13,false)],[(1,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4328858 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(13,false)],[(1,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4328786 ([(6,false),(5,false),(4,false),(3,false),(2,false),(1,false),(13,false)],[(0,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4328870 ([(6,false),(5,false),(4,false),(3,false),(2,false),(1,false),(13,false)],[(0,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))))
                (.node 4345946 ([(3,true),(10,false),(6,false),(5,false),(8,true),(1,false),(13,false)],[(0,false),(9,false),(2,true),(7,true),(4,false),(11,true),(12,true)])
                  (.node 4345142 ([(4,true),(5,true),(11,false),(2,false),(8,true),(0,true),(13,false)],[(1,true),(7,false),(3,false),(10,false),(9,false),(6,false),(12,true)])
                    (.node 4343624 ([(5,true),(6,true),(10,true),(3,true),(8,false),(1,false),(13,false)],[(0,false),(9,false),(4,true),(7,true),(2,true),(11,true),(12,true)])
                      (.node 4342874 ([(4,true),(5,true),(6,true),(8,true),(2,false),(1,false),(13,false)],[(0,false),(7,false),(3,false),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4342418 ([(3,true),(4,true),(8,true),(6,false),(11,false),(1,false),(13,false)],[(0,false),(9,true),(10,true),(2,true),(7,true),(5,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4343672 ([(4,true),(5,true),(6,true),(10,true),(2,false),(1,false),(13,false)],[(0,false),(9,false),(8,false),(7,false),(3,false),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4345226 ([(4,true),(5,true),(11,false),(2,false),(8,false),(0,true),(13,false)],[(1,true),(9,true),(10,true),(3,true),(7,true),(6,false),(12,true)])
                      (.node 4345154 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(13,false)],[(1,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4345250 ([(6,false),(5,false),(4,false),(3,false),(2,false),(1,false),(13,false)],[(0,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)))
                  (.node 4346762 ([(6,false),(5,false),(4,false),(3,false),(2,false),(1,false),(13,false)],[(0,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                    (.node 4346534 ([(3,true),(4,true),(5,true),(6,true),(9,true),(1,false),(13,false)],[(0,false),(8,false),(7,false),(2,false),(10,true),(11,true),(12,true)])
                      (.node 4346522 ([(5,true),(6,true),(8,false),(3,true),(10,false),(1,false),(13,false)],[(0,false),(9,true),(2,true),(7,false),(4,false),(11,true),(12,true)])
                        (.node 4345994 ([(2,true),(3,true),(4,true),(5,true),(6,true),(0,true),(13,false)],[(1,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4346744 ([(3,true),(10,false),(9,false),(5,true),(6,true),(0,true),(13,false)],[(1,true),(2,true),(7,true),(8,true),(4,false),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4362026 ([(4,true),(5,true),(8,true),(0,false),(11,false),(2,false),(13,false)],[(1,false),(9,true),(10,true),(3,true),(7,true),(6,true),(12,true)])
                      (.node 4362014 ([(6,true),(0,true),(8,false),(4,true),(10,true),(2,false),(13,false)],[(1,false),(9,true),(5,true),(7,true),(3,false),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4362482 ([(5,true),(6,true),(0,true),(8,true),(3,false),(2,false),(13,false)],[(1,false),(7,false),(4,false),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)))))
              (.node 4424384 ([(6,true),(8,false),(3,true),(4,true),(10,true),(1,true),(13,false)],[(2,true),(7,false),(5,false),(9,false),(0,true),(11,true),(12,true)])
                (.node 4366142 ([(4,true),(5,true),(6,true),(0,true),(9,true),(2,false),(13,false)],[(1,false),(8,false),(7,false),(3,false),(10,true),(11,true),(12,true)])
                  (.node 4364858 ([(0,false),(6,false),(5,false),(4,false),(3,false),(2,false),(13,false)],[(1,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                    (.node 4364762 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(13,false)],[(2,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4364750 ([(5,true),(6,true),(11,false),(3,false),(8,true),(1,true),(13,false)],[(2,true),(7,false),(4,false),(10,false),(9,false),(0,false),(12,true)])
                        (.node 4363280 ([(5,true),(6,true),(0,true),(10,true),(3,false),(2,false),(13,false)],[(1,false),(9,false),(8,false),(7,false),(4,false),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4364834 ([(5,true),(6,true),(11,false),(3,false),(8,false),(1,true),(13,false)],[(2,true),(9,true),(10,true),(4,true),(7,true),(0,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4365602 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(13,false)],[(2,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4365554 ([(4,true),(10,false),(0,false),(6,false),(8,true),(2,false),(13,false)],[(1,false),(9,false),(3,true),(7,true),(5,false),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4366130 ([(6,true),(0,true),(8,false),(4,true),(10,false),(2,false),(13,false)],[(1,false),(9,true),(3,true),(7,false),(5,false),(11,true),(12,true)])
                        .empty
                        .empty)))
                  (.node 4422032 ([(6,true),(0,true),(9,true),(4,false),(3,false),(2,false),(13,false)],[(1,false),(8,false),(7,false),(5,false),(10,true),(11,true),(12,true)])
                    (.node 4421528 ([(6,true),(0,true),(8,true),(4,false),(3,false),(2,false),(13,false)],[(1,false),(7,false),(5,false),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4366370 ([(0,false),(6,false),(5,false),(4,false),(3,false),(2,false),(13,false)],[(1,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4366352 ([(4,true),(10,false),(9,false),(6,true),(0,true),(1,true),(13,false)],[(2,true),(3,true),(7,true),(8,true),(5,false),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4421576 ([(5,true),(9,true),(3,true),(11,false),(0,true),(1,true),(13,false)],[(2,true),(10,true),(6,false),(8,false),(7,false),(4,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4422116 ([(6,true),(10,false),(4,false),(3,false),(8,false),(1,true),(13,false)],[(2,true),(9,true),(5,true),(7,true),(0,false),(11,true),(12,true)])
                      (.node 4422050 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(13,false)],[(2,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4422146 ([(0,false),(6,false),(5,false),(4,false),(3,false),(2,false),(13,false)],[(1,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))))
                (.node 4438160 ([(6,true),(11,true),(4,false),(3,false),(9,false),(1,true),(13,false)],[(2,true),(10,true),(0,true),(8,false),(7,false),(5,false),(12,true)])
                  (.node 4435238 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(13,false)],[(2,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                    (.node 4435142 ([(5,true),(11,true),(3,false),(8,false),(0,true),(1,true),(13,false)],[(2,true),(9,true),(10,true),(6,true),(7,false),(4,false),(12,true)])
                      (.node 4424882 ([(0,true),(11,true),(4,true),(5,true),(9,false),(2,false),(13,false)],[(1,false),(10,false),(6,true),(7,true),(8,true),(3,true),(12,true)])
                        (.node 4424852 ([(5,true),(6,true),(0,true),(11,true),(3,false),(2,false),(13,false)],[(1,false),(10,false),(9,false),(8,false),(7,false),(4,false),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4435172 ([(0,true),(10,true),(5,false),(4,false),(3,false),(2,false),(13,false)],[(1,false),(9,false),(8,false),(7,false),(6,false),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4435712 ([(0,false),(6,false),(5,false),(4,false),(3,false),(2,false),(13,false)],[(1,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4435256 ([(0,true),(9,false),(5,true),(11,true),(3,false),(2,false),(13,false)],[(1,false),(10,true),(6,true),(7,true),(8,true),(4,false),(12,true)])
                        .empty
                        .empty)
                      (.node 4435760 ([(0,true),(8,false),(5,true),(11,true),(3,false),(2,false),(13,false)],[(1,false),(9,true),(10,true),(6,true),(7,true),(4,false),(12,true)])
                        .empty
                        .empty)))
                  (.node 4438514 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(13,false)],[(2,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                    (.node 4438400 ([(0,false),(6,false),(5,false),(4,false),(3,false),(2,false),(13,false)],[(1,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4438382 ([(4,true),(5,true),(8,false),(0,false),(10,false),(2,false),(13,false)],[(1,false),(7,false),(3,false),(9,false),(6,true),(11,true),(12,true)])
                        (.node 4438172 ([(4,true),(5,true),(6,true),(0,true),(9,true),(2,false),(13,false)],[(1,false),(8,false),(7,false),(3,false),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4438496 ([(6,true),(11,true),(4,false),(9,false),(8,false),(2,false),(13,false)],[(1,false),(0,false),(10,false),(3,false),(7,false),(5,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4438736 ([(0,false),(6,false),(5,false),(4,false),(3,false),(2,false),(13,false)],[(1,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4438724 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(13,false)],[(2,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4440512 ([(6,true),(0,true),(11,true),(4,false),(3,false),(2,false),(13,false)],[(1,false),(10,false),(9,false),(8,false),(7,false),(5,false),(12,true)])
                        .empty
                        .empty))))))))
        (.node 4692830 ([(2,true),(10,true),(0,false),(6,false),(5,false),(4,false),(13,false)],[(3,false),(9,false),(8,false),(7,false),(1,false),(11,true),(12,true)])
          (.node 4559738 ([(1,true),(11,true),(5,true),(6,true),(9,false),(3,false),(13,false)],[(2,false),(10,false),(0,true),(7,true),(8,true),(4,true),(12,true)])
            (.node 4483226 ([(6,true),(0,true),(10,true),(4,false),(8,false),(2,true),(13,false)],[(3,true),(9,true),(1,true),(7,false),(5,false),(11,true),(12,true)])
              (.node 4463618 ([(5,true),(6,true),(10,true),(3,false),(8,false),(1,true),(13,false)],[(2,true),(9,true),(0,true),(7,false),(4,false),(11,true),(12,true)])
                (.node 4457654 ([(5,true),(6,true),(8,false),(3,true),(10,true),(1,true),(13,false)],[(2,true),(7,false),(4,false),(9,false),(0,true),(11,true),(12,true)])
                  (.node 4444460 ([(6,true),(10,true),(11,true),(4,false),(8,false),(1,true),(13,false)],[(2,true),(3,true),(9,true),(0,true),(7,false),(5,false),(12,true)])
                    (.node 4441658 ([(4,true),(5,true),(9,false),(8,false),(0,true),(1,true),(13,false)],[(2,true),(3,true),(7,true),(6,false),(10,true),(11,true),(12,true)])
                      (.node 4441136 ([(0,true),(11,true),(4,false),(9,false),(8,false),(2,false),(13,false)],[(1,false),(10,false),(3,false),(7,false),(6,false),(5,false),(12,true)])
                        (.node 4440848 ([(6,true),(0,true),(11,true),(4,false),(3,false),(2,false),(13,false)],[(1,false),(10,false),(9,false),(8,false),(7,false),(5,false),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4441706 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(13,false)],[(2,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4446386 ([(0,true),(8,false),(4,true),(5,true),(10,true),(2,false),(13,false)],[(1,false),(9,true),(6,true),(7,true),(3,false),(11,true),(12,true)])
                      (.node 4444916 ([(0,true),(9,false),(8,false),(4,true),(11,false),(2,false),(13,false)],[(1,false),(10,true),(3,true),(7,false),(6,false),(5,false),(12,true)])
                        (.node 4444490 ([(0,false),(6,false),(5,false),(4,false),(3,false),(2,false),(13,false)],[(1,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4457534 ([(4,true),(8,false),(6,false),(11,false),(10,false),(2,false),(13,false)],[(1,false),(0,false),(7,false),(3,false),(9,false),(5,true),(12,true)])
                        .empty
                        .empty)))
                  (.node 4461602 ([(5,true),(6,true),(8,true),(9,true),(10,true),(2,false),(13,false)],[(1,false),(0,false),(7,false),(4,false),(3,false),(11,true),(12,true)])
                    (.node 4461266 ([(5,true),(6,true),(0,true),(8,true),(3,false),(2,false),(13,false)],[(1,false),(7,false),(4,false),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4458122 ([(4,true),(5,true),(11,false),(0,false),(8,true),(2,false),(13,false)],[(1,false),(10,false),(9,false),(3,true),(7,true),(6,false),(12,true)])
                        (.node 4457666 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(13,false)],[(2,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4461314 ([(4,true),(5,true),(11,false),(10,false),(0,true),(1,true),(13,false)],[(2,true),(3,true),(7,true),(8,true),(9,true),(6,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4462802 ([(0,false),(6,false),(5,false),(4,false),(3,false),(2,false),(13,false)],[(1,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4461650 ([(4,true),(5,true),(6,true),(0,true),(10,true),(2,false),(13,false)],[(1,false),(9,false),(8,false),(7,false),(3,false),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4462850 ([(0,true),(8,false),(4,true),(5,true),(11,false),(2,false),(13,false)],[(1,false),(9,true),(10,true),(3,true),(7,false),(6,false),(12,true)])
                        .empty
                        .empty))))
                (.node 4477262 ([(6,true),(0,true),(8,false),(4,true),(10,true),(2,true),(13,false)],[(3,true),(7,false),(5,false),(9,false),(1,true),(11,true),(12,true)])
                  (.node 4463984 ([(0,true),(10,true),(11,true),(5,false),(8,true),(2,false),(13,false)],[(1,false),(9,false),(3,true),(4,true),(7,false),(6,false),(12,true)])
                    (.node 4463726 ([(0,false),(6,false),(5,false),(4,false),(3,false),(2,false),(13,false)],[(1,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4463714 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(13,false)],[(2,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4463642 ([(0,false),(6,false),(5,false),(4,false),(3,false),(2,false),(13,false)],[(1,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4463954 ([(5,true),(6,true),(0,true),(10,true),(3,false),(2,false),(13,false)],[(1,false),(9,false),(8,false),(7,false),(4,false),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4464068 ([(0,true),(9,false),(5,true),(11,false),(3,false),(2,false),(13,false)],[(1,false),(10,true),(4,true),(8,false),(7,false),(6,false),(12,true)])
                      (.node 4464050 ([(3,true),(4,true),(5,true),(6,true),(0,true),(1,true),(13,false)],[(2,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4477142 ([(5,true),(8,false),(0,false),(11,false),(10,false),(3,false),(13,false)],[(2,false),(1,false),(7,false),(4,false),(9,false),(6,true),(12,true)])
                        .empty
                        .empty)))
                  (.node 4481210 ([(6,true),(0,true),(8,true),(9,true),(10,true),(3,false),(13,false)],[(2,false),(1,false),(7,false),(5,false),(4,false),(11,true),(12,true)])
                    (.node 4480874 ([(6,true),(0,true),(1,true),(8,true),(4,false),(3,false),(13,false)],[(2,false),(7,false),(5,false),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4477730 ([(5,true),(6,true),(11,false),(1,false),(8,true),(3,false),(13,false)],[(2,false),(10,false),(9,false),(4,true),(7,true),(0,false),(12,true)])
                        (.node 4477274 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(13,false)],[(3,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4480922 ([(5,true),(6,true),(11,false),(10,false),(1,true),(2,true),(13,false)],[(3,true),(4,true),(7,true),(8,true),(9,true),(0,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4482410 ([(1,false),(0,false),(6,false),(5,false),(4,false),(3,false),(13,false)],[(2,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4481258 ([(5,true),(6,true),(0,true),(1,true),(10,true),(3,false),(13,false)],[(2,false),(9,false),(8,false),(7,false),(4,false),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4482458 ([(1,true),(8,false),(5,true),(6,true),(11,false),(3,false),(13,false)],[(2,false),(9,true),(10,true),(4,true),(7,false),(0,false),(12,true)])
                        .empty
                        .empty)))))
              (.node 4502810 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(13,false)],[(3,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                (.node 4499234 ([(5,true),(6,true),(8,true),(1,false),(11,false),(3,false),(13,false)],[(2,false),(9,true),(10,true),(4,true),(7,true),(0,true),(12,true)])
                  (.node 4483592 ([(1,true),(10,true),(11,true),(6,false),(8,true),(3,false),(13,false)],[(2,false),(9,false),(4,true),(5,true),(7,false),(0,false),(12,true)])
                    (.node 4483334 ([(1,false),(0,false),(6,false),(5,false),(4,false),(3,false),(13,false)],[(2,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4483322 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(13,false)],[(3,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4483250 ([(1,false),(0,false),(6,false),(5,false),(4,false),(3,false),(13,false)],[(2,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4483562 ([(6,true),(0,true),(1,true),(10,true),(4,false),(3,false),(13,false)],[(2,false),(9,false),(8,false),(7,false),(5,false),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4483676 ([(1,true),(9,false),(6,true),(11,false),(4,false),(3,false),(13,false)],[(2,false),(10,true),(5,true),(8,false),(7,false),(0,false),(12,true)])
                      (.node 4483658 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(13,false)],[(3,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4497338 ([(6,true),(0,true),(1,true),(8,true),(4,false),(3,false),(13,false)],[(2,false),(7,false),(5,false),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)))
                  (.node 4499714 ([(1,false),(0,false),(6,false),(5,false),(4,false),(3,false),(13,false)],[(2,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                    (.node 4499618 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(13,false)],[(3,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4499606 ([(6,true),(0,true),(11,false),(4,false),(8,true),(2,true),(13,false)],[(3,true),(7,false),(5,false),(10,false),(9,false),(1,false),(12,true)])
                        (.node 4499264 ([(0,true),(1,true),(8,false),(5,true),(10,true),(3,false),(13,false)],[(2,false),(9,true),(6,true),(7,true),(4,false),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4499690 ([(6,true),(0,true),(11,false),(4,false),(8,false),(2,true),(13,false)],[(3,true),(9,true),(10,true),(5,true),(7,true),(1,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4500482 ([(0,true),(1,true),(10,true),(5,true),(8,false),(3,false),(13,false)],[(2,false),(9,false),(6,true),(7,true),(4,true),(11,true),(12,true)])
                      (.node 4500194 ([(6,true),(0,true),(1,true),(10,true),(4,false),(3,false),(13,false)],[(2,false),(9,false),(8,false),(7,false),(5,false),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4502762 ([(5,true),(10,false),(1,false),(0,false),(8,true),(3,false),(13,false)],[(2,false),(9,false),(4,true),(7,true),(6,false),(11,true),(12,true)])
                        .empty
                        .empty))))
                (.node 4556162 ([(1,false),(0,false),(6,false),(5,false),(4,false),(3,false),(13,false)],[(2,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                  (.node 4555592 ([(6,true),(11,true),(4,false),(8,false),(1,true),(2,true),(13,false)],[(3,true),(9,true),(10,true),(0,true),(7,false),(5,false),(12,true)])
                    (.node 4503350 ([(5,true),(6,true),(0,true),(1,true),(9,true),(3,false),(13,false)],[(2,false),(8,false),(7,false),(4,false),(10,true),(11,true),(12,true)])
                      (.node 4503284 ([(1,false),(0,false),(6,false),(5,false),(4,false),(3,false),(13,false)],[(2,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4503266 ([(5,true),(10,false),(9,false),(0,true),(1,true),(2,true),(13,false)],[(3,true),(4,true),(7,true),(8,true),(6,false),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4503380 ([(0,true),(1,true),(8,false),(5,true),(10,false),(3,false),(13,false)],[(2,false),(9,true),(4,true),(7,false),(6,false),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4555688 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(13,false)],[(3,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4555622 ([(1,true),(10,true),(6,false),(5,false),(4,false),(3,false),(13,false)],[(2,false),(9,false),(8,false),(7,false),(0,false),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4555706 ([(1,true),(9,false),(6,true),(11,true),(4,false),(3,false),(13,false)],[(2,false),(10,true),(0,true),(7,true),(8,true),(5,false),(12,true)])
                        .empty
                        .empty)))
                  (.node 4559282 ([(0,true),(1,true),(9,true),(5,false),(4,false),(3,false),(13,false)],[(2,false),(8,false),(7,false),(6,false),(10,true),(11,true),(12,true)])
                    (.node 4558778 ([(0,true),(1,true),(8,true),(5,false),(4,false),(3,false),(13,false)],[(2,false),(7,false),(6,false),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4558490 ([(6,true),(9,true),(4,true),(11,false),(1,true),(2,true),(13,false)],[(3,true),(10,true),(0,false),(8,false),(7,false),(5,false),(12,true)])
                        (.node 4556210 ([(1,true),(8,false),(6,true),(11,true),(4,false),(3,false),(13,false)],[(2,false),(9,true),(10,true),(0,true),(7,true),(5,false),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4559258 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(13,false)],[(3,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4559366 ([(0,true),(10,false),(5,false),(4,false),(8,false),(2,true),(13,false)],[(3,true),(9,true),(6,true),(7,true),(1,false),(11,true),(12,true)])
                      (.node 4559354 ([(1,false),(0,false),(6,false),(5,false),(4,false),(3,false),(13,false)],[(2,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4559708 ([(6,true),(0,true),(1,true),(11,true),(4,false),(3,false),(13,false)],[(2,false),(10,false),(9,false),(8,false),(7,false),(5,false),(12,true)])
                        .empty
                        .empty))))))
            (.node 4601438 ([(2,true),(9,false),(8,false),(6,true),(11,false),(4,false),(13,false)],[(3,false),(10,true),(5,true),(7,false),(1,false),(0,false),(12,true)])
              (.node 4581830 ([(1,true),(9,false),(8,false),(5,true),(11,false),(3,false),(13,false)],[(2,false),(10,true),(4,true),(7,false),(0,false),(6,false),(12,true)])
                (.node 4576514 ([(5,true),(6,true),(9,false),(8,false),(1,true),(2,true),(13,false)],[(3,true),(4,true),(7,true),(0,false),(10,true),(11,true),(12,true)])
                  (.node 4575410 ([(0,true),(11,true),(5,false),(4,false),(9,false),(2,true),(13,false)],[(3,true),(10,true),(1,true),(8,false),(7,false),(6,false),(12,true)])
                    (.node 4575314 ([(1,false),(0,false),(6,false),(5,false),(4,false),(3,false),(13,false)],[(2,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4575296 ([(5,true),(6,true),(8,false),(1,false),(10,false),(3,false),(13,false)],[(2,false),(7,false),(4,false),(9,false),(0,true),(11,true),(12,true)])
                        (.node 4561634 ([(0,true),(8,false),(4,true),(5,true),(10,true),(2,true),(13,false)],[(3,true),(7,false),(6,false),(9,false),(1,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4575380 ([(5,true),(6,true),(0,true),(1,true),(9,true),(3,false),(13,false)],[(2,false),(8,false),(7,false),(4,false),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4575722 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(13,false)],[(3,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4575650 ([(1,false),(0,false),(6,false),(5,false),(4,false),(3,false),(13,false)],[(2,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4575638 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(13,false)],[(3,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4575746 ([(0,true),(11,true),(5,false),(9,false),(8,false),(3,false),(13,false)],[(2,false),(1,false),(10,false),(4,false),(7,false),(6,false),(12,true)])
                        .empty
                        .empty)))
                  (.node 4578098 ([(0,true),(1,true),(11,true),(5,false),(4,false),(3,false),(13,false)],[(2,false),(10,false),(9,false),(8,false),(7,false),(6,false),(12,true)])
                    (.node 4577762 ([(0,true),(1,true),(11,true),(5,false),(4,false),(3,false),(13,false)],[(2,false),(10,false),(9,false),(8,false),(7,false),(6,false),(12,true)])
                      (.node 4577714 ([(1,true),(11,true),(5,false),(8,true),(9,true),(3,false),(13,false)],[(2,false),(10,false),(4,true),(7,false),(0,false),(6,false),(12,true)])
                        (.node 4576562 ([(4,true),(5,true),(6,true),(0,true),(1,true),(2,true),(13,false)],[(3,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4578050 ([(1,true),(11,true),(5,false),(9,false),(8,false),(3,false),(13,false)],[(2,false),(10,false),(4,false),(7,false),(0,false),(6,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4581698 ([(1,false),(0,false),(6,false),(5,false),(4,false),(3,false),(13,false)],[(2,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4581242 ([(1,true),(8,false),(5,true),(6,true),(10,true),(3,false),(13,false)],[(2,false),(9,true),(0,true),(7,true),(4,false),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4581710 ([(0,true),(10,true),(11,true),(5,false),(8,false),(2,true),(13,false)],[(3,true),(4,true),(9,true),(1,true),(7,false),(6,false),(12,true)])
                        .empty
                        .empty))))
                (.node 4596122 ([(6,true),(0,true),(9,false),(8,false),(2,true),(3,true),(13,false)],[(4,true),(5,true),(7,true),(1,false),(10,true),(11,true),(12,true)])
                  (.node 4595246 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(13,false)],[(4,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                    (.node 4594988 ([(6,true),(0,true),(1,true),(2,true),(9,true),(4,false),(13,false)],[(3,false),(8,false),(7,false),(5,false),(10,true),(11,true),(12,true)])
                      (.node 4594922 ([(2,false),(1,false),(0,false),(6,false),(5,false),(4,false),(13,false)],[(3,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4594904 ([(6,true),(0,true),(8,false),(2,false),(10,false),(4,false),(13,false)],[(3,false),(7,false),(5,false),(9,false),(1,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4595018 ([(1,true),(11,true),(6,false),(5,false),(9,false),(3,true),(13,false)],[(4,true),(10,true),(2,true),(8,false),(7,false),(0,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4595330 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(13,false)],[(4,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4595258 ([(2,false),(1,false),(0,false),(6,false),(5,false),(4,false),(13,false)],[(3,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4595354 ([(1,true),(11,true),(6,false),(9,false),(8,false),(4,false),(13,false)],[(3,false),(2,false),(10,false),(5,false),(7,false),(0,false),(12,true)])
                        .empty
                        .empty)))
                  (.node 4597706 ([(1,true),(2,true),(11,true),(6,false),(5,false),(4,false),(13,false)],[(3,false),(10,false),(9,false),(8,false),(7,false),(0,false),(12,true)])
                    (.node 4597370 ([(1,true),(2,true),(11,true),(6,false),(5,false),(4,false),(13,false)],[(3,false),(10,false),(9,false),(8,false),(7,false),(0,false),(12,true)])
                      (.node 4597322 ([(2,true),(11,true),(6,false),(8,true),(9,true),(4,false),(13,false)],[(3,false),(10,false),(5,true),(7,false),(1,false),(0,false),(12,true)])
                        (.node 4596170 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(13,false)],[(4,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4597658 ([(2,true),(11,true),(6,false),(9,false),(8,false),(4,false),(13,false)],[(3,false),(10,false),(5,false),(7,false),(1,false),(0,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4601306 ([(2,false),(1,false),(0,false),(6,false),(5,false),(4,false),(13,false)],[(3,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4600850 ([(2,true),(8,false),(6,true),(0,true),(10,true),(4,false),(13,false)],[(3,false),(9,true),(1,true),(7,true),(5,false),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4601318 ([(1,true),(10,true),(11,true),(6,false),(8,false),(3,true),(13,false)],[(4,true),(5,true),(9,true),(2,true),(7,false),(0,false),(12,true)])
                        .empty
                        .empty)))))
              (.node 4620812 ([(0,true),(1,true),(2,true),(10,true),(5,false),(4,false),(13,false)],[(3,false),(9,false),(8,false),(7,false),(6,false),(11,true),(12,true)])
                (.node 4618172 ([(6,true),(0,true),(1,true),(2,true),(10,true),(4,false),(13,false)],[(3,false),(9,false),(8,false),(7,false),(5,false),(11,true),(12,true)])
                  (.node 4617266 ([(2,false),(1,false),(0,false),(6,false),(5,false),(4,false),(13,false)],[(3,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                    (.node 4614482 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(13,false)],[(4,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4614056 ([(6,true),(8,false),(1,false),(11,false),(10,false),(4,false),(13,false)],[(3,false),(2,false),(7,false),(5,false),(9,false),(0,true),(12,true)])
                        (.node 4612586 ([(6,true),(0,true),(11,false),(2,false),(8,true),(4,false),(13,false)],[(3,false),(10,false),(9,false),(5,true),(7,true),(1,false),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4614512 ([(0,true),(1,true),(8,false),(5,true),(10,true),(3,true),(13,false)],[(4,true),(7,false),(6,false),(9,false),(2,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4617836 ([(6,true),(0,true),(11,false),(10,false),(2,true),(3,true),(13,false)],[(4,true),(5,true),(7,true),(8,true),(9,true),(1,false),(12,true)])
                      (.node 4617314 ([(2,true),(8,false),(6,true),(0,true),(11,false),(4,false),(13,false)],[(3,false),(9,true),(10,true),(5,true),(7,false),(1,false),(12,true)])
                        .empty
                        .empty)
                      (.node 4618124 ([(0,true),(1,true),(2,true),(8,true),(5,false),(4,false),(13,false)],[(3,false),(7,false),(6,false),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)))
                  (.node 4620476 ([(0,true),(1,true),(10,true),(5,false),(8,false),(3,true),(13,false)],[(4,true),(9,true),(2,true),(7,false),(6,false),(11,true),(12,true)])
                    (.node 4620248 ([(2,false),(1,false),(0,false),(6,false),(5,false),(4,false),(13,false)],[(3,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4620236 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(13,false)],[(4,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4618460 ([(0,true),(1,true),(8,true),(9,true),(10,true),(4,false),(13,false)],[(3,false),(2,false),(7,false),(6,false),(5,false),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4620458 ([(2,false),(1,false),(0,false),(6,false),(5,false),(4,false),(13,false)],[(3,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4620590 ([(2,true),(9,false),(0,true),(11,false),(5,false),(4,false),(13,false)],[(3,false),(10,true),(6,true),(8,false),(7,false),(1,false),(12,true)])
                      (.node 4620572 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(13,false)],[(4,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4620800 ([(2,true),(10,true),(11,true),(0,false),(8,true),(4,false),(13,false)],[(3,false),(9,false),(5,true),(6,true),(7,false),(1,false),(12,true)])
                        .empty
                        .empty))))
                (.node 4634588 ([(0,true),(1,true),(2,true),(8,true),(5,false),(4,false),(13,false)],[(3,false),(7,false),(6,false),(9,true),(10,true),(11,true),(12,true)])
                  (.node 4623800 ([(6,true),(0,true),(1,true),(2,true),(9,true),(4,false),(13,false)],[(3,false),(8,false),(7,false),(5,false),(10,true),(11,true),(12,true)])
                    (.node 4623716 ([(6,true),(10,false),(9,false),(1,true),(2,true),(3,true),(13,false)],[(4,true),(5,true),(7,true),(8,true),(0,false),(11,true),(12,true)])
                      (.node 4623260 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(13,false)],[(4,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4623212 ([(6,true),(10,false),(2,false),(1,false),(8,true),(4,false),(13,false)],[(3,false),(9,false),(5,true),(7,true),(0,false),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4623734 ([(2,false),(1,false),(0,false),(6,false),(5,false),(4,false),(13,false)],[(3,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4634090 ([(6,true),(0,true),(8,true),(2,false),(11,false),(4,false),(13,false)],[(3,false),(9,true),(10,true),(5,true),(7,true),(1,true),(12,true)])
                      (.node 4623830 ([(1,true),(2,true),(8,false),(6,true),(10,false),(4,false),(13,false)],[(3,false),(9,true),(5,true),(7,false),(0,false),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4634120 ([(1,true),(2,true),(8,false),(6,true),(10,true),(4,false),(13,false)],[(3,false),(9,true),(0,true),(7,true),(5,false),(11,true),(12,true)])
                        .empty
                        .empty)))
                  (.node 4637396 ([(1,true),(2,true),(10,true),(6,true),(8,false),(4,false),(13,false)],[(3,false),(9,false),(0,true),(7,true),(5,true),(11,true),(12,true)])
                    (.node 4636922 ([(2,false),(1,false),(0,false),(6,false),(5,false),(4,false),(13,false)],[(3,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4636856 ([(0,true),(1,true),(11,false),(5,false),(8,true),(3,true),(13,false)],[(4,true),(7,false),(6,false),(10,false),(9,false),(2,false),(12,true)])
                        (.node 4636826 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(13,false)],[(4,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4636940 ([(0,true),(1,true),(11,false),(5,false),(8,false),(3,true),(13,false)],[(4,true),(9,true),(10,true),(6,true),(7,true),(2,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4692602 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(13,false)],[(4,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4637444 ([(0,true),(1,true),(2,true),(10,true),(5,false),(4,false),(13,false)],[(3,false),(9,false),(8,false),(7,false),(6,false),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4692620 ([(2,true),(9,false),(0,true),(11,true),(5,false),(4,false),(13,false)],[(3,false),(10,true),(1,true),(7,true),(8,true),(6,false),(12,true)])
                        .empty
                        .empty)))))))
          (.node 4760966 ([(0,true),(10,false),(9,false),(2,true),(3,true),(4,true),(13,false)],[(5,true),(6,true),(7,true),(8,true),(1,false),(11,true),(12,true)])
            (.node 4732562 ([(2,true),(3,true),(11,true),(0,false),(6,false),(5,false),(13,false)],[(4,false),(10,false),(9,false),(8,false),(7,false),(1,false),(12,true)])
              (.node 4713722 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(13,false)],[(5,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                (.node 4696490 ([(1,true),(8,false),(5,true),(6,true),(10,true),(3,true),(13,false)],[(4,true),(7,false),(0,false),(9,false),(2,true),(11,true),(12,true)])
                  (.node 4694138 ([(1,true),(2,true),(9,true),(6,false),(5,false),(4,false),(13,false)],[(3,false),(8,false),(7,false),(0,false),(10,true),(11,true),(12,true)])
                    (.node 4693418 ([(2,true),(8,false),(0,true),(11,true),(5,false),(4,false),(13,false)],[(3,false),(9,true),(10,true),(1,true),(7,true),(6,false),(12,true)])
                      (.node 4693370 ([(2,false),(1,false),(0,false),(6,false),(5,false),(4,false),(13,false)],[(3,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4692842 ([(0,true),(11,true),(5,false),(8,false),(2,true),(3,true),(13,false)],[(4,true),(9,true),(10,true),(1,true),(7,false),(6,false),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4694114 ([(5,true),(6,true),(0,true),(1,true),(2,true),(3,true),(13,false)],[(4,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4695692 ([(1,true),(2,true),(8,true),(6,false),(5,false),(4,false),(13,false)],[(3,false),(7,false),(0,false),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4694222 ([(1,true),(10,false),(6,false),(5,false),(8,false),(3,true),(13,false)],[(4,true),(9,true),(0,true),(7,true),(2,false),(11,true),(12,true)])
                        (.node 4694210 ([(2,false),(1,false),(0,false),(6,false),(5,false),(4,false),(13,false)],[(3,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4695740 ([(0,true),(9,true),(5,true),(11,false),(2,true),(3,true),(13,false)],[(4,true),(10,true),(1,false),(8,false),(7,false),(6,false),(12,true)])
                        .empty
                        .empty)))
                  (.node 4712438 ([(3,true),(10,true),(1,false),(0,false),(6,false),(5,false),(13,false)],[(4,false),(9,false),(8,false),(7,false),(2,false),(11,true),(12,true)])
                    (.node 4712210 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(13,false)],[(5,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4696958 ([(0,true),(1,true),(2,true),(11,true),(5,false),(4,false),(13,false)],[(3,false),(10,false),(9,false),(8,false),(7,false),(6,false),(12,true)])
                        (.node 4696946 ([(2,true),(11,true),(6,true),(0,true),(9,false),(4,false),(13,false)],[(3,false),(10,false),(1,true),(7,true),(8,true),(5,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4712228 ([(3,true),(9,false),(1,true),(11,true),(6,false),(5,false),(13,false)],[(4,false),(10,true),(2,true),(7,true),(8,true),(0,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4712978 ([(3,false),(2,false),(1,false),(0,false),(6,false),(5,false),(13,false)],[(4,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4712450 ([(1,true),(11,true),(6,false),(8,false),(3,true),(4,true),(13,false)],[(5,true),(9,true),(10,true),(2,true),(7,false),(0,false),(12,true)])
                        .empty
                        .empty)
                      (.node 4713026 ([(3,true),(8,false),(1,true),(11,true),(6,false),(5,false),(13,false)],[(4,false),(9,true),(10,true),(2,true),(7,true),(0,false),(12,true)])
                        .empty
                        .empty))))
                (.node 4730102 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(13,false)],[(5,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                  (.node 4715348 ([(1,true),(9,true),(6,true),(11,false),(3,true),(4,true),(13,false)],[(5,true),(10,true),(2,false),(8,false),(7,false),(0,false),(12,true)])
                    (.node 4713830 ([(2,true),(10,false),(0,false),(6,false),(8,false),(4,true),(13,false)],[(5,true),(9,true),(1,true),(7,true),(3,false),(11,true),(12,true)])
                      (.node 4713818 ([(3,false),(2,false),(1,false),(0,false),(6,false),(5,false),(13,false)],[(4,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4713746 ([(2,true),(3,true),(9,true),(0,false),(6,false),(5,false),(13,false)],[(4,false),(8,false),(7,false),(1,false),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4715300 ([(2,true),(3,true),(8,true),(0,false),(6,false),(5,false),(13,false)],[(4,false),(7,false),(1,false),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4716554 ([(3,true),(11,true),(0,true),(1,true),(9,false),(5,false),(13,false)],[(4,false),(10,false),(2,true),(7,true),(8,true),(6,true),(12,true)])
                      (.node 4716098 ([(2,true),(8,false),(6,true),(0,true),(10,true),(4,true),(13,false)],[(5,true),(7,false),(1,false),(9,false),(3,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4716566 ([(1,true),(2,true),(3,true),(11,true),(6,false),(5,false),(13,false)],[(4,false),(10,false),(9,false),(8,false),(7,false),(0,false),(12,true)])
                        .empty
                        .empty)))
                  (.node 4732154 ([(0,true),(1,true),(8,false),(3,false),(10,false),(5,false),(13,false)],[(4,false),(7,false),(6,false),(9,false),(2,true),(11,true),(12,true)])
                    (.node 4730210 ([(2,true),(11,true),(0,false),(9,false),(8,false),(5,false),(13,false)],[(4,false),(3,false),(10,false),(6,false),(7,false),(1,false),(12,true)])
                      (.node 4730186 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(13,false)],[(5,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4730114 ([(3,false),(2,false),(1,false),(0,false),(6,false),(5,false),(13,false)],[(4,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4732130 ([(3,false),(2,false),(1,false),(0,false),(6,false),(5,false),(13,false)],[(4,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4732238 ([(0,true),(1,true),(2,true),(3,true),(9,true),(5,false),(13,false)],[(4,false),(8,false),(7,false),(6,false),(10,true),(11,true),(12,true)])
                      (.node 4732226 ([(2,true),(11,true),(0,false),(6,false),(9,false),(4,true),(13,false)],[(5,true),(10,true),(3,true),(8,false),(7,false),(1,false),(12,true)])
                        .empty
                        .empty)
                      (.node 4732514 ([(3,true),(11,true),(0,false),(9,false),(8,false),(5,false),(13,false)],[(4,false),(10,false),(6,false),(7,false),(2,false),(1,false),(12,true)])
                        .empty
                        .empty)))))
              (.node 4749368 ([(1,true),(2,true),(8,false),(6,true),(10,true),(4,true),(13,false)],[(5,true),(7,false),(0,false),(9,false),(3,true),(11,true),(12,true)])
                (.node 4740686 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(13,false)],[(5,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                  (.node 4738058 ([(3,true),(8,false),(0,true),(1,true),(10,true),(5,false),(13,false)],[(4,false),(9,true),(2,true),(7,true),(6,false),(11,true),(12,true)])
                    (.node 4734530 ([(3,true),(11,true),(0,false),(8,true),(9,true),(5,false),(13,false)],[(4,false),(10,false),(6,true),(7,false),(2,false),(1,false),(12,true)])
                      (.node 4733372 ([(0,true),(1,true),(9,false),(8,false),(3,true),(4,true),(13,false)],[(5,true),(6,true),(7,true),(2,false),(10,true),(11,true),(12,true)])
                        (.node 4733084 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(13,false)],[(5,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4734578 ([(2,true),(3,true),(11,true),(0,false),(6,false),(5,false),(13,false)],[(4,false),(10,false),(9,false),(8,false),(7,false),(1,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4738232 ([(2,true),(10,true),(11,true),(0,false),(8,false),(4,true),(13,false)],[(5,true),(6,true),(9,true),(3,true),(7,false),(1,false),(12,true)])
                      (.node 4738220 ([(3,false),(2,false),(1,false),(0,false),(6,false),(5,false),(13,false)],[(4,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4738646 ([(3,true),(9,false),(8,false),(0,true),(11,false),(5,false),(13,false)],[(4,false),(10,true),(6,true),(7,false),(2,false),(1,false),(12,true)])
                        .empty
                        .empty)))
                  (.node 4741040 ([(3,true),(9,false),(1,true),(11,false),(6,false),(5,false),(13,false)],[(4,false),(10,true),(0,true),(8,false),(7,false),(2,false),(12,true)])
                    (.node 4740926 ([(1,true),(2,true),(10,true),(6,false),(8,false),(4,true),(13,false)],[(5,true),(9,true),(3,true),(7,false),(0,false),(11,true),(12,true)])
                      (.node 4740908 ([(3,false),(2,false),(1,false),(0,false),(6,false),(5,false),(13,false)],[(4,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4740698 ([(3,false),(2,false),(1,false),(0,false),(6,false),(5,false),(13,false)],[(4,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4741022 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(13,false)],[(5,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4741262 ([(1,true),(2,true),(3,true),(10,true),(6,false),(5,false),(13,false)],[(4,false),(9,false),(8,false),(7,false),(0,false),(11,true),(12,true)])
                      (.node 4741250 ([(3,true),(10,true),(11,true),(1,false),(8,true),(5,false),(13,false)],[(4,false),(9,false),(6,true),(0,true),(7,false),(2,false),(12,true)])
                        .empty
                        .empty)
                      (.node 4749338 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(13,false)],[(5,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))))
                (.node 4757276 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(13,false)],[(5,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                  (.node 4755038 ([(1,true),(2,true),(3,true),(8,true),(6,false),(5,false),(13,false)],[(4,false),(7,false),(0,false),(9,true),(10,true),(11,true),(12,true)])
                    (.node 4754474 ([(3,false),(2,false),(1,false),(0,false),(6,false),(5,false),(13,false)],[(4,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4751306 ([(0,true),(8,false),(2,false),(11,false),(10,false),(5,false),(13,false)],[(4,false),(3,false),(7,false),(6,false),(9,false),(1,true),(12,true)])
                        (.node 4749836 ([(0,true),(1,true),(11,false),(3,false),(8,true),(5,false),(13,false)],[(4,false),(10,false),(9,false),(6,true),(7,true),(2,false),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4754522 ([(3,true),(8,false),(0,true),(1,true),(11,false),(5,false),(13,false)],[(4,false),(9,true),(10,true),(6,true),(7,false),(2,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4755374 ([(1,true),(2,true),(8,true),(9,true),(10,true),(5,false),(13,false)],[(4,false),(3,false),(7,false),(0,false),(6,false),(11,true),(12,true)])
                      (.node 4755086 ([(0,true),(1,true),(11,false),(10,false),(3,true),(4,true),(13,false)],[(5,true),(6,true),(7,true),(8,true),(9,true),(2,false),(12,true)])
                        .empty
                        .empty)
                      (.node 4755422 ([(0,true),(1,true),(2,true),(3,true),(10,true),(5,false),(13,false)],[(4,false),(9,false),(8,false),(7,false),(6,false),(11,true),(12,true)])
                        .empty
                        .empty)))
                  (.node 4757894 ([(1,true),(2,true),(3,true),(10,true),(6,false),(5,false),(13,false)],[(4,false),(9,false),(8,false),(7,false),(0,false),(11,true),(12,true)])
                    (.node 4757390 ([(1,true),(2,true),(11,false),(6,false),(8,false),(4,true),(13,false)],[(5,true),(9,true),(10,true),(0,true),(7,true),(3,false),(12,true)])
                      (.node 4757372 ([(3,false),(2,false),(1,false),(0,false),(6,false),(5,false),(13,false)],[(4,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4757306 ([(1,true),(2,true),(11,false),(6,false),(8,true),(4,true),(13,false)],[(5,true),(7,false),(0,false),(10,false),(9,false),(3,false),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4757846 ([(2,true),(3,true),(10,true),(0,true),(8,false),(5,false),(13,false)],[(4,false),(9,false),(1,true),(7,true),(6,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4760462 ([(0,true),(10,false),(3,false),(2,false),(8,true),(5,false),(13,false)],[(4,false),(9,false),(6,true),(7,true),(1,false),(11,true),(12,true)])
                      (.node 4760174 ([(6,true),(0,true),(1,true),(2,true),(3,true),(4,true),(13,false)],[(5,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4760942 ([(3,false),(2,false),(1,false),(0,false),(6,false),(5,false),(13,false)],[(4,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))))))
            (.node 4869770 ([(3,true),(4,true),(11,true),(1,false),(0,false),(6,false),(13,false)],[(5,false),(10,false),(9,false),(8,false),(7,false),(2,false),(12,true)])
              (.node 4853306 ([(3,true),(8,false),(0,true),(1,true),(10,true),(5,true),(13,false)],[(6,true),(7,false),(2,false),(9,false),(4,true),(11,true),(12,true)])
                (.node 4849364 ([(2,true),(11,true),(0,false),(8,false),(4,true),(5,true),(13,false)],[(6,true),(9,true),(10,true),(3,true),(7,false),(1,false),(12,true)])
                  (.node 4771502 ([(1,true),(2,true),(3,true),(8,true),(6,false),(5,false),(13,false)],[(4,false),(7,false),(0,false),(9,true),(10,true),(11,true),(12,true)])
                    (.node 4771328 ([(2,true),(3,true),(8,false),(0,true),(10,true),(5,false),(13,false)],[(4,false),(9,true),(1,true),(7,true),(6,false),(11,true),(12,true)])
                      (.node 4761050 ([(0,true),(1,true),(2,true),(3,true),(9,true),(5,false),(13,false)],[(4,false),(8,false),(7,false),(6,false),(10,true),(11,true),(12,true)])
                        (.node 4761038 ([(2,true),(3,true),(8,false),(0,true),(10,false),(5,false),(13,false)],[(4,false),(9,true),(6,true),(7,false),(1,false),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4771340 ([(0,true),(1,true),(8,true),(3,false),(11,false),(5,false),(13,false)],[(4,false),(9,true),(10,true),(6,true),(7,true),(2,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4847882 ([(4,true),(8,false),(2,true),(11,true),(0,false),(6,false),(13,false)],[(5,false),(9,true),(10,true),(3,true),(7,true),(1,false),(12,true)])
                      (.node 4847834 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false),(13,false)],[(5,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4849352 ([(4,true),(10,true),(2,false),(1,false),(0,false),(6,false),(13,false)],[(5,false),(9,false),(8,false),(7,false),(3,false),(11,true),(12,true)])
                        .empty
                        .empty)))
                  (.node 4850732 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false),(13,false)],[(5,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                    (.node 4850156 ([(3,true),(4,true),(8,true),(1,false),(0,false),(6,false),(13,false)],[(5,false),(7,false),(2,false),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4849460 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(13,false)],[(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4849436 ([(4,true),(9,false),(2,true),(11,true),(0,false),(6,false),(13,false)],[(5,false),(10,true),(3,true),(7,true),(8,true),(1,false),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4850204 ([(2,true),(9,true),(0,true),(11,false),(4,true),(5,true),(13,false)],[(6,true),(10,true),(3,false),(8,false),(7,false),(1,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4850954 ([(3,true),(4,true),(9,true),(1,false),(0,false),(6,false),(13,false)],[(5,false),(8,false),(7,false),(2,false),(10,true),(11,true),(12,true)])
                      (.node 4850744 ([(3,true),(10,false),(1,false),(0,false),(8,false),(5,true),(13,false)],[(6,true),(9,true),(2,true),(7,true),(4,false),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4850972 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(13,false)],[(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))))
                (.node 4867082 ([(3,true),(11,true),(1,false),(0,false),(9,false),(5,true),(13,false)],[(6,true),(10,true),(4,true),(8,false),(7,false),(2,false),(12,true)])
                  (.node 4858682 ([(3,true),(10,true),(11,true),(1,false),(8,false),(5,true),(13,false)],[(6,true),(0,true),(9,true),(4,true),(7,false),(2,false),(12,true)])
                    (.node 4858508 ([(4,true),(8,false),(1,true),(2,true),(10,true),(6,false),(13,false)],[(5,false),(9,true),(3,true),(7,true),(0,false),(11,true),(12,true)])
                      (.node 4853480 ([(2,true),(3,true),(4,true),(11,true),(0,false),(6,false),(13,false)],[(5,false),(10,false),(9,false),(8,false),(7,false),(1,false),(12,true)])
                        (.node 4853468 ([(4,true),(11,true),(1,true),(2,true),(9,false),(6,false),(13,false)],[(5,false),(10,false),(3,true),(7,true),(8,true),(0,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4858670 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false),(13,false)],[(5,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4866986 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false),(13,false)],[(5,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4859096 ([(4,true),(9,false),(8,false),(1,true),(11,false),(6,false),(13,false)],[(5,false),(10,true),(0,true),(7,false),(3,false),(2,false),(12,true)])
                        .empty
                        .empty)
                      (.node 4867010 ([(1,true),(2,true),(8,false),(4,false),(10,false),(6,false),(13,false)],[(5,false),(7,false),(0,false),(9,false),(3,true),(11,true),(12,true)])
                        .empty
                        .empty)))
                  (.node 4867436 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(13,false)],[(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                    (.node 4867352 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(13,false)],[(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4867322 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false),(13,false)],[(5,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4867094 ([(1,true),(2,true),(3,true),(4,true),(9,true),(6,false),(13,false)],[(5,false),(8,false),(7,false),(0,false),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4867418 ([(3,true),(11,true),(1,false),(9,false),(8,false),(6,false),(13,false)],[(5,false),(4,false),(10,false),(0,false),(7,false),(2,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4869434 ([(3,true),(4,true),(11,true),(1,false),(0,false),(6,false),(13,false)],[(5,false),(10,false),(9,false),(8,false),(7,false),(2,false),(12,true)])
                      (.node 4869386 ([(4,true),(11,true),(1,false),(8,true),(9,true),(6,false),(13,false)],[(5,false),(10,false),(0,true),(7,false),(3,false),(2,false),(12,true)])
                        .empty
                        .empty)
                      (.node 4869722 ([(4,true),(11,true),(1,false),(9,false),(8,false),(6,false),(13,false)],[(5,false),(10,false),(0,false),(7,false),(3,false),(2,false),(12,true)])
                        .empty
                        .empty)))))
              (.node 4886576 ([(2,true),(3,true),(8,false),(0,true),(10,true),(5,true),(13,false)],[(6,true),(7,false),(1,false),(9,false),(4,true),(11,true),(12,true)])
                (.node 4877822 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false),(13,false)],[(5,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                  (.node 4875488 ([(2,true),(3,true),(4,true),(8,true),(0,false),(6,false),(13,false)],[(5,false),(7,false),(1,false),(9,true),(10,true),(11,true),(12,true)])
                    (.node 4874924 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false),(13,false)],[(5,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4870334 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(13,false)],[(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4870286 ([(1,true),(2,true),(9,false),(8,false),(4,true),(5,true),(13,false)],[(6,true),(0,true),(7,true),(3,false),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4874972 ([(4,true),(8,false),(1,true),(2,true),(11,false),(6,false),(13,false)],[(5,false),(9,true),(10,true),(0,true),(7,false),(3,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4875824 ([(2,true),(3,true),(8,true),(9,true),(10,true),(6,false),(13,false)],[(5,false),(4,false),(7,false),(1,false),(0,false),(11,true),(12,true)])
                      (.node 4875536 ([(1,true),(2,true),(11,false),(10,false),(4,true),(5,true),(13,false)],[(6,true),(0,true),(7,true),(8,true),(9,true),(3,false),(12,true)])
                        .empty
                        .empty)
                      (.node 4875872 ([(1,true),(2,true),(3,true),(4,true),(10,true),(6,false),(13,false)],[(5,false),(9,false),(8,false),(7,false),(0,false),(11,true),(12,true)])
                        .empty
                        .empty)))
                  (.node 4878176 ([(2,true),(3,true),(4,true),(10,true),(0,false),(6,false),(13,false)],[(5,false),(9,false),(8,false),(7,false),(1,false),(11,true),(12,true)])
                    (.node 4877936 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(13,false)],[(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4877906 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false),(13,false)],[(5,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        (.node 4877840 ([(2,true),(3,true),(10,true),(0,false),(8,false),(5,true),(13,false)],[(6,true),(9,true),(4,true),(7,false),(1,false),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4878164 ([(4,true),(10,true),(11,true),(2,false),(8,true),(6,false),(13,false)],[(5,false),(9,false),(0,true),(1,true),(7,false),(3,false),(12,true)])
                        .empty
                        .empty))
                    (.node 4878272 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(13,false)],[(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4878248 ([(4,true),(9,false),(2,true),(11,false),(0,false),(6,false),(13,false)],[(5,false),(10,true),(1,true),(8,false),(7,false),(3,false),(12,true)])
                        .empty
                        .empty)
                      (.node 4886162 ([(1,true),(8,false),(3,false),(11,false),(10,false),(6,false),(13,false)],[(5,false),(4,false),(7,false),(0,false),(9,false),(2,true),(12,true)])
                        .empty
                        .empty))))
                (.node 4894526 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(13,false)],[(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                  (.node 4891952 ([(2,true),(3,true),(4,true),(8,true),(0,false),(6,false),(13,false)],[(5,false),(7,false),(1,false),(9,true),(10,true),(11,true),(12,true)])
                    (.node 4891778 ([(3,true),(4,true),(8,false),(1,true),(10,true),(6,false),(13,false)],[(5,false),(9,true),(2,true),(7,true),(0,false),(11,true),(12,true)])
                      (.node 4886750 ([(1,true),(2,true),(11,false),(4,false),(8,true),(6,false),(13,false)],[(5,false),(10,false),(9,false),(0,true),(7,true),(3,false),(12,true)])
                        (.node 4886588 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(13,false)],[(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4891790 ([(1,true),(2,true),(8,true),(4,false),(11,false),(6,false),(13,false)],[(5,false),(9,true),(10,true),(0,true),(7,true),(3,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4894304 ([(2,true),(3,true),(11,false),(0,false),(8,false),(5,true),(13,false)],[(6,true),(9,true),(10,true),(1,true),(7,true),(4,false),(12,true)])
                      (.node 4894286 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false),(13,false)],[(5,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4894514 ([(2,true),(3,true),(11,false),(0,false),(8,true),(5,true),(13,false)],[(6,true),(7,false),(1,false),(10,false),(9,false),(4,false),(12,true)])
                        .empty
                        .empty)))
                  (.node 4895894 ([(3,true),(4,true),(8,false),(1,true),(10,false),(6,false),(13,false)],[(5,false),(9,true),(0,true),(7,false),(2,false),(11,true),(12,true)])
                    (.node 4895798 ([(4,false),(3,false),(2,false),(1,false),(0,false),(6,false),(13,false)],[(5,false),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                      (.node 4895102 ([(2,true),(3,true),(4,true),(10,true),(0,false),(6,false),(13,false)],[(5,false),(9,false),(8,false),(7,false),(1,false),(11,true),(12,true)])
                        (.node 4895054 ([(3,true),(4,true),(10,true),(1,true),(8,false),(6,false),(13,false)],[(5,false),(9,false),(2,true),(7,true),(0,true),(11,true),(12,true)])
                          .empty
                          .empty)
                        .empty)
                      (.node 4895822 ([(1,true),(10,false),(9,false),(3,true),(4,true),(5,true),(13,false)],[(6,true),(0,true),(7,true),(8,true),(2,false),(11,true),(12,true)])
                        .empty
                        .empty))
                    (.node 4897376 ([(1,true),(10,false),(4,false),(3,false),(8,true),(6,false),(13,false)],[(5,false),(9,false),(0,true),(7,true),(2,false),(11,true),(12,true)])
                      (.node 4895906 ([(1,true),(2,true),(3,true),(4,true),(9,true),(6,false),(13,false)],[(5,false),(8,false),(7,false),(0,false),(10,true),(11,true),(12,true)])
                        .empty
                        .empty)
                      (.node 4897424 ([(0,true),(1,true),(2,true),(3,true),(4,true),(5,true),(13,false)],[(6,true),(7,true),(8,true),(9,true),(10,true),(11,true),(12,true)])
                        .empty
                        .empty))))))))))))

noncomputable def choice (p : Fin 7 → Fin 7) (d : Fin 6) : Steps × Steps :=
  (CertificateTree.lookup certificates (code p d)).getD ([],[])

def fromList (a : Fin 7) (l : List (Fin 7)) (i : Fin 7) : Fin 7 := (a::l).getD i.val 0


end Erdos583HeptagonExcursionRoutesDevelopment
