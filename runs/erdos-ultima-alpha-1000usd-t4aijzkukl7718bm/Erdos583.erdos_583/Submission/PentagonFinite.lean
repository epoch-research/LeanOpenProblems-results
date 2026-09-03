import Submission.Work
import Submission.PieceRoutes

/-! Finite certificates for a pentagon with one split path link. -/
namespace Erdos583PentagonRoutesDevelopment
open SimpleGraph Erdos583Work Erdos583PieceRoutesDevelopment
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

def extended (p : Fin 5 → Fin 5) (d : Fin 4) (i : Fin 6) : Fin 6 :=
  if h : i.val ≤ d.val then (p ⟨i.val,by omega⟩).castSucc
  else if i.val=d.val+1 then 5 else (p ⟨i.val-1,by omega⟩).castSucc

def pieceSource (p : Fin 5 → Fin 5) (d : Fin 4) (e : Fin 10) : Fin 6 :=
  if h : e.val < 5 then (⟨e.val,h⟩ : Fin 5).castSucc
  else extended p d ⟨e.val-5,by omega⟩

def pieceTarget (p : Fin 5 → Fin 5) (d : Fin 4) (e : Fin 10) : Fin 6 :=
  if e.val < 5 then (⟨(e.val+1)%5,Nat.mod_lt _ (by decide)⟩ : Fin 5).castSucc
  else extended p d ⟨e.val-4,by omega⟩

def adjacent (a b : Fin 5) : Prop := (a.val+1)%5=b.val ∨ (b.val+1)%5=a.val
instance (a b : Fin 5) : Decidable (adjacent a b) := inferInstanceAs (Decidable (_ ∨ _))

abbrev Steps := List (Fin 10 × Bool)

def Valid (p : Fin 5 → Fin 5) (d : Fin 4) (v : Steps × Steps) : Prop :=
  Route.compatible (s := pieceSource p d) (t := pieceTarget p d) (p 0).castSucc 5 v.1=true ∧
  Route.compatible (s := pieceSource p d) (t := pieceTarget p d) (p 4).castSucc 5 v.2=true ∧
  ((p 0).castSucc :: v.1.map (fun ed ↦ target (pieceSource p d) (pieceTarget p d) ed.1 ed.2)).Nodup ∧
  ((p 4).castSucc :: v.2.map (fun ed ↦ target (pieceSource p d) (pieceTarget p d) ed.1 ed.2)).Nodup ∧
  (∀ e : Fin 10, e ∈ v.1.map Prod.fst → e ∉ v.2.map Prod.fst) ∧
  ∀ e : Fin 10, e ∈ v.1.map Prod.fst ∨ e ∈ v.2.map Prod.fst

instance (p : Fin 5 → Fin 5) (d : Fin 4) (v : Steps × Steps) : Decidable (Valid p d v) := by
  unfold Valid
  infer_instance

def code (p : Fin 5 → Fin 5) (d : Fin 4) : ℕ :=
  (p 0).val+5*(p 1).val+25*(p 2).val+125*(p 3).val+625*(p 4).val+3125*d.val

def certificates : List (ℕ × (Steps × Steps)) := [
  (2710,([(4,false),(9,false),(8,false),(2,false),(6,false)],[(3,false),(7,false),(1,false),(0,false),(5,true)])),
  (5835,([(0,true),(9,true),(3,false),(2,false),(6,true)],[(4,true),(5,true),(1,false),(8,false),(7,false)])),
  (8960,([(4,false),(9,false),(1,true),(2,true),(7,true)],[(3,false),(6,false),(5,false),(0,true),(8,false)])),
  (12085,([(0,true),(1,true),(2,true),(3,true),(9,false)],[(4,true),(5,true),(6,true),(7,true),(8,true)])),
  (1210,([(0,true),(9,false),(3,false),(2,false),(6,false)],[(1,true),(7,true),(8,true),(4,true),(5,true)])),
  (4335,([(0,true),(9,false),(3,false),(2,false),(6,true)],[(1,true),(5,false),(4,false),(8,false),(7,false)])),
  (7460,([(4,false),(9,true),(1,true),(2,true),(7,true)],[(0,false),(5,true),(6,true),(3,true),(8,false)])),
  (10585,([(4,false),(3,false),(2,false),(1,false),(9,false)],[(0,false),(5,true),(6,true),(7,true),(8,true)])),
  (2110,([(0,true),(8,false),(3,false),(2,false),(6,false)],[(9,false),(1,true),(7,true),(4,true),(5,true)])),
  (5235,([(0,true),(8,false),(3,false),(2,false),(6,true)],[(9,false),(1,true),(5,false),(4,false),(7,false)])),
  (8360,([(0,true),(9,true),(2,false),(6,true),(7,true)],[(3,true),(4,true),(5,true),(1,false),(8,false)])),
  (11485,([(0,true),(1,true),(6,true),(3,false),(9,false)],[(2,false),(5,false),(4,false),(7,true),(8,true)])),
  (1110,([(0,true),(9,false),(3,true),(7,false),(6,false)],[(1,true),(2,true),(8,false),(4,true),(5,true)])),
  (4235,([(4,false),(3,false),(9,true),(1,true),(6,true)],[(0,false),(5,true),(2,true),(8,false),(7,false)])),
  (7360,([(0,true),(9,false),(2,false),(6,true),(7,true)],[(1,true),(5,false),(4,false),(3,false),(8,false)])),
  (10485,([(4,false),(3,false),(2,false),(1,false),(9,false)],[(0,false),(5,true),(6,true),(7,true),(8,true)])),
  (2790,([(4,false),(9,false),(1,false),(7,false),(6,false)],[(3,false),(2,false),(8,false),(0,false),(5,true)])),
  (5915,([(0,true),(1,true),(9,true),(3,false),(6,true)],[(4,true),(5,true),(2,false),(8,false),(7,false)])),
  (9040,([(4,false),(9,false),(2,true),(6,true),(7,true)],[(3,false),(5,false),(0,true),(1,true),(8,false)])),
  (12165,([(0,true),(1,true),(2,true),(3,true),(9,false)],[(4,true),(5,true),(6,true),(7,true),(8,true)])),
  (1790,([(0,true),(1,true),(9,false),(3,false),(6,false)],[(2,true),(7,true),(8,true),(4,true),(5,true)])),
  (4915,([(0,true),(1,true),(9,false),(3,false),(6,true)],[(2,true),(5,false),(4,false),(8,false),(7,false)])),
  (8040,([(4,false),(9,true),(2,true),(6,true),(7,true)],[(1,false),(0,false),(5,true),(3,true),(8,false)])),
  (11165,([(0,true),(7,true),(3,false),(2,false),(9,false)],[(1,false),(6,false),(5,false),(4,false),(8,true)])),
  (2690,([(4,false),(9,false),(1,true),(2,true),(6,false)],[(3,false),(7,true),(8,true),(0,false),(5,true)])),
  (5815,([(4,false),(9,false),(1,true),(2,true),(6,true)],[(3,false),(5,false),(0,true),(8,false),(7,false)])),
  (8940,([(0,true),(9,true),(3,false),(2,false),(7,true)],[(4,true),(5,true),(6,true),(1,false),(8,false)])),
  (12065,([(0,true),(1,true),(2,true),(3,true),(9,false)],[(4,true),(5,true),(6,true),(7,true),(8,true)])),
  (1190,([(0,true),(9,false),(8,false),(2,true),(6,false)],[(1,true),(7,false),(3,true),(4,true),(5,true)])),
  (4315,([(0,true),(1,true),(8,true),(3,false),(6,true)],[(9,false),(4,true),(5,true),(2,false),(7,false)])),
  (7440,([(0,true),(9,false),(3,false),(2,false),(7,true)],[(1,true),(6,false),(5,false),(4,false),(8,false)])),
  (10565,([(4,false),(3,false),(2,false),(1,false),(9,false)],[(0,false),(5,true),(6,true),(7,true),(8,true)])),
  (2766,([(0,false),(4,false),(9,false),(2,true),(6,false)],[(3,false),(7,true),(8,true),(1,false),(5,true)])),
  (5891,([(0,false),(4,false),(9,false),(2,true),(6,true)],[(3,false),(5,false),(1,true),(8,false),(7,false)])),
  (9016,([(1,true),(9,true),(3,false),(6,true),(7,true)],[(4,true),(0,true),(5,true),(2,false),(8,false)])),
  (12141,([(0,false),(7,true),(2,true),(3,true),(9,false)],[(4,true),(6,false),(5,false),(1,true),(8,true)])),
  (1766,([(1,true),(9,false),(4,true),(7,false),(6,false)],[(2,true),(3,true),(8,false),(0,true),(5,true)])),
  (4891,([(0,false),(4,false),(9,true),(2,true),(6,true)],[(1,false),(5,true),(3,true),(8,false),(7,false)])),
  (8016,([(1,true),(9,false),(3,false),(6,true),(7,true)],[(2,true),(5,false),(0,false),(4,false),(8,false)])),
  (11141,([(0,false),(4,false),(3,false),(2,false),(9,false)],[(1,false),(5,true),(6,true),(7,true),(8,true)])),
  (1366,([(1,true),(9,false),(4,false),(3,false),(6,false)],[(2,true),(7,true),(8,true),(0,true),(5,true)])),
  (4491,([(1,true),(9,false),(4,false),(3,false),(6,true)],[(2,true),(5,false),(0,false),(8,false),(7,false)])),
  (7616,([(0,false),(9,true),(2,true),(3,true),(7,true)],[(1,false),(5,true),(6,true),(4,true),(8,false)])),
  (10741,([(0,false),(4,false),(3,false),(2,false),(9,false)],[(1,false),(5,true),(6,true),(7,true),(8,true)])),
  (366,([(0,false),(9,false),(8,false),(3,false),(6,false)],[(4,false),(7,false),(2,false),(1,false),(5,true)])),
  (3491,([(0,false),(4,false),(8,true),(2,true),(6,true)],[(9,false),(1,false),(5,true),(3,true),(7,false)])),
  (6616,([(0,false),(9,false),(2,true),(3,true),(7,true)],[(4,false),(6,false),(5,false),(1,true),(8,false)])),
  (9741,([(1,true),(2,true),(3,true),(4,true),(9,false)],[(0,true),(5,true),(6,true),(7,true),(8,true)])),
  (1946,([(0,false),(8,false),(2,true),(3,true),(6,false)],[(9,false),(4,false),(7,true),(1,false),(5,true)])),
  (5071,([(0,false),(8,false),(2,true),(3,true),(6,true)],[(9,false),(4,false),(5,false),(1,true),(7,false)])),
  (8196,([(0,false),(9,true),(3,true),(6,true),(7,true)],[(2,false),(1,false),(5,true),(4,true),(8,false)])),
  (11321,([(0,false),(4,false),(6,true),(2,true),(9,false)],[(3,true),(5,false),(1,true),(7,true),(8,true)])),
  (446,([(0,false),(9,false),(2,false),(7,false),(6,false)],[(4,false),(3,false),(8,false),(1,false),(5,true)])),
  (3571,([(1,true),(2,true),(9,true),(4,false),(6,true)],[(0,true),(5,true),(3,false),(8,false),(7,false)])),
  (6696,([(0,false),(9,false),(3,true),(6,true),(7,true)],[(4,false),(5,false),(1,true),(2,true),(8,false)])),
  (9821,([(1,true),(2,true),(3,true),(4,true),(9,false)],[(0,true),(5,true),(6,true),(7,true),(8,true)])),
  (1346,([(1,true),(9,false),(8,false),(3,true),(6,false)],[(2,true),(7,false),(4,true),(0,true),(5,true)])),
  (4471,([(0,false),(9,true),(2,true),(3,true),(6,true)],[(1,false),(5,true),(4,true),(8,false),(7,false)])),
  (7596,([(1,true),(9,false),(4,false),(3,false),(7,true)],[(2,true),(6,false),(5,false),(0,false),(8,false)])),
  (10721,([(0,false),(4,false),(3,false),(2,false),(9,false)],[(1,false),(5,true),(6,true),(7,true),(8,true)])),
  (346,([(0,false),(9,false),(2,true),(3,true),(6,false)],[(4,false),(7,true),(8,true),(1,false),(5,true)])),
  (3471,([(0,false),(9,false),(2,true),(3,true),(6,true)],[(4,false),(5,false),(1,true),(8,false),(7,false)])),
  (6596,([(1,true),(9,true),(4,false),(3,false),(7,true)],[(0,true),(5,true),(6,true),(2,false),(8,false)])),
  (9721,([(1,true),(2,true),(3,true),(4,true),(9,false)],[(0,true),(5,true),(6,true),(7,true),(8,true)])),
  (2702,([(1,false),(8,false),(3,true),(4,true),(6,false)],[(9,false),(0,false),(7,true),(2,false),(5,true)])),
  (5827,([(1,false),(8,false),(3,true),(4,true),(6,true)],[(9,false),(0,false),(5,false),(2,true),(7,false)])),
  (8952,([(1,false),(9,true),(4,true),(6,true),(7,true)],[(3,false),(2,false),(5,true),(0,true),(8,false)])),
  (12077,([(1,false),(0,false),(6,true),(3,true),(9,false)],[(4,true),(5,false),(2,true),(7,true),(8,true)])),
  (1202,([(1,false),(9,false),(3,false),(7,false),(6,false)],[(0,false),(4,false),(8,false),(2,false),(5,true)])),
  (4327,([(2,true),(3,true),(9,true),(0,false),(6,true)],[(1,true),(5,true),(4,false),(8,false),(7,false)])),
  (7452,([(1,false),(9,false),(4,true),(6,true),(7,true)],[(0,false),(5,false),(2,true),(3,true),(8,false)])),
  (10577,([(2,true),(3,true),(4,true),(0,true),(9,false)],[(1,true),(5,true),(6,true),(7,true),(8,true)])),
  (2102,([(2,true),(9,false),(8,false),(4,true),(6,false)],[(3,true),(7,false),(0,true),(1,true),(5,true)])),
  (5227,([(1,false),(9,true),(3,true),(4,true),(6,true)],[(2,false),(5,true),(0,true),(8,false),(7,false)])),
  (8352,([(2,true),(9,false),(0,false),(4,false),(7,true)],[(3,true),(6,false),(5,false),(1,false),(8,false)])),
  (11477,([(1,false),(0,false),(4,false),(3,false),(9,false)],[(2,false),(5,true),(6,true),(7,true),(8,true)])),
  (1102,([(1,false),(9,false),(3,true),(4,true),(6,false)],[(0,false),(7,true),(8,true),(2,false),(5,true)])),
  (4227,([(1,false),(9,false),(3,true),(4,true),(6,true)],[(0,false),(5,false),(2,true),(8,false),(7,false)])),
  (7352,([(2,true),(9,true),(0,false),(4,false),(7,true)],[(1,true),(5,true),(6,true),(3,false),(8,false)])),
  (10477,([(2,true),(3,true),(4,true),(0,true),(9,false)],[(1,true),(5,true),(6,true),(7,true),(8,true)])),
  (2022,([(2,true),(9,false),(0,false),(4,false),(6,false)],[(3,true),(7,true),(8,true),(1,true),(5,true)])),
  (5147,([(2,true),(9,false),(0,false),(4,false),(6,true)],[(3,true),(5,false),(1,false),(8,false),(7,false)])),
  (8272,([(1,false),(9,true),(3,true),(4,true),(7,true)],[(2,false),(5,true),(6,true),(0,true),(8,false)])),
  (11397,([(1,false),(0,false),(4,false),(3,false),(9,false)],[(2,false),(5,true),(6,true),(7,true),(8,true)])),
  (1022,([(1,false),(9,false),(8,false),(4,false),(6,false)],[(0,false),(7,false),(3,false),(2,false),(5,true)])),
  (4147,([(1,false),(0,false),(8,true),(3,true),(6,true)],[(9,false),(2,false),(5,true),(4,true),(7,false)])),
  (7272,([(1,false),(9,false),(3,true),(4,true),(7,true)],[(0,false),(6,false),(5,false),(2,true),(8,false)])),
  (10397,([(2,true),(3,true),(4,true),(0,true),(9,false)],[(1,true),(5,true),(6,true),(7,true),(8,true)])),
  (1922,([(2,true),(9,false),(0,true),(7,false),(6,false)],[(3,true),(4,true),(8,false),(1,true),(5,true)])),
  (5047,([(1,false),(0,false),(9,true),(3,true),(6,true)],[(2,false),(5,true),(4,true),(8,false),(7,false)])),
  (8172,([(2,true),(9,false),(4,false),(6,true),(7,true)],[(3,true),(5,false),(1,false),(0,false),(8,false)])),
  (11297,([(1,false),(0,false),(4,false),(3,false),(9,false)],[(2,false),(5,true),(6,true),(7,true),(8,true)])),
  (422,([(1,false),(0,false),(9,false),(3,true),(6,false)],[(4,false),(7,true),(8,true),(2,false),(5,true)])),
  (3547,([(1,false),(0,false),(9,false),(3,true),(6,true)],[(4,false),(5,false),(2,true),(8,false),(7,false)])),
  (6672,([(2,true),(9,true),(4,false),(6,true),(7,true)],[(0,true),(1,true),(5,true),(3,false),(8,false)])),
  (9797,([(1,false),(7,true),(3,true),(4,true),(9,false)],[(0,true),(6,false),(5,false),(2,true),(8,true)])),
  (2778,([(3,true),(9,false),(1,false),(0,false),(6,false)],[(4,true),(7,true),(8,true),(2,true),(5,true)])),
  (5903,([(3,true),(9,false),(1,false),(0,false),(6,true)],[(4,true),(5,false),(2,false),(8,false),(7,false)])),
  (9028,([(2,false),(9,true),(4,true),(0,true),(7,true)],[(3,false),(5,true),(6,true),(1,true),(8,false)])),
  (12153,([(2,false),(1,false),(0,false),(4,false),(9,false)],[(3,false),(5,true),(6,true),(7,true),(8,true)])),
  (1778,([(2,false),(9,false),(8,false),(0,false),(6,false)],[(1,false),(7,false),(4,false),(3,false),(5,true)])),
  (4903,([(2,false),(1,false),(8,true),(4,true),(6,true)],[(9,false),(3,false),(5,true),(0,true),(7,false)])),
  (8028,([(2,false),(9,false),(4,true),(0,true),(7,true)],[(1,false),(6,false),(5,false),(3,true),(8,false)])),
  (11153,([(3,true),(4,true),(0,true),(1,true),(9,false)],[(2,true),(5,true),(6,true),(7,true),(8,true)])),
  (2678,([(3,true),(9,false),(1,true),(7,false),(6,false)],[(4,true),(0,true),(8,false),(2,true),(5,true)])),
  (5803,([(2,false),(1,false),(9,true),(4,true),(6,true)],[(3,false),(5,true),(0,true),(8,false),(7,false)])),
  (8928,([(3,true),(9,false),(0,false),(6,true),(7,true)],[(4,true),(5,false),(2,false),(1,false),(8,false)])),
  (12053,([(2,false),(1,false),(0,false),(4,false),(9,false)],[(3,false),(5,true),(6,true),(7,true),(8,true)])),
  (1178,([(2,false),(1,false),(9,false),(4,true),(6,false)],[(0,false),(7,true),(8,true),(3,false),(5,true)])),
  (4303,([(2,false),(1,false),(9,false),(4,true),(6,true)],[(0,false),(5,false),(3,true),(8,false),(7,false)])),
  (7428,([(3,true),(9,true),(0,false),(6,true),(7,true)],[(1,true),(2,true),(5,true),(4,false),(8,false)])),
  (10553,([(2,false),(7,true),(4,true),(0,true),(9,false)],[(1,true),(6,false),(5,false),(3,true),(8,true)])),
  (2758,([(3,true),(9,false),(8,false),(0,true),(6,false)],[(4,true),(7,false),(1,true),(2,true),(5,true)])),
  (5883,([(2,false),(9,true),(4,true),(0,true),(6,true)],[(3,false),(5,true),(1,true),(8,false),(7,false)])),
  (9008,([(3,true),(9,false),(1,false),(0,false),(7,true)],[(4,true),(6,false),(5,false),(2,false),(8,false)])),
  (12133,([(2,false),(1,false),(0,false),(4,false),(9,false)],[(3,false),(5,true),(6,true),(7,true),(8,true)])),
  (1758,([(2,false),(9,false),(4,true),(0,true),(6,false)],[(1,false),(7,true),(8,true),(3,false),(5,true)])),
  (4883,([(2,false),(9,false),(4,true),(0,true),(6,true)],[(1,false),(5,false),(3,true),(8,false),(7,false)])),
  (8008,([(3,true),(9,true),(1,false),(0,false),(7,true)],[(2,true),(5,true),(6,true),(4,false),(8,false)])),
  (11133,([(3,true),(4,true),(0,true),(1,true),(9,false)],[(2,true),(5,true),(6,true),(7,true),(8,true)])),
  (1358,([(2,false),(9,false),(4,false),(7,false),(6,false)],[(1,false),(0,false),(8,false),(3,false),(5,true)])),
  (4483,([(3,true),(4,true),(9,true),(1,false),(6,true)],[(2,true),(5,true),(0,false),(8,false),(7,false)])),
  (7608,([(2,false),(9,false),(0,true),(6,true),(7,true)],[(1,false),(5,false),(3,true),(4,true),(8,false)])),
  (10733,([(3,true),(4,true),(0,true),(1,true),(9,false)],[(2,true),(5,true),(6,true),(7,true),(8,true)])),
  (358,([(2,false),(8,false),(4,true),(0,true),(6,false)],[(9,false),(1,false),(7,true),(3,false),(5,true)])),
  (3483,([(2,false),(8,false),(4,true),(0,true),(6,true)],[(9,false),(1,false),(5,false),(3,true),(7,false)])),
  (6608,([(2,false),(9,true),(0,true),(6,true),(7,true)],[(4,false),(3,false),(5,true),(1,true),(8,false)])),
  (9733,([(2,false),(1,false),(6,true),(4,true),(9,false)],[(0,true),(5,false),(3,true),(7,true),(8,true)])),
  (1934,([(3,false),(9,false),(8,false),(1,false),(6,false)],[(2,false),(7,false),(0,false),(4,false),(5,true)])),
  (5059,([(3,false),(2,false),(8,true),(0,true),(6,true)],[(9,false),(4,false),(5,true),(1,true),(7,false)])),
  (8184,([(3,false),(9,false),(0,true),(1,true),(7,true)],[(2,false),(6,false),(5,false),(4,true),(8,false)])),
  (11309,([(4,true),(0,true),(1,true),(2,true),(9,false)],[(3,true),(5,true),(6,true),(7,true),(8,true)])),
  (434,([(4,true),(9,false),(2,false),(1,false),(6,false)],[(0,true),(7,true),(8,true),(3,true),(5,true)])),
  (3559,([(4,true),(9,false),(2,false),(1,false),(6,true)],[(0,true),(5,false),(3,false),(8,false),(7,false)])),
  (6684,([(3,false),(9,true),(0,true),(1,true),(7,true)],[(4,false),(5,true),(6,true),(2,true),(8,false)])),
  (9809,([(3,false),(2,false),(1,false),(0,false),(9,false)],[(4,false),(5,true),(6,true),(7,true),(8,true)])),
  (1334,([(3,false),(2,false),(9,false),(0,true),(6,false)],[(1,false),(7,true),(8,true),(4,false),(5,true)])),
  (4459,([(3,false),(2,false),(9,false),(0,true),(6,true)],[(1,false),(5,false),(4,true),(8,false),(7,false)])),
  (7584,([(4,true),(9,true),(1,false),(6,true),(7,true)],[(2,true),(3,true),(5,true),(0,false),(8,false)])),
  (10709,([(3,false),(7,true),(0,true),(1,true),(9,false)],[(2,true),(6,false),(5,false),(4,true),(8,true)])),
  (334,([(4,true),(9,false),(2,true),(7,false),(6,false)],[(0,true),(1,true),(8,false),(3,true),(5,true)])),
  (3459,([(3,false),(2,false),(9,true),(0,true),(6,true)],[(4,false),(5,true),(1,true),(8,false),(7,false)])),
  (6584,([(4,true),(9,false),(1,false),(6,true),(7,true)],[(0,true),(5,false),(3,false),(2,false),(8,false)])),
  (9709,([(3,false),(2,false),(1,false),(0,false),(9,false)],[(4,false),(5,true),(6,true),(7,true),(8,true)])),
  (2014,([(3,false),(9,false),(0,false),(7,false),(6,false)],[(2,false),(1,false),(8,false),(4,false),(5,true)])),
  (5139,([(4,true),(0,true),(9,true),(2,false),(6,true)],[(3,true),(5,true),(1,false),(8,false),(7,false)])),
  (8264,([(3,false),(9,false),(1,true),(6,true),(7,true)],[(2,false),(5,false),(4,true),(0,true),(8,false)])),
  (11389,([(4,true),(0,true),(1,true),(2,true),(9,false)],[(3,true),(5,true),(6,true),(7,true),(8,true)])),
  (1014,([(3,false),(8,false),(0,true),(1,true),(6,false)],[(9,false),(2,false),(7,true),(4,false),(5,true)])),
  (4139,([(3,false),(8,false),(0,true),(1,true),(6,true)],[(9,false),(2,false),(5,false),(4,true),(7,false)])),
  (7264,([(3,false),(9,true),(1,true),(6,true),(7,true)],[(0,false),(4,false),(5,true),(2,true),(8,false)])),
  (10389,([(3,false),(2,false),(6,true),(0,true),(9,false)],[(1,true),(5,false),(4,true),(7,true),(8,true)])),
  (1914,([(3,false),(9,false),(0,true),(1,true),(6,false)],[(2,false),(7,true),(8,true),(4,false),(5,true)])),
  (5039,([(3,false),(9,false),(0,true),(1,true),(6,true)],[(2,false),(5,false),(4,true),(8,false),(7,false)])),
  (8164,([(4,true),(9,true),(2,false),(1,false),(7,true)],[(3,true),(5,true),(6,true),(0,false),(8,false)])),
  (11289,([(4,true),(0,true),(1,true),(2,true),(9,false)],[(3,true),(5,true),(6,true),(7,true),(8,true)])),
  (414,([(4,true),(9,false),(8,false),(1,true),(6,false)],[(0,true),(7,false),(2,true),(3,true),(5,true)])),
  (3539,([(3,false),(9,true),(0,true),(1,true),(6,true)],[(4,false),(5,true),(2,true),(8,false),(7,false)])),
  (6664,([(4,true),(9,false),(2,false),(1,false),(7,true)],[(0,true),(6,false),(5,false),(3,false),(8,false)])),
  (9789,([(3,false),(2,false),(1,false),(0,false),(9,false)],[(4,false),(5,true),(6,true),(7,true),(8,true)]))]

def choice (p : Fin 5 → Fin 5) (d : Fin 4) : Steps × Steps :=
  (certificates.lookup (code p d)).getD ([],[])

lemma finite_certificate_vec : ∀ a b c e f : Fin 5,
    (List.ofFn ![a,b,c,e,f]).Nodup → ¬adjacent a b → ¬adjacent e f →
    ∀ d : Fin 4, Valid ![a,b,c,e,f] d (choice ![a,b,c,e,f] d) := by
  decide

lemma finite_certificate (p : Fin 5 → Fin 5)
    (hp : (List.ofFn p).Nodup) (hf : ¬adjacent (p 0) (p 1)) (hl : ¬adjacent (p 3) (p 4))
    (d : Fin 4) : Valid p d (choice p d) := by
  have he : ![p 0,p 1,p 2,p 3,p 4]=p := by
    funext i
    fin_cases i <;> rfl
  have hh := finite_certificate_vec (p 0) (p 1) (p 2) (p 3) (p 4)
    (by rwa [he]) hf hl d
  simpa only [he] using hh

lemma exists_routes (p : Fin 5 → Fin 5) (hp : Function.Injective p)
    (hfirst : ¬adjacent (p 0) (p 1)) (hlast : ¬adjacent (p 3) (p 4)) (d : Fin 4) :
    ∃ X : Route (pieceSource p d) (pieceTarget p d) (p 0).castSucc 5,
    ∃ Y : Route (pieceSource p d) (pieceTarget p d) (p 4).castSucc 5,
      X.support.Nodup ∧ Y.support.Nodup ∧ X.pieces.Disjoint Y.pieces ∧
        ∀ e, e ∈ X.pieces ∨ e ∈ Y.pieces := by
  have hpn : (List.ofFn p).Nodup := List.nodup_ofFn.mpr hp
  obtain ⟨ha,hb,hnX,hnY,hd,hc⟩ := finite_certificate p hpn hfirst hlast d
  obtain ⟨X,hXs,hXp⟩ := Route.of_compatible (choice p d).1 ha
  obtain ⟨Y,hYs,hYp⟩ := Route.of_compatible (choice p d).2 hb
  exact ⟨X,Y,hXs.symm ▸ hnX,hYs.symm ▸ hnY,by simpa only [hXp,hYp] using hd,
    by simpa only [hXp,hYp] using hc⟩

end Erdos583PentagonRoutesDevelopment
