import Submission.Work

/-! Kernel-checked routes for a six-cycle missing one path vertex. -/
namespace Erdos583HexagonRoutesDevelopment
open SimpleGraph Erdos583Work Erdos583Work.PieceRoutes
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

def next (i : Fin 6) : Fin 6 := ⟨(i.val+1)%6,Nat.mod_lt _ (by decide)⟩

def pieceSource (p : Fin 5 → Fin 5) (e : Fin 10) : Fin 6 :=
  if h : e.val < 6 then ⟨e.val,h⟩ else (p ⟨e.val-6,by omega⟩).castSucc

def pieceTarget (p : Fin 5 → Fin 5) (e : Fin 10) : Fin 6 :=
  if e.val < 6 then ⟨(e.val+1)%6,Nat.mod_lt _ (by decide)⟩ else (p ⟨e.val-5,by omega⟩).castSucc

def adjacent (a b : Fin 5) : Prop := a.val+1=b.val ∨ b.val+1=a.val
instance (a b : Fin 5) : Decidable (adjacent a b) := inferInstanceAs (Decidable (_ ∨ _))

abbrev Steps := List (Fin 10 × Bool)

def Valid (p : Fin 5 → Fin 5) (v : Steps × Steps) : Prop :=
  Route.compatible (s := pieceSource p) (t := pieceTarget p) (p 0).castSucc 5 v.1=true ∧
  Route.compatible (s := pieceSource p) (t := pieceTarget p) (p 4).castSucc 5 v.2=true ∧
  ((p 0).castSucc :: v.1.map (fun ed ↦ target (pieceSource p) (pieceTarget p) ed.1 ed.2)).Nodup ∧
  ((p 4).castSucc :: v.2.map (fun ed ↦ target (pieceSource p) (pieceTarget p) ed.1 ed.2)).Nodup ∧
  (∀ e : Fin 10, e ∈ v.1.map Prod.fst → e ∉ v.2.map Prod.fst) ∧
  ∀ e : Fin 10, e ∈ v.1.map Prod.fst ∨ e ∈ v.2.map Prod.fst

instance (p : Fin 5 → Fin 5) (v : Steps × Steps) : Decidable (Valid p v) := by
  unfold Valid
  infer_instance

def code (p : Fin 5 → Fin 5) : ℕ :=
  (p 0).val+5*(p 1).val+25*(p 2).val+125*(p 3).val+625*(p 4).val

def certificates : List (ℕ × (Steps × Steps)) := [
  (2710,([(0,true),(1,true),(2,true),(3,true),(4,true)],[(9,false),(8,false),(7,false),(6,false),(5,false)])),
  (1210,([(0,true),(1,true),(2,true),(3,true),(4,true)],[(9,false),(8,false),(7,false),(6,false),(5,false)])),
  (2110,([(0,true),(1,true),(2,true),(3,true),(4,true)],[(9,false),(8,false),(7,false),(6,false),(5,false)])),
  (1110,([(0,true),(1,true),(2,true),(3,true),(4,true)],[(9,false),(8,false),(7,false),(6,false),(5,false)])),
  (2790,([(0,true),(1,true),(2,true),(3,true),(4,true)],[(9,false),(8,false),(7,false),(6,false),(5,false)])),
  (1790,([(0,true),(1,true),(2,true),(3,true),(4,true)],[(9,false),(8,false),(7,false),(6,false),(5,false)])),
  (2690,([(0,true),(1,true),(2,true),(3,true),(4,true)],[(9,false),(8,false),(7,false),(6,false),(5,false)])),
  (1190,([(0,true),(1,true),(2,true),(3,true),(4,true)],[(9,false),(8,false),(7,false),(6,false),(5,false)])),
  (2070,([(0,true),(1,true),(2,true),(3,true),(4,true)],[(9,false),(8,false),(7,false),(6,false),(5,false)])),
  (1070,([(0,true),(1,true),(2,true),(3,true),(4,true)],[(9,false),(8,false),(7,false),(6,false),(5,false)])),
  (2766,([(0,false),(7,false),(2,false),(9,true),(4,true)],[(3,false),(6,false),(1,true),(8,false),(5,false)])),
  (1766,([(0,false),(7,false),(2,false),(9,false),(4,true)],[(1,false),(6,true),(3,true),(8,false),(5,false)])),
  (2566,([(6,true),(2,false),(8,true),(9,true),(4,true)],[(3,false),(7,true),(1,false),(0,false),(5,false)])),
  (566,([(1,true),(2,true),(3,true),(9,true),(5,false)],[(0,true),(6,true),(7,true),(8,true),(4,true)])),
  (1366,([(0,false),(9,true),(2,true),(3,true),(4,true)],[(1,false),(6,true),(7,true),(8,true),(5,false)])),
  (366,([(6,true),(3,true),(8,true),(9,true),(5,false)],[(0,true),(1,true),(2,true),(7,true),(4,true)])),
  (1946,([(0,false),(9,true),(2,false),(7,false),(4,true)],[(3,true),(6,false),(1,true),(8,true),(5,false)])),
  (446,([(6,true),(7,true),(2,true),(9,true),(5,false)],[(0,true),(1,true),(8,true),(3,true),(4,true)])),
  (1346,([(0,false),(9,true),(2,true),(3,true),(4,true)],[(1,false),(6,true),(7,true),(8,true),(5,false)])),
  (346,([(6,true),(3,false),(2,false),(9,true),(5,false)],[(0,true),(1,true),(8,false),(7,false),(4,true)])),
  (2702,([(1,false),(0,false),(7,true),(3,true),(4,true)],[(9,false),(8,false),(2,false),(6,true),(5,false)])),
  (1202,([(1,false),(0,false),(7,true),(3,true),(4,true)],[(9,false),(8,false),(2,false),(6,true),(5,false)])),
  (2102,([(1,false),(9,true),(3,true),(7,false),(5,false)],[(2,false),(6,true),(0,true),(8,false),(4,true)])),
  (1102,([(1,false),(9,false),(3,true),(7,false),(5,false)],[(0,false),(6,false),(2,true),(8,false),(4,true)])),
  (2022,([(2,true),(9,false),(0,false),(7,false),(4,true)],[(3,true),(6,false),(1,false),(8,false),(5,false)])),
  (1022,([(1,false),(0,false),(8,true),(3,true),(4,true)],[(9,false),(2,false),(6,true),(7,true),(5,false)])),
  (1922,([(1,false),(0,false),(9,true),(3,true),(4,true)],[(2,false),(6,true),(7,true),(8,true),(5,false)])),
  (422,([(1,false),(7,false),(3,false),(9,true),(5,false)],[(0,true),(8,true),(2,false),(6,true),(4,true)])),
  (2778,([(6,true),(0,true),(1,true),(9,true),(4,true)],[(3,false),(2,false),(8,false),(7,false),(5,false)])),
  (1778,([(2,false),(9,false),(8,false),(0,false),(5,false)],[(1,false),(7,false),(6,false),(3,true),(4,true)])),
  (2678,([(6,true),(7,true),(1,false),(9,true),(4,true)],[(3,false),(2,false),(8,true),(0,false),(5,false)])),
  (1178,([(2,false),(7,false),(0,true),(9,false),(4,true)],[(1,true),(8,true),(3,false),(6,true),(5,false)])),
  (2758,([(6,true),(0,false),(8,true),(9,true),(4,true)],[(3,false),(2,false),(1,false),(7,true),(5,false)])),
  (1758,([(2,false),(1,false),(0,false),(8,true),(4,true)],[(9,false),(3,false),(6,true),(7,true),(5,false)])),
  (2558,([(2,false),(1,false),(0,false),(9,true),(4,true)],[(3,false),(6,true),(7,true),(8,true),(5,false)])),
  (558,([(6,true),(1,true),(8,true),(9,true),(5,false)],[(0,true),(7,true),(2,true),(3,true),(4,true)])),
  (1358,([(2,false),(1,false),(7,true),(8,true),(5,false)],[(9,false),(0,true),(6,false),(3,true),(4,true)])),
  (358,([(2,false),(8,false),(7,false),(0,false),(5,false)],[(9,false),(1,false),(6,false),(3,true),(4,true)])),
  (2054,([(3,false),(2,false),(1,false),(0,false),(5,false)],[(9,false),(8,false),(7,false),(6,false),(4,true)])),
  (1054,([(3,false),(2,false),(1,false),(0,false),(5,false)],[(9,false),(8,false),(7,false),(6,false),(4,true)])),
  (1934,([(3,false),(2,false),(1,false),(0,false),(5,false)],[(9,false),(8,false),(7,false),(6,false),(4,true)])),
  (434,([(3,false),(2,false),(1,false),(0,false),(5,false)],[(9,false),(8,false),(7,false),(6,false),(4,true)])),
  (1334,([(3,false),(2,false),(1,false),(0,false),(5,false)],[(9,false),(8,false),(7,false),(6,false),(4,true)])),
  (334,([(3,false),(2,false),(1,false),(0,false),(5,false)],[(9,false),(8,false),(7,false),(6,false),(4,true)])),
  (2014,([(3,false),(2,false),(1,false),(0,false),(5,false)],[(9,false),(8,false),(7,false),(6,false),(4,true)])),
  (1014,([(3,false),(2,false),(1,false),(0,false),(5,false)],[(9,false),(8,false),(7,false),(6,false),(4,true)])),
  (1914,([(3,false),(2,false),(1,false),(0,false),(5,false)],[(9,false),(8,false),(7,false),(6,false),(4,true)])),
  (414,([(3,false),(2,false),(1,false),(0,false),(5,false)],[(9,false),(8,false),(7,false),(6,false),(4,true)]))]

def choice (p : Fin 5 → Fin 5) : Steps × Steps := (certificates.lookup (code p)).getD ([],[])

lemma finite_certificate_vec : ∀ a b c d e : Fin 5,
    (List.ofFn ![a,b,c,d,e]).Nodup → ¬adjacent a b → ¬adjacent d e →
    Valid ![a,b,c,d,e] (choice ![a,b,c,d,e]) := by
  decide

lemma finite_certificate (p : Fin 5 → Fin 5)
    (hp : (List.ofFn p).Nodup) (hf : ¬adjacent (p 0) (p 1)) (hl : ¬adjacent (p 3) (p 4)) :
    Valid p (choice p) := by
  have he : ![p 0,p 1,p 2,p 3,p 4]=p := by funext i; fin_cases i <;> rfl
  simpa only [he] using finite_certificate_vec (p 0) (p 1) (p 2) (p 3) (p 4) (by rwa [he]) hf hl

lemma exists_routes (p : Fin 5 → Fin 5) (hp : Function.Injective p)
    (hfirst : ¬adjacent (p 0) (p 1)) (hlast : ¬adjacent (p 3) (p 4)) :
    ∃ X : Route (pieceSource p) (pieceTarget p) (p 0).castSucc 5,
    ∃ Y : Route (pieceSource p) (pieceTarget p) (p 4).castSucc 5,
      X.support.Nodup ∧ Y.support.Nodup ∧ X.pieces.Disjoint Y.pieces ∧
        ∀ e, e ∈ X.pieces ∨ e ∈ Y.pieces := by
  obtain ⟨ha,hb,hnX,hnY,hd,hc⟩ := finite_certificate p (List.nodup_ofFn.mpr hp) hfirst hlast
  obtain ⟨X,hXs,hXp⟩ := Route.of_compatible (choice p).1 ha
  obtain ⟨Y,hYs,hYp⟩ := Route.of_compatible (choice p).2 hb
  exact ⟨X,Y,hXs.symm ▸ hnX,hYs.symm ▸ hnY,by simpa only [hXp,hYp] using hd,
    by simpa only [hXp,hYp] using hc⟩

end Erdos583HexagonRoutesDevelopment
