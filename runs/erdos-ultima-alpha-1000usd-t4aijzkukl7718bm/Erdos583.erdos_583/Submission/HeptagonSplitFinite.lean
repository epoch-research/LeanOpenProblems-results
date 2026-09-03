import Submission.HeptagonFinite

/-! The four exceptional seven-cycle visit orders, split at their second path gap. -/
namespace Erdos583HeptagonSplitRoutesDevelopment
open SimpleGraph Erdos583Work Erdos583Work.PieceRoutes
open Erdos583HeptagonRoutesDevelopment (Exceptional adjacent code fromList)
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

end Erdos583HeptagonSplitRoutesDevelopment
