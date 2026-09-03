import Submission.CorePathPieces

/-! Kernel-checked finite route certificates for a two-triangle core. -/
namespace Erdos583ButterflyRoutesDevelopment
open SimpleGraph Erdos583Work.PieceRoutes Erdos583CorePathPiecesDevelopment
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
set_option Elab.async false

def baseSource : Fin 6 → Fin 5 := ![0,1,2,0,3,4]
def baseTarget : Fin 6 → Fin 5 := ![1,2,0,3,4,0]
def outer (i : Fin 4) : Fin 5 := ⟨i.val+1,by omega⟩

def wordCode {k n : ℕ} (p : Fin k → Fin n) : ℕ :=
  (List.ofFn p).foldr (fun i c ↦ i.val+n*c) 0

namespace Missing
abbrev RawSteps := List (ℕ × Bool)

def code (n : Fin 3) (p : Fin (n.val+1) → Fin 4) : ℕ := 256*n.val+wordCode p

def certificates : List (ℕ × (Fin 5 × (RawSteps × RawSteps))) := [
  (0,(3,([(1,true),(2,true),(5,false),(4,false)],[(0,false),(3,true)]))),
  (1,(3,([(2,true),(5,false),(4,false)],[(1,false),(0,false),(3,true)]))),
  (2,(1,([(4,true),(5,true),(2,false),(1,false)],[(3,false),(0,true)]))),
  (3,(1,([(5,true),(2,false),(1,false)],[(4,false),(3,false),(0,true)]))),
  (260,(3,([(6,true),(2,true),(5,false),(4,false)],[(1,false),(0,false),(3,true)]))),
  (264,(2,([(6,true),(4,true),(5,true),(2,false)],[(3,false),(0,true),(1,true)]))),
  (268,(2,([(6,true),(5,true),(2,false)],[(4,false),(3,false),(0,true),(1,true)]))),
  (257,(3,([(6,true),(0,false),(5,false),(4,false)],[(1,true),(2,true),(3,true)]))),
  (265,(1,([(6,true),(4,true),(5,true),(0,true)],[(3,false),(2,false),(1,false)]))),
  (269,(1,([(6,true),(5,true),(0,true)],[(4,false),(3,false),(2,false),(1,false)]))),
  (258,(2,([(4,true),(5,true),(0,true),(1,true)],[(6,false),(3,false),(2,false)]))),
  (262,(1,([(4,true),(5,true),(2,false),(1,false)],[(6,false),(3,false),(0,true)]))),
  (270,(1,([(6,true),(5,true),(2,false),(1,false)],[(4,false),(3,false),(0,true)]))),
  (259,(2,([(5,true),(0,true),(1,true)],[(6,false),(4,false),(3,false),(2,false)]))),
  (263,(1,([(5,true),(2,false),(1,false)],[(6,false),(4,false),(3,false),(0,true)]))),
  (267,(1,([(6,true),(3,false),(2,false),(1,false)],[(4,true),(5,true),(0,true)]))),
  (548,(4,([(6,true),(2,true),(3,true),(4,true)],[(7,false),(1,false),(0,false),(5,false)]))),
  (564,(3,([(6,true),(2,true),(5,false),(4,false)],[(7,false),(1,false),(0,false),(3,true)]))),
  (536,(4,([(6,true),(7,true),(2,true),(5,false)],[(1,false),(0,false),(3,true),(4,true)]))),
  (568,(2,([(6,true),(7,true),(5,true),(2,false)],[(4,false),(3,false),(0,true),(1,true)]))),
  (540,(3,([(6,true),(7,true),(2,true),(3,true)],[(1,false),(0,false),(5,false),(4,false)]))),
  (556,(2,([(6,true),(7,true),(3,false),(2,false)],[(4,true),(5,true),(0,true),(1,true)]))),
  (545,(4,([(6,true),(0,false),(3,true),(4,true)],[(7,false),(1,true),(2,true),(5,false)]))),
  (561,(3,([(6,true),(0,false),(5,false),(4,false)],[(7,false),(1,true),(2,true),(3,true)]))),
  (521,(4,([(1,false),(7,false),(3,false),(5,false)],[(0,false),(2,false),(6,true),(4,true)]))),
  (569,(1,([(6,true),(7,true),(5,true),(0,true)],[(4,false),(3,false),(2,false),(1,false)]))),
  (525,(3,([(1,false),(7,false),(5,true),(3,true)],[(0,false),(2,false),(6,true),(4,false)]))),
  (557,(1,([(6,true),(7,true),(3,false),(0,true)],[(4,true),(5,true),(2,false),(1,false)]))),
  (530,(4,([(6,true),(7,true),(2,true),(5,false)],[(1,false),(0,false),(3,true),(4,true)]))),
  (562,(2,([(6,true),(7,true),(5,true),(2,false)],[(4,false),(3,false),(0,true),(1,true)]))),
  (518,(4,([(6,true),(7,true),(0,false),(5,false)],[(1,true),(2,true),(3,true),(4,true)]))),
  (566,(1,([(6,true),(7,true),(5,true),(0,true)],[(4,false),(3,false),(2,false),(1,false)]))),
  (526,(2,([(6,true),(5,true),(0,true),(1,true)],[(7,false),(4,false),(3,false),(2,false)]))),
  (542,(1,([(6,true),(5,true),(2,false),(1,false)],[(7,false),(4,false),(3,false),(0,true)]))),
  (531,(3,([(6,true),(7,true),(2,true),(3,true)],[(1,false),(0,false),(5,false),(4,false)]))),
  (547,(2,([(4,false),(7,false),(0,false),(2,false)],[(3,false),(5,false),(6,true),(1,true)]))),
  (519,(3,([(6,true),(7,true),(0,false),(3,true)],[(1,true),(2,true),(5,false),(4,false)]))),
  (551,(1,([(4,false),(7,false),(2,true),(0,true)],[(3,false),(5,false),(6,true),(1,false)]))),
  (523,(2,([(6,true),(3,false),(0,true),(1,true)],[(7,false),(4,true),(5,true),(2,false)]))),
  (539,(1,([(6,true),(3,false),(2,false),(1,false)],[(7,false),(4,true),(5,true),(0,true)])))]

def rawChoice (n : Fin 3) (p : Fin (n.val+1) → Fin 4) : Fin 5 × (RawSteps × RawSteps) :=
  (certificates.lookup (code n p)).getD (0,[],[])

def convertSteps (n : Fin 3) (l : RawSteps) : List (Fin (6+n.val) × Bool) :=
  l.map (fun ed ↦ (⟨ed.1 % (6+n.val),Nat.mod_lt _ (by omega)⟩,ed.2))

def choice (n : Fin 3) (p : Fin (n.val+1) → Fin 4) :=
  ((rawChoice n p).1, convertSteps n (rawChoice n p).2.1, convertSteps n (rawChoice n p).2.2)

def Valid (n : Fin 3) (p : Fin (n.val+1) → Fin 4)
    (v : Fin 5 × (List (Fin (6+n.val) × Bool) × List (Fin (6+n.val) × Bool))) : Prop :=
  let s := pieceSource baseSource (outer ∘ p)
  let t := pieceTarget baseTarget (outer ∘ p)
  Route.compatible (s := s) (t := t) (outer (p 0)) v.1 v.2.1=true ∧
  Route.compatible (s := s) (t := t) (outer (p (Fin.last n.val))) v.1 v.2.2=true ∧
  (outer (p 0) :: v.2.1.map (fun ed ↦ target s t ed.1 ed.2)).Nodup ∧
  (outer (p (Fin.last n.val)) :: v.2.2.map (fun ed ↦ target s t ed.1 ed.2)).Nodup ∧
  (∀ e, e ∈ v.2.1.map Prod.fst → e ∉ v.2.2.map Prod.fst) ∧
  ∀ e, e ∈ v.2.1.map Prod.fst ∨ e ∈ v.2.2.map Prod.fst

instance (n : Fin 3) (p : Fin (n.val+1) → Fin 4) (v) : Decidable (Valid n p v) := by
  unfold Valid
  infer_instance

lemma finite_certificate : ∀ (n : Fin 3) (p : Fin (n.val+1) → Fin 4),
    (List.ofFn p).Nodup → Valid n p (choice n p) := by
  decide

lemma exists_routes (n : Fin 3) (p : Fin (n.val+1) → Fin 4) (hp : Function.Injective p) :
    ∃ z : Fin 5,
    ∃ X : Route (pieceSource baseSource (outer ∘ p)) (pieceTarget baseTarget (outer ∘ p)) (outer (p 0)) z,
    ∃ Y : Route (pieceSource baseSource (outer ∘ p)) (pieceTarget baseTarget (outer ∘ p)) (outer (p (Fin.last n.val))) z,
      X.support.Nodup ∧ Y.support.Nodup ∧ X.pieces.Disjoint Y.pieces ∧
        ∀ e, e ∈ X.pieces ∨ e ∈ Y.pieces := by
  obtain ⟨ha,hb,hnX,hnY,hd,hc⟩ := finite_certificate n p (List.nodup_ofFn.mpr hp)
  obtain ⟨X,hXs,hXp⟩ := Route.of_compatible (choice n p).2.1 ha
  obtain ⟨Y,hYs,hYp⟩ := Route.of_compatible (choice n p).2.2 hb
  exact ⟨(choice n p).1,X,Y,hXs.symm ▸ hnX,hYs.symm ▸ hnY,
    by simpa only [hXp,hYp] using hd,by simpa only [hXp,hYp] using hc⟩
end Missing

namespace Excursion
abbrev Steps := List (Fin 10 × Bool)

def source : Fin 6 → Fin 6 := Fin.castSucc ∘ baseSource
def target : Fin 6 → Fin 6 := Fin.castSucc ∘ baseTarget

def certificates : List (ℕ × (Steps × Steps)) := [
  (5935,([(0,false),(5,false),(9,false),(8,false),(7,false)],[(4,false),(3,false),(2,false),(1,false),(6,true)])),
  (6025,([(6,true),(2,true),(5,false),(9,false),(8,false)],[(4,false),(3,false),(0,true),(1,true),(7,true)])),
  (6385,([(6,true),(2,true),(3,true),(4,true),(9,false)],[(5,true),(0,true),(1,true),(7,true),(8,true)])),
  (4855,([(0,false),(3,true),(9,false),(8,false),(7,false)],[(4,true),(5,true),(2,false),(1,false),(6,true)])),
  (4945,([(6,true),(2,true),(3,true),(9,false),(8,false)],[(4,true),(5,true),(0,true),(1,true),(7,true)])),
  (5125,([(6,true),(2,true),(5,false),(4,false),(9,false)],[(3,false),(0,true),(1,true),(7,true),(8,true)])),
  (5755,([(0,false),(5,false),(9,false),(8,false),(7,false)],[(4,false),(3,false),(2,false),(1,false),(6,true)])),
  (5815,([(1,true),(9,true),(5,true),(3,true),(7,true)],[(4,false),(6,false),(0,false),(2,false),(8,false)])),
  (6355,([(6,true),(7,true),(2,true),(5,false),(9,false)],[(4,false),(3,false),(0,true),(1,true),(8,true)])),
  (3595,([(1,true),(2,true),(5,false),(8,false),(7,false)],[(9,false),(4,false),(3,false),(0,true),(6,true)])),
  (3655,([(6,true),(3,false),(2,false),(9,false),(8,false)],[(1,false),(0,false),(5,false),(4,false),(7,true)])),
  (3835,([(6,true),(7,true),(5,true),(2,false),(9,false)],[(1,false),(0,false),(3,true),(4,true),(8,true)])),
  (4495,([(0,false),(2,false),(9,true),(4,true),(7,false)],[(3,false),(5,false),(8,true),(1,false),(6,true)])),
  (4525,([(0,false),(5,false),(4,false),(9,false),(8,false)],[(3,false),(2,false),(1,false),(6,true),(7,true)])),
  (5065,([(1,true),(2,true),(5,false),(4,false),(9,false)],[(3,false),(0,true),(6,true),(7,true),(8,true)])),
  (3415,([(1,true),(2,true),(3,true),(8,false),(7,false)],[(9,false),(4,true),(5,true),(0,true),(6,true)])),
  (3445,([(6,true),(5,true),(2,false),(9,false),(8,false)],[(1,false),(0,false),(3,true),(4,true),(7,true)])),
  (3805,([(6,true),(7,true),(3,false),(2,false),(9,false)],[(1,false),(0,false),(5,false),(4,false),(8,true)])),
  (5900,([(2,true),(5,false),(9,false),(8,false),(7,false)],[(4,false),(3,false),(0,true),(1,true),(6,true)])),
  (6020,([(6,true),(0,false),(5,false),(9,false),(8,false)],[(4,false),(3,false),(2,false),(1,false),(7,true)])),
  (6380,([(6,true),(0,false),(3,true),(4,true),(9,false)],[(5,true),(2,false),(1,false),(7,true),(8,true)])),
  (4820,([(2,true),(3,true),(9,false),(8,false),(7,false)],[(4,true),(5,true),(0,true),(1,true),(6,true)])),
  (4940,([(6,true),(0,false),(3,true),(9,false),(8,false)],[(4,true),(5,true),(2,false),(1,false),(7,true)])),
  (5120,([(6,true),(0,false),(5,false),(4,false),(9,false)],[(3,false),(2,false),(1,false),(7,true),(8,true)])),
  (5540,([(2,true),(5,false),(9,false),(8,false),(7,false)],[(4,false),(3,false),(0,true),(1,true),(6,true)])),
  (5600,([(1,false),(9,true),(5,true),(3,true),(7,true)],[(4,false),(6,false),(2,true),(0,true),(8,false)])),
  (6320,([(6,true),(7,true),(0,false),(5,false),(9,false)],[(4,false),(3,false),(2,false),(1,false),(8,true)])),
  (2300,([(1,false),(0,false),(5,false),(8,false),(7,false)],[(9,false),(4,false),(3,false),(2,false),(6,true)])),
  (2360,([(1,false),(9,false),(5,true),(3,true),(7,true)],[(0,false),(2,false),(6,true),(4,true),(8,false)])),
  (2540,([(6,true),(7,true),(5,true),(0,true),(9,false)],[(1,true),(2,true),(3,true),(4,true),(8,true)])),
  (4280,([(2,true),(0,true),(9,true),(4,true),(7,false)],[(3,false),(5,false),(8,true),(1,true),(6,true)])),
  (4310,([(2,true),(5,false),(4,false),(9,false),(8,false)],[(3,false),(0,true),(1,true),(6,true),(7,true)])),
  (5030,([(1,false),(0,false),(5,false),(4,false),(9,false)],[(3,false),(2,false),(6,true),(7,true),(8,true)])),
  (2120,([(1,false),(0,false),(3,true),(8,false),(7,false)],[(9,false),(4,true),(5,true),(2,false),(6,true)])),
  (2150,([(1,false),(9,false),(3,false),(5,false),(7,true)],[(0,false),(2,false),(6,true),(4,false),(8,false)])),
  (2510,([(6,true),(7,true),(3,false),(0,true),(9,false)],[(1,true),(2,true),(5,false),(4,false),(8,true)])),
  (5685,([(4,true),(5,true),(2,false),(8,false),(7,false)],[(9,false),(1,false),(0,false),(3,true),(6,true)])),
  (5805,([(6,true),(0,false),(5,false),(9,false),(8,false)],[(4,false),(3,false),(2,false),(1,false),(7,true)])),
  (6345,([(6,true),(7,true),(2,true),(5,false),(9,false)],[(4,false),(3,false),(0,true),(1,true),(8,true)])),
  (3525,([(3,false),(2,false),(9,false),(8,false),(7,false)],[(1,false),(0,false),(5,false),(4,false),(6,true)])),
  (3645,([(4,true),(9,true),(2,true),(0,true),(7,true)],[(1,false),(6,false),(3,false),(5,false),(8,false)])),
  (3825,([(6,true),(7,true),(5,true),(2,false),(9,false)],[(1,false),(0,false),(3,true),(4,true),(8,true)])),
  (5505,([(4,true),(5,true),(0,true),(8,false),(7,false)],[(9,false),(1,true),(2,true),(3,true),(6,true)])),
  (5595,([(6,true),(2,true),(5,false),(9,false),(8,false)],[(4,false),(3,false),(0,true),(1,true),(7,true)])),
  (6315,([(6,true),(7,true),(0,false),(5,false),(9,false)],[(4,false),(3,false),(2,false),(1,false),(8,true)])),
  (2265,([(3,false),(5,false),(9,true),(1,true),(7,false)],[(0,false),(2,false),(8,true),(4,false),(6,true)])),
  (2355,([(3,false),(5,false),(9,true),(1,true),(7,true)],[(0,false),(2,false),(6,false),(4,true),(8,false)])),
  (2535,([(3,false),(5,false),(7,false),(1,false),(9,false)],[(0,false),(2,false),(6,false),(4,true),(8,true)])),
  (2985,([(3,false),(2,false),(9,false),(8,false),(7,false)],[(1,false),(0,false),(5,false),(4,false),(6,true)])),
  (3015,([(6,true),(5,true),(2,false),(9,false),(8,false)],[(1,false),(0,false),(3,true),(4,true),(7,true)])),
  (3735,([(6,true),(5,true),(0,true),(1,true),(9,false)],[(2,true),(3,true),(4,true),(7,true),(8,true)])),
  (1905,([(3,false),(0,true),(9,false),(8,false),(7,false)],[(1,true),(2,true),(5,false),(4,false),(6,true)])),
  (1935,([(6,true),(5,true),(0,true),(9,false),(8,false)],[(1,true),(2,true),(3,true),(4,true),(7,true)])),
  (2475,([(6,true),(5,true),(2,false),(1,false),(9,false)],[(0,false),(3,true),(4,true),(7,true),(8,true)])),
  (4390,([(4,false),(3,false),(2,false),(8,false),(7,false)],[(9,false),(1,false),(0,false),(5,false),(6,true)])),
  (4510,([(4,false),(9,false),(2,true),(0,true),(7,true)],[(3,false),(5,false),(6,true),(1,true),(8,false)])),
  (5050,([(6,true),(7,true),(2,true),(3,true),(9,false)],[(4,true),(5,true),(0,true),(1,true),(8,true)])),
  (3310,([(5,true),(2,false),(9,false),(8,false),(7,false)],[(1,false),(0,false),(3,true),(4,true),(6,true)])),
  (3430,([(4,false),(9,true),(2,true),(0,true),(7,true)],[(1,false),(6,false),(5,true),(3,true),(8,false)])),
  (3790,([(6,true),(7,true),(3,false),(2,false),(9,false)],[(1,false),(0,false),(5,false),(4,false),(8,true)])),
  (4210,([(4,false),(3,false),(0,true),(8,false),(7,false)],[(9,false),(1,true),(2,true),(5,false),(6,true)])),
  (4300,([(4,false),(9,false),(0,false),(2,false),(7,true)],[(3,false),(5,false),(6,true),(1,false),(8,false)])),
  (5020,([(6,true),(7,true),(0,false),(3,true),(9,false)],[(4,true),(5,true),(2,false),(1,false),(8,true)])),
  (2050,([(5,true),(3,true),(9,true),(1,true),(7,false)],[(0,false),(2,false),(8,true),(4,true),(6,true)])),
  (2140,([(5,true),(3,true),(9,true),(1,true),(7,true)],[(0,false),(2,false),(6,false),(4,false),(8,false)])),
  (2500,([(5,true),(3,true),(7,false),(1,false),(9,false)],[(0,false),(2,false),(6,false),(4,false),(8,true)])),
  (2950,([(5,true),(2,false),(9,false),(8,false),(7,false)],[(1,false),(0,false),(3,true),(4,true),(6,true)])),
  (3010,([(6,true),(3,false),(2,false),(9,false),(8,false)],[(1,false),(0,false),(5,false),(4,false),(7,true)])),
  (3730,([(6,true),(3,false),(0,true),(1,true),(9,false)],[(2,true),(5,false),(4,false),(7,true),(8,true)])),
  (1870,([(5,true),(0,true),(9,false),(8,false),(7,false)],[(1,true),(2,true),(3,true),(4,true),(6,true)])),
  (1930,([(6,true),(3,false),(0,true),(9,false),(8,false)],[(1,true),(2,true),(5,false),(4,false),(7,true)])),
  (2470,([(6,true),(3,false),(2,false),(1,false),(9,false)],[(0,false),(5,false),(4,false),(7,true),(8,true)]))]

def choice (q : Fin 5 → Fin 6) : Steps × Steps :=
  (certificates.lookup (wordCode q)).getD ([],[])

def Valid (q : Fin 5 → Fin 6) (v : Steps × Steps) : Prop :=
  let s := pieceSource source q
  let t := pieceTarget target q
  Route.compatible (s := s) (t := t) (q 0) 5 v.1=true ∧
  Route.compatible (s := s) (t := t) (q 4) 5 v.2=true ∧
  (q 0 :: v.1.map (fun ed ↦ Erdos583Work.PieceRoutes.target s t ed.1 ed.2)).Nodup ∧
  (q 4 :: v.2.map (fun ed ↦ Erdos583Work.PieceRoutes.target s t ed.1 ed.2)).Nodup ∧
  (∀ e, e ∈ v.1.map Prod.fst → e ∉ v.2.map Prod.fst) ∧
  ∀ e, e ∈ v.1.map Prod.fst ∨ e ∈ v.2.map Prod.fst

instance (q : Fin 5 → Fin 6) (v) : Decidable (Valid q v) := by
  unfold Valid
  infer_instance

lemma finite_certificate_vec : ∀ a b c d e : Fin 6,
    (List.ofFn ![a,b,c,d,e]).Nodup →
    (∀ i, (![a,b,c,d,e] : Fin 5 → Fin 6) i ≠ 0) → a ≠ 5 → e ≠ 5 →
    Valid ![a,b,c,d,e] (choice ![a,b,c,d,e]) := by
  decide

lemma finite_certificate (q : Fin 5 → Fin 6) (hq : Function.Injective q)
    (hn : ∀ i, q i ≠ 0) (h0 : q 0 ≠ 5) (h4 : q 4 ≠ 5) : Valid q (choice q) := by
  have he : ![q 0,q 1,q 2,q 3,q 4]=q := by funext i; fin_cases i <;> rfl
  have hh := finite_certificate_vec (q 0) (q 1) (q 2) (q 3) (q 4)
    (by rw [he]; exact List.nodup_ofFn.mpr hq) (by rwa [he]) h0 h4
  simpa only [he] using hh

lemma exists_routes (q : Fin 5 → Fin 6) (hq : Function.Injective q)
    (hn : ∀ i, q i ≠ 0) (h0 : q 0 ≠ 5) (h4 : q 4 ≠ 5) :
    ∃ X : Route (pieceSource source q) (pieceTarget target q) (q 0) 5,
    ∃ Y : Route (pieceSource source q) (pieceTarget target q) (q 4) 5,
      X.support.Nodup ∧ Y.support.Nodup ∧ X.pieces.Disjoint Y.pieces ∧
        ∀ e, e ∈ X.pieces ∨ e ∈ Y.pieces := by
  obtain ⟨ha,hb,hnX,hnY,hd,hc⟩ := finite_certificate q hq hn h0 h4
  obtain ⟨X,hXs,hXp⟩ := Route.of_compatible (choice q).1 ha
  obtain ⟨Y,hYs,hYp⟩ := Route.of_compatible (choice q).2 hb
  exact ⟨X,Y,hXs.symm ▸ hnX,hYs.symm ▸ hnY,
    by simpa only [hXp,hYp] using hd,by simpa only [hXp,hYp] using hc⟩
end Excursion
end Erdos583ButterflyRoutesDevelopment
