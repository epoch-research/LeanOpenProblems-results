import Submission.UniversalProfilePattern
import Submission.NoOppositeTriangleCover

/-! A covered second right adjoint for the universal nine-point bundle.
This is an exclusion of a candidate family, not a settlement of Erdos 595. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595UniversalProfile
open Erdos595ArcAdjoint Erdos595FiniteFiberUniversal Erdos595NoOppositeTriangle
universe u
variable {I : Type u} (B : SimpleGraph I)

abbrev Bic := Biclique (H B)

def side (p : Bic B) (s : Fin 2) : Set (I × Nine) := if s = 0 then p.val.1 else p.val.2

def code (p : Bic B) : Fin 2 → Set Nine := fun s => Prod.snd '' side B p s

def ref : Fin 2 → Fin 6 := ![0,2]

section Realization
variable (p : Fin 6 → Bic B)
  (ht : ∀ i, code B (p i) = code B (p (ref (cls i))))
  (h01 : (right (H B)).Adj (p 0) (p 1))
  (h02 : (right (H B)).Adj (p 0) (p 2))
  (h12 : (right (H B)).Adj (p 1) (p 2))
  (h34 : (right (H B)).Adj (p 3) (p 4))
  (h35 : (right (H B)).Adj (p 3) (p 5))
  (h45 : (right (H B)).Adj (p 4) (p 5))

include h01 h02 h12 h34 h35 h45 in
lemma witness_edge (w : Fin 12) : (right (H B)).Adj (p (source w)) (p (target w)) := by
  fin_cases w
  · exact h01
  · exact h02
  · exact h01.symm
  · exact h12
  · exact h02.symm
  · exact h12.symm
  · exact h34
  · exact h35
  · exact h34.symm
  · exact h45
  · exact h35.symm
  · exact h45.symm

noncomputable def witness (w : Fin 12) : I × Nine :=
  (witness_edge B p h01 h02 h12 h34 h35 h45 w).1.choose

lemma witness_mem (w : Fin 12) :
    witness B p h01 h02 h12 h34 h35 h45 w ∈ (p (source w)).val.2 ∧
    witness B p h01 h02 h12 h34 h35 h45 w ∈ (p (target w)).val.1 :=
  (witness_edge B p h01 h02 h12 h34 h35 h45 w).1.choose_spec

def marks (t s : Fin 2) (c : Fin 9) : Prop := coord c ∈ code B (p (ref t)) s

variable (d : I)

noncomputable def pick (i : Fin 6) (s : Fin 2) (c : Fin 9) : I × Nine := by
  classical
  exact if h : ∃ x ∈ side B (p i) s, x.2 = coord c then h.choose else (d,coord c)

lemma pick_fixed (i : Fin 6) (s : Fin 2) (c : Fin 9) :
    (pick B p d i s c).2 = coord c := by
  classical
  dsimp only [pick]
  split_ifs with h
  · exact h.choose_spec.2
  · rfl

include ht in
lemma pick_mem (i : Fin 6) (s : Fin 2) (c : Fin 9) (hc : marks B p (cls i) s c) :
    pick B p d i s c ∈ side B (p i) s := by
  classical
  have hh : coord c ∈ code B (p i) s := by rw [ht i]; exact hc
  obtain ⟨x,hx,hxc⟩ := hh
  have hex : ∃ x ∈ side B (p i) s, x.2 = coord c := ⟨x,hx,hxc⟩
  simp only [pick,dif_pos hex]
  exact hex.choose_spec.1

noncomputable def sample (n : Fin 120) : I × Nine :=
  if h : n.val < 108 then
    pick B p d ⟨n.val/18,by omega⟩ ⟨(n.val%18)/9,by omega⟩ ⟨n.val%9,Nat.mod_lt _ (by decide)⟩
  else witness B p h01 h02 h12 h34 h35 h45 ⟨n.val-108,by omega⟩

lemma sample_rep (i : Fin 6) (s : Fin 2) (c : Fin 9) :
    sample B p h01 h02 h12 h34 h35 h45 d (rep i s c) = pick B p d i s c := by
  fin_cases i <;> fin_cases s <;> fin_cases c <;> rfl

lemma sample_wit (w : Fin 12) :
    sample B p h01 h02 h12 h34 h35 h45 d (wit w) = witness B p h01 h02 h12 h34 h35 h45 w := by
  fin_cases w <;> rfl

include ht in
lemma sample_left (i : Fin 6) (n : Fin 120) (hl : LeftSlot i n) (ha : active (marks B p) n) :
    sample B p h01 h02 h12 h34 h35 h45 d n ∈ (p i).val.1 := by
  classical
  by_cases hn : n.val < 108
  · have hs : n.val/18 = i.val ∧ n.val%18 < 9 := by simpa only [LeftSlot,dif_pos hn] using hl
    have hi : (⟨n.val/18,by omega⟩ : Fin 6) = i := Fin.ext hs.1
    have hz : (⟨(n.val%18)/9,by omega⟩ : Fin 2) = 0 := by apply Fin.ext; dsimp; omega
    dsimp only [sample]
    rw [dif_pos hn,hi,hz]
    have hmark : marks B p (cls i) 0 ⟨n.val%9,Nat.mod_lt _ (by decide)⟩ := by
      simpa only [active,dif_pos hn,hi,hz] using ha
    exact pick_mem B p ht d i 0 _ hmark
  · have hs : target ⟨n.val-108,by omega⟩ = i := by simpa only [LeftSlot,dif_neg hn] using hl
    dsimp only [sample]
    rw [dif_neg hn]
    simpa only [hs] using (witness_mem B p h01 h02 h12 h34 h35 h45 ⟨n.val-108,by omega⟩).2

include ht in
lemma sample_right (i : Fin 6) (n : Fin 120) (hl : RightSlot i n) (ha : active (marks B p) n) :
    sample B p h01 h02 h12 h34 h35 h45 d n ∈ (p i).val.2 := by
  classical
  by_cases hn : n.val < 108
  · have hs : n.val/18 = i.val ∧ 9 ≤ n.val%18 := by simpa only [RightSlot,dif_pos hn] using hl
    have hi : (⟨n.val/18,by omega⟩ : Fin 6) = i := Fin.ext hs.1
    have hz : (⟨(n.val%18)/9,by omega⟩ : Fin 2) = 1 := by apply Fin.ext; dsimp; omega
    dsimp only [sample]
    rw [dif_pos hn,hi,hz]
    have hmark : marks B p (cls i) 1 ⟨n.val%9,Nat.mod_lt _ (by decide)⟩ := by
      simpa only [active,dif_pos hn,hi,hz] using ha
    exact pick_mem B p ht d i 1 _ hmark
  · have hs : source ⟨n.val-108,by omega⟩ = i := by simpa only [RightSlot,dif_neg hn] using hl
    dsimp only [sample]
    rw [dif_neg hn]
    simpa only [hs] using (witness_mem B p h01 h02 h12 h34 h35 h45 ⟨n.val-108,by omega⟩).1

include ht in
lemma realized : Conditions B (sample B p h01 h02 h12 h34 h35 h45 d) (marks B p) := by
  constructor
  · intro i s c
    rw [sample_rep]
    exact pick_fixed B p d i s c
  · intro i a b ha hb hca hcb
    exact (p i).property _ (sample_left B p ht h01 h02 h12 h34 h35 h45 d i a ha hca)
      _ (sample_right B p ht h01 h02 h12 h34 h35 h45 d i b hb hcb)
  · intro w c hc
    rw [sample_wit] at hc
    have hh : coord c ∈ code B (p (source w)) 1 :=
      ⟨_,(witness_mem B p h01 h02 h12 h34 h35 h45 w).1,hc⟩
    rw [ht (source w)] at hh
    exact hh
  · intro w c hc
    rw [sample_wit] at hc
    have hh : coord c ∈ code B (p (target w)) 0 :=
      ⟨_,(witness_mem B p h01 h02 h12 h34 h35 h45 w).2,hc⟩
    rw [ht (target w)] at hh
    exact hh

include ht h01 h02 h12 h34 h35 h45 in
lemma two_triangle_profiles_impossible (hB : B.CliqueFree 3) : False := by
  let d := (witness B p h01 h02 h12 h34 h35 h45 0).1
  exact no_pattern B (sample B p h01 h02 h12 h34 h35 h45 d) (marks B p) hB
    (realized B p ht h01 h02 h12 h34 h35 h45 d)

end Realization

lemma no_opposite (hB : B.CliqueFree 3) : NoOpposite (right (H B)) (code B) := by
  intro a b d x y z hab had hbd hxy hxz hyz heab hexy heaz hed
  let p : Fin 6 → Bic B := ![a,b,d,z,x,y]
  have ht : ∀ i, code B (p i) = code B (p (ref (cls i))) := by
    intro i
    fin_cases i
    · rfl
    · exact heab.symm
    · rfl
    · exact heaz.symm
    · exact hed.symm
    · exact hexy.symm.trans hed.symm
  exact two_triangle_profiles_impossible B p ht hab had hbd hxz.symm hyz.symm hxy hB

/-- The universal second right stage is countably edge-covered over every
triangle-free index graph; no odd-walk bound beyond triangles is needed. -/
theorem second_right_cover (hB : B.CliqueFree 3) :
    Erdos595Work.IsCountableUnionOfTriangleFree (right (right (H B))) :=
  Erdos595NoOppositeTriangle.right_cover (right (H B)) (code B) (no_opposite B hB)

/-- This covers every compatible two-three-coloring fiber template at stage two,
even when the original fiber is infinite. -/
theorem template_second_right_cover {S : Type u} (F : SimpleGraph S)
    (P : S → S → Prop) (hP : Symmetric P)
    (t : Erdos595FiniteFiberOddBound.Template F P) (hB : B.CliqueFree 3) :
    Erdos595Work.IsCountableUnionOfTriangleFree
      (right (right (Erdos595FiniteFiberOddBound.bundle F P hP B))) :=
  Erdos595Work.countable_union_of_hom
    (Erdos595RightFiber.rightHom (Erdos595RightFiber.rightHom (fold F P hP t B)))
    (second_right_cover B hB)

#print axioms no_opposite
#print axioms second_right_cover
#print axioms template_second_right_cover
end Erdos595UniversalProfile
