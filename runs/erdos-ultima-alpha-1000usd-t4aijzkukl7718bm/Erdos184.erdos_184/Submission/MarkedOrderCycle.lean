import Submission.FastMarkedOrder

/-! Structural cyclicity of recursive marked orders. No finite enumeration is used. -/
namespace Erdos184Work.CycleSegments
open Equiv Equiv.Perm
set_option maxHeartbeats 1000000

section Insert
variable {W : Type*} [DecidableEq W]

def insertPerm (p : Equiv.Perm W) (j : W) : Equiv.Perm (W ⊕ Unit) :=
  Equiv.sumCongr p (Equiv.refl Unit) * Equiv.swap (Sum.inl j) (Sum.inr ())

lemma insertPerm_apply (p : Equiv.Perm W) (j : W) (i : W ⊕ Unit) :
    insertPerm p j i = insertNext p j i := by
  cases i with
  | inl i =>
    by_cases h : i = j
    · subst i; simp [insertPerm,insertNext]
    · simp [insertPerm,insertNext,h,Equiv.swap_apply_of_ne_of_ne]
  | inr u => cases u; simp [insertPerm,insertNext]

lemma insertPerm_step (p : Equiv.Perm W) (j i : W) :
    (insertPerm p j).SameCycle (Sum.inl i) (Sum.inl (p i)) := by
  by_cases h : i = j
  · subst i
    refine ⟨(2 : ℕ),?_⟩
    norm_num only [Int.cast_ofNat, zpow_ofNat]
    change insertPerm p j (insertPerm p j (Sum.inl j)) = Sum.inl (p j)
    simp [insertPerm_apply,insertNext]
  · refine ⟨1,?_⟩
    simp [insertPerm_apply,insertNext,h]

lemma insertPerm_pow (p : Equiv.Perm W) (j i : W) (n : ℕ) :
    (insertPerm p j).SameCycle (Sum.inl i) (Sum.inl ((p ^ n) i)) := by
  induction n with
  | zero => exact SameCycle.rfl
  | succ n ih =>
    have hs := insertPerm_step p j ((p ^ n) i)
    simpa only [pow_succ',Equiv.Perm.mul_apply] using ih.trans hs

lemma insertPerm_isCycleOn [Fintype W] (p : Equiv.Perm W) (j : W)
    (hp : p.IsCycleOn Set.univ) : (insertPerm p j).IsCycleOn Set.univ := by
  have h_old (x y : W) : (insertPerm p j).SameCycle (Sum.inl x) (Sum.inl y) := by
    have hp' : p.IsCycleOn (Finset.univ : Finset W) := by simpa using hp
    obtain ⟨n,_,hn⟩ := hp'.exists_pow_eq (a := x) (b := y) (Finset.mem_univ _) (Finset.mem_univ _)
    simpa only [hn] using insertPerm_pow p j x n
  have h_new : (insertPerm p j).SameCycle (Sum.inl j) (Sum.inr ()) := by
    refine ⟨1,?_⟩
    simp [insertPerm_apply,insertNext]
  refine ⟨(insertPerm p j).bijective.bijOn_univ,?_⟩
  intro x _ y _
  cases x with
  | inl x =>
    cases y with
    | inl y => exact h_old x y
    | inr u => cases u; exact (h_old x j).trans h_new
  | inr u =>
    cases u
    cases y with
    | inl y => exact h_new.symm.trans (h_old j y)
    | inr u => cases u; exact SameCycle.rfl
end Insert

lemma isCycleOn_permCongr {W W' : Type*} (e : W ≃ W') (p : Equiv.Perm W)
    (hp : p.IsCycleOn Set.univ) : (e.permCongrHom p).IsCycleOn Set.univ := by
  refine ⟨(e.permCongrHom p).bijective.bijOn_univ,?_⟩
  intro x _ y _
  obtain ⟨n,hn⟩ := hp.2 (x := e.symm x) (Set.mem_univ _) (y := e.symm y) (Set.mem_univ _)
  refine ⟨n,?_⟩
  rw [← map_zpow]
  change e ((p ^ n) (e.symm x)) = y
  rw [hn,e.apply_symm_apply]

namespace Marked

def nextPerm : (n : ℕ) → Order n → Equiv.Perm (Marker n)
  | 0, _ => Equiv.swap (0 : Fin 2) (1 : Fin 2)
  | n+1, o => insertPerm (nextPerm n o.1) o.2

lemma nextPerm_apply : ∀ n (o : Order n) (i : Marker n), nextPerm n o i = next n o i := by
  intro n
  induction n with
  | zero =>
    intro o i
    change (Equiv.swap (0 : Fin 2) 1) i = (![1,0] : Fin 2 → Fin 2) i
    fin_cases i <;> decide
  | succ n ih =>
    intro o i
    change insertPerm (nextPerm n o.1) o.2 i = insertNext (next n o.1) o.2 i
    rw [insertPerm_apply]
    have he : (nextPerm n o.1 : Marker n → Marker n) = next n o.1 := funext (ih o.1)
    rw [he]

lemma nextPerm_isCycleOn : ∀ n (o : Order n), (nextPerm n o).IsCycleOn Set.univ := by
  intro n
  induction n with
  | zero =>
    intro o
    have h := Equiv.Perm.isCycleOn_swap (by decide : (0 : Fin 2) ≠ 1)
    have hs : ({(0 : Fin 2),1} : Set (Fin 2)) = Set.univ := by ext i; fin_cases i <;> simp
    simpa only [hs] using h
  | succ n ih => intro o; exact insertPerm_isCycleOn _ _ (ih o.1)

def numberedPerm (n : ℕ) (o : Order n) : Equiv.Perm (Fin (n+2)) :=
  (markerEquiv n).permCongrHom (nextPerm n o)

lemma numberedPerm_apply (n : ℕ) (o : Order n) (i : Fin (n+2)) :
    numberedPerm n o i = nextFin n o i := by
  change markerEquiv n (nextPerm n o ((markerEquiv n).symm i)) = _
  rw [nextPerm_apply]
  rfl

lemma numberedPerm_isCycleOn (n : ℕ) (o : Order n) :
    (numberedPerm n o).IsCycleOn Set.univ :=
  isCycleOn_permCongr _ _ (nextPerm_isCycleOn n o)

lemma fastNext_coe_numberedPerm (n : ℕ) (o : Order n) :
    fastNext n o = (numberedPerm n o : Fin (n+2) → Fin (n+2)) := by
  funext i
  rw [fastNext_eq,numberedPerm_apply]

#print axioms numberedPerm_isCycleOn
end Marked
end Erdos184Work.CycleSegments
