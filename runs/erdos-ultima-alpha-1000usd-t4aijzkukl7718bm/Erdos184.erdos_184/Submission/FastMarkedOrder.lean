import Submission.NumberedCycleSegmentation

/-! Direct numbered successor tables for the recursive marked-cycle orders.
These avoid repeatedly evaluating conjugations through nested sum equivalences. -/
namespace Erdos184Work.CycleSegments.Marked
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

lemma markerEquiv_inl (n : ℕ) (i : Marker n) :
    markerEquiv (n+1) (Sum.inl i) = (markerEquiv n i).castSucc := by
  apply Fin.ext
  rfl

lemma markerEquiv_inr (n : ℕ) :
    markerEquiv (n+1) (Sum.inr ()) = Fin.last (n+2) := by
  apply Fin.ext
  rfl

lemma markerEquiv_symm_castSucc (n : ℕ) (i : Fin (n+2)) :
    (markerEquiv (n+1)).symm i.castSucc = Sum.inl ((markerEquiv n).symm i) := by
  apply (markerEquiv (n+1)).injective
  rw [Equiv.apply_symm_apply,markerEquiv_inl,Equiv.apply_symm_apply]

lemma markerEquiv_symm_last (n : ℕ) :
    (markerEquiv (n+1)).symm (Fin.last (n+2)) = Sum.inr () := by
  apply (markerEquiv (n+1)).injective
  rw [Equiv.apply_symm_apply,markerEquiv_inr]

lemma nextFin_castSucc (n : ℕ) (o : Order n) (j : Marker n) (i : Fin (n+2)) :
    nextFin (n+1) (o,j) i.castSucc =
      if i = markerEquiv n j then Fin.last (n+2) else (nextFin n o i).castSucc := by
  change markerEquiv (n+1) (next (n+1) (o,j) ((markerEquiv (n+1)).symm i.castSucc)) = _
  rw [markerEquiv_symm_castSucc]
  change markerEquiv (n+1) (if (markerEquiv n).symm i = j then Sum.inr ()
    else Sum.inl (next n o ((markerEquiv n).symm i))) = _
  by_cases h : i = markerEquiv n j
  · have hh : (markerEquiv n).symm i = j := by rw [h,Equiv.symm_apply_apply]
    rw [if_pos hh,if_pos h,markerEquiv_inr]
  · have hh : (markerEquiv n).symm i ≠ j := by
      intro he
      apply h
      have he' := congrArg (markerEquiv n) he
      simpa only [Equiv.apply_symm_apply] using he'
    rw [if_neg hh,if_neg h,markerEquiv_inl]
    rfl

lemma nextFin_last (n : ℕ) (o : Order n) (j : Marker n) :
    nextFin (n+1) (o,j) (Fin.last (n+2)) = (nextFin n o (markerEquiv n j)).castSucc := by
  change markerEquiv (n+1) (next (n+1) (o,j) ((markerEquiv (n+1)).symm (Fin.last (n+2)))) = _
  rw [markerEquiv_symm_last]
  change markerEquiv (n+1) (Sum.inl (next n o j)) = _
  rw [markerEquiv_inl]
  simp only [nextFin,Function.comp_apply,Equiv.symm_apply_apply]

def fastNext : (n : ℕ) → Order n → Fin (n+2) → Fin (n+2)
  | 0, _ => ![1,0]
  | n+1, o => Fin.lastCases
      (fastNext n o.1 (markerEquiv n o.2)).castSucc
      (fun i => if i = markerEquiv n o.2 then Fin.last (n+2) else (fastNext n o.1 i).castSucc)

lemma fastNext_eq : ∀ n (o : Order n), fastNext n o = nextFin n o := by
  intro n
  induction n with
  | zero => intro o; rfl
  | succ n ih =>
    intro o
    rcases o with ⟨o,j⟩
    funext i
    induction i using Fin.lastCases with
    | last => simp only [fastNext,Fin.lastCases_last,nextFin_last,ih]
    | cast i => simp only [fastNext,Fin.lastCases_castSucc,nextFin_castSucc,ih]

#print axioms fastNext_eq
end Erdos184Work.CycleSegments.Marked
