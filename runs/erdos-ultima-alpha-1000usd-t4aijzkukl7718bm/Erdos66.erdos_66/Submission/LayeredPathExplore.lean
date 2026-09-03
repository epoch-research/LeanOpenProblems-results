import Submission.LayeredDigitAsymptoticExplore

/-! Word semantics for position-dependent nondeterministic digit programs,
with an explicit initial digit offset. -/
namespace Erdos66LayeredPath
open Erdos66LayeredDigitProgram Erdos66DigitBoxEnergy Erdos66DfaCounting
  Erdos66DigitLoopPeak
open scoped Classical
set_option maxHeartbeats 2600000
variable {b : ℕ} {σ : Type*}

def Path (E : ℕ → σ → Fin b → σ → Prop) : ℕ → List (Fin b) → σ → σ → Prop
  | _, [], a, z => a=z
  | i, x::xs, a, z => ∃ t, E i a x t ∧ Path E (i+1) xs t z

lemma path_append (E : ℕ → σ → Fin b → σ → Prop) (w v : List (Fin b))
    (i : ℕ) (a z : σ) :
    Path E i (w++v) a z ↔ ∃ t, Path E i w a t ∧ Path E (i+w.length) v t z := by
  induction w generalizing i a with
  | nil => simp [Path]
  | cons x w ih =>
    simp only [List.cons_append,Path,List.length_cons]
    simp only [ih]
    constructor
    · rintro ⟨t,he,u,hw,hv⟩
      exact ⟨u,⟨t,he,hw⟩,by simpa only [Nat.add_assoc,Nat.add_comm 1] using hv⟩
    · rintro ⟨u,⟨t,he,hw⟩,hv⟩
      exact ⟨t,he,u,hw,by simpa only [Nat.add_assoc,Nat.add_comm 1] using hv⟩

lemma path_ofFn_iff (E : ℕ → σ → Fin b → σ → Prop) {k : ℕ}
    (x : Fin k → Fin b) (i : ℕ) (a z : σ) :
    Path E i (List.ofFn x) a z ↔ ∃ q : Fin (k+1) → σ,
      q 0=a ∧ q (Fin.last k)=z ∧
        ∀ j, E (i+j.val) (q j.castSucc) (x j) (q j.succ) := by
  induction k generalizing i a with
  | zero =>
    simp only [List.ofFn_zero,Path,Fin.last_zero,Fin.forall_fin_zero,and_true]
    constructor
    · intro h; exact ⟨fun _ ↦ a,rfl,h⟩
    · rintro ⟨q,hq,hz⟩; exact hq.symm.trans hz
  | succ k ih =>
    rw [List.ofFn_succ]
    simp only [Path]
    constructor
    · rintro ⟨t,he,ht⟩
      obtain ⟨q,hq0,hqz,hq⟩ := (ih (fun j ↦ x j.succ) (i+1) t).mp ht
      refine ⟨Fin.cases a q,by simp,?_,?_⟩
      · simpa using hqz
      · intro j
        refine Fin.cases ?_ (fun j ↦ ?_) j
        · simpa only [Fin.val_zero,Nat.add_zero,Fin.castSucc_zero,Fin.cases_zero,
            Fin.cases_succ,hq0] using he
        · simpa [Nat.add_assoc,Nat.add_comm 1] using hq j
    · rintro ⟨q,hq0,hqz,hq⟩
      refine ⟨q 1,?_,?_⟩
      · simpa [hq0] using hq 0
      · apply (ih (fun j ↦ x j.succ) (i+1) (q 1)).mpr
        refine ⟨fun j ↦ q j.succ,rfl,?_,?_⟩
        · simpa using hqz
        · intro j
          simpa [Nat.add_assoc,Nat.add_comm 1] using hq j.succ

end Erdos66LayeredPath
