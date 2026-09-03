import Submission.DigitLoopPeakExplore

/-! Last-visit coding of accepted words in an automaton whose productive
states have at most one loop of each length. This gives a polynomial word
count, without an asymptotic spectral theorem for transition matrices. -/
namespace Erdos66DfaLoopCode
open Erdos66DigitLoopPeak Filter AdditiveCombinatorics
open scoped Classical Topology
set_option maxHeartbeats 2000000

variable {α σ : Type*} (M : DFA α σ)

def ContextLoopUnique : Prop := ∀ a z : List α, a++z ∈ M.accepts →
  ∀ u v : List α, u.length=v.length →
    M.evalFrom (M.eval a) u=M.eval a → M.evalFrom (M.eval a) v=M.eval a → u=v

lemma eval_slice (w : List α) (k p : ℕ) (hkp : k ≤ p) :
    M.evalFrom (M.eval (w.take k)) ((w.drop k).take (p-k))=M.eval (w.take p) := by
  change M.evalFrom (M.evalFrom M.start (w.take k)) _=M.evalFrom M.start _
  rw [←M.evalFrom_of_append]
  congr 1
  rw [←List.take_add,Nat.add_sub_of_le hkp]

noncomputable def visits (w : List α) (q : σ) : Finset ℕ :=
  (Finset.range (w.length+1)).filter (fun k ↦ M.eval (w.take k)=q)

noncomputable def lastVisit (w : List α) (q : σ) : ℕ := (visits M w q).sup id

lemma lastVisit_le (w : List α) (q : σ) : lastVisit M w q ≤ w.length := by
  apply Finset.sup_le
  intro k hk
  have hh := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  exact Nat.le_of_lt_succ hh

lemma lastVisit_spec (w : List α) (q : σ) (k : ℕ) (hk : k ≤ w.length)
    (hq : M.eval (w.take k)=q) :
    k ≤ lastVisit M w q ∧ M.eval (w.take (lastVisit M w q))=q := by
  have hmem : k∈visits M w q := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hq⟩
  refine ⟨Finset.le_sup (f := id) hmem,?_⟩
  have hh := Finset.sup_mem_of_nonempty (f := id) (show (visits M w q).Nonempty from ⟨k,hmem⟩)
  have hh' : lastVisit M w q∈visits M w q := by simpa [lastVisit] using hh
  exact (Finset.mem_filter.mp hh').2

noncomputable def lastCode (n : ℕ) (w : List α) : σ → Fin (n+1) × Option α := fun q ↦
  (⟨min n (lastVisit M w q),by omega⟩,w[min n (lastVisit M w q)]?)

lemma lastCode_eq (n : ℕ) (w : List α) (hw : w.length=n) (q : σ) :
    ((lastCode M n w q).1 : ℕ)=lastVisit M w q ∧
      (lastCode M n w q).2=w[lastVisit M w q]? := by
  have hh := lastVisit_le M w q
  simp only [lastCode]
  rw [min_eq_right (by omega)]
  exact ⟨rfl,rfl⟩

/-- A word is determined by the last visit and exit letter at each state,
provided all productive equal-length loops are unique. -/
theorem lastCode_injective (hunique : ContextLoopUnique M) (n : ℕ) :
    Set.InjOn (lastCode M n) {w : List α | w.length=n ∧ w∈M.accepts} := by
  intro w hw v hv he
  have hwlen : w.length=n := hw.1
  have hvlen : v.length=n := hv.1
  have htake : ∀ k, k ≤ n → w.take k=v.take k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have hk' : k ≤ n := by omega
      have hprev := ih hk'
      let q := M.eval (w.take k)
      let p := lastVisit M w q
      have hqw : M.eval (w.take k)=q := rfl
      have hqv : M.eval (v.take k)=q := by rw [←hprev]
      obtain ⟨hkp,hwp⟩ := lastVisit_spec M w q k (by omega) hqw
      obtain ⟨hkp',hvp⟩ := lastVisit_spec M v q k (by omega) hqv
      have hp : lastVisit M w q=lastVisit M v q := by
        have hh := congrArg (fun r : Fin (n+1) × Option α ↦ (r.1 : ℕ)) (congrFun he q)
        simpa only [(lastCode_eq M n w hw.1 q).1,(lastCode_eq M n v hv.1 q).1] using hh
      have hexit : w[p]?=v[p]? := by
        have hh := congrArg Prod.snd (congrFun he q)
        simpa only [(lastCode_eq M n w hw.1 q).2,(lastCode_eq M n v hv.1 q).2,←hp] using hh
      have hpw : p ≤ w.length := lastVisit_le M w q
      have hpv : p ≤ v.length := by dsimp only [p]; rw [hp]; exact lastVisit_le M v q
      have heloop : (w.drop k).take (p-k)=(v.drop k).take (p-k) := by
        apply hunique (w.take k) (w.drop k) (by simpa using hw.2)
        · simp only [List.length_take,List.length_drop]
          omega
        · rw [eval_slice M w k p hkp]
          exact hwp
        · rw [show M.eval (w.take k)=M.eval (v.take k) by rw [hprev],eval_slice M v k p hkp]
          rw [←hp] at hvp
          exact hvp.trans hqv.symm
      have hletter : w[k]?=v[k]? := by
        by_cases hlt : k<p
        · have hh := congrArg (fun l : List α ↦ l[0]?) heloop
          simpa only [List.getElem?_take,List.getElem?_drop,
            if_pos (show 0<p-k by omega),Nat.add_zero] using hh
        · have heq : k=p := by omega
          simpa only [heq] using hexit
      rw [List.take_succ,List.take_succ,hprev,hletter]
  simpa only [List.take_of_length_le hwlen.le,List.take_of_length_le hvlen.le] using htake n le_rfl

/-- Polynomial accepted-word bound, with an explicit code size. -/
theorem accepted_finset_bound [Fintype σ] [Fintype α] (hunique : ContextLoopUnique M)
    (n : ℕ) (W : Finset (List α)) (hW : ∀ w∈W, w.length=n ∧ w∈M.accepts) :
    W.card ≤ ((n+1)*(Fintype.card α+1))^Fintype.card σ := by
  have hi := Finset.card_le_card_of_injOn (s := W)
    (t := (Finset.univ : Finset (σ → Fin (n+1) × Option α))) (lastCode M n)
    (by intro w hw; exact Finset.mem_univ _)
    (fun w hw v hv he ↦ lastCode_injective M hunique n (hW w hw) (hW v hv) he)
  simpa using hi

variable {b : ℕ}

lemma eval_blocks (M : DFA (Fin b) σ) (q : σ) (u v : List (Fin b))
    (hu : M.evalFrom q u=q) (hv : M.evalFrom q v=q) (xs : List Bool) :
    M.evalFrom q (blocks u v xs)=q := by
  induction xs with
  | nil => simp [blocks]
  | cons x xs ih => cases x <;> simp only [blocks,Bool.false_eq_true,↓reduceIte,
      M.evalFrom_of_append,hu,hv,ih]

/-- Any finite logarithmic representation limit makes all productive
same-length digit loops unique. Finiteness of the state space is not needed
for this implication. -/
theorem loop_unique_of_log_limit (hb : 1<b) (M : DFA (Fin b) σ) (A : Set ℕ)
    (hA : ∀ w∈M.accepts, code w∈A) (c : ℝ)
    (hc : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ContextLoopUnique M := by
  intro a z haz u v hl hu hv
  by_contra hne
  apply no_log_limit_of_digit_loops hb A a u v z hl hne ?_ c hc
  intro xs
  apply hA
  rw [DFA.mem_accepts,DFA.eval,DFA.evalFrom_of_append,DFA.evalFrom_of_append,
    eval_blocks M (M.evalFrom M.start a) u v hu hv]
  simpa only [DFA.mem_accepts,DFA.eval,DFA.evalFrom_of_append] using haz

end Erdos66DfaLoopCode
