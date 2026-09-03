import FormalConjecturesUtil

/-! Kernel-checkable prime coverage using proper-factor witnesses.
Primality of the candidate list is not assumed or asserted. -/
namespace Erdos7PrimeCoverage
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

def entryCheck (P : ℕ → ℕ) (count n w : ℕ) : Bool :=
  if 2048 ≤ w then decide (w-2048 < count) && (n==P (w-2048))
  else decide (1 < w) && decide (w < n) && (n%w==0)

lemma entryCheck_sound (P : ℕ → ℕ) (count n w : ℕ) (hn : n.Prime)
    (hh : entryCheck P count n w=true) : ∃ j,j < count ∧ P j=n := by
  unfold entryCheck at hh
  split_ifs at hh with hw
  · simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hh
    exact ⟨w-2048,hh.1,hh.2.symm⟩
  · simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hh
    have hd : w ∣ n := Nat.dvd_of_mod_eq_zero hh.2
    have he := hn.eq_one_or_self_of_dvd w hd
    omega

def coverageCheck (lo width count : ℕ) (P W : ℕ → ℕ) : Bool :=
  (List.range' lo width).all (fun n => entryCheck P count n (W (n-lo)))

lemma coverageCheck_sound (lo width count : ℕ) (P W : ℕ → ℕ)
    (hh : coverageCheck lo width count P W=true) (n : ℕ) (hn : n.Prime)
    (hlo : lo ≤ n) (hhi : n < lo+width) : ∃ j,j < count ∧ P j=n := by
  simp only [coverageCheck,List.all_eq_true,List.mem_range'] at hh
  exact entryCheck_sound P count n _ hn (hh n ⟨n-lo,by omega,by omega⟩)

/-- Every checked candidate is in the interval and successive candidates are ordered. -/
def orderCheck (lo hi count : ℕ) (P : ℕ → ℕ) : Bool :=
  (List.range count).all (fun j => decide (lo ≤ P j) && decide (P j < hi) &&
    (if j+1 < count then decide (P j < P (j+1)) else true))

lemma orderCheck_mem (lo hi count : ℕ) (P : ℕ → ℕ) (hh : orderCheck lo hi count P=true)
    (j : ℕ) (hj : j < count) : lo ≤ P j ∧ P j < hi := by
  simp only [orderCheck,List.all_eq_true,List.mem_range,Bool.and_eq_true,decide_eq_true_eq] at hh
  exact (hh j hj).1

lemma orderCheck_succ (lo hi count : ℕ) (P : ℕ → ℕ) (hh : orderCheck lo hi count P=true)
    (j : ℕ) (hj : j+1 < count) : P j < P (j+1) := by
  simp only [orderCheck,List.all_eq_true,List.mem_range,Bool.and_eq_true,decide_eq_true_eq] at hh
  have hr := (hh j (by omega)).2
  simpa only [if_pos hj,decide_eq_true_eq] using hr

lemma orderCheck_strictMono (lo hi count : ℕ) (P : ℕ → ℕ) (hh : orderCheck lo hi count P=true) :
    StrictMono (fun j : Fin count => P j.val) := by
  cases count with
  | zero => intro i; exact Fin.elim0 i
  | succ count =>
    apply Fin.strictMono_iff_lt_succ.mpr
    intro j
    exact orderCheck_succ lo hi (count+1) P hh j.val (by omega)

#print axioms coverageCheck_sound
end Erdos7PrimeCoverage
