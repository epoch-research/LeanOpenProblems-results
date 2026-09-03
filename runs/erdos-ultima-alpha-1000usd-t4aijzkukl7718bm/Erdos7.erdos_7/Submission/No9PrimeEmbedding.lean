import Submission.No9ScheduledArithmetic
import Submission.No9SmallCandidates

/-! Padding arbitrary finite prime supports into the certified sequence. -/
namespace Erdos7No9Certificate
open scoped BigOperators
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

noncomputable def extendedCandidate (T : Finset ℕ) (i : Fin (smallLength+T.card)) : ℕ :=
  if hi : i.val < smallLength then smallCandidate i.val else
    T.orderEmbOfFin rfl ⟨i.val-smallLength,by omega⟩

lemma extendedCandidate_small (T : Finset ℕ) (i : Fin (smallLength+T.card)) (hi : i.val < smallLength) :
    extendedCandidate T i=smallCandidate i.val := by simp only [extendedCandidate,dif_pos hi]

lemma extendedCandidate_tail_mem (T : Finset ℕ) (i : Fin (smallLength+T.card)) (hi : smallLength ≤ i.val) :
    extendedCandidate T i∈T := by
  simp only [extendedCandidate,dif_neg (Nat.not_lt.mpr hi)]
  exact T.orderEmbOfFin_mem rfl _

lemma extendedCandidate_strictMono (T : Finset ℕ) (hT : ∀ q∈T,1500000 < q) : StrictMono (extendedCandidate T) := by
  intro i j hij
  have hij' : i.val < j.val := hij
  by_cases hi : i.val < smallLength
  · by_cases hj : j.val < smallLength
    · rw [extendedCandidate_small T i hi,extendedCandidate_small T j hj]
      exact smallCandidate_strictMono (show (⟨i.val,hi⟩:Fin smallLength) < ⟨j.val,hj⟩ from hij')
    · rw [extendedCandidate_small T i hi]
      exact (smallCandidate_bounds i.val hi).2.trans_lt (hT _ (extendedCandidate_tail_mem T j (by omega)))
  · have hj : ¬j.val < smallLength := by omega
    simp only [extendedCandidate,dif_neg hi,dif_neg hj]
    exact (T.orderEmbOfFin rfl).strictMono (by change i.val-smallLength < j.val-smallLength; omega)

lemma extendedCandidate_tail_covers (T : Finset ℕ) (q : ℕ) (hq : q∈T) :
    ∃ i : Fin (smallLength+T.card),extendedCandidate T i=q := by
  let j : Fin T.card := (T.orderIsoOfFin rfl).symm ⟨q,hq⟩
  let i : Fin (smallLength+T.card) := ⟨smallLength+j.val,by have := j.isLt; omega⟩
  refine ⟨i,?_⟩
  have hi : ¬i.val < smallLength := by dsimp [i]; omega
  simp only [extendedCandidate,dif_neg hi]
  have hj : (⟨i.val-smallLength,by have := i.isLt; omega⟩:Fin T.card)=j := by
    apply Fin.ext
    simp only [i,Nat.add_sub_cancel_left]
  rw [hj]
  have hh := (T.orderIsoOfFin rfl).apply_symm_apply ⟨q,hq⟩
  exact congrArg Subtype.val hh

lemma extendedCandidate_covers (T : Finset ℕ) (q : ℕ) (hq : q.Prime) (hq0 : 3 ≤ q)
    (hqT : 1500000 < q → q∈T) : ∃ i : Fin (smallLength+T.card),extendedCandidate T i=q := by
  by_cases hqsmall : q ≤ 1500000
  · obtain ⟨j,hj,hjp⟩ := smallCandidate_covers q hq hq0 hqsmall
    let i : Fin (smallLength+T.card) := ⟨j,by omega⟩
    exact ⟨i,by simpa only [extendedCandidate_small T i hj] using hjp⟩
  · exact extendedCandidate_tail_covers T q (hqT (by omega))

noncomputable def requiredExponent (t : ℕ) : ℕ :=
  if t < prefixLength then (prefixControl t).R else
  if t < smallLength then (blockControl (blockPosition t).1).R else 1

lemma requiredExponent_prefix (t : ℕ) (ht : t < prefixLength) : requiredExponent t=(prefixControl t).R := by
  simp only [requiredExponent,if_pos ht]

lemma requiredExponent_block (b j : ℕ) (hb : b < blockLength) (hj : j < (blockControl b).count) :
    requiredExponent (blockOffset b+j)=(blockControl b).R := by
  have hh := block_index_bounds b j hb hj
  simp only [requiredExponent,if_neg (Nat.not_lt.mpr hh.1),if_pos hh.2,blockPosition_eq b j hb hj]

noncomputable def paddedExponent {n : ℕ} {κ : Type*} [Fintype κ]
    (p : Fin n → ℕ) (e : κ → Fin n → ℕ) (i : Fin n) : ℕ :=
  if p i=3 then 1 else max 1 (max (requiredExponent i.val) (Finset.univ.sup (fun k => e k i)))

lemma paddedExponent_pos {n : ℕ} {κ : Type*} [Fintype κ]
    (p : Fin n → ℕ) (e : κ → Fin n → ℕ) (i : Fin n) : 0 < paddedExponent p e i := by
  unfold paddedExponent
  split_ifs <;> omega

lemma paddedExponent_le {n : ℕ} {κ : Type*} [Fintype κ]
    (p : Fin n → ℕ) (e : κ → Fin n → ℕ) (h3 : ∀ k i,p i=3 → e k i ≤ 1)
    (k : κ) (i : Fin n) : e k i ≤ paddedExponent p e i := by
  unfold paddedExponent
  split_ifs with hi
  · exact h3 k i hi
  · exact (Finset.le_sup (f:=fun k => e k i) (Finset.mem_univ k)).trans ((le_max_right _ _).trans (le_max_right _ _))

lemma paddedExponent_required {n : ℕ} {κ : Type*} [Fintype κ]
    (p : Fin n → ℕ) (e : κ → Fin n → ℕ) (i : Fin n) (hi : p i≠3) :
    requiredExponent i.val ≤ paddedExponent p e i := by
  simp only [paddedExponent,if_neg hi]
  exact (le_max_left _ _).trans (le_max_right _ _)

lemma padded_prime_schedule {κ : Type*} [Fintype κ] (T : Finset ℕ)
    (hT : ∀ q∈T,q.Prime ∧ 1500000 < q) (e : κ → Fin (smallLength+T.card) → ℕ) :
    PrimeSchedule (extendedCandidate T) (paddedExponent (extendedCandidate T) e) := by
  refine ⟨by omega,extendedCandidate_strictMono T (fun q hq => (hT q hq).2),
    paddedExponent_pos _ _,?_,?_,?_⟩
  · intro i hi
    have hsmall : i.val < smallLength := hi.trans_le prefix_le_small
    have hp : extendedCandidate T i=(prefixControl i.val).p := by
      rw [extendedCandidate_small T i hsmall,smallCandidate_prefix i.val hi]
    refine ⟨hp,?_⟩
    split_ifs with h3
    · simp only [paddedExponent,hp,if_pos h3]
    · have hp3 : extendedCandidate T i≠3 := by simpa only [hp] using h3
      simpa only [requiredExponent_prefix i.val hi] using paddedExponent_required (extendedCandidate T) e i hp3
  · intro i b j hb hj heq
    have hbounds := block_index_bounds b j hb hj
    have hsmall : i.val < smallLength := by omega
    have hp : extendedCandidate T i=blockCandidate b j := by
      rw [extendedCandidate_small T i hsmall,heq,smallCandidate_block b j hb hj]
    have hc := block_candidate_bounds b hb j hj
    refine ⟨by simpa only [hp] using hc.1,by simpa only [hp] using hc.2.le,?_⟩
    have hp3 : extendedCandidate T i≠3 := by
      have hh := (block_candidate_global_bounds b j hb hj).1
      rw [hp]
      omega
    have he := paddedExponent_required (extendedCandidate T) e i hp3
    simpa only [heq,requiredExponent_block b j hb hj] using he
  · intro i hi
    have hh := hT _ (extendedCandidate_tail_mem T i hi)
    exact ⟨hh.1,hh.2.le⟩

#print axioms padded_prime_schedule
end Erdos7No9Certificate
