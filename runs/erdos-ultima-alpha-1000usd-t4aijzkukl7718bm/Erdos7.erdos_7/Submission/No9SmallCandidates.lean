import Submission.No9Coverage

/-! A finite strictly increasing list containing every small odd prime. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

lemma prefix_order_facts : (prefixControl 0).p=3 ∧ (prefixControl (prefixLength-1)).p < 5000 ∧
    ∀ i,i < prefixLength-1 → (prefixControl i).p < (prefixControl (i+1)).p := by
  simpa only [prefixOrderCheck,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,List.all_eq_true,List.mem_range,and_assoc] using prefix_order_check

lemma prefix_candidates_strictMono : StrictMono (fun i : Fin prefixLength => (prefixControl i.val).p) := by
  change StrictMono (fun i : Fin (667+1) => (prefixControl i.val).p)
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact prefix_order_facts.2.2 i.val i.isLt

lemma prefix_candidate_bounds (i : ℕ) (hi : i < prefixLength) : 3 ≤ (prefixControl i).p ∧ (prefixControl i).p < 5000 := by
  have hp : 0 < prefixLength := by decide +kernel
  have h0 := prefix_candidates_strictMono.monotone
    (show (⟨0,hp⟩:Fin prefixLength) ≤ ⟨i,hi⟩ from Nat.zero_le _)
  have h1 := prefix_candidates_strictMono.monotone
    (show (⟨i,hi⟩:Fin prefixLength) ≤ ⟨prefixLength-1,by omega⟩ from by change i ≤ prefixLength-1; omega)
  exact ⟨by simpa only [prefix_order_facts.1] using h0,h1.trans_lt prefix_order_facts.2.1⟩

lemma block_boundary_strictMono : StrictMono (fun i : Fin (blockLength+1) => blockBoundary i.val) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  change blockBoundary i.val < blockBoundary (i.val+1)
  rw [block_boundary_eq_lo i.val i.isLt,block_boundary_succ]
  exact (block_coverage_facts i.val i.isLt).1

lemma block_boundary_mono {i j : ℕ} (hij : i ≤ j) (hj : j ≤ blockLength) : blockBoundary i ≤ blockBoundary j :=
  block_boundary_strictMono.monotone (show (⟨i,by omega⟩:Fin (blockLength+1)) ≤ ⟨j,by omega⟩ from hij)

lemma block_candidate_global_bounds (b j : ℕ) (hb : b < blockLength) (hj : j < (blockControl b).count) :
    5000 ≤ blockCandidate b j ∧ blockCandidate b j ≤ 1500000 := by
  have hlo := block_boundary_mono (Nat.zero_le b) hb.le
  have hhi := block_boundary_mono (show b+1 ≤ blockLength by omega) le_rfl
  rw [block_boundary_zero,block_boundary_eq_lo b hb] at hlo
  rw [block_boundary_last,block_boundary_succ] at hhi
  have hr := block_candidate_bounds b hb j hj
  omega

noncomputable def smallCandidate (t : ℕ) : ℕ :=
  if t < prefixLength then (prefixControl t).p else blockCandidate (blockPosition t).1 (blockPosition t).2

lemma smallCandidate_prefix (i : ℕ) (hi : i < prefixLength) : smallCandidate i=(prefixControl i).p := by
  simp only [smallCandidate,if_pos hi]

lemma smallCandidate_block (b j : ℕ) (hb : b < blockLength) (hj : j < (blockControl b).count) :
    smallCandidate (blockOffset b+j)=blockCandidate b j := by
  have hbounds := block_index_bounds b j hb hj
  simp only [smallCandidate,if_neg (Nat.not_lt.mpr hbounds.1),blockPosition_eq b j hb hj]

lemma smallCandidate_bounds (i : ℕ) (hi : i < smallLength) : 3 ≤ smallCandidate i ∧ smallCandidate i ≤ 1500000 := by
  by_cases hp : i < prefixLength
  · rw [smallCandidate_prefix i hp]
    have hh := prefix_candidate_bounds i hp
    omega
  · obtain ⟨b,j,hb,hj,rfl⟩ := small_index_block i (by omega) hi
    rw [smallCandidate_block b j hb hj]
    have hh := block_candidate_global_bounds b j hb hj
    omega

lemma smallCandidate_covers (p : ℕ) (hp : p.Prime) (hp0 : 3 ≤ p) (hp1 : p ≤ 1500000) :
    ∃ i,i < smallLength ∧ smallCandidate i=p := by
  rcases all_small_primes_covered p hp hp0 hp1 with ⟨i,hi,he⟩ | ⟨b,j,hb,hj,he⟩
  · exact ⟨i,hi.trans_le prefix_le_small,by rwa [smallCandidate_prefix i hi]⟩
  · exact ⟨blockOffset b+j,(block_index_bounds b j hb hj).2,by rwa [smallCandidate_block b j hb hj]⟩

lemma smallCandidate_strictMono : StrictMono (fun i : Fin smallLength => smallCandidate i.val) := by
  intro i j hij
  change smallCandidate i.val < smallCandidate j.val
  change i.val < j.val at hij
  by_cases hi : i.val < prefixLength
  · by_cases hj : j.val < prefixLength
    · rw [smallCandidate_prefix i.val hi,smallCandidate_prefix j.val hj]
      exact prefix_candidates_strictMono (show (⟨i.val,hi⟩:Fin prefixLength) < ⟨j.val,hj⟩ from hij)
    · obtain ⟨b,k,hb,hk,hjEq⟩ := small_index_block j.val (by omega) j.isLt
      rw [smallCandidate_prefix i.val hi,hjEq,smallCandidate_block b k hb hk]
      exact (prefix_candidate_bounds i.val hi).2.trans_le (block_candidate_global_bounds b k hb hk).1
  · have hj : prefixLength ≤ j.val := by omega
    obtain ⟨b,k,hb,hk,hiEq⟩ := small_index_block i.val (by omega) i.isLt
    obtain ⟨d,l,hd,hl,hjEq⟩ := small_index_block j.val hj j.isLt
    rw [hiEq,hjEq] at hij
    rw [hiEq,hjEq,smallCandidate_block b k hb hk,smallCandidate_block d l hd hl]
    by_cases hbd : b=d
    · subst d
      exact block_candidates_strictMono b hb (show (⟨k,hk⟩:Fin (blockControl b).count) < ⟨l,hl⟩ from by change k < l; omega)
    · have hlt : b < d := by
        by_contra hn
        have hdb : d+1 ≤ b := by omega
        have hm := block_offset_mono hdb hb.le
        rw [block_offset_succ d hd] at hm
        omega
      have hm := block_boundary_mono (show b+1 ≤ d by omega) hd.le
      rw [block_boundary_succ,block_boundary_eq_lo d hd] at hm
      exact (block_candidate_bounds b hb k hk).2.trans_le (hm.trans (block_candidate_bounds d hd l hl).1)

#print axioms smallCandidate_covers
#print axioms smallCandidate_strictMono
end Erdos7No9Certificate
