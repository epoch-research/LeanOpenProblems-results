import Submission.RankProfileGapExplore

/-! Long one-sided replacement windows in a specified cumulative-rank cell.
This reverses the earlier viewpoint: the deleted old point is prescribed. -/
namespace Erdos66RankCellWindow
open Erdos66Counting Erdos66Generating Erdos66ClampedPrefixContinuation
  Erdos66BracketOrderedExchange Erdos66BracketRankMove Erdos66RankCellExchange
open scoped Classical
set_option maxHeartbeats 2200000

lemma count_strict_of_mem (A : Set ℕ) (d e : ℕ) (hd : d∈A) (hde : d<e) :
    count A d<count A e := by
  have hh := count_monotone A (show d+1 ≤ e by omega)
  rw [count_succ,if_pos hd] at hh
  omega

lemma count_injOn (A : Set ℕ) : Set.InjOn (count A) A := by
  intro d hd e he hcount
  rcases lt_trichotomy d e with h | h | h
  · have hh := count_strict_of_mem A d e hd h
    omega
  · exact h
  · have hh := count_strict_of_mem A e d he h
    omega

lemma rankPoint_at_mem (A : Set ℕ) (hunb : ∀ j, ∃ N, j<count A N)
    (d : ℕ) (hd : d∈A) : rankPoint A hunb (count A d)=d :=
  count_injOn A (rankPoint_mem A hunb _) hd (rankPoint_count A hunb _)

lemma mass_add_upper (p : ℕ → ℝ) (hp : Antitone p) (a w : ℕ) :
    mass p (a+w) ≤ mass p a+(w : ℝ)*p a := by
  have he : mass p (a+w)=mass p a+∑ i∈Finset.range w, p (a+i) := Finset.sum_range_add p a w
  rw [he]
  have hh : (∑ i∈Finset.range w, p (a+i)) ≤ ∑ _i∈Finset.range w, p a :=
    Finset.sum_le_sum (fun i _ ↦ hp (by omega))
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,add_comm] using add_le_add_right hh (mass p a)

/-- A quarter-unit mass bound on a centered window leaves an entire one-sided
window in the old point's rank cell. Every candidate differs from the old point. -/
theorem exists_rank_cell_window (p : ℕ → ℝ) (A : Set ℕ)
    (hp : ∀ i, 0 ≤ p i) (hanti : Antitone p) (hbr : ∀ L, PrefixBrackets p A L)
    (hunb : ∀ j, ∃ N, j<count A N) (d w : ℕ) (hd : d∈A) (hwd : w ≤ d)
    (hmass : (w : ℝ)*p (d-w) ≤ 1/4) :
    ∃ L : ℕ, d-w ≤ L ∧ L ≤ d+1 ∧
      ∀ i : Fin w, d-w ≤ L+i.val ∧ L+i.val ≤ d+w ∧ L+i.val≠d ∧
        cell p (L+i.val)=count A d ∧
        rankPoint A hunb (cell p (L+i.val))=d := by
  let j := count A d
  have hb := rankPoint_mass_bounds p A hbr hunb j
  rw [show rankPoint A hunb j=d from rankPoint_at_mem A hunb d hd] at hb
  have hcell (u : ℕ) (hlo : (j : ℝ) < mass p u) (hhi : mass p u<(j : ℝ)+1) :
      cell p u=j ∧ rankPoint A hunb (cell p u)=d := by
    have he : cell p u=j := (Nat.floor_eq_iff (Finset.sum_nonneg (fun i _ ↦ hp i))).mpr ⟨hlo.le,hhi⟩
    exact ⟨he,by rw [he]; exact rankPoint_at_mem A hunb d hd⟩
  by_cases hm : mass p d ≤ (j : ℝ)+1/2
  · refine ⟨d+1,by omega,le_rfl,?_⟩
    intro i
    have hi := i.isLt
    have hsmall : (w : ℝ)*p d ≤ 1/4 :=
      (mul_le_mul_of_nonneg_left (hanti (show d-w ≤ d by omega)) (Nat.cast_nonneg w)).trans hmass
    have hupper := mass_add_upper p hanti d w
    have hlo := mass_mono hp (show d+1 ≤ d+1+i.val by omega)
    have hhi := mass_mono hp (show d+1+i.val ≤ d+w by omega)
    obtain ⟨hc,hr⟩ := hcell (d+1+i.val) (by linarith [hb.2]) (by linarith)
    exact ⟨by omega,by omega,by omega,hc,hr⟩
  · refine ⟨d-w,le_rfl,by omega,?_⟩
    intro i
    have hi := i.isLt
    have hupper := mass_add_upper p hanti (d-w) w
    rw [Nat.sub_add_cancel hwd] at hupper
    have hlo := mass_mono hp (show d-w ≤ d-w+i.val by omega)
    have hhi := mass_mono hp (show d-w+i.val ≤ d by omega)
    obtain ⟨hc,hr⟩ := hcell (d-w+i.val) (by linarith) (by linarith [hb.1])
    exact ⟨by omega,by omega,by omega,hc,hr⟩

end Erdos66RankCellWindow
