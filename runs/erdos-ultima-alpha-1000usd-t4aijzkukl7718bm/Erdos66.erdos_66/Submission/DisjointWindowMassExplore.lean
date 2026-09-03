import Submission.BracketWindowOccupancyExplore
import Submission.AntitoneFiniteMassExplore
import Submission.AdaptiveSingletonAlgebraExplore

/-! Summing old-point degrees over disjoint rows, including reflected rows
truncated at zero. -/
namespace Erdos66DisjointWindowMass
open Erdos66ShortSupportSwapTail Erdos66Rounding Erdos66ClampedPrefixContinuation Erdos66Fractional Erdos66ReflectionRoundingPatch
  Erdos66CumulativeRoundingError Erdos66AntitoneFiniteMass Erdos66AdaptiveSingletonAlgebra
open scoped Classical
set_option maxHeartbeats 2000000

lemma disjoint_intervals_count_bound (p : ℕ → ℝ) (hp : Antitone p) (hpos : ∀ i, 0 ≤ p i)
    (A : Set ℕ) (hbr : ∀ L, PrefixBrackets p A L)
    (m w : ℕ) (a b : ℕ → ℕ) (hab : ∀ k < m, a k ≤ b k)
    (hw : ∀ k < m, b k-a k ≤ w)
    (hdisj : (Finset.range m : Set ℕ).PairwiseDisjoint (fun k ↦ Finset.Ico (a k) (b k))) :
    (∑ k∈Finset.range m, ((intervalPart A (a k) (b k)).card : ℝ)) ≤
      2*m + ∑ i∈Finset.range (m*w), p i := by
  let S := (Finset.range m).biUnion (fun k ↦ Finset.Ico (a k) (b k))
  have hc : S.card ≤ m*w := by
    calc
      S.card ≤ ∑ k∈Finset.range m, (Finset.Ico (a k) (b k)).card := Finset.card_biUnion_le
      _ ≤ ∑ _k∈Finset.range m, w := Finset.sum_le_sum (fun k hk ↦ by
        simpa only [Nat.card_Ico] using hw k (Finset.mem_range.mp hk))
      _ = m*w := by simp
  have hm : (∑ k∈Finset.range m, ∑ i∈Finset.Ico (a k) (b k), p i) ≤
      ∑ i∈Finset.range (m*w), p i := by
    rw [←Finset.sum_biUnion hdisj]
    exact finite_sum_le_prefix_of_card_le p hp hpos S (m*w) hc
  have he (k : ℕ) (hk : k < m) : ((intervalPart A (a k) (b k)).card : ℝ) ≤
      2+∑ i∈Finset.Ico (a k) (b k), p i := by
    have h := (abs_le.mp (local_count_error A p 1
      (brackets_count_discrepancy p A hbr) (a k) (b k) (hab k hk))).2
    linarith
  have hs := Finset.sum_le_sum (fun k hk ↦ he k (Finset.mem_range.mp hk))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  linarith

/-- Summing reflected partner degrees pays one compressed profile prefix and
only two count-discrepancy units per row, rather than `m` worst-row bounds. -/
lemma sum_partnerChoices_bound (p : ℕ → ℝ) (hp : Antitone p) (hpos : ∀ i, 0 ≤ p i)
    (A : Set ℕ) (hbr : ∀ N, PrefixBrackets p A N) (A₀ : Finset ℕ) (hA₀ : (A₀ : Set ℕ) ⊆ A)
    (L : ℕ → ℕ) (w m : ℕ)
    (hsep : ∀ i < m, ∀ j < m, i≠j → L i+w ≤ L j ∨ L j+w ≤ L i)
    (z : ℕ) :
    (∑ k∈Finset.range m, ((partnerChoices A₀ (fun i : Fin w ↦ L k+i.val) z).card : ℝ)) ≤
      2*m + ∑ i∈Finset.range (m*w), p i := by
  let a (k : ℕ) := z+1-(L k+w)
  let b (k : ℕ) := z+1-L k
  have hd : (Finset.range m : Set ℕ).PairwiseDisjoint (fun k ↦ Finset.Ico (a k) (b k)) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro u hui huj
    simp only [Finset.mem_Ico,a,b] at hui huj
    rcases hsep i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij with h | h <;> omega
  have hc (k : ℕ) : (partnerChoices A₀ (fun i : Fin w ↦ L k+i.val) z).card ≤
      (intervalPart A (a k) (b k)).card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin w ↦ z-(L k+i.val))
    · intro i hi
      simp only [partnerChoices,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and] at hi
      change z-(L k+i.val) ∈ intervalPart A (a k) (b k)
      simp only [intervalPart,Finset.mem_filter,Finset.mem_Ico]
      refine ⟨?_,hA₀ hi.2⟩
      dsimp only [a,b]
      have := i.isLt
      omega
    · intro i hi j hj he
      simp only [partnerChoices,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
      change z-(L k+i.val)=z-(L k+j.val) at he
      apply Fin.ext
      omega
  have hs : (∑ k∈Finset.range m, ((partnerChoices A₀ (fun i : Fin w ↦ L k+i.val) z).card : ℝ)) ≤
      ∑ k∈Finset.range m, ((intervalPart A (a k) (b k)).card : ℝ) := by
    apply Finset.sum_le_sum
    intro k _
    exact_mod_cast hc k
  exact hs.trans (disjoint_intervals_count_bound p hp hpos A hbr m w a b
    (by intro k _; dsimp only [a,b]; omega) (by intro k _; dsimp only [a,b]; omega) hd)

end Erdos66DisjointWindowMass
