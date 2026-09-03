import Submission.LocatedPredecessorPacketExplore
import Submission.IntervalPredecessorRepairExplore

/-! Support-localized finite predecessor repair. -/
namespace Erdos66LocatedIntervalPredecessor
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66PredecessorCell
  Erdos66PredecessorPacketRepair Erdos66PredecessorCandidateDegree
  Erdos66ReflectionRoundingPatch Erdos66FiniteSwapAlgebra Erdos66Counting
  Erdos66IntervalPredecessorRepair Erdos66LocatedPredecessorPacket
open scoped Classical
set_option maxHeartbeats 2200000

theorem exists_located_interval_predecessor_repair (A : Finset ℕ) (V : ℝ)
    (hA : ∀ z, (sumRep (A : Set ℕ) z : ℝ) ≤ V)
    (n L W H : ℕ) (hW : 0 < W) (hmargin : 2*(L+W)+H ≤ n)
    (hmem : ∀ b (i : Fin W), predecessor (A : Set ℕ) (endpoint n (fun i : Fin W ↦ L+i.val) b i) ∈ A)
    (hgap : ∀ b (i : Fin W), endpoint n (fun i : Fin W ↦ L+i.val) b i <
      predecessor (A : Set ℕ) (endpoint n (fun i : Fin W ↦ L+i.val) b i)+H)
    (m : ℕ) (T : Finset ℕ) (R t : ℝ) (ht : 0 < t)
    (hsmall : ((m : ℝ)^4+4*m^2*H+m*(2*Real.sqrt (2*W*V)+2*H*V))/W +
      T.card * Real.exp ((m : ℝ)*Real.exp t*(2*Real.sqrt (2*W*V)+2*H*V)/W-t*R) < 1) :
    ∃ D F : Finset ℕ, D ⊆ A ∧ Disjoint A F ∧ D.card = 2*m ∧ F.card = 2*m ∧
      (∀ N, -1 ≤ (count (swapped A D F : Set ℕ) N : ℝ)-count (A : Set ℕ) N ∧
        (count (swapped A D F : Set ℕ) N : ℝ)-count (A : Set ℕ) N ≤ 0) ∧
      sumRep (swapped A D F : Set ℕ) n = sumRep (A : Set ℕ) n+2*m ∧
      (∀ z, z ≠ n → sumRep (F : Set ℕ) z ≤ 6) ∧
      (∀ u ∈ D ∪ F, L ≤ u + H ∧ u ≤ n-L) ∧
      ∀ z ∈ T, z ≠ n →
        |(sumRep (swapped A D F : Set ℕ) z : ℝ)-sumRep (A : Set ℕ) z| < 4*R+6 := by
  letI : NeZero W := ⟨by omega⟩
  let x : Fin W → ℕ := fun i ↦ L+i.val
  let start : Bool → ℕ := fun b ↦ if b then n+1-(L+W) else L
  have hx : Function.Injective x := by
    intro i j he
    apply Fin.ext
    dsimp only [x] at he
    omega
  have hn : ∀ i, x i ≤ n := by
    intro i
    have hi := i.isLt
    dsimp only [x]
    omega
  have hhalf : ∀ i, 2*x i < n := by
    intro i
    have hi := i.isLt
    dsimp only [x]
    omega
  have hm : ∀ i, 2*x i+H ≤ n := by
    intro i
    have hi := i.isLt
    dsimp only [x]
    omega
  have hinj b := endpoint_injective n x hx hn b
  have hwindow : ∀ b i, start b ≤ endpoint n x b i ∧ endpoint n x b i < start b+W := by
    intro b i
    have hi := i.isLt
    cases b <;> simp [start, endpoint, x] <;> omega
  have hlocal := natural_window_bound A V hA
  have hdeg := predecessor_candidate_degrees A n x H W start (Real.sqrt (2*W*V))
    hinj hwindow (fun a ↦ hlocal a W) hmem hgap
  have hdegree (z : ℕ) : 2*Real.sqrt (2*W*V)+2*H*sumRep (A : Set ℕ) z ≤
      2*Real.sqrt (2*W*V)+2*H*V := by
    have hh := mul_le_mul_of_nonneg_left (hA z) (show (0 : ℝ) ≤ 2*H by positivity)
    linarith only [hh]
  obtain ⟨D,F,hD,hF,hDc,hFc,hpref,htarget,hself,hshape,hpoints,hcol⟩ :=
    exists_predecessor_packet_repair_located A n x hx hhalf hmem H
    (fun b r ↦ endpoint_fiber_bound (A : Set ℕ) (endpoint n x b) (hinj b) H (hgap b) r)
    (endpoint_cells_separated (A : Set ℕ) n x H hm (hgap true)) m T
    (2*Real.sqrt (2*W*V)+2*H*V) (2*Real.sqrt (2*W*V)+2*H*V) R t
    (hdeg.1.trans (hdegree n)) (fun z _ ↦ (hdeg.2 z).trans (hdegree z)) ht
    (by simpa only [Fintype.card_fin] using hsmall)
  refine ⟨D,F,hD,hF,hDc,hFc,hpref,htarget,hself,?_,hcol⟩
  have hp (u : ℕ) (hu : u ∈ F) : L ≤ u ∧ u ≤ n-L := by
    obtain ⟨b,i,rfl⟩ := hpoints u hu
    have hi := i.isLt
    cases b <;> simp only [endpoint, Bool.false_eq_true, if_false, if_true, x] <;> omega
  intro u hu
  rcases Finset.mem_union.mp hu with hu | hu
  · rw [hshape] at hu
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b,i,rfl⟩ := hpoints v hv
    have hh : endpoint n x b i < predecessor (A : Set ℕ) (endpoint n x b i)+H := hgap b i
    have hl := (hp _ hv).1
    have hb := (hp _ hv).2
    have hh' := predecessor_le (A : Set ℕ) (endpoint n x b i)
    exact ⟨by omega, by omega⟩
  · have hh := hp u hu
    exact ⟨by omega,hh.2⟩

end Erdos66LocatedIntervalPredecessor
