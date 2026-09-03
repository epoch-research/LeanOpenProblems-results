import Submission.PredecessorCandidateDegreeExplore

/-! A concrete interval version of the finite predecessor repair criterion.
The assumptions are a representation envelope and a gap bound on the two
endpoint windows; there are no unbounded difference-correlation assumptions. -/
namespace Erdos66IntervalPredecessorRepair
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66PredecessorCell
  Erdos66PredecessorPacketRepair Erdos66PredecessorCandidateDegree
  Erdos66ReflectionRoundingPatch Erdos66FiniteSwapAlgebra Erdos66Counting
open scoped Classical
set_option maxHeartbeats 2200000

lemma natural_window_bound (A : Finset ℕ) (V : ℝ)
    (hA : ∀ z, (sumRep (A : Set ℕ) z : ℝ) ≤ V) (L W : ℕ) :
    ((intervalPart (A : Set ℕ) L (L+W)).card : ℝ) ≤ Real.sqrt (2*W*V) := by
  let Q := intervalPart (A : Set ℕ) L (L+W)
  let T := Finset.Ico (2*L) (2*L+2*W)
  have hQA : Q ⊆ A := by
    intro a ha
    have hh : (L ≤ a ∧ a < L+W) ∧ a ∈ A := by
      simpa only [Q, intervalPart, Finset.mem_filter, Finset.mem_Ico, Finset.mem_coe] using ha
    exact hh.2
  have hmap : Set.MapsTo (fun p : ℕ × ℕ ↦ p.1+p.2) (Q.product Q : Set (ℕ × ℕ)) (T : Set ℕ) := by
    intro p hp
    obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
    have hh1 : (L ≤ p.1 ∧ p.1 < L+W) ∧ p.1 ∈ A := by
      simpa only [Q, intervalPart, Finset.mem_filter, Finset.mem_Ico, Finset.mem_coe] using hp1
    have hh2 : (L ≤ p.2 ∧ p.2 < L+W) ∧ p.2 ∈ A := by
      simpa only [Q, intervalPart, Finset.mem_filter, Finset.mem_Ico, Finset.mem_coe] using hp2
    obtain ⟨⟨hl1,hu1⟩,_⟩ := hh1
    obtain ⟨⟨hl2,hu2⟩,_⟩ := hh2
    change p.1+p.2 ∈ Finset.Ico (2*L) (2*L+2*W)
    apply Finset.mem_Ico.mpr
    constructor <;> omega
  have hmass : (Q.card : ℝ)^2 = ∑ z ∈ T, (pairs Q Q z : ℝ) := by
    have hh := Finset.card_eq_sum_card_fiberwise hmap
    change (Q.product Q).card = ∑ z ∈ T, pairs Q Q z at hh
    simp only [Finset.product_eq_sprod, Finset.card_product] at hh
    have hh' : (Q.card : ℝ)*Q.card = ∑ z ∈ T, (pairs Q Q z : ℝ) := by exact_mod_cast hh
    nlinarith only [hh']
  have hsq : (Q.card : ℝ)^2 ≤ 2*W*V := by
    rw [hmass]
    calc
      _ ≤ ∑ _z ∈ T, V := by
        apply Finset.sum_le_sum
        intro z hz
        have hh := (pairs_mono_left hQA z).trans (pairs_mono_right hQA z)
        have hh' : (pairs Q Q z : ℝ) ≤ sumRep (A : Set ℕ) z := by
          rw [← pairs_self]
          exact_mod_cast hh
        exact hh'.trans (hA z)
      _ = _ := by
        simp only [T, Finset.sum_const, nsmul_eq_mul, Nat.card_Ico,
          Nat.add_sub_cancel_left, Nat.cast_mul, Nat.cast_ofNat]
  have hh := Real.sqrt_le_sqrt hsq
  simpa only [Real.sqrt_sq (Nat.cast_nonneg _)] using hh

lemma endpoint_injective {α : Type*} (n : ℕ) (x : α → ℕ)
    (hx : Function.Injective x) (hn : ∀ a, x a ≤ n) (b : Bool) :
    Function.Injective (endpoint n x b) := by
  cases b with
  | false => exact hx
  | true =>
    intro a b he
    simp only [endpoint, if_true] at he
    exact hx (by have := hn a; have := hn b; omega)

lemma endpoint_cells_separated {α : Type*} (A : Set ℕ) (n : ℕ) (x : α → ℕ) (H : ℕ)
    (hmargin : ∀ a, 2*x a+H ≤ n)
    (hgap : ∀ a, n-x a < predecessor A (n-x a)+H) :
    ∀ a, Function.Injective (fun b ↦ predecessor A (endpoint n x b a)) := by
  intro a b c he
  have hlow := predecessor_le A (x a)
  have hhigh := hgap a
  have hm := hmargin a
  have hlt : predecessor A (x a) < predecessor A (n-x a) := by omega
  cases b <;> cases c <;> simp only [endpoint, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_false, Bool.not_true, ↓reduceIte] at he ⊢ <;> omega

/-- An interval of width W supplies a 2m-point symmetric packet and the same
number of predecessor deletions whenever the stated finite criterion holds. -/
theorem exists_interval_predecessor_repair (A : Finset ℕ) (V : ℝ)
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
  apply exists_predecessor_packet_repair A n x hx hhalf hmem H
    (fun b r ↦ endpoint_fiber_bound (A : Set ℕ) (endpoint n x b) (hinj b) H (hgap b) r)
    (endpoint_cells_separated (A : Set ℕ) n x H hm (hgap true)) m T
    (2*Real.sqrt (2*W*V)+2*H*V) (2*Real.sqrt (2*W*V)+2*H*V) R t
    (hdeg.1.trans (hdegree n)) (fun z _ ↦ (hdeg.2 z).trans (hdegree z)) ht
  simpa only [Fintype.card_fin] using hsmall

end Erdos66IntervalPredecessorRepair
