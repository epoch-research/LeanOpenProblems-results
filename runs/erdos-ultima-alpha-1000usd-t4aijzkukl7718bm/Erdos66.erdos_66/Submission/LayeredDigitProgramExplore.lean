import Submission.DigitBoxEnergyExplore

/-! A finite counting restriction for position-dependent digit programs.
The transition relation can change at every position and can be
nondeterministic. No stationary automaton is assumed. -/
namespace Erdos66LayeredDigitProgram
open Erdos66DigitBoxEnergy AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 2600000
variable {b k : ℕ} {σ : Type*} [Fintype σ]

/-- An edge relation for each digit position. Initial and accepting states
are explicit; transitions need not be deterministic. -/
structure Program (b k : ℕ) (σ : Type*) where
  edge : Fin k → σ → Fin b → σ → Prop
  initial : σ
  accepting : Set σ

noncomputable def paths (P : Program b k σ) : Finset (Fin (k+1) → σ) :=
  Finset.univ.filter (fun q ↦ q 0=P.initial ∧ q (Fin.last k)∈P.accepting)

noncomputable def pathDigits (P : Program b k σ) (q : Fin (k+1) → σ) :
    Fin k → Finset (Fin b) := fun i ↦
  Finset.univ.filter (fun a ↦ P.edge i (q i.castSucc) a (q i.succ))

noncomputable def accepted (P : Program b k σ) : Finset ℕ :=
  (paths P).biUnion (fun q ↦ box (pathDigits P q))

/-- The definition is ordinary digit recognition via a state at each
boundary. No consistency of programs at different lengths is imposed. -/
theorem mem_accepted_encode (hb : 1<b) (P : Program b k σ) (x : Fin k → Fin b) :
    encode x∈accepted P ↔ ∃ q : Fin (k+1) → σ,
      q 0=P.initial ∧ q (Fin.last k)∈P.accepting ∧
        ∀ i, P.edge i (q i.castSucc) (x i) (q i.succ) := by
  simp only [accepted,Finset.mem_biUnion,paths,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨q,⟨hq0,hq1⟩,hq⟩
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hq
    have hyx : y=x := encode_injective hb he
    subst y
    refine ⟨q,hq0,hq1,fun i ↦ ?_⟩
    exact (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hy i)).2
  · rintro ⟨q,hq0,hq1,hq⟩
    refine ⟨q,⟨hq0,hq1⟩,mem_box _ _ ?_⟩
    intro i
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq i⟩

lemma accepted_lt (hb : 1<b) (P : Program b k σ) {n : ℕ} (hn : n∈accepted P) : n<b^k := by
  obtain ⟨q,hq,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hn
  exact encode_lt hb x

/-- Every boundary-state path contributes one Cartesian digit box. Under
a representation cap M, each box has at most M^b points. -/
theorem accepted_card_le (hb : 1<b) (P : Program b k σ) (A : Set ℕ)
    (hA : (accepted P : Set ℕ)⊆A) (M : ℕ)
    (hM : ∀ n<2*b^k, sumRep A n≤M) :
    (accepted P).card≤(Fintype.card σ)^(k+1)*M^b := by
  have hbox (q : Fin (k+1) → σ) (hq : q∈paths P) :
      (box (pathDigits P q)).card≤M^b := by
    apply box_card_le_cap_power hb A _ _ M hM
    intro n hn
    exact hA (Finset.mem_biUnion.mpr ⟨q,hq,hn⟩)
  have hpaths : (paths P).card≤(Fintype.card σ)^(k+1) := by
    simpa using Finset.card_le_univ (paths P)
  calc
    _ ≤ ∑ q∈paths P, (box (pathDigits P q)).card := Finset.card_biUnion_le
    _ ≤ ∑ _q∈paths P, M^b := Finset.sum_le_sum hbox
    _ = (paths P).card*M^b := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hpaths

/-- A finite-set version, useful when the program is only a description
of a subset of one candidate prefix. -/
theorem accepted_card_le_of_finite_cap (hb : 1<b) (P : Program b k σ) (M : ℕ)
    (hM : ∀ n<2*b^k, sumRep (accepted P : Set ℕ) n≤M) :
    (accepted P).card≤(Fintype.card σ)^(k+1)*M^b :=
  accepted_card_le hb P (accepted P) Set.Subset.rfl M hM

end Erdos66LayeredDigitProgram
