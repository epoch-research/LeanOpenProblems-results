import Submission.AssignedPacketDegreeExplore
import Submission.IntervalPredecessorRepairExplore

/-! Localized packet repair for a two-sided nearby assignment into the old set. -/
namespace Erdos66AssignedIntervalRepair
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66PredecessorCell
  Erdos66PredecessorPacketRepair Erdos66PredecessorCandidateDegree
  Erdos66ReflectionRoundingPatch Erdos66FiniteSwapAlgebra Erdos66Counting
  Erdos66IntervalPredecessorRepair Erdos66AssignedPacketRepair Erdos66AssignedPacketDegree
open scoped Classical
set_option maxHeartbeats 2800000

lemma nearby_assignment_fiber {α : Type*} [Fintype α]
    (assign : ℕ → ℕ) (f : α → ℕ) (hf : Function.Injective f) (H : ℕ)
    (hgap : ∀ a, f a<assign (f a)+H ∧ assign (f a)<f a+H) (r : ℕ) :
    (Finset.univ.filter (fun a ↦ assign (f a)=r)).card ≤ 2*H := by
  have hc : (Finset.univ.filter (fun a ↦ assign (f a)=r)).card ≤
      (Finset.Ico (r-H) (r+H)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro a ha
      have he := (Finset.mem_filter.mp ha).2
      have hh := hgap a
      rw [he] at hh
      exact Finset.mem_Ico.mpr ⟨by omega,hh.1⟩
    · exact hf.injOn
  rw [Nat.card_Ico] at hc
  omega

lemma assigned_endpoints_separated {α : Type*} (assign : ℕ → ℕ)
    (n : ℕ) (x : α → ℕ) (H : ℕ)
    (hm : ∀ a, 2*x a+2*H ≤ n)
    (hgap : ∀ b a, endpoint n x b a<assign (endpoint n x b a)+H ∧
      assign (endpoint n x b a)<endpoint n x b a+H) :
    ∀ a, Function.Injective (fun b ↦ assign (endpoint n x b a)) := by
  intro a b c he
  have hl := hgap false a
  have hr := hgap true a
  have hh := hm a
  cases b <;> cases c
  all_goals first | rfl | (simp only [endpoint,Bool.false_eq_true,if_false,if_true] at he hl hr; omega)

theorem exists_assigned_interval_repair (A : Finset ℕ) (assign : ℕ → ℕ) (V : ℝ)
    (hA : ∀ z, (sumRep (A : Set ℕ) z : ℝ) ≤ V)
    (n L W H : ℕ) (hW : 0<W) (hmargin : 2*(L+W)+2*H ≤ n)
    (hmem : ∀ b (i : Fin W), assign (endpoint n (fun i : Fin W ↦ L+i.val) b i) ∈ A)
    (hgap : ∀ b (i : Fin W),
      endpoint n (fun i : Fin W ↦ L+i.val) b i<assign (endpoint n (fun i : Fin W ↦ L+i.val) b i)+H ∧
      assign (endpoint n (fun i : Fin W ↦ L+i.val) b i)<endpoint n (fun i : Fin W ↦ L+i.val) b i+H)
    (m : ℕ) (T : Finset ℕ) (R t : ℝ) (ht : 0<t)
    (hsmall : ((m : ℝ)^4+8*m^2*H+m*(2*Real.sqrt (2*W*V)+4*H*V))/W+
      T.card*Real.exp ((m : ℝ)*Real.exp t*(2*Real.sqrt (2*W*V)+4*H*V)/W-t*R)<1) :
    ∃ D F : Finset ℕ, D ⊆ A ∧ Disjoint A F ∧ D.card=2*m ∧ F.card=2*m ∧
      sumRep (swapped A D F : Set ℕ) n=sumRep (A : Set ℕ) n+2*m ∧
      (∀ z, z≠n → sumRep (F : Set ℕ) z ≤ 6) ∧
      D=F.image assign ∧ Set.InjOn assign (F : Set ℕ) ∧
      (∀ u ∈ D∪F, L ≤ u+H ∧ u ≤ n-L+H) ∧
      ∀ z ∈ T, z≠n → |(sumRep (swapped A D F : Set ℕ) z : ℝ)-sumRep (A : Set ℕ) z|<4*R+6 := by
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
  have hhalf : ∀ i, 2*x i<n := by
    intro i
    have hi := i.isLt
    dsimp only [x]
    omega
  have hm : ∀ i, 2*x i+2*H ≤ n := by
    intro i
    have hi := i.isLt
    dsimp only [x]
    omega
  have hinj b := endpoint_injective n x hx hn b
  have hwindow : ∀ b i, start b ≤ endpoint n x b i ∧ endpoint n x b i<start b+W := by
    intro b i
    have hi := i.isLt
    cases b <;> simp [start,endpoint,x] <;> omega
  have hfiber b r := nearby_assignment_fiber assign (endpoint n x b) (hinj b) H (hgap b) r
  have hlocal := natural_window_bound A V hA
  have hdeg := assigned_candidate_degrees A assign n x (2*H) W start (Real.sqrt (2*W*V))
    hinj hwindow (fun a ↦ hlocal a W) hmem hfiber
  have hdegree (z : ℕ) : 2*Real.sqrt (2*W*V)+2*(2*H : ℕ)*sumRep (A : Set ℕ) z ≤
      2*Real.sqrt (2*W*V)+4*H*V := by
    have hh := mul_le_mul_of_nonneg_left (hA z) (show (0 : ℝ) ≤ 4*H by positivity)
    push_cast
    linarith
  have hsmall' : ((m : ℝ)^4+4*m^2*(2*H : ℕ)+m*(2*Real.sqrt (2*W*V)+4*H*V))/Fintype.card (Fin W)+
      T.card*Real.exp ((m : ℝ)*Real.exp t*(2*Real.sqrt (2*W*V)+4*H*V)/Fintype.card (Fin W)-t*R)<1 := by
    have he : 4*(m : ℝ)^2*((2*H : ℕ) : ℝ)=8*(m : ℝ)^2*H := by push_cast; ring
    rw [Fintype.card_fin,he]
    exact hsmall
  obtain ⟨D,F,hD,hF,hDc,hFc,htarget,hself,hshape,hinjF,hpoints,hcol⟩ :=
    exists_assigned_packet_repair A assign n x hx hhalf hmem (2*H) hfiber
      (assigned_endpoints_separated assign n x H hm hgap) m T
      (2*Real.sqrt (2*W*V)+4*H*V) (2*Real.sqrt (2*W*V)+4*H*V) R t
      (hdeg.1.trans (hdegree n)) (fun z _ ↦ (hdeg.2 z).trans (hdegree z)) ht hsmall'
  refine ⟨D,F,hD,hF,hDc,hFc,htarget,hself,hshape,hinjF,?_,hcol⟩
  have hp (u : ℕ) (hu : u∈F) : L ≤ u ∧ u ≤ n-L := by
    obtain ⟨b,i,rfl⟩ := hpoints u hu
    have hi := i.isLt
    cases b <;> simp only [endpoint,Bool.false_eq_true,if_false,if_true,x] <;> omega
  intro u hu
  rcases Finset.mem_union.mp hu with hu | hu
  · rw [hshape] at hu
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    have hpv := hp v hv
    obtain ⟨b,i,rfl⟩ := hpoints v hv
    have hh := hgap b i
    dsimp only [x] at hpv ⊢
    constructor <;> omega
  · have hh := hp u hu
    constructor <;> omega

end Erdos66AssignedIntervalRepair
