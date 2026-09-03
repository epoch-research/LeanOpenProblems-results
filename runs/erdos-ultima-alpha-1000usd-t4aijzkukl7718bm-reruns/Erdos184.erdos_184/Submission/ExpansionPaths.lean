import Submission.SqrtDeficitSeparator

/-! Elementary short paths from uniform expansion above a set-size threshold. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.ExpansionPaths
open SqrtDeficitSeparator (externalBoundary)
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V]

/-- Closed neighborhoods iterated from a set. No connectedness is presupposed. -/
def ball (H : SimpleGraph V) (A : Set V) : ℕ → Set V
  | 0 => A
  | k+1 => ball H A k ∪ externalBoundary H (ball H A k)

omit [Fintype V] in
lemma ball_step (H : SimpleGraph V) (A : Set V) (k : ℕ) :
    ball H A k ⊆ ball H A (k+1) := Set.subset_union_left

lemma ball_mono (H : SimpleGraph V) (A : Set V) : Monotone (ball H A) :=
  monotone_nat_of_le_succ (ball_step H A)

lemma subset_ball (H : SimpleGraph V) (A : Set V) (k : ℕ) : A ⊆ ball H A k :=
  ball_mono H A (Nat.zero_le k)

lemma ball_card_mono (H : SimpleGraph V) (A : Set V) :
    Monotone (fun k => (ball H A k).ncard) :=
  fun _ _ h => Set.ncard_le_ncard (ball_mono H A h)

lemma ball_card_succ (H : SimpleGraph V) (A : Set V) (k : ℕ) :
    (ball H A (k+1)).ncard = (ball H A k).ncard +
      (externalBoundary H (ball H A k)).ncard := by
  have hd : Disjoint (ball H A k) (externalBoundary H (ball H A k)) := by
    apply Set.disjoint_left.mpr
    intro x hx hb
    exact hb.1 hx
  exact Set.ncard_union_eq hd

omit [Fintype V] in
lemma walk_of_mem_ball (H : SimpleGraph V) (A : Set V) {k : ℕ} {x : V}
    (hx : x ∈ ball H A k) : ∃ a ∈ A, ∃ p : H.Walk a x, p.length ≤ k := by
  induction k generalizing x with
  | zero => exact ⟨x,hx,Walk.nil,Nat.zero_le _⟩
  | succ k ih =>
    rcases hx with hx | hx
    · obtain ⟨a,ha,p,hp⟩ := ih hx
      exact ⟨a,ha,p,hp.trans (Nat.le_succ _)⟩
    · obtain ⟨y,hy,hyx⟩ := hx.2
      obtain ⟨a,ha,p,hp⟩ := ih hy
      refine ⟨a,ha,p.append hyx.toWalk,?_⟩
      simpa using Nat.add_le_add_right hp 1

/-- An R-step block doubles a monotone sequence if every step expands at
relative rate at least 1/R. The statement uses only natural arithmetic. -/
lemma doubling_block {b : ℕ → ℕ} (hb : Monotone b) {R q : ℕ} (hR : 0 < R)
    (hstep : ∀ i < R, b (q+i) + R*b (q+i) ≤ R*b (q+i+1)) :
    2*b q ≤ b (q+R) := by
  have h (j : ℕ) (hj : j ≤ R) : (R+j)*b q ≤ R*b (q+j) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hi := ih (by omega)
      have hs := hstep j (by omega)
      have hm := hb (show q ≤ q+j by omega)
      simp only [Nat.add_assoc] at hs
      nlinarith
  have hh := h R le_rfl
  nlinarith

/-- A uniformly expanding monotone sequence must exceed half the ambient
order after O(R log n) steps, starting from any positive value. -/
lemma half_lt_of_growth {b : ℕ → ℕ} (hb : Monotone b) {R n : ℕ}
    (hR : 0 < R) (hb0 : 0 < b 0)
    (hstep : ∀ i, 2*b i ≤ n → b i + R*b i ≤ R*b (i+1)) :
    n < 2*b (R*(Nat.log 2 n + 1)) := by
  by_contra! hsmall
  let k := Nat.log 2 n + 1
  have hblocks (j : ℕ) (hj : j ≤ k) : 2^j * b 0 ≤ b (R*j) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hjk : j ≤ k := by omega
      have hi := ih hjk
      have hd := doubling_block hb hR (q := R*j) (fun i hiR => by
        have hindex : R*j+i ≤ R*k := by nlinarith
        have hm := hb hindex
        apply hstep
        change 2*b (R*k) ≤ n at hsmall
        omega)
      have hidx : R*j+R = R*(j+1) := by ring
      rw [hidx] at hd
      simp only [pow_succ]
      nlinarith
  have hlast := hblocks k le_rfl
  have hp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  change n < 2^(Nat.log 2 n + 1) at hp
  change n < 2^k at hp
  change 2*b (R*k) ≤ n at hsmall
  nlinarith

/-- Expansion is only needed for sets at least as large as a specified
threshold; smaller balls never enter the proof. -/
def ExpandsAbove (H : SimpleGraph V) (a R : ℕ) : Prop :=
  ∀ X : Set V, a ≤ X.ncard → 0 < X.ncard → 2*X.ncard ≤ Fintype.card V →
    X.ncard ≤ R*(externalBoundary H X).ncard

lemma ball_large (H : SimpleGraph V) {a R : ℕ} (hR : 0 < R)
    (hexp : ExpandsAbove H a R) (A : Set V) (hA : 0 < A.ncard) (haA : a ≤ A.ncard) :
    Fintype.card V < 2*(ball H A (R*(Nat.log 2 (Fintype.card V)+1))).ncard := by
  apply half_lt_of_growth (ball_card_mono H A) hR hA
  intro i hi
  have hlo := Set.ncard_le_ncard (subset_ball H A i)
  have he := hexp (ball H A i) (haA.trans hlo) (hA.trans_le hlo) hi
  rw [ball_card_succ]
  nlinarith

/-- Two sets of size at least the expansion threshold can be joined by a
simple path of length at most 2R(log_2 n+1). -/
theorem short_path_between_sets (H : SimpleGraph V) {a R : ℕ} (hR : 0 < R)
    (hexp : ExpandsAbove H a R) (A B : Set V)
    (hA : 0 < A.ncard) (haA : a ≤ A.ncard)
    (hB : 0 < B.ncard) (haB : a ≤ B.ncard) :
    ∃ u ∈ A, ∃ v ∈ B, ∃ p : H.Walk u v,
      p.IsPath ∧ p.length ≤ 2*R*(Nat.log 2 (Fintype.card V)+1) := by
  let r := R*(Nat.log 2 (Fintype.card V)+1)
  have hLA := ball_large H hR hexp A hA haA
  have hLB := ball_large H hR hexp B hB haB
  have hi : (ball H A r ∩ ball H B r).Nonempty := by
    have hsum := Set.ncard_union_add_ncard_inter (ball H A r) (ball H B r)
    have hun : (ball H A r ∪ ball H B r).ncard ≤ Fintype.card V := by
      simpa only [Set.ncard_univ,Nat.card_eq_fintype_card] using
        Set.ncard_le_ncard (Set.subset_univ (ball H A r ∪ ball H B r))
    apply (Set.ncard_pos (Set.toFinite _)).mp
    change Fintype.card V < 2*(ball H A r).ncard at hLA
    change Fintype.card V < 2*(ball H B r).ncard at hLB
    omega
  obtain ⟨x,hxA,hxB⟩ := hi
  obtain ⟨u,hu,p,hp⟩ := walk_of_mem_ball H A hxA
  obtain ⟨v,hv,q,hq⟩ := walk_of_mem_ball H B hxB
  let w := p.append q.reverse
  refine ⟨u,hu,v,hv,w.bypass,w.bypass_isPath,?_⟩
  have hw := w.length_bypass_le
  have hl : w.length ≤ 2*r := by
    dsimp only [w]
    rw [Walk.length_append,Walk.length_reverse]
    omega
  apply hw.trans
  dsimp only [r] at hl
  nlinarith

end Erdos184.ExpansionPaths
