import Submission.StoppingDigitRestriction

/-! A finite-prefix closure criterion for predictable digit deletion. The
blocking relation is abstract and must be supplied by an arithmetic family. -/
namespace Erdos7StoppingPrefixClosure
open Erdos7StoppingDigitRestriction
set_option autoImplicit false
set_option maxHeartbeats 2000000

abbrev Node (E : ℕ) (R : Type*) := (t : Fin E) × (Fin t.val → R)

def node {E : ℕ} {R : Type*} (x : Fin E → R) (t : Fin E) : Node E R :=
  ⟨t,fun j => x ⟨j.val,j.isLt.trans_le t.isLt.le⟩⟩

def root {E : ℕ} {R : Type*} (hE : 0 < E) : Node E R :=
  ⟨⟨0,hE⟩,fun j => j.elim0⟩

lemma node_zero {E : ℕ} {R : Type*} (hE : 0 < E) (x : Fin E → R) :
    node x ⟨0,hE⟩ = root hE := by
  apply congrArg (fun u : Fin 0 → R => (⟨⟨0,hE⟩,u⟩ : Node E R))
  funext j
  exact j.elim0

lemma node_agree {E : ℕ} {R : Type*} (x y : Fin E → R) (t : Fin E)
    (h : Agree t.val x y) : node x t = node y t := by
  apply congrArg (fun u : Fin t.val → R => (⟨t,u⟩ : Node E R))
  funext j
  exact h _ j.isLt

section Closure
variable {E : ℕ} {R : Type*} (hE : 0 < E)
    (Block : Set (Node E R) → Node E R → R → Prop)

/-- Reached prefixes begin at the root. If every possible deletion value at
one reached prefix is blocked, all its next prefixes must also be reached. -/
def Closed (B : Set (Node E R)) : Prop :=
  root hE ∈ B ∧ ∀ x : Fin E → R, ∀ t : Fin E, ∀ ht : t.val+1 < E,
    node x t ∈ B → (∀ r, Block B (node x t) r) → node x ⟨t.val+1,ht⟩ ∈ B

def Frozen : Set (Node E R) := {u | ∀ B, Closed hE Block B → u ∈ B}

/-- At the last possible deletion position there is no continuation option. -/
def Terminal (B : Set (Node E R)) : Prop :=
  ∃ x : Fin E → R,
    node x ⟨E-1,by omega⟩ ∈ B ∧ ∀ r, Block B (node x ⟨E-1,by omega⟩) r

variable (hmono : ∀ {B C : Set (Node E R)}, B ⊆ C →
    ∀ {u r}, Block B u r → Block C u r)

lemma frozen_le {B : Set (Node E R)} (hB : Closed hE Block B) :
    Frozen hE Block ⊆ B := fun _ hu => hu B hB

include hmono in
lemma frozen_closed : Closed hE Block (Frozen hE Block) := by
  constructor
  · intro B hB
    exact hB.1
  · intro x t ht hx hr B hB
    exact hB.2 x t ht (hx B hB)
      (fun r => hmono (frozen_le hE Block hB) (hr r))

include hmono in
lemma terminal_mono {B C : Set (Node E R)} (hBC : B ⊆ C) :
    Terminal hE Block B → Terminal hE Block C := by
  rintro ⟨x,hx,hr⟩
  exact ⟨x,hBC hx,fun r => hmono hBC (hr r)⟩

include hmono in
theorem terminal_frozen_iff : Terminal hE Block (Frozen hE Block) ↔
    ¬ ∃ B, Closed hE Block B ∧ ¬ Terminal hE Block B := by
  constructor
  · rintro ht ⟨B,hB,hn⟩
    exact hn (terminal_mono hE Block hmono (frozen_le hE Block hB) ht)
  · intro hn
    by_contra ht
    exact hn ⟨Frozen hE Block,frozen_closed hE Block hmono,ht⟩

/-- A nonterminal closed prefix set gives an actual predictable stopping
position and value. All prefixes through the stopping node are reached. -/
theorem policy_of_closed [Nonempty R] (B : Set (Node E R))
    (hB : Closed hE Block B) (hn : ¬ Terminal hE Block B) :
    ∃ T : (Fin E → R) → Fin E, ∃ V : (Fin E → R) → R,
      Predictable T ∧ PredictableValue T V ∧
      (∀ x, ∀ t : Fin E, t.val ≤ (T x).val → node x t ∈ B) ∧
      ∀ x, ¬ Block B (node x (T x)) (V x) := by
  classical
  have hfree (x : Fin E → R) : ∃ t : Fin E, ∃ r, ¬ Block B (node x t) r := by
    by_contra! hnot
    have hreach : ∀ n, ∀ hn : n < E, node x ⟨n,hn⟩ ∈ B := by
      intro n
      induction n with
      | zero => intro hn; simpa only [node_zero] using hB.1
      | succ n ih =>
        intro hn
        exact hB.2 x ⟨n,by omega⟩ hn (ih (by omega)) (hnot _)
    exact hn ⟨x,hreach (E-1) (by omega),hnot _⟩
  let Q (x : Fin E → R) (n : ℕ) : Prop :=
    ∃ hn : n < E, ∃ r, ¬ Block B (node x ⟨n,hn⟩) r
  have hex (x : Fin E → R) : ∃ n, Q x n := by
    obtain ⟨t,r,hr⟩ := hfree x
    exact ⟨t.val,t.isLt,r,hr⟩
  let T (x : Fin E → R) : Fin E :=
    ⟨Nat.find (hex x),(Nat.find_spec (hex x)).choose⟩
  have hTfree (x : Fin E → R) : ∃ r, ¬ Block B (node x (T x)) r :=
    (Nat.find_spec (hex x)).choose_spec
  have hblocked (x : Fin E → R) (t : Fin E) (ht : t.val < (T x).val) :
      ∀ r, Block B (node x t) r := by
    intro r
    by_contra hr
    exact Nat.find_min (hex x) ht ⟨t.isLt,r,hr⟩
  have hpred : Predictable T := by
    intro x y hxy
    have hle : (T y).val ≤ (T x).val := by
      apply Nat.find_min' (hex y)
      refine ⟨(T x).isLt,?_⟩
      rw [← node_agree x y (T x) hxy]
      exact hTfree x
    have hge : (T x).val ≤ (T y).val := by
      by_contra! ht
      obtain ⟨r,hr⟩ := hTfree y
      have hh := hblocked x (T y) ht r
      rw [node_agree x y (T y) (hxy.mono ht.le)] at hh
      exact hr hh
    exact Fin.ext (Nat.le_antisymm hle hge)
  let pick (u : Node E R) : R :=
    if hh : ∃ r, ¬ Block B u r then hh.choose else Classical.arbitrary R
  have hpick (u : Node E R) (hu : ∃ r, ¬ Block B u r) : ¬ Block B u (pick u) := by
    dsimp only [pick]
    rw [dif_pos hu]
    exact hu.choose_spec
  let V (x : Fin E → R) := pick (node x (T x))
  refine ⟨T,V,hpred,?_,?_,fun x => hpick _ (hTfree x)⟩
  · intro x y hxy
    change pick (node y (T y)) = pick (node x (T x))
    rw [hpred x y hxy, node_agree x y (T x) hxy]
  · intro x t ht
    have hreach : ∀ n, ∀ hn : n < E, n ≤ (T x).val → node x ⟨n,hn⟩ ∈ B := by
      intro n
      induction n with
      | zero => intro hn hle; simpa only [node_zero] using hB.1
      | succ n ih =>
        intro hn hle
        exact hB.2 x ⟨n,by omega⟩ hn (ih (by omega) (by omega))
          (hblocked x ⟨n,by omega⟩ (show n < (T x).val from by omega))
    exact hreach t.val t.isLt ht

include hmono in
theorem policy_of_frozen_nonterminal [Nonempty R]
    (hn : ¬ Terminal hE Block (Frozen hE Block)) :
    ∃ T : (Fin E → R) → Fin E, ∃ V : (Fin E → R) → R,
      Predictable T ∧ PredictableValue T V ∧
      (∀ x, ∀ t : Fin E, t.val ≤ (T x).val → node x t ∈ Frozen hE Block) ∧
      ∀ x, ¬ Block (Frozen hE Block) (node x (T x)) (V x) :=
  policy_of_closed hE Block _ (frozen_closed hE Block hmono) hn
/-- A policy always exists if the last position is allowed as a fallback.
Every earlier stop uses a genuinely unblocked value. -/
theorem policy_with_terminal_fallback [Nonempty R] (B : Set (Node E R))
    (hB : Closed hE Block B) :
    ∃ T : (Fin E → R) → Fin E, ∃ V : (Fin E → R) → R,
      Predictable T ∧ PredictableValue T V ∧
      (∀ x, ∀ t : Fin E, t.val ≤ (T x).val → node x t ∈ B) ∧
      ∀ x, (T x).val+1 < E → ¬ Block B (node x (T x)) (V x) := by
  classical
  let Block' (C : Set (Node E R)) (u : Node E R) (r : R) :=
    u.1.val+1 < E ∧ Block C u r
  have hB' : Closed hE Block' B :=
    ⟨hB.1,fun x t ht hx hr => hB.2 x t ht hx (fun r => (hr r).2)⟩
  have hn' : ¬ Terminal hE Block' B := by
    rintro ⟨x,_,hr⟩
    have hh := (hr (Classical.arbitrary R)).1
    change E-1+1 < E at hh
    omega
  obtain ⟨T,V,hT,hV,hr,hfree⟩ := policy_of_closed hE Block' B hB' hn'
  exact ⟨T,V,hT,hV,hr,fun x hx hb => hfree x ⟨hx,hb⟩⟩

/-- The selected value at last-depth nodes can be varied without changing any
position or any earlier selected value. -/
lemma predictable_terminal_value {T : (Fin E → R) → Fin E}
    {V : (Fin E → R) → R} (hT : Predictable T) (hV : PredictableValue T V)
    (r : R) : PredictableValue T (fun x => if (T x).val = E-1 then r else V x) := by
  intro x y hxy
  dsimp only
  rw [hT x y hxy, hV x y hxy]

section Finite
variable [Fintype R] [DecidableEq R]

/-- The closure starts at the root, never at a self-supporting component. -/
noncomputable def stage : ℕ → Finset (Node E R)
  | 0 => {root hE}
  | n+1 => by
      classical
      exact stage n ∪ Finset.univ.filter (fun u =>
        ∃ x : Fin E → R, ∃ t : Fin E, ∃ ht : t.val+1 < E,
          node x t ∈ stage n ∧ (∀ r, Block (stage n : Set (Node E R)) (node x t) r) ∧
          u = node x ⟨t.val+1,ht⟩)

lemma stage_le_succ (n : ℕ) : stage hE Block n ⊆ stage hE Block (n+1) := by
  classical
  exact Finset.subset_union_left

lemma root_mem_stage (n : ℕ) : root hE ∈ stage hE Block n := by
  classical
  induction n with
  | zero => simp [stage]
  | succ n ih => exact stage_le_succ hE Block n ih

include hmono in
lemma stage_le_frozen (n : ℕ) :
    (stage hE Block n : Set (Node E R)) ⊆ Frozen hE Block := by
  classical
  induction n with
  | zero =>
    intro u hu
    have hu' : u = root hE := by simpa [stage] using hu
    rw [hu']
    exact (frozen_closed hE Block hmono).1
  | succ n ih =>
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact ih hu
    · obtain ⟨x,t,ht,hx,hr,rfl⟩ := (Finset.mem_filter.mp hu).2
      exact (frozen_closed hE Block hmono).2 x t ht (ih hx)
        (fun r => hmono ih (hr r))

lemma stage_closed_of_fixed (n : ℕ)
    (hh : stage hE Block (n+1) = stage hE Block n) :
    Closed hE Block (stage hE Block n : Set (Node E R)) := by
  classical
  refine ⟨root_mem_stage hE Block n,fun x t ht hx hr => ?_⟩
  have hmem : node x ⟨t.val+1,ht⟩ ∈ stage hE Block (n+1) :=
    Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,x,t,ht,hx,hr,rfl⟩)
  rwa [hh] at hmem

theorem exists_stable_stage : ∃ n ≤ Fintype.card (Node E R),
    stage hE Block (n+1) = stage hE Block n := by
  classical
  by_contra! hn
  have hcard : ∀ n ≤ Fintype.card (Node E R)+1, n ≤ (stage hE Block n).card := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hbound
      have hprev := ih (by omega)
      have hlt : (stage hE Block n).card < (stage hE Block (n+1)).card := by
        apply Finset.card_lt_card
        apply Finset.ssubset_iff_subset_ne.mpr
        exact ⟨stage_le_succ hE Block n,fun h => hn n (by omega) h.symm⟩
      omega
  have hh := hcard (Fintype.card (Node E R)+1) le_rfl
  have hb := Finset.card_le_univ (stage hE Block (Fintype.card (Node E R)+1))
  omega

include hmono in
theorem exists_stage_eq_frozen : ∃ n ≤ Fintype.card (Node E R),
    (stage hE Block n : Set (Node E R)) = Frozen hE Block := by
  classical
  obtain ⟨n,hn,hfix⟩ := exists_stable_stage hE Block
  exact ⟨n,hn,Set.Subset.antisymm (stage_le_frozen hE Block hmono n)
    (frozen_le hE Block (stage_closed_of_fixed hE Block n hfix))⟩
end Finite

end Closure

#print axioms policy_with_terminal_fallback
#print axioms predictable_terminal_value
#print axioms exists_stage_eq_frozen
#print axioms frozen_closed
#print axioms terminal_frozen_iff
#print axioms policy_of_closed
#print axioms policy_of_frozen_nonterminal
end Erdos7StoppingPrefixClosure
