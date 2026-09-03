import FormalConjecturesUtil

/-! A least closed set for the two-tail-position deletion game.  These are
abstract combinatorial statements; they do not exclude all odd covers. -/
namespace Erdos7AdaptiveTailClosure
set_option autoImplicit false
set_option linter.style.existsImplication false
set_option maxHeartbeats 1000000

variable {U R : Type*} (M : U → R → Prop) (A : U → R → R → U → Prop)

/-- A low choice is forbidden either by a middle/lower pair, or by an upper
class whose middle companion belongs to the set of late-deletion branches. -/
def Blocked (B : Set U) (u : U) (v : R) : Prop :=
  M u v ∨ ∃ r w, w ∈ B ∧ A u v r w

/-- Every branch with all its early choices blocked must be treated late. -/
def Closed (B : Set U) : Prop := ∀ u, (∀ v, Blocked M A B u v) → u ∈ B

/-- The least set closed under the forcing rule. -/
def Frozen : Set U := {u | ∀ B : Set U, Closed M A B → u ∈ B}

/-- A late branch with a full upper node whose companions are all late. -/
def Terminal (B : Set U) : Prop := ∃ u ∈ B, ∃ v, ∀ r, ∃ w ∈ B, A u v r w

lemma blocked_mono {B C : Set U} (h : B ⊆ C) {u : U} {v : R} :
    Blocked M A B u v → Blocked M A C u v := by
  rintro (hm | ⟨r,w,hw,ha⟩)
  · exact Or.inl hm
  · exact Or.inr ⟨r,w,h hw,ha⟩

lemma frozen_le {B : Set U} (hB : Closed M A B) : Frozen M A ⊆ B := by
  intro u hu
  exact hu B hB

lemma frozen_closed : Closed M A (Frozen M A) := by
  intro u hu B hB
  apply hB u
  intro v
  exact blocked_mono M A (frozen_le M A hB) (hu v)

lemma terminal_mono {B C : Set U} (h : B ⊆ C) :
    Terminal A B → Terminal A C := by
  rintro ⟨u,hu,v,hv⟩
  refine ⟨u,h hu,v,fun r => ?_⟩
  obtain ⟨w,hw,ha⟩ := hv r
  exact ⟨w,h hw,ha⟩

/-- It suffices to test the least closed set: adding late branches cannot
remove a terminal obstruction already present there. -/
theorem terminal_frozen_iff : Terminal A (Frozen M A) ↔
    ¬ ∃ B : Set U, Closed M A B ∧ ¬ Terminal A B := by
  constructor
  · rintro ht ⟨B,hB,hn⟩
    exact hn (terminal_mono A (frozen_le M A hB) ht)
  · intro h
    by_contra ht
    exact h ⟨Frozen M A,frozen_closed M A,ht⟩

/-- Every branch outside a closed set has an admissible early value. -/
theorem choices_outside_closed [Nonempty R] (B : Set U) (hB : Closed M A B) :
    ∃ low : U → R, ∀ u, u ∉ B → ¬ Blocked M A B u (low u) := by
  classical
  have hlo (u : U) : ∃ v : R, u ∉ B → ¬ Blocked M A B u v := by
    by_cases hu : u ∈ B
    · exact ⟨Classical.arbitrary R,fun hn => (hn hu).elim⟩
    · have hn : ¬ ∀ v, Blocked M A B u v := fun ha => hu (hB u ha)
      push_neg at hn
      obtain ⟨v,hv⟩ := hn
      exact ⟨v,fun _ => hv⟩
  choose low hlow using hlo
  exact ⟨low,hlow⟩

/-- Explicit choices for every early and late branch, extracted without any
independence assumption on the marked pairs. -/
theorem policy_of_not_terminal [Nonempty R]
    (h : ¬ Terminal A (Frozen M A)) :
    ∃ low : U → R, ∃ high : U → R → R,
      (∀ u, u ∉ Frozen M A → ¬ Blocked M A (Frozen M A) u (low u)) ∧
      (∀ u, u ∈ Frozen M A → ∀ v w, w ∈ Frozen M A →
        ¬ A u v (high u v) w) := by
  classical
  have hlo (u : U) : ∃ v : R, u ∉ Frozen M A →
      ¬ Blocked M A (Frozen M A) u v := by
    by_cases hu : u ∈ Frozen M A
    · exact ⟨Classical.arbitrary R,fun hn => (hn hu).elim⟩
    · have hn : ¬ ∀ v, Blocked M A (Frozen M A) u v :=
        fun ha => hu (frozen_closed M A u ha)
      push_neg at hn
      obtain ⟨v,hv⟩ := hn
      exact ⟨v,fun _ => hv⟩
  have hhi (u : U) (v : R) : ∃ r : R, u ∈ Frozen M A →
      ∀ w, w ∈ Frozen M A → ¬ A u v r w := by
    by_cases hu : u ∈ Frozen M A
    · have hn : ¬ ∀ r, ∃ w ∈ Frozen M A, A u v r w :=
        fun ha => h ⟨u,hu,v,ha⟩
      push_neg at hn
      obtain ⟨r,hr⟩ := hn
      exact ⟨r,fun _ => hr⟩
    · exact ⟨Classical.arbitrary R,fun hh => (hu hh).elim⟩
  choose low hlow using hlo
  choose high hhigh using hhi
  exact ⟨low,high,hlow,fun u hu v w hw => hhigh u v hu w hw⟩

section Finite
variable [Fintype U] [Fintype R] [DecidableEq U]

/-- Iterative closure, starting with no late branches. -/
noncomputable def stage : ℕ → Finset U
  | 0 => ∅
  | n+1 => by
      classical
      exact stage n ∪ Finset.univ.filter (fun u => ∀ v,
        Blocked M A (stage n : Set U) u v)

lemma stage_le_succ (n : ℕ) : stage M A n ⊆ stage M A (n+1) := by
  classical
  exact Finset.subset_union_left

lemma stage_le_frozen (n : ℕ) : (stage M A n : Set U) ⊆ Frozen M A := by
  classical
  induction n with
  | zero => simp [stage]
  | succ n ih =>
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact ih hu
    · apply frozen_closed M A u
      intro v
      exact blocked_mono M A ih ((Finset.mem_filter.mp hu).2 v)

lemma stage_closed_of_fixed (n : ℕ)
    (h : stage M A (n+1) = stage M A n) : Closed M A (stage M A n : Set U) := by
  classical
  intro u hu
  have hh : u ∈ stage M A (n+1) :=
    Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩)
  rwa [h] at hh

/-- Stabilization occurs after at most the number of branches many steps. -/
theorem exists_stable_stage : ∃ n ≤ Fintype.card U, stage M A (n+1) = stage M A n := by
  classical
  by_contra! hn
  have hcard : ∀ n ≤ Fintype.card U+1, n ≤ (stage M A n).card := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hbound
      have hprev := ih (by omega)
      have hlt : (stage M A n).card < (stage M A (n+1)).card := by
        apply Finset.card_lt_card
        apply Finset.ssubset_iff_subset_ne.mpr
        exact ⟨stage_le_succ M A n,fun h => hn n (by omega) h.symm⟩
      omega
  have hh := hcard (Fintype.card U+1) le_rfl
  have hb := Finset.card_le_univ (stage M A (Fintype.card U+1))
  omega

/-- The least closed set is exactly a finite iteration, not an extra limiting
or self-support assumption. -/
theorem exists_stage_eq_frozen : ∃ n ≤ Fintype.card U,
    (stage M A n : Set U) = Frozen M A := by
  classical
  obtain ⟨n,hn,hfix⟩ := exists_stable_stage M A
  exact ⟨n,hn,Set.Subset.antisymm (stage_le_frozen M A n)
    (frozen_le M A (stage_closed_of_fixed M A n hfix))⟩
end Finite

#print axioms frozen_closed
#print axioms terminal_frozen_iff
#print axioms policy_of_not_terminal
#print axioms exists_stage_eq_frozen
end Erdos7AdaptiveTailClosure
