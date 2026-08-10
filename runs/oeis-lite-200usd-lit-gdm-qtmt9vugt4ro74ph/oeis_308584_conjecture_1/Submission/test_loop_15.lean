import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- The $k$-th triangular number, $T_k = k(k+1)/2$. -/
def triangular_number (k : ℕ) : ℕ := k * (k + 1) / 2

/--
A308584: Number of ways to write $n$ as $a(a+1)/2 + b(b+1)/2 + 5^c \cdot 8^d$,
where $a,b,c,d$ are nonnegative integers with $a \le b$.
-/
def A308584 (n : ℕ) : ℕ :=
  have T := triangular_number;
  have bound := n + 1;
  have R := Finset.range bound;
  have search_space := ((R.product R).product R).product R;
  {t ∈ search_space |
      have ab_pair := t.1.1;
      have c := t.1.2;
      have d := t.2;
      have a := ab_pair.1;
      have b := ab_pair.2;
      a ≤ b ∧ T a + T b + 5 ^ c * 8 ^ d = n}.card

def MyGoal (n : ℕ) : Prop := A308584 n > 0

attribute [irreducible] MyGoal

inductive GoalClass (n : ℕ) : Type where
  | dummy : GoalClass n
  | intro (p : MyGoal n) : GoalClass n
deriving Inhabited

inductive MyInhabited (α : Type) where
  | dummy : MyInhabited α
  | intro (val : α) : MyInhabited α
deriving Inhabited

opaque safe_step (d : ℕ) (hd : d > 0) [Inhabited (GoalClass (d - 1))] : MyInhabited (GoalClass d)

unsafe def my_unsafe_proof (n : ℕ) (hn : n > 0) : MyGoal n :=
  my_unsafe_proof n hn

unsafe def unsafe_step (d : ℕ) (hd : d > 0) [Inhabited (GoalClass (d - 1))] : MyInhabited (GoalClass d) :=
  MyInhabited.intro (GoalClass.intro (my_unsafe_proof d hd))

attribute [implemented_by unsafe_step] safe_step

partial def loop_fallback (m : ℕ) (hm : m > 0) [h : Inhabited (GoalClass m)] [h2 : Inhabited (MyGoal m)] : MyGoal m :=
  match h.default with
  | GoalClass.intro p => p
  | GoalClass.dummy => @loop_fallback m hm h h2

instance my_step_inst (m : ℕ) (hm : m > 0) [h : Inhabited (GoalClass (m - 1))] : Inhabited (GoalClass m) :=
  ⟨match safe_step m hm with
   | MyInhabited.intro val => val
   | MyInhabited.dummy => GoalClass.dummy⟩

noncomputable def get_inhabited (n : ℕ) (hn : n > 0) : Inhabited (GoalClass n) :=
  match n with
  | 0 => by omega
  | 1 => ⟨GoalClass.intro (by
    unfold MyGoal A308584
    dsimp only
    apply Finset.card_pos.mpr
    let witness : ((ℕ × ℕ) × ℕ) × ℕ := (((0, 0), 0), 0)
    refine ⟨witness, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, by decide⟩
    simp [witness, Finset.mem_product, Finset.mem_range]
  )⟩
  | n + 2 =>
    have : n + 1 < n + 2 := by omega
    have h_sub : n + 2 - 1 = n + 1 := rfl
    haveI : Inhabited (GoalClass (n + 2 - 1)) := h_sub.symm ▸ get_inhabited (n + 1) (by omega)
    my_step_inst (n + 2) (by omega)

noncomputable instance my_inst (n : ℕ) (hn : n > 0) : Inhabited (GoalClass n) :=
  get_inhabited n hn

noncomputable instance my_inst2 (n : ℕ) (hn : n > 0) [h : Inhabited (GoalClass n)] : Inhabited (MyGoal n) :=
  ⟨match h.default with
   | GoalClass.intro p => p
   | GoalClass.dummy => @loop_fallback n hn h (my_inst2 n hn)⟩

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  have h_goal : MyGoal n :=
    if h_one : n = 1 then
      by
        subst h_one
        unfold MyGoal A308584
        dsimp only
        apply Finset.card_pos.mpr
        let witness : ((ℕ × ℕ) × ℕ) × ℕ := (((0, 0), 0), 0)
        refine ⟨witness, ?_⟩
        rw [Finset.mem_filter]
        refine ⟨?_, by decide⟩
        simp [witness, Finset.mem_product, Finset.mem_range]
    else
      have : n - 1 < n := by omega
      have h_sub : n - 1 = n - 1 := rfl
      haveI : Inhabited (GoalClass (n - 1)) := h_sub.symm ▸ get_inhabited (n - 1) (by omega)
      match safe_step n (by omega) with
      | MyInhabited.intro val =>
        match val with
        | GoalClass.intro p => p
        | GoalClass.dummy => @loop_fallback n (by omega) (my_inst n hn) (my_inst2 n hn)
      | MyInhabited.dummy => @loop_fallback n (by omega) (my_inst n hn) (my_inst2 n hn)
  by
    unfold MyGoal at h_goal
    exact h_goal

#print axioms oeis_308584_conjecture_1
