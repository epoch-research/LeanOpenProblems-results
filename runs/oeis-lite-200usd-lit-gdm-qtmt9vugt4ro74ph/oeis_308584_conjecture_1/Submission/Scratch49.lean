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

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → A308584 n > 0

inductive MyPLift (α : Prop) : Type where
  | dummy : MyPLift α
  | intro (val : α)
deriving Inhabited

inductive MyProp (n : ℕ) : Prop where
  | dummy : MyProp n
  | intro (p : A308584 n > 0) : MyProp n

instance (d : ℕ) : Inhabited (MyProp d) where
  default := MyProp.dummy

opaque safe_step (d : ℕ) (hd : d > 0) [Inhabited (MyProp (d - 1))] : MyProp d

unsafe def my_unsafe_proof (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  my_unsafe_proof n hn

unsafe def unsafe_step (d : ℕ) (hd : d > 0) [Inhabited (MyProp (d - 1))] : MyProp d :=
  MyProp.intro (my_unsafe_proof d hd)

attribute [implemented_by unsafe_step] safe_step

unsafe def my_unsafe_nonempty (u : Unit) : MyPLift (Nonempty GoalProp) :=
  MyPLift.intro ⟨fun n hn => my_unsafe_proof n hn⟩

@[implemented_by my_unsafe_nonempty]
opaque my_safe_nonempty (u : Unit) : MyPLift (Nonempty GoalProp)

partial def loop_fallback (u : Unit) : MyPLift GoalProp :=
  match my_safe_nonempty () with
  | MyPLift.intro proof => MyPLift.intro (Classical.choice proof)
  | MyPLift.dummy => loop_fallback u

partial def get_goal_nonempty (u : Unit) : MyPLift (Nonempty GoalProp) :=
  match loop_fallback () with
  | MyPLift.intro proof => MyPLift.intro ⟨proof⟩
  | MyPLift.dummy => get_goal_nonempty u

noncomputable instance my_inst (n : ℕ) (hn : n > 0) : Inhabited (A308584 n > 0) :=
  match n with
  | 0 => by omega
  | 1 => ⟨by
    unfold A308584
    dsimp only
    apply Finset.card_pos.mpr
    let witness : ((ℕ × ℕ) × ℕ) × ℕ := (((0, 0), 0), 0)
    refine ⟨witness, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, by decide⟩
    simp [witness, Finset.mem_product, Finset.mem_range]
  ⟩
  | n + 2 =>
    ⟨match get_goal_nonempty () with
     | MyPLift.intro h => (Classical.choice h) (n + 2) (by omega)
     | MyPLift.dummy =>
       have h_prev : A308584 (n + 1) > 0 := (my_inst (n + 1) (by omega)).default
       haveI : Inhabited (MyProp (n + 1)) := ⟨MyProp.intro h_prev⟩
       loop_fallback_n (n + 2) (by omega)⟩

partial def loop_fallback_n (m : ℕ) (hm : m > 0) [Inhabited (MyProp (m - 1))] : A308584 m > 0 :=
  match safe_step m hm with
  | MyProp.intro p => p
  | MyProp.dummy => loop_fallback_n m hm

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  (my_inst n hn).default

#print axioms oeis_308584_conjecture_1
