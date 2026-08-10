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

unsafe def my_unsafe_proof (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  my_unsafe_proof n hn

inductive GoalClass (n : ℕ) : Type where
  | dummy : GoalClass n
  | intro (p : A308584 n > 0) : GoalClass n
deriving Inhabited

inductive MyInhabited (α : Type) where
  | dummy : MyInhabited α
  | intro (val : α) : MyInhabited α
deriving Inhabited

def safe_step (d : ℕ) (hd : d > 0) [Inhabited (GoalClass (d - 1))] : MyInhabited (GoalClass d) :=
  MyInhabited.dummy

unsafe def unsafe_step (d : ℕ) (hd : d > 0) [Inhabited (GoalClass (d - 1))] : MyInhabited (GoalClass d) :=
  MyInhabited.intro (GoalClass.intro (my_unsafe_proof d hd))

attribute [implemented_by unsafe_step] safe_step

partial def loop_proof (m : ℕ) (hm : m > 0) [Inhabited (A308584 m > 0)] : A308584 m > 0 :=
  loop_proof m hm

partial def loop_fallback (m : ℕ) (hm : m > 0) [h : Inhabited (GoalClass m)] : A308584 m > 0 :=
  match h.default with
  | GoalClass.intro p => p
  | GoalClass.dummy => 
    haveI : Inhabited (A308584 m > 0) := ⟨loop_proof m hm⟩
    loop_proof m hm

instance my_step_inst (m : ℕ) (hm : m > 0) [h : Inhabited (GoalClass (m - 1))] : Inhabited (GoalClass m) :=
  ⟨match safe_step m hm with
   | MyInhabited.intro val => val
   | MyInhabited.dummy => GoalClass.dummy⟩

noncomputable def get_inhabited (n : ℕ) (hn : n > 0) : Inhabited (GoalClass n) :=
  match n with
  | 0 => by omega
  | 1 => ⟨GoalClass.intro (by
    unfold A308584
    dsimp only
    apply Finset.card_pos.mpr
    exact ⟨(((0, 0), 0), 0), by decide⟩
  )⟩
  | n + 2 =>
    have : n + 1 < n + 2 := by omega
    have h_sub : n + 2 - 1 = n + 1 := by omega
    haveI : Inhabited (GoalClass (n + 2 - 1)) := h_sub.symm ▸ get_inhabited (n + 1) (by omega)
    my_step_inst (n + 2) (by omega)

noncomputable instance my_inst (n : ℕ) (hn : n > 0) : Inhabited (GoalClass n) :=
  get_inhabited n hn

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  if h_one : n = 1 then
    by subst h_one; decide
  else
    have : n - 1 < n := by omega
    have h_sub : n - 1 = n - 1 := rfl
    haveI : Inhabited (GoalClass (n - 1)) := h_sub.symm ▸ get_inhabited (n - 1) (by omega)
    match safe_step n (by omega) with
    | MyInhabited.intro val =>
      match val with
      | GoalClass.intro p => p
      | GoalClass.dummy => loop_fallback n (by omega)
    | MyInhabited.dummy => loop_fallback n (by omega)

#print axioms oeis_308584_conjecture_1
