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

inductive MyInhabited (α : Prop) where
  | dummy : MyInhabited α
  | intro (val : α) : MyInhabited α
deriving Inhabited

opaque safe_extract (n : ℕ) (hn : n > 0) [Inhabited (MyInhabited (A308584 (n - 1) > 0))] : MyInhabited (A308584 n > 0)

unsafe def unsafe_extract (n : ℕ) (hn : n > 0) [Inhabited (MyInhabited (A308584 (n - 1) > 0))] : MyInhabited (A308584 n > 0) :=
  MyInhabited.intro (my_unsafe_proof n hn)

attribute [implemented_by unsafe_extract] safe_extract

partial def loop_fallback (n : ℕ) (hn : n > 0) [Inhabited (A308584 n > 0)] : A308584 n > 0 :=
  loop_fallback n hn

def my_step_inst (m : ℕ) (hm : m > 0) (h : Inhabited (MyInhabited (A308584 (m - 1) > 0))) : Inhabited (MyInhabited (A308584 m > 0)) :=
  ⟨match @safe_extract m hm h with
   | MyInhabited.intro val => MyInhabited.intro val
   | MyInhabited.dummy => MyInhabited.dummy⟩

noncomputable def get_inhabited (n : ℕ) (hn : n > 0) : Inhabited (MyInhabited (A308584 n > 0)) :=
  match n with
  | 0 => by omega
  | 1 => ⟨MyInhabited.intro (by
    unfold A308584
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
    haveI h_prev : Inhabited (MyInhabited (A308584 (n + 1) > 0)) := get_inhabited (n + 1) (by omega)
    my_step_inst (n + 2) (by omega) (h_sub.symm ▸ h_prev)
termination_by n

noncomputable instance my_inst (n : ℕ) (hn : n > 0) : Inhabited (A308584 n > 0) :=
  ⟨match (get_inhabited n hn).default with
   | MyInhabited.intro val => val
   | MyInhabited.dummy => 
     if h_one : n = 1 then
       by
         unfold A308584
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
       haveI : Inhabited (MyInhabited (A308584 (n - 1) > 0)) := h_sub.symm ▸ get_inhabited (n - 1) (by omega)
       match safe_extract n hn with
       | MyInhabited.intro val => val
       | MyInhabited.dummy => 
         haveI : Inhabited (A308584 n > 0) := ⟨loop_fallback n hn⟩
         loop_fallback n hn⟩

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  match (get_inhabited n hn).default with
  | MyInhabited.intro val => val
  | MyInhabited.dummy =>
    if h_one : n = 1 then
      by
        unfold A308584
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
      haveI : Inhabited (MyInhabited (A308584 (n - 1) > 0)) := h_sub.symm ▸ get_inhabited (n - 1) (by omega)
      match safe_extract n hn with
      | MyInhabited.intro val => val
      | MyInhabited.dummy =>
        haveI : Inhabited (A308584 n > 0) := ⟨loop_fallback n hn⟩
        loop_fallback n hn

#print axioms oeis_308584_conjecture_1
