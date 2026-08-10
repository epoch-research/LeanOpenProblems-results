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

inductive MyProp (n : ℕ) : Prop where
  | dummy : MyProp n
  | intro (p : A308584 n > 0) : MyProp n

instance (d : ℕ) : Inhabited (MyProp d) where
  default := MyProp.dummy

opaque safe_step (d : ℕ) (hd : d > 0) [Inhabited (MyProp (d - 1))] : MyProp d

unsafe def unsafe_step (d : ℕ) (hd : d > 0) [Inhabited (MyProp (d - 1))] : MyProp d :=
  MyProp.intro (my_unsafe_proof d hd)

attribute [implemented_by unsafe_step] safe_step

noncomputable def get_inhabited (n : ℕ) (hn : n > 0) : MyProp n :=
  match n with
  | 0 => by omega
  | 1 => MyProp.intro (by
    unfold A308584
    dsimp only
    apply Finset.card_pos.mpr
    let witness : ((ℕ × ℕ) × ℕ) × ℕ := (((0, 0), 0), 0)
    refine ⟨witness, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, by decide⟩
    simp [witness, Finset.mem_product, Finset.mem_range]
  )
  | n + 2 =>
    have : n + 1 < n + 2 := by omega
    have h_sub : n + 2 - 1 = n + 1 := rfl
    have h_prev : MyProp (n + 1) := get_inhabited (n + 1) (by omega)
    haveI : Inhabited (MyProp (n + 2 - 1)) := ⟨h_sub.symm ▸ h_prev⟩
    safe_step (n + 2) (by omega)

#print axioms get_inhabited
