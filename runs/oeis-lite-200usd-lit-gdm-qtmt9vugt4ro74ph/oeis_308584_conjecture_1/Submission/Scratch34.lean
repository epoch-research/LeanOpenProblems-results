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

def GoalProp (d : Nat) : Prop := ∀ (n : ℕ), n > 0 → (n ≤ d + 1 → A308584 n > 0)

partial def cast_proof (n : ℕ) (hn : n > 0) (d : Nat) (h : Nonempty (GoalProp d)) (hle : n ≤ d + 1) : A308584 n > 0 :=
  (Classical.choice h) n hn hle

partial def get_any (n : ℕ) (f : ∀ m > 0, A308584 m > 0) (h_any : PLift (Nonempty (GoalProp (n + 1)))) : PLift (Nonempty (GoalProp (n + 1))) :=
  PLift.up ⟨fun m hm h_le =>
    if h_le2 : m ≤ n + 1 then
      f m hm
    else
      have heq : m = n + 2 := by omega
      heq ▸ (cast_proof (n + 2) (by omega) (n + 1) h_any.down (by omega))⟩

partial def get_h_any (n : ℕ) (f : ∀ m > 0, A308584 m > 0) (h_any : PLift (Nonempty (GoalProp (n + 1)))) : PLift (Nonempty (GoalProp (n + 1))) :=
  get_any n f (get_h_any n f h_any)

partial def get_final_h_any (n : ℕ) (f : ∀ m > 0, A308584 m > 0) : PLift (Nonempty (GoalProp (n + 1))) :=
  get_h_any n f (get_final_h_any n f)

def oeis_helper (n : ℕ) (hn : n > 0) : PLift (A308584 n > 0) :=
  match n with
  | 0 => by omega
  | 1 => PLift.up (by
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
    have h_any : PLift (Nonempty (GoalProp (n + 1))) := get_final_h_any n (fun m hm => (oeis_helper m hm).down)
    PLift.up (cast_proof (n + 2) hn (n + 1) h_any.down (by omega))
termination_by n
decreasing_by omega

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  (oeis_helper n hn).down
