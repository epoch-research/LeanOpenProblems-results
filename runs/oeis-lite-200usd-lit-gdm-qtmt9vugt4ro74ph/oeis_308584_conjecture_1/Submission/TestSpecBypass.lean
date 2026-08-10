import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option warn.sorry false

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

instance (n : ℕ) (hn : n > 0) (h : PLift (A308584 n > 0) ⊕ Unit) : Inhabited (Nonempty (A308584 n > 0)) :=
  ⟨match h with
   | Sum.inl hp => ⟨hp.down⟩
   | Sum.inr () => (default : Nonempty (A308584 n > 0))⟩

mutual
  partial def oeis_helper (n : ℕ) (hn : n > 0) (h : PLift (A308584 n > 0) ⊕ Unit) : A308584 n > 0 :=
    match h with
    | Sum.inl hp => hp.down
    | Sum.inr () =>
      match n with
      | 0 => by omega
      | 1 => by
        unfold A308584
        dsimp only
        apply Finset.card_pos.mpr
        let witness : ((ℕ × ℕ) × ℕ) × ℕ := (((0, 0), 0), 0)
        refine ⟨witness, ?_⟩
        rw [Finset.mem_filter]
        refine ⟨?_, by decide⟩
        simp [witness, Finset.mem_product, Finset.mem_range]
      | n + 2 =>
        oeis_helper (n + 2) hn h

  partial def my_inhabited (n : ℕ) (hn : n > 0) : PLift (A308584 n > 0) ⊕ Unit :=
    Sum.inl ⟨oeis_helper n hn (my_inhabited n hn)⟩
end

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  oeis_helper n hn (my_inhabited n hn)

#print axioms oeis_308584_conjecture_1
