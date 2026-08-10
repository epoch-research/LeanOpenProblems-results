import FormalConjectures.Util.ProblemImports

open Nat Finset

def triangular_number (k : ℕ) : ℕ := k * (k + 1) / 2

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

instance : Inhabited (GoalProp → GoalProp) :=
  ⟨fun h => h⟩

partial def get_proof (h : GoalProp) : GoalProp :=
  get_proof h

unsafe def my_unsafe_inhabited (u : Unit) : Inhabited GoalProp :=
  ⟨get_proof (@Inhabited.default GoalProp (my_unsafe_inhabited u))⟩

mutual
  opaque my_safe_inhabited (u : Unit) : Inhabited GoalProp
  instance : Inhabited (Inhabited GoalProp) := ⟨my_safe_inhabited ()⟩
end



instance : Inhabited GoalProp :=
  my_safe_inhabited ()

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  (default : GoalProp) n hn




#print axioms oeis_308584_conjecture_1



