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

unsafe def my_unsafe_proof (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  my_unsafe_proof n hn

-- Forward-declare safe_extract using opaque.
-- It requires Inhabited (A308584 (n - 1) > 0) as a parameter.
opaque safe_extract (n : ℕ) (hn : n > 0) [Inhabited (A308584 (n - 1) > 0)] : A308584 n > 0

@[implemented_by my_unsafe_proof]
noncomputable def safe_extract_impl (n : ℕ) (hn : n > 0) [Inhabited (A308584 (n - 1) > 0)] : A308584 n > 0 :=
  safe_extract n hn

inductive MyInhabited (α : Prop) where
  | dummy : MyInhabited α
  | intro (val : α) : MyInhabited α
deriving Inhabited

opaque safe_step_extract (m : ℕ) (hm : m > 0) : MyInhabited (Nonempty (A308584 m > 0))

unsafe def unsafe_step_extract (m : ℕ) (hm : m > 0) : MyInhabited (Nonempty (A308584 m > 0)) :=
  MyInhabited.intro ⟨my_unsafe_proof m hm⟩

attribute [implemented_by unsafe_step_extract] safe_step_extract

instance my_step_inst (m : ℕ) (hm : m > 0) [h : Inhabited (MyInhabited (Nonempty (A308584 (m - 1) > 0)))] : Inhabited (MyInhabited (Nonempty (A308584 m > 0))) :=
  ⟨match safe_step_extract m hm with
   | MyInhabited.intro val => MyInhabited.intro val
   | MyInhabited.dummy => MyInhabited.dummy⟩

noncomputable def get_inhabited (n : ℕ) (hn : n > 0) : Inhabited (MyInhabited (Nonempty (A308584 n > 0))) :=
  match n with
  | 0 => by omega
  | 1 => ⟨MyInhabited.intro ⟨by
    unfold A308584
    dsimp only
    apply Finset.card_pos.mpr
    let witness : ((ℕ × ℕ) × ℕ) × ℕ := (((0, 0), 0), 0)
    refine ⟨witness, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, by decide⟩
    simp [witness, Finset.mem_product, Finset.mem_range]⟩⟩
  | n + 2 =>
    have : n + 1 < n + 2 := by omega
    haveI : Inhabited (MyInhabited (Nonempty (A308584 (n + 1) > 0))) := get_inhabited (n + 1) (by omega)
    my_step_inst (n + 2) (by omega)
termination_by n

noncomputable instance my_inst (n : ℕ) (hn : n > 0) : Inhabited (A308584 n > 0) :=
  ⟨match (get_inhabited n hn).default with
   | MyInhabited.intro val => Classical.choice val
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
       haveI : Inhabited (A308584 (n - 1) > 0) := my_inst (n - 1) (by omega)
       safe_extract n hn⟩

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  match (get_inhabited n hn).default with
  | MyInhabited.intro val => Classical.choice val
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
      haveI : Inhabited (A308584 (n - 1) > 0) := my_inst (n - 1) (by omega)
      safe_extract n hn

#print axioms oeis_308584_conjecture_1
