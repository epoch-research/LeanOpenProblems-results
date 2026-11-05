import FormalConjecturesUtil

/-!
# Basic facts about the Ramsey numbers in Erdős problem 812

This file isolates the defining finite Ramsey property and the precise quantitative
extension estimate that suffices for the ratio conjecture. It does not assume the conjecture.
-/

namespace Erdos812.Support

open Combinatorics Filter

/-- The finite property whose least satisfying order is `hypergraphRamsey r n`. -/
def RamseyProperty (r n m : ℕ) : Prop :=
  ∀ c : Finset (Fin m) → Bool,
    ∃ S : Finset (Fin m), S.card = n ∧
      ∃ b : Bool, ∀ e : Finset (Fin m), e ⊆ S → e.card = r → c e = b

lemma graph_property_nonempty (n : ℕ) :
    {m | RamseyProperty 2 n m}.Nonempty := by
  refine ⟨(n + n).choose n, ?_⟩
  intro c
  have hcard : (n + n).choose n ≤
      (Finset.univ : Finset (Fin ((n + n).choose n))).card := by simp
  rcases Diagonal.hasRamseyProperty_choose n n c Finset.univ hcard with
    ⟨S, _, hS, hmono⟩ | ⟨S, _, hS, hmono⟩
  · exact ⟨S, hS, false, hmono⟩
  · exact ⟨S, hS, true, hmono⟩

lemma graph_property_at_ramsey (n : ℕ) :
    RamseyProperty 2 n (hypergraphRamsey 2 n) := by
  exact Nat.sInf_mem (graph_property_nonempty n)

lemma target_le_graph_ramsey (n : ℕ) : n ≤ hypergraphRamsey 2 n := by
  exact le_hypergraphRamsey 2 n (graph_property_nonempty n)

lemma graph_ramsey_pos {n : ℕ} (hn : 0 < n) : 0 < hypergraphRamsey 2 n :=
  lt_of_lt_of_le hn (target_le_graph_ramsey n)

lemma ramsey_le_of_property {r n m : ℕ} (h : RamseyProperty r n m) :
    hypergraphRamsey r n ≤ m :=
  Nat.sInf_le h

lemma not_property_of_lt_ramsey {r n m : ℕ} (hm : m < hypergraphRamsey r n) :
    ¬ RamseyProperty r n m := by
  intro h
  exact (Nat.not_le_of_gt hm) (ramsey_le_of_property h)

/-- There is a coloring immediately below the Ramsey threshold avoiding the target. -/
lemma critical_coloring {n : ℕ} (hn : 0 < n) :
    ∃ c : Finset (Fin (hypergraphRamsey 2 n - 1)) → Bool,
      ¬ ∃ S : Finset (Fin (hypergraphRamsey 2 n - 1)), S.card = n ∧
        ∃ b : Bool, ∀ e : Finset (Fin (hypergraphRamsey 2 n - 1)),
          e ⊆ S → e.card = 2 → c e = b := by
  have hpos := graph_ramsey_pos hn
  have hnot : ¬ RamseyProperty 2 n (hypergraphRamsey 2 n - 1) :=
    not_property_of_lt_ramsey (by omega)
  exact Classical.not_forall.mp hnot

/-- The finite Ramsey property is monotone in the available order. -/
lemma RamseyProperty.mono_order {r n m m' : ℕ}
    (h : RamseyProperty r n m) (hm : m ≤ m') : RamseyProperty r n m' := by
  classical
  intro c
  let f : Fin m ↪ Fin m' := Fin.castLEEmb hm
  obtain ⟨S, hS, b, hmono⟩ := h (fun e => c (e.map f))
  refine ⟨S.map f, by simpa using hS, b, ?_⟩
  intro e he her
  let e₀ := S.filter (fun x => f x ∈ e)
  have he₀ : e₀ ⊆ S := Finset.filter_subset _ _
  have hmap : e₀.map f = e := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact (Finset.mem_filter.mp hy).2
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp (he hx)
      exact Finset.mem_map.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hx⟩, rfl⟩
  have hcard : e₀.card = r := by
    calc e₀.card = (e₀.map f).card := (Finset.card_map f).symm
      _ = e.card := congrArg Finset.card hmap
      _ = r := her
  simpa only [hmap] using hmono e₀ he₀ hcard

/-- The finite Ramsey property is antitone in the requested homogeneous size. -/
lemma RamseyProperty.mono_target {r n n' m : ℕ}
    (h : RamseyProperty r n' m) (hn : n ≤ n') : RamseyProperty r n m := by
  intro c
  obtain ⟨S, hS, b, hmono⟩ := h c
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq (hn.trans_eq hS.symm)
  exact ⟨T, hcard, b, fun e he her => hmono e (he.trans hT) her⟩

lemma graph_ramsey_monotone : Monotone (hypergraphRamsey 2) := by
  intro n n' hn
  exact ramsey_le_of_property ((graph_property_at_ramsey n').mono_target hn)

/-- An avoiding coloring on `m` vertices is strictly below the Ramsey threshold. -/
lemma order_lt_graph_ramsey_of_avoiding {n m : ℕ}
    (h : ¬ RamseyProperty 2 n m) : m < hypergraphRamsey 2 n := by
  by_contra hnot
  exact h ((graph_property_at_ramsey n).mono_order (Nat.le_of_not_gt hnot))

/-- A fixed fractional extension of a critical coloring is enough for the target ratio. -/
lemma extension_implies_ratio {δ : ℝ} (hδ : 0 < δ)
    (hext : ∀ᶠ n : ℕ in atTop,
      (hypergraphRamsey 2 (n + 1) : ℝ) ≥
        (1 + δ) * ((hypergraphRamsey 2 n : ℝ) - 1) + 1) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop,
      (hypergraphRamsey 2 (n + 1) : ℝ) / (hypergraphRamsey 2 n : ℝ) ≥ 1 + c := by
  refine ⟨δ / 2, by positivity, ?_⟩
  filter_upwards [hext, eventually_ge_atTop (2 : ℕ)] with n hn hn₂
  have hR : (2 : ℝ) ≤ (hypergraphRamsey 2 n : ℝ) := by
    exact_mod_cast hn₂.trans (target_le_graph_ramsey n)
  have hpos : (0 : ℝ) < (hypergraphRamsey 2 n : ℝ) := by linarith
  apply (le_div_iff₀ hpos).2
  have hnonneg : 0 ≤ δ * ((hypergraphRamsey 2 n : ℝ) - 2) :=
    mul_nonneg hδ.le (sub_nonneg.mpr hR)
  nlinarith

end Erdos812.Support
