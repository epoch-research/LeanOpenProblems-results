import FormalConjecturesUtil

/-!
A counting constraint for reversible insertion on unordered states. This is
an auxiliary combinatorial statement, not a proof or disproof of Erdos 773.
-/
namespace Erdos773.ReversibleInsertionCapacity
open Finset
set_option maxHeartbeats 1000000
variable {α : Type*} [DecidableEq α] [Fintype α]

def level (F : Finset (Finset α)) (k : ℕ) : Finset (Finset α) :=
  F.filter (fun S => S.card = k)

def children (F : Finset (Finset α)) (k : ℕ)
    (parent : Finset α → Finset α) (S : Finset α) : Finset (Finset α) :=
  (level F (k+1)).filter (fun T => parent T = S)

omit [DecidableEq α] [Fintype α] in
lemma level_sized (F : Finset (Finset α)) (k : ℕ) :
    (level F k : Set (Finset α)).Sized k := by
  intro S hS
  exact (mem_filter.mp hS).2

/-- Downward closure gives the usual local LYM ratio between successive
levels, including for independence families. -/
theorem level_ratio (F : Finset (Finset α)) (k : ℕ)
    (hk : k < Fintype.card α)
    (hdown : ∀ T ∈ F, ∀ S ⊆ T, S ∈ F) :
    (level F (k+1)).card*(k+1) ≤ (level F k).card*(Fintype.card α-k) := by
  have hshadow : (level F (k+1)).shadow ⊆ level F k := by
    intro S hS
    obtain ⟨T,hT,hST,hcard⟩ := mem_shadow_iff_exists_mem_card_add_one.mp hS
    obtain ⟨hTF,hTk⟩ := mem_filter.mp hT
    exact mem_filter.mpr ⟨hdown T hTF S hST, by omega⟩
  have hh := local_lubell_yamamoto_meshalkin_inequality_mul (level_sized F (k+1))
  have he : Fintype.card α-(k+1)+1 = Fintype.card α-k := by omega
  rw [he] at hh
  exact hh.trans (Nat.mul_le_mul_right _ (card_le_card hshadow))

omit [Fintype α] in
lemma children_sum (F : Finset (Finset α)) (k : ℕ)
    (parent : Finset α → Finset α)
    (hp : ∀ T ∈ level F (k+1), parent T ∈ level F k) :
    (∑ S ∈ level F k, (children F k parent S).card) = (level F (k+1)).card := by
  symm
  exact card_eq_sum_card_fiberwise hp

/-- A unique parent for each next state cannot give every current state
more than `(N-k)/(k+1)` distinct reversible extensions. The estimate does
not claim that every state has few children. -/
theorem uniform_branching_bound (F : Finset (Finset α)) (k D : ℕ)
    (hk : k < Fintype.card α)
    (hdown : ∀ T ∈ F, ∀ S ⊆ T, S ∈ F)
    (hne : (level F k).Nonempty)
    (parent : Finset α → Finset α)
    (hp : ∀ T ∈ level F (k+1), parent T ∈ level F k)
    (hD : ∀ S ∈ level F k, D ≤ (children F k parent S).card) :
    D*(k+1) ≤ Fintype.card α-k := by
  have hs : (level F k).card*D ≤ (level F (k+1)).card := by
    calc
      _ = ∑ S ∈ level F k, D := by simp
      _ ≤ ∑ S ∈ level F k, (children F k parent S).card := sum_le_sum hD
      _ = _ := children_sum F k parent hp
  have hh := (Nat.mul_le_mul_right (k+1) hs).trans (level_ratio F k hk hdown)
  rw [Nat.mul_assoc] at hh
  exact Nat.le_of_mul_le_mul_left hh (card_pos.mpr hne)

/-- At least one state has the small branching count. This does not exclude
an algorithm with large branching on some specially selected states. -/
theorem exists_small_branch (F : Finset (Finset α)) (k : ℕ)
    (hk : k < Fintype.card α)
    (hdown : ∀ T ∈ F, ∀ S ⊆ T, S ∈ F)
    (hne : (level F k).Nonempty)
    (parent : Finset α → Finset α)
    (hp : ∀ T ∈ level F (k+1), parent T ∈ level F k) :
    ∃ S ∈ level F k,
      (children F k parent S).card*(k+1) ≤ Fintype.card α-k := by
  obtain ⟨S,hS,hmin⟩ := (level F k).exists_min_image (fun S => (children F k parent S).card) hne
  exact ⟨S,hS,uniform_branching_bound F k _ hk hdown hne parent hp hmin⟩

#print axioms level_ratio
#print axioms uniform_branching_bound
#print axioms exists_small_branch
end Erdos773.ReversibleInsertionCapacity
