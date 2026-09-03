import FormalConjecturesUtil
/-! Finite closed-walk certificate for a cycle bundle diagnostic. -/
open SimpleGraph Fin.NatCast
namespace Erdos713CycleBundleCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def pos (x : Fin 9) (s : Fin 8 → Bool) : ℕ → Fin 9
  | 0 => x
  | n+1 => pos x s n + if s (↑n : Fin 8) then 1 else -1

lemma walk_certificate : ∀ (x : Fin 9) (b0 b1 b2 b3 b4 b5 b6 b7 : Bool),
    pos x ![b0,b1,b2,b3,b4,b5,b6,b7] 8 = x →
      ∃ i j : Fin 8, i < j ∧
        (pos x ![b0,b1,b2,b3,b4,b5,b6,b7] i).val % 2 = 0 ∧
        pos x ![b0,b1,b2,b3,b4,b5,b6,b7] i = pos x ![b0,b1,b2,b3,b4,b5,b6,b7] j := by
  decide

lemma repeated_hub_of_closed_walk (x : Fin 9) (s : Fin 8 → Bool)
    (h : pos x s 8 = x) :
    ∃ i j : Fin 8, i < j ∧ (pos x s i).val % 2 = 0 ∧ pos x s i = pos x s j := by
  have hv : ![s 0,s 1,s 2,s 3,s 4,s 5,s 6,s 7] = s := by
    funext i
    fin_cases i <;> rfl
  have hh := walk_certificate x (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) (s 6) (s 7)
  simpa only [hv] using hh h

lemma adj_options : ∀ x y : Fin 9, (cycleGraph 9).Adj x y → y = x+1 ∨ y = x+(-1) := by
  simp only [cycleGraph_adj]
  decide

lemma repeated_hub_of_hom (g : Fin 8 → Fin 9)
    (h : ∀ i, (cycleGraph 9).Adj (g i) (g (i+1))) :
    ∃ i j : Fin 8, i < j ∧ (g i).val % 2 = 0 ∧ g i = g j := by
  let s : Fin 8 → Bool := fun i => decide (g (i+1) = g i+1)
  have hs (i : Fin 8) : g (i+1) = g i + if s i then 1 else -1 := by
    by_cases hi : g (i+1) = g i+1
    · simp [s,hi]
    · have hj := (adj_options _ _ (h i)).resolve_left hi
      simpa [s,hi] using hj
  have heq (k : ℕ) : pos (g 0) s k = g (k : Fin 8) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      calc
        _ = g (k : Fin 8) + if s (k : Fin 8) then 1 else -1 := by rw [pos,ih]
        _ = g ((k : Fin 8)+1) := (hs _).symm
        _ = g (↑(k+1) : Fin 8) := by simp
  have hclosed : pos (g 0) s 8 = g 0 := by simpa using heq 8
  obtain ⟨i,j,hij,hi,hij'⟩ := repeated_hub_of_closed_walk (g 0) s hclosed
  refine ⟨i,j,hij,?_,?_⟩
  · simpa only [heq,Fin.cast_val_eq_self] using hi
  · simpa only [heq,Fin.cast_val_eq_self] using hij'

#print axioms repeated_hub_of_hom
#print axioms walk_certificate
end Erdos713CycleBundleCertificate
