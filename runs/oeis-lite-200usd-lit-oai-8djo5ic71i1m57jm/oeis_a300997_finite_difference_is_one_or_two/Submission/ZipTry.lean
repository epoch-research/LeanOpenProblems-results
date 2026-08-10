import FormalConjectures.Util.ProblemImports
open List Nat

def halfC (m : ℕ) := (m+1)/2
def halfF (m : ℕ) := m/2
def mass (l : List ℕ) (i : ℕ) := l.getD i 0

example (config : List ℕ) :
    (List.zipWith Nat.add (config.map halfC ++ [0]) (0 :: config.map halfF)).getD 0 0 =
      halfC (mass config 0) := by
  cases config <;> simp [mass, halfC, halfF]

example (config : List ℕ) (j : ℕ) :
    (List.zipWith Nat.add (config.map halfC ++ [0]) (0 :: config.map halfF)).getD (j+1) 0 =
      halfC (mass config (j+1)) + halfF (mass config j) := by
  by_cases hj : j < config.length
  · by_cases hj1 : j+1 < config.length
    · simp [mass, halfC, halfF, hj, hj1]
    · have hlen : config.length = j+1 := by omega
      simp [mass, halfC, halfF, hj, hlen]
  · have hlenj : config.length ≤ j := by omega
    have hlenj1 : config.length ≤ j+1 := by omega
    simp [mass, halfC, halfF, hj, hlenj, hlenj1]
