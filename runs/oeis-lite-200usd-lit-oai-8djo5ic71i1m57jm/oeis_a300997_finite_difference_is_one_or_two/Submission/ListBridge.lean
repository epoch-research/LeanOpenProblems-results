import FormalConjectures.Util.ProblemImports
open List Nat Function Set

def halfC (m : ℕ) := (m+1)/2
def halfF (m : ℕ) := m/2
def trimZ (l : List ℕ) := (List.reverse l).dropWhile (fun x => x=0) |>.reverse
def caStep (config : List ℕ) : List ℕ :=
  let base_masses := config.map halfC ++ [0]
  let received_masses := 0 :: config.map halfF
  let next_config_long := List.zipWith Nat.add base_masses received_masses
  trimZ next_config_long

def mass (l : List ℕ) (i : ℕ) := l.getD i 0
def pref (l : List ℕ) (j : ℕ) := ∑ i ∈ Finset.range j, mass l i

#check Finset.sum_range_succ
#check Finset.sum_range_zero
#check List.getD_map
#check List.getD_append
#check List.getD_append_right
#check List.getD_eq_default
#check List.length_zipWith
#check List.getElem?_zipWith
#check List.getElem_zipWith
#check List.getD_cons_zero
#check List.getD_cons_succ

lemma getD_cons_zero_nat (x:ℕ) (l:List ℕ) : (x::l).getD 0 0 = x := rfl
lemma getD_cons_succ_nat (x:ℕ) (l:List ℕ) (i:ℕ) : (x::l).getD (i+1) 0 = l.getD i 0 := rfl

lemma getD_append_zero (l : List ℕ) (i : ℕ) : (l ++ [0]).getD i 0 = l.getD i 0 := by
  by_cases h : i < l.length
  · rw [List.getD_append _ _ _ _ h]
  · have hle : l.length ≤ i := by omega
    rw [List.getD_append_right _ _ _ _ hle]
    rw [List.getD_eq_default _ _ hle]
    simp

lemma trimZ_getD (l : List ℕ) (i : ℕ) : (trimZ l).getD i 0 = l.getD i 0 := by
  unfold trimZ
  -- try induction reverseRec
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
      by_cases hx : x = 0
      · simp [List.reverse_append, hx]
        change (dropWhile (fun x => decide (x = 0)) xs.reverse).reverse.getD i 0 = (xs ++ [0]).getD i 0
        rw [ih, getD_append_zero]
      · simp [List.reverse_append, hx]

def longStep (config : List ℕ) : List ℕ :=
  List.zipWith Nat.add (config.map halfC ++ [0]) (0 :: config.map halfF)

lemma caStep_getD (config : List ℕ) (i : ℕ) :
    mass (caStep config) i = halfC (mass config i) + if i = 0 then 0 else halfF (mass config (i-1)) := by
  unfold caStep mass
  rw [trimZ_getD]
  unfold longStep
  -- unfold zip expression directly
  simp only
  rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  cases i with
  | zero =>
      simp [halfC, halfF, List.getD_eq_getElem?_getD]
  | succ j =>
      by_cases hj : j < config.length
      · have hjmap : j < (config.map halfF).length := by simpa using hj
        have hs1 : (0 :: map halfF config)[j+1]? = some (halfF (config.getD j 0)) := by
          simp [List.getD_eq_getElem?_getD, hj]
        -- hard continue
        sorry
      · sorry
