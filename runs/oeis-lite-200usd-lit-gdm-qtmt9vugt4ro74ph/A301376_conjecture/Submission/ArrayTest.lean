import FormalConjectures.Util.ProblemImports

def get_witness_tree_0 (m : ℕ) : ℕ × ℕ × ℕ × ℕ := (0,0,0,0)
def get_witness_tree_1 (m : ℕ) : ℕ × ℕ × ℕ × ℕ := (1,1,1,1)
def get_witness_tree_2 (m : ℕ) : ℕ × ℕ × ℕ × ℕ := (2,2,2,2)
def get_witness_tree_3 (m : ℕ) : ℕ × ℕ × ℕ × ℕ := (3,3,3,3)
def get_witness_tree_4 (m : ℕ) : ℕ × ℕ × ℕ × ℕ := (4,4,4,4)
def get_witness_tree_5 (m : ℕ) : ℕ × ℕ × ℕ × ℕ := (5,5,5,5)
def get_witness_tree_6 (m : ℕ) : ℕ × ℕ × ℕ × ℕ := (6,6,6,6)
def get_witness_tree_7 (m : ℕ) : ℕ × ℕ × ℕ × ℕ := (7,7,7,7)
def get_witness_tree_8 (m : ℕ) : ℕ × ℕ × ℕ × ℕ := (8,8,8,8)
def get_witness_tree_9 (m : ℕ) : ℕ × ℕ × ℕ × ℕ := (9,9,9,9)

def get_witness (m : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  if m ≤ 5000 then
    if m ≤ 3000 then
      if m ≤ 1000 then get_witness_tree_0 m
      else if m ≤ 2000 then get_witness_tree_1 (m - 1000)
      else get_witness_tree_2 (m - 2000)
    else
      if m ≤ 4000 then get_witness_tree_3 (m - 3000)
      else get_witness_tree_4 (m - 4000)
  else
    if m ≤ 8000 then
      if m ≤ 7000 then
        if m ≤ 6000 then get_witness_tree_5 (m - 5000)
        else get_witness_tree_6 (m - 6000)
      else get_witness_tree_7 (m - 7000)
    else
      if m ≤ 9000 then get_witness_tree_8 (m - 8000)
      else get_witness_tree_9 (m - 9000)

lemma get_witness_eq_tree_0 (m : ℕ) (h_gt : 0 < m) (h_le : m ≤ 1000) :
    get_witness m = get_witness_tree_0 m := by
  unfold get_witness
  split_ifs
  all_goals (try omega)
  all_goals (try rfl)

lemma get_witness_eq_tree_1 (m : ℕ) (h_gt : 1000 < m) (h_le : m ≤ 2000) :
    get_witness m = get_witness_tree_1 (m - 1000) := by
  unfold get_witness
  split_ifs
  all_goals (try omega)
  all_goals (try rfl)
