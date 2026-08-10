import FormalConjectures.Util.ProblemImports
open List Nat Function Set

def half_ceil (m : ℕ) : ℕ := (m + 1) / 2
def half_floor (m : ℕ) : ℕ := m / 2
def rawWith (c : ℕ) : List ℕ → List ℕ
| [] => [c]
| a::l => (half_ceil a + c) :: rawWith (half_floor a) l

def tailSum (l : List ℕ) (i : ℕ) : ℕ := (l.drop i).sum

lemma ceil_add_floor (a : ℕ) : half_ceil a + half_floor a = a := by
  unfold half_ceil half_floor
  omega

lemma sum_rawWith (c : ℕ) (l : List ℕ) : (rawWith c l).sum = c + l.sum := by
  induction l generalizing c with
  | nil => simp [rawWith]
  | cons a l ih =>
      simp [rawWith, ih]
      have h := ceil_add_floor a
      omega

lemma tailSum_rawWith_succ_carry (c : ℕ) (l : List ℕ) (i : ℕ) :
    tailSum (rawWith c l) (i+1) = tailSum (rawWith 0 l) (i+1) := by
  induction l generalizing c i with
  | nil => cases i <;> simp [tailSum, rawWith]
  | cons a l ih =>
      cases i with
      | zero => simp [tailSum, rawWith, sum_rawWith]
      | succ i => simp [tailSum, rawWith, ih]

lemma tail_rawWith_zero (l : List ℕ) (i : ℕ) :
    tailSum (rawWith 0 l) (i+1) = (tailSum l i + tailSum l (i+1))/2 := by
  induction l generalizing i with
  | nil => cases i <;> simp [tailSum, rawWith]
  | cons a l ih =>
      cases i with
      | zero =>
          simp [tailSum, rawWith, sum_rawWith]
          unfold half_floor
          rw [show a + l.sum + l.sum = a + 2 * l.sum by omega]
          rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
      | succ i =>
          simp [tailSum, rawWith]
          change tailSum (rawWith (half_floor a) l) (i+1) = (tailSum l i + tailSum l (i+1)) / 2
          rw [tailSum_rawWith_succ_carry]
          exact ih i
