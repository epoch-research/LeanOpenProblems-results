import Mathlib

namespace KTest

/-- next Pascal column: given column k (as list C(0,k), C(1,k), ..., C(N,k)),
    produce column k+1 using C(n+1,k+1) = C(n,k) + C(n,k+1). -/
def pascalStep (col : List ℕ) : List ℕ :=
  -- col' n = sum of col[0..n-1]? No: C(n+1,k+1)=C(n,k+1)+C(n,k), C(0,k+1)=0
  (col.foldl (fun (acc : List ℕ × ℕ) c => (acc.2 :: acc.1, acc.2 + c)) ([], 0)).1.reverse

/-- correction list: n-th entry = C(n,k) * prev[n-k], i.e. zeros for n < k. -/
def corr (k : ℕ) (colk prev : List ℤ) : List ℤ :=
  List.replicate k 0 ++ List.zipWith (· * ·) (colk.drop k) prev

def rowStep (prev : List ℤ) (k : ℕ) (colk : List ℕ) : List ℤ :=
  List.zipWith (· - ·) prev (corr k (colk.map (Int.ofNat)) prev)

/-- iterate factors k = 1..K, carrying (row, pascal column (k)). -/
def dp (N : ℕ) : List ℤ :=
  let row0 : List ℤ := 1 :: List.replicate N 0
  let col1 : List ℕ := List.range (N+1)   -- C(n,1) = n
  let rec go (k : ℕ) (fuel : ℕ) (row : List ℤ) (col : List ℕ) : List ℤ :=
    match fuel with
    | 0 => row
    | fuel+1 => go (k+1) fuel (rowStep row k col) (pascalStep col)
  go 1 N row0 col1

/-- triangular index m(n): number of t >= 1 with t*(t+1)/2 <= n -/
def mIdx (n : ℕ) : ℕ :=
  let rec go (t acc : ℕ) (fuel : ℕ) : ℕ :=
    match fuel with
    | 0 => acc
    | fuel+1 => if (t+1)*(t+2)/2 ≤ n then go (t+1) (acc+1) fuel else acc
  go 0 0 n

def signOK (n : ℕ) (a : ℤ) : Bool :=
  if mIdx n % 2 == 0 then a > 0 else a < 0

def checkAll (N : ℕ) : Bool :=
  let l := dp N
  (l.zipIdx.all fun (a, n) => signOK n a)

end KTest
