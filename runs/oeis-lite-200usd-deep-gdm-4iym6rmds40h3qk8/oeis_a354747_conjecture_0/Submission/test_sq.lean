import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000

def sq_1 (x : ℕ) : ℕ := (x * x) % 1000000
def sq_2 (x : ℕ) : ℕ := sq_1 (sq_1 x)
def sq_4 (x : ℕ) : ℕ := sq_2 (sq_2 x)
def sq_8 (x : ℕ) : ℕ := sq_4 (sq_4 x)
def sq_16 (x : ℕ) : ℕ := sq_8 (sq_8 x)
def sq_32 (x : ℕ) : ℕ := sq_16 (sq_16 x)
def sq_64 (x : ℕ) : ℕ := sq_32 (sq_32 x)
def sq_128 (x : ℕ) : ℕ := sq_64 (sq_64 x)
def sq_256 (x : ℕ) : ℕ := sq_128 (sq_128 x)
def sq_512 (x : ℕ) : ℕ := sq_256 (sq_256 x)
def sq_1024 (x : ℕ) : ℕ := sq_512 (sq_512 x)
def sq_2048 (x : ℕ) : ℕ := sq_1024 (sq_1024 x)
def sq_4096 (x : ℕ) : ℕ := sq_2048 (sq_2048 x)
def sq_8192 (x : ℕ) : ℕ := sq_4096 (sq_4096 x)
def sq_16384 (x : ℕ) : ℕ := sq_8192 (sq_8192 x)
def sq_32768 (x : ℕ) : ℕ := sq_16384 (sq_16384 x)

theorem test_sq : sq_32768 2 = 612544 := by
  decide
