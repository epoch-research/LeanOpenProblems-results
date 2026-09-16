set_option maxRecDepth 2000000

def sumLoop : Nat → Nat → Nat
| 0, acc => acc
| n + 1, acc => sumLoop n (acc + (n + 1))

theorem sum_1000 : sumLoop 1000 0 = 500500 := by decide
