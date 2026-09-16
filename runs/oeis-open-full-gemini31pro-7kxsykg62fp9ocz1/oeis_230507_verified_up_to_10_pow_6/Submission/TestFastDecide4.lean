set_option maxRecDepth 2000000

def sumLoop : Nat → Nat → Nat
| 0, acc => acc
| n + 1, acc => sumLoop n (acc + (n + 1))

-- sum of 1 to 100000 is 100000 * 100001 / 2 = 5000050000
theorem sum_100000 : sumLoop 100000 0 = 5000050000 := by decide
