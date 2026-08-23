import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

example : 511 * 255 * 509 * 127 * 507 * 253 / 315 = 3430050471991 := by norm_num
example : 512 * 3430050471991 = 1756185841659392 := by norm_num

def popc (n : ℕ) : ℕ := (List.range (n.log2 + 1)).countP n.testBit

example : popc 1756185841659392 % 2 = 0 := by decide
example : popc 1756185841659392 = 22 := by decide
