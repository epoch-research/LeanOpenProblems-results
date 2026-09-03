import Submission.BuchstabGridData
open Erdos970.BuchstabGrid
#eval (101%10 : ℚ)
#eval ((101%10 : ℕ) : ℚ)
#eval ((1-((101%10 : ℕ):ℚ)/10)*profileValues[0]!+(((101%10 : ℕ):ℚ)/10)*profileValues[1]!)
example : (90009/50000 : ℚ)*((1-((101%10 : ℕ):ℚ)/10)*profileValues[0]!+(((101%10 : ℕ):ℚ)/10)*profileValues[1]!) ≤ (baseNodes[101]! : ℚ)/scale := by decide +kernel
