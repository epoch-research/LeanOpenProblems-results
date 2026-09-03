import Submission.SinglePrimeExchange
open Erdos970.OptimalCoverCore
example : (survivors 20 {3,5} (fun _ => 0)).card = 11 := by decide +kernel
