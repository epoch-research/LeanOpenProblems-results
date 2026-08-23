import FormalConjectures.Util.ProblemImports
open Nat

def SunGoodD (n : ℕ) : Bool :=
  (List.range (n + 1)).any fun a =>
    (List.range (n + 1)).any fun b =>
      let m := 2 ^ a * 3 ^ b
      (m ≤ n && (6 * (n - m) + 1).Prime) ||
      (m < n && (6 * (n - m) - 1).Prime)

#eval SunGoodD 21

lemma test20 : (List.range 20).all (fun n => n ≤ 1 || SunGoodD n) = true := by native_decide
