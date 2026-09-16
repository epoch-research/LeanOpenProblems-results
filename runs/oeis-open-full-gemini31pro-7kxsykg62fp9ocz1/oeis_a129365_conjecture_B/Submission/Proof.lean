
import Submission.Spec
open Nat Finset

def num (n : ℕ) := (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k
def den (n : ℕ) := (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k

lemma a_eq (n : ℕ) : a n = num n / den n := rfl
