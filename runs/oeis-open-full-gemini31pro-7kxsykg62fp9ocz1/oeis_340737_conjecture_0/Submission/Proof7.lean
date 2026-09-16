import Mathlib
open Nat
open Polynomial Filter Topology
open scoped Polynomial

-- assume a_seq_eq_Q and b_seq_eq_Q are proven

-- I want to show E_int_odd_bound: |(B_int (2*k+1) : ℝ) * Real.exp 1 - (A_int (2*k+1) : ℝ)| ≤ Real.exp 1 / ((k+1).factorial * 4^(k+1))
