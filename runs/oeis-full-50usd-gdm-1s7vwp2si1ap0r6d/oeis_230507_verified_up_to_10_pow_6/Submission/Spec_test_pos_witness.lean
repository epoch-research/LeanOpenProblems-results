import FormalConjectures.Util.ProblemImports
open Nat Finset

namespace OeisA230507

def C_array : Array ℕ := #[1, 2]
def CustomS (m : ℕ) : Bool := true
def witness_S_all_1 : Array ℕ := #[0, 1]

def check_S_witness_1 (n : ℕ) : Bool :=
  if n < 3 then true
  else
    let idx := n - 0
    let a_idx := witness_S_all_1.getD (2 * idx) 0
    let b_idx := witness_S_all_1.getD (2 * idx + 1) 0
    let a := C_array.getD a_idx 0
    let b := C_array.getD b_idx 0
    let c := n - a - b
    decide (1 ≤ a ∧ a ≤ n / 3 ∧ a ≤ b ∧ b ≤ (n - a) / 2) && CustomS a && CustomS b && CustomS c

def A230507_underestimate (n : ℕ) : ℕ := 0

theorem A230507_underestimate_pos_of_witness_1 (n : ℕ) (h_range : n > 2 ∧ n < 20000) (h : check_S_witness_1 n = true) :
    A230507_underestimate n > 0 := by
  dsimp [check_S_witness_1] at h
  split_ifs at h with hn3
  · omega
  · rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨h_bounds, hSa⟩, hSb⟩, hSc⟩
    rw [decide_eq_true_iff] at h_bounds
    have ha1 := h_bounds.1
    have ha2 := h_bounds.2.1
    have hab := h_bounds.2.2.1
    have hb2 := h_bounds.2.2.2
    sorry
