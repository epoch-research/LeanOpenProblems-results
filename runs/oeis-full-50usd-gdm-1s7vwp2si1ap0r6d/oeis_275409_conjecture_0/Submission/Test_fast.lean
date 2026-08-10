import Mathlib

def loop_z (n w x y z : Nat) (acc : Nat) : Nat :=
  match z with
  | 0 =>
    let sum_sq := 2 * w^2 + x^2 + y^2 + 0^2
    let lin_comb := w + x + 2 * y + 4 * 0
    if sum_sq == n && lin_comb.sqrt * lin_comb.sqrt == lin_comb then acc + 1 else acc
  | z + 1 =>
    let sum_sq := 2 * w^2 + x^2 + y^2 + (z + 1)^2
    let lin_comb := w + x + 2 * y + 4 * (z + 1)
    let new_acc := if sum_sq == n && lin_comb.sqrt * lin_comb.sqrt == lin_comb then acc + 1 else acc
    loop_z n w x y z new_acc

def loop_y (n w x y max_z : Nat) (acc : Nat) : Nat :=
  match y with
  | 0 => loop_z n w x 0 max_z acc
  | y + 1 =>
    let new_acc := loop_z n w x (y + 1) max_z acc
    loop_y n w x y max_z new_acc

def loop_x (n w x max_y max_z : Nat) (acc : Nat) : Nat :=
  match x with
  | 0 => loop_y n w 0 max_y max_z acc
  | x + 1 =>
    let new_acc := loop_y n w (x + 1) max_y max_z acc
    loop_x n w x max_y max_z new_acc

def loop_w (n w max_x max_y max_z : Nat) (acc : Nat) : Nat :=
  match w with
  | 0 => loop_x n 0 max_x max_y max_z acc
  | w + 1 =>
    let new_acc := loop_x n (w + 1) max_x max_y max_z acc
    loop_w n w max_x max_y max_z new_acc

def a_fast (n : ℕ) : ℕ :=
  let M := n.sqrt
  loop_w n M M M M 0

theorem test_fast_decide : a_fast 2 = 1 := by decide
