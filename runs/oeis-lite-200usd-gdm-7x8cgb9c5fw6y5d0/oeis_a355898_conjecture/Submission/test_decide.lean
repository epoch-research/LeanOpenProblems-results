import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 50000

open Nat

def A355898_loop : ℕ → ℕ → ℕ → ℕ × ℕ
| 0, a, b => (a, b)
| n + 1, a, b =>
  let g := Nat.gcd b a
  A355898_loop n b (g + (b + a) / g)

theorem A355898_loop_split (n : ℕ) (m : ℕ) (a b : ℕ) :
  A355898_loop (m + n) a b = A355898_loop m (A355898_loop n a b).1 (A355898_loop n a b).2 := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [A355898_loop]
    exact ih b (Nat.gcd b a + (b + a) / Nat.gcd b a)

def B_part1_fst : ℕ := 21083164479806096515356722572657032356452641532196964471734454042069427768422851
def B_part1_snd : ℕ := 28915667640405551860002330528287313672011298792593740112205349379187439965146791

def B_part1 : ℕ × ℕ := A355898_loop 943 1 1
theorem B_part1_val : B_part1 = (B_part1_fst, B_part1_snd) := by rfl

def B_part2_fst : ℕ := 61487173697280314342847829416770492687570365949542092984749465909417812015617904429397845115959129814651904544478994917699943899328892088595804830844499234278310202491877
def B_part2_snd : ℕ := 76452161361304736281088243638640555729162999178938902184563884252154698646312583302755156747828014724173207943131557663222458413180216472794072256364899776140123822883869

def B_part2 : ℕ × ℕ := A355898_loop 943 B_part1_fst B_part1_snd
theorem B_part2_val : B_part2 = (B_part2_fst, B_part2_snd) := by rfl

def B_part3_fst : ℕ := 1955059339396018443372029741556451192023211403061736598798234747381694774477959657294963315480106623922746813904458104264393864310344623705220400715382930865062908015182938479578907726707904661884874420477344397971135336243231366048163813483166897363371693362473
def B_part3_snd : ℕ := 3157649818594930623793329955375556915208473211333536978291044055440152992403556419629532678905191324526797350592478211046441177433313934515853901178319113643530603228852094227112651022432753789328087358688680169293194075836252937384645382835408925077460089932725

def B_part3 : ℕ × ℕ := A355898_loop 943 B_part2_fst B_part2_snd
theorem B_part3_val : B_part3 = (B_part3_fst, B_part3_snd) := by rfl

def B_final_3771 : ℕ × ℕ := A355898_loop 942 B_part3_fst B_part3_snd
def B_final : ℕ × ℕ := A355898_loop 943 B_part3_fst B_part3_snd

def B0 : ℕ := B_final.1 + 1
def B1 : ℕ := B_final.2 + 1
def A3772 : ℕ := B_final_3771.1

theorem B_final_eq : A355898_loop 3772 1 1 = B_final := by
  have h_split1 := A355898_loop_split 943 943 1 1
  have h_add1 : 943 + 943 = 1886 := by omega
  rw [h_add1] at h_split1
  rw [h_split1]
  change A355898_loop 943 B_part1.1 B_part1.2 = B_part2
  rw [B_part1_val]
  have h_split2 := A355898_loop_split 943 1886 1 1
  have h_add2 : 1886 + 943 = 2829 := by omega
  rw [h_add2] at h_split2
  rw [h_split2]
  change A355898_loop 943 (A355898_loop 1886 1 1).1 (A355898_loop 1886 1 1).2 = B_part3
  rw [h_split1]
  change A355898_loop 943 B_part2.1 B_part2.2 = B_part3
  rw [B_part2_val]
  have h_split3 := A355898_loop_split 943 2829 1 1
  have h_add3 : 2829 + 943 = 3772 := by omega
  rw [h_add3] at h_split3
  rw [h_split3]
  change A355898_loop 943 (A355898_loop 2829 1 1).1 (A355898_loop 2829 1 1).2 = B_final
  rw [h_split2]
  change A355898_loop 943 B_part3.1 B_part3.2 = B_final
  rw [B_part3_val]
  rfl

theorem B_final_3771_eq : A355898_loop 3771 1 1 = B_final_3771 := by
  have h_split1 := A355898_loop_split 943 943 1 1
  have h_add1 : 943 + 943 = 1886 := by omega
  rw [h_add1] at h_split1
  have h_split2 := A355898_loop_split 943 1886 1 1
  have h_add2 : 1886 + 943 = 2829 := by omega
  rw [h_add2] at h_split2
  have h_split3 := A355898_loop_split 942 2829 1 1
  have h_add3 : 2829 + 942 = 3771 := by omega
  rw [h_add3] at h_split3
  rw [h_split3]
  change A355898_loop 942 (A355898_loop 2829 1 1).1 (A355898_loop 2829 1 1).2 = B_final_3771
  rw [h_split2]
  change A355898_loop 942 B_part3.1 B_part3.2 = B_final_3771
  rw [B_part3_val]
  rfl

attribute [irreducible] B0 B1 A3772

def B : ℕ → ℕ
| 0 => B0
| 1 => B1
| k + 2 => B (k + 1) + B k

theorem base_gcd_0 : Nat.gcd (B 1 - 1) (B 0 - 1) = 1 := by
  unfold B B0 B1
  decide

theorem base_gcd_1 : Nat.gcd (B 1 - 1) (B 0) = 1 := by
  unfold B B0 B1
  decide

theorem base_gcd_2 : Nat.gcd (B 1) (B 0 - 1) = 1 := by
  unfold B B0 B1
  decide

theorem A3772_identity : A3772 + 1 = B 1 - B 0 := by
  unfold A3772 B B1 B0
  decide
