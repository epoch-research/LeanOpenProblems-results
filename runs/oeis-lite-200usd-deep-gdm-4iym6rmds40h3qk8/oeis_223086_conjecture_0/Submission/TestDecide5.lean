import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 10000000

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

lemma step1 : A006368_map^[100] 64 = 11574 := by decide
lemma step2 : A006368_map^[100] 11574 = 2089746 := by decide
lemma step3 : A006368_map^[100] 2089746 = 47162797 := by decide
lemma step4 : A006368_map^[100] 47162797 = 139513299931002 := by decide
lemma step5 : A006368_map^[100] 139513299931002 = 100756188284683804 := by decide
lemma step6 : A006368_map^[100] 100756188284683804 = 4657016978965305652129 := by decide
lemma step7 : A006368_map^[100] 4657016978965305652129 = 105102721346651848180727 := by decide
lemma step8 : A006368_map^[100] 105102721346651848180727 = 607239572799050767489311236 := by decide
lemma step9 : A006368_map^[100] 607239572799050767489311236 = 219273520019636635525971950843 := by decide
lemma step10 : A006368_map^[100] 219273520019636635525971950843 = 9897427377833507869287616648508 := by decide

lemma iterate_1000_eq : A006368_map^[1000] 64 = 9897427377833507869287616648508 := by
  have h1 : A006368_map^[100] 64 = 11574 := step1
  have h2 : A006368_map^[200] 64 = 2089746 := by
    rw [show 200 = 100 + 100 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h1, step2]
  have h3 : A006368_map^[300] 64 = 47162797 := by
    rw [show 300 = 100 + 200 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h2, step3]
  have h4 : A006368_map^[400] 64 = 139513299931002 := by
    rw [show 400 = 100 + 300 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h3, step4]
  have h5 : A006368_map^[500] 64 = 100756188284683804 := by
    rw [show 500 = 100 + 400 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h4, step5]
  have h6 : A006368_map^[600] 64 = 4657016978965305652129 := by
    rw [show 600 = 100 + 500 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h5, step6]
  have h7 : A006368_map^[700] 64 = 105102721346651848180727 := by
    rw [show 700 = 100 + 600 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h6, step7]
  have h8 : A006368_map^[800] 64 = 607239572799050767489311236 := by
    rw [show 800 = 100 + 700 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h7, step8]
  have h9 : A006368_map^[900] 64 = 219273520019636635525971950843 := by
    rw [show 900 = 100 + 800 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h8, step9]
  rw [show 1000 = 100 + 900 by omega, Function.iterate_add]
  dsimp only [Function.comp_apply]
  rw [h9, step10]
