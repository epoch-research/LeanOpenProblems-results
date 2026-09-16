import Submission.DC

set_option exponentiation.threshold 2000
set_option maxRecDepth 200000

def dc_exact (fuel a b : ℕ) : ℤ × ℤ :=
  match fuel with
  | 0 => (1, 0)
  | fuel' + 1 =>
    if a + 1 = b then
      let k : ℤ := a + 1
      let X := k
      let Z : ℤ := if (a + 1) % 2 == 0 then 1 else -1
      (X, Z)
    else if a + 1 < b then
      let mid := (a + b) / 2
      let (X1, Z1) := dc_exact fuel' a mid
      let (X2, Z2) := dc_exact fuel' mid b
      let X := (X2 * X1)
      let Z := (X2 * Z1 + Z2 * X1)
      (X, Z)
    else
      (1, 0)

lemma dc_exact_mod (fuel a b : ℕ) :
  ((dc_exact fuel a b).1 % P, (dc_exact fuel a b).2 % P) = dc_mod fuel a b := by
  induction fuel generalizing a b
  case zero => rfl
  case succ fuel' ih =>
    unfold dc_exact dc_mod
    split_ifs with h1 h2
    · dsimp; rfl
    · dsimp
      have ih1 := ih a ((a + b) / 2)
      have ih2 := ih ((a + b) / 2) b
      have hx1 : (dc_exact fuel' a ((a + b) / 2)).1 % P = (dc_mod fuel' a ((a + b) / 2)).1 := congrArg Prod.fst ih1
      have hz1 : (dc_exact fuel' a ((a + b) / 2)).2 % P = (dc_mod fuel' a ((a + b) / 2)).2 := congrArg Prod.snd ih1
      have hx2 : (dc_exact fuel' ((a + b) / 2) b).1 % P = (dc_mod fuel' ((a + b) / 2) b).1 := congrArg Prod.fst ih2
      have hz2 : (dc_exact fuel' ((a + b) / 2) b).2 % P = (dc_mod fuel' ((a + b) / 2) b).2 := congrArg Prod.snd ih2
      have eq1 : ((dc_exact fuel' ((a + b) / 2) b).1 * (dc_exact fuel' a ((a + b) / 2)).1) % P = ((dc_mod fuel' ((a + b) / 2) b).1 * (dc_mod fuel' a ((a + b) / 2)).1) % P := by
        rw [Int.mul_emod, hx2, hx1, ← Int.mul_emod]
      have eq2 : ((dc_exact fuel' ((a + b) / 2) b).1 * (dc_exact fuel' a ((a + b) / 2)).2 + (dc_exact fuel' ((a + b) / 2) b).2 * (dc_exact fuel' a ((a + b) / 2)).1) % P = ((dc_mod fuel' ((a + b) / 2) b).1 * (dc_mod fuel' a ((a + b) / 2)).2 + (dc_mod fuel' ((a + b) / 2) b).2 * (dc_mod fuel' a ((a + b) / 2)).1) % P := by
        rw [Int.add_emod]
        have t1 : ((dc_exact fuel' ((a + b) / 2) b).1 * (dc_exact fuel' a ((a + b) / 2)).2) % P = ((dc_mod fuel' ((a + b) / 2) b).1 * (dc_mod fuel' a ((a + b) / 2)).2) % P := by
          rw [Int.mul_emod, hx2, hz1, ← Int.mul_emod]
        have t2 : ((dc_exact fuel' ((a + b) / 2) b).2 * (dc_exact fuel' a ((a + b) / 2)).1) % P = ((dc_mod fuel' ((a + b) / 2) b).2 * (dc_mod fuel' a ((a + b) / 2)).1) % P := by
          rw [Int.mul_emod, hz2, hx1, ← Int.mul_emod]
        rw [t1, t2, ← Int.add_emod]
      ext
      · exact eq1
      · exact eq2
    · rfl
