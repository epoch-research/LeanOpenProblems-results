import Submission.Basic

/-!
# Periodic lift of cyclic ternary codes

A binary low block and a complemented high block turn a cyclic code into a
return block.  The auxiliary odd period is chosen explicitly by division, so
the construction is independent of the CRT construction used elsewhere.
-/

namespace ErdosDSS

open scoped BigOperators

private def liftBinaryRow (t : ℕ) : Fin t → ℕ := fun i => 2 ^ i.val

private theorem liftBinaryBounds (t : ℕ) (e : Fin t → ℤ) (he : Ternary e) :
    -(2 ^ t : ℤ) + 1 ≤ signedSum (liftBinaryRow t) e ∧
      signedSum (liftBinaryRow t) e ≤ (2 ^ t : ℤ) - 1 := by
  induction t with
  | zero => simp [signedSum, liftBinaryRow]
  | succ t ih =>
    have he' : Ternary (fun i : Fin t => e i.castSucc) := fun i => he i.castSucc
    have hb := ih (fun i : Fin t => e i.castSucc) he'
    have hl := he (Fin.last t)
    have hp : 0 ≤ (2 ^ t : ℤ) := by positivity
    have hs : signedSum (liftBinaryRow (t + 1)) e =
        signedSum (liftBinaryRow t) (fun i => e i.castSucc) +
          e (Fin.last t) * (2 ^ t : ℤ) := by
      simp [signedSum, liftBinaryRow, Fin.sum_univ_castSucc]
    rw [hs, pow_succ]
    constructor <;> nlinarith

private theorem liftBinaryZero (t : ℕ) (e : Fin t → ℤ) (he : Ternary e)
    (hz : signedSum (liftBinaryRow t) e = 0) : e = 0 := by
  induction t with
  | zero => ext i; exact Fin.elim0 i
  | succ t ih =>
    have he' : Ternary (fun i : Fin t => e i.castSucc) := fun i => he i.castSucc
    have hb := liftBinaryBounds t (fun i => e i.castSucc) he'
    have hl := he (Fin.last t)
    have hp : 0 < (2 ^ t : ℤ) := by positivity
    have hs : signedSum (liftBinaryRow (t + 1)) e =
        signedSum (liftBinaryRow t) (fun i => e i.castSucc) +
          e (Fin.last t) * (2 ^ t : ℤ) := by
      simp [signedSum, liftBinaryRow, Fin.sum_univ_castSucc]
    have hlast : e (Fin.last t) = 0 := by
      rw [hs] at hz
      have hcases : e (Fin.last t) = -1 ∨ e (Fin.last t) = 0 ∨
          e (Fin.last t) = 1 := by omega
      rcases hcases with h | h | h
      · rw [h] at hz
        nlinarith [hb.2]
      · exact h
      · rw [h] at hz
        nlinarith [hb.1]
    have hz' : signedSum (liftBinaryRow t) (fun i => e i.castSucc) = 0 := by
      rw [hs, hlast] at hz
      simpa using hz
    have hzero := ih (fun i : Fin t => e i.castSucc) he' hz'
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hlast
    · exact congrFun hzero j

private def liftExponent (m P : ℕ) : ℕ := 35 * (m + 2 * P + 1)

private def liftMultiplier (m P : ℕ) : ℕ :=
  2 * P * ((2 ^ liftExponent m P + m) / (2 * P) + 1) + 1

private theorem liftPeriod (m P : ℕ) (hP : 0 < P) :
    0 < liftExponent m P ∧ Odd (liftMultiplier m P) ∧
      Nat.ModEq P (liftMultiplier m P) 1 ∧
      2 ^ liftExponent m P + m < liftMultiplier m P ∧
      35 * liftMultiplier m P ≤ 36 * 2 ^ liftExponent m P := by
  let t := liftExponent m P
  let L := 2 ^ t
  let C := 2 * P * ((L + m) / (2 * P) + 1) + 1
  have ht : 0 < t := by dsimp [t, liftExponent]; positivity
  have hL : 35 * (m + 2 * P + 1) ≤ L := by
    exact Nat.le_of_lt (Nat.lt_two_pow_self (n := t))
  have hden : 0 < 2 * P := by omega
  have hgap : L + m < C := by
    have h := Nat.lt_mul_div_succ (L + m) hden
    dsimp [C]
    omega
  have hupper : C ≤ L + m + 2 * P + 1 := by
    have h := Nat.mul_div_le (L + m) (2 * P)
    dsimp [C]
    nlinarith
  have heff : 35 * C ≤ 36 * L := by omega
  have hodd : Odd C := by
    apply odd_iff_exists_bit1.mpr
    refine ⟨P * ((L + m) / (2 * P) + 1), ?_⟩
    dsimp [C]
    ring
  have hmod : Nat.ModEq P C 1 := by
    simp [C, Nat.ModEq, Nat.mul_mod, Nat.add_mod]
  exact ⟨ht, hodd, hmod, hgap, heff⟩

private theorem liftSignedBounds {m B : ℕ} (b : Fin m → ℕ)
    (hb : ∀ i, b i ≤ B) (e : Fin m → ℤ) (he : Ternary e) :
    -(m : ℤ) * (B : ℤ) ≤ signedSum b e ∧
      signedSum b e ≤ (m : ℤ) * (B : ℤ) := by
  have hlow : ∀ i, -(B : ℤ) ≤ e i * (b i : ℤ) := by
    intro i
    have hbi : (b i : ℤ) ≤ (B : ℤ) := by exact_mod_cast hb i
    have hnonneg : 0 ≤ (b i : ℤ) := by positivity
    have hei := he i
    nlinarith
  have hhigh : ∀ i, e i * (b i : ℤ) ≤ (B : ℤ) := by
    intro i
    have hbi : (b i : ℤ) ≤ (B : ℤ) := by exact_mod_cast hb i
    have hnonneg : 0 ≤ (b i : ℤ) := by positivity
    have hei := he i
    nlinarith
  constructor
  · simpa [signedSum, mul_neg] using
      (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlow i))
  · simpa [signedSum] using
      (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hhigh i))

private def liftRow (t m B C : ℕ) (b : Fin m → ℕ) : Fin (t + m) → ℕ :=
  Fin.addCases (fun i : Fin t => B * 2 ^ i.val)
    (fun j : Fin m => B * C - b j)

private theorem liftRowSum (t m B C : ℕ) (b : Fin m → ℕ)
    (hb : ∀ j, b j ≤ B * C) (e : Fin (t + m) → ℤ) :
    signedSum (liftRow t m B C b) e =
      (B : ℤ) * signedSum (liftBinaryRow t) (fun i => e (Fin.castAdd m i)) +
        ((B : ℤ) * (C : ℤ)) * charge (fun j => e (Fin.natAdd t j)) -
          signedSum b (fun j => e (Fin.natAdd t j)) := by
  have hsub (j : Fin m) : ((B * C - b j : ℕ) : ℤ) =
      (B : ℤ) * (C : ℤ) - (b j : ℤ) := by
    rw [Int.natCast_sub (hb j), Nat.cast_mul]
  have hlowterm (i : Fin t) :
      e (Fin.castAdd m i) * ((B : ℤ) * (2 ^ i.val : ℤ)) =
        (B : ℤ) * (e (Fin.castAdd m i) * (2 ^ i.val : ℤ)) := by ring
  have hhighterm (j : Fin m) :
      e (Fin.natAdd t j) * ((B : ℤ) * (C : ℤ)) =
        ((B : ℤ) * (C : ℤ)) * e (Fin.natAdd t j) := by ring
  simp only [signedSum, liftRow, liftBinaryRow, charge]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  simp_rw [hsub, mul_sub, hlowterm, hhighterm]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

private theorem liftRowReturns {t m B C q : ℕ} (b : Fin m → ℕ)
    (hB : 0 < B) (hsmall : ∀ i, 0 < b i ∧ b i < B)
    (hgap : 2 ^ t + m < C)
    (hkernel : ∀ g : Fin m → ℤ, Ternary g → (B : ℤ) ∣ signedSum b g →
      g = 0 ∨ charge g = (q : ℤ) ∨ charge g = -(q : ℤ)) :
    ∀ e : Fin (t + m) → ℤ, Ternary e → ∀ k : ℤ,
      signedSum (liftRow t m B C b) e = k * ((B * C : ℕ) : ℤ) →
      (e = 0 ∧ k = 0) ∨ k = (q : ℤ) ∨ k = -(q : ℤ) := by
  intro e he k hreturn
  let f : Fin t → ℤ := fun i => e (Fin.castAdd m i)
  let g : Fin m → ℤ := fun j => e (Fin.natAdd t j)
  let s : ℤ := signedSum (liftBinaryRow t) f
  let d : ℤ := signedSum b g
  let c : ℤ := charge g
  have hf : Ternary f := fun i => he (Fin.castAdd m i)
  have hg : Ternary g := fun j => he (Fin.natAdd t j)
  have hBz : 0 < (B : ℤ) := by exact_mod_cast hB
  have hC : 0 < C := lt_of_le_of_lt (Nat.zero_le (2 ^ t + m)) hgap
  have hCz : 0 < (C : ℤ) := by exact_mod_cast hC
  have hbp : ∀ j, b j ≤ B * C := by
    intro j
    have hmul : B ≤ B * C := by
      simpa using Nat.mul_le_mul_left B (show 1 ≤ C by omega)
    exact (Nat.le_of_lt (hsmall j).2).trans hmul
  have hsplit := liftRowSum t m B C b hbp e
  change signedSum (liftRow t m B C b) e =
    (B : ℤ) * s + ((B : ℤ) * (C : ℤ)) * c - d at hsplit
  have hEq : (B : ℤ) * s + ((B : ℤ) * (C : ℤ)) * c - d =
      k * ((B : ℤ) * (C : ℤ)) := by
    rw [← hsplit]
    simpa only [Nat.cast_mul] using hreturn
  have hdvd : (B : ℤ) ∣ d := by
    refine ⟨s + (C : ℤ) * (c - k), ?_⟩
    nlinarith [hEq]
  obtain ⟨ell, hd⟩ := hdvd
  have hdbounds := liftSignedBounds b (fun j => Nat.le_of_lt (hsmall j).2) g hg
  change -(m : ℤ) * (B : ℤ) ≤ d ∧ d ≤ (m : ℤ) * (B : ℤ) at hdbounds
  have hell : -(m : ℤ) ≤ ell ∧ ell ≤ (m : ℤ) := by
    constructor
    · apply (Int.mul_le_mul_left hBz).mp
      nlinarith [hd, hdbounds.1]
    · apply (Int.mul_le_mul_left hBz).mp
      nlinarith [hd, hdbounds.2]
  have hs := liftBinaryBounds t f hf
  change -(2 ^ t : ℤ) + 1 ≤ s ∧ s ≤ (2 ^ t : ℤ) - 1 at hs
  have hgapz : (2 ^ t : ℤ) + (m : ℤ) < (C : ℤ) := by exact_mod_cast hgap
  have hcancel : s - ell = (C : ℤ) * (k - c) := by
    apply mul_left_cancel₀ (ne_of_gt hBz)
    nlinarith [hEq, hd]
  have hdiffbound : |s - ell| < (C : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hzero : s - ell = 0 :=
    Int.eq_zero_of_abs_lt_dvd ⟨k - c, hcancel⟩ hdiffbound
  have hkc : k = c := by
    have hprod : (C : ℤ) * (k - c) = 0 := hcancel.symm.trans hzero
    have hdiff : k - c = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hCz)
    omega
  rcases hkernel g hg ⟨ell, hd⟩ with hgzero | hplus | hminus
  · have hd0 : d = 0 := by simp [d, signedSum, hgzero]
    have hc0 : c = 0 := by simp [c, charge, hgzero]
    have hell0 : ell = 0 := by
      have hprod : (B : ℤ) * ell = 0 := hd.symm.trans hd0
      exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hBz)
    have hszero : s = 0 := by omega
    have hfzero : f = 0 := liftBinaryZero t f hf hszero
    left
    constructor
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · exact congrFun hfzero j
      · exact congrFun hgzero j
    · omega
  · exact Or.inr (Or.inl (hkc.trans hplus))
  · exact Or.inr (Or.inr (hkc.trans hminus))

/-- Lift a cyclic code to an odd-period return block.  Only positivity of the
external modulus is needed for the lift itself. -/
def CyclicCode.periodicLift {q P : ℕ} (code : CyclicCode q P) (hP : 0 < P) :
    ReturnBlock q P := by
  let t := liftExponent code.m P
  let C := liftMultiplier code.m P
  have hperiod := liftPeriod code.m P hP
  have hodd : Odd C := hperiod.2.1
  have hmod : Nat.ModEq P C 1 := hperiod.2.2.1
  have hgap : 2 ^ t + code.m < C := hperiod.2.2.2.1
  have heff : 35 * C ≤ 36 * 2 ^ t := hperiod.2.2.2.2
  have hC : 0 < C := lt_of_le_of_lt (Nat.zero_le (2 ^ t + code.m)) hgap
  have hBC : 0 < code.B * C := Nat.mul_pos code.B_pos hC
  refine {
    n := t + code.m
    p := code.B * C
    a := liftRow t code.m code.B C code.b
    q_pos := code.q_pos
    p_pos := hBC
    p_odd := code.B_odd.mul hodd
    small := ?_
    returns := liftRowReturns code.b code.B_pos code.small hgap code.kernel
    efficiency := ?_
    residue := ?_
  }
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [liftRow, Fin.addCases_left]
      have hpow : 0 < 2 ^ j.val := by positivity
      have hj : 2 ^ j.val < C := by
        have hlt : 2 ^ j.val < 2 ^ t := pow_lt_pow_right₀ (by omega) j.isLt
        omega
      exact ⟨Nat.mul_pos code.B_pos hpow, Nat.mul_lt_mul_of_pos_left hj code.B_pos⟩
    · simp only [liftRow, Fin.addCases_right]
      have hb := code.small j
      have hmul : code.B ≤ code.B * C := by
        simpa using Nat.mul_le_mul_left code.B (show 1 ≤ C by omega)
      constructor <;> omega
  · rw [pow_add]
    have h1 := Nat.mul_le_mul_right C code.efficiency
    have h2 := Nat.mul_le_mul_left (2 ^ code.m) heff
    nlinarith
  · simpa using code.residue.mul hmod

/-- An unbounded supply of cyclic codes gives an unbounded supply of return
blocks with the same prescribed charges and external residues. -/
theorem codeSupply_blockSupply (hs : CodeSupply) : BlockSupply := by
  intro P hP hodd K
  obtain ⟨q, hq, ⟨code⟩⟩ := hs P hP hodd K
  exact ⟨q, hq, ⟨code.periodicLift hP⟩⟩

end ErdosDSS
