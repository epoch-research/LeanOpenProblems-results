import Submission.PrimePowerCombFamily

/-! First non-stem digit, with an explicit finite depth bound. -/
namespace Erdos7PrimePowerFirstExit
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma first_exit (p E : ℕ) (hp : 2 ≤ p) (x : ℤ)
    (hE : ¬ (p : ℤ)^E ∣ x+1) :
    ∃ e c : ℕ, 0 < e ∧ e ≤ E ∧ 0 < c ∧ c < p ∧
      (p : ℤ)^e ∣ x - Erdos7PrimePowerCombFamily.exitValue p e c := by
  classical
  let H : ∃ e : ℕ, ¬ (p : ℤ)^e ∣ x+1 := ⟨E,hE⟩
  let e := Nat.find H
  have he : ¬ (p : ℤ)^e ∣ x+1 := Nat.find_spec H
  have heE : e ≤ E := Nat.find_min' H hE
  have he0 : 0 < e := by
    by_contra! hh
    have hz : e=0 := by omega
    simp [hz] at he
  have hlow : (p : ℤ)^(e-1) ∣ x+1 := by
    have hh := Nat.find_min H (show e-1 < e by omega)
    simpa using hh
  obtain ⟨y,hy⟩ := hlow
  have hep : e=(e-1)+1 := by omega
  have hpower : (p : ℤ)^e = (p : ℤ)^(e-1) * p := by
    conv_lhs => rw [hep,pow_succ]
  have hpy : ¬ (p : ℤ) ∣ y := by
    rintro ⟨k,hk⟩
    apply he
    refine ⟨k, ?_⟩
    rw [hy,hk,hpower]
    ring
  have hpz : (0 : ℤ)<p := by omega
  have hc0 : 0 ≤ y % (p : ℤ) := Int.emod_nonneg _ hpz.ne'
  have hcp : y % (p : ℤ) < p := Int.emod_lt_of_pos _ hpz
  have hcn : y % (p : ℤ) ≠ 0 := fun h => hpy (Int.dvd_of_emod_eq_zero h)
  let c := (y % (p : ℤ)).toNat
  have hc : (c : ℤ) = y % (p : ℤ) := Int.natCast_toNat_eq_self.mpr hc0
  refine ⟨e,c,he0,heE,?_,?_,?_⟩
  · have : (0 : ℤ)<c := by rw [hc]; omega
    exact_mod_cast this
  · exact_mod_cast (show (c : ℤ)<p by rw [hc]; exact hcp)
  · refine ⟨y / (p : ℤ), ?_⟩
    dsimp [Erdos7PrimePowerCombFamily.exitValue]
    rw [hc,Int.emod_def]
    rw [hpower]
    nlinarith [hy]

#print axioms first_exit
end Erdos7PrimePowerFirstExit
