import FormalConjecturesUtil

/-!
A restriction on a particular affine boundary-repair ansatz, not a disproof
of Erdős 773. The explicit lists below describe the missing slope labels
in the radius-12, h=8k-1 exploratory encoding. No completeness claim about
that encoding or about the factorial carrier is made here.
-/
namespace Erdos773.AffineSlopeRepairObstruction

/-- Paired coefficient rows preserve the output slope modulo six when their
carry difference is divisible by six. This is an integer identity. -/
theorem paired_slope_congruence {x z u v w cx cz L : ℤ}
    (hx : x = u + 12*v - 3*w - L*cx)
    (hz : z = u + 12*v + 3*w - L*cz)
    (hc : 6 ∣ cz-cx) : 6 ∣ x-z := by
  have h1 : (6 : ℤ) ∣ -6*w := by simp
  have h2 : (6 : ℤ) ∣ L*(cz-cx) := dvd_mul_of_dvd_right hc L
  convert dvd_add h1 h2 using 1
  rw [hx,hz]
  ring

/-- The constant-coefficient carry rows propagate this divisibility from
column zero. No boundedness assumption or solver result is used. -/
theorem carry_difference_mod_six (x z u v w cx cz : ℕ → ℤ)
    (hx : ∀ i, 6*x i = u i + 12*v i - 3*w i + cx i-cx (i+1))
    (hz : ∀ i, 6*z i = u i + 12*v i + 3*w i + cz i-cz (i+1))
    (hzero : 6 ∣ cz 0-cx 0) : ∀ i, 6 ∣ cz i-cx i := by
  intro i
  induction i with
  | zero => exact hzero
  | succ i ih =>
    have he : cz (i+1)-cx (i+1) = cz i-cx i+6*(w i+x i-z i) := by
      linear_combination hz i - hx i
    rw [he]
    exact dvd_add ih (dvd_mul_right 6 _)


def xTarget : List ℤ :=
  List.replicate 6 0 ++ List.replicate 29 1 ++ List.replicate 29 2 ++
    List.replicate 29 7 ++ List.replicate 22 8

def zTarget : List ℤ :=
  List.replicate 29 1 ++ List.replicate 29 2 ++
    List.replicate 29 7 ++ List.replicate 28 8

lemma target_lengths : xTarget.length = 115 ∧ zTarget.length = 115 := by
  norm_num [xTarget,zTarget]

/-- These two particular target multisets cannot be matched pointwise by
slopes congruent modulo six. This result does not rely on a solver. -/
theorem targets_incompatible (x z : Fin 115 → ℤ)
    (hx : (List.ofFn x).Perm xTarget)
    (hz : (List.ofFn z).Perm zTarget)
    (hc : ∀ i, 6 ∣ x i-z i) : False := by
  have hzero : (0 : ℤ) ∈ xTarget := by simp [xTarget]
  have hzero' : (0 : ℤ) ∈ List.ofFn x := hx.mem_iff.mpr hzero
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hzero'
  have hzi : z i ∈ zTarget := hz.mem_iff.mp (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have hd := hc i
  rw [hi] at hd
  have hcases : z i = 1 ∨ z i = 2 ∨ z i = 7 ∨ z i = 8 := by
    simpa [zTarget] using hzi
  rcases hcases with h | h | h | h <;> rw [h] at hd <;> norm_num at hd

/-- A precise finite obstruction to the displayed slope-repair system.
The coefficient rows and the carry condition are explicit hypotheses. -/
theorem no_target_repair (x z u v w cx cz : Fin 115 → ℤ)
    (hx : (List.ofFn x).Perm xTarget)
    (hz : (List.ofFn z).Perm zTarget)
    (hrx : ∀ i, x i = u i + 12*v i - 3*w i - 8*cx i)
    (hrz : ∀ i, z i = u i + 12*v i + 3*w i - 8*cz i)
    (hc : ∀ i, 6 ∣ cz i-cx i) : False := by
  apply targets_incompatible x z hx hz
  intro i
  exact paired_slope_congruence (hrx i) (hrz i) (hc i)

end Erdos773.AffineSlopeRepairObstruction

#print axioms Erdos773.AffineSlopeRepairObstruction.paired_slope_congruence
#print axioms Erdos773.AffineSlopeRepairObstruction.targets_incompatible
#print axioms Erdos773.AffineSlopeRepairObstruction.no_target_repair

#print axioms Erdos773.AffineSlopeRepairObstruction.carry_difference_mod_six