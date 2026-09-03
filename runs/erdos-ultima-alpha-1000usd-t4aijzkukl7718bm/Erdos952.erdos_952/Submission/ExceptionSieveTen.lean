import Submission.ComponentTen
import Submission.ExceptionSieveDecision

/-! A concrete rejecting exception-retaining cutoff for jump bounds at most ten. -/
namespace Erdos952Investigation.ExceptionSieveTen
open FiniteSieveReduction ExceptionSieveReduction ExceptionSieveDecision
set_option maxHeartbeats 0

lemma candidate_not_blocked {z : GaussianInt} (hz : Candidate 89 z) : ¬ blocked10 z := by
  intro hblock
  rcases hz with hp | ⟨hlarge,ha⟩
  · exact prime_not_blocked10 hp hblock
  rcases hblock with hsmall | ⟨a,hamem,ha1,haz,har,hai⟩
  · norm_num at hlarge
    omega
  have hbound : ∀ b ∈ smallDivisors10, b.norm ≤ 89 := by
    have hh : smallDivisors10.all (fun b => decide (b.norm ≤ 89)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using hh
  have had := gaussian_divisor_of_congruences a z (by omega)
    (Int.dvd_of_emod_eq_zero har) (Int.dvd_of_emod_eq_zero hai)
  have hd : a.norm ∣ z.norm := map_dvd (Zsqrtd.normMonoidHom (d := -1)) had
  have habs : (a.norm.natAbs : ℤ) = a.norm := Int.natAbs_of_nonneg (GaussianInt.norm_nonneg _)
  have hne : a.norm.natAbs ≠ 1 := by intro he; rw [he] at habs; omega
  obtain ⟨p,hp,hpa⟩ := Nat.exists_prime_and_dvd hne
  have hpn : p ≤ 89 := by
    have hpos : 0 < a.norm.natAbs := Int.natAbs_pos.mpr (by omega)
    have hh := Nat.le_of_dvd hpos hpa
    have haa := hbound a hamem
    omega
  apply ha p hpn hp
  have hdiv : (p : ℤ) ∣ a.norm := by
    have hh := Int.natCast_dvd.mpr hpa
    exact hh
  exact hdiv.trans hd

lemma candidate_fold {N : ℕ} {z : GaussianInt} (hz : Candidate N z) :
    Candidate N (OctantReduction.fold z) := by
  rcases hz with hp | ⟨hlarge,ha⟩
  · exact Or.inl (OctantReduction.prime_fold hp)
  · exact Or.inr ⟨by simpa only [OctantReduction.norm_fold] using hlarge,
      fun p hpN hp hd => ha p hpN hp (by simpa only [OctantReduction.norm_fold] using hd)⟩

lemma octant_closed_not_blocked {z w : GaussianInt} (hz : InOctantComponent10 z)
    (hw : ¬ blocked10 w) (hd : (w-z).norm < 10) (hwO : OctantReduction.InOctant w) :
    InOctantComponent10 w := by
  have hd' : (w.re-z.re)^2+(w.im-z.im)^2 < 10 := by
    simpa only [gaussian_norm_sq,Zsqrtd.re_sub,Zsqrtd.im_sub] using hd
  have hdr : -3 ≤ w.re-z.re ∧ w.re-z.re ≤ 3 := by
    constructor <;> nlinarith [sq_nonneg (w.im-z.im)]
  have hdi : -3 ≤ w.im-z.im ∧ w.im-z.im ≤ 3 := by
    constructor <;> nlinarith [sq_nonneg (w.re-z.re)]
  have hi0 := hz.1
  have hir := hz.2.1
  have hr1 := hz.2.2.1
  let r : Fin 85 := ⟨z.re.toNat,by omega⟩
  let s : Fin 85 := ⟨z.im.toNat,by omega⟩
  let a : Fin 7 := ⟨(w.re-z.re+3).toNat,by omega⟩
  let b : Fin 7 := ⟨(w.im-z.im+3).toNat,by omega⟩
  have hr : (r : ℤ) = z.re := by dsimp [r]; omega
  have hs : (s : ℤ) = z.im := by dsimp [s]; omega
  have ha : (a : ℤ)-3 = w.re-z.re := by dsimp [a]; omega
  have hb : (b : ℤ)-3 = w.im-z.im := by dsimp [b]; omega
  have hrow := component_rows10 r s
  dsimp only at hrow
  rw [hr,hs] at hrow
  have hstep := hrow hz a b
  rw [ha,hb] at hstep
  have heq : (⟨z.re+(w.re-z.re),z.im+(w.im-z.im)⟩ : GaussianInt) = w := by
    ext <;> simp
  have hrow' : InOctantComponent10 w ∨ blocked10 w := by
    simpa only [heq] using hstep hd' (by simpa only [heq] using hwO)
  exact hrow'.resolve_right hw

lemma candidate_component_closed {C : ℤ} (hC : C ≤ 10) {z w : GaussianInt}
    (hz : InComponent10 z) (hw : (candidateGraph C 89).Adj z w) : InComponent10 w :=
  octant_closed_not_blocked hz (candidate_not_blocked (candidate_fold hw.2.1))
    ((OctantReduction.fold_contract _ _).trans_lt (hw.2.2.2.trans_le hC))
    (OctantReduction.fold_in_octant _)

theorem cutoff_component_finite (C : ℤ) (hC : C ≤ 10) :
    {w | (candidateGraph C 89).Reachable (3 : GaussianInt) w}.Finite := by
  apply inComponent10_finite.subset
  have hwalk : ∀ {z w : GaussianInt}, (candidateGraph C 89).Walk z w →
      InComponent10 z → InComponent10 w := by
    intro z w p
    induction p with
    | nil => exact id
    | cons h p ih => exact fun hz => ih (candidate_component_closed hC hz h)
  intro w hw
  exact hw.elim fun p => hwalk p three_inComponent10

theorem cutoffTest_false_le_ten (C : ℤ) (hC : C ≤ 10) : cutoffTest C 89 = false :=
  (cutoffTest_false_iff C 89).mpr (cutoff_component_finite C hC)

#print axioms cutoffTest_false_le_ten
end Erdos952Investigation.ExceptionSieveTen
