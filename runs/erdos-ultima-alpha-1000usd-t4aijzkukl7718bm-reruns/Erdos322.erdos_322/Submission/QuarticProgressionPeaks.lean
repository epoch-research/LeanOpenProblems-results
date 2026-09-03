import Submission.QuarticFiberCRT
import Submission.LocalCRTConcentration
import Submission.PolynomialPeakCriterion

/-! Unbounded exact quartic counts in every represented congruence class.
The counts asserted here are not positive powers of the targets. -/
namespace Erdos322Research.QuarticProgressionPeaks
noncomputable section
open Finset QuarticFiberBasic QuarticFiberCRT LocalPeakCounting LocalCRTConcentration
open PolynomialPeakCriterion
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

lemma fiberCount_congr_target {q a b : ℕ} (h : a ≡ b [MOD q]) :
    fiberCount q a=fiberCount q b := by
  unfold fiberCount
  apply Fintype.card_congr
  exact Equiv.subtypeEquivProp (funext fun x ↦ propext ⟨fun hx ↦ hx.trans h,fun hx ↦ hx.trans h.symm⟩)

lemma fiberCount_zero (q : ℕ) : fiberCount q 0=rootCount 4 q := by
  simp only [fiberCount,rootCount,Fiber,Roots,Nat.modEq_zero_iff_dvd]

/-- Critical normalized density remains unbounded while avoiding an arbitrary
prescribed set of prime factors. -/
lemma exists_large_root_density_avoiding (B C : ℕ) (hB : 0 < B) :
    ∃ q : ℕ, 0 < q ∧ q.Coprime B ∧ C*q^3 < rootCount 4 q := by
  obtain ⟨p,hp,hpk,hpB,a,ha,hseed⟩ := good_prime_avoiding 4 B (by decide) hB
  letI : Fact p.Prime := ⟨hp⟩
  let d := C*p^3
  let q := p^(4*d+1)
  have hq : 0 < q := pow_pos hp.pos _
  have hg := rootCount_growth p 2 hpk a ha hseed d
  refine ⟨q,hq,hpB.pow_left _,?_⟩
  calc
    C*q^3 = d*p^(4*d*3) := by
      dsimp only [q,d]
      rw [← pow_mul,show (4*(C*p^3)+1)*3=3+4*(C*p^3)*3 by ring,pow_add]
      ring
    _ < (d+1)*p^(4*d*3) := Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos hp.pos _)
    _ ≤ rootCount 4 q := hg

private lemma tuple_sum_bound (q : ℕ) (x : Fin 4 → Fin q) :
    ∑ i, (x i : ℕ)^4 ≤ q*(4*q^3) := by
  calc
    ∑ i, (x i : ℕ)^4 ≤ ∑ _i : Fin 4, q^4 :=
      sum_le_sum fun i _ ↦ Nat.pow_le_pow_left (x i).isLt.le 4
    _ = q*(4*q^3) := by simp; ring

private def quotientTarget (q u : ℕ) (hq : 0 < q) (x : Fiber q u) :
    Fin (4*q^3+1) :=
  ⟨(∑ i, (x.val i : ℕ)^4)/q,by
    have hh := Nat.div_le_div_right (c := q) (tuple_sum_bound q x.val)
    rw [Nat.mul_div_cancel_left _ hq] at hh
    omega⟩

private lemma quotientTarget_sum (q u : ℕ) (hq : 0 < q) (x : Fiber q u) :
    ∑ i, (x.val i : ℕ)^4=u%q+q*(quotientTarget q u hq x : ℕ) := by
  have hh := Nat.mod_add_div (∑ i, (x.val i : ℕ)^4) q
  have hr : (∑ i, (x.val i : ℕ)^4)%q=u%q := x.property
  rw [hr] at hh
  exact hh.symm

/-- Exact pigeonhole extraction for an arbitrary modular fiber. -/
theorem peak_of_fiberCount (q u M : ℕ) (hq : 0 < q)
    (hsize : (4*q^3+1)*M < fiberCount q u) :
    ∃ n : ℕ, n ≡ u [MOD q] ∧ M < Erdos322.representationCount 4 n := by
  have hfsize : Fintype.card (Fin (4*q^3+1))*M < Fintype.card (Fiber q u) := by
    simpa only [fiberCount,Fintype.card_fin] using hsize
  obtain ⟨y,hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (quotientTarget q u hq) hfsize
  let T := {x : Fiber q u // quotientTarget q u hq x=y}
  let E : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  let v : Fin (Fintype.card T) → Fin 4 → ℕ := fun a i ↦ ((E a).val.val i : ℕ)
  have hs (a : Fin (Fintype.card T)) : ∑ i, v a i^4=u%q+q*(y : ℕ) := by
    change ∑ i, ((E a).val.val i : ℕ)^4=_
    rw [quotientTarget_sum q u hq (E a).val,(E a).property]
  have hi : Function.Injective v := by
    intro a b h
    apply E.injective
    apply Subtype.ext
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrFun h i
  have hb := count_lower_of_injective (by decide : 0 < 4) v hs hi
  have hy' : M < Fintype.card T := by simpa only [T,Fintype.card_subtype] using hy
  refine ⟨u%q+q*(y : ℕ),?_,hy'.trans_le hb⟩
  change (u%q+q*(y : ℕ))%q=u%q
  simp only [Nat.add_mul_mod_self_left,Nat.mod_mod]

/-- Any congruence class represented modulo B contains targets with
arbitrarily large FULL exact counts. No prescribed coordinate is fixed. -/
theorem count_unbounded_in_represented_progression (B r M : ℕ) (hB : 0 < B)
    (hr : 0 < fiberCount B r) :
    ∃ n : ℕ, n ≡ r [MOD B] ∧ M < Erdos322.representationCount 4 n := by
  obtain ⟨q,hq,hcop,hlarge⟩ := exists_large_root_density_avoiding B ((4*B^3+1)*M) hB
  obtain ⟨u,huB,huq⟩ := Nat.chineseRemainder hcop.symm r 0
  have hlocal : fiberCount B u=fiberCount B r := fiberCount_congr_target huB
  have hroot : fiberCount q u=rootCount 4 q := (fiberCount_congr_target huq).trans (fiberCount_zero q)
  have hf : rootCount 4 q ≤ fiberCount (B*q) u := by
    rw [fiberCount_mul B q u hB hq hcop.symm,hlocal,hroot]
    have h1 : 1 ≤ fiberCount B r := hr
    simpa only [one_mul] using Nat.mul_le_mul_right (rootCount 4 q) h1
  have hpow : 1 ≤ q^3 := one_le_pow₀ (by omega)
  have hsize : (4*(B*q)^3+1)*M < fiberCount (B*q) u := by
    apply lt_of_le_of_lt _ (hlarge.trans_le hf)
    rw [mul_pow]
    nlinarith [Nat.mul_le_mul_left M hpow]
  obtain ⟨n,hn,hcount⟩ := peak_of_fiberCount (B*q) u M (Nat.mul_pos hB hq) hsize
  exact ⟨n,(hn.of_dvd (dvd_mul_right B q)).trans huB,hcount⟩

/-- The high-count targets in each such progression are infinite, not merely
nonempty. The multiplicity threshold here is fixed, not a power of n. -/
theorem infinitely_many_large_counts_in_progression (B r M : ℕ) (hB : 0 < B)
    (hr : 0 < fiberCount B r) :
    {n : ℕ | n ≡ r [MOD B] ∧ M < Erdos322.representationCount 4 n}.Infinite := by
  by_contra hh
  have hf : {n : ℕ | n ≡ r [MOD B] ∧ M < Erdos322.representationCount 4 n}.Finite :=
    Set.not_infinite.mp hh
  let T := hf.toFinset
  obtain ⟨n,hn,hcount⟩ := count_unbounded_in_represented_progression B r
    (max M (T.sup (Erdos322.representationCount 4))) hB hr
  have hm : M < Erdos322.representationCount 4 n := (le_max_left _ _).trans_lt hcount
  have hmem : n ∈ T := hf.mem_toFinset.mpr ⟨hn,hm⟩
  have hb : Erdos322.representationCount 4 n ≤ T.sup (Erdos322.representationCount 4) :=
    Finset.le_sup (f := Erdos322.representationCount 4) hmem
  have hmax := le_max_right M (T.sup (Erdos322.representationCount 4))
  omega

end
end Erdos322Research.QuarticProgressionPeaks
