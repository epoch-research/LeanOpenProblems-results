import Submission.LocalSeedDensity

/-! Upper bounds for nonsingular prime-power congruence fibers. These do not
bound the number of exact representations of a fixed integer. -/
namespace Erdos322Research.LocalRootUpperBasic
noncomputable section
open Finset LocalPowerRoots LocalPeakCounting LocalSeedDensity
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

lemma finite_fiber_bound {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) (C : ℕ) (h : ∀ b, Fintype.card {a : A // f a=b} ≤ C) :
    Fintype.card A ≤ Fintype.card B*C := by
  calc
    Fintype.card A = ∑ b : B, Fintype.card {a : A // f a=b} := by
      rw [← Fintype.card_sigma]
      exact (Fintype.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ ≤ ∑ _b : B, C := Finset.sum_le_sum (fun b _ ↦ h b)
    _ = _ := by simp

lemma field_power_fiber_bound (p k : ℕ) [Fact p.Prime] (hk : 0 < k)
    (a : ZMod p) : Fintype.card {x : ZMod p // x^k=a} ≤ k := by
  let S := (Polynomial.nthRoots k a).toFinset
  let f : {x : ZMod p // x^k=a} → S := fun x ↦
    ⟨x.val,by simpa only [S,Multiset.mem_toFinset,Polynomial.mem_nthRoots hk] using x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hh := congrArg (fun z : S ↦ z.val) h
    exact hh
  calc
    Fintype.card {x : ZMod p // x^k=a} ≤ Fintype.card S := Fintype.card_le_of_injective f hf
    _ = S.card := Fintype.card_coe _
    _ ≤ (Polynomial.nthRoots k a).card := Multiset.toFinset_card_le _
    _ ≤ k := Polynomial.card_nthRoots _ _

/-- At a prime not dividing the exponent, at most k nonsingular roots of
one power equation exist modulo any prime power. -/
theorem unit_power_fiber_bound (p e k : ℕ) [Fact p.Prime] (hk : ¬p ∣ k)
    (v : ZMod (p^(e+1))) :
    Fintype.card {x : ZMod (p^(e+1)) // x^k=v ∧ reduction p e x ≠ 0} ≤ k := by
  have hkpos : 0 < k := Nat.pos_of_ne_zero (fun h ↦ hk (h ▸ dvd_zero p))
  let f : {x : ZMod (p^(e+1)) // x^k=v ∧ reduction p e x ≠ 0} →
      {a : ZMod p // a^k=reduction p e v} := fun x ↦
    ⟨reduction p e x.val,by simpa only [map_pow] using congrArg (reduction p e) x.property.1⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have he := congrArg Subtype.val h
    exact pow_injective_on_residue p e k hk (reduction p e x.val) x.property.2
      x.val y.val rfl he.symm (x.property.1.trans y.property.1.symm)
  exact (Fintype.card_le_of_injective f hf).trans (field_power_fiber_bound p k hkpos _)

abbrev FirstRoots (k p e : ℕ) :=
  {x : Roots (k+2) (p^(e+1)) // ¬p ∣ (x.val 0 : ℕ)}

/-- The nonsingular first-coordinate part of the critical k-variable fiber
has size at most k times the (k-1)-dimensional box volume. -/
theorem first_roots_upper (k p e : ℕ) [Fact p.Prime] (hk : ¬p ∣ k+2) :
    Fintype.card (FirstRoots k p e) ≤ (k+2)*(p^(e+1))^(k+1) := by
  classical
  let q := p^(e+1)
  let tail : FirstRoots k p e → (Fin (k+1) → Fin q) := fun x j ↦ x.val.val j.succ
  have hf (t : Fin (k+1) → Fin q) :
      Fintype.card {x : FirstRoots k p e // tail x=t} ≤ k+2 := by
    let v : ZMod q := -∑ j, ((t j : ℕ) : ZMod q)^(k+2)
    let f : {x : FirstRoots k p e // tail x=t} →
        {a : ZMod q // a^(k+2)=v ∧ reduction p e a ≠ 0} := fun x ↦
      ⟨(x.val.val.val 0 : ℕ),by
        constructor
        · have hh : (∑ i, ((x.val.val.val i : ℕ) : ZMod q)^(k+2))=0 := by
            have hcast := (ZMod.natCast_eq_zero_iff _ q).mpr x.val.val.property
            push_cast at hcast
            exact hcast
          rw [Fin.sum_univ_succ] at hh
          have ht (j : Fin (k+1)) : x.val.val.val j.succ=t j := congrFun x.property j
          simp only [ht] at hh
          dsimp only [v]
          linear_combination hh
        · rw [reduction_natCast]
          exact (ZMod.natCast_eq_zero_iff _ _).not.mpr x.val.property⟩
    have hinj : Function.Injective f := by
      intro x y h
      have h0 := congrArg Subtype.val h
      have h0' : x.val.val.val 0=y.val.val.val 0 := by
        apply Fin.ext
        have hv := congrArg ZMod.val h0
        simpa only [f,ZMod.val_natCast_of_lt (x.val.val.val 0).isLt,
          ZMod.val_natCast_of_lt (y.val.val.val 0).isLt] using hv
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      funext i
      refine Fin.cases h0' (fun j ↦ ?_) i
      exact (congrFun x.property j).trans (congrFun y.property j).symm
    exact (Fintype.card_le_of_injective f hinj).trans (unit_power_fiber_bound p e (k+2) hk v)
  have hh := finite_fiber_bound tail (k+2) hf
  simpa only [Fintype.card_fun,Fintype.card_fin,mul_comm] using hh

end
end Erdos322Research.LocalRootUpperBasic
