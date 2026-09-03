import Submission.UnitFourthCongruence

/-! Uniform primitive bounds for arbitrary quartic congruence targets. -/
namespace Erdos322Research.QuarticFiberBasic
noncomputable section
open Finset LocalPowerRoots LocalRootUpperBasic UnitFourthCongruence
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

abbrev Fiber (q n : ℕ) := {x : Fin 4 → Fin q // (∑ i, (x i : ℕ)^4) ≡ n [MOD q]}
def fiberCount (q n : ℕ) : ℕ := Fintype.card (Fiber q n)
abbrev FirstFiber (p e n : ℕ) := {x : Fiber (p^(e+1)) n // ¬p ∣ (x.val 0 : ℕ)}
abbrev DivFiber (p q n : ℕ) := {x : Fiber q n // ∀ i, p ∣ (x.val i : ℕ)}

/-- A unit first coordinate leaves only a divisor-bounded number of choices. -/
theorem first_fiber_upper (p e n : ℕ) [Fact p.Prime] :
    Fintype.card (FirstFiber p e n) ≤ 4*(p^(e+1)).divisors.card^2*(p^(e+1))^3 := by
  classical
  let q := p^(e+1)
  let tail : FirstFiber p e n → (Fin 3 → Fin q) := fun x j ↦ x.val.val j.succ
  have hf (t : Fin 3 → Fin q) : Fintype.card {x : FirstFiber p e n // tail x=t} ≤
      4*q.divisors.card^2 := by
    let v : ZMod q := (n : ZMod q)-∑ j, ((t j : ℕ) : ZMod q)^4
    let f : {x : FirstFiber p e n // tail x=t} →
        {a : ZMod q // a^4=v ∧ IsUnit a} := fun x ↦
      ⟨(x.val.val.val 0 : ℕ),by
        constructor
        · have hh : (∑ i, ((x.val.val.val i : ℕ) : ZMod q)^4)=(n : ZMod q) := by
            have hcast := (ZMod.natCast_eq_natCast_iff _ _ q).mpr x.val.val.property
            push_cast at hcast
            exact hcast
          rw [Fin.sum_univ_succ] at hh
          have ht (j : Fin 3) : x.val.val.val j.succ=t j := congrFun x.property j
          simp only [ht] at hh
          dsimp only [v]
          linear_combination hh
        · exact (ZMod.isUnit_iff_coprime _ _).mpr
            ((Fact.out : p.Prime).coprime_pow_of_not_dvd x.val.property)⟩
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
    exact (Fintype.card_le_of_injective f hinj).trans
      (unit_fourth_fiber q (pow_pos (Fact.out : p.Prime).pos _) v)
  have hh := finite_fiber_bound tail (4*q.divisors.card^2) hf
  simpa only [Fintype.card_fun,Fintype.card_fin,mul_comm] using hh

/-- Cover by the all-divisible part and four possible unit coordinates. -/
theorem fiber_cover_upper (p e n : ℕ) [Fact p.Prime] :
    fiberCount (p^(e+1)) n ≤ Fintype.card (DivFiber p (p^(e+1)) n)+
      16*(p^(e+1)).divisors.card^2*(p^(e+1))^3 := by
  classical
  let A := DivFiber p (p^(e+1)) n ⊕ (Fin 4 × FirstFiber p e n)
  let f : A → Fiber (p^(e+1)) n := fun z ↦ match z with
    | .inl x => x.val
    | .inr (i,x) => ⟨fun j ↦ x.val.val (Equiv.swap 0 i j),by
      rw [Equiv.sum_comp (Equiv.swap 0 i) (fun j ↦ (x.val.val j : ℕ)^4)]
      exact x.val.property⟩
  have hf : Function.Surjective f := by
    intro x
    by_cases hd : ∀ i, p ∣ (x.val i : ℕ)
    · exact ⟨.inl ⟨x,hd⟩,rfl⟩
    · push_neg at hd
      obtain ⟨i,hi⟩ := hd
      let y : FirstFiber p e n := ⟨⟨fun j ↦ x.val (Equiv.swap 0 i j),by
        rw [Equiv.sum_comp (Equiv.swap 0 i) (fun j ↦ (x.val j : ℕ)^4)]
        exact x.property⟩,by simpa only [Equiv.swap_apply_left] using hi⟩
      refine ⟨.inr (i,y),?_⟩
      apply Subtype.ext
      funext j
      simp only [f,y,Equiv.swap_apply_self]
  have hh := Fintype.card_le_of_surjective f hf
  have hfirst := first_fiber_upper p e n
  change fiberCount (p^(e+1)) n ≤ _ at hh
  simp only [A,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] at hh
  calc
    fiberCount (p^(e+1)) n ≤ _ := hh
    _ ≤ Fintype.card (DivFiber p (p^(e+1)) n)+
        4*(4*(p^(e+1)).divisors.card^2*(p^(e+1))^3) := by gcongr
    _ = _ := by ring

end
end Erdos322Research.QuarticFiberBasic
