import Submission.QuarticFiberBasic

/-! Singular scaling for quartic congruences with arbitrary target. -/
namespace Erdos322Research.QuarticFiberScaling
noncomputable section
open Finset QuarticFiberBasic
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

theorem divisible_box_upper (p e n : ℕ) (hp : 0 < p) :
    Fintype.card (DivFiber p (p^(e+1)) n) ≤ p^(4*e) := by
  let f : DivFiber p (p^(e+1)) n → (Fin 4 → Fin (p^e)) := fun x i ↦
    ⟨(x.val.val i : ℕ)/p,by
      apply (Nat.div_lt_iff_lt_mul hp).mpr
      simpa only [pow_succ] using (x.val.val i).isLt⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hh := congrArg (fun z : Fin 4 → Fin (p^e) ↦ (z i : ℕ)) h
    change (x.val.val i : ℕ)/p=(y.val.val i : ℕ)/p at hh
    calc
      (x.val.val i : ℕ) = p*((x.val.val i : ℕ)/p) := (Nat.mul_div_cancel' (x.property i)).symm
      _ = p*((y.val.val i : ℕ)/p) := congrArg (p*·) hh
      _ = (y.val.val i : ℕ) := Nat.mul_div_cancel' (y.property i)
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fun,Fintype.card_fin,← pow_mul,mul_comm e 4] using hh

private lemma quotient_bound (p q n : ℕ) (hp : 0 < p)
    (x : DivFiber p (p^4*q) n) (i : Fin 4) :
    (x.val.val i : ℕ)/p < q*p^3 := by
  apply (Nat.div_lt_iff_lt_mul hp).mpr
  have hx := (x.val.val i).isLt
  convert hx using 1
  ring

/-- If the singular fiber is nonempty, divide one reference solution by p.
All other divided tuples have the same new target modulo q. -/
theorem divisible_scaling_upper (p q n : ℕ) (hp : 0 < p) (hq : 0 < q) :
    ∃ m : ℕ, Fintype.card (DivFiber p (p^4*q) n) ≤ fiberCount q m*p^12 := by
  classical
  by_cases hA : Nonempty (DivFiber p (p^4*q) n)
  · let a : DivFiber p (p^4*q) n := Classical.choice hA
    let y (x : DivFiber p (p^4*q) n) (i : Fin 4) := (x.val.val i : ℕ)/p
    let m := ∑ i, y a i^4
    have hy (x : DivFiber p (p^4*q) n) : (∑ i, y x i^4) ≡ m [MOD q] := by
      apply Nat.ModEq.mul_left_cancel' (c := p^4) (pow_ne_zero _ hp.ne')
      have hh := x.val.property.trans a.val.property.symm
      convert hh using 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [← mul_pow]
        exact congrArg (fun z ↦ z^4) (Nat.mul_div_cancel' (x.property i))
      · dsimp only [m]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [← mul_pow]
        exact congrArg (fun z ↦ z^4) (Nat.mul_div_cancel' (a.property i))
    let r (x : DivFiber p (p^4*q) n) : Fiber q m :=
      ⟨fun i ↦ ⟨y x i%q,Nat.mod_lt _ hq⟩,by
        apply (ZMod.natCast_eq_natCast_iff _ _ q).mp
        push_cast
        simp only [ZMod.natCast_mod]
        have hh := (ZMod.natCast_eq_natCast_iff _ _ q).mpr (hy x)
        push_cast at hh
        exact hh⟩
    let t (x : DivFiber p (p^4*q) n) (i : Fin 4) : Fin (p^3) :=
      ⟨y x i/q,by
        apply (Nat.div_lt_iff_lt_mul hq).mpr
        simpa only [mul_comm] using quotient_bound p q n hp x i⟩
    let f : DivFiber p (p^4*q) n → Fiber q m × (Fin 4 → Fin (p^3)) := fun x ↦ (r x,t x)
    have hf : Function.Injective f := by
      intro x z h
      have hr := congrArg Prod.fst h
      have ht := congrArg Prod.snd h
      apply Subtype.ext
      apply Subtype.ext
      funext i
      apply Fin.ext
      have hrem := congrArg (fun a : Fiber q m ↦ (a.val i : ℕ)) hr
      have hdiv := congrArg (fun a : Fin 4 → Fin (p^3) ↦ (a i : ℕ)) ht
      change y x i%q=y z i%q at hrem
      change y x i/q=y z i/q at hdiv
      have he : y x i=y z i := by
        calc
          y x i = y x i%q+q*(y x i/q) := (Nat.mod_add_div _ _).symm
          _ = y z i%q+q*(y z i/q) := by rw [hrem,hdiv]
          _ = y z i := Nat.mod_add_div _ _
      dsimp only [y] at he
      calc
        (x.val.val i : ℕ) = p*((x.val.val i : ℕ)/p) := (Nat.mul_div_cancel' (x.property i)).symm
        _ = p*((z.val.val i : ℕ)/p) := congrArg (p*·) he
        _ = (z.val.val i : ℕ) := Nat.mul_div_cancel' (z.property i)
    refine ⟨m,?_⟩
    have hh := Fintype.card_le_of_injective f hf
    simpa only [fiberCount,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,← pow_mul] using hh
  · haveI : IsEmpty (DivFiber p (p^4*q) n) := not_nonempty_iff.mp hA
    exact ⟨0,by simp⟩

end
end Erdos322Research.QuarticFiberScaling
