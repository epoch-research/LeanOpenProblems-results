import Submission.LocalRootUpperBasic

/-! Primitive and singular upper bounds for critical power-sum congruences. -/
namespace Erdos322Research.LocalRootUpperScaling
noncomputable section
open Finset LocalPeakCounting LocalRootUpperBasic
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

abbrev DivRoots (k p q : ℕ) := {x : Roots (k+2) q // ∀ i, p ∣ (x.val i : ℕ)}

/-- Cover roots by the all-divisible part and one nonsingular coordinate. -/
theorem root_cover_upper (k p e : ℕ) [Fact p.Prime] (hk : ¬p ∣ k+2) :
    rootCount (k+2) (p^(e+1)) ≤ Fintype.card (DivRoots k p (p^(e+1))) +
      (k+2)^2*(p^(e+1))^(k+1) := by
  classical
  let A := DivRoots k p (p^(e+1)) ⊕ (Fin (k+2) × FirstRoots k p e)
  let f : A → Roots (k+2) (p^(e+1)) := fun z ↦ match z with
    | .inl x => x.val
    | .inr (i,x) => ⟨fun j ↦ x.val.val (Equiv.swap 0 i j),by
      rw [Equiv.sum_comp (Equiv.swap 0 i) (fun j ↦ (x.val.val j : ℕ)^(k+2))]
      exact x.val.property⟩
  have hf : Function.Surjective f := by
    intro x
    by_cases hd : ∀ i, p ∣ (x.val i : ℕ)
    · exact ⟨.inl ⟨x,hd⟩,rfl⟩
    · push_neg at hd
      obtain ⟨i,hi⟩ := hd
      let y : FirstRoots k p e := ⟨⟨fun j ↦ x.val (Equiv.swap 0 i j),by
        rw [Equiv.sum_comp (Equiv.swap 0 i) (fun j ↦ (x.val j : ℕ)^(k+2))]
        exact x.property⟩,by simpa only [Equiv.swap_apply_left] using hi⟩
      refine ⟨.inr (i,y),?_⟩
      apply Subtype.ext
      funext j
      simp only [f,y,Equiv.swap_apply_self]
  have hh := Fintype.card_le_of_surjective f hf
  have hfirst := first_roots_upper k p e hk
  change rootCount (k+2) (p^(e+1)) ≤ _ at hh
  simp only [A,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] at hh
  calc
    rootCount (k+2) (p^(e+1)) ≤ _ := hh
    _ ≤ Fintype.card (DivRoots k p (p^(e+1)))+
        (k+2)*((k+2)*(p^(e+1))^(k+1)) := by gcongr
    _ = _ := by ring

/-- A crude singular bound, used before one whole degree of scaling. -/
theorem divisible_box_upper (k p e : ℕ) (hp : 0 < p) :
    Fintype.card (DivRoots k p (p^(e+1))) ≤ p^(e*(k+2)) := by
  let f : DivRoots k p (p^(e+1)) → (Fin (k+2) → Fin (p^e)) := fun x i ↦
    ⟨(x.val.val i : ℕ)/p,by
      apply (Nat.div_lt_iff_lt_mul hp).mpr
      simpa only [pow_succ] using (x.val.val i).isLt⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hh := congrArg (fun z : Fin (k+2) → Fin (p^e) ↦ (z i : ℕ)) h
    change (x.val.val i : ℕ)/p=(y.val.val i : ℕ)/p at hh
    have hx := Nat.mul_div_cancel' (x.property i)
    have hy := Nat.mul_div_cancel' (y.property i)
    calc
      (x.val.val i : ℕ) = p*((x.val.val i : ℕ)/p) := hx.symm
      _ = p*((y.val.val i : ℕ)/p) := congrArg (p*·) hh
      _ = (y.val.val i : ℕ) := hy
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fun,Fintype.card_fin,← pow_mul] using hh

private lemma quotient_bound (k p q : ℕ) (hp : 0 < p)
    (x : DivRoots k p (p^(k+2)*q)) (i : Fin (k+2)) :
    (x.val.val i : ℕ)/p < q*p^(k+1) := by
  apply (Nat.div_lt_iff_lt_mul hp).mpr
  have hx := (x.val.val i).isLt
  convert hx using 1
  rw [show k+2=k+1+1 by omega,pow_succ]
  ring

/-- The singular part scales with exactly the critical dimension. -/
theorem divisible_scaling_upper (k p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    Fintype.card (DivRoots k p (p^(k+2)*q)) ≤
      rootCount (k+2) q*p^((k+2)*(k+1)) := by
  classical
  let y (x : DivRoots k p (p^(k+2)*q)) (i : Fin (k+2)) := (x.val.val i : ℕ)/p
  have hy (x : DivRoots k p (p^(k+2)*q)) : q ∣ ∑ i, y x i^(k+2) := by
    apply Nat.dvd_of_mul_dvd_mul_left (pow_pos hp (k+2))
    rw [Finset.mul_sum]
    convert x.val.property using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_pow]
    exact congrArg (fun n ↦ n^(k+2)) (Nat.mul_div_cancel' (x.property i))
  let r (x : DivRoots k p (p^(k+2)*q)) : Roots (k+2) q :=
    ⟨fun i ↦ ⟨y x i%q,Nat.mod_lt _ hq⟩,by
      apply (ZMod.natCast_eq_zero_iff _ q).mp
      push_cast
      simp only [ZMod.natCast_mod]
      have hh := (ZMod.natCast_eq_zero_iff _ q).mpr (hy x)
      push_cast at hh
      exact hh⟩
  let t (x : DivRoots k p (p^(k+2)*q)) (i : Fin (k+2)) : Fin (p^(k+1)) :=
    ⟨y x i/q,by
      apply (Nat.div_lt_iff_lt_mul hq).mpr
      simpa only [mul_comm] using quotient_bound k p q hp x i⟩
  let f : DivRoots k p (p^(k+2)*q) → Roots (k+2) q × (Fin (k+2) → Fin (p^(k+1))) :=
    fun x ↦ (r x,t x)
  have hf : Function.Injective f := by
    intro x z h
    have hr := congrArg Prod.fst h
    have ht := congrArg Prod.snd h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hrem := congrArg (fun a : Roots (k+2) q ↦ (a.val i : ℕ)) hr
    have hdiv := congrArg (fun a : Fin (k+2) → Fin (p^(k+1)) ↦ (a i : ℕ)) ht
    change y x i%q=y z i%q at hrem
    change y x i/q=y z i/q at hdiv
    have he : y x i=y z i := by
      calc
        y x i = y x i%q+q*(y x i/q) := (Nat.mod_add_div _ _).symm
        _ = y z i%q+q*(y z i/q) := by rw [hrem,hdiv]
        _ = y z i := Nat.mod_add_div _ _
    have hx := Nat.mul_div_cancel' (x.property i)
    have hz := Nat.mul_div_cancel' (z.property i)
    dsimp only [y] at he
    calc
      (x.val.val i : ℕ) = p*((x.val.val i : ℕ)/p) := hx.symm
      _ = p*((z.val.val i : ℕ)/p) := congrArg (p*·) he
      _ = (z.val.val i : ℕ) := hz
  have hh := Fintype.card_le_of_injective f hf
  simpa only [rootCount,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,← pow_mul,
    mul_comm (k+1) (k+2)] using hh

end
end Erdos322Research.LocalRootUpperScaling
