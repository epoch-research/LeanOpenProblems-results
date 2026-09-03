import Submission.QuarticFiberScaling

/-! Chinese remainder factorization of arbitrary quartic congruence fibers. -/
namespace Erdos322Research.QuarticFiberCRT
noncomputable section
open QuarticFiberBasic
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

abbrev RingFiber (R : Type*) [CommRing R] (n : ℕ) :=
  {x : Fin 4 → R // ∑ i, x i^4=(n : R)}

def fiberEquiv (q n : ℕ) [NeZero q] : Fiber q n ≃ RingFiber (ZMod q) n where
  toFun x := ⟨fun i ↦ (x.val i : ℕ),by
    have hh := (ZMod.natCast_eq_natCast_iff _ _ q).mpr x.property
    simpa only [Nat.cast_sum,Nat.cast_pow] using hh⟩
  invFun x := ⟨fun i ↦ ⟨(x.val i).val,ZMod.val_lt _⟩,by
    apply (ZMod.natCast_eq_natCast_iff _ _ q).mp
    push_cast
    simpa only [ZMod.natCast_zmod_val] using x.property⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact ZMod.val_natCast_of_lt (x.val i).isLt
  right_inv x := by
    apply Subtype.ext
    funext i
    exact ZMod.natCast_zmod_val _

private def ringFiberCongr (n : ℕ) {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : RingFiber R n ≃ RingFiber S n where
  toFun x := ⟨fun i ↦ e (x.val i),by simpa only [map_sum,map_pow,map_natCast] using congrArg e x.property⟩
  invFun x := ⟨fun i ↦ e.symm (x.val i),by simpa only [map_sum,map_pow,map_natCast] using congrArg e.symm x.property⟩
  left_inv x := by apply Subtype.ext; funext i; exact e.symm_apply_apply _
  right_inv x := by apply Subtype.ext; funext i; exact e.apply_symm_apply _

private def ringFiberProd (n : ℕ) {R S : Type*} [CommRing R] [CommRing S] :
    RingFiber (R × S) n ≃ RingFiber R n × RingFiber S n where
  toFun x := (⟨fun i ↦ (x.val i).1,by
    simpa only [Prod.fst_sum,Prod.pow_fst,Prod.fst_natCast] using congrArg Prod.fst x.property⟩,
    ⟨fun i ↦ (x.val i).2,by
    simpa only [Prod.snd_sum,Prod.pow_snd,Prod.snd_natCast] using congrArg Prod.snd x.property⟩)
  invFun x := ⟨fun i ↦ (x.1.val i,x.2.val i),by
    apply Prod.ext
    · simpa only [Prod.fst_sum,Prod.pow_fst,Prod.fst_natCast] using x.1.property
    · simpa only [Prod.snd_sum,Prod.pow_snd,Prod.snd_natCast] using x.2.property⟩
  left_inv x := by apply Subtype.ext; funext i; rfl
  right_inv x := by rfl

/-- Factorization holds for every target, not just the zero fiber. -/
theorem fiberCount_mul (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a.Coprime b) :
    fiberCount (a*b) n=fiberCount a n*fiberCount b n := by
  letI : NeZero a := ⟨ha.ne'⟩
  letI : NeZero b := ⟨hb.ne'⟩
  let e : Fiber (a*b) n ≃ Fiber a n × Fiber b n :=
    ((fiberEquiv (a*b) n).trans
      ((ringFiberCongr n (ZMod.chineseRemainder h)).trans (ringFiberProd n))).trans
      ((fiberEquiv a n).symm.prodCongr (fiberEquiv b n).symm)
  simpa only [fiberCount,Fintype.card_prod] using Fintype.card_congr e

end
end Erdos322Research.QuarticFiberCRT
