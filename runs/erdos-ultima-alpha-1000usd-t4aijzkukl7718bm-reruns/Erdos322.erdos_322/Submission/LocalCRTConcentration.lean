import Submission.LocalPeakCounting

/-! Independent prime-power concentrations combine by the Chinese remainder theorem. -/
namespace Erdos322Research.LocalCRTConcentration
noncomputable section
open Finset LocalPeakCounting
set_option maxHeartbeats 0

private abbrev RingRoots (k : ℕ) (R : Type*) [CommRing R] :=
  {x : Fin k → R // ∑ i, x i^k=0}

private def rootsEquiv (k q : ℕ) [NeZero q] : Roots k q ≃ RingRoots k (ZMod q) where
  toFun x := ⟨fun i ↦ (x.val i : ℕ),by
    have hh := (ZMod.natCast_eq_zero_iff _ _).mpr x.property
    simpa only [Nat.cast_sum,Nat.cast_pow] using hh⟩
  invFun x := ⟨fun i ↦ ⟨(x.val i).val,ZMod.val_lt _⟩,by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
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

private def ringRootsCongr (k : ℕ) {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : RingRoots k R ≃ RingRoots k S where
  toFun x := ⟨fun i ↦ e (x.val i),by simpa only [map_sum,map_pow,map_zero] using congrArg e x.property⟩
  invFun x := ⟨fun i ↦ e.symm (x.val i),by simpa only [map_sum,map_pow,map_zero] using congrArg e.symm x.property⟩
  left_inv x := by apply Subtype.ext; funext i; exact e.symm_apply_apply _
  right_inv x := by apply Subtype.ext; funext i; exact e.apply_symm_apply _

private def ringRootsProd (k : ℕ) {R S : Type*} [CommRing R] [CommRing S] :
    RingRoots k (R × S) ≃ RingRoots k R × RingRoots k S where
  toFun x := (⟨fun i ↦ (x.val i).1,by
    simpa only [Prod.fst_sum,Prod.pow_fst,Prod.fst_zero] using congrArg Prod.fst x.property⟩,
    ⟨fun i ↦ (x.val i).2,by
    simpa only [Prod.snd_sum,Prod.pow_snd,Prod.snd_zero] using congrArg Prod.snd x.property⟩)
  invFun x := ⟨fun i ↦ (x.1.val i,x.2.val i),by
    apply Prod.ext
    · simpa only [Prod.fst_sum,Prod.pow_fst,Prod.fst_zero] using x.1.property
    · simpa only [Prod.snd_sum,Prod.pow_snd,Prod.snd_zero] using x.2.property⟩
  left_inv x := by apply Subtype.ext; funext i; rfl
  right_inv x := by rfl

/-- The exact box-congruence count is multiplicative in coprime moduli. -/
theorem rootCount_mul (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (h : m.Coprime n) :
    rootCount k (m*n)=rootCount k m*rootCount k n := by
  classical
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero n := ⟨hn.ne'⟩
  let e : Roots k (m*n) ≃ Roots k m × Roots k n :=
    ((rootsEquiv k (m*n)).trans
      ((ringRootsCongr k (ZMod.chineseRemainder h)).trans (ringRootsProd k))).trans
      ((rootsEquiv k m).symm.prodCongr (rootsEquiv k n).symm)
  simpa only [rootCount,Fintype.card_prod] using Fintype.card_congr e

/-- A good prime can be chosen outside any finite collection of prime divisors. -/
theorem good_prime_avoiding (k B : ℕ) (hk : 2 ≤ k) (hB : 0 < B) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ k ∧ p.Coprime B ∧
      ∃ a : ZMod p, a ≠ 0 ∧ a^k+1=0 := by
  have hb : 0 < (2*k*B)^k := pow_pos (by positivity) _
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (show (2*k*B)^k+1 ≠ 1 by omega)
  have hn : ¬p ∣ 2*k*B := by
    intro hh
    have hh' : p ∣ (2*k*B)^k := dvd_pow hh (by omega : k ≠ 0)
    have h1 : p ∣ 1 := by simpa using Nat.dvd_sub hd hh'
    exact hp.not_dvd_one h1
  have hpk : ¬p ∣ k := fun hh ↦ hn (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hh 2) B)
  have hpB : p.Coprime B := hp.coprime_iff_not_dvd.mpr fun hh ↦ hn (dvd_mul_of_dvd_right hh (2*k))
  refine ⟨p,hp,hpk,hpB,(2*k*B : ℕ),?_,?_⟩
  · exact (ZMod.natCast_eq_zero_iff _ _).not.mpr hn
  · have hh := (ZMod.natCast_eq_zero_iff ((2*k*B)^k+1) p).mpr hd
    simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_one] using hh

/-- Arbitrarily many independent local singular contributions give arbitrarily
high polynomial growth in the depth, while the modulus grows exponentially. -/
theorem arbitrary_order_concentration (k r : ℕ) :
    ∃ B : ℕ, 1 < B ∧ ∀ d : ℕ,
      (d+1)^(r+1)*B^((k+2)*d*(k+1)) ≤ rootCount (k+2) (B^((k+2)*d+1)) := by
  induction r with
  | zero =>
    obtain ⟨p,hp,hpk,a,ha,hseed⟩ := exists_good_prime (k+2) (by omega)
    letI : Fact p.Prime := ⟨hp⟩
    refine ⟨p,hp.one_lt,?_⟩
    intro d
    simpa using rootCount_growth p k hpk a ha hseed d
  | succ r ih =>
    obtain ⟨B,hB,h⟩ := ih
    obtain ⟨p,hp,hpk,hpB,a,ha,hseed⟩ := good_prime_avoiding (k+2) B (by omega) (by omega)
    letI : Fact p.Prime := ⟨hp⟩
    refine ⟨p*B,by nlinarith [hp.two_le],?_⟩
    intro d
    conv_rhs => rw [mul_pow,rootCount_mul _ _ _ (pow_pos hp.pos _) (pow_pos (by omega : 0 < B) _)
      (hpB.pow _ _)]
    have h1 := rootCount_growth p k hpk a ha hseed d
    have h2 := h d
    calc
      (d+1)^(r+1+1)*(p*B)^((k+2)*d*(k+1)) =
          ((d+1)*p^((k+2)*d*(k+1)))*((d+1)^(r+1)*B^((k+2)*d*(k+1))) := by
        rw [pow_succ,mul_pow]
        ring
      _ ≤ _ := Nat.mul_le_mul h1 h2

end
end Erdos322Research.LocalCRTConcentration
