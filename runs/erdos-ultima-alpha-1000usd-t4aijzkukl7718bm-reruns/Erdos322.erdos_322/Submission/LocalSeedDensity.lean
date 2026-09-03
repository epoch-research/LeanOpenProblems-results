import Submission.LocalCRTConcentration

/-! Uniform seed density for even critical power sums. These congruence bounds
are not upper or positive-power lower bounds for the exact representation count. -/
namespace Erdos322Research.LocalSeedDensity
noncomputable section
open Finset LocalPeakCounting
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

abbrev RingRoots (k : ℕ) (R : Type*) [CommRing R] :=
  {x : Fin k → R // ∑ i, x i^k=0}

abbrev FirstSeeds (k p : ℕ) :=
  {x : Fin (k+2) → ZMod p // (∑ i, x i^(k+2)=0) ∧ x 0 ≠ 0}

def firstSeedCount (k p : ℕ) [NeZero p] : ℕ := Fintype.card (FirstSeeds k p)

def rootsEquiv (k q : ℕ) [NeZero q] : Roots k q ≃ RingRoots k (ZMod q) where
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

/-- Cauchy--Schwarz for the fibers of a map between finite sets. -/
theorem fiber_energy {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] (f : A → B) :
    Fintype.card A ^ 2 ≤ Fintype.card B *
      Fintype.card (Σ b : B, {x : A // f x=b} × {x : A // f x=b}) := by
  have hc : ∑ b : B, Fintype.card {x : A // f x=b}=Fintype.card A := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset B)
    (fun _ ↦ (1 : ℕ)) (fun b ↦ Fintype.card {x : A // f x=b})
  simpa only [one_mul,one_pow,sum_const,card_univ,smul_eq_mul,mul_one,hc,
    Fintype.card_sigma,Fintype.card_prod,pow_two] using hh

/-- For an even number of variables and a kth root of -1, the zero fiber
has at least its average size. -/
theorem even_root_count_lower (k p : ℕ) [Fact p.Prime] (hk : 0 < k) (he : Even k)
    (a : ZMod p) (ha : a^k+1=0) : p^(k-1) ≤ rootCount k p := by
  classical
  obtain ⟨m,rfl⟩ := he
  have ha0 : a ≠ 0 := by
    intro hz
    simp only [hz,zero_pow hk.ne',zero_add] at ha
    exact one_ne_zero ha
  let A := Fin m → ZMod p
  let f : A → ZMod p := fun x ↦ ∑ i, x i^(m+m)
  let E := Σ b : ZMod p, {x : A // f x=b} × {x : A // f x=b}
  let g : E → RingRoots (m+m) (ZMod p) := fun x ↦
    ⟨Fin.append x.2.1.val (fun i ↦ a*x.2.2.val i),by
      simp only [Fin.sum_univ_add,Fin.append_left,Fin.append_right,mul_pow,
        ← Finset.mul_sum]
      change f x.2.1.val+a^(m+m)*f x.2.2.val=0
      rw [x.2.1.property,x.2.2.property]
      linear_combination x.1*ha⟩
  have hg : Function.Injective g := by
    rintro ⟨b,x,y⟩ ⟨c,u,v⟩ h
    have hx : x.val=u.val := by
      funext i
      have hh := congrArg (fun z : RingRoots (m+m) (ZMod p) ↦ z.val (Fin.castAdd m i)) h
      simpa only [g,Fin.append_left] using hh
    have hy : y.val=v.val := by
      funext i
      have hh := congrArg (fun z : RingRoots (m+m) (ZMod p) ↦ z.val (Fin.natAdd m i)) h
      simp only [g,Fin.append_right] at hh
      exact mul_left_cancel₀ ha0 hh
    have hbc : b=c := x.property.symm.trans ((congrArg f hx).trans u.property)
    subst c
    congr 1
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  have hh := fiber_energy f
  rw [ZMod.card] at hh
  have hh := hh.trans (Nat.mul_le_mul_left p (Fintype.card_le_of_injective g hg))
  have hc : p^(m+m) ≤ p*rootCount (m+m) p := by
    have heq := Fintype.card_congr (rootsEquiv (m+m) p)
    simp only [A,Fintype.card_fun,Fintype.card_fin,ZMod.card,pow_two,← pow_add] at hh
    simpa only [rootCount,heq] using hh
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpw : p^(m+m)=p*p^(m+m-1) := by
    rw [← pow_succ',Nat.sub_add_cancel (by omega : 1 ≤ m+m)]
  rw [hpw] at hc
  exact Nat.le_of_mul_le_mul_left hc hp

/-- All roots except zero have a nonzero coordinate; coordinate permutations
make each of the possible first-coordinate seed sets equally large. -/
theorem root_count_le_first_seeds (k p : ℕ) [Fact p.Prime] :
    rootCount (k+2) p ≤ 1+(k+2)*firstSeedCount k p := by
  classical
  let zeroRoot : RingRoots (k+2) (ZMod p) := ⟨0,by simp⟩
  let f : Option (Fin (k+2) × FirstSeeds k p) → RingRoots (k+2) (ZMod p) :=
    fun x ↦ match x with
    | none => zeroRoot
    | some (i,a) => ⟨fun j ↦ a.val (Equiv.swap 0 i j),by
      exact (Equiv.sum_comp (Equiv.swap 0 i) (fun j ↦ a.val j^(k+2))).trans a.property.1⟩
  have hf : Function.Surjective f := by
    intro x
    by_cases hx : x.val=0
    · refine ⟨none,?_⟩
      apply Subtype.ext
      exact hx.symm
    · have hi : ∃ i, x.val i ≠ 0 := by
        by_contra hn
        push_neg at hn
        apply hx
        funext i
        exact hn i
      obtain ⟨i,hi⟩ := hi
      let a : FirstSeeds k p := ⟨fun j ↦ x.val (Equiv.swap 0 i j),by
        constructor
        · exact (Equiv.sum_comp (Equiv.swap 0 i) (fun j ↦ x.val j^(k+2))).trans x.property
        · simpa only [Equiv.swap_apply_left] using hi⟩
      refine ⟨some (i,a),?_⟩
      apply Subtype.ext
      funext j
      simp only [f,a,Equiv.swap_apply_self]
  have hh := Fintype.card_le_of_surjective f hf
  have heq := Fintype.card_congr (rootsEquiv (k+2) p)
  simpa only [rootCount,heq,Fintype.card_option,Fintype.card_prod,
    Fintype.card_fin,firstSeedCount,add_comm] using hh

/-- Uniformly in the prime, a fixed fraction of p^(k-1) seed roots has a
nonzero first coordinate. The loss is 2k, not p^(k-1). -/
theorem first_seed_density (k p : ℕ) [Fact p.Prime] (he : Even (k+2))
    (a : ZMod p) (ha : a^(k+2)+1=0) :
    p^(k+1) ≤ (2*(k+2))*firstSeedCount k p := by
  have h1 : p^(k+1) ≤ rootCount (k+2) p := by
    simpa using even_root_count_lower (k+2) p (by omega) he a ha
  have h2 := root_count_le_first_seeds k p
  have h3 : 2 ≤ p^(k+1) :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_pow (by omega))
  nlinarith

end
end Erdos322Research.LocalSeedDensity
