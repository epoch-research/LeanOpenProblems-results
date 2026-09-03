import Submission.GrowingOriginRepairExplore

/-! The old scalar field itself supplies the additive block for a growing,
exact-slice finite extension. No small-doubling input remains in this
specialization, and all capacity bounds are explicit. -/
namespace Erdos66GrowingSubfieldBlock
open Erdos66GrowingFieldSlice Erdos66GrowingOriginRepair
  Erdos66OddExtensionFlatSet Erdos66FiniteField Erdos66OriginRepair
  Erdos66ParabolaRepair Erdos66Coset Erdos66GrowingParameterTranslate
open scoped Classical
set_option maxHeartbeats 2800000

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]

omit [DecidableEq F] [Fintype K] in
lemma scalarRange_add {x y : K} (hx : x∈scalarRange (F:=F))
    (hy : y∈scalarRange (F:=F)) : x+y∈scalarRange (F:=F) := by
  obtain ⟨a,rfl⟩ := (mem_scalarRange x).mp hx
  obtain ⟨b,rfl⟩ := (mem_scalarRange y).mp hy
  exact (mem_scalarRange _).mpr ⟨a+b,map_add _ _ _⟩

lemma cubic_extension_capacity (q Q u t : ℕ) (hq : 3≤q) (hQ : q^3≤Q)
    (hu : u≤q) (ht : t≤q) :
    2*(q*q+q)<Q ∧ t≤(u+q)^2/2 ∧ (u+q)^2/2-t≤Q-q := by
  have hq2 : q*q≥3*q := Nat.mul_le_mul_right q hq
  have hstrict : 2*(q*q+q)<q^3 := by
    have h₁ := Nat.mul_le_mul_left (q-2) hq2
    have h₂ : 1≤q-2 := by omega
    nlinarith [Nat.mul_sub_left_distrib q q 2]
  have hmlo : 2*q≤(u+q)^2 := by nlinarith [sq_nonneg (u:ℤ)]
  have hmhi : (u+q)^2≤4*q^2 := by nlinarith
  have hQhi : 2*q^2+q≤Q := by nlinarith [hstrict]
  refine ⟨hstrict.trans_le hQ,?_,?_⟩
  · omega
  · omega

/-- Every sufficiently large odd extension admits a larger repaired model
with its exact old slice. The new nominal mean is `(q+|U|)^2`, not the old
mean `|U|^2`; `q` is the old field cardinality. -/
theorem exists_subfield_block_extension (hd : Odd (Module.finrank F K))
    (hK : ringChar K≠2) (hq : 3≤Fintype.card F)
    (hQ : (Fintype.card F)^3≤Fintype.card K)
    (U : Finset F) (hne : U.Nonempty) (hU : ∀ u∈U, u≠0)
    (hUU : ∀ u∈U, ∀ v∈U, u+v≠0)
    (w : F) (hw : w≠0) (hwU : w∉U) (hnwU : -w∉U)
    (T : Finset F) (hT : (0:F)∉T) :
    ∃ (B : Finset (K×K)) (E : ℝ),
      (∀ z : F×F, planeMap z∈B ↔ z∈parabolaSet U∪repairPoints w T) ∧
      0≤E ∧ E^2≤8*(Fintype.card F:ℝ)^3 ∧
      pairCount B B 0=1+2*((U.card+Fintype.card F)^2/2) ∧
      ∀ z : K×K, |(pairCount B B z:ℝ)-((U.card:ℝ)+Fintype.card F)^2| ≤
        (U.card:ℝ)^2+E+2*(U.card:ℝ)*Fintype.card F+
          10*((U.card:ℝ)+Fintype.card F)+9 := by
  have hcap := cubic_extension_capacity (Fintype.card F) (Fintype.card K)
    U.card T.card hq hQ (Finset.card_le_univ _) (Finset.card_le_univ _)
  let R := scalarRange (F:=F) (K:=K)
  obtain ⟨B,E,hslice,hE,hE2,hzero,hcount⟩ := exists_growing_repaired_slice hd hK U hne hU hUU
    w hw hwU hnwU T hT R R (fun x hx y hy ↦ scalarRange_add hx hy)
    (by simpa only [R,scalarRange_card] using hcap.1)
    (by simpa only [R,scalarRange_card] using hcap.2.1)
    (by simpa only [R,scalarRange_card] using hcap.2.2)
  simp only [R,scalarRange_card] at hE2 hzero hcount
  have henergy : E^2≤8*(Fintype.card F:ℝ)^3 := by nlinarith only [hE2]
  have hu : (∑ a : F, |(charFiber U a:ℝ)|) ≤ (U.card:ℝ)^2 := by
    have hh := crossCharFiber_l1_le U U
    change (∑ a : F, |charFiber U a|) ≤ (U.card:ℤ)*U.card at hh
    exact_mod_cast (by nlinarith only [hh] :
      (∑ a : F, |charFiber U a|) ≤ (U.card:ℤ)^2)
  refine ⟨B,E,hslice,hE,henergy,hzero,fun z ↦ ?_⟩
  exact (hcount z).trans (by linarith)

lemma growing_error_relative (q u E ε : ℝ) (hq : 1≤q) (hu : 0≤u)
    (hε : 0<ε) (hε1 : ε≤1) (huq : 10*u≤ε*q)
    (hprecision : 1600≤ε^2*q) (hE2 : E^2≤8*q^3) :
    u^2+E+2*u*q+10*(u+q)+9 ≤ ε*(u+q)^2 := by
  have hq0 : 0<q := by linarith
  have hq2 : 0<q^2 := sq_pos_of_pos hq0
  have heq : E≤ε*q^2/10 := by
    have hmul := mul_le_mul_of_nonneg_right hprecision (show 0≤q^3 by positivity)
    apply le_of_sq_le_sq _ (by positivity : 0≤ε*q^2/10)
    nlinarith only [hmul,hE2,show 0≤q^3 by positivity]
  have huu : u≤q := by nlinarith
  have hu2 : u^2≤ε*q^2/10 := by
    have h₁ := mul_le_mul_of_nonneg_right huq hu
    have h₂ := mul_le_mul_of_nonneg_left huu (mul_nonneg hε.le hq0.le)
    nlinarith only [h₁,h₂]
  have hcross : 2*u*q≤ε*q^2/5 := by nlinarith [mul_le_mul_of_nonneg_right huq hq0.le]
  have hεq : 1600≤ε*q := by
    have hh := mul_le_mul_of_nonneg_right hε1 (mul_nonneg hε.le hq0.le)
    nlinarith only [hprecision,hh]
  have hlin : 10*(u+q)+9≤ε*q^2/10 := by
    have hh := mul_le_mul_of_nonneg_right hεq hq0.le
    nlinarith only [hh,huu,hq]
  have htarget : ε*q^2≤ε*(u+q)^2 := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    nlinarith
  nlinarith only [hu2,heq,hcross,hlin,htarget,mul_pos hε hq2]

/-- An explicit improving-precision form. No natural ordering is used. -/
theorem exists_accurate_subfield_block_extension (hd : Odd (Module.finrank F K))
    (hK : ringChar K≠2) (hq : 3≤Fintype.card F)
    (hQ : (Fintype.card F)^3≤Fintype.card K)
    (U : Finset F) (hne : U.Nonempty) (hU : ∀ u∈U, u≠0)
    (hUU : ∀ u∈U, ∀ v∈U, u+v≠0)
    (w : F) (hw : w≠0) (hwU : w∉U) (hnwU : -w∉U)
    (T : Finset F) (hT : (0:F)∉T) (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1)
    (huq : 10*(U.card:ℝ)≤ε*Fintype.card F)
    (hprecision : 1600≤ε^2*Fintype.card F) :
    ∃ B : Finset (K×K),
      (∀ z : F×F, planeMap z∈B ↔ z∈parabolaSet U∪repairPoints w T) ∧
      ∀ z : K×K, |(pairCount B B z:ℝ)-((U.card:ℝ)+Fintype.card F)^2| ≤
        ε*((U.card:ℝ)+Fintype.card F)^2 := by
  obtain ⟨B,E,hslice,hE,hE2,hzero,hcount⟩ := exists_subfield_block_extension hd hK hq hQ
    U hne hU hUU w hw hwU hnwU T hT
  refine ⟨B,hslice,fun z ↦ (hcount z).trans ?_⟩
  exact growing_error_relative _ _ E ε (by exact_mod_cast (show 1≤Fintype.card F by omega))
    (Nat.cast_nonneg _) hε hε1 huq hprecision hE2

end Erdos66GrowingSubfieldBlock
