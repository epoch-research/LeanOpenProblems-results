import Submission.GroupRepBernoulliExplore

/-! A finite mixed-flat family can be extended by a denser superset when the
explicit mean-scale concentration criterion holds. This is not an integer
scale-transition theorem. -/
namespace Erdos66DenseGroupExtension
open Erdos66FiniteBernoulli Erdos66VariableBernoulliBounds Erdos66GroupRepBernoulli
open scoped Classical
variable {G : Type*} [Fintype G] [AddCommGroup G] [LinearOrder G]
set_option maxHeartbeats 2000000

noncomputable def extendProb (C : Finset G) (θ : ℝ) (a : G) : ℝ := if a∈C then 1 else θ
noncomputable def expectedCard (C : Finset G) (θ : ℝ) : ℝ :=
  θ*Fintype.card G+(1-θ)*C.card
noncomputable def actualMean (C D : Finset G) : ℝ := (C.card : ℝ)*D.card/Fintype.card G

lemma extendProb_bounds (C : Finset G) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (a : G) :
    0 ≤ extendProb C θ a ∧ extendProb C θ a ≤ 1 := by
  unfold extendProb
  split_ifs <;> norm_num <;> exact ⟨hθ,hθ1⟩

lemma extendProb_eq (C : Finset G) (θ : ℝ) (a : G) :
    extendProb C θ a=θ+(1-θ)*(if a∈C then 1 else 0) := by
  unfold extendProb
  split_ifs <;> ring

lemma sum_indicator (C : Finset G) : (∑ a : G, if a∈C then (1 : ℝ) else 0)=C.card := by simp

lemma sum_reflected_indicator (C : Finset G) (z : G) :
    (∑ a : G, if z-a∈C then (1 : ℝ) else 0)=C.card := by
  rw [←Equiv.sum_comp (Equiv.subLeft z)]
  simp [Equiv.subLeft_apply]

lemma count_indicator (C D : Finset G) (z : G) :
    (count C D z : ℝ)=∑ a : G, (if a∈C then 1 else 0)*(if z-a∈D then 1 else 0) := by
  simp only [count,Finset.card_filter]
  push_cast
  simp only [ite_mul,one_mul,zero_mul]
  rw [←Finset.sum_filter]
  simp

lemma sum_extendProb (C : Finset G) (θ : ℝ) :
    (∑ a : G, extendProb C θ a)=expectedCard C θ := by
  simp_rw [extendProb_eq]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,sum_indicator]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,expectedCard]
  ring

lemma mixed_extendProb (A C : Finset G) (θ : ℝ) (z : G) :
    (∑ a∈A, extendProb C θ (z-a))=θ*A.card+(1-θ)*count A C z := by
  simp_rw [extendProb_eq]
  rw [Finset.sum_add_distrib,←Finset.mul_sum]
  have he : (∑ a∈A, if z-a∈C then (1 : ℝ) else 0)=(count A C z : ℝ) := by
    simp only [count,Finset.card_filter]; push_cast; rfl
  rw [he]
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

lemma self_extendProb (C : Finset G) (θ : ℝ) (z : G) :
    selfMean z (extendProb C θ)=θ^2*Fintype.card G+2*θ*(1-θ)*C.card+
      (1-θ)^2*count C C z+diagCorrection z (extendProb C θ) := by
  rw [selfMean_decomposition]
  congr 1
  simp_rw [extendProb_eq]
  have he (a : G) : (θ+(1-θ)*(if a∈C then 1 else 0))*(θ+(1-θ)*(if z-a∈C then 1 else 0)) =
      θ^2+θ*(1-θ)*(if a∈C then 1 else 0)+θ*(1-θ)*(if z-a∈C then 1 else 0)+
        (1-θ)^2*((if a∈C then 1 else 0)*(if z-a∈C then 1 else 0)) := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_add_distrib,
    ←Finset.mul_sum,←Finset.mul_sum,←Finset.mul_sum,sum_indicator,sum_reflected_indicator,←count_indicator]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

/-- All selected points of C are forced: the witness has positive product
weight. Self, mixed, and cardinality tests can have different scales. -/
theorem exists_extension_about_means (C : Finset G) (H : ℕ) (A : Fin H → Finset G)
    (θ ε v Vs Vc : ℝ) (Vm : Fin H → ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hself : ∀ z, selfMean z (extendProb C θ) ≤ Vs)
    (hmixed : ∀ i z, (∑ a∈A i, extendProb C θ (z-a)) ≤ Vm i)
    (hcard : expectedCard C θ ≤ Vc)
    (hvs : v ≤ Vs) (hvm : ∀ i, v ≤ Vm i) (hvc : v ≤ Vc)
    (hsmall : 2*((H+1)*Fintype.card G+1)*Real.exp (-ε^2*v/8) < 1) :
    ∃ B : Finset G, C ⊆ B ∧
      (∀ z, |(count B B z : ℝ)-selfMean z (extendProb C θ)| < ε*Vs) ∧
      (∀ i z, |(count (A i) B z : ℝ)-(∑ a∈A i, extendProb C θ (z-a))| < ε*Vm i) ∧
      |(B.card : ℝ)-expectedCard C θ| < ε*Vc := by
  let T := Option (Sum G (Fin H × G))
  let F : T → (G → Bool) → ℝ := fun k ω ↦ match k with
    | none => (selected ω).card
    | some (.inl z) => count (selected ω) (selected ω) z
    | some (.inr (i,z)) => count (A i) (selected ω) z
  let m : T → ℝ := fun k ↦ match k with
    | none => ∑ a : G, extendProb C θ a
    | some (.inl z) => selfMean z (extendProb C θ)
    | some (.inr (i,z)) => ∑ a∈A i, extendProb C θ (z-a)
  let V : T → ℝ := fun k ↦ match k with
    | none => Vc
    | some (.inl _) => Vs
    | some (.inr (i,_)) => Vm i
  have hp := extendProb_bounds C θ hθ hθ1
  have hm : ∀ k∈(Finset.univ : Finset T), m k ≤ V k := by
    intro k hk
    rcases k with _ | (z | ⟨i,z⟩)
    · simpa only [m,V,sum_extendProb] using hcard
    · exact hself z
    · exact hmixed i z
  have hv : ∀ k∈(Finset.univ : Finset T), v ≤ V k := by
    intro k hk
    rcases k with _ | (z | ⟨i,z⟩)
    · exact hvc
    · exact hvs
    · exact hvm i
  have hmgf : ∀ k∈(Finset.univ : Finset T), ∀ t : ℝ, |t| ≤ 1/2 →
      expect (extendProb C θ) (fun ω ↦ Real.exp (t*(F k ω-m k))) ≤ Real.exp (2*t^2*m k) := by
    intro k hk t ht
    rcases k with _ | (z | ⟨i,z⟩)
    · exact card_mgf _ hp t ht
    · exact self_mgf z _ hp t ht
    · exact mixed_mgf (A i) z _ hp t ht
  have hsmall' : 2*(Finset.univ : Finset T).card*Real.exp (-ε^2*v/8) < 1 := by
    have he : (Finset.univ : Finset T).card=(H+1)*Fintype.card G+1 := by
      simp only [T,Finset.card_univ,Fintype.card_option,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
      ring
    simpa only [he,Nat.cast_add,Nat.cast_mul,Nat.cast_one] using hsmall
  obtain ⟨ω,hw,hω⟩ := exists_variable_bound (extendProb C θ) hp Finset.univ F m V v ε hε hε1 hm hv hmgf hsmall'
  refine ⟨selected ω,?_,?_,?_,?_⟩
  · intro a ha
    exact (mem_selected ω a).mpr (forced_true _ hp ω hw a (by simp [extendProb,ha]))
  · intro z; exact hω (some (.inl z)) (Finset.mem_univ _)
  · intro i z; exact hω (some (.inr (i,z))) (Finset.mem_univ _)
  · simpa only [F,m,V,sum_extendProb] using hω none (Finset.mem_univ _)

noncomputable def nominalSelf (C : Finset G) (θ : ℝ) : ℝ :=
  (expectedCard C θ)^2/Fintype.card G
noncomputable def nominalMixed (A C : Finset G) (θ : ℝ) : ℝ :=
  (A.card : ℝ)*expectedCard C θ/Fintype.card G

lemma card_group_pos : (0 : ℝ) < Fintype.card G := by
  exact_mod_cast Fintype.card_pos

lemma expectedCard_bounds (C : Finset G) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    0 ≤ expectedCard C θ ∧ (1-θ)*C.card ≤ expectedCard C θ ∧
      (C.card : ℝ) ≤ expectedCard C θ := by
  have hc : (C.card : ℝ) ≤ Fintype.card G := by exact_mod_cast Finset.card_le_univ C
  have hcn := Nat.cast_nonneg (α := ℝ) C.card
  have hn := card_group_pos (G := G)
  have h₁ := mul_nonneg hθ hn.le
  have h₂ := mul_nonneg (sub_nonneg.mpr hθ1) hcn
  have h₃ := mul_nonneg hθ (sub_nonneg.mpr hc)
  dsimp [expectedCard]
  constructor
  · positivity
  · constructor <;> nlinarith

lemma nominal_nonneg (A C : Finset G) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    0 ≤ nominalSelf C θ ∧ 0 ≤ nominalMixed A C θ := by
  have hb := (expectedCard_bounds C θ hθ hθ1).1
  constructor <;> dsimp only [nominalSelf,nominalMixed] <;> positivity

lemma nominal_self_identity (C : Finset G) (θ : ℝ) :
    nominalSelf C θ=θ^2*Fintype.card G+2*θ*(1-θ)*C.card+(1-θ)^2*actualMean C C := by
  have hn := (card_group_pos (G := G)).ne'
  dsimp [nominalSelf,expectedCard,actualMean]
  field_simp <;> ring

lemma nominal_mixed_identity (A C : Finset G) (θ : ℝ) :
    nominalMixed A C θ=θ*A.card+(1-θ)*actualMean A C := by
  have hn := (card_group_pos (G := G)).ne'
  dsimp [nominalMixed,expectedCard,actualMean]
  field_simp <;> ring

lemma old_mean_le_nominal (A C : Finset G) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1-θ)^2*actualMean C C ≤ nominalSelf C θ ∧
      (1-θ)*actualMean A C ≤ nominalMixed A C θ := by
  have hb := expectedCard_bounds C θ hθ hθ1
  have hbase : 0 ≤ (1-θ)*(C.card : ℝ) := mul_nonneg (sub_nonneg.mpr hθ1) (Nat.cast_nonneg _)
  have hs := pow_le_pow_left₀ hbase hb.2.1 2
  have hn := (card_group_pos (G := G)).le
  have hq := div_le_div_of_nonneg_right hs hn
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb.2.1 (Nat.cast_nonneg (α := ℝ) A.card)) hn
  constructor
  · convert hq using 1 <;> dsimp [actualMean,nominalSelf] <;> ring
  · convert hm using 1 <;> dsimp [actualMean,nominalMixed] <;> ring

lemma self_mean_error (hinj : Function.Injective (fun a : G ↦ a+a))
    (C : Finset G) (θ η : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hη : 0 ≤ η)
    (hC : ∀ z, |(count C C z : ℝ)-actualMean C C| ≤ η*actualMean C C) (z : G) :
    |selfMean z (extendProb C θ)-nominalSelf C θ| ≤ η*nominalSelf C θ+1 := by
  have hd := diagCorrection_bounds hinj z (extendProb C θ) (extendProb_bounds C θ hθ hθ1)
  have he : selfMean z (extendProb C θ)-nominalSelf C θ =
      (1-θ)^2*((count C C z : ℝ)-actualMean C C)+diagCorrection z (extendProb C θ) := by
    rw [self_extendProb,nominal_self_identity]
    ring
  rw [he]
  calc
    _ ≤ |(1-θ)^2*((count C C z : ℝ)-actualMean C C)|+|diagCorrection z (extendProb C θ)| := abs_add_le _ _
    _ = (1-θ)^2*|(count C C z : ℝ)-actualMean C C|+diagCorrection z (extendProb C θ) := by
      rw [abs_mul,abs_of_nonneg (sq_nonneg _),abs_of_nonneg hd.1]
    _ ≤ (1-θ)^2*(η*actualMean C C)+1 :=
      add_le_add (mul_le_mul_of_nonneg_left (hC z) (sq_nonneg _)) hd.2
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (old_mean_le_nominal C C θ hθ hθ1).1 hη
      nlinarith

lemma mixed_mean_error (A C : Finset G) (θ η : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hη : 0 ≤ η)
    (hAC : ∀ z, |(count A C z : ℝ)-actualMean A C| ≤ η*actualMean A C) (z : G) :
    |(∑ a∈A, extendProb C θ (z-a))-nominalMixed A C θ| ≤ η*nominalMixed A C θ := by
  have he : (∑ a∈A, extendProb C θ (z-a))-nominalMixed A C θ =
      (1-θ)*((count A C z : ℝ)-actualMean A C) := by
    rw [mixed_extendProb,nominal_mixed_identity]
    ring
  rw [he,abs_mul,abs_of_nonneg (sub_nonneg.mpr hθ1)]
  calc
    _ ≤ (1-θ)*(η*actualMean A C) := mul_le_mul_of_nonneg_left (hAC z) (sub_nonneg.mpr hθ1)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (old_mean_le_nominal A C θ hθ hθ1).2 hη
      nlinarith

/-- A controlled denser superset, including every old point. The three mean
conditions and the exponential criterion are explicit; no uniform existence
in the critical small-mean regime is inferred. -/
theorem exists_dense_extension_nominal (hinj : Function.Injective (fun a : G ↦ a+a))
    (C : Finset G) (H : ℕ) (A : Fin H → Finset G) (θ ε v : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1/4)
    (hC : ∀ z, |(count C C z : ℝ)-actualMean C C| ≤ ε*actualMean C C)
    (hAC : ∀ i z, |(count (A i) C z : ℝ)-actualMean (A i) C| ≤ ε*actualMean (A i) C)
    (hlarge : 1 ≤ ε*nominalSelf C θ)
    (hvs : v ≤ nominalSelf C θ) (hvm : ∀ i, v ≤ nominalMixed (A i) C θ)
    (hvc : v ≤ expectedCard C θ)
    (hsmall : 2*((H+1)*Fintype.card G+1)*Real.exp (-ε^2*v/8) < 1) :
    ∃ B : Finset G, C ⊆ B ∧
      (∀ z, |(count B B z : ℝ)-nominalSelf C θ| < 4*ε*nominalSelf C θ) ∧
      (∀ i z, |(count (A i) B z : ℝ)-nominalMixed (A i) C θ| < 3*ε*nominalMixed (A i) C θ) ∧
      |(B.card : ℝ)-expectedCard C θ| < ε*expectedCard C θ := by
  have hself := self_mean_error hinj C θ ε hθ hθ1 hε.le hC
  have hmix := fun i ↦ mixed_mean_error (A i) C θ ε hθ hθ1 hε.le (hAC i)
  have hn := (nominal_nonneg C C θ hθ hθ1).1
  have hmn := fun i ↦ (nominal_nonneg (A i) C θ hθ hθ1).2
  obtain ⟨B,hCB,hB,hAB,hcard⟩ := exists_extension_about_means C H A θ ε v
    ((1+ε)*nominalSelf C θ+1) (expectedCard C θ)
    (fun i ↦ (1+ε)*nominalMixed (A i) C θ) hθ hθ1 hε (by linarith)
    (fun z ↦ by have := (abs_le.mp (hself z)).2; linarith)
    (fun i z ↦ by have := (abs_le.mp (hmix i z)).2; linarith)
    le_rfl (by nlinarith) (fun i ↦ by have := hmn i; have := hvm i; nlinarith) hvc hsmall
  refine ⟨B,hCB,?_,?_,hcard⟩
  · intro z
    have hh := (abs_sub_le (count B B z : ℝ) (selfMean z (extendProb C θ)) (nominalSelf C θ)).trans_lt
      (add_lt_add_of_lt_of_le (hB z) (hself z))
    have hmul := mul_le_mul_of_nonneg_left hlarge hε.le
    have hsmallε := mul_le_mul_of_nonneg_right hε1 (mul_nonneg hε.le hn)
    nlinarith
  · intro i z
    have hh := (abs_sub_le (count (A i) B z : ℝ) (∑ a∈A i, extendProb C θ (z-a))
      (nominalMixed (A i) C θ)).trans_lt (add_lt_add_of_lt_of_le (hAB i z) (hmix i z))
    have hsmallε := mul_le_mul_of_nonneg_right (show ε ≤ 1 by linarith)
      (mul_nonneg hε.le (hmn i))
    nlinarith

lemma cardinality_mean_stability (A B C : Finset G) (θ ε : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/2)
    (hcard : |(B.card : ℝ)-expectedCard C θ| ≤ ε*expectedCard C θ) :
    |actualMean B B-nominalSelf C θ| ≤ 3*ε*nominalSelf C θ ∧
    nominalSelf C θ ≤ 4*actualMean B B ∧
    |actualMean A B-nominalMixed A C θ| ≤ ε*nominalMixed A C θ ∧
    nominalMixed A C θ ≤ 2*actualMean A B := by
  let a : ℝ := B.card
  let b := expectedCard C θ
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hb : 0 ≤ b := (expectedCard_bounds C θ hθ hθ1).1
  have hcb : |a-b| ≤ ε*b := hcard
  have habs := abs_le.mp hcb
  have hsmall := mul_le_mul_of_nonneg_right hε1 hb
  have hab : a ≤ 2*b := by linarith
  have hba : b ≤ 2*a := by linarith
  have hs : |a*a-b^2| ≤ 3*ε*b^2 := by
    calc
      _ = |a-b| *(a+b) := by
        rw [←abs_of_nonneg (add_nonneg ha hb),←abs_mul]
        congr 1
        ring
      _ ≤ (ε*b)*(3*b) := mul_le_mul hcb (by linarith) (by positivity) (by positivity)
      _ = _ := by ring
  have hs' : b^2 ≤ 4*(a*a) := by
    have hh := pow_le_pow_left₀ hb hba 2
    nlinarith
  have hn := card_group_pos (G := G)
  have hdiv := div_le_div_of_nonneg_right hs hn.le
  have hdiv' := div_le_div_of_nonneg_right hs' hn.le
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcb (Nat.cast_nonneg (α := ℝ) A.card)) hn.le
  have hm' := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hba (Nat.cast_nonneg (α := ℝ) A.card)) hn.le
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [actualMean,nominalSelf]
    rw [←sub_div,abs_div,abs_of_pos hn]
    convert hdiv using 1 <;> dsimp [a,b] <;> ring
  · convert hdiv' using 1 <;> dsimp [actualMean,nominalSelf,a,b] <;> ring
  · dsimp [actualMean,nominalMixed]
    rw [←sub_div,←mul_sub,abs_div,abs_mul,abs_of_pos hn,abs_of_nonneg (Nat.cast_nonneg _)]
    convert hm using 1 <;> dsimp [a,b] <;> ring
  · convert hm' using 1 <;> dsimp [actualMean,nominalMixed,a,b] <;> ring

/-- The same extension normalized by its actual cardinality. This output is
suitable for adjoining one member to a finite mixed-flat palette. -/
theorem exists_dense_extension_actual (hinj : Function.Injective (fun a : G ↦ a+a))
    (C : Finset G) (H : ℕ) (A : Fin H → Finset G) (θ ε v : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1/4)
    (hC : ∀ z, |(count C C z : ℝ)-actualMean C C| ≤ ε*actualMean C C)
    (hAC : ∀ i z, |(count (A i) C z : ℝ)-actualMean (A i) C| ≤ ε*actualMean (A i) C)
    (hlarge : 1 ≤ ε*nominalSelf C θ)
    (hvs : v ≤ nominalSelf C θ) (hvm : ∀ i, v ≤ nominalMixed (A i) C θ)
    (hvc : v ≤ expectedCard C θ)
    (hsmall : 2*((H+1)*Fintype.card G+1)*Real.exp (-ε^2*v/8) < 1) :
    ∃ B : Finset G, C ⊆ B ∧
      (∀ z, |(count B B z : ℝ)-actualMean B B| < 28*ε*actualMean B B) ∧
      (∀ i z, |(count (A i) B z : ℝ)-actualMean (A i) B| < 8*ε*actualMean (A i) B) ∧
      |(B.card : ℝ)-expectedCard C θ| < ε*expectedCard C θ := by
  obtain ⟨B,hCB,hB,hAB,hcard⟩ := exists_dense_extension_nominal hinj C H A θ ε v hθ hθ1 hε hε1
    hC hAC hlarge hvs hvm hvc hsmall
  refine ⟨B,hCB,?_,?_,hcard⟩
  · intro z
    have hs := cardinality_mean_stability C B C θ ε hθ hθ1 hε.le (by linarith) hcard.le
    have hh := (abs_sub_le (count B B z : ℝ) (nominalSelf C θ) (actualMean B B)).trans_lt
      (add_lt_add_of_lt_of_le (hB z) (by simpa only [abs_sub_comm] using hs.1))
    have hm := mul_le_mul_of_nonneg_left hs.2.1 (show 0 ≤ 7*ε by positivity)
    nlinarith
  · intro i z
    have hs := cardinality_mean_stability (A i) B C θ ε hθ hθ1 hε.le (by linarith) hcard.le
    have hh := (abs_sub_le (count (A i) B z : ℝ) (nominalMixed (A i) C θ) (actualMean (A i) B)).trans_lt
      (add_lt_add_of_lt_of_le (hAB i z) (by simpa only [abs_sub_comm] using hs.2.2.1))
    have hm := mul_le_mul_of_nonneg_left hs.2.2.2 (show 0 ≤ 4*ε by positivity)
    nlinarith

end Erdos66DenseGroupExtension
