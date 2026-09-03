import Submission.SupportTailIteration

/-! Lower laws on a finite set of support states. Missing states and missing
geometric increments are charged via the full moment, not discarded losses. -/
namespace Erdos7SupportLowerLaw
open scoped BigOperators
open Erdos7SupportCompression Erdos7SupportTailIteration Erdos7SupportPolynomialTail
open Erdos7CompressionSieve
set_option autoImplicit false
set_option maxHeartbeats 3000000

lemma tripleUpdate_injective (a : ℕ) : Function.Injective (tripleUpdate a) := by
  intro x y h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [tripleUpdate] at h₁ h₂
  have he : x.1=y.1 := by omega
  rw [he] at h₂
  exact Prod.ext he (by omega)

lemma tripleStep_apply (E : ℕ) (q : ℕ → ℚ) (μ : TripleState →₀ ℚ) (x : TripleState) :
    tripleStep E q μ x=(1-q 0)*μ x+
      ∑ g ∈ Finset.range E,(q g-q (g+1))*(μ.mapDomain (tripleUpdate (g+1))) x := by
  simp only [tripleStep,Finsupp.add_apply,Finsupp.smul_apply,Finsupp.coe_finset_sum,
    Finset.sum_apply,smul_eq_mul]

lemma tripleStep_mono (E : ℕ) (q : ℕ → ℚ) (hq₀ : q 0 ≤ 1)
    (hq : ∀ g, g < E → q (g+1) ≤ q g) {μ ν : TripleState →₀ ℚ} (h : μ ≤ ν) :
    tripleStep E q μ ≤ tripleStep E q ν := by
  intro x
  rw [tripleStep_apply,tripleStep_apply]
  apply add_le_add (mul_le_mul_of_nonneg_left (h x) (by linarith))
  apply Finset.sum_le_sum
  intro g hg
  exact mul_le_mul_of_nonneg_left ((Finsupp.mapDomain_mono h) x)
    (sub_nonneg.mpr (hq g (Finset.mem_range.mp hg)))

lemma tripleStep_nonneg (E : ℕ) (q : ℕ → ℚ) (hq₀ : q 0 ≤ 1)
    (hq : ∀ g, g < E → q (g+1) ≤ q g) (μ : TripleState →₀ ℚ) (hμ : 0 ≤ μ) :
    0 ≤ tripleStep E q μ := by
  have h := tripleStep_mono E q hq₀ hq hμ
  simpa [tripleStep] using h

lemma tripleStep_mass (E : ℕ) (q : ℕ → ℚ) (hq : q E=0) (μ : TripleState →₀ ℚ) :
    pairExpect (tripleStep E q μ) (fun _ => 1)=pairExpect μ (fun _ => 1) := by
  rw [← pairExpect_op]
  simp only [op_const E q hq 1]

lemma triplePrefixLaw_nonneg {n : ℕ} (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ)
    (hq₀ : ∀ i, q i 0 ≤ 1) (hq : ∀ i g, g < E i → q i (g+1) ≤ q i g) (t : ℕ) :
    0 ≤ triplePrefixLaw E q t := by
  induction t with
  | zero => simp only [triplePrefixLaw,tripleInitial]; exact Finsupp.single_nonneg.mpr (by norm_num)
  | succ t ih =>
    simp only [triplePrefixLaw]
    split_ifs with h
    · exact tripleStep_nonneg _ _ (hq₀ _) (hq _) _ ih
    · exact ih

lemma triplePrefixLaw_mass {n : ℕ} (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ)
    (hq : ∀ i, q i (E i)=0) (t : ℕ) : pairExpect (triplePrefixLaw E q t) (fun _ => 1)=1 := by
  induction t with
  | zero => simp only [triplePrefixLaw,pairExpect_initial]
  | succ t ih =>
    simp only [triplePrefixLaw]
    split_ifs
    · rw [tripleStep_mass _ _ (hq _),ih]
    · exact ih

noncomputable def encode {I : Type*} [Fintype I] (repr : I → TripleState) (D : I → ℚ) :
    TripleState →₀ ℚ := (Finsupp.equivFunOnFinite.symm D).mapDomain repr

lemma encode_apply {I : Type*} [Fintype I] (repr : I → TripleState) (hinj : Function.Injective repr)
    (D : I → ℚ) (i : I) : encode repr D (repr i)=D i := by
  exact Finsupp.mapDomain_apply hinj _ i

lemma encode_nonneg {I : Type*} [Fintype I] (repr : I → TripleState) (D : I → ℚ)
    (hD : ∀ i, 0 ≤ D i) : 0 ≤ encode repr D :=
  Finsupp.mapDomain_nonneg (fun i => hD i)

lemma encode_notin_range {I : Type*} [Fintype I] (repr : I → TripleState) (D : I → ℚ)
    (x : TripleState) (hx : x ∉ Set.range repr) : encode repr D x=0 :=
  Finsupp.mapDomain_notin_range _ _ hx

lemma pairExpect_encode {I : Type*} [Fintype I] (repr : I → TripleState) (D : I → ℚ)
    (f : TripleState → ℚ) : pairExpect (encode repr D) f=∑ i,D i*f (repr i) := by
  unfold pairExpect encode
  rw [Finsupp.sum_mapDomain_index (by intros; simp) (by intros; ring)]
  rw [Finsupp.sum_fintype _ _ (by intros; simp)]
  simp only [Finsupp.equivFunOnFinite_symm_apply_apply]

lemma encode_le_iff {I : Type*} [Fintype I] (repr : I → TripleState) (hinj : Function.Injective repr)
    (D : I → ℚ) (μ : TripleState →₀ ℚ) (hμ : 0 ≤ μ) :
    encode repr D ≤ μ ↔ ∀ i,D i ≤ μ (repr i) := by
  constructor
  · intro h i
    simpa only [encode_apply repr hinj] using h (repr i)
  · intro h x
    by_cases hx : x ∈ Set.range repr
    · obtain ⟨i,rfl⟩ := hx
      simpa only [encode_apply repr hinj] using h i
    · rw [encode_notin_range repr D x hx]
      exact hμ x

lemma pred_bound {I : Type*} [Fintype I] (repr : I → TripleState) (hinj : Function.Injective repr)
    (D : I → ℚ) (hD : ∀ i, 0 ≤ D i) (a : ℕ) (j : I) (pred : Option I)
    (hpred : ∀ k, pred=some k → tripleUpdate a (repr k)=repr j) :
    pred.elim 0 D ≤ ((encode repr D).mapDomain (tripleUpdate a)) (repr j) := by
  cases pred with
  | none => exact (Finsupp.mapDomain_nonneg (encode_nonneg repr D hD)) (repr j)
  | some k =>
    have he := hpred k rfl
    rw [← he,Finsupp.mapDomain_apply (tripleUpdate_injective a),encode_apply repr hinj]
    rfl

lemma powerTail_difference (p E a : ℕ) (hp : 0 < p) (ha : a+1 < E) (c : ℚ) :
    powerTail p c E a-powerTail p c E (a+1)=c*((p:ℚ)-1)/(p:ℚ)^(a+2) := by
  have hpQ : (p:ℚ)≠0 := by exact_mod_cast hp.ne'
  simp only [powerTail,if_pos ha,if_pos (show a < E by omega)]
  rw [inv_pow,inv_pow]
  rw [show a+2=(a+1)+1 by omega,pow_succ]
  field_simp
  <;> ring

/-- A row may keep just one predecessor at each retained increment. No
claim that the retained law has full mass is made. -/
theorem lower_step {I : Type*} [Fintype I] (repr : I → TripleState)
    (hinj : Function.Injective repr) (D D' : I → ℚ) (hD : ∀ i, 0 ≤ D i)
    (p E T : ℕ) (hp : 1 < p) (hT : T < E) (c : ℚ) (hc : 0 ≤ c) (hcp : c ≤ p)
    (pred : I → Fin T → Option I)
    (hpred : ∀ j a k, pred j a=some k → tripleUpdate (a.val+1) (repr k)=repr j)
    (hrow : ∀ j,D' j ≤ (1-c/(p:ℚ))*D j+
      ∑ a : Fin T,c*((p:ℚ)-1)/(p:ℚ)^(a.val+2)*(pred j a).elim 0 D) :
    encode repr D' ≤ tripleStep E (powerTail p c E) (encode repr D) := by
  have hq0 := powerTail_zero_le_one p hp c hcp E
  have hdec := powerTail_decreasing p hp c hc E
  have henc := encode_nonneg repr D hD
  have hn := tripleStep_nonneg E _ hq0 (fun g _ => hdec g) _ henc
  apply (encode_le_iff repr hinj D' _ hn).mpr
  intro j
  apply (hrow j).trans
  rw [tripleStep_apply,encode_apply repr hinj]
  have he0 : powerTail p c E 0=c/(p:ℚ) := by
    simp only [powerTail,if_pos (show 0 < E by omega),Nat.zero_add,pow_one,div_eq_mul_inv]
  rw [he0]
  apply add_le_add le_rfl
  have hsum : (∑ a : Fin T,c*((p:ℚ)-1)/(p:ℚ)^(a.val+2)*(pred j a).elim 0 D) ≤
      ∑ a : Fin T,(powerTail p c E a.val-powerTail p c E (a.val+1))*
        ((encode repr D).mapDomain (tripleUpdate (a.val+1))) (repr j) := by
    apply Finset.sum_le_sum
    intro a _
    rw [powerTail_difference p E a.val (by omega) (by have := a.isLt; omega)]
    apply mul_le_mul_of_nonneg_left (pred_bound repr hinj D hD _ j _ (hpred j a))
    have hpQ : (1:ℚ) < p := by exact_mod_cast hp
    have hm : 0 ≤ (p:ℚ)-1 := by linarith
    positivity
  apply hsum.trans
  rw [Fin.sum_univ_eq_sum_range (fun a => (powerTail p c E a-powerTail p c E (a+1))*
    ((encode repr D).mapDomain (tripleUpdate (a+1))) (repr j)) T]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_of_lt hT))
  intro a ha _
  exact mul_nonneg (sub_nonneg.mpr (hdec a))
    ((Finsupp.mapDomain_nonneg henc) (repr j))

#print axioms triplePrefixLaw_mass
#print axioms lower_step
end Erdos7SupportLowerLaw
