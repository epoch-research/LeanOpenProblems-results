import FormalConjecturesUtil

/-! Translation of real multivariate polynomials preserves total degree, while
its nonzero finite difference has strictly smaller total degree. -/
namespace Erdos952Investigation.MvPolynomialTranslation
open MvPolynomial
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

variable {σ : Type*}

def translate (d : σ → ℝ) : MvPolynomial σ ℝ →+* MvPolynomial σ ℝ :=
  eval₂Hom C (fun i => X i + C (d i))

@[simp] lemma translate_C (d : σ → ℝ) (c : ℝ) : translate d (C c) = C c := by
  simp [translate]

@[simp] lemma translate_X (d : σ → ℝ) (i : σ) : translate d (X i) = X i+C (d i) := by
  simp [translate]

lemma eval_translate (d z : σ → ℝ) (p : MvPolynomial σ ℝ) :
    eval z (translate d p) = eval (fun i => z i+d i) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp]

lemma translate_translate (d e : σ → ℝ) (p : MvPolynomial σ ℝ) :
    translate d (translate e p) = translate (fun i => d i+e i) p := by
  apply MvPolynomial.funext
  intro z
  simp only [eval_translate,add_assoc]

@[simp] lemma translate_zero (p : MvPolynomial σ ℝ) : translate (fun _ => 0) p = p := by
  apply MvPolynomial.funext
  intro z
  simp only [eval_translate,add_zero]

lemma translate_injective (d : σ → ℝ) : Function.Injective (translate d) := by
  intro p q h
  have hh := congrArg (translate (fun i => -d i)) h
  simpa only [translate_translate,neg_add_cancel,translate_zero] using hh

lemma translate_ne_zero (d : σ → ℝ) {p : MvPolynomial σ ℝ} (hp : p ≠ 0) :
    translate d p ≠ 0 := by
  intro h
  apply hp
  apply translate_injective d
  simpa using h

lemma totalDegree_monomial_add (a : σ →₀ ℕ) (b : ℝ) (p : MvPolynomial σ ℝ)
    (ha : a ∉ p.support) (hb : b ≠ 0) :
    (monomial a b+p).totalDegree = max (monomial a b).totalDegree p.totalDegree := by
  classical
  have hdis : Disjoint (monomial a b : MvPolynomial σ ℝ).support p.support := by
    simpa only [support_monomial,if_neg hb,Finset.disjoint_singleton_left] using ha
  change ((monomial a b+p).support.sup _) = _
  have he : (monomial a b+p).support =
      (monomial a b : MvPolynomial σ ℝ).support ∪ p.support :=
    Finsupp.support_add_eq hdis
  rw [he,Finset.sup_union]
  rfl

lemma translation_degree_bounds (d : σ → ℝ) (p : MvPolynomial σ ℝ) :
    (translate d p).totalDegree ≤ p.totalDegree ∧
      (translate d p-p = 0 ∨ (translate d p-p).totalDegree < p.totalDegree) := by
  classical
  induction p using MvPolynomial.induction_on'' with
  | C c => simp
  | monomial_add a b p ha hb hp hm =>
    have hd := totalDegree_monomial_add a b p ha hb
    constructor
    · rw [map_add,hd]
      exact (totalDegree_add _ _).trans (max_le_max hm.1 hp.1)
    · have he : translate d (monomial a b+p)-(monomial a b+p) =
          (translate d (monomial a b)-monomial a b)+(translate d p-p) := by
        rw [map_add]; ring
      rw [he,hd]
      rcases hm.2 with hm0 | hmd <;> rcases hp.2 with hp0 | hpd
      · exact Or.inl (by rw [hm0,hp0,zero_add])
      · exact Or.inr (by rw [hm0,zero_add]; exact hpd.trans_le (le_max_right _ _))
      · exact Or.inr (by rw [hp0,add_zero]; exact hmd.trans_le (le_max_left _ _))
      · exact Or.inr ((totalDegree_add _ _).trans_lt
          (max_lt (hmd.trans_le (le_max_left _ _)) (hpd.trans_le (le_max_right _ _))))
  | mul_X p i hp =>
    by_cases hp0 : p = 0
    · simp [hp0]
    have hdeg : (p*X i).totalDegree = p.totalDegree+1 := by
      rw [totalDegree_mul_of_isDomain hp0 (X_ne_zero i),totalDegree_X]
    have hX : (X i+C (d i) : MvPolynomial σ ℝ).totalDegree ≤ 1 := by
      simpa using totalDegree_add (X i : MvPolynomial σ ℝ) (C (d i))
    constructor
    · rw [map_mul,translate_X,hdeg]
      exact (totalDegree_mul _ _).trans (Nat.add_le_add hp.1 hX)
    · have he : translate d (p*X i)-p*X i =
          (translate d p-p)*(X i+C (d i))+p*C (d i) := by
        rw [map_mul,translate_X]; ring
      have hpc : (p*C (d i)).totalDegree ≤ p.totalDegree := by
        simpa using totalDegree_mul p (C (d i))
      rw [he,hdeg]
      right
      rcases hp.2 with hp0 | hpd
      · rw [hp0,zero_mul,zero_add]
        omega
      · apply (totalDegree_add _ _).trans_lt
        apply max_lt
        · exact (totalDegree_mul _ _).trans_lt (by omega)
        · omega

lemma totalDegree_translate (d : σ → ℝ) (p : MvPolynomial σ ℝ) :
    (translate d p).totalDegree = p.totalDegree := by
  apply le_antisymm (translation_degree_bounds d p).1
  have hh := (translation_degree_bounds (fun i => -d i) (translate d p)).1
  simpa only [translate_translate,neg_add_cancel,translate_zero] using hh

lemma totalDegree_difference_lt (d : σ → ℝ) (p : MvPolynomial σ ℝ)
    (h : translate d p-p ≠ 0) : (translate d p-p).totalDegree < p.totalDegree :=
  (translation_degree_bounds d p).2.resolve_left h

#print axioms totalDegree_difference_lt
#print axioms totalDegree_translate
end
end Erdos952Investigation.MvPolynomialTranslation
