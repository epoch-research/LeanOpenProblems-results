import FormalConjecturesUtil

/-!
A pair-incidence Gram bound for exact fourth-order designs. Exact uniformity
is much stronger than the bounded multiplicities in Erdős 714; this file does
not settle that conjecture or rule out general partial packings.
-/
noncomputable section
open Finset Matrix Classical
set_option maxHeartbeats 2000000
namespace Erdos714ExactDesign

/-- A positive identity contribution to a Gram decomposition forces full
column rank. The other two Gram contributions only need nonnegative weights. -/
theorem gram_rank_bound {A I V : Type*} [Fintype A] [Fintype I] [Fintype V] [DecidableEq I]
    (M : Matrix A I ℝ) (Z : Matrix V I ℝ) (O : Matrix Unit I ℝ)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hM : Mᵀ*M = a • (1 : Matrix I I ℝ)+b • (Zᵀ*Z)+c • (Oᵀ*O)) :
    Fintype.card I ≤ Fintype.card A := by
  have hZ : (Zᵀ*Z).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self Z
  have hO : (Oᵀ*O).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self O
  have hp : (Mᵀ*M).PosDef := by
    rw [hM]
    exact ((Matrix.PosDef.one.smul ha).add_posSemidef (hZ.smul hb)).add_posSemidef (hO.smul hc)
  have hfull := Matrix.rank_of_isUnit (Mᵀ*M) hp.isUnit
  rw [Matrix.rank_transpose_mul_self] at hfull
  rw [← hfull]
  exact Matrix.rank_le_card_height M

variable {A V : Type*} [Fintype A] [Fintype V]

/-- The number of indexed blocks containing a finite point set, viewed in ℝ. -/
def coverage (S : A → Finset V) (T : Finset V) : ℝ :=
  ∑ a : A, if T ⊆ S a then 1 else 0

abbrev Pair (V : Type*) [Fintype V] := ((univ : Finset V).powersetCard 2)

lemma pair_card (p : Pair V) : p.val.card = 2 := (mem_powersetCard.mp p.property).2

def pairMatrix (S : A → Finset V) : Matrix A (Pair V) ℝ :=
  fun a p => if p.val ⊆ S a then 1 else 0

def pointMatrix : Matrix V (Pair V) ℝ := fun v p => if v ∈ p.val then 1 else 0

def onesMatrix : Matrix Unit (Pair V) ℝ := fun _ _ => 1

lemma pair_gram (S : A → Finset V) (p q : Pair V) :
    ((pairMatrix S)ᵀ*pairMatrix S) p q = coverage S (p.val ∪ q.val) := by
  unfold pairMatrix coverage
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply sum_congr rfl
  intro a _
  by_cases hp : p.val ⊆ S a <;> by_cases hq : q.val ⊆ S a <;> simp [hp,hq,union_subset_iff]

lemma point_gram (p q : Pair V) :
    ((pointMatrix (V := V))ᵀ*(pointMatrix (V := V))) p q = ((p.val ∩ q.val).card : ℝ) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pointMatrix]
  have hi (v : V) : (if v ∈ p.val then (1 : ℝ) else 0)*(if v ∈ q.val then 1 else 0) =
      if v ∈ p.val ∩ q.val then 1 else 0 := by
    by_cases hp : v ∈ p.val <;> by_cases hq : v ∈ q.val <;> simp [hp,hq]
  simp_rw [hi]
  simp only [sum_boole]
  congr 2
  ext v
  simp

lemma ones_gram (p q : Pair V) :
    ((onesMatrix (V := V))ᵀ*(onesMatrix (V := V))) p q = 1 := by simp [Matrix.mul_apply,onesMatrix]

lemma pair_union_cases (p q : Pair V) (hpq : p ≠ q) :
    (p.val ∪ q.val).card = 3 ∨ (p.val ∪ q.val).card = 4 := by
  have hp := pair_card p
  have hq := pair_card q
  have hl := card_le_card (subset_union_left (s₁ := p.val) (s₂ := q.val))
  have hu := card_union_le p.val q.val
  have hn : (p.val ∪ q.val).card ≠ 2 := by
    intro h
    have hp' := eq_of_subset_of_card_le (subset_union_left (s₁ := p.val) (s₂ := q.val)) (by omega)
    have hq' := eq_of_subset_of_card_le (subset_union_right (s₁ := p.val) (s₂ := q.val)) (by omega)
    exact hpq (Subtype.ext (hp'.trans hq'.symm))
  omega

/-- Uniform counts for pairs, triples, and quadruples determine the whole
pair-incidence Gram matrix. Repeated indexed blocks are still counted. -/
lemma pair_gram_decomposition (S : A → Finset V) (l₂ l₃ l₄ : ℝ)
    (h₂ : ∀ T : Finset V, T.card = 2 → coverage S T = l₂)
    (h₃ : ∀ T : Finset V, T.card = 3 → coverage S T = l₃)
    (h₄ : ∀ T : Finset V, T.card = 4 → coverage S T = l₄) :
    (pairMatrix S)ᵀ*pairMatrix S = (l₂-2*l₃+l₄) • (1 : Matrix (Pair V) (Pair V) ℝ)+
      (l₃-l₄) • ((pointMatrix (V := V))ᵀ*(pointMatrix (V := V)))+
      l₄ • ((onesMatrix (V := V))ᵀ*(onesMatrix (V := V))) := by
  ext p q
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, pair_gram, point_gram, ones_gram,
    Matrix.one_apply]
  by_cases hpq : p = q
  · subst q
    rw [union_self, inter_self, pair_card, h₂ p.val (pair_card p), if_pos rfl]
    norm_num
    ring
  · rw [if_neg hpq]
    have hcard := card_union_add_card_inter p.val q.val
    rw [pair_card p, pair_card q] at hcard
    rcases pair_union_cases p q hpq with h | h
    · have hi : (p.val ∩ q.val).card = 1 := by omega
      rw [h₃ _ h, hi]
      norm_num
    · have hi : (p.val ∩ q.val).card = 0 := by omega
      rw [h₄ _ h, hi]
      norm_num

/-- The second-order Fisher bound, under explicit uniformity and positivity
conditions. It does not follow merely from fourth-order coverage <=3. -/
theorem pair_fisher_bound (S : A → Finset V) (l₂ l₃ l₄ : ℝ)
    (h₂ : ∀ T : Finset V, T.card = 2 → coverage S T = l₂)
    (h₃ : ∀ T : Finset V, T.card = 3 → coverage S T = l₃)
    (h₄ : ∀ T : Finset V, T.card = 4 → coverage S T = l₄)
    (ha : 0 < l₂-2*l₃+l₄) (hb : 0 ≤ l₃-l₄) (hc : 0 ≤ l₄) :
    (Fintype.card V).choose 2 ≤ Fintype.card A := by
  have h := gram_rank_bound (pairMatrix S) pointMatrix onesMatrix
    _ _ _ ha hb hc (pair_gram_decomposition S l₂ l₃ l₄ h₂ h₃ h₄)
  simpa only [Fintype.card_coe, card_powersetCard, card_univ] using h

omit [Fintype V] in
lemma coverage_eq_card (S : A → Finset V) (T : Finset V) :
    coverage S T = (Fintype.card {a : A // T ⊆ S a} : ℝ) := by
  simp [coverage, Fintype.card_subtype]

/-- Count one-point extensions of a covered set in two orders. -/
def extensionEquiv (S : A → Finset V) (T : Finset V) :
    (Σ a : {a : A // T ⊆ S a}, {x : V // x ∈ S a.val \ T}) ≃
      (Σ x : {x : V // x ∉ T}, {a : A // insert x.val T ⊆ S a}) where
  toFun p := ⟨⟨p.2.val,(mem_sdiff.mp p.2.property).2⟩,
    ⟨p.1.val,insert_subset_iff.mpr ⟨(mem_sdiff.mp p.2.property).1,p.1.property⟩⟩⟩
  invFun p := ⟨⟨p.2.val,(insert_subset_iff.mp p.2.property).2⟩,
    ⟨p.1.val,mem_sdiff.mpr ⟨(insert_subset_iff.mp p.2.property).1,p.1.property⟩⟩⟩
  left_inv p := by rcases p with ⟨⟨a,ha⟩,⟨x,hx⟩⟩; rfl
  right_inv p := by rcases p with ⟨⟨x,hx⟩,⟨a,ha⟩⟩; rfl

/-- Uniform coverage at order s+1 descends by exact double counting. -/
theorem uniform_downward (S : A → Finset V) (k s : ℕ) (l : ℝ)
    (hk : ∀ a, (S a).card = k)
    (hstep : ∀ U : Finset V, U.card = s+1 → coverage S U = l)
    (T : Finset V) (hT : T.card = s) :
    ((k-s : ℕ) : ℝ)*coverage S T = ((Fintype.card V-s : ℕ) : ℝ)*l := by
  have hdiff (a : {a : A // T ⊆ S a}) :
      Fintype.card {x : V // x ∈ S a.val \ T} = k-s := by
    rw [Fintype.card_subtype]
    simp only [filter_mem_eq_inter, univ_inter, card_sdiff, inter_eq_left.mpr a.property, hk, hT]
  have hnext (x : {x : V // x ∉ T}) :
      (Fintype.card {a : A // insert x.val T ⊆ S a} : ℝ) = l := by
    rw [← coverage_eq_card]
    exact hstep _ (by rw [card_insert_of_notMem x.property,hT])
  have hout : Fintype.card {x : V // x ∉ T} = Fintype.card V-s := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_coe, hT]
  have h := congrArg (fun n : ℕ => (n : ℝ)) (Fintype.card_congr (extensionEquiv S T))
  simp only [Fintype.card_sigma, Nat.cast_sum] at h
  simp_rw [hdiff, hnext] at h
  simpa only [sum_const, card_univ, nsmul_eq_mul, hout, coverage_eq_card, mul_comm] using h

/-- The Ray-Chaudhuri--Wilson bound for an exact fourth-order design, proved
here via its pair-incidence Gram matrix. It requires *equal* coverage of
all quadruples, not merely a uniform upper bound. -/
theorem fourth_design_block_bound (S : A → Finset V) (k : ℕ) (l : ℝ)
    (hk : ∀ a, (S a).card = k) (hk4 : 4 ≤ k) (hkv : k+2 ≤ Fintype.card V)
    (hl : 0 < l) (h₄ : ∀ T : Finset V, T.card = 4 → coverage S T = l) :
    (Fintype.card V).choose 2 ≤ Fintype.card A := by
  let v : ℝ := Fintype.card V
  let l₃ : ℝ := l*(v-3)/((k : ℝ)-3)
  let l₂ : ℝ := l₃*(v-2)/((k : ℝ)-2)
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk4
  have hkvR : (k : ℝ)+2 ≤ v := by dsimp [v]; exact_mod_cast hkv
  have hk3 : (0 : ℝ) < k-3 := by linarith
  have hk2 : (0 : ℝ) < k-2 := by linarith
  have hvk : 0 < v-k := by linarith
  have hvk1 : 0 < v-k-1 := by linarith
  have h₃ (T : Finset V) (hT : T.card = 3) : coverage S T = l₃ := by
    have h := uniform_downward S k 3 l hk (by simpa using h₄) T hT
    rw [Nat.cast_sub (by omega : 3 ≤ k), Nat.cast_sub (by omega : 3 ≤ Fintype.card V)] at h
    change ((k : ℝ)-3)*coverage S T = (v-3)*l at h
    exact (eq_div_iff hk3.ne').mpr (by nlinarith [h])
  have h₂ (T : Finset V) (hT : T.card = 2) : coverage S T = l₂ := by
    have h := uniform_downward S k 2 l₃ hk (by simpa using h₃) T hT
    rw [Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_sub (by omega : 2 ≤ Fintype.card V)] at h
    change ((k : ℝ)-2)*coverage S T = (v-2)*l₃ at h
    exact (eq_div_iff hk2.ne').mpr (by nlinarith [h])
  have ha : l₂-2*l₃+l = l*(v-k)*(v-k-1)/(((k : ℝ)-2)*((k : ℝ)-3)) := by
    dsimp [l₂,l₃]
    field_simp
    ring
  have hb : l₃-l = l*(v-k)/((k : ℝ)-3) := by
    dsimp [l₃]
    field_simp
    ring
  apply pair_fisher_bound S l₂ l₃ l h₂ h₃ h₄
  · rw [ha]
    exact div_pos (mul_pos (mul_pos hl hvk) hvk1) (mul_pos hk2 hk3)
  · rw [hb]
    exact (div_pos (mul_pos hl hvk) hk3).le
  · exact hl.le

/-- A nontrivial exact fourth-order design cannot have at most as many
indexed blocks as points. This remains distinct from a partial packing. -/
theorem not_balanced_exact_design (S : A → Finset V) (k : ℕ)
    (hk : ∀ a, (S a).card = k) (hk4 : 4 ≤ k) (hkv : k+2 ≤ Fintype.card V)
    (hA : Fintype.card A ≤ Fintype.card V) :
    ¬ ∃ l : ℝ, 0 < l ∧ ∀ T : Finset V, T.card = 4 → coverage S T = l := by
  rintro ⟨l,hl,hT⟩
  have h := (fourth_design_block_bound S k l hk hk4 hkv hl hT).trans hA
  rw [Nat.choose_two_right] at h
  have hv : 6 ≤ Fintype.card V := by omega
  have hs : Fintype.card V-1+1 = Fintype.card V := by omega
  have hh := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mp (Nat.lt_succ_of_le h)
  nlinarith

omit [Fintype V] in
lemma coverage_pos_of_subset (S : A → Finset V) (T : Finset V) (a : A)
    (ha : T ⊆ S a) : 0 < coverage S T := by
  unfold coverage
  apply sum_pos'
  · intro b _
    split_ifs <;> norm_num
  · exact ⟨a,mem_univ _,by simp [ha]⟩

/-- Balanced regular block systems at the nontrivial fourth-order scale must
have genuinely nonconstant four-point coverage. No freeness is assumed. -/
theorem exists_unequal_quadruple_coverage [Nonempty A] (S : A → Finset V) (k : ℕ)
    (hk : ∀ a, (S a).card = k) (hk4 : 4 ≤ k) (hkv : k+2 ≤ Fintype.card V)
    (hA : Fintype.card A ≤ Fintype.card V) :
    ∃ T U : Finset V, T.card = 4 ∧ U.card = 4 ∧ coverage S T ≠ coverage S U := by
  obtain ⟨a⟩ := ‹Nonempty A›
  obtain ⟨T,hT,hcard⟩ := exists_subset_card_eq (show 4 ≤ (S a).card by rw [hk a]; exact hk4)
  by_contra! h
  apply not_balanced_exact_design S k hk hk4 hkv hA
  refine ⟨coverage S T,coverage_pos_of_subset S T a hT,?_⟩
  intro U hU
  exact (h T U hcard hU).symm

#print axioms gram_rank_bound
#print axioms pair_gram_decomposition
#print axioms pair_fisher_bound
#print axioms extensionEquiv
#print axioms uniform_downward
#print axioms fourth_design_block_bound
#print axioms not_balanced_exact_design
#print axioms exists_unequal_quadruple_coverage
end Erdos714ExactDesign
