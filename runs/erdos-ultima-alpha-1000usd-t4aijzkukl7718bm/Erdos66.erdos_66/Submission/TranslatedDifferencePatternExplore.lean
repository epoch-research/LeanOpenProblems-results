import Submission.DifferenceNaturalPatternExplore

/-! Difference pairs with their smaller endpoint in [N,2N), with no
restriction on the positive translation. Polynomial translation horizons
produce logarithmic bounds from the same positive-pattern selector. -/
namespace Erdos66TranslatedDifferencePattern
open Filter AdditiveCombinatorics Erdos66NaturalPositivePattern Erdos66MatchingNaturalPattern
  Erdos66BernoulliMatchingPolynomial Erdos66DisjointMatchingPolynomial
  Erdos66FiniteRepBernoulli Erdos66FiniteBernoulli Erdos66Fractional
  Erdos66NaturalPatternRestriction Erdos66RarePatternCodeGrowth
  Erdos66FractionalFourthPower
open scoped Classical Topology
set_option maxHeartbeats 2600000

noncomputable def indices (N d b : ℕ) : Finset ℕ :=
  (Finset.Ico N (2*N)).filter (fun a ↦ (a/d)%2=b)

noncomputable def endpoint (N d : ℕ) (a : ℕ) : Fin (2*N+d+1) × Fin (2*N+d+1) :=
  if ha : a<2*N then (⟨a,by omega⟩,⟨a+d,by omega⟩) else (0,0)

noncomputable def edgeClass (N d b : ℕ) : Finset (Fin (2*N+d+1) × Fin (2*N+d+1)) :=
  (indices N d b).image (endpoint N d)

lemma endpoint_of_lt (N d a : ℕ) (ha : a<2*N) :
    (endpoint N d a).1.val=a ∧ (endpoint N d a).2.val=a+d := by
  simp [endpoint,ha]

lemma mem_edgeClass {N d b : ℕ} {e : Fin (2*N+d+1) × Fin (2*N+d+1)} :
    e∈edgeClass N d b ↔ N ≤ e.1.val ∧ e.1.val<2*N ∧ e.2.val=e.1.val+d ∧ (e.1.val/d)%2=b := by
  constructor
  · intro he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨ha,hb⟩ := Finset.mem_filter.mp ha
    have hi := Finset.mem_Ico.mp ha
    rw [(endpoint_of_lt N d a hi.2).1,(endpoint_of_lt N d a hi.2).2]
    exact ⟨hi.1,hi.2,rfl,hb⟩
  · rintro ⟨hN,h2,he,hb⟩
    apply Finset.mem_image.mpr
    refine ⟨e.1.val,Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hN,h2⟩,hb⟩,?_⟩
    have hv := endpoint_of_lt N d e.1.val h2
    exact Prod.ext (Fin.ext hv.1) (Fin.ext (hv.2.trans he.symm))

lemma edgeClass_disjoint (N d b : ℕ) (hd : 0<d) :
    (edgeClass N d b : Set (Fin (2*N+d+1) × Fin (2*N+d+1))).Pairwise (fun a c ↦ Disjoint (pairCoords a) (pairCoords c)) := by
  intro a ha c hc hac
  obtain ⟨_,_,haeq,haq⟩ := mem_edgeClass.mp ha
  obtain ⟨_,_,hceq,hcq⟩ := mem_edgeClass.mp hc
  have had : a.2.val/d=a.1.val/d+1 := by rw [haeq,Nat.add_div_right _ hd]
  have hcd : c.2.val/d=c.1.val/d+1 := by rw [hceq,Nat.add_div_right _ hd]
  have hneq : a.1.val≠c.1.val ∨ a.2.val≠c.2.val := by
    by_contra hn
    push_neg at hn
    exact hac (Prod.ext (Fin.ext hn.1) (Fin.ext hn.2))
  apply Finset.disjoint_left.mpr
  intro i hia hic
  simp only [pairCoords,Finset.mem_insert,Finset.mem_singleton] at hia hic
  rcases hia with hia | hia <;> rcases hic with hic | hic <;>
    have he := congrArg Fin.val (hia.symm.trans hic) <;>
    have hed := congrArg (fun j : ℕ ↦ j/d) he <;> dsimp only at hed <;> omega

lemma edgeClass_card_le (N d b : ℕ) : (edgeClass N d b).card ≤ N := by
  have hh := (Finset.card_image_le (s := indices N d b) (f := endpoint N d)).trans
    (Finset.card_le_card (Finset.filter_subset _ _))
  simpa only [Nat.card_Ico,show 2*N-N=N by omega] using hh

noncomputable def mean (N d b : ℕ) (p : ℕ → ℝ) : ℝ :=
  ∑ e∈edgeClass N d b, ∏ i∈pairCoords e, p i.val

lemma harmonic_mean_bound (N d b : ℕ) (hd : 0<d) : mean N d b profile ≤ (harmonic (N+1) : ℝ) := by
  have hs : mean N d b profile ≤ (N : ℝ)*(profile N)^2 := by
    calc
      _ ≤ ∑ _e∈edgeClass N d b, (profile N)^2 := by
        apply Finset.sum_le_sum
        intro e he
        obtain ⟨hN,_,heq,_⟩ := mem_edgeClass.mp he
        have hne : e.1≠e.2 := by intro he; have := congrArg Fin.val he; omega
        simp only [pairCoords,Finset.prod_pair hne,pow_two]
        apply mul_le_mul (profile_antitone hN) (profile_antitone (by omega))
          (profile_nonneg _) (profile_nonneg _)
      _ = ((edgeClass N d b).card : ℝ)*(profile N)^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast edgeClass_card_le N d b) (sq_nonneg _)
  have hp := profile_square_bound N
  push_cast at hp
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  exact hs.trans (by nlinarith [sq_nonneg (profile N)])

noncomputable def differencePattern (N d b : ℕ) : Pattern :=
  matchingPattern (2*N+d) (edgeClass N d b) pairCoords (1/2) (by norm_num)

def differenceCode (N d b : ℕ) : ℕ := Nat.pair 3 (Nat.pair N (Nat.pair d b))

lemma differencePattern_mean (N d b : ℕ) (hd : 0<d) :
    (differencePattern N d b).eval profile ≤ 3*((N : ℝ)+1) := by
  rw [differencePattern,matchingPattern_eval]
  have hu := matchingPoly_upper (edgeClass N d b) pairCoords (1/2) (by norm_num)
    (fun i ↦ profile i.val) (fun i ↦ profile_nonneg _)
  have he2 : Real.exp (1/2 : ℝ)-1 ≤ 1 := by
    have he : Real.exp (1/2 : ℝ)*Real.exp (1/2 : ℝ)=Real.exp 1 := by rw [←Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1/2 : ℝ),Real.exp_one_lt_d9]
  have hm0 : 0 ≤ mean N d b profile := Finset.sum_nonneg (fun e _ ↦
    Finset.prod_nonneg (fun i _ ↦ profile_nonneg _))
  have hm := mul_le_mul_of_nonneg_right he2 hm0
  simp only [one_mul] at hm
  have hmean := harmonic_mean_bound N d b hd
  have hH := harmonic_le_one_add_log (N+1)
  have hu' : _ ≤ Real.exp (1+Real.log ((N+1 : ℕ) : ℝ)) :=
    hu.trans (Real.exp_le_exp.mpr ((hm.trans hmean).trans hH))
  rw [Real.exp_add,Real.exp_log (by positivity)] at hu'
  push_cast at hu'
  exact hu'.trans (mul_le_mul_of_nonneg_right (by linarith [Real.exp_one_lt_d9]) (by positivity))

noncomputable def colorCount (A : Set ℕ) (N d b : ℕ) : ℕ :=
  ((indices N d b).filter (fun a ↦ a∈A ∧ a+d∈A)).card

noncomputable def translatedDiff (A : Set ℕ) (N d : ℕ) : ℕ :=
  ((Finset.Ico N (2*N)).filter (fun a ↦ a∈A ∧ a+d∈A)).card

lemma colorCount_realized (A : Set ℕ) (N d b : ℕ) :
    colorCount A N d b=(realized (edgeClass N d b) pairCoords (restrict A (2*N+d))).card := by
  apply Finset.card_bij (fun a _ ↦ endpoint N d a)
  · intro a ha
    obtain ⟨ha,haA,hadA⟩ := Finset.mem_filter.mp ha
    have hi := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
    have hv := endpoint_of_lt N d a hi.2
    apply (mem_realized _ _ _ _).mpr
    refine ⟨Finset.mem_image.mpr ⟨a,ha,rfl⟩,?_⟩
    intro i hi
    simp only [pairCoords,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simpa only [restrict,hv.1,decide_eq_true_eq] using haA
    · simpa only [restrict,hv.2,decide_eq_true_eq] using hadA
  · intro a ha c hc he
    have ha' := (Finset.mem_Ico.mp (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1).2
    have hc' := (Finset.mem_Ico.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1).2
    have hh := congrArg (fun e : Fin (2*N+d+1) × Fin (2*N+d+1) ↦ e.1.val) he
    dsimp only at hh
    rwa [(endpoint_of_lt N d a ha').1,(endpoint_of_lt N d c hc').1] at hh
  · intro e he
    obtain ⟨he,hA⟩ := (mem_realized _ _ _ _).mp he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    have hi := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
    have hv := endpoint_of_lt N d a hi.2
    refine ⟨a,Finset.mem_filter.mpr ⟨ha,?_,?_⟩,rfl⟩
    · have hh := hA (endpoint N d a).1 (by simp [pairCoords])
      simpa only [restrict,hv.1,decide_eq_true_eq] using hh
    · have hh := hA (endpoint N d a).2 (by simp [pairCoords])
      simpa only [restrict,hv.2,decide_eq_true_eq] using hh

lemma differencePattern_value (A : Set ℕ) (N d b : ℕ) (hd : 0<d) :
    (differencePattern N d b).value (fun i ↦ decide (i∈A))=Real.exp ((1/2 : ℝ)*(colorCount A N d b : ℝ)) := by
  rw [Pattern.value,differencePattern,matchingPattern_eval]
  change matchingPoly _ _ _ (fun i ↦ bit (restrict A (2*N+d) i))=_
  rw [matchingPoly_binary_disjoint _ _ (edgeClass_disjoint N d b hd),←colorCount_realized]

lemma translatedDiff_split (A : Set ℕ) (N d : ℕ) :
    translatedDiff A N d=colorCount A N d 0+colorCount A N d 1 := by
  have he : ((Finset.Ico N (2*N)).filter (fun a ↦ a∈A ∧ a+d∈A)).filter (fun a ↦ (a/d)%2=0)=
      (indices N d 0).filter (fun a ↦ a∈A ∧ a+d∈A) := by
    ext a
    simp only [indices,Finset.mem_filter]
    tauto
  have he' : ((Finset.Ico N (2*N)).filter (fun a ↦ a∈A ∧ a+d∈A)).filter (fun a ↦ ¬(a/d)%2=0)=
      (indices N d 1).filter (fun a ↦ a∈A ∧ a+d∈A) := by
    ext a
    simp only [indices,Finset.mem_filter]
    have hh := Nat.mod_lt (a/d) (by norm_num : 0<2)
    have hi : (¬(a/d)%2=0) ↔ (a/d)%2=1 := by omega
    rw [hi]
    tauto
  have hh := Finset.card_filter_add_card_filter_not (s := (Finset.Ico N (2*N)).filter (fun a ↦ a∈A ∧ a+d∈A))
    (fun a ↦ (a/d)%2=0)
  rw [he,he'] at hh
  exact hh.symm

lemma differenceCode_bound (N d b h : ℕ) (hN : 3 ≤ N) (hd : d ≤ N^h) (hb : b<2) :
    differenceCode N d b+1 ≤ (N+1)^(8*(h+1)) := by
  let K := (N+1)^(h+1)
  have hKN : N+1 ≤ K := Nat.le_self_pow (by omega) (N+1)
  have hKd : d+1 ≤ K := by
    have h1 := Nat.pow_le_pow_left (Nat.le_succ N) h
    have h2 := Nat.pow_lt_pow_right (by omega : 1<N+1) (by omega : h<h+1)
    exact Nat.succ_le_of_lt ((hd.trans h1).trans_lt h2)
  have h1 := pair_succ_le_sq d b K hKd (by omega)
  have h2 := pair_succ_le_pow N (Nat.pair d b) K 2 (by omega) (by omega) hKN h1
  have h3 := pair_succ_le_pow 3 (Nat.pair N (Nat.pair d b)) K 4 (by omega) (by omega) (by omega) h2
  simpa only [K,←pow_mul,mul_comm (h+1) 8] using h3

lemma translatedDiff_of_pattern_budget (A : Set ℕ) (M N d h : ℕ)
    (hN : 3 ≤ N) (hM : M ≤ N) (hd : 0<d) (hdN : d ≤ N^h)
    (hbudget : ∀ b<2, (differencePattern N d b).value (fun i ↦ decide (i∈A)) ≤
      ((differenceCode N d b : ℝ)+M+2)^4) :
    (translatedDiff A N d : ℝ) ≤ 16*((8*(h+1)+1 : ℕ) : ℝ)*Real.log ((N : ℝ)+1) := by
  have hb (b : ℕ) (hb : b<2) :
      (colorCount A N d b : ℝ) ≤ 8*((8*(h+1)+1 : ℕ) : ℝ)*Real.log ((N : ℝ)+1) := by
    have hc := code_shift_bound (differenceCode N d b) M N (8*(h+1)) (by omega) hM (by omega)
      (differenceCode_bound N d b h hN hdN hb)
    have hc' : (differenceCode N d b : ℝ)+M+2 ≤ ((N : ℝ)+1)^(8*(h+1)+1) := by exact_mod_cast hc
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (differenceCode N d b : ℝ)+M+2) hc' 4
    have hh := hbudget b hb
    rw [differencePattern_value A N d b hd] at hh
    have hl := Real.log_le_log (Real.exp_pos _) (hh.trans hp)
    rw [Real.log_exp,Real.log_pow,Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    linarith
  have he := translatedDiff_split A N d
  have he' : (translatedDiff A N d : ℝ)=(colorCount A N d 0 : ℝ)+colorCount A N d 1 := by exact_mod_cast he
  linarith [hb 0 (by norm_num),hb 1 (by norm_num)]

end Erdos66TranslatedDifferencePattern
