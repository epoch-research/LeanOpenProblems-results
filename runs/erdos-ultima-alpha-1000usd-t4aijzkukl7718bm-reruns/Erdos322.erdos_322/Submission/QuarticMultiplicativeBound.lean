import Submission.Spec

/-! A uniform bound for quartic representations with a multiplicative coordinate relation. -/
namespace Erdos322Research.QuarticMultiplicative

open Erdos322.QuarticAdditive

private def matrixTuple (u v : ℕ × ℕ) : Fin 4 → ℕ :=
  ![u.1*v.1, u.1*v.2, u.2*v.1, u.2*v.2]

private lemma matrixTuple_sum (u v : ℕ × ℕ) :
    ∑ i, matrixTuple u v i ^ 4 = (u.1^4+u.2^4)*(v.1^4+v.2^4) := by
  simp [Fin.sum_univ_four, matrixTuple]
  ring

/-- Every nonnegative integral rank-one two-by-two matrix is an outer product
of two nonnegative integral vectors. Zero rows and columns are included. -/
private lemma rank_one_factorization (a : Fin 4 → ℕ) (h : a 0*a 3=a 1*a 2) :
    ∃ u v : ℕ × ℕ, a=matrixTuple u v := by
  by_cases hx : a 0=0
  · by_cases hy : a 1=0
    · refine ⟨(0,1),(a 2,a 3),?_⟩
      funext i
      fin_cases i <;> simp [matrixTuple, hx, hy]
    · have hz : a 2=0 := by
        rw [hx, zero_mul] at h
        exact (mul_eq_zero.mp h.symm).resolve_left hy
      refine ⟨(a 1,a 3),(0,1),?_⟩
      funext i
      fin_cases i <;> simp [matrixTuple, hx, hz]
  · let g := (a 0).gcd (a 1)
    have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hx)
    obtain ⟨x,y,hcop,hxg,hyg⟩ := Nat.exists_coprime (a 0) (a 1)
    change a 0=x*g at hxg
    change a 1=y*g at hyg
    have hxp : 0 < x := by
      by_contra hn
      have hx0 : x=0 := by omega
      simp [hx0] at hxg
      exact hx hxg
    have hcross : x*a 3=y*a 2 := by
      apply Nat.mul_left_cancel hg
      calc
        g*(x*a 3) = a 0*a 3 := by rw [hxg]; ring
        _ = a 1*a 2 := h
        _ = g*(y*a 2) := by rw [hyg]; ring
    have hdiv : x ∣ a 2 := hcop.dvd_of_dvd_mul_left (hcross ▸ dvd_mul_right x (a 3))
    obtain ⟨z,hz⟩ := hdiv
    have hw : a 3=y*z := by
      apply Nat.mul_left_cancel hxp
      calc
        x*a 3 = y*a 2 := hcross
        _ = x*(y*z) := by rw [hz]; ring
    refine ⟨(g,z),(x,y),?_⟩
    funext i
    fin_cases i <;> simp [matrixTuple, hxg, hyg, hz, hw, mul_comm]

private def fourthPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n+1) ×ˢ Finset.range (n+1)).filter (fun p ↦ p.1^4+p.2^4=n)

private lemma mem_fourthPairs (n : ℕ) (p : ℕ × ℕ) :
    p ∈ fourthPairs n ↔ p.1^4+p.2^4=n := by
  simp only [fourthPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact And.right
  · intro hp
    have h₁ := Nat.le_pow (a := p.1) (by decide : 0 < 4)
    have h₂ := Nat.le_pow (a := p.2) (by decide : 0 < 4)
    exact ⟨⟨by omega, by omega⟩,hp⟩

private lemma fourthPairs_bound {n : ℕ} (hn : 0 < n) :
    (fourthPairs n).card ≤ 4*n.divisors.card^2 := by
  apply le_trans _ (Erdos322.UniformBinaryNorm.binary_norm_count_uniform (by decide : 0 < 1) hn)
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ ↦ (p.1^2,p.2^2))
  · intro p hp
    apply (mem_binaryNormSolutions (by decide : 0 < 1) _).mpr
    have hp' := (mem_fourthPairs n p).mp hp
    change (p.1^2)^2+1*(p.2^2)^2=n
    simpa only [← pow_mul, one_mul] using hp'
  · intro p hp q hq he
    have h₁ : p.1^2=q.1^2 := congrArg Prod.fst he
    have h₂ : p.2^2=q.2^2 := congrArg Prod.snd he
    exact Prod.ext (Nat.pow_left_injective (by decide : 2 ≠ 0) h₁)
      (Nat.pow_left_injective (by decide : 2 ≠ 0) h₂)

private def fixedReps (n : ℕ) : Finset (Fin 4 → Fin (n+1)) :=
  Finset.univ.filter (fun a ↦ (∑ i, (a i : ℕ)^4=n) ∧
    (a 0 : ℕ)*(a 3 : ℕ)=(a 1 : ℕ)*(a 2 : ℕ))

def fixedMultiplicativeCount (n : ℕ) : ℕ := (fixedReps n).card

private def factorImages (n d : ℕ) : Finset (Fin 4 → ℕ) :=
  (fourthPairs d ×ˢ fourthPairs (n/d)).image (fun p ↦ matrixTuple p.1 p.2)

private lemma fixed_count_le_divisor_sum {n : ℕ} (hn : 0 < n) :
    fixedMultiplicativeCount n ≤
      ∑ d ∈ n.divisors, (fourthPairs d).card*(fourthPairs (n/d)).card := by
  classical
  have hcard : fixedMultiplicativeCount n ≤ (n.divisors.biUnion (factorImages n)).card := by
    apply Finset.card_le_card_of_injOn (fun a : Fin 4 → Fin (n+1) ↦ fun i ↦ (a i : ℕ))
    · intro a ha
      simp only [Finset.mem_coe, fixedReps, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨u,v,he⟩ := rank_one_factorization (fun i ↦ (a i : ℕ)) ha.2
      let d := u.1^4+u.2^4
      let e := v.1^4+v.2^4
      have hm : d*e=n := by
        rw [← matrixTuple_sum u v, ← he]
        exact ha.1
      have hd : 0 < d := by
        by_contra hn'
        have hd0 : d=0 := by omega
        rw [hd0, zero_mul] at hm
        omega
      have hdn : d ∣ n := ⟨e,hm.symm⟩
      have hquot : n/d=e := by rw [← hm, Nat.mul_div_cancel_left _ hd]
      apply Finset.mem_biUnion.mpr
      refine ⟨d,Nat.mem_divisors.mpr ⟨hdn,hn.ne'⟩,?_⟩
      apply Finset.mem_image.mpr
      refine ⟨(u,v),Finset.mem_product.mpr ⟨?_,?_⟩,he.symm⟩
      · exact (mem_fourthPairs d u).mpr rfl
      · rw [hquot]
        exact (mem_fourthPairs e v).mpr rfl
    · intro a ha b hb he
      funext i
      exact Fin.ext (congrArg (fun f ↦ f i) he)
  apply hcard.trans (Finset.card_biUnion_le.trans ?_)
  apply Finset.sum_le_sum
  intro d hd
  exact (Finset.card_image_le (s := fourthPairs d ×ˢ fourthPairs (n/d))).trans_eq
    (Finset.card_product _ _)

/-- The whole fixed multiplicative-relation locus has a divisor bound. -/
theorem fixed_multiplicative_divisor_bound {n : ℕ} (hn : 0 < n) :
    fixedMultiplicativeCount n ≤ 16*n.divisors.card^5 := by
  apply (fixed_count_le_divisor_sum hn).trans
  have ht (d : ℕ) (hd : d ∈ n.divisors) :
      (fourthPairs d).card*(fourthPairs (n/d)).card ≤ 16*n.divisors.card^4 := by
    have hdn := (Nat.mem_divisors.mp hd).1
    have hdp : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hqp : 0 < n/d := Nat.div_pos (Nat.le_of_dvd hn hdn) hdp
    have hdcard : d.divisors.card ≤ n.divisors.card :=
      Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' hdn)
    have hqcard : (n/d).divisors.card ≤ n.divisors.card :=
      Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' (Nat.div_dvd_of_dvd hdn))
    calc
      (fourthPairs d).card*(fourthPairs (n/d)).card ≤
          (4*d.divisors.card^2)*(4*(n/d).divisors.card^2) :=
        Nat.mul_le_mul (fourthPairs_bound hdp) (fourthPairs_bound hqp)
      _ ≤ (4*n.divisors.card^2)*(4*n.divisors.card^2) := by gcongr
      _ = 16*n.divisors.card^4 := by ring
  calc
    ∑ d ∈ n.divisors, (fourthPairs d).card*(fourthPairs (n/d)).card ≤
        ∑ _d ∈ n.divisors, 16*n.divisors.card^4 := Finset.sum_le_sum ht
    _ = 16*n.divisors.card^5 := by simp; ring

/-- Some permutation of the four coordinates forms a rank-one matrix. -/
def HasProductRelation {n : ℕ} (a : Fin 4 → Fin (n+1)) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4),
    (a (σ 0) : ℕ)*(a (σ 3) : ℕ)=(a (σ 1) : ℕ)*(a (σ 2) : ℕ)

instance {n : ℕ} (a : Fin 4 → Fin (n+1)) : Decidable (HasProductRelation a) :=
  inferInstanceAs (Decidable (∃ σ : Equiv.Perm (Fin 4),
    (a (σ 0) : ℕ)*(a (σ 3) : ℕ)=(a (σ 1) : ℕ)*(a (σ 2) : ℕ)))

def multiplicativeQuarticCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun a : Fin 4 → Fin (n+1) ↦
    (∑ i, (a i : ℕ)^4=n) ∧ HasProductRelation a)).card

private def permReps (n : ℕ) (σ : Equiv.Perm (Fin 4)) : Finset (Fin 4 → Fin (n+1)) :=
  Finset.univ.filter (fun a ↦ (∑ i, (a i : ℕ)^4=n) ∧
    (a (σ 0) : ℕ)*(a (σ 3) : ℕ)=(a (σ 1) : ℕ)*(a (σ 2) : ℕ))

private lemma permReps_card (n : ℕ) (σ : Equiv.Perm (Fin 4)) :
    (permReps n σ).card=fixedMultiplicativeCount n := by
  classical
  apply Finset.card_nbij (fun a i ↦ a (σ i))
  · intro a ha
    simp only [Finset.mem_coe, permReps, fixedReps,
      Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ⟨(Equiv.sum_comp σ (fun i ↦ (a i : ℕ)^4)).trans ha.1,ha.2⟩
  · intro a ha b hb he
    funext i
    have hh := congrArg (fun f ↦ f (σ.symm i)) he
    simpa using hh
  · intro a ha
    simp only [Finset.mem_coe, fixedReps, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    refine ⟨fun i ↦ a (σ.symm i),?_,?_⟩
    · simp only [Finset.mem_coe, permReps, Finset.mem_filter,
        Finset.mem_univ, true_and, Equiv.symm_apply_apply]
      exact ⟨(Equiv.sum_comp σ.symm (fun i ↦ (a i : ℕ)^4)).trans ha.1,ha.2⟩
    · funext i
      simp

private lemma multiplicative_le (n : ℕ) :
    multiplicativeQuarticCount n ≤ 24*fixedMultiplicativeCount n := by
  classical
  have he : Finset.univ.filter (fun a : Fin 4 → Fin (n+1) ↦
      (∑ i, (a i : ℕ)^4=n) ∧ HasProductRelation a) = Finset.univ.biUnion (permReps n) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      permReps, HasProductRelation]
    tauto
  change (Finset.univ.filter _).card ≤ _
  rw [he]
  have hb := Finset.card_biUnion_le (s := (Finset.univ : Finset (Equiv.Perm (Fin 4))))
    (t := permReps n)
  simp only [permReps_card, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, smul_eq_mul] at hb
  norm_num at hb
  exact hb

/-- All ordered quartic representations containing a product relation satisfy
this bound, regardless of the factors used in a construction. -/
theorem multiplicative_quartic_divisor_bound {n : ℕ} (hn : 0 < n) :
    multiplicativeQuarticCount n ≤ 384*n.divisors.card^5 := by
  calc
    multiplicativeQuarticCount n ≤ 24*fixedMultiplicativeCount n := multiplicative_le n
    _ ≤ 24*(16*n.divisors.card^5) := Nat.mul_le_mul_left _ (fixed_multiplicative_divisor_bound hn)
    _ = 384*n.divisors.card^5 := by ring

theorem multiplicative_quartic_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      (multiplicativeQuarticCount n : ℝ) ≤ C*(n : ℝ)^ε := by
  obtain ⟨C,hC,hdiv⟩ := Erdos322.divisor_count_subpolynomial (ε/5) (by linarith)
  refine ⟨384*C^5,by positivity,fun n hn ↦ ?_⟩
  have hp : ((n : ℝ)^(ε/5))^5=(n : ℝ)^ε := by
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ n)]
    congr 1
    norm_num
  calc
    (multiplicativeQuarticCount n : ℝ) ≤ 384*(n.divisors.card : ℝ)^5 := by
      exact_mod_cast multiplicative_quartic_divisor_bound hn
    _ ≤ 384*(C*(n : ℝ)^(ε/5))^5 := by gcongr; exact hdiv n hn
    _ = (384*C^5)*(n : ℝ)^ε := by rw [mul_pow,hp]; ring

end Erdos322Research.QuarticMultiplicative
