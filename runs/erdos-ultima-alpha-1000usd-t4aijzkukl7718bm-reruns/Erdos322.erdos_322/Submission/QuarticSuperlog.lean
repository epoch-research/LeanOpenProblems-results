import Submission.Spec

/-! Elementary superlogarithmic lower bounds for primitive quartic representations. -/

namespace Erdos322Research
open scoped BigOperators
abbrev EZ := Zsqrtd (-3)

def content (z : EZ) : ℕ := Int.gcd z.re z.im

lemma content_eq_one {z : EZ} (h : IsCoprime z (star z)) : content z = 1 := by
  have hd : ((content z : ℤ) : EZ) ∣ z := by
    rw [Zsqrtd.intCast_dvd]
    exact ⟨Int.gcd_dvd_left _ _, Int.gcd_dvd_right _ _⟩
  have hs : ((content z : ℤ) : EZ) ∣ star z := by
    rw [Zsqrtd.intCast_dvd]
    exact ⟨Int.gcd_dvd_left _ _, dvd_neg.mpr (Int.gcd_dvd_right _ _)⟩
  obtain ⟨a,b,hab⟩ := h
  have hu : ((content z : ℤ) : EZ) ∣ 1 := by
    rw [← hab]
    exact dvd_add (dvd_mul_of_dvd_right hd _) (dvd_mul_of_dvd_right hs _)
  have hu' : (content z : ℤ) ∣ (1 : ℤ) := (Zsqrtd.intCast_dvd_intCast _ _).mp hu
  exact Nat.dvd_one.mp (by exact_mod_cast hu')

lemma content_smul (d : ℕ) (z : EZ) : content ((d : EZ) * z) = d * content z := by
  simp [content, Int.gcd_mul_left]

lemma norm_cast_coprime {z w : EZ} (h : IsCoprime z.norm w.norm) :
    IsCoprime z (star w) := by
  have hc := h.map (Int.castRingHom EZ)
  simp only [Int.coe_castRingHom, Zsqrtd.norm_eq_mul_conj] at hc
  exact hc.of_mul_left_left.of_mul_right_right

lemma norm_pow (z : EZ) (m : ℕ) : (z ^ m).norm = z.norm ^ m :=
  map_pow Zsqrtd.normMonoidHom z m

lemma norm_prod {ι : Type*} (s : Finset ι) (z : ι → EZ) :
    (∏ i ∈ s, z i).norm = ∏ i ∈ s, (z i).norm :=
  map_prod Zsqrtd.normMonoidHom z s

lemma coprime_prod_star {ι : Type*} (s : Finset ι) (z : ι → EZ)
    (h : ∀ i ∈ s, ∀ j ∈ s, IsCoprime (z i) (star (z j))) :
    IsCoprime (∏ i ∈ s, z i) (star (∏ i ∈ s, z i)) := by
  rw [star_prod]
  exact IsCoprime.prod_left fun i hi ↦ IsCoprime.prod_right fun j hj ↦ h i hi j hj

lemma primitive_product {r : ℕ} (a : Fin r → EZ)
    (h : ∀ i j, IsCoprime (a i) (star (a j))) (e : Fin r → ℕ) :
    content (∏ i, a i ^ e i) = 1 := by
  apply content_eq_one
  apply coprime_prod_star
  intro i _ j _
  rw [star_pow]
  exact (h i j).pow

lemma new_norm_coprime (B : ℕ) : Nat.Coprime (1 + 12 * B ^ 2) B := by
  apply Nat.isCoprime_iff_coprime.mp
  refine ⟨1, -12 * (B : ℤ), ?_⟩
  push_cast
  ring

lemma new_element_coprime (B : ℕ) :
    IsCoprime (⟨1, 2 * B⟩ : EZ) (star (⟨1, 2 * B⟩ : EZ)) := by
  let a : EZ := ⟨1, 2 * B⟩
  refine ⟨star a - 6 * (B : EZ) ^ 2, -6 * (B : EZ) ^ 2, ?_⟩
  ext <;> simp [a, pow_two] <;> ring

lemma good_system (r : ℕ) : ∃ (q : Fin r → ℕ) (a : Fin r → EZ),
    (∀ i, 1 < q i) ∧ (∀ i, (a i).norm = (q i : ℤ)) ∧
    Pairwise (Function.onFun Nat.Coprime q) ∧
    (∀ i j, IsCoprime (a i) (star (a j))) := by
  induction r with
  | zero =>
    refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_⟩ <;> intro i <;> exact i.elim0
  | succ r ih =>
    obtain ⟨q,a,hq,ha,hqq,haa⟩ := ih
    let B := ∏ i, q i
    have hB : 0 < B := Finset.prod_pos fun i _ ↦ (by have := hq i; omega)
    let Q := 1 + 12 * B ^ 2
    let A : EZ := ⟨1, 2 * B⟩
    have hQ : 1 < Q := by dsimp [Q]; nlinarith [sq_pos_of_pos hB]
    have hA : A.norm = (Q : ℤ) := by simp [A, Q, Zsqrtd.norm]; ring
    have hQi (i : Fin r) : Nat.Coprime Q (q i) :=
      (new_norm_coprime B).of_dvd_right (Finset.dvd_prod_of_mem q (Finset.mem_univ i))
    refine ⟨Fin.cons Q q, Fin.cons A a, ?_, ?_, ?_, ?_⟩
    · intro i; refine Fin.cases hQ (fun j ↦ hq j) i
    · intro i; refine Fin.cases hA (fun j ↦ ha j) i
    · intro i
      induction i using Fin.cases with
      | zero =>
        intro j
        induction j using Fin.cases with
        | zero => exact fun h ↦ False.elim (h rfl)
        | succ j => exact fun _ ↦ hQi j
      | succ i =>
        intro j
        induction j using Fin.cases with
        | zero => exact fun _ ↦ (hQi i).symm
        | succ j =>
          intro hij
          exact hqq (by intro he; exact hij (congrArg Fin.succ he))
    · intro i j
      refine Fin.cases ?_ (fun i' ↦ ?_) i
      · refine Fin.cases (new_element_coprime B) (fun j' ↦ ?_) j
        apply norm_cast_coprime
        simp only [Fin.cons_zero, Fin.cons_succ, hA, ha]
        exact (hQi j').isCoprime
      · refine Fin.cases ?_ (fun j' ↦ haa i' j') j
        apply norm_cast_coprime
        simp only [Fin.cons_zero, Fin.cons_succ, ha, hA]
        exact (hQi i').symm.isCoprime

lemma coprime_power_product_injective {r m : ℕ} (q : Fin r → ℕ)
    (hq : ∀ i, 1 < q i) (hqq : Pairwise (Function.onFun Nat.Coprime q)) :
    Function.Injective (fun j : Fin r → Fin (m + 1) ↦ ∏ i, q i ^ (j i : ℕ)) := by
  intro j k hjk
  funext i
  apply Fin.ext
  have hg (j : Fin r → Fin (m + 1)) :
      (∏ l, q l ^ (j l : ℕ)).gcd (q i ^ m) = q i ^ (j i : ℕ) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    apply Nat.gcd_mul_of_coprime_of_dvd
    · apply Nat.Coprime.prod_left
      intro l hl
      exact (hqq (Finset.mem_erase.mp hl).1).pow _ _
    · exact Nat.pow_dvd_pow _ (Nat.le_of_lt_succ (j i).isLt)
  have he := congrArg (fun d ↦ Nat.gcd d (q i ^ m)) hjk
  dsimp only at he
  rw [hg, hg] at he
  exact Nat.pow_right_injective (hq i) he

def divisorWord {r m : ℕ} (q : Fin r → ℕ) (j : Fin r → Fin (m + 1)) : ℕ :=
  ∏ i, q i ^ (j i : ℕ)

def primitiveWord {r m : ℕ} (a : Fin r → EZ) (j : Fin r → Fin (m + 1)) : EZ :=
  ∏ i, a i ^ (2 * (m - (j i : ℕ)))

def word {r m : ℕ} (q : Fin r → ℕ) (a : Fin r → EZ)
    (j : Fin r → Fin (m + 1)) : EZ :=
  (divisorWord q j : EZ) * primitiveWord a j

lemma word_content {r m : ℕ} (q : Fin r → ℕ) (a : Fin r → EZ)
    (haa : ∀ i j, IsCoprime (a i) (star (a j))) (j : Fin r → Fin (m + 1)) :
    content (word q a j) = divisorWord q j := by
  rw [word, content_smul, primitiveWord, primitive_product a haa, mul_one]

lemma word_norm {r m : ℕ} (q : Fin r → ℕ) (a : Fin r → EZ)
    (ha : ∀ i, (a i).norm = (q i : ℤ)) (j : Fin r → Fin (m + 1)) :
    (word q a j).norm = (∏ i, (q i : ℤ)) ^ (2 * m) := by
  simp only [word, Zsqrtd.norm_mul, Zsqrtd.norm_natCast, divisorWord,
    primitiveWord, norm_prod, norm_pow, ha, Nat.cast_prod, Nat.cast_pow]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_two, ← pow_mul, ← pow_add]
  congr 1
  have := (j i).isLt
  omega

def quarticVector (z : EZ) : Fin 4 → ℕ :=
  ![(z.re + z.im).natAbs, (z.re - z.im).natAbs, (2 * z.im).natAbs, 1]

lemma quarticVector_sum (z : EZ) :
    (∑ i, quarticVector z i ^ 4 : ℕ) = 2 * z.norm.natAbs ^ 2 + 1 := by
  apply Int.natCast_inj.mp
  push_cast
  simp only [Fin.sum_univ_four, quarticVector, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Int.natCast_natAbs,
    (by decide : Even (4 : ℕ)).pow_abs, sq_abs]
  simp [Zsqrtd.norm]
  ring

lemma quarticVector_content {z w : EZ} (h : quarticVector z = quarticVector w) :
    content z = content w := by
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  have h2 := congrFun h (2 : Fin 4)
  change (z.re + z.im).natAbs = (w.re + w.im).natAbs at h0
  change (z.re - z.im).natAbs = (w.re - w.im).natAbs at h1
  change (2 * z.im).natAbs = (2 * w.im).natAbs at h2
  have hx : z.re.natAbs = w.re.natAbs := by
    apply Int.natAbs_eq_natAbs_iff.mpr
    rcases Int.natAbs_eq_natAbs_iff.mp h0 with h0 | h0 <;>
    rcases Int.natAbs_eq_natAbs_iff.mp h1 with h1 | h1 <;>
    rcases Int.natAbs_eq_natAbs_iff.mp h2 with h2 | h2 <;> omega
  have hy : z.im.natAbs = w.im.natAbs := by
    simp only [Int.natAbs_mul] at h2
    omega
  simp only [content, Int.gcd_eq_natAbs, hx, hy]

lemma vector_word_injective {r m : ℕ} (q : Fin r → ℕ) (a : Fin r → EZ)
    (hq : ∀ i, 1 < q i) (hqq : Pairwise (Function.onFun Nat.Coprime q))
    (haa : ∀ i j, IsCoprime (a i) (star (a j))) :
    Function.Injective (fun j : Fin r → Fin (m + 1) ↦ quarticVector (word q a j)) := by
  intro j k hjk
  have h := quarticVector_content hjk
  rw [word_content q a haa, word_content q a haa] at h
  exact coprime_power_product_injective q hq hqq h

lemma count_of_injective_vectors {ι : Type*} [Fintype ι] (n : ℕ)
    (v : ι → Fin 4 → ℕ) (hv : Function.Injective v)
    (hs : ∀ j, ∑ i, v j i ^ 4 = n) (h3 : ∀ j, v j 3 = 1) :
    Fintype.card ι ≤ Erdos322.primitiveRepresentationCount 4 n := by
  classical
  let f : ι → Fin 4 → Fin (n + 1) := fun j i ↦ ⟨v j i, by
    have hb : v j i ≤ v j i ^ 4 := Nat.le_pow (by decide)
    have hc : v j i ^ 4 ≤ ∑ l, v j l ^ 4 :=
      Finset.single_le_sum (f := fun l : Fin 4 ↦ v j l ^ 4)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hn := hs j
    omega⟩
  have hf : Function.Injective f := by
    intro j k he
    apply hv
    funext i
    exact congrArg (fun g ↦ (g i).val) he
  unfold Erdos322.primitiveRepresentationCount
  have hc := Finset.card_le_card_of_injOn f (s := Finset.univ)
    (t := Finset.univ.filter (fun g : Fin 4 → Fin (n + 1) ↦
      (∑ i, (g i : ℕ) ^ 4 = n) ∧ Finset.univ.gcd (fun i ↦ (g i : ℕ)) = 1))
    (by
      intro j _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hs j, Nat.dvd_one.mp ?_⟩
      have hd := Finset.gcd_dvd (f := fun i ↦ (f j i : ℕ)) (Finset.mem_univ (3 : Fin 4))
      change _ ∣ v j 3 at hd
      rw [h3 j] at hd
      exact hd)
    hf.injOn
  simpa using hc

lemma system_lower_bound {r : ℕ} (q : Fin r → ℕ) (a : Fin r → EZ)
    (hq : ∀ i, 1 < q i) (ha : ∀ i, (a i).norm = (q i : ℤ))
    (hqq : Pairwise (Function.onFun Nat.Coprime q))
    (haa : ∀ i j, IsCoprime (a i) (star (a j))) (m : ℕ) :
    (m + 1) ^ r ≤ Erdos322.primitiveRepresentationCount 4
      (2 * (∏ i, q i) ^ (4 * m) + 1) := by
  have hv := vector_word_injective (m := m) q a hq hqq haa
  have hs (j : Fin r → Fin (m + 1)) : ∑ i, quarticVector (word q a j) i ^ 4 =
      2 * (∏ i, q i) ^ (4 * m) + 1 := by
    rw [quarticVector_sum, word_norm q a ha, ← Nat.cast_prod,
      Int.natAbs_pow, Int.natAbs_natCast, ← pow_mul]
    congr 3
    omega
  have h := count_of_injective_vectors _ _ hv hs (fun _ ↦ rfl)
  simpa using h

/-- At exponentially growing targets the primitive quartic count dominates any fixed
power of the exponent. In particular, no fixed power of the logarithm is an upper bound. -/
theorem quartic_arbitrary_log_degree (r : ℕ) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ m : ℕ, (m + 1) ^ (r + 1) ≤
      Erdos322.primitiveRepresentationCount 4 (2 * B ^ (4 * m) + 1) := by
  obtain ⟨q,a,hq,ha,hqq,haa⟩ := good_system (r + 1)
  refine ⟨∏ i, q i, ?_, system_lower_bound q a hq ha hqq haa⟩
  have hpos : 0 < ∏ i, q i := Finset.prod_pos fun i _ ↦ by have := hq i; omega
  have hd : q 0 ∣ ∏ i, q i := Finset.dvd_prod_of_mem q (Finset.mem_univ 0)
  exact (hq 0).trans_le (Nat.le_of_dvd hpos hd)

lemma quartic_target_log_bound {B : ℕ} (hB : 2 ≤ B) (m : ℕ) :
    Real.log (2 * (B : ℝ) ^ (4 * m) + 1) ≤ (3 + 4 * B : ℕ) * (m + 1 : ℕ) := by
  have hB1 : 1 ≤ (B : ℝ) := by exact_mod_cast (show 1 ≤ B by omega)
  have hp : 1 ≤ (B : ℝ) ^ (4 * m) := one_le_pow₀ hB1
  have hlog : Real.log (3 * (B : ℝ) ^ (4 * m)) =
      Real.log 3 + (4 * m : ℕ) * Real.log B := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  calc
    Real.log (2 * (B : ℝ) ^ (4 * m) + 1) ≤
        Real.log (3 * (B : ℝ) ^ (4 * m)) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 3 + (4 * m : ℕ) * Real.log B := hlog
    _ ≤ 3 + (4 * m : ℕ) * (B : ℝ) := by
      gcongr
      · exact Real.log_le_self (by norm_num)
      · exact Real.log_le_self (by positivity)
    _ ≤ (3 + 4 * B : ℕ) * (m + 1 : ℕ) := by push_cast; nlinarith

/-- Every fixed polylogarithmic bound fails infinitely often, even when all
quartic representations are required to be primitive. -/
theorem primitive_quartic_superlogarithmic (A : ℕ) :
    {n : ℕ | (Real.log n) ^ A <
      Erdos322.primitiveRepresentationCount 4 n}.Infinite := by
  obtain ⟨B,hB,hcount⟩ := quartic_arbitrary_log_degree A
  let C := 3 + 4 * B
  let M := C ^ A
  let f : ℕ → ℕ := fun t ↦ 2 * B ^ (4 * (M + t)) + 1
  have hf : Function.Injective f := by
    intro s t h
    change 2 * B ^ (4 * (M + s)) + 1 = 2 * B ^ (4 * (M + t)) + 1 at h
    have hp : B ^ (4 * (M + s)) = B ^ (4 * (M + t)) := by omega
    have he := Nat.pow_right_injective hB hp
    omega
  apply (Set.infinite_range_of_injective hf).mono
  rintro n ⟨t,rfl⟩
  let m := M + t
  have hm : C ^ A < m + 1 := by dsimp [m,M]; omega
  have hpos : 0 < (m + 1 : ℕ) := by omega
  have hn : 1 ≤ f t := by dsimp [f]; omega
  have hlog : Real.log (f t) ≤ (C : ℝ) * (m + 1 : ℕ) := by
    simpa [f,m,C] using quartic_target_log_bound hB (M + t)
  have hnonneg : 0 ≤ Real.log (f t) := Real.log_nonneg (by exact_mod_cast hn)
  change (Real.log (f t)) ^ A < _
  calc
    (Real.log (f t)) ^ A ≤ ((C : ℝ) * (m + 1 : ℕ)) ^ A :=
      pow_le_pow_left₀ hnonneg hlog A
    _ = (C : ℝ) ^ A * ((m + 1 : ℕ) : ℝ) ^ A := mul_pow _ _ _
    _ < ((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) ^ A := by
      apply mul_lt_mul_of_pos_right
      · exact_mod_cast hm
      · positivity
    _ = ((m + 1 : ℕ) : ℝ) ^ (A + 1) := by ring
    _ ≤ Erdos322.primitiveRepresentationCount 4 (f t) := by
      exact_mod_cast hcount m

/-- The unrestricted count also exceeds every fixed power of the logarithm infinitely often. -/
theorem quartic_superlogarithmic (A : ℕ) :
    {n : ℕ | (Real.log n) ^ A < Erdos322.representationCount 4 n}.Infinite := by
  apply (primitive_quartic_superlogarithmic A).mono
  intro n hn
  have hle : (Erdos322.primitiveRepresentationCount 4 n : ℝ) ≤
      Erdos322.representationCount 4 n := by
    exact_mod_cast Erdos322.primitiveRepresentationCount_le 4 n
  exact lt_of_lt_of_le hn hle

end Erdos322Research
