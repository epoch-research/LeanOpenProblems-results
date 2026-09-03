import FormalConjecturesUtil

/-!
# An elementary bound for weighted sign Gram kernels

For nonnegative weights of positive total mass, signs with square one, and
`2 * card κ * G i j ≤ ∑ p, β p` off the diagonal, the number of vertices is at
most `4 * card κ`. The proof uses finite sums, Cauchy–Schwarz for the weights,
and the polynomial `(x + B) * (2 * s * x - B)`. No matrix rank, spectral theorem,
or Euclidean embedding is used.
-/

open scoped BigOperators NNReal

namespace E126.Spherical126

noncomputable section

variable {ι κ : Type*} [Fintype κ]

/-- The weighted sign Gram kernel; arbitrary real features are allowed here. -/
def gram (β : κ → ℝ) (σ : κ → ι → ℝ) (i j : ι) : ℝ :=
  ∑ p, β p * σ p i * σ p j

/-- Square-one signs make the diagonal equal to the total weight. -/
theorem gram_diag (β : κ → ℝ) (σ : κ → ι → ℝ)
    (hσ : ∀ p i, σ p i ^ 2 = 1) (i : ι) :
    gram β σ i i = ∑ p, β p := by
  simp only [gram, mul_assoc, ← pow_two, hσ, mul_one]

/-- Every entry is at least minus the total weight. -/
theorem neg_sum_le_gram (β : κ → ℝ) (σ : κ → ι → ℝ)
    (hβ : ∀ p, 0 ≤ β p) (hσ : ∀ p i, σ p i ^ 2 = 1) (i j : ι) :
    -(∑ p, β p) ≤ gram β σ i j := by
  calc
    -(∑ p, β p) = ∑ p, β p * (-1) := by simp
    _ ≤ gram β σ i j := by
      apply Finset.sum_le_sum
      intro p hp
      have hprod : -1 ≤ σ p i * σ p j := by
        nlinarith [sq_nonneg (σ p i + σ p j), hσ p i, hσ p j]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod (hβ p)

variable [Fintype ι]

/-- The sum of a weighted Gram kernel is a weighted sum of squares. -/
theorem sum_gram_eq (β : κ → ℝ) (σ : κ → ι → ℝ) :
    (∑ i, ∑ j, gram β σ i j) = ∑ p, β p * (∑ i, σ p i) ^ 2 := by
  classical
  unfold gram
  calc
    (∑ i, ∑ j, ∑ p, β p * σ p i * σ p j) =
        ∑ i, ∑ p, ∑ j, β p * σ p i * σ p j := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ p, ∑ i, ∑ j, β p * σ p i * σ p j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [pow_two, Finset.sum_mul_sum]
      simp only [Finset.mul_sum, mul_assoc]

/-- Nonnegative weights imply a nonnegative sum of Gram entries. -/
theorem sum_gram_nonneg (β : κ → ℝ) (σ : κ → ι → ℝ)
    (hβ : ∀ p, 0 ≤ β p) : 0 ≤ ∑ i, ∑ j, gram β σ i j := by
  rw [sum_gram_eq]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hβ p) (sq_nonneg _)

/-- Expanding the square interchanges the vertex and feature Gram kernels. -/
theorem sum_sq_gram_eq (β : κ → ℝ) (σ : κ → ι → ℝ) :
    (∑ i, ∑ j, gram β σ i j ^ 2) =
      ∑ p, ∑ q, β p * β q * (∑ i, σ p i * σ q i) ^ 2 := by
  classical
  have hsq (i j : ι) : gram β σ i j ^ 2 =
      gram (fun pq : κ × κ => β pq.1 * β pq.2)
        (fun pq i => σ pq.1 i * σ pq.2 i) i j := by
    simp only [gram, pow_two, Finset.sum_mul_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    ring
  simp_rw [hsq]
  rw [sum_gram_eq]
  simp only [Fintype.sum_prod_type]

/-- Keeping only equal-feature terms gives the elementary trace lower bound. -/
theorem card_sq_mul_sum_sq_le_sum_sq_gram (β : κ → ℝ) (σ : κ → ι → ℝ)
    (hβ : ∀ p, 0 ≤ β p) (hσ : ∀ p i, σ p i ^ 2 = 1) :
    (Fintype.card ι : ℝ) ^ 2 * (∑ p, β p ^ 2) ≤
      ∑ i, ∑ j, gram β σ i j ^ 2 := by
  classical
  have hinner (p : κ) : (∑ i, σ p i * σ p i) = (Fintype.card ι : ℝ) := by
    simp only [← pow_two, hσ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
  rw [sum_sq_gram_eq]
  calc
    (Fintype.card ι : ℝ) ^ 2 * (∑ p, β p ^ 2) =
        ∑ p, β p * β p * (∑ i, σ p i * σ p i) ^ 2 := by
      simp_rw [hinner, ← pow_two, ← Finset.sum_mul]
      ring
    _ ≤ ∑ p, ∑ q, β p * β q * (∑ i, σ p i * σ q i) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.single_le_sum
        (fun q _ => mul_nonneg (mul_nonneg (hβ p) (hβ q))
          (sq_nonneg (∑ i, σ p i * σ q i)))
        (Finset.mem_univ p)

/-- Finite Cauchy–Schwarz converts the sum of squared weights into total mass.
This is the usual Gram trace/rank inequality, with denominators cleared. -/
theorem trace_sq_le (β : κ → ℝ) (σ : κ → ι → ℝ)
    (hβ : ∀ p, 0 ≤ β p) (hσ : ∀ p i, σ p i ^ 2 = 1) :
    (Fintype.card ι : ℝ) ^ 2 * (∑ p, β p) ^ 2 ≤
      (Fintype.card κ : ℝ) * (∑ i, ∑ j, gram β σ i j ^ 2) := by
  have hCS : (∑ p, β p) ^ 2 ≤ (Fintype.card κ : ℝ) * (∑ p, β p ^ 2) := by
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset κ) (fun _ => (1 : ℝ)) β
  calc
    (Fintype.card ι : ℝ) ^ 2 * (∑ p, β p) ^ 2 ≤
        (Fintype.card ι : ℝ) ^ 2 * ((Fintype.card κ : ℝ) * (∑ p, β p ^ 2)) :=
      mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    _ = (Fintype.card κ : ℝ) * ((Fintype.card ι : ℝ) ^ 2 * (∑ p, β p ^ 2)) := by
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (card_sq_mul_sum_sq_le_sum_sq_gram β σ hβ hσ) (Nat.cast_nonneg _)

/-- Almost-obtuse weighted sign vectors have at most four times as many vertices
as features. The off-diagonal hypothesis has no divisions. Positive total mass
already forces the feature type to be nonempty; the vertex type may be empty. -/
theorem card_le_four_mul (β : κ → ℝ) (σ : κ → ι → ℝ)
    (hβ : ∀ p, 0 ≤ β p) (hσ : ∀ p i, σ p i ^ 2 = 1)
    (hB : 0 < ∑ p, β p)
    (hoff : ∀ i j, i ≠ j →
      2 * (Fintype.card κ : ℝ) * gram β σ i j ≤ ∑ p, β p) :
    Fintype.card ι ≤ 4 * Fintype.card κ := by
  classical
  by_cases hι : Fintype.card ι = 0
  · simp [hι]
  let N : ℝ := Fintype.card ι
  let s : ℝ := Fintype.card κ
  let B : ℝ := ∑ p, β p
  let G := gram β σ
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero hι
  have hs : 1 ≤ s := by
    have hc : 1 ≤ Fintype.card κ := by
      by_contra hc
      haveI : IsEmpty κ := Fintype.card_eq_zero_iff.mp (by omega)
      simp at hB
    dsimp [s]
    exact_mod_cast hc
  have hB' : 0 < B := hB
  have hsum : 0 ≤ ∑ i, ∑ j, G i j := sum_gram_nonneg β σ hβ
  have htrace : N ^ 2 * B ^ 2 ≤ s * (∑ i, ∑ j, G i j ^ 2) :=
    trace_sq_le β σ hβ hσ
  have hcoef : 0 ≤ (2 * s - 1) * B * (∑ i, ∑ j, G i j) :=
    mul_nonneg (mul_nonneg (by linarith) hB'.le) hsum
  let f : ℝ → ℝ := fun x => (x + B) * (2 * s * x - B)
  have hupper : (∑ i, ∑ j, f (G i j)) ≤ N * (4 * s * B ^ 2) := by
    calc
      (∑ i, ∑ j, f (G i j)) ≤
          ∑ i : ι, ∑ j : ι, if i = j then 4 * s * B ^ 2 else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        split_ifs with hij
        · subst j
          have hdiag : G i i = B := gram_diag β σ hσ i
          dsimp only [f]
          rw [hdiag]
          nlinarith [sq_nonneg B]
        · have hlow : -B ≤ G i j := neg_sum_le_gram β σ hβ hσ i j
          have hhigh : 2 * s * G i j ≤ B := hoff i j hij
          exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      _ = N * (4 * s * B ^ 2) := by simp [N]
  have hpoly : (∑ i, ∑ j, f (G i j)) =
      2 * s * (∑ i, ∑ j, G i j ^ 2) +
        (2 * s - 1) * B * (∑ i, ∑ j, G i j) - B ^ 2 * N ^ 2 := by
    have hf (i j : ι) : f (G i j) =
        2 * s * G i j ^ 2 + (2 * s - 1) * B * G i j - B ^ 2 := by
      dsimp only [f]
      ring
    simp_rw [hf, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp only [N]
    ring
  rw [hpoly] at hupper
  have hbound : B ^ 2 * N ^ 2 ≤ B ^ 2 * (4 * s * N) := by
    nlinarith only [htrace, hcoef, hupper]
  have hcancel := le_of_mul_le_mul_left hbound (sq_pos_of_pos hB')
  have hcard : N ≤ 4 * s :=
    le_of_mul_le_mul_right (by simpa only [pow_two] using hcancel) hN
  change (Fintype.card ι : ℝ) ≤ 4 * (Fintype.card κ : ℝ) at hcard
  exact_mod_cast hcard

/-- The same bound with the original divided off-diagonal hypothesis. -/
theorem card_le_four_mul_of_div (β : κ → ℝ) (σ : κ → ι → ℝ)
    (hβ : ∀ p, 0 ≤ β p) (hσ : ∀ p i, σ p i ^ 2 = 1)
    (hB : 0 < ∑ p, β p)
    (hoff : ∀ i j, i ≠ j →
      gram β σ i j ≤ (∑ p, β p) / (2 * (Fintype.card κ : ℝ))) :
    Fintype.card ι ≤ 4 * Fintype.card κ := by
  have hs : 0 < Fintype.card κ := by
    simpa only [Finset.card_univ] using
      Finset.card_pos.mpr (Finset.nonempty_of_sum_ne_zero (ne_of_gt hB))
  have hd : 0 < 2 * (Fintype.card κ : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr hs)
  apply card_le_four_mul β σ hβ hσ hB
  intro i j hij
  simpa only [mul_comm] using (le_div_iff₀ hd).mp (hoff i j hij)

/-- The nonnegative-real weight interface to the denominator-free bound. -/
theorem card_le_four_mul_nnreal (β : κ → ℝ≥0) (σ : κ → ι → ℝ)
    (hσ : ∀ p i, σ p i ^ 2 = 1) (hB : 0 < ∑ p, (β p : ℝ))
    (hoff : ∀ i j, i ≠ j →
      2 * (Fintype.card κ : ℝ) * gram (fun p => (β p : ℝ)) σ i j ≤
        ∑ p, (β p : ℝ)) :
    Fintype.card ι ≤ 4 * Fintype.card κ :=
  card_le_four_mul (fun p => (β p : ℝ)) σ (fun p => (β p).coe_nonneg) hσ hB hoff

/-- Nonnegative-real weights and the divided off-diagonal hypothesis. -/
theorem card_le_four_mul_nnreal_of_div (β : κ → ℝ≥0) (σ : κ → ι → ℝ)
    (hσ : ∀ p i, σ p i ^ 2 = 1) (hB : 0 < ∑ p, (β p : ℝ))
    (hoff : ∀ i j, i ≠ j →
      gram (fun p => (β p : ℝ)) σ i j ≤
        (∑ p, (β p : ℝ)) / (2 * (Fintype.card κ : ℝ))) :
    Fintype.card ι ≤ 4 * Fintype.card κ :=
  card_le_four_mul_of_div (fun p => (β p : ℝ)) σ
    (fun p => (β p).coe_nonneg) hσ hB hoff

/-- Restriction to a finite vertex set, with no finiteness assumption on its
ambient type. Only signs and off-diagonal bounds on that set are needed. -/
theorem card_finset_le_four_mul {α : Type*} (T : Finset α)
    (β : κ → ℝ) (σ : κ → α → ℝ)
    (hβ : ∀ p, 0 ≤ β p) (hσ : ∀ p i, i ∈ T → σ p i ^ 2 = 1)
    (hB : 0 < ∑ p, β p)
    (hoff : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      2 * (Fintype.card κ : ℝ) * gram β σ i j ≤ ∑ p, β p) :
    T.card ≤ 4 * Fintype.card κ := by
  classical
  simpa only [Fintype.card_coe] using
    card_le_four_mul β (fun p (i : T) => σ p i)
      hβ (fun p i => hσ p i i.property) hB
      (fun i j hij => hoff i i.property j j.property (fun h => hij (Subtype.ext h)))

end

end E126.Spherical126
