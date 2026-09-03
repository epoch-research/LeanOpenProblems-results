import Submission.CofactorBilinearLargeSieve

/-!
# Retaining a finite multiplier pool in cofactor character means

Multiplication is reindexed with its collision multiplicity, bounded by
the divisor-square moment. No primality or distribution of the pool is
assumed, and no new smooth-prime supply is asserted here.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

noncomputable def pairCofactorCoefficient (P A : Finset ℕ) (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ z ∈ (P ×ˢ A).filter (fun z => z.1*z.2=n), w z.2

lemma pairCofactor_fiber_card_le (P A : Finset ℕ)
    (hP : ∀ c ∈ P, 0 < c) (hA : ∀ a ∈ A, 0 < a) (n : ℕ) :
    ((P ×ˢ A).filter (fun z => z.1*z.2=n)).card ≤ n.divisors.card := by
  apply card_le_card_of_injOn Prod.fst
  · intro z hz
    obtain ⟨hz,heq⟩ := mem_filter.mp hz
    obtain ⟨hc,ha⟩ := mem_product.mp hz
    exact Nat.mem_divisors.mpr ⟨heq ▸ Nat.dvd_mul_right _ _,
      (heq ▸ Nat.mul_pos (hP _ hc) (hA _ ha)).ne'⟩
  · intro z hz z' hz' heq
    obtain ⟨hz,hzn⟩ := mem_filter.mp hz
    obtain ⟨hz',hz'n⟩ := mem_filter.mp hz'
    apply Prod.ext heq
    apply Nat.eq_of_mul_eq_mul_left (hP _ (mem_product.mp hz).1)
    calc
      z.1*z.2 = n := hzn
      _ = z'.1*z'.2 := hz'n.symm
      _ = z.1*z'.2 := by rw [heq]

lemma pairCofactorCoefficient_norm_le (P A : Finset ℕ) (w : ℕ → ℂ)
    (hP : ∀ c ∈ P, 0 < c) (hA : ∀ a ∈ A, 0 < a)
    (hw : ∀ a ∈ A, ‖w a‖ ≤ 1) (n : ℕ) :
    ‖pairCofactorCoefficient P A w n‖ ≤ (n.divisors.card : ℝ) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _z ∈ (P ×ˢ A).filter (fun z => z.1*z.2=n), (1 : ℝ) := by
      apply sum_le_sum
      intro z hz
      exact hw _ (mem_product.mp (mem_filter.mp hz).1).2
    _ = (((P ×ˢ A).filter (fun z => z.1*z.2=n)).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast pairCofactor_fiber_card_le P A hP hA n

lemma pairCofactorCoefficient_energy (P A : Finset ℕ) (w : ℕ → ℂ)
    (hP : ∀ c ∈ P, 0 < c) (hA : ∀ a ∈ A, 0 < a)
    (hw : ∀ a ∈ A, ‖w a‖ ≤ 1) (X : ℕ) :
    (∑ n ∈ Icc 1 X, ‖pairCofactorCoefficient P A w n‖^2) ≤
      (X : ℝ)*(1+Real.log X)^3 := by
  apply le_trans _ (sum_divisor_card_sq_le_log X)
  apply sum_le_sum
  intro n hn
  exact pow_le_pow_left₀ (norm_nonneg _) (pairCofactorCoefficient_norm_le P A w hP hA hw n) 2

lemma pairCofactorCoefficient_character_sum (P A : Finset ℕ) (w : ℕ → ℂ)
    (D B : ℕ) (hP : P ⊆ Icc 1 D) (hA : A ⊆ Icc 1 B)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ Icc 1 (D*B), pairCofactorCoefficient P A w n*χ (n : ZMod q)) =
      (∑ c ∈ P, χ (c : ZMod q))*(∑ a ∈ A, w a*χ (a : ZMod q)) := by
  have hmap : ∀ z ∈ P ×ˢ A, z.1*z.2 ∈ Icc 1 (D*B) := by
    intro z hz
    obtain ⟨hc,ha⟩ := mem_product.mp hz
    obtain ⟨hc0,hcD⟩ := mem_Icc.mp (hP hc)
    obtain ⟨ha0,haB⟩ := mem_Icc.mp (hA ha)
    exact mem_Icc.mpr ⟨Nat.mul_pos hc0 ha0,Nat.mul_le_mul hcD haB⟩
  calc
    _ = ∑ n ∈ Icc 1 (D*B), ∑ z ∈ (P ×ˢ A).filter (fun z => z.1*z.2=n),
        w z.2*χ ((z.1*z.2 : ℕ) : ZMod q) := by
      unfold pairCofactorCoefficient
      simp only [sum_mul]
      apply sum_congr rfl
      intro n hn
      exact sum_congr rfl (fun z hz => by rw [(mem_filter.mp hz).2])
    _ = ∑ z ∈ P ×ˢ A, w z.2*χ ((z.1*z.2 : ℕ) : ZMod q) :=
      sum_fiberwise_of_maps_to hmap _
    _ = _ := by
      rw [sum_product,sum_mul]
      simp only [Nat.cast_mul,map_mul,mul_sum]
      exact sum_congr rfl (fun c hc => sum_congr rfl (fun a ha => by ring))

noncomputable def pairCofactorKernel (Q D B N : ℕ) : ℝ :=
  (1+Real.log (D*B : ℕ))^2*cofactorBilinearKernel Q (D*B) N

lemma pairCofactorKernel_nonneg (Q D B N : ℕ) : 0 ≤ pairCofactorKernel Q D B N :=
  mul_nonneg (sq_nonneg _) (cofactorBilinearKernel_nonneg _ _ _)

/-- A finite multiplier pool is retained inside the character mean. The
ambient cofactor length is D*B, not B. All product collisions are charged. -/
theorem primitive_pairCofactor_bilinear_bound (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n)
    (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q) (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive)
    (P A : Finset ℕ) (w : ℕ → ℂ) (D B N : ℕ)
    (hP : P ⊆ Icc 1 D) (hA : A ⊆ Icc 1 B) (hw : ∀ a ∈ A, ‖w a‖ ≤ 1) :
    (∑ q ∈ M, ((q : ℕ) : ℝ)/(q : ℕ).totient*∑ χ ∈ C q,
      ‖∑ c ∈ P, χ (c : ZMod (q : ℕ))‖*
      ‖∑ a ∈ A, w a*χ (a : ZMod (q : ℕ))‖*
      ‖twistedArithmeticSum χ f N‖) ≤ pairCofactorKernel Q D B N := by
  have hh := adaptive_prefix_bilinear_large_sieve_nat M Q hQ hM C hC
    (Icc 1 (D*B)) (Icc 1 N) (pairCofactorCoefficient P A w)
    (fun n => (f n : ℂ)) (D*B) N
    (fun n hn => (mem_Icc.mp hn).2) (fun n hn => (mem_Icc.mp hn).2)
    (fun _ _ => D*B) (fun _ _ _ _ => le_rfl)
  simp only [cofactorPrefix_filter _ _ le_rfl,
    pairCofactorCoefficient_character_sum P A w D B hP hA,norm_mul] at hh
  change (∑ q ∈ M, ((q : ℕ) : ℝ)/(q : ℕ).totient*∑ χ ∈ C q,
    ‖∑ c ∈ P, χ (c : ZMod (q : ℕ))‖*‖∑ a ∈ A, w a*χ (a : ZMod (q : ℕ))‖*
      ‖twistedArithmeticSum χ f N‖) ≤ _ at hh
  apply hh.trans
  let H : ℝ := 1+Real.log (D*B : ℕ)
  have hH : 1 ≤ H := by dsimp [H]; linarith [Real.log_natCast_nonneg (D*B)]
  have he := pairCofactorCoefficient_energy P A w
    (fun c hc => (mem_Icc.mp (hP hc)).1) (fun a ha => (mem_Icc.mp (hA ha)).1) hw (D*B)
  have he' : (∑ n ∈ Icc 1 (D*B), ‖pairCofactorCoefficient P A w n‖^2) ≤
      ((D*B : ℕ) : ℝ)*H^4 := by
    apply he.trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH (by decide : 3 ≤ 4)) (Nat.cast_nonneg _)
  have hfenergy : (∑ n ∈ Icc 1 N, ‖(f n : ℂ)‖^2) ≤ (N : ℝ)*(Real.log N)^2 := by
    apply le_trans _ (mangoldt_coefficient_energy N)
    apply sum_le_sum
    intro n hn
    simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]
    nlinarith [hf n,hΛ n,vonMangoldt_nonneg (n := n)]
  unfold pairCofactorKernel cofactorBilinearKernel
  rw [show H^2*((2+Real.log (((D*B : ℕ) : ℝ)+2))*Real.sqrt
      ((2*(Q : ℝ)^2+4*(2*Real.pi*(D*B : ℕ)+1))*(2*(Q : ℝ)^2+4*(2*Real.pi*N+1))*
        ((D*B : ℕ) : ℝ)*((N : ℝ)*(Real.log N)^2))) =
      (2+Real.log (((D*B : ℕ) : ℝ)+2))*(H^2*Real.sqrt
      ((2*(Q : ℝ)^2+4*(2*Real.pi*(D*B : ℕ)+1))*(2*(Q : ℝ)^2+4*(2*Real.pi*N+1))*
        ((D*B : ℕ) : ℝ)*((N : ℝ)*(Real.log N)^2))) by ring]
  apply mul_le_mul_of_nonneg_left _ (by
    have := Real.log_nonneg (show (1 : ℝ) ≤ ((D*B : ℕ) : ℝ)+2 by linarith [Nat.cast_nonneg (α := ℝ) (D*B)])
    linarith)
  rw [← Real.sqrt_sq (show 0 ≤ H^2 by positivity),← Real.sqrt_mul (sq_nonneg (H^2))]
  apply Real.sqrt_le_sqrt
  have hcoef : 0 ≤ (2*(Q : ℝ)^2+4*(2*Real.pi*(D*B : ℕ)+1))*
      (2*(Q : ℝ)^2+4*(2*Real.pi*N+1)) := by positivity
  have hb := mul_le_mul (mul_le_mul_of_nonneg_left he' hcoef) hfenergy
    (by positivity) (by positivity)
  convert hb using 1; ring

end Erdos821.AnalyticSieve
