import Submission.RoughHalfMean

/-!
# Uniform initial cutoffs in the below-half primitive-conductor means

The arithmetic sum may stop at any X below the ambient scale. All conductor
level and power-saving restrictions remain unchanged.
-/
open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

theorem primitivePoolMean_le_unbalanced_cutoff (P : Finset ℕ) (L Q U V N B X : ℕ) (hXN : X ≤ N)
    (hL : 0 < L) (hQ : 0 < Q)
    (hP : ∀ d ∈ P, 2 ≤ d ∧ L ≤ d ∧ d ≤ Q)
    (hB : 1 ≤ B) (hBU : B^2 ≤ U+1) (hBV : B^2 ≤ V) :
    primitivePoolMean P X ≤
      ((Q : ℝ)^2*vaughanShortMajorant U V N Q + unbalancedTypeIIMajorant N Q B)/(L : ℝ) := by
  let M : Finset ℕ+ := P.attach.image (fun d => ⟨d.val, by have := (hP d.val d.property).1; omega⟩)
  have hmem {d : ℕ+} : d ∈ M ↔ (d : ℕ) ∈ P := by
    constructor
    · intro hd
      obtain ⟨e, he, heq⟩ := mem_image.mp hd
      have hv := congrArg (fun x : ℕ+ => (x : ℕ)) heq
      change e.val = (d : ℕ) at hv
      exact hv ▸ e.property
    · intro hd
      exact mem_image.mpr ⟨⟨d,hd⟩, mem_attach _ _, Subtype.ext rfl⟩
  have hsum (F : ℕ → ℝ) : (∑ d ∈ M, F d) = ∑ d ∈ P, F d := by
    apply sum_bij (fun (d : ℕ+) _ => (d : ℕ))
    · intro d hd
      exact hmem.mp hd
    · intro d hd e he h
      exact PNat.coe_injective h
    · intro d hd
      have hd0 : 0 < d := by have := (hP d hd).1; omega
      exact ⟨⟨d,hd0⟩, hmem.mpr hd, rfl⟩
    · intros
      rfl
  have hmean := primitive_vonMangoldt_unbalanced_mean_bound M Q hQ
    (fun d hd => ⟨(hP d (hmem.mp hd)).1, (hP d (hmem.mp hd)).2.2⟩)
    (fun d => primitiveCharacters (d : ℕ))
    (fun _ _ _ hc => (mem_filter.mp hc).2) U V N B hB hBU hBV
    (fun _ _ => X) (fun _ _ _ _ => hXN)
  dsimp only at hmean
  rw [hsum (fun d => (d : ℝ)/(d.totient : ℝ) * ∑ χ ∈ primitiveCharacters d, ‖twistedArithmeticSum χ vonMangoldt X‖)] at hmean
  apply (le_div_iff₀ (by exact_mod_cast hL : (0 : ℝ) < L)).mpr
  rw [mul_comm, primitivePoolMean, mul_sum]
  apply (sum_le_sum (fun d hd => ?_)).trans hmean
  have hdL : (L : ℝ) ≤ d := by exact_mod_cast (hP d hd).2.1
  calc
    _ ≤ (d : ℝ)*((∑ χ ∈ primitiveCharacters d, ‖twistedArithmeticSum χ vonMangoldt X‖)/(d.totient : ℝ)) :=
      mul_le_mul_of_nonneg_right hdL (div_nonneg (sum_nonneg (fun _ _ => norm_nonneg _)) (Nat.cast_nonneg _))
    _ = _ := by ring

theorem wide_primitive_mean_bound_cutoff (P : Finset ℕ) (a b t m X : ℕ) (hXN : X ≤ progressionScaleN (t*m))
    (ha : 1 ≤ a) (ht : 1 ≤ t) (hhalf : 2*b ≤ t)
    (h1 : 4*b+1 ≤ t+2*a) (h2 : 64*b+1 ≤ 64*a+3*t)
    (hP : ∀ d ∈ P, 2 ≤ d ∧ progressionScaleN (a*m) ≤ d ∧ d ≤ progressionScaleN (b*m)) :
    primitivePoolMean P X ≤
      (wideMeanConstant t : ℝ)*((m : ℝ)+1)^5*(2 : ℝ)^((64*t-1)*m) := by
  let Q := progressionScaleN (b*m)
  let N := progressionScaleN (t*m)
  let U := progressionScaleU (t*m)
  let L : ℝ := progressionScaleN (a*m)
  let B : ℕ := 2^(3*(t*m))
  let z : ℝ := ((t*m : ℕ) : ℝ)+1
  let F : ℝ := (2 : ℝ)^((64*t-1)*m)
  have hz : 1 ≤ z := by dsimp [z]; linarith [Nat.cast_nonneg (α := ℝ) (t*m)]
  have hL : 0 < L := by dsimp [L, progressionScaleN]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hB : 1 ≤ B := Nat.one_le_of_lt (by dsimp [B]; positivity)
  have hBU : B^2 = U := by dsimp [B,U,progressionScaleU]; rw [← pow_mul]; congr 1; ring
  have hmean := primitivePoolMean_le_unbalanced_cutoff P (progressionScaleN (a*m)) Q U U N B X hXN
    (by unfold progressionScaleN; positivity) (by dsimp [Q,progressionScaleN]; positivity) hP hB
    (by rw [hBU]; omega) (by rw [hBU])
  have hrat := wide_conductor_scale_ratios a b t m ha ht h1 h2
  change (Q : ℝ)^2*Real.sqrt N/L ≤ F ∧ (Q : ℝ)*N/B/L ≤ F ∧ (N : ℝ)/L ≤ F at hrat
  have hQhalf : Q ≤ progressionScaleQ (t*m) 0 := by
    simp only [Q, progressionScaleN, progressionScaleQ, Nat.mul_zero, Nat.sub_zero]
    apply Nat.pow_le_pow_right (by decide)
    nlinarith only [Nat.mul_le_mul_right m hhalf]
  have hshort : vaughanShortMajorant U U N Q ≤ 6400*z^2*Real.sqrt N := by
    apply (vaughanShortMajorant_mono_modulus U U N hQhalf).trans
    dsimp only [U,N,z]
    rw [sqrt_progressionScaleN]
    exact progression_scales_short_bound (t*m) 0
  have hshortDiv : (Q : ℝ)^2*vaughanShortMajorant U U N Q/L ≤ 6400*z^2*F := by
    calc
      _ ≤ (Q : ℝ)^2*(6400*z^2*Real.sqrt N)/L := by gcongr
      _ = 6400*z^2*((Q : ℝ)^2*Real.sqrt N/L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrat.1 (by positivity)
  have hIIDiv : unbalancedTypeIIMajorant N Q B/L ≤ 3000000000000*z^5*F := by
    calc
      _ ≤ (1000000000000*z^5*((Q : ℝ)^2*Real.sqrt N+(Q : ℝ)*N/B+N))/L :=
        div_le_div_of_nonneg_right (unbalanced_majorant_scale_log_bound (t*m) Q B) hL.le
      _ = 1000000000000*z^5*((Q : ℝ)^2*Real.sqrt N/L+(Q : ℝ)*N/B/L+(N : ℝ)/L) := by ring
      _ ≤ 1000000000000*z^5*(F+F+F) :=
        mul_le_mul_of_nonneg_left (_root_.add_le_add (_root_.add_le_add hrat.1 hrat.2.1) hrat.2.2) (by positivity)
      _ = _ := by ring
  have hraw : primitivePoolMean P X ≤ 4000000000000*z^5*F := by
    change primitivePoolMean P X ≤ ((Q : ℝ)^2*vaughanShortMajorant U U N Q+unbalancedTypeIIMajorant N Q B)/L at hmean
    rw [add_div] at hmean
    have hz25 := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hz (by decide : 2 ≤ 5)) hF
    have hn : 0 ≤ z^5*F := by positivity
    nlinarith only [hmean,hshortDiv,hIIDiv,hz25,hn]
  apply hraw.trans
  have hzUp : z ≤ ((t : ℝ)+1)*((m : ℝ)+1) := by
    dsimp [z]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) t, Nat.cast_nonneg (α := ℝ) m]
  calc
    _ ≤ 4000000000000*(((t : ℝ)+1)*((m : ℝ)+1))^5*F := by gcongr
    _ = _ := by
      simp only [wideMeanConstant, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        Nat.cast_add, Nat.cast_one, mul_pow, F]
      ring

theorem interval_primitive_mean_below_half_cutoff (a b t m X : ℕ) (hXN : X ≤ progressionScaleN (t*m))
    (ha : 1 ≤ a) (hab : a ≤ b) (ht : 22 ≤ t) (hb : 2*b+5 ≤ t) (hm : 1 ≤ m) :
    primitivePoolMean (Icc (progressionScaleN (a*m)) (progressionScaleN (b*m)))
      X ≤
      ((b+1 : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*((m : ℝ)+1)^5*
        (2 : ℝ)^((64*t-1)*m) := by
  let Q (j : ℕ) := Icc (progressionScaleN (j*m)) (progressionScaleN ((j+1)*m))
  have hf : Monotone (fun j => progressionScaleN (j*m)) := by
    intro i j hij
    unfold progressionScaleN
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 64 (Nat.mul_le_mul_right m hij))
  have hcover := exists_consecutive_interval_cover (fun j => progressionScaleN (j*m)) hf a b hab
  have hs := sum_le_sum_interval_cover
    (Icc (progressionScaleN (a*m)) (progressionScaleN (b*m))) (Icc a b) Q
    (fun d => (∑ χ ∈ primitiveCharacters d, ‖twistedArithmeticSum χ vonMangoldt X‖)/(d.totient : ℝ))
    (fun d => by positivity) hcover
  change primitivePoolMean _ _ ≤ ∑ j ∈ Icc a b, primitivePoolMean (Q j) _ at hs
  have hmean (j : ℕ) (hj : j ∈ Icc a b) :
      primitivePoolMean (Q j) X ≤
        (wideMeanConstant t : ℝ)*((m : ℝ)+1)^5*(2 : ℝ)^((64*t-1)*m) := by
    obtain ⟨haj,hjb⟩ := mem_Icc.mp hj
    apply wide_primitive_mean_bound_cutoff (Q j) j (j+1) t m X hXN (by omega) (by omega)
      (by omega) (by omega) (by omega)
    intro d hd
    have hd' := mem_Icc.mp hd
    refine ⟨?_,hd'⟩
    have he : 0 < 64*(j*m) := Nat.mul_pos (by decide) (Nat.mul_pos (by omega) hm)
    exact (Nat.one_lt_pow he.ne' (by decide)).trans_le hd'.1
  apply hs.trans
  calc
    _ ≤ ∑ _j ∈ Icc a b, (wideMeanConstant t : ℝ)*((m : ℝ)+1)^5*(2 : ℝ)^((64*t-1)*m) :=
      sum_le_sum hmean
    _ = ((Icc a b).card : ℝ)*((wideMeanConstant t : ℝ)*((m : ℝ)+1)^5*(2 : ℝ)^((64*t-1)*m)) := by
      simp only [sum_const,nsmul_eq_mul]
    _ ≤ _ := by
      have hc : (Icc a b).card ≤ b+1 := by simp only [Nat.card_Icc]; omega
      have hcR : ((Icc a b).card : ℝ) ≤ (b+1 : ℕ) := by exact_mod_cast hc
      have hh := mul_le_mul_of_nonneg_right hcR
        (show 0 ≤ (wideMeanConstant t : ℝ)*((m : ℝ)+1)^5*(2 : ℝ)^((64*t-1)*m) by positivity)
      simpa only [mul_assoc] using hh

end Erdos821
