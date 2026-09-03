import Submission.QuarticBranching
import Submission.BinaryNormBound

/-! Bounds for every common integral scale of the ternary branching family.
Unlike the earlier product-denominator estimate, the common scale here may
be chosen arbitrarily. These are not upper bounds for all representations. -/
namespace Erdos322Research.QuarticBranchingDenominators

open QuarticBranching

/-- The first two coordinates lie on a fixed positive definite ellipse. -/
theorem ellipse_identity {P : Point ℤ} (hP : Good P) :
    1207*(rationalTriple P 0+rationalTriple P 1)^2+
      213*(rationalTriple P 0-rationalTriple P 1)^2=20164 := by
  have hw : (P.w : ℚ) ≠ 0 := by exact_mod_cast hP.w_ne
  have hq : (P.w : ℚ)^2=1207*(P.s : ℚ)^2+213*(P.t : ℚ)^2 := by
    exact_mod_cast hP.quad2
  simp only [rationalTriple,Matrix.cons_val_zero,Matrix.cons_val_one]
  field_simp
  linear_combination -20164*hq

theorem third_square_identity {P : Point ℤ} (hP : Good P) :
    rationalTriple P 2^2=6*(rationalTriple P 0+rationalTriple P 1)^2+
      (rationalTriple P 0-rationalTriple P 1)^2 := by
  have hw : (P.w : ℚ) ≠ 0 := by exact_mod_cast hP.w_ne
  have hq : (P.z : ℚ)^2=6*(P.s : ℚ)^2+(P.t : ℚ)^2 := by
    exact_mod_cast hP.quad1
  simp only [rationalTriple,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  field_simp
  linear_combination 20164*hq

private lemma signed_natAbs_injective :
    Function.Injective (fun z : ℤ ↦ (z.natAbs,decide (z<0))) := by
  intro a b he
  have ha := congrArg Prod.fst he
  have ht := decide_eq_decide.mp (congrArg Prod.snd he)
  have he' : |a|=|b| := by
    have hcast := congrArg (fun n : ℕ ↦ (n : ℤ)) ha
    simpa only [Int.natCast_natAbs] using hcast
  by_cases h : a<0
  · have h' : b<0 := ht.mp h
    rw [abs_of_neg h,abs_of_neg h'] at he'
    omega
  · have h' : ¬b<0 := fun hh ↦ h (ht.mpr hh)
    rw [abs_of_nonneg (by omega),abs_of_nonneg (by omega)] at he'
    exact he'

/-- An arbitrary common integral scale of the entire depth-d family has a
subpolynomial capacity, regardless of how that scale was obtained. -/
theorem arbitrary_scale_count_bound (d L : ℕ) (hL : 0 < L)
    (hint : ∀ f : Fin d → Fin 3, ∀ i : Fin 3,
      ∃ z : ℤ, (L : ℚ)*rationalTriple (point d f) i=z) :
    3^d ≤ 4*(binaryNormSolutions (1207*213) (1207*20164*L^2)).card := by
  classical
  choose z hz using hint
  let U : (Fin d → Fin 3) → ℤ := fun f ↦ 1207*(z f 0+z f 1)
  let V : (Fin d → Fin 3) → ℤ := fun f ↦ z f 0-z f 1
  let N := 1207*20164*L^2
  have hnorm (f : Fin d → Fin 3) : (U f)^2+(1207*213)*(V f)^2=(N : ℤ) := by
    have hq := ellipse_identity (point_good d f)
    have he : 1207*((z f 0 : ℚ)+z f 1)^2+
        213*((z f 0 : ℚ)-z f 1)^2=20164*(L : ℚ)^2 := by
      rw [← hz f 0,← hz f 1]
      linear_combination (L : ℚ)^2*hq
    have he' : 1207*(z f 0+z f 1)^2+213*(z f 0-z f 1)^2=20164*(L : ℤ)^2 := by
      exact_mod_cast he
    dsimp only [U,V,N]
    push_cast
    linear_combination 1207*he'
  have hmem (f : Fin d → Fin 3) :
      ((U f).natAbs,(V f).natAbs) ∈ binaryNormSolutions (1207*213) N := by
    apply (mem_binaryNormSolutions (by decide : 0 < 1207*213) _).mpr
    have h : (((U f).natAbs : ℤ))^2+(1207*213)*(((V f).natAbs : ℤ))^2=(N : ℤ) := by
      simpa only [Int.natCast_natAbs,sq_abs] using hnorm f
    exact_mod_cast h
  let enc (f : Fin d → Fin 3) :=
    (((U f).natAbs,(V f).natAbs),(decide (U f<0),decide (V f<0)))
  have hinj : Function.Injective enc := by
    intro f g he
    have hU : U f=U g := signed_natAbs_injective (by
      apply Prod.ext
      · exact congrArg (fun e ↦ e.1.1) he
      · exact congrArg (fun e ↦ e.2.1) he)
    have hV : V f=V g := signed_natAbs_injective (by
      apply Prod.ext
      · exact congrArg (fun e ↦ e.1.2) he
      · exact congrArg (fun e ↦ e.2.2) he)
    dsimp only [U,V] at hU hV
    have h0 : z f 0=z g 0 := by omega
    have h1 : z f 1=z g 1 := by omega
    have hL0 : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
    have hq0 : rationalTriple (point d f) 0=rationalTriple (point d g) 0 := by
      apply mul_left_cancel₀ hL0
      rw [hz f 0,hz g 0,h0]
    have hq1 : rationalTriple (point d f) 1=rationalTriple (point d g) 1 := by
      apply mul_left_cancel₀ hL0
      rw [hz f 1,hz g 1,h1]
    apply point_squared_triple_injective d
    funext i
    fin_cases i
    · change rationalTriple (point d f) 0^2=rationalTriple (point d g) 0^2
      rw [hq0]
    · change rationalTriple (point d f) 1^2=rationalTriple (point d g) 1^2
      rw [hq1]
    · change rationalTriple (point d f) 2^2=rationalTriple (point d g) 2^2
      rw [third_square_identity (point_good d f),third_square_identity (point_good d g),hq0,hq1]
  have hcard := Finset.card_le_card_of_injOn enc
    (s := Finset.univ)
    (t := (binaryNormSolutions (1207*213) N) ×ˢ (Finset.univ : Finset (Bool × Bool)))
    (by
      intro f hf
      exact Finset.mem_product.mpr ⟨hmem f,Finset.mem_univ _⟩)
    hinj.injOn
  simpa only [Finset.card_product,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
    Fintype.card_prod,Fintype.card_bool,show 2*2=4 by decide,N,mul_comm] using hcard

/-- Uniform in the depth and in the choice of common integral scale. -/
theorem arbitrary_scale_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ d L : ℕ, 0 < L →
      (∀ f : Fin d → Fin 3, ∀ i : Fin 3,
        ∃ z : ℤ, (L : ℚ)*rationalTriple (point d f) i=z) →
      (3 : ℝ)^d ≤ C*(L : ℝ)^ε := by
  obtain ⟨A,hA,hbound⟩ := binary_norm_subpolynomial_general
    (by decide : 0 < 1207*213) (ε/2) (by linarith)
  refine ⟨4*A*((1207*20164 : ℕ) : ℝ)^(ε/2),by positivity,?_⟩
  intro d L hL hint
  have hp : ((L : ℝ)^2)^(ε/2)=(L : ℝ)^ε := by
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg L)]
    congr 1
    norm_num
    ring
  calc
    (3 : ℝ)^d ≤ 4*((binaryNormSolutions (1207*213) (1207*20164*L^2)).card : ℝ) := by
      exact_mod_cast arbitrary_scale_count_bound d L hL hint
    _ ≤ 4*(A*((1207*20164*L^2 : ℕ) : ℝ)^(ε/2)) := by
      gcongr
      exact hbound _ (by positivity)
    _ = (4*A*((1207*20164 : ℕ) : ℝ)^(ε/2))*(L : ℝ)^ε := by
      rw [Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity),Nat.cast_pow,hp]
      ring

/-- The target obtained from any admissible common scale by doubling the
three coordinates and appending one, as in the original construction. -/
def scaledTarget (L : ℕ) : ℕ := 10082*(2*L)^4+1

private lemma scale_le_target (L : ℕ) : L ≤ scaledTarget L := by
  have hp : L ≤ L^4 := Nat.le_pow (by decide)
  dsimp only [scaledTarget]
  nlinarith

/-- Even replacing the product denominator by an arbitrary optimized common
scale leaves the certified contribution subpolynomial in its target. -/
theorem optimized_contribution_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ d L : ℕ, 0 < L →
      (∀ f : Fin d → Fin 3, ∀ i : Fin 3,
        ∃ z : ℤ, (L : ℚ)*rationalTriple (point d f) i=z) →
      (3 : ℝ)^d ≤ C*(scaledTarget L : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := arbitrary_scale_subpolynomial ε hε
  refine ⟨C,hC,fun d L hL hint ↦ (hbound d L hL hint).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast scale_le_target L) hε.le

/-- No sequence of optimized common scales can turn the `3^d` certified
representations into infinitely many fixed-positive-power peaks. This says
nothing about additional, uncounted representations of the same targets. -/
theorem certified_peaks_finite (c : ℝ) (hc : 0 < c) (L : ℕ → ℕ)
    (hL : ∀ d, 0 < L d)
    (hint : ∀ d, ∀ f : Fin d → Fin 3, ∀ i : Fin 3,
      ∃ z : ℤ, (L d : ℚ)*rationalTriple (point d f) i=z) :
    {n : ℕ | ∃ d : ℕ, n=scaledTarget (L d) ∧ (n : ℝ)^c < (3 : ℝ)^d}.Finite := by
  obtain ⟨C,hC,hbound⟩ := optimized_contribution_subpolynomial (c/2) (by linarith)
  have ht : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)^(c/2)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < c/2)).comp tendsto_natCast_atTop_atTop
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop C)
  apply (Finset.finite_toSet (Finset.range M)).subset
  rintro n ⟨d,rfl,hd⟩
  simp only [Finset.mem_coe,Finset.mem_range]
  by_contra hnot
  have hlarge := hM (scaledTarget (L d)) (by omega)
  have hb := hbound d (L d) (hL d) (hint d)
  have hn : (0 : ℝ) < scaledTarget (L d) := by
    exact_mod_cast (show 0 < scaledTarget (L d) by unfold scaledTarget; positivity)
  have hp : (scaledTarget (L d) : ℝ)^(c/2)*(scaledTarget (L d) : ℝ)^(c/2)=
      (scaledTarget (L d) : ℝ)^c := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have he := mul_le_mul_of_nonneg_right hlarge
    (Real.rpow_nonneg hn.le (c/2))
  rw [hp] at he
  linarith

end Erdos322Research.QuarticBranchingDenominators
