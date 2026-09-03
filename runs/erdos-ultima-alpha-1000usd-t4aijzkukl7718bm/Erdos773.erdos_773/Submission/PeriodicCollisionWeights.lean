import Submission.ParityTriangleCount

/-!
Periodic averaging of the parity and small-prime sieve weights. The estimates
are uniform and have explicit additive errors.
-/
noncomputable section
namespace Erdos773.PeriodicCollisionWeights
open Finset PrimitiveSquareCollisions ParityTriangleCount
set_option maxHeartbeats 1000000

def row (u : ℕ) : ℕ := ∑ v ∈ range 30, sieveWeight u v

lemma row_le (u : ℕ) : row u ≤ 60 := by
  calc
    _ ≤ ∑ _v ∈ range 30, 2 := sum_le_sum (fun v _ => sieveWeight_le_two u v)
    _ = 60 := by norm_num

lemma row_mod (u : ℕ) : row u = row (u%30) := by
  apply sum_congr rfl
  intro v hv
  rw [sieveWeight_mod u v,Nat.mod_eq_of_lt (mem_range.mp hv)]

lemma row_sum : ∑ u ∈ range 30, row u = 768 := sieveWeight_sum

lemma weighted_interval (S : Finset ℕ) (u : ℕ) (L U : ℝ) (hLU : L ≤ U)
    (hS : ∀ v ∈ S, L ≤ v ∧ (v : ℝ) ≤ U) :
    (∑ v ∈ S, (sieveWeight u v : ℝ)) ≤ (row u : ℝ)*((U-L)/30+1) := by
  have hf := sum_fiberwise_of_maps_to
    (fun (v : ℕ) (_hv : v ∈ S) => mem_range.mpr (Nat.mod_lt v (by omega : 0 < 30)))
    (fun v => (sieveWeight u v : ℝ))
  rw [← hf]
  calc
    _ = ∑ j ∈ range 30, (sieveWeight u j : ℝ)*(S.filter (fun v => v%30=j)).card := by
      apply sum_congr rfl
      intro j hj
      calc
        _ = ∑ _v ∈ S.filter (fun v => v%30=j), (sieveWeight u j : ℝ) := by
          apply sum_congr rfl
          intro v hv
          rw [sieveWeight_mod_right u v,(mem_filter.mp hv).2]
        _ = _ := by simp [mul_comm]
    _ ≤ ∑ j ∈ range 30, (sieveWeight u j : ℝ)*((U-L)/30+1) := by
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply residue_interval_card_bound _ L U 30 j (by omega) hLU
      intro v hv
      obtain ⟨hv,hpar⟩ := mem_filter.mp hv
      exact ⟨hpar,(hS v hv).1,(hS v hv).2⟩
    _ = _ := by rw [← sum_mul]; norm_cast

lemma weighted_bin (S : Finset ℕ) (u i : ℕ)
    (hS : ∀ v ∈ S, u*i ≤ 20*v ∧ 20*v ≤ u*(i+1)) :
    (∑ v ∈ S, (sieveWeight u v : ℝ)) ≤ (row u : ℝ)*((u:ℝ)/600+1) := by
  have hl : (0 : ℝ) ≤ u := by positivity
  have hb := weighted_interval S u ((u:ℝ)*i/20) ((u:ℝ)*(i+1)/20)
    (by nlinarith) (by
      intro v hv
      obtain ⟨hvlo,hvhi⟩ := hS v hv
      have hlo : (u:ℝ)*i ≤ 20*v := by exact_mod_cast hvlo
      have hhi : 20*(v:ℝ) ≤ (u:ℝ)*(i+1) := by exact_mod_cast hvhi
      constructor <;> nlinarith only [hlo,hhi])
  have heq : (((u:ℝ)*(i+1)/20)-(u:ℝ)*i/20)/30+1 = (u:ℝ)/600+1 := by ring
  rwa [heq] at hb

lemma row_harmonic (M : ℕ) :
    (∑ u ∈ Icc 1 M, (row u : ℝ)/u) ≤ (768/30:ℝ)*harmonic M+1800 := by
  let T := (Icc 1 M).filter (fun u => 30 ≤ u)
  let P := (Icc 1 M).filter (fun u => ¬30 ≤ u)
  let F : ℕ × ℕ → ℝ := fun t => (row t.2 : ℝ)/(30*t.1)
  have hPcard : P.card ≤ 30 := by
    apply (card_le_card (show P ⊆ range 30 by
      intro u hu
      obtain ⟨_,hu⟩ := mem_filter.mp hu
      exact mem_range.mpr (by omega))).trans_eq
    exact card_range 30
  have hP : (∑ u ∈ P, (row u : ℝ)/u) ≤ 1800 := by
    calc
      _ ≤ ∑ _u ∈ P, (60:ℝ) := by
        apply sum_le_sum
        intro u hu
        have hu1 := (mem_Icc.mp (mem_filter.mp hu).1).1
        have huR : (1:ℝ) ≤ u := by exact_mod_cast hu1
        have hur : (row u : ℝ) ≤ 60 := by exact_mod_cast row_le u
        apply (div_le_iff₀ (by linarith : (0:ℝ)<u)).mpr
        nlinarith only [huR,hur]
      _ = 60*(P.card : ℝ) := by simp [mul_comm]
      _ ≤ 1800 := by exact_mod_cast (show 60*P.card ≤ 1800 by omega)
  have hmap : (T.image (fun u => (u/30,u%30))) ⊆ (Icc 1 M) ×ˢ range 30 := by
    intro t ht
    obtain ⟨u,hu,rfl⟩ := mem_image.mp ht
    obtain ⟨hu,hu30⟩ := mem_filter.mp hu
    have huM := (mem_Icc.mp hu).2
    apply mem_product.mpr
    exact ⟨mem_Icc.mpr ⟨by omega,(Nat.div_le_self _ _).trans huM⟩,
      mem_range.mpr (Nat.mod_lt _ (by omega))⟩
  have hinj : Set.InjOn (fun u : ℕ => (u/30,u%30)) T := by
    intro u hu v hv he
    simp only [Prod.mk.injEq] at he
    omega
  have hT : (∑ u ∈ T, (row u : ℝ)/u) ≤ (768/30:ℝ)*harmonic M := by
    calc
      _ ≤ ∑ u ∈ T, F (u/30,u%30) := by
        apply sum_le_sum
        intro u hu
        have hu30 := (mem_filter.mp hu).2
        have hk : (0:ℝ) < 30*(u/30 : ℕ) := by exact_mod_cast (show 0<30*(u/30) by omega)
        have hup : (30:ℝ)*(u/30 : ℕ) ≤ u := by exact_mod_cast Nat.mul_div_le u 30
        dsimp [F]
        rw [row_mod u]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hk hup
      _ = ∑ t ∈ T.image (fun u => (u/30,u%30)), F t := (sum_image hinj).symm
      _ ≤ ∑ t ∈ (Icc 1 M) ×ˢ range 30, F t :=
        sum_le_sum_of_subset_of_nonneg hmap (fun t ht _ => by
          exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
      _ = (768/30:ℝ)*harmonic M := by
        rw [sum_product]
        dsimp [F]
        simp only [← sum_div]
        have hrow : (∑ v ∈ range 30, (row v : ℝ)) = 768 := by exact_mod_cast row_sum
        simp only [hrow,div_mul_eq_div_div]
        rw [harmonic_eq_sum_Icc]
        push_cast
        simp only [div_eq_mul_inv,← mul_sum]
  have heq : (∑ u ∈ T, (row u : ℝ)/u)+(∑ u ∈ P, (row u : ℝ)/u) =
      ∑ u ∈ Icc 1 M, (row u : ℝ)/u := sum_filter_add_sum_filter_not _ _ _
  linarith

lemma row_log (M : ℕ) :
    (∑ u ∈ Icc 1 M, (row u : ℝ)/u) ≤ (768/30:ℝ)*(1+Real.log M)+1800 := by
  have hh := harmonic_le_one_add_log M
  have hb := row_harmonic M
  nlinarith only [hh,hb]

lemma inverse_square_sum (M : ℕ) : (∑ u ∈ Icc 1 M, 1/(u:ℝ)^2) ≤ 2 := by
  have hstrong (M : ℕ) : (∑ u ∈ Icc 1 M, 1/(u:ℝ)^2) ≤ 2-2/((M:ℝ)+1) := by
    induction M with
    | zero => norm_num
    | succ M ih =>
      rw [sum_Icc_succ_top (by omega)]
      push_cast
      have hstep : 1/((M:ℝ)+1)^2 ≤ 2/((M:ℝ)+1)-2/((M:ℝ)+2) := by
        have h1 : (0:ℝ) < M+1 := by positivity
        have h2 : (0:ℝ) < M+2 := by positivity
        apply (div_le_iff₀ (sq_pos_of_pos h1)).mpr
        field_simp
        nlinarith
      have he : (M:ℝ)+1+1 = M+2 := by ring
      rw [he]
      linarith
  have hh := hstrong M
  have hn : (0:ℝ) ≤ 2/((M:ℝ)+1) := by positivity
  linarith

#print axioms weighted_interval
#print axioms weighted_bin
#print axioms row_harmonic
#print axioms row_log
#print axioms inverse_square_sum
end Erdos773.PeriodicCollisionWeights
