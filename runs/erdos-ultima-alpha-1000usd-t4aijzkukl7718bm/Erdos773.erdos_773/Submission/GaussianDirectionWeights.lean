import Submission.PeriodicCollisionWeights

/-! A period-210 sieve for primitive opposite-parity Gaussian directions. -/
noncomputable section
namespace Erdos773.GaussianDirectionWeights
open Finset ParityTriangleCount
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

def weight (u v : ℕ) : ℕ :=
  if u%2=v%2 ∨ (u%3=0 ∧ v%3=0) ∨ (u%5=0 ∧ v%5=0) ∨ (u%7=0 ∧ v%7=0) then 0 else 1

lemma weight_le_one (u v : ℕ) : weight u v ≤ 1 := by unfold weight; split_ifs <;> omega

lemma weight_of_coprime {u v : ℕ} (hc : u.Coprime v) (hp : u%2 ≠ v%2) : weight u v=1 := by
  have hnot (p : ℕ) (hp : 1<p) : ¬(u%p=0 ∧ v%p=0) := by
    rintro ⟨hu,hv⟩
    have hd := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hu) (Nat.dvd_of_mod_eq_zero hv)
    rw [hc.gcd_eq_one] at hd
    have hh := Nat.le_of_dvd (by omega : 0<1) hd
    omega
  simp [weight,hp,hnot 3 (by omega),hnot 5 (by omega),hnot 7 (by omega)]

lemma weight_mod (u v : ℕ) : weight u v=weight (u%210) (v%210) := by
  simp only [weight,Nat.mod_mod_of_dvd _ (by decide : 2∣210),
    Nat.mod_mod_of_dvd _ (by decide : 3∣210),Nat.mod_mod_of_dvd _ (by decide : 5∣210),
    Nat.mod_mod_of_dvd _ (by decide : 7∣210)]

lemma weight_mod_right (u v : ℕ) : weight u v=weight u (v%210) := by
  simp only [weight,Nat.mod_mod_of_dvd _ (by decide : 2∣210),
    Nat.mod_mod_of_dvd _ (by decide : 3∣210),Nat.mod_mod_of_dvd _ (by decide : 5∣210),
    Nat.mod_mod_of_dvd _ (by decide : 7∣210)]

lemma weight_sum : ∑ u ∈ range 210, ∑ v ∈ range 210, weight u v=18432 := by
  decide +kernel

def row (u : ℕ) : ℕ := ∑ v ∈ range 210, weight u v

lemma row_le (u : ℕ) : row u  ≤  210 := by
  calc
    _  ≤  ∑ _v ∈ range 210, 1 := sum_le_sum (fun v _ => weight_le_one u v)
    _ = 210 := by norm_num

lemma row_mod (u : ℕ) : row u = row (u%210) := by
  apply sum_congr rfl
  intro v hv
  rw [weight_mod u v,Nat.mod_eq_of_lt (mem_range.mp hv)]

lemma row_sum : ∑ u ∈ range 210, row u = 18432 := weight_sum

lemma weighted_interval (S : Finset ℕ) (u : ℕ) (L U : ℝ) (hLU : L  ≤  U)
    (hS : ∀ v ∈ S, L  ≤  v ∧ (v : ℝ)  ≤  U) :
    (∑ v ∈ S, (weight u v : ℝ))  ≤  (row u : ℝ)*((U-L)/210+1) := by
  have hf := sum_fiberwise_of_maps_to
    (fun (v : ℕ) (_hv : v ∈ S) => mem_range.mpr (Nat.mod_lt v (by omega : 0 < 210)))
    (fun v => (weight u v : ℝ))
  rw [← hf]
  calc
    _ = ∑ j ∈ range 210, (weight u j : ℝ)*(S.filter (fun v => v%210=j)).card := by
      apply sum_congr rfl
      intro j hj
      calc
        _ = ∑ _v ∈ S.filter (fun v => v%210=j), (weight u j : ℝ) := by
          apply sum_congr rfl
          intro v hv
          rw [weight_mod_right u v,(mem_filter.mp hv).2]
        _ = _ := by simp [mul_comm]
    _  ≤  ∑ j ∈ range 210, (weight u j : ℝ)*((U-L)/210+1) := by
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply residue_interval_card_bound _ L U 210 j (by omega) hLU
      intro v hv
      obtain ⟨hv,hpar⟩ := mem_filter.mp hv
      exact ⟨hpar,(hS v hv).1,(hS v hv).2⟩
    _ = _ := by rw [← sum_mul]; norm_cast

lemma weighted_bin (S : Finset ℕ) (u i : ℕ)
    (hS : ∀ v ∈ S, u*i  ≤  40*v ∧ 40*v  ≤  u*(i+1)) :
    (∑ v ∈ S, (weight u v : ℝ))  ≤  (row u : ℝ)*((u:ℝ)/8400+1) := by
  have hl : (0 : ℝ)  ≤  u := by positivity
  have hb := weighted_interval S u ((u:ℝ)*i/40) ((u:ℝ)*(i+1)/40)
    (by nlinarith) (by
      intro v hv
      obtain ⟨hvlo,hvhi⟩ := hS v hv
      have hlo : (u:ℝ)*i  ≤  40*v := by exact_mod_cast hvlo
      have hhi : 40*(v:ℝ)  ≤  (u:ℝ)*(i+1) := by exact_mod_cast hvhi
      constructor <;> nlinarith only [hlo,hhi])
  have heq : (((u:ℝ)*(i+1)/40)-(u:ℝ)*i/40)/210+1 = (u:ℝ)/8400+1 := by ring
  rwa [heq] at hb

lemma row_harmonic (M : ℕ) :
    (∑ u ∈ Icc 1 M, (row u : ℝ)/u)  ≤  (18432/210:ℝ)*harmonic M+44100 := by
  let T := (Icc 1 M).filter (fun u => 210  ≤  u)
  let P := (Icc 1 M).filter (fun u => ¬210  ≤  u)
  let F : ℕ × ℕ → ℝ := fun t => (row t.2 : ℝ)/(210*t.1)
  have hPcard : P.card  ≤  210 := by
    apply (card_le_card (show P ⊆ range 210 by
      intro u hu
      obtain ⟨_,hu⟩ := mem_filter.mp hu
      exact mem_range.mpr (by omega))).trans_eq
    exact card_range 210
  have hP : (∑ u ∈ P, (row u : ℝ)/u)  ≤  44100 := by
    calc
      _  ≤  ∑ _u ∈ P, (210:ℝ) := by
        apply sum_le_sum
        intro u hu
        have hu1 := (mem_Icc.mp (mem_filter.mp hu).1).1
        have huR : (1:ℝ)  ≤  u := by exact_mod_cast hu1
        have hur : (row u : ℝ)  ≤  210 := by exact_mod_cast row_le u
        apply (div_le_iff₀ (by linarith : (0:ℝ)<u)).mpr
        nlinarith only [huR,hur]
      _ = 210*(P.card : ℝ) := by simp [mul_comm]
      _  ≤  44100 := by exact_mod_cast (show 210*P.card  ≤  44100 by omega)
  have hmap : (T.image (fun u => (u/210,u%210))) ⊆ (Icc 1 M) ×ˢ range 210 := by
    intro t ht
    obtain ⟨u,hu,rfl⟩ := mem_image.mp ht
    obtain ⟨hu,hu30⟩ := mem_filter.mp hu
    have huM := (mem_Icc.mp hu).2
    apply mem_product.mpr
    exact ⟨mem_Icc.mpr ⟨by omega,(Nat.div_le_self _ _).trans huM⟩,
      mem_range.mpr (Nat.mod_lt _ (by omega))⟩
  have hinj : Set.InjOn (fun u : ℕ => (u/210,u%210)) T := by
    intro u hu v hv he
    simp only [Prod.mk.injEq] at he
    omega
  have hT : (∑ u ∈ T, (row u : ℝ)/u)  ≤  (18432/210:ℝ)*harmonic M := by
    calc
      _  ≤  ∑ u ∈ T, F (u/210,u%210) := by
        apply sum_le_sum
        intro u hu
        have hu30 := (mem_filter.mp hu).2
        have hk : (0:ℝ) < 210*(u/210 : ℕ) := by exact_mod_cast (show 0<210*(u/210) by omega)
        have hup : (210:ℝ)*(u/210 : ℕ)  ≤  u := by exact_mod_cast Nat.mul_div_le u 210
        dsimp [F]
        rw [row_mod u]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hk hup
      _ = ∑ t ∈ T.image (fun u => (u/210,u%210)), F t := (sum_image hinj).symm
      _  ≤  ∑ t ∈ (Icc 1 M) ×ˢ range 210, F t :=
        sum_le_sum_of_subset_of_nonneg hmap (fun t ht _ => by
          exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
      _ = (18432/210:ℝ)*harmonic M := by
        rw [sum_product]
        dsimp [F]
        simp only [← sum_div]
        have hrow : (∑ v ∈ range 210, (row v : ℝ)) = 18432 := by exact_mod_cast row_sum
        simp only [hrow,div_mul_eq_div_div]
        rw [harmonic_eq_sum_Icc]
        push_cast
        simp only [div_eq_mul_inv,← mul_sum]
  have heq : (∑ u ∈ T, (row u : ℝ)/u)+(∑ u ∈ P, (row u : ℝ)/u) =
      ∑ u ∈ Icc 1 M, (row u : ℝ)/u := sum_filter_add_sum_filter_not _ _ _
  linarith

lemma row_log (M : ℕ) :
    (∑ u ∈ Icc 1 M, (row u : ℝ)/u)  ≤  (18432/210:ℝ)*(1+Real.log M)+44100 := by
  have hh := harmonic_le_one_add_log M
  have hb := row_harmonic M
  nlinarith only [hh,hb]

#print axioms weight_sum
#print axioms weight_of_coprime
#print axioms weighted_bin
#print axioms row_log
end Erdos773.GaussianDirectionWeights
