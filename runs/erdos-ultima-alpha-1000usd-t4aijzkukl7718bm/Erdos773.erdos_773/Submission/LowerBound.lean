import FormalConjecturesUtil
import Submission.Hypergraph
import Submission.APBounds
import Submission.CollisionBounds

/-! Combining the alteration argument with bounds on square-sum collisions. -/

namespace Erdos773

open Finset Filter

lemma nontrivial_sum_cross_ne {a b c d : ℕ} (he : a + c = b + d)
    (hn : ¬ ((a = b ∧ c = d) ∨ (a = d ∧ c = b))) :
    a ≠ b ∧ a ≠ d ∧ c ≠ b ∧ c ≠ d := by omega

lemma sidonObstructions_card_either (A : Finset ℕ) (e : Finset A)
    (he : e ∈ sidonObstructions A) : e.card = 3 ∨ e.card = 4 := by
  classical
  obtain ⟨_, a, b, c, d, rfl, he, hn⟩ := Finset.mem_filter.mp he
  have hn' : ¬ ((a.val = b.val ∧ c.val = d.val) ∨ (a.val = d.val ∧ c.val = b.val)) := by
    simpa only [Subtype.ext_iff] using hn
  have hcross := nontrivial_sum_cross_ne he hn'
  have hab : a ≠ b := fun h => hcross.1 (congrArg Subtype.val h)
  have had : a ≠ d := fun h => hcross.2.1 (congrArg Subtype.val h)
  have hcb : c ≠ b := fun h => hcross.2.2.1 (congrArg Subtype.val h)
  have hcd : c ≠ d := fun h => hcross.2.2.2 (congrArg Subtype.val h)
  by_cases hac : a = c
  · subst c
    have hbd : b ≠ d := by
      intro h
      apply hab
      apply Subtype.ext
      have hv := congrArg Subtype.val h
      omega
    simp [hab, Ne.symm hab, had, hbd]
  · by_cases hbd : b = d
    · subst d
      simp [hab, hac, hcb, Ne.symm hcb]
    · simp [hab, hac, had, hbd, hcb, Ne.symm hcb, hcd]

def squaresBelow (N : ℕ) : Finset ℕ := (Icc 1 N).image (fun n => n ^ 2)

def squareAPSupport (t : (ℕ × ℕ) × ℕ) : Finset ℕ := {t.1.1 ^ 2, t.1.2 ^ 2, t.2 ^ 2}

def squareCollisionSupport (t : (ℕ × ℕ) × (ℕ × ℕ)) : Finset ℕ :=
  {t.1.1 ^ 2, t.1.2 ^ 2, t.2.1 ^ 2, t.2.2 ^ 2}

lemma support_of_squareAP_mem {N a b c : ℕ}
    (ha : a ∈ Icc 1 N) (hb : b ∈ Icc 1 N) (hc : c ∈ Icc 1 N)
    (he : a ^ 2 + c ^ 2 = 2 * b ^ 2) (hne : a ≠ c) :
    {a ^ 2, b ^ 2, c ^ 2} ∈ (squareAPs N).image squareAPSupport := by
  rcases lt_or_gt_of_ne hne with hac | hca
  · have hab : a < b := by nlinarith
    have hbc : b < c := by nlinarith
    apply Finset.mem_image.mpr
    refine ⟨((a, b), c), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hc⟩, hab, hbc, he⟩
  · have hcb : c < b := by nlinarith
    have hba : b < a := by nlinarith
    apply Finset.mem_image.mpr
    refine ⟨((c, b), a), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hc, hb⟩, ha⟩, hcb, hba, by simpa [add_comm] using he⟩
    · ext x
      simp [squareAPSupport, or_comm, or_left_comm, or_assoc]

lemma square_obstructions_four_bound (N : ℕ) :
    ((sidonObstructions (squaresBelow N)).filter (fun e => e.card = 4)).card ≤
      (squareCollisions N).card := by
  classical
  apply le_trans _ (Finset.card_image_le (f := squareCollisionSupport) (s := squareCollisions N))
  apply Finset.card_le_card_of_injOn (fun e : Finset (squaresBelow N) => e.image Subtype.val)
  · intro e he
    change e ∈ (sidonObstructions (squaresBelow N)).filter (fun e => e.card = 4) at he
    obtain ⟨he, _⟩ := Finset.mem_filter.mp he
    obtain ⟨_, a, b, c, d, rfl, he, hn⟩ := Finset.mem_filter.mp he
    have hn' : ¬ ((a.val = b.val ∧ c.val = d.val) ∨ (a.val = d.val ∧ c.val = b.val)) := by
      simpa only [Subtype.ext_iff] using hn
    have hab := (nontrivial_sum_cross_ne he hn').1
    obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp a.property
    obtain ⟨y, hy, hyb⟩ := Finset.mem_image.mp b.property
    obtain ⟨z, hz, hzc⟩ := Finset.mem_image.mp c.property
    obtain ⟨w, hw, hwd⟩ := Finset.mem_image.mp d.property
    have hxy : x ≠ y := by intro h; apply hab; rw [← hxa, ← hyb, h]
    have heq : x ^ 2 + z ^ 2 = y ^ 2 + w ^ 2 := by simpa [hxa, hyb, hzc, hwd] using he
    rcases lt_or_gt_of_ne hxy with hxy | hyx
    · apply Finset.mem_image.mpr
      refine ⟨((y, x), (w, z)), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨hy, hx⟩, Finset.mem_product.mpr ⟨hw, hz⟩⟩,
          hxy, heq.symm⟩
      · ext v
        simp [squareCollisionSupport, hxa, hyb, hzc, hwd, or_comm, or_left_comm, or_assoc]
    · apply Finset.mem_image.mpr
      refine ⟨((x, y), (z, w)), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨hx, hy⟩, Finset.mem_product.mpr ⟨hz, hw⟩⟩,
          hyx, heq⟩
      · simp [squareCollisionSupport, hxa, hyb, hzc, hwd]
  · exact (Finset.image_injective Subtype.val_injective).injOn

lemma square_obstructions_three_bound (N : ℕ) :
    ((sidonObstructions (squaresBelow N)).filter (fun e => e.card = 3)).card ≤
      (squareAPs N).card := by
  classical
  apply le_trans _ (Finset.card_image_le (f := squareAPSupport) (s := squareAPs N))
  apply Finset.card_le_card_of_injOn (fun e : Finset (squaresBelow N) => e.image Subtype.val)
  · intro e he
    change e ∈ (sidonObstructions (squaresBelow N)).filter (fun e => e.card = 3) at he
    obtain ⟨he, hecard⟩ := Finset.mem_filter.mp he
    obtain ⟨_, a, b, c, d, rfl, he, hn⟩ := Finset.mem_filter.mp he
    have hn' : ¬ ((a.val = b.val ∧ c.val = d.val) ∨ (a.val = d.val ∧ c.val = b.val)) := by
      simpa only [Subtype.ext_iff] using hn
    have hcross := nontrivial_sum_cross_ne he hn'
    have hab : a ≠ b := fun h => hcross.1 (congrArg Subtype.val h)
    have had : a ≠ d := fun h => hcross.2.1 (congrArg Subtype.val h)
    have hcb : c ≠ b := fun h => hcross.2.2.1 (congrArg Subtype.val h)
    have hcd : c ≠ d := fun h => hcross.2.2.2 (congrArg Subtype.val h)
    have hsame : a = c ∨ b = d := by
      by_cases hac : a = c
      · exact Or.inl hac
      by_cases hbd : b = d
      · exact Or.inr hbd
      have hfour : ({a, b, c, d} : Finset (squaresBelow N)).card = 4 := by
        simp [hab, hac, had, hbd, Ne.symm hcb, hcd]
      omega
    rcases hsame with hsame | hsame
    · subst c
      have hbd : b ≠ d := by
        intro h
        apply hab
        apply Subtype.ext
        have hv := congrArg Subtype.val h
        omega
      obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp a.property
      obtain ⟨y, hy, hyb⟩ := Finset.mem_image.mp b.property
      obtain ⟨w, hw, hwd⟩ := Finset.mem_image.mp d.property
      have hyw : y ≠ w := by
        intro h
        apply hbd
        apply Subtype.ext
        rw [← hyb, ← hwd, h]
      have heq : y ^ 2 + w ^ 2 = 2 * x ^ 2 := by rw [hyb, hwd, hxa]; omega
      have hAP := support_of_squareAP_mem hy hx hw heq hyw
      rw [hyb, hxa, hwd] at hAP
      convert hAP using 1 <;> ext v <;> simp [or_comm, or_left_comm, or_assoc]
    · subst d
      have hac : a ≠ c := by
        intro h
        apply hab
        apply Subtype.ext
        have hv := congrArg Subtype.val h
        omega
      obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp a.property
      obtain ⟨y, hy, hyb⟩ := Finset.mem_image.mp b.property
      obtain ⟨z, hz, hzc⟩ := Finset.mem_image.mp c.property
      have hxz : x ≠ z := by
        intro h
        apply hac
        apply Subtype.ext
        rw [← hxa, ← hzc, h]
      have heq : x ^ 2 + z ^ 2 = 2 * y ^ 2 := by rw [hxa, hzc, hyb]; omega
      have hAP := support_of_squareAP_mem hx hy hz heq hxz
      rw [hxa, hyb, hzc] at hAP
      convert hAP using 1 <;> ext v <;> simp [or_comm, or_left_comm, or_assoc]
  · exact (Finset.image_injective Subtype.val_injective).injOn

lemma obstruction_weight_sum (A : Finset ℕ) (p : ℝ) :
    (∑ e ∈ sidonObstructions A, p ^ e.card) =
      p ^ 3 * ((sidonObstructions A).filter (fun e => e.card = 3)).card +
      p ^ 4 * ((sidonObstructions A).filter (fun e => e.card = 4)).card := by
  classical
  calc
    _ = ∑ e ∈ sidonObstructions A,
        ((if e.card = 3 then p ^ 3 else 0) + (if e.card = 4 then p ^ 4 else 0)) := by
      apply Finset.sum_congr rfl
      intro e he
      rcases sidonObstructions_card_either A e he with h | h <;> simp [h]
    _ = _ := by simp [Finset.sum_add_distrib, ← Finset.sum_filter, mul_comm]

lemma squaresBelow_card (N : ℕ) : (squaresBelow N).card = N := by
  unfold squaresBelow
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b hab
    nlinarith

lemma square_sidon_alteration (N : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p * N - p ^ 3 * (squareAPs N).card - p ^ 4 * (squareCollisions N).card ≤
      (Finset.maxSidonSubsetCard (squaresBelow N) : ℝ) := by
  have hm := sidon_alteration_bound (squaresBelow N) p hp hp1
  rw [squaresBelow_card, obstruction_weight_sum] at hm
  have h3 : (((sidonObstructions (squaresBelow N)).filter (fun e => e.card = 3)).card : ℝ) ≤
      (squareAPs N).card := by exact_mod_cast square_obstructions_three_bound N
  have h4 : (((sidonObstructions (squaresBelow N)).filter (fun e => e.card = 4)).card : ℝ) ≤
      (squareCollisions N).card := by exact_mod_cast square_obstructions_four_bound N
  have h3' := mul_le_mul_of_nonneg_left h3 (pow_nonneg hp 3)
  have h4' := mul_le_mul_of_nonneg_left h4 (pow_nonneg hp 4)
  linarith

lemma square_sidon_subpower_alteration (δ : ℝ) (hδ : 0 < δ) :
    ∃ C₃ > (0 : ℝ), ∃ C₄ > (0 : ℝ), ∀ (N : ℕ) (p : ℝ), 0 ≤ p → p ≤ 1 →
      p * N - (C₃ * (N : ℝ) ^ (1 + 2 * δ)) * p ^ 3 -
        (C₄ * (N : ℝ) ^ (2 + 2 * δ)) * p ^ 4 ≤
          (Finset.maxSidonSubsetCard (squaresBelow N) : ℝ) := by
  obtain ⟨C₃, hC₃, h3⟩ := squareAPs_subpower δ hδ
  obtain ⟨C₄, hC₄, h4⟩ := squareCollisions_subpower δ hδ
  refine ⟨C₃, hC₃, C₄, hC₄, ?_⟩
  intro N p hp hp1
  have hm := square_sidon_alteration N p hp hp1
  have h3' := mul_le_mul_of_nonneg_left (h3 N) (pow_nonneg hp 3)
  have h4' := mul_le_mul_of_nonneg_left (h4 N) (pow_nonneg hp 4)
  nlinarith only [hm, h3', h4']

lemma square_sidon_two_thirds (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (2 / 3 - 2 * η) ≤
      (Finset.maxSidonSubsetCard (squaresBelow N) : ℝ) := by
  obtain ⟨C₃, hC₃, C₄, hC₄, hbound⟩ :=
    square_sidon_subpower_alteration (η / 2) (by positivity)
  have ht (C r : ℝ) (hr : 0 < r) :
      Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-r)) atTop (nhds 0) := by
    simpa using ((tendsto_rpow_neg_atTop hr).comp tendsto_natCast_atTop_atTop).const_mul C
  have h3 := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4)
    (ht C₃ (2 / 3 + η) (by linarith))
  have h4 := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4)
    (ht C₄ (2 * η) (by positivity))
  have h0 := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2) (ht 1 η hη)
  filter_upwards [h3, h4, h0, eventually_ge_atTop 1] with N h3 h4 h0 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  let p : ℝ := (N : ℝ) ^ (-(1 / 3 + η))
  let S : ℝ := (N : ℝ) ^ (2 / 3 - η)
  have hp : 0 ≤ p := Real.rpow_nonneg hNpos.le _
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hS : 0 ≤ S := Real.rpow_nonneg hNpos.le _
  have hmain := hbound N p hp hp1
  have hδ1 : (1 : ℝ) + 2 * (η / 2) = 1 + η := by ring
  have hδ2 : (2 : ℝ) + 2 * (η / 2) = 2 + η := by ring
  rw [hδ1, hδ2] at hmain
  have hPN : p * N = S := by
    dsimp [p, S]
    calc
      _ = (N : ℝ) ^ (-(1 / 3 + η)) * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ (2 / 3 - η) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
  have hm (C r s : ℝ) (k : ℕ) :
      (C * (N : ℝ) ^ r) * ((N : ℝ) ^ s) ^ k = C * (N : ℝ) ^ (r + s * k) := by
    rw [mul_assoc, ← Real.rpow_mul_natCast hNpos.le, ← Real.rpow_add hNpos]
  have he3 : (C₃ * (N : ℝ) ^ (1 + η)) * p ^ 3 =
      S * (C₃ * (N : ℝ) ^ (-(2 / 3 + η))) := by
    dsimp [p, S]
    rw [hm, mul_left_comm _ C₃, ← Real.rpow_add hNpos]
    congr 2
    norm_num
    ring
  have he4 : (C₄ * (N : ℝ) ^ (2 + η)) * p ^ 4 =
      S * (C₄ * (N : ℝ) ^ (-(2 * η))) := by
    dsimp [p, S]
    rw [hm, mul_left_comm _ C₄, ← Real.rpow_add hNpos]
    congr 2
    norm_num
    ring
  have he0 : (N : ℝ) ^ (2 / 3 - 2 * η) = S * (N : ℝ) ^ (-η) := by
    dsimp [S]
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have h3' := mul_le_mul_of_nonneg_left h3 hS
  have h4' := mul_le_mul_of_nonneg_left h4 hS
  have h0' := mul_le_mul_of_nonneg_left h0 hS
  rw [hPN, he3, he4] at hmain
  rw [he0]
  nlinarith only [hmain, h3', h4', h0']

lemma conjecture_for_epsilon_gt_third (ε : ℝ) (hε : 1 / 3 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - ε) ≤
        (Finset.maxSidonSubsetCard
          (Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc 1 N)) : ℝ) := by
  have h := square_sidon_two_thirds ((ε - 1 / 3) / 2) (by linarith)
  have he : (2 : ℝ) / 3 - 2 * ((ε - 1 / 3) / 2) = 1 - ε := by ring
  simpa only [he, squaresBelow] using h

#print axioms conjecture_for_epsilon_gt_third

end Erdos773
