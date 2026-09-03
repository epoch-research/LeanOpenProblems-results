import FormalConjecturesUtil

/-! Centered complex correlation yields a density increment on a sufficiently
large cell of any finite partition that approximates the correlating test. -/
namespace Erdos3FinitePartitionIncrement
open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

variable {I : Type*} [Fintype I] [Nonempty I]

/-- A centered signed distribution with substantial L¹ mass has a positive cell
with both nonnegligible mass and a nonnegligible relative density increase. -/
lemma positive_cell_of_L1 (m u : I → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hms : ∑ i, m i = 1) (hu : ∀ i, |u i| ≤ m i) (hus : ∑ i, u i = 0)
    {s : ℝ} (hs : 0 < s) (hL : s ≤ ∑ i, |u i|) :
    ∃ i : I, s/(8*(Fintype.card I : ℝ)) ≤ m i ∧ (s/8)*m i ≤ u i := by
  have hN : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hc : 0 < s/(8*(Fintype.card I : ℝ)) := by positivity
  by_contra! hn
  have hbound (i : I) : u i ≤ (s/8)*m i+s/(8*(Fintype.card I : ℝ)) := by
    by_cases hi : s/(8*(Fintype.card I : ℝ)) ≤ m i
    · have hh := hn i hi
      linarith
    · have hh : u i ≤ m i := (le_abs_self _).trans (hu i)
      have hh' : 0 ≤ (s/8)*m i := mul_nonneg (by positivity) (hm i)
      linarith
  have habs (i : I) : |u i| ≤ 2*((s/8)*m i+s/(8*(Fintype.card I : ℝ)))-u i := by
    apply abs_le.mpr
    constructor
    · have hh : 0 ≤ (s/8)*m i := mul_nonneg (by positivity) (hm i)
      linarith
    · linarith [hbound i]
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) ↦ habs i)
  have he : (∑ i : I, (2*((s/8)*m i+s/(8*(Fintype.card I : ℝ)))-u i)) = s/2 := by
    rw [sum_sub_distrib,← mul_sum,sum_add_distrib,← mul_sum,hms,hus]
    simp only [sum_const,card_univ,nsmul_eq_mul]
    field_simp
    ring
  rw [he] at hsum
  linarith

variable {V : Type*} [Fintype V] [Nonempty V]

noncomputable def cellMass (c : V → I) (i : I) : ℝ := 𝔼 x, if c x = i then 1 else 0
noncomputable def cellCharge (c : V → I) (f : V → ℝ) (i : I) : ℝ :=
  𝔼 x, if c x = i then f x else 0
noncomputable def cell (c : V → I) (i : I) : Finset V := univ.filter (fun x ↦ c x = i)

lemma cellMass_nonneg (c : V → I) (i : I) : 0 ≤ cellMass c i := by
  apply expect_nonneg
  intro x _
  split_ifs <;> norm_num

lemma sum_cellMass (c : V → I) : ∑ i, cellMass c i = 1 := by
  unfold cellMass
  rw [← expect_sum_comm]
  simp

lemma sum_cellCharge (c : V → I) (f : V → ℝ) : ∑ i, cellCharge c f i = 𝔼 x, f x := by
  unfold cellCharge
  rw [← expect_sum_comm]
  simp

lemma abs_cellCharge_le (c : V → I) (f : V → ℝ) (hf : ∀ x, |f x| ≤ 1) (i : I) :
    |cellCharge c f i| ≤ cellMass c i := by
  rw [← Real.norm_eq_abs]
  apply (RCLike.norm_expect_le (K := ℝ)).trans
  apply expect_le_expect
  intro x _
  split_ifs <;> simp_all only [Real.norm_eq_abs,norm_zero,le_refl]

lemma cellCharge_pairing (c : V → I) (f : V → ℝ) (w : I → ℂ) :
    (𝔼 x, (f x : ℂ)*w (c x)) = ∑ i, (cellCharge c f i : ℂ)*w i := by
  simp only [cellCharge,Complex.ofReal_expect,expect_mul]
  rw [← expect_sum_comm]
  apply expect_congr rfl
  intro x _
  simp only [apply_ite,Complex.ofReal_zero,ite_mul,zero_mul]
  simp

/-- Correlation with an approximable bounded test gives a quantitatively large
positive cell. Centering is essential: correlation alone can detect a deficit. -/
theorem correlation_cell_increment (c : V → I) (f : V → ℝ) (v : V → ℂ) (w : I → ℂ)
    (hf : ∀ x, |f x| ≤ 1) (hf0 : 𝔼 x, f x = 0)
    (hv : ∀ x, ‖v x‖ ≤ 1) (hw : ∀ i, ‖w i‖ ≤ 1)
    {r ε : ℝ} (hr : 0 < r) (hε : ε ≤ r/2)
    (happrox : ∀ x, ‖v x-w (c x)‖ ≤ ε)
    (hcorr : r ≤ ‖𝔼 x, (f x : ℂ)*v x‖^2) :
    ∃ i : I, r/(16*(Fintype.card I : ℝ)) ≤ cellMass c i ∧
      (r/16)*cellMass c i ≤ cellCharge c f i := by
  have hnorm : ‖𝔼 x, (f x : ℂ)*v x‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply expect_le univ_nonempty
    intro x _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul (hf x) (hv x) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have herr : ‖(𝔼 x, (f x : ℂ)*v x)-(𝔼 x, (f x : ℂ)*w (c x))‖ ≤ ε := by
    rw [← expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply expect_le univ_nonempty
    intro x _
    rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact ((mul_le_mul_of_nonneg_right (hf x) (norm_nonneg _)).trans_eq (one_mul _)).trans (happrox x)
  have hp : ‖𝔼 x, (f x : ℂ)*w (c x)‖ ≤ ∑ i, |cellCharge c f i| := by
    rw [cellCharge_pairing]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro i _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _)).trans_eq (mul_one _)
  have hc : ‖𝔼 x, (f x : ℂ)*v x‖ ≤ ε+∑ i, |cellCharge c f i| := by
    calc
      _ ≤ ‖(𝔼 x, (f x : ℂ)*v x)-(𝔼 x, (f x : ℂ)*w (c x))‖+
          ‖𝔼 x, (f x : ℂ)*w (c x)‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := add_le_add herr hp
  have hL : r/2 ≤ ∑ i, |cellCharge c f i| := by
    have hn := norm_nonneg (𝔼 x, (f x : ℂ)*v x)
    nlinarith
  obtain ⟨i,hi,hinc⟩ := positive_cell_of_L1 (cellMass c) (cellCharge c f)
    (cellMass_nonneg c) (sum_cellMass c) (abs_cellCharge_le c f hf)
    ((sum_cellCharge c f).trans hf0) (by positivity : 0 < r/2) hL
  exact ⟨i,by convert hi using 1 <;> ring,by convert hinc using 1 <;> ring⟩

#print axioms correlation_cell_increment
end Erdos3FinitePartitionIncrement
