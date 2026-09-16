import FormalConjectures.Util.ProblemImports
import Submission.Spec

open List Nat Finset Classical WithBot

lemma option_rec_gt_7 {opt : Option ℕ} (h : Option.rec 0 id opt > 7) : ∃ m, opt = Option.some m ∧ m > 7 := by
  cases opt with
  | none => revert h; decide
  | some m => exact ⟨m, rfl, h⟩

lemma filter_prop {α} {s : Finset α} {p : α → Prop} {dec : DecidablePred p} {a : α} (h : a ∈ @Finset.filter α p dec s) : p a :=
  (@Finset.mem_filter α p dec s a).mp h |>.2

def valid_squares (n : ℕ) : Bool :=
  let bnds := 0 :: List.range' 8 20
  bnds.any fun x =>
    bnds.any fun y =>
      bnds.any fun z =>
        bnds.any fun w =>
          x^2 + y^2 + z^2 + w^2 == n

set_option maxHeartbeats 2000000

lemma no_sum : valid_squares 736 = false := by decide

lemma valid_squares_true (x y z w : ℕ) (hx : x ∈ 0 :: List.range' 8 20) (hy : y ∈ 0 :: List.range' 8 20) 
  (hz : z ∈ 0 :: List.range' 8 20) (hw : w ∈ 0 :: List.range' 8 20) (hsum : x^2 + y^2 + z^2 + w^2 = 736) : 
  valid_squares 736 = true := by
  unfold valid_squares
  rw [List.any_eq_true]
  refine ⟨x, hx, ?_⟩
  rw [List.any_eq_true]
  refine ⟨y, hy, ?_⟩
  rw [List.any_eq_true]
  refine ⟨z, hz, ?_⟩
  rw [List.any_eq_true]
  refine ⟨w, hw, ?_⟩
  simp [hsum]

lemma mem_bnds_0 : 0 ∈ 0 :: List.range' 8 20 := by exact List.Mem.head _

lemma mem_bnds {v m : ℕ} (h1 : m > 7) (h2 : m ≤ v) (h3 : v^2 ≤ 736) : v ∈ 0 :: List.range' 8 20 := by
  have hv1 : v ≥ 8 := by omega
  have hv2 : v ≤ 27 := by
    by_contra h
    push_neg at h
    have : v^2 ≥ 28^2 := by nlinarith
    have : v^2 ≥ 784 := by nlinarith
    omega
  revert hv1 hv2
  intro hv1 hv2
  revert v; exact by decide

set_option linter.unusedVariables false

lemma sorted_1 {x m : ℕ} (h1 : ([x]).head? = Option.some m) (h2 : List.Pairwise (· ≤ ·) [x]) : m = x := by
  simp at h1
  exact h1.symm

lemma sorted_2 {x y m : ℕ} (h1 : ([x, y]).head? = Option.some m) (h2 : List.Pairwise (· ≤ ·) [x, y]) : m = x ∧ x ≤ y := by
  simp at h1 h2
  exact ⟨h1.symm, h2⟩

lemma sorted_3 {x y z m : ℕ} (h1 : ([x, y, z]).head? = Option.some m) (h2 : List.Pairwise (· ≤ ·) [x, y, z]) : m = x ∧ x ≤ y ∧ y ≤ z := by
  simp at h1 h2
  omega

lemma sorted_4 {x y z w m : ℕ} (h1 : ([x, y, z, w]).head? = Option.some m) (h2 : List.Pairwise (· ≤ ·) [x, y, z, w]) : m = x ∧ x ≤ y ∧ y ≤ z ∧ z ≤ w := by
  simp at h1 h2
  omega

theorem oeis_disproof : ¬ (type_of% @oeis_241898_conjecture_0) := by
  intro h_conj
  have h := h_conj 736 (by decide)
  unfold a at h
  dsimp only at h
  have ⟨m, hmax, hm7⟩ := option_rec_gt_7 h
  have hm := Finset.mem_of_max hmax
  have hm2 := filter_prop hm
  rcases hm2 with ⟨hm_pos, s, hs_len_pos, hs_len_le, hs_sum, hs_sorted, hs_head⟩
  
  have h_false : valid_squares 736 = true := by
    rcases s with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, _ | ⟨e, s⟩⟩⟩⟩⟩
    · cases hs_len_pos
    · have h_m := sorted_1 hs_head hs_sorted
      have hx_le : x^2 ≤ 736 := by simp at hs_sum; omega
      have hx_bnd := mem_bnds hm7 (by omega) hx_le
      have hsum_eq : x^2 + 0^2 + 0^2 + 0^2 = 736 := by simp at hs_sum; omega
      exact valid_squares_true x 0 0 0 hx_bnd mem_bnds_0 mem_bnds_0 mem_bnds_0 hsum_eq
    · have ⟨h_m, h_xy⟩ := sorted_2 hs_head hs_sorted
      have hx_le : x^2 ≤ 736 := by simp at hs_sum; omega
      have hy_le : y^2 ≤ 736 := by simp at hs_sum; omega
      have hx_bnd := mem_bnds hm7 (by omega) hx_le
      have hy_bnd := mem_bnds hm7 (by omega) hy_le
      have hsum_eq : x^2 + y^2 + 0^2 + 0^2 = 736 := by simp at hs_sum; omega
      exact valid_squares_true x y 0 0 hx_bnd hy_bnd mem_bnds_0 mem_bnds_0 hsum_eq
    · have ⟨h_m, h_xy, h_yz⟩ := sorted_3 hs_head hs_sorted
      have hx_le : x^2 ≤ 736 := by simp at hs_sum; omega
      have hy_le : y^2 ≤ 736 := by simp at hs_sum; omega
      have hz_le : z^2 ≤ 736 := by simp at hs_sum; omega
      have hx_bnd := mem_bnds hm7 (by omega) hx_le
      have hy_bnd := mem_bnds hm7 (by omega) hy_le
      have hz_bnd := mem_bnds hm7 (by omega) hz_le
      have hsum_eq : x^2 + y^2 + z^2 + 0^2 = 736 := by simp at hs_sum; omega
      exact valid_squares_true x y z 0 hx_bnd hy_bnd hz_bnd mem_bnds_0 hsum_eq
    · have ⟨h_m, h_xy, h_yz, h_zw⟩ := sorted_4 hs_head hs_sorted
      have hx_le : x^2 ≤ 736 := by simp at hs_sum; omega
      have hy_le : y^2 ≤ 736 := by simp at hs_sum; omega
      have hz_le : z^2 ≤ 736 := by simp at hs_sum; omega
      have hw_le : w^2 ≤ 736 := by simp at hs_sum; omega
      have hx_bnd := mem_bnds hm7 (by omega) hx_le
      have hy_bnd := mem_bnds hm7 (by omega) hy_le
      have hz_bnd := mem_bnds hm7 (by omega) hz_le
      have hw_bnd := mem_bnds hm7 (by omega) hw_le
      have hsum_eq : x^2 + y^2 + z^2 + w^2 = 736 := by simp at hs_sum; omega
      exact valid_squares_true x y z w hx_bnd hy_bnd hz_bnd hw_bnd hsum_eq
    · revert hs_len_le; simp; intro; omega
  rw [no_sum] at h_false
  contradiction
