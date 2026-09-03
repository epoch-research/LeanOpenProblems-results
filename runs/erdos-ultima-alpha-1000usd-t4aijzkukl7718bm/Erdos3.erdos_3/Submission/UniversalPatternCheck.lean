import Submission.Reduction
import Submission.CubeCase
import Submission.ApproximateAPCase

/-! A summable k-AP-free set can contain affine copies of every finite k-AP-free pattern.
This tests the limitations of local-pattern reductions; it is not a disproof of Erdős 3. -/

namespace Erdos3UniversalPatternCheck

open Erdos3Reduction

set_option maxHeartbeats 1000000

lemma free_empty {k : ℕ} (hk : 3 ≤ k) : (∅ : Set ℕ).IsAPOfLengthFree k := by
  rw [free_iff_not_hasNatAP (by omega : 2 ≤ k)]
  rintro ⟨a, d, hd, hmem⟩
  simpa using hmem 0 (by omega)

lemma finite_extension {k : ℕ} (hk : 3 ≤ k) (U S : Finset ℕ)
    (hU : (U : Set ℕ).IsAPOfLengthFree k) (hS : (S : Set ℕ).IsAPOfLengthFree k)
    (n : ℕ) :
    ∃ T : Finset ℕ, ∃ q r : ℕ, 0 < q ∧ U ⊆ T ∧
      (∀ x ∈ S, q * x + r ∈ T) ∧ (T : Set ℕ).IsAPOfLengthFree k ∧
      recipWeight T ≤ recipWeight U + (1 / 2 : ℝ) ^ n := by
  classical
  let L := U.sup id
  let r := 2 * L + 1 + 2 ^ n * S.card
  let q := 2 * r + 1
  have hr : 0 < r := by dsimp [r]; omega
  have hq : 0 < q := by dsimp [q]; omega
  let V := S.map (affineEmbedding q r hq)
  have hUL : ∀ x ∈ U, x ≤ L := fun x hx ↦ Finset.le_sup (f := id) hx
  have hVr : ∀ x ∈ V, r ≤ x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    change r ≤ q * y + r
    omega
  have hVmod : ∀ x ∈ V, Nat.ModEq q x r := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    change (q * y + r) % q = r % q
    exact Nat.mul_add_mod_self_left _ _ _
  have hVfree : (V : Set ℕ).IsAPOfLengthFree k := by
    rw [show (V : Set ℕ) = (fun x : ℕ ↦ q * x + r) '' (S : Set ℕ) by
      simp only [V, Finset.coe_map, affineEmbedding, Function.Embedding.coeFn_mk]]
    exact free_affine_image (by omega) hq hS
  have hdis : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro x hxU hxV
    have := hUL x hxU
    have := hVr x hxV
    dsimp [r] at *
    omega
  have hfree : ((U ∪ V : Finset ℕ) : Set ℕ).IsAPOfLengthFree k := by
    rw [Finset.coe_union]
    apply free_union_separated hk hUL _ hVmod _ _ hU hVfree
    · intro x hx
      have := hVr x hx
      dsimp [r] at this
      omega
    · dsimp [r]; omega
    · dsimp [q]; omega
  have hweight : recipWeight V ≤ (1 / 2 : ℝ) ^ n := by
    have hrr : (0 : ℝ) < r := by exact_mod_cast hr
    calc
      recipWeight V = ∑ x ∈ S, 1 / ((q * x + r : ℕ) : ℝ) := by
        simp [V, recipWeight, affineEmbedding]
      _ ≤ ∑ _x ∈ S, 1 / (r : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        apply one_div_le_one_div_of_le hrr
        exact_mod_cast (show r ≤ q * x + r by omega)
      _ = (S.card : ℝ) / r := by simp [div_eq_mul_inv]
      _ ≤ (1 / 2 : ℝ) ^ n := by
        rw [div_pow, one_pow]
        apply (div_le_div_iff₀ hrr (by positivity)).mpr
        have hnat : S.card * 2 ^ n ≤ r := by dsimp [r]; nlinarith
        simpa only [one_mul] using (show (S.card : ℝ) * (2 : ℝ) ^ n ≤ (r : ℝ) by
          exact_mod_cast hnat)
  refine ⟨U ∪ V, q, r, hq, Finset.subset_union_left, ?_, hfree, ?_⟩
  · intro x hx
    apply Finset.mem_union_right
    exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
  · have heq : recipWeight (U ∪ V) = recipWeight U + recipWeight V :=
      Finset.sum_union hdis
    rw [heq]
    exact add_le_add le_rfl hweight

lemma finite_subset_chain {f : ℕ → Finset ℕ} (hf : Monotone f) {S : Finset ℕ}
    (hS : ∀ x ∈ S, ∃ n : ℕ, x ∈ f n) : ∃ n, S ⊆ f n := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | @insert a S ha ih =>
    obtain ⟨i, hi⟩ := hS a (Finset.mem_insert_self _ _)
    obtain ⟨j, hj⟩ := ih (fun x hx ↦ hS x (Finset.mem_insert_of_mem hx))
    refine ⟨i + j, Finset.insert_subset_iff.mpr ⟨?_, ?_⟩⟩
    · exact hf (by omega : i ≤ i + j) hi
    · exact hj.trans (hf (by omega : j ≤ i + j))

/-- A summable AP-free set can be universal for all finite AP-free affine patterns. -/
theorem summable_universal_free_set (k : ℕ) (hk : 3 ≤ k) :
    ∃ A : Set ℕ, A.IsAPOfLengthFree k ∧
      Summable (fun a : A ↦ 1 / (a : ℝ)) ∧
      (∑' a : A, 1 / (a : ℝ)) ≤ 2 ∧
      ∀ S : Finset ℕ, (S : Set ℕ).IsAPOfLengthFree k →
        ∃ q r : ℕ, 0 < q ∧ ∀ x ∈ S, q * x + r ∈ A := by
  classical
  let B := {S : Finset ℕ // (S : Set ℕ).IsAPOfLengthFree k}
  have hempty : (∅ : Set ℕ).IsAPOfLengthFree k := free_empty hk
  letI : Nonempty B := ⟨⟨∅, by simpa using hempty⟩⟩
  obtain ⟨pattern, hpattern⟩ := exists_surjective_nat B
  have hext : ∀ U : B, ∀ n : ℕ, ∃ T : B, ∃ q r : ℕ,
      0 < q ∧ U.val ⊆ T.val ∧
      (∀ x ∈ (pattern n).val, q * x + r ∈ T.val) ∧
      recipWeight T.val ≤ recipWeight U.val + (1 / 2 : ℝ) ^ n := by
    intro U n
    obtain ⟨T, q, r, hq, hUT, hcopy, hT, hweight⟩ :=
      finite_extension hk U.val (pattern n).val U.property (pattern n).property n
    exact ⟨⟨T, hT⟩, q, r, hq, hUT, hcopy, hweight⟩
  choose next q r hq hinc hcopy hweight using hext
  let chain : ℕ → B := Nat.rec ⟨∅, by simpa using hempty⟩ (fun n U ↦ next U n)
  have hmono : Monotone (fun n ↦ (chain n).val) :=
    monotone_nat_of_le_succ (fun n ↦ hinc (chain n) n)
  have hbound : ∀ n, recipWeight (chain n).val ≤ ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := by
    intro n
    induction n with
    | zero => simp [chain, recipWeight]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      exact (hweight (chain n) n).trans (add_le_add ih le_rfl)
  have hgeo : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hbound_two (n : ℕ) : recipWeight (chain n).val ≤ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := hbound n
      _ ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ i :=
        Summable.sum_le_tsum _ (fun i _ ↦ by positivity) hgeo
      _ = 2 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  let A : Set ℕ := {x | ∃ n, x ∈ (chain n).val}
  have hAfree : A.IsAPOfLengthFree k := by
    rw [free_iff_not_hasNatAP (by omega : 2 ≤ k)]
    rintro ⟨a, d, hd, hmem⟩
    have hstages : ∀ i : Fin k, ∃ n : ℕ, a + i.val * d ∈ (chain n).val :=
      fun i ↦ hmem i.val i.isLt
    choose stage hstage using hstages
    let N := Finset.univ.sup stage
    have hNmem : ∀ i < k, a + i * d ∈ (chain N).val := by
      intro i hi
      have hle : stage ⟨i, hi⟩ ≤ N := Finset.le_sup (Finset.mem_univ _)
      exact hmono hle (hstage ⟨i, hi⟩)
    exact (free_iff_not_hasNatAP (by omega : 2 ≤ k)).mp (chain N).property
      ⟨a, d, hd, hNmem⟩
  have hfinite : ∀ F : Finset A, (∑ a ∈ F, 1 / (a : ℝ)) ≤ 2 := by
    intro F
    let e : A ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
    have hsub : ∀ x ∈ F.map e, ∃ n, x ∈ (chain n).val := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
      exact a.property
    obtain ⟨n, hn⟩ := finite_subset_chain hmono hsub
    have hF := (recipWeight_mono hn).trans (hbound_two n)
    simpa only [recipWeight, Finset.sum_map, e, Function.Embedding.coeFn_mk] using hF
  have hsum : Summable (fun a : A ↦ 1 / (a : ℝ)) :=
    summable_of_sum_le (fun _ ↦ by positivity) hfinite
  refine ⟨A, hAfree, hsum, hsum.tsum_le_of_sum_le hfinite, ?_⟩
  intro S hS
  obtain ⟨n, hn⟩ := hpattern ⟨S, hS⟩
  refine ⟨q (chain n) n, r (chain n) n, hq (chain n) n, ?_⟩
  intro x hx
  refine ⟨n + 1, ?_⟩
  apply hcopy (chain n) n
  simpa only [hn] using hx

lemma threeAPFree_iff_free_three (A : Set ℕ) :
    ThreeAPFree A ↔ A.IsAPOfLengthFree (3 : ℕ) := by
  rw [Erdos3Reduction.free_iff_not_hasNatAP (by norm_num : 2 ≤ 3)]
  constructor
  · intro h
    rintro ⟨a, d, hd, hmem⟩
    have ha := hmem 0 (by norm_num)
    have hb := hmem 1 (by norm_num)
    have hc := hmem 2 (by norm_num)
    simp only [zero_mul, add_zero, one_mul] at ha hb
    have := h ha hb hc (by ring)
    omega
  · intro h a ha b hb c hc heq
    by_contra hne
    have hmake {x y z : ℕ} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
        (hxy : x < y) (he : x + z = y + y) : Erdos3Reduction.HasNatAP A 3 := by
      refine ⟨x, y - x, by omega, ?_⟩
      intro i hi
      interval_cases i
      · simpa using hx
      · have : x + 1 * (y - x) = y := by omega
        simpa only [this] using hy
      · have : x + 2 * (y - x) = z := by omega
        simpa only [this] using hz
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact h (hmake ha hb hc hlt heq)
    · exact h (hmake hc hb ha (by omega) (by omega))


lemma reflectedCube_affine {m : ℕ} {S : Finset ℕ}
    (h : Erdos3CubeCase.ReflectedCube m S) {q : ℕ} (hq : 0 < q) (r : ℕ) :
    Erdos3CubeCase.ReflectedCube m (S.image (fun x ↦ q * x + r)) := by
  classical
  induction h with
  | point a => simpa using Erdos3CubeCase.ReflectedCube.point (q * a + r)
  | @reflect m S h c hsep ih =>
    have hcsep : ∀ x ∈ S.image (fun x ↦ q * x + r), 2 * x < q * c + 2 * r := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have hmul := Nat.mul_lt_mul_of_pos_left (hsep y hy) hq
      nlinarith
    have hreflection := Erdos3CubeCase.ReflectedCube.reflect ih (q * c + 2 * r) hcsep
    convert hreflection using 1
    rw [Finset.image_union, Finset.image_image, Finset.image_image]
    congr 1
    apply Finset.image_congr
    intro x hx
    have hxc : x ≤ c := by have := hsep x hx; omega
    have heq : q * c = q * x + q * (c - x) := by
      rw [← Nat.mul_add, Nat.add_sub_of_le hxc]
    dsimp
    omega

/-- One summable 3-AP-free set simultaneously has every finite reflected-cube dimension
and approximate progressions of every length and every prescribed relative accuracy. -/
theorem cubes_and_approximate_progressions_do_not_force_threeAP :
    ∃ A : Set ℕ, ThreeAPFree A ∧
      Summable (fun a : A ↦ 1 / (a : ℝ)) ∧
      (∀ m : ℕ, Erdos3CubeCase.HasCube A m) ∧
      ∀ k M : ℕ, ∃ a d L : ℕ, 0 < L ∧ d = (M + 2) * L ∧
        ∃ f : Fin k → ℕ, StrictMono f ∧
          ∀ i : Fin k, f i ∈ A ∧
            a + i.val * d ≤ f i ∧ f i < a + i.val * d + L := by
  classical
  obtain ⟨A, hfree, hsum, _, huniv⟩ := summable_universal_free_set 3 (by norm_num)
  refine ⟨A, (threeAPFree_iff_free_three A).mpr hfree, hsum, ?_, ?_⟩
  · intro m
    have hS := (threeAPFree_iff_free_three _).mp (Erdos3CubeCase.sparseCube_free m)
    obtain ⟨q, r, hq, hcopy⟩ := huniv (Erdos3CubeCase.sparseCube m) hS
    refine ⟨(Erdos3CubeCase.sparseCube m).image (fun x ↦ q * x + r), ?_,
      reflectedCube_affine (Erdos3CubeCase.sparseCube_cube m) hq r⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hcopy y hy
  · intro k M
    obtain ⟨D, L, hL, hD, f, hfmono, hffree, hf⟩ :=
      Erdos3ApproximateAPCase.threeAPFree_arbitrarily_accurate_finite_progressions k M
    let S : Finset ℕ := Finset.univ.image f
    have hScoe : (S : Set ℕ) = Set.range f := by
      simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    have hSfree : (S : Set ℕ).IsAPOfLengthFree (3 : ℕ) := by
      rw [hScoe]
      exact (threeAPFree_iff_free_three _).mp hffree
    obtain ⟨q, r, hq, hcopy⟩ := huniv S hSfree
    let g : Fin k → ℕ := fun i ↦ q * f i + r
    refine ⟨r, q * D, q * L, by positivity, ?_, g, ?_, ?_⟩
    · rw [hD]
      ring
    · intro i j hij
      exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left (hfmono hij) hq) r
    · intro i
      refine ⟨hcopy (f i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩), ?_, ?_⟩
      · have hmul := Nat.mul_le_mul_left q (hf i).1
        dsimp [g]
        nlinarith
      · have hmul := Nat.mul_lt_mul_of_pos_left (hf i).2 hq
        dsimp [g]
        nlinarith

#print axioms summable_universal_free_set
#print axioms cubes_and_approximate_progressions_do_not_force_threeAP

end Erdos3UniversalPatternCheck
