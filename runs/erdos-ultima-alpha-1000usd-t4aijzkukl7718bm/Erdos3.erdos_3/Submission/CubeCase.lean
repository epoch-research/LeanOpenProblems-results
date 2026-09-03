import FormalConjecturesUtil

/-! Proper reflected additive cubes forced by reciprocal divergence.
This is a partial result, not a settlement of Erdős Problem 3. -/

namespace Erdos3CubeCase

open scoped Classical
set_option maxHeartbeats 1000000

/-- Reflection across a center larger than every doubled point gives a new,
disjoint half of a proper additive cube. -/
inductive ReflectedCube : ℕ → Finset ℕ → Prop
  | point (a : ℕ) : ReflectedCube 0 {a}
  | reflect {d : ℕ} {S : Finset ℕ} (h : ReflectedCube d S)
      (c : ℕ) (hsep : ∀ x ∈ S, 2 * x < c) :
      ReflectedCube (d + 1) (S ∪ S.image (fun x ↦ c - x))

def HasCube (A : Set ℕ) (d : ℕ) : Prop :=
  ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ ReflectedCube d S

lemma reflectedCube_card {d : ℕ} {S : Finset ℕ} (h : ReflectedCube d S) :
    S.card = 2 ^ d := by
  induction h with
  | point a => simp
  | @reflect d S h c hsep ih =>
    have hdis : Disjoint S (S.image (fun x ↦ c - x)) := by
      apply Finset.disjoint_left.mpr
      intro x hx hi
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hi
      have := hsep y hy
      have := hsep (c - y) hx
      omega
    have hinj : Set.InjOn (fun x ↦ c - x) (S : Set ℕ) := by
      intro x hx y hy heq
      dsimp only at heq
      have := hsep x hx
      have := hsep y hy
      omega
    rw [Finset.card_union_of_disjoint hdis, Finset.card_image_iff.mpr hinj, ih,
      pow_succ]
    omega

lemma max_fiber {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (f : α → β) :
    ∃ b : β, Fintype.card α ≤ Fintype.card β *
      ((Finset.univ : Finset α).filter (fun x ↦ f x = b)).card := by
  obtain ⟨b, _, hb⟩ := Finset.exists_max_image (Finset.univ : Finset β)
    (fun b ↦ ((Finset.univ : Finset α).filter (fun x ↦ f x = b)).card)
    Finset.univ_nonempty
  refine ⟨b, ?_⟩
  calc
    Fintype.card α = ∑ b : β,
        ((Finset.univ : Finset α).filter (fun x ↦ f x = b)).card := by
      simpa using (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset β))
        (f := f) (by simp))
    _ ≤ ∑ _b : β,
        ((Finset.univ : Finset α).filter (fun x ↦ f x = b)).card :=
      Finset.sum_le_sum (fun b' hb' ↦ hb b' hb')
    _ = _ := by simp

lemma split_bound (S : Finset ℕ) (N : ℕ) (hN : ∀ n ∈ S, n ≤ N) :
    ∃ c : ℕ, ∃ B : Finset ℕ, B ⊆ S ∧
      (∀ x ∈ B, 2 * x < c ∧ c - x ∈ S) ∧
      S.card * (S.card - 1) ≤ 2 * (2 * N + 1) * B.card := by
  let e : S.offDiag → Fin (2 * N + 1) × Bool := fun p ↦
    (⟨p.1.1 + p.1.2, by
      have hp := Finset.mem_offDiag.mp p.2
      have := hN p.1.1 hp.1
      have := hN p.1.2 hp.2.1
      omega⟩, decide (p.1.1 ≤ p.1.2))
  obtain ⟨b, hb⟩ := max_fiber e
  let F := (Finset.univ : Finset S.offDiag).filter (fun p ↦ e p = b)
  let g : S.offDiag → ℕ := fun p ↦ min p.1.1 p.1.2
  let B := F.image g
  have hf {p : S.offDiag} (hp : p ∈ F) : e p = b := (Finset.mem_filter.mp hp).2
  have hg : Set.InjOn g (F : Set S.offDiag) := by
    intro p hp q hq heq
    have he : e p = e q := (hf hp).trans (hf hq).symm
    have hsum : p.1.1 + p.1.2 = q.1.1 + q.1.2 := congrArg (fun x ↦ x.1.val) he
    have hflag : decide (p.1.1 ≤ p.1.2) = decide (q.1.1 ≤ q.1.2) :=
      congrArg Prod.snd he
    apply Subtype.ext
    apply Prod.ext
    all_goals
      by_cases hpq : p.1.1 ≤ p.1.2
      · have hqp : q.1.1 ≤ q.1.2 := by simpa [hpq] using hflag.symm
        simp only [g, min_eq_left hpq, min_eq_left hqp] at heq
        omega
      · have hqp : ¬ q.1.1 ≤ q.1.2 := by simpa [hpq] using hflag.symm
        simp only [g, min_eq_right (by omega : p.1.2 ≤ p.1.1),
          min_eq_right (by omega : q.1.2 ≤ q.1.1)] at heq
        omega
  have hBc : B.card = F.card := Finset.card_image_iff.mpr hg
  refine ⟨b.1.val, B, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    have hp' := Finset.mem_offDiag.mp p.2
    dsimp only [g]
    rcases min_choice p.1.1 p.1.2 with h | h
    · simpa only [h] using hp'.1
    · simpa only [h] using hp'.2.1
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    have hp' := Finset.mem_offDiag.mp p.2
    have hsum : p.1.1 + p.1.2 = b.1.val := congrArg (fun x ↦ x.1.val) (hf hp)
    dsimp [g]
    by_cases hle : p.1.1 ≤ p.1.2
    · rw [min_eq_left hle]
      refine ⟨by omega, ?_⟩
      have : b.1.val - p.1.1 = p.1.2 := by omega
      simpa [this] using hp'.2.1
    · rw [min_eq_right (by omega : p.1.2 ≤ p.1.1)]
      refine ⟨by omega, ?_⟩
      have : b.1.val - p.1.2 = p.1.1 := by omega
      simpa [this] using hp'.1
  · rw [hBc]
    have hb' : Fintype.card S.offDiag ≤
        Fintype.card (Fin (2 * N + 1) × Bool) * F.card := by
      convert hb using 1
      congr 2
      ext p
      simp [F]
    simpa only [Fintype.card_coe, Finset.offDiag_card, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_bool, Nat.mul_sub_left_distrib, Nat.mul_one,
      mul_comm (2 * N + 1) 2] using hb'


lemma hasCube_reflect {A B : Set ℕ} {d c : ℕ} (hB : HasCube B d)
    (hBA : B ⊆ A) (hsep : ∀ x ∈ B, 2 * x < c ∧ c - x ∈ A) :
    HasCube A (d + 1) := by
  obtain ⟨S, hSB, hS⟩ := hB
  refine ⟨S ∪ S.image (fun x ↦ c - x), ?_,
    hS.reflect c (fun x hx ↦ (hsep x (hSB hx)).1)⟩
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact hBA (hSB hx)
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (hsep y (hSB hy)).2

/-- A fixed forbidden cube dimension gives polynomial counting decay. -/
theorem cubeFree_card_bound {d : ℕ} {A : Set ℕ} (h : ¬ HasCube A d)
    {S : Finset ℕ} {N : ℕ} (hS : (S : Set ℕ) ⊆ A) (hN : ∀ n ∈ S, n ≤ N) :
    S.card ^ (2 ^ d) ≤ (8 * (N + 1)) ^ (2 ^ d - 1) := by
  induction d generalizing A S N with
  | zero =>
    have he : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact h ⟨{a}, by simpa using hS ha, ReflectedCube.point a⟩
    simp [he]
  | succ d ih =>
    obtain ⟨c, B, hBS, hsep, hcard⟩ := split_bound S N hN
    have hB : ¬ HasCube (B : Set ℕ) d := by
      intro hb
      apply h
      exact hasCube_reflect hb (fun x hx ↦ hS (hBS hx))
        (fun x hx ↦ ⟨(hsep x hx).1, hS (hsep x hx).2⟩)
    have hb := ih hB (Set.Subset.refl _) (fun n hn ↦ hN n (hBS hn))
    have hp : 1 ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    by_cases hs : S.card ≤ 1
    · exact (pow_le_pow_left' hs _).trans (by
        simpa using (one_le_pow₀ (show 1 ≤ 8 * (N + 1) by omega) (n := 2 ^ (d + 1) - 1)))
    · have hpred : S.card - 1 + 1 = S.card := Nat.sub_add_cancel (by omega)
      have hsquare : S.card ^ 2 ≤ 8 * (N + 1) * B.card := by nlinarith
      calc
        S.card ^ (2 ^ (d + 1)) = (S.card ^ 2) ^ (2 ^ d) := by
          rw [← pow_mul, pow_succ']
        _ ≤ (8 * (N + 1) * B.card) ^ (2 ^ d) := pow_le_pow_left' hsquare _
        _ = (8 * (N + 1)) ^ (2 ^ d) * B.card ^ (2 ^ d) := mul_pow _ _ _
        _ ≤ (8 * (N + 1)) ^ (2 ^ d) * (8 * (N + 1)) ^ (2 ^ d - 1) :=
          Nat.mul_le_mul_left _ hb
        _ = (8 * (N + 1)) ^ (2 ^ (d + 1) - 1) := by
          rw [← pow_add, pow_succ']
          congr 1
          omega

lemma cubeFree_card_geometric_bound {d : ℕ} {A : Set ℕ} (h : ¬ HasCube A d)
    {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ A) (j : ℕ)
    (hN : ∀ n ∈ S, n < (2 ^ (2 ^ d)) ^ j) :
    S.card ≤ 8 * (2 ^ (2 ^ d - 1)) ^ j := by
  have hp : 1 ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hpos : 0 < (2 ^ (2 ^ d)) ^ j := by positivity
  have hb := cubeFree_card_bound h hS
    (N := (2 ^ (2 ^ d)) ^ j - 1) (fun n hn ↦ by have := hN n hn; omega)
  rw [Nat.sub_add_cancel hpos, mul_pow] at hb
  have hexp : ((2 ^ (2 ^ d)) ^ j) ^ (2 ^ d - 1) =
      ((2 ^ (2 ^ d - 1)) ^ j) ^ (2 ^ d) := by
    simp only [← pow_mul]
    congr 1
    ring
  rw [hexp] at hb
  apply (Nat.pow_le_pow_iff_left (by positivity : 2 ^ d ≠ 0)).mp
  rw [mul_pow]
  exact hb.trans (Nat.mul_le_mul_right _
    (pow_le_pow_right' (by norm_num : 1 ≤ (8 : ℕ)) (Nat.sub_le _ _)))

/-- A uniform reciprocal bound for finite sets omitting one cube dimension. -/
theorem cubeFree_finite_recip_sum_bound {d : ℕ} {A : Set ℕ}
    (h : ¬ HasCube A d) (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A) :
    (∑ n ∈ S, 1 / (n : ℝ)) ≤ 16 * (2 ^ (2 ^ d - 1) : ℕ) := by
  let Q : ℕ := 2 ^ (2 ^ d)
  let R : ℕ := 2 ^ (2 ^ d - 1)
  have hQ : 1 < Q := one_lt_pow₀ one_lt_two (by positivity)
  have hR : 0 < (R : ℝ) := by dsimp [R]; positivity
  have hQR : Q = 2 * R := by
    dsimp [Q, R]
    rw [← pow_succ']
    congr 1
    have : 0 < 2 ^ d := by positivity
    omega
  have hratio : (R : ℝ) / Q = 1 / 2 := by
    rw [hQR]
    push_cast
    field_simp
  have hgeo : Summable (fun j : ℕ ↦ (8 * (R : ℝ)) * (1 / 2) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left _
  let S' := S.erase 0
  let J := S'.image (Nat.log Q)
  have hfiber (j : ℕ) :
      (∑ n ∈ S'.filter (fun n ↦ Nat.log Q n = j), 1 / (n : ℝ)) ≤
        (8 * (R : ℝ)) * (1 / 2) ^ j := by
    let T := S'.filter (fun n ↦ Nat.log Q n = j)
    have hTsub : (T : Set ℕ) ⊆ A := by
      intro n hn
      exact hS ((Finset.erase_subset _ _) ((Finset.filter_subset _ _) hn))
    have hTb : ∀ n ∈ T, n < Q ^ (j + 1) := by
      intro n hn
      obtain ⟨_, hnj⟩ := Finset.mem_filter.mp hn
      simpa [hnj] using Nat.lt_pow_succ_log_self hQ n
    have hTc : T.card ≤ 8 * R ^ (j + 1) :=
      cubeFree_card_geometric_bound h hTsub (j + 1) hTb
    calc
      (∑ n ∈ T, 1 / (n : ℝ)) ≤ ∑ n ∈ T, 1 / ((Q ^ j : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hnS, hnj⟩ := Finset.mem_filter.mp hn
        have hn0 := (Finset.mem_erase.mp hnS).1
        have hpow : Q ^ j ≤ n := by simpa [hnj] using Nat.pow_log_le_self Q hn0
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hpow)
      _ = (T.card : ℝ) / ((Q ^ j : ℕ) : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ ((8 * R ^ (j + 1) : ℕ) : ℝ) / ((Q ^ j : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hTc
      _ = (8 * (R : ℝ)) * (1 / 2) ^ j := by
        push_cast
        rw [pow_succ', ← mul_assoc, mul_div_assoc, ← div_pow, hratio]
  calc
    (∑ n ∈ S, 1 / (n : ℝ)) = ∑ n ∈ S', 1 / (n : ℝ) :=
      (Finset.sum_erase S (by simp : (1 : ℝ) / (0 : ℕ) = 0)).symm
    _ = ∑ j ∈ J, ∑ n ∈ S'.filter (fun n ↦ Nat.log Q n = j), 1 / (n : ℝ) :=
      (Finset.sum_fiberwise_of_maps_to
        (fun n hn ↦ Finset.mem_image_of_mem (Nat.log Q) hn) (fun n : ℕ ↦ 1 / (n : ℝ))).symm
    _ ≤ ∑ j ∈ J, (8 * (R : ℝ)) * (1 / 2) ^ j :=
      Finset.sum_le_sum (fun j _ ↦ hfiber j)
    _ ≤ ∑' j : ℕ, (8 * (R : ℝ)) * (1 / 2) ^ j :=
      Summable.sum_le_tsum _ (fun _ _ ↦ by positivity) hgeo
    _ = 16 * (R : ℝ) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)]
      ring

/-- Omitting a fixed proper cube dimension forces convergence of the reciprocal sum. -/
theorem summable_of_no_cube {d : ℕ} {A : Set ℕ} (h : ¬ HasCube A d) :
    Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  apply summable_of_sum_le (c := 16 * (2 ^ (2 ^ d - 1) : ℕ))
    (fun _ ↦ by positivity)
  intro F
  let e : A ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hsub : (F.map e : Set ℕ) ⊆ A := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hn
    exact a.property
  simpa [e] using cubeFree_finite_recip_sum_bound h (F.map e) hsub

theorem divergence_has_cubes {A : Set ℕ}
    (h : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) (d : ℕ) : HasCube A d := by
  by_contra hno
  exact h (summable_of_no_cube hno)

#print axioms divergence_has_cubes

/-- The usual vertices of a translated subset-sum cube, with one generator for
 each entry of the list. -/
def vertices (a : ℕ) : List ℕ → Finset ℕ
  | [] => {a}
  | r :: L => vertices a L ∪ (vertices a L).image (fun x ↦ r + x)

lemma reflectedCube_representation {d : ℕ} {S : Finset ℕ} (h : ReflectedCube d S) :
    ∃ a : ℕ, ∃ L : List ℕ, ∃ t : ℕ, L.length = d ∧
      (∀ r ∈ L, 0 < r) ∧ S = vertices a L ∧
      (∀ x ∈ S, x ≤ t ∧ t - x ∈ S) := by
  induction h with
  | point a =>
    refine ⟨a, [], 2 * a, rfl, by simp, rfl, ?_⟩
    intro x hx
    have : x = a := Finset.mem_singleton.mp hx
    subst x
    exact ⟨by omega, by simp; omega⟩
  | @reflect d S h c hsep ih =>
    obtain ⟨a, L, t, hL, hpos, hrep, hsym⟩ := ih
    have hnon : S.Nonempty := Finset.card_pos.mp (by rw [reflectedCube_card h]; positivity)
    obtain ⟨x, hx⟩ := hnon
    have htc : t < c := by
      have hx' := hsym x hx
      have := hsep x hx
      have := hsep (t - x) hx'.2
      omega
    have himage : S.image (fun x ↦ c - x) = S.image (fun x ↦ (c - t) + x) := by
      ext z
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨t - y, (hsym y hy).2, ?_⟩
        have := (hsym y hy).1
        omega
      · rintro ⟨y, hy, rfl⟩
        refine ⟨t - y, (hsym y hy).2, ?_⟩
        have := (hsym y hy).1
        omega
    refine ⟨a, (c - t) :: L, c, by simp [hL], ?_, ?_, ?_⟩
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · omega
      · exact hpos r hr
    · simp only [vertices, ← hrep, himage]
    · intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · have hzc := hsep z hz
        refine ⟨by omega, Finset.mem_union_right _ ?_⟩
        exact Finset.mem_image_of_mem _ hz
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
        have hyc := hsep y hy
        refine ⟨by omega, Finset.mem_union_left _ ?_⟩
        have : c - (c - y) = y := by omega
        simpa only [this] using hy

/-- Reciprocal divergence forces proper subset-sum cubes of every finite dimension.
The exact cardinality guarantees that all 2^d subset sums are distinct. -/
theorem divergence_has_proper_additive_cubes {A : Set ℕ}
    (h : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) (d : ℕ) :
    ∃ a : ℕ, ∃ L : List ℕ, L.length = d ∧ (∀ r ∈ L, 0 < r) ∧
      (vertices a L : Set ℕ) ⊆ A ∧ (vertices a L).card = 2 ^ d := by
  obtain ⟨S, hSA, hS⟩ := divergence_has_cubes h d
  obtain ⟨a, L, t, hL, hpos, hrep, hsym⟩ := reflectedCube_representation hS
  refine ⟨a, L, hL, hpos, ?_, ?_⟩
  · simpa only [← hrep] using hSA
  · simpa only [← hrep] using reflectedCube_card hS

#print axioms divergence_has_proper_additive_cubes

lemma threeAPFree_reflect {S : Finset ℕ} {N c : ℕ}
    (h : ThreeAPFree (S : Set ℕ)) (hN : ∀ x ∈ S, x ≤ N) (hgap : 3 * N < c) :
    ThreeAPFree ((S ∪ S.image (fun x ↦ c - x) : Finset ℕ) : Set ℕ) := by
  have hrep {x : ℕ} (hx : x ∈ S ∪ S.image (fun x ↦ c - x)) :
      ∃ y ∈ S, x = y ∨ x = c - y := by
    rcases Finset.mem_union.mp hx with hx | hx
    · exact ⟨x, hx, Or.inl rfl⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨y, hy, Or.inr rfl⟩
  intro a ha b hb z hz heq
  obtain ⟨x, hx, ha⟩ := hrep ha
  obtain ⟨y, hy, hb⟩ := hrep hb
  obtain ⟨w, hw, hz⟩ := hrep hz
  have hxN := hN x hx
  have hyN := hN y hy
  have hwN := hN w hw
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hz with rfl | rfl
  all_goals first
    | exact h hx hy hw heq
    | (have h' : x + w = y + y := by omega
       have := h hx hy hw h'
       omega)
    | omega

/-- A sparse nested family of proper cubes. -/
def sparseCube : ℕ → Finset ℕ
  | 0 => {0}
  | d + 1 => sparseCube d ∪ (sparseCube d).image (fun x ↦ 4 ^ (d + 1) - x)

lemma sparseCube_bound (d : ℕ) : ∀ x ∈ sparseCube d, x ≤ 4 ^ d := by
  induction d with
  | zero => simp [sparseCube]
  | succ d ih =>
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have := ih x hx
      have : 4 ^ d ≤ 4 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact Nat.sub_le _ _

lemma sparseCube_cube (d : ℕ) : ReflectedCube d (sparseCube d) := by
  induction d with
  | zero => exact ReflectedCube.point 0
  | succ d ih =>
    apply ih.reflect
    intro x hx
    have := sparseCube_bound d x hx
    have : 0 < 4 ^ d := by positivity
    rw [pow_succ']
    omega

lemma sparseCube_free (d : ℕ) : ThreeAPFree (sparseCube d : Set ℕ) := by
  induction d with
  | zero => simp [sparseCube]
  | succ d ih =>
    apply threeAPFree_reflect ih (sparseCube_bound d)
    rw [pow_succ']
    have : 0 < 4 ^ d := by positivity
    omega

lemma sparseCube_mono : Monotone sparseCube :=
  monotone_nat_of_le_succ (fun _ ↦ Finset.subset_union_left)

/-- A single 3-AP-free set can contain proper cubes of every finite dimension.
Thus the unconditional cube conclusion does not imply the target AP conclusion. -/
theorem cubes_do_not_force_threeAP :
    ∃ A : Set ℕ, ThreeAPFree A ∧ ∀ d : ℕ, HasCube A d := by
  refine ⟨⋃ d : ℕ, (sparseCube d : Set ℕ), ?_, ?_⟩
  · intro a ha b hb c hc heq
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hc
    exact sparseCube_free (i + j + k)
      (sparseCube_mono (by omega : i ≤ i + j + k) hi)
      (sparseCube_mono (by omega : j ≤ i + j + k) hj)
      (sparseCube_mono (by omega : k ≤ i + j + k) hk) heq
  · intro d
    refine ⟨sparseCube d, ?_, sparseCube_cube d⟩
    exact Set.subset_iUnion (fun d : ℕ ↦ (sparseCube d : Set ℕ)) d

#print axioms cubes_do_not_force_threeAP

lemma sparseCube_recip_sum (d : ℕ) :
    (∑ n ∈ sparseCube d, 1 / (n : ℝ)) ≤
      ∑ j ∈ Finset.range d, (1 / 3 : ℝ) * (1 / 2) ^ j := by
  induction d with
  | zero => simp [sparseCube]
  | succ d ih =>
    have hdis : Disjoint (sparseCube d)
        ((sparseCube d).image (fun x ↦ 4 ^ (d + 1) - x)) := by
      apply Finset.disjoint_left.mpr
      intro x hx hi
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hi
      have := sparseCube_bound d y hy
      have := sparseCube_bound d (4 ^ (d + 1) - y) hx
      have : 0 < 4 ^ d := by positivity
      rw [pow_succ'] at *
      omega
    have hinj : Set.InjOn (fun x ↦ 4 ^ (d + 1) - x) (sparseCube d : Set ℕ) := by
      intro x hx y hy heq
      dsimp only at heq
      have := sparseCube_bound d x hx
      have := sparseCube_bound d y hy
      have : 0 < 4 ^ d := by positivity
      rw [pow_succ'] at heq
      omega
    have hsum : (∑ n ∈ (sparseCube d).image (fun x ↦ (4 ^ (d + 1) - x : ℕ)),
        1 / (n : ℝ)) ≤ (1 / 3 : ℝ) * (1 / 2) ^ d := by
      rw [Finset.sum_image hinj]
      calc
        (∑ n ∈ sparseCube d, 1 / ((4 ^ (d + 1) - n : ℕ) : ℝ)) ≤
            ∑ _n ∈ sparseCube d, 1 / ((3 * 4 ^ d : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have hb := sparseCube_bound d n hn
          have hgap : 3 * 4 ^ d ≤ 4 ^ (d + 1) - n := by rw [pow_succ']; omega
          exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hgap)
        _ = (1 / 3 : ℝ) * (1 / 2) ^ d := by
          simp only [Finset.sum_const, nsmul_eq_mul,
            reflectedCube_card (sparseCube_cube d)]
          push_cast
          rw [mul_one_div, mul_comm (3 : ℝ), div_mul_eq_div_div, ← div_pow]
          norm_num
          ring
    rw [sparseCube, Finset.sum_union hdis, Finset.sum_range_succ]
    exact add_le_add ih hsum

lemma finite_subset_sparseCube {S : Finset ℕ}
    (h : (S : Set ℕ) ⊆ ⋃ d : ℕ, (sparseCube d : Set ℕ)) :
    ∃ d : ℕ, S ⊆ sparseCube d := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | @insert a S ha ih =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (h (Finset.mem_insert_self _ _))
    obtain ⟨j, hj⟩ := ih (fun x hx ↦ h (Finset.mem_insert_of_mem hx))
    refine ⟨i + j, Finset.insert_subset_iff.mpr ⟨?_, ?_⟩⟩
    · exact sparseCube_mono (by omega : i ≤ i + j) hi
    · exact hj.trans (sparseCube_mono (by omega : j ≤ i + j))

/-- The explicit cube-rich, 3-AP-free example has convergent reciprocal sum;
it is not a counterexample to the original conjecture. -/
theorem sparseCube_union_summable :
    Summable (fun a : (⋃ d : ℕ, (sparseCube d : Set ℕ)) ↦ 1 / (a : ℝ)) := by
  let f : ℕ → ℝ := fun j ↦ (1 / 3 : ℝ) * (1 / 2) ^ j
  have hf : Summable f :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left _
  apply summable_of_sum_le (c := ∑' j : ℕ, f j) (fun _ ↦ by positivity)
  intro F
  let e : (⋃ d : ℕ, (sparseCube d : Set ℕ)) ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hsub : (F.map e : Set ℕ) ⊆ ⋃ d : ℕ, (sparseCube d : Set ℕ) := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hn
    exact a.property
  obtain ⟨d, hd⟩ := finite_subset_sparseCube hsub
  have hsum : (∑ n ∈ F.map e, 1 / (n : ℝ)) ≤ ∑' j : ℕ, f j := calc
    _ ≤ ∑ n ∈ sparseCube d, 1 / (n : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hd (fun _ _ _ ↦ by positivity)
    _ ≤ ∑ j ∈ Finset.range d, f j := sparseCube_recip_sum d
    _ ≤ _ := Summable.sum_le_tsum _ (fun _ _ ↦ by positivity) hf
  simpa [e] using hsum

#print axioms sparseCube_union_summable

end Erdos3CubeCase
