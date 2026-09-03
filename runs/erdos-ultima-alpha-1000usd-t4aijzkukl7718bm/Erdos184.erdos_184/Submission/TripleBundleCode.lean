import Submission.BinaryExtensionHull

/-!
Three parallel edge bundles. This auxiliary binary/graphical code will supply
an obstruction to the unrestricted one-generator hull inequality.
-/
open scoped Classical symmDiff
namespace Erdos184Serial.TripleBundle
open BinaryExtension
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {A : Type*} [DecidableEq A]
abbrev Edge (A : Type*) := Fin 3 × A

def row (s : Finset (Edge A)) (i : Fin 3) : Finset (Edge A) :=
  s.filter (fun e => e.1 = i)
def count (s : Finset (Edge A)) (i : Fin 3) : ℕ := (row s i).card

lemma count_sdiff_add {s t : Finset (Edge A)} (h : t ⊆ s) (i : Fin 3) :
    count (s \ t) i + count t i = count s i := by
  have he : row (s \ t) i = row s i \ row t i := by
    ext e
    simp only [row, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  unfold count
  rw [he]
  exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset_filter _ h)

lemma count_mono {s t : Finset (Edge A)} (h : s ⊆ t) (i : Fin 3) :
    count s i ≤ count t i := Finset.card_le_card (Finset.filter_subset_filter _ h)

lemma count_pos_of_mem {s : Finset (Edge A)} {e : Edge A} (he : e ∈ s) :
    0 < count s e.1 := Finset.card_pos.mpr ⟨e, by simp [row, he]⟩

lemma count_zero_iff {s : Finset (Edge A)} {i : Fin 3} :
    count s i = 0 ↔ ∀ e ∈ s, e.1 ≠ i := by
  simp [count, row, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

lemma count_sum (s : Finset (Edge A)) : ∑ i : Fin 3, count s i = s.card := by
  symm
  exact Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := s)
    (t := Finset.univ) (by intro e he; simp)

lemma card_mod_symmDiff {E : Type*} [DecidableEq E] (s t : Finset E) :
    (s ∆ t).card % 2 = (s.card + t.card) % 2 := by
  have h1 := Finset.card_sdiff_add_card_inter s t
  have h2 := Finset.card_sdiff_add_card_inter t s
  have hd : Disjoint (s \ t) (t \ s) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have h3 := Finset.card_union_of_disjoint hd
  have he : s ∆ t = (s \ t) ∪ (t \ s) := rfl
  rw [← he] at h3
  rw [Finset.inter_comm t s] at h2
  omega

lemma count_mod_symmDiff (s t : Finset (Edge A)) (i : Fin 3) :
    count (s ∆ t) i % 2 = (count s i + count t i) % 2 := by
  have he : row (s ∆ t) i = row s i ∆ row t i := by
    ext e
    simp only [row, Finset.mem_filter, Finset.mem_symmDiff]
    tauto
  simpa only [count, he] using card_mod_symmDiff (row s i) (row t i)

/-- Independent even parity in each bundle, as in a chain of bundles. -/
def source : Code (Edge A) where
  valid s := ∀ i, count s i % 2 = 0
  empty := by intro i; simp [count, row]
  diff := by
    intro s t hs ht hts i
    have hc := count_sdiff_add hts i
    have h1 := hs i
    have h2 := ht i
    omega

/-- Equal parity in all three bundles, as in a triangle of bundles. -/
def target : Code (Edge A) where
  valid s := ∀ i j, count s i % 2 = count s j % 2
  empty := by intro i j; simp [count, row]
  diff := by
    intro s t hs ht hts i j
    have hi := count_sdiff_add hts i
    have hj := count_sdiff_add hts j
    have h1 := hs i j
    have h2 := ht i j
    omega

lemma source_xorClosed : XorClosed (source (A := A)) := by
  intro s t hs ht i
  rw [count_mod_symmDiff, Nat.add_mod, hs i, ht i]

lemma target_xorClosed : XorClosed (target (A := A)) := by
  intro s t hs ht i j
  rw [count_mod_symmDiff, count_mod_symmDiff]
  have h1 := hs i j
  have h2 := ht i j
  omega

lemma source_to_target {s : Finset (Edge A)} (hs : source.valid s) : target.valid s :=
  fun i j => (hs i).trans (hs j).symm

/-- One edge chosen in each of the three bundles. -/
def triple (a : Fin 3 → A) : Finset (Edge A) := Finset.univ.image (fun i => (i, a i))

lemma triple_mem (a : Fin 3 → A) (i : Fin 3) : (i, a i) ∈ triple a := by
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

lemma row_triple (a : Fin 3 → A) (i : Fin 3) : row (triple a) i = {(i, a i)} := by
  ext e
  simp only [row, triple, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨j, rfl⟩, rfl⟩
    rfl
  · rintro rfl
    exact ⟨⟨i, rfl⟩, rfl⟩

lemma count_triple (a : Fin 3 → A) (i : Fin 3) : count (triple a) i = 1 := by
  simp [count, row_triple]

lemma card_triple (a : Fin 3 → A) : (triple a).card = 3 := by
  rw [← count_sum]
  simp [count_triple]

lemma triple_valid (a : Fin 3 → A) : target.valid (triple a) := by
  intro i j
  rw [count_triple, count_triple]

lemma triple_circuit (a : Fin 3 → A) : Circuit target (triple a) := by
  refine ⟨triple_valid a, ⟨(0, a 0), triple_mem a 0⟩, ?_⟩
  intro t ht hv hn
  obtain ⟨e, he⟩ := hn
  have hpos := count_pos_of_mem he
  have hub (i : Fin 3) : count t i ≤ 1 := by
    simpa only [count_triple] using count_mono ht i
  have hc (i : Fin 3) : count t i = 1 := by
    have hp := hv i e.1
    have h0 := hub e.1
    have h1 := hub i
    omega
  apply Finset.Subset.antisymm ht
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  have hp : 0 < (row t i).card := by change 0 < count t i; rw [hc]; omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hp
  have hyi := (Finset.mem_filter.mp hy).2
  have hyt := (Finset.mem_filter.mp hy).1
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (ht hyt)
  have hji : j = i := by simpa only [← hj] using hyi
  subst j
  simpa only [← hj] using hyt

lemma target_extension (a : Fin 3 → A) : ExtensionBy source target (triple a) := by
  intro s
  constructor
  · intro hs
    by_cases h0 : count s 0 % 2 = 0
    · exact Or.inl (fun i => (hs i 0).trans h0)
    · right
      intro i
      rw [count_mod_symmDiff, count_triple]
      have hi := hs i 0
      omega
  · rintro (hs | hs)
    · exact source_to_target hs
    · intro i j
      have hi := hs i
      have hj := hs j
      rw [count_mod_symmDiff, count_triple] at hi hj
      omega

lemma row_pair (i j : Fin 3) (a b : A) :
    row {(i, a), (i, b)} j = if i = j then {(i, a), (i, b)} else ∅ := by
  by_cases h : i = j
  · subst j
    simp [row]
  · simp [row, h]

lemma count_pair (i j : Fin 3) {a b : A} (hab : a ≠ b) :
    count {(i, a), (i, b)} j = if i = j then 2 else 0 := by
  have he : (i, a) ≠ (i, b) := fun h => hab (congrArg Prod.snd h)
  simp only [count, row_pair]
  split_ifs <;> simp [Finset.card_pair he]

lemma pair_source_valid (i : Fin 3) {a b : A} (hab : a ≠ b) :
    source.valid {(i, a), (i, b)} := by
  intro j
  rw [count_pair i j hab]
  split_ifs <;> decide

lemma pair_circuit (i : Fin 3) {a b : A} (hab : a ≠ b) :
    Circuit target {(i, a), (i, b)} := by
  have he : (i, a) ≠ (i, b) := fun h => hab (congrArg Prod.snd h)
  refine ⟨source_to_target (pair_source_valid i hab), by simp, ?_⟩
  intro t ht hv hn
  have hrow : row t i = t := by
    apply Finset.filter_eq_self.mpr
    intro e het
    have hh := ht het
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl <;> rfl
  obtain ⟨j, hji⟩ := exists_ne i
  have hcj : count t j = 0 := by
    have hle := count_mono ht j
    rw [count_pair i j hab, if_neg (Ne.symm hji)] at hle
    omega
  have hp := hv i j
  change (row t i).card % 2 = count t j % 2 at hp
  rw [hrow, hcj] at hp
  have hpos := Finset.card_pos.mpr hn
  have hle := Finset.card_le_card ht
  rw [Finset.card_pair he] at hle
  have hcard : t.card = 2 := by omega
  apply Finset.eq_of_subset_of_card_le ht
  rw [Finset.card_pair he, hcard]

lemma source_circuit_card {s : Finset (Edge A)} (hs : Circuit source s) :
    s.card = 2 := by
  obtain ⟨e, he⟩ := hs.2.1
  have hp := count_pos_of_mem he
  have hv := hs.1 e.1
  have htwo : 1 < (row s e.1).card := by change 1 < count s e.1; omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp htwo
  obtain ⟨hx, hxi⟩ := Finset.mem_filter.mp hx
  obtain ⟨hy, hyi⟩ := Finset.mem_filter.mp hy
  have hxs : (e.1, x.2) = x := Prod.ext hxi.symm rfl
  have hys : (e.1, y.2) = y := Prod.ext hyi.symm rfl
  have hne : x.2 ≠ y.2 := by
    intro h
    apply hxy
    exact Prod.ext (hxi.trans hyi.symm) h
  have hsub : {(e.1, x.2), (e.1, y.2)} ⊆ s := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hxs.symm ▸ hx, hys.symm ▸ hy⟩
  have heq := hs.2.2 _ hsub (pair_source_valid e.1 hne) (by simp)
  have hpair : (e.1, x.2) ≠ (e.1, y.2) := by
    intro h
    have hh := congrArg (fun p : Edge A => p.2) h
    exact hne hh
  rw [← heq, Finset.card_pair hpair]

lemma source_partition_card {s : Finset (Edge A)} {D : Finset (Finset (Edge A))}
    (hD : Partition source s D) : 2 * D.card = s.card := by
  have hc := Finset.card_biUnion (s := D) (t := id) hD.2.1
  rw [← hD.2.2, hc]
  change 2 * D.card = ∑ a ∈ D, a.card
  have he : ∑ a ∈ D, a.card = ∑ a ∈ D, 2 :=
    Finset.sum_congr rfl (fun a ha => source_circuit_card (hD.1 a ha))
  simpa [mul_comm] using he.symm

lemma exists_row_pair {s : Finset (Edge A)} {i : Fin 3} (h : 2 ≤ count s i) :
    ∃ a b : A, a ≠ b ∧ (i, a) ∈ s ∧ (i, b) ∈ s := by
  have htwo : 1 < (row s i).card := by change 1 < count s i; omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp htwo
  obtain ⟨hx, hxi⟩ := Finset.mem_filter.mp hx
  obtain ⟨hy, hyi⟩ := Finset.mem_filter.mp hy
  refine ⟨x.2, y.2, ?_, ?_, ?_⟩
  · intro hh
    exact hxy (Prod.ext (hxi.trans hyi.symm) hh)
  · have he : (i, x.2) = x := Prod.ext hxi.symm rfl
    exact he.symm ▸ hx
  · have he : (i, y.2) = y := Prod.ext hyi.symm rfl
    exact he.symm ▸ hy

/-- Greedily use triangles until a least-populated bundle is exhausted, then
pair the edges in the remaining two bundles. Every piece uses exactly two
edges outside the least-populated bundle. -/
lemma target_partition (s : Finset (Edge A)) :
    ∀ (_hs : target.valid s) (k : Fin 3), (∀ i, count s k ≤ count s i) →
    ∃ D, Partition target s D ∧ 2 * D.card + count s k = s.card := by
  induction s using Finset.strongInductionOn
  rename_i s ih
  intro hs k hmin
  by_cases hn : s.Nonempty
  · by_cases hall : ∀ i, 0 < count s i
    · have hex (i : Fin 3) : ∃ a : A, (i, a) ∈ s := by
        obtain ⟨e, he⟩ := Finset.card_pos.mp (hall i)
        obtain ⟨he, hei⟩ := Finset.mem_filter.mp he
        refine ⟨e.2, ?_⟩
        have heq : (i, e.2) = e := Prod.ext hei.symm rfl
        exact heq.symm ▸ he
      choose a ha using hex
      have hp : triple a ⊆ s := by
        intro e he
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
        exact ha i
      have hv := triple_circuit a
      have hrest := target.diff hs hv.1 hp
      have hct (i : Fin 3) : count (s \ triple a) i + 1 = count s i := by
        simpa only [count_triple] using count_sdiff_add hp i
      have hmin' (i : Fin 3) : count (s \ triple a) k ≤ count (s \ triple a) i := by
        have h1 := hct k
        have h2 := hct i
        have h3 := hmin i
        omega
      obtain ⟨D, hD, hc⟩ := ih (s \ triple a) (Finset.sdiff_ssubset hp hv.2.1)
        hrest k hmin'
      have hd : Disjoint (triple a) (s \ triple a) := by
        apply Finset.disjoint_left.mpr
        intro e he hf
        exact (Finset.mem_sdiff.mp hf).2 he
      obtain ⟨hP, hcard⟩ := (partition_singleton hv).join hD hd
      rw [Finset.union_sdiff_of_subset hp] at hP
      refine ⟨_, hP, ?_⟩
      have hsize := Finset.card_sdiff_add_card_eq_card hp
      rw [card_triple] at hsize
      simp only [Finset.card_singleton] at hcard
      have hck := hct k
      omega
    · obtain ⟨j, hj⟩ := not_forall.mp hall
      have hz : count s j = 0 := by omega
      have hkz : count s k = 0 := by have hh := hmin j; omega
      obtain ⟨e, he⟩ := hn
      have hpos := count_pos_of_mem he
      have hpar := hs e.1 j
      have htwo : 2 ≤ count s e.1 := by omega
      obtain ⟨a, b, hab, ha, hb⟩ := exists_row_pair htwo
      let p : Finset (Edge A) := {(e.1, a), (e.1, b)}
      have hp : p ⊆ s := by
        simp only [p, Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨ha, hb⟩
      have hv : Circuit target p := pair_circuit e.1 hab
      have hpk : count p k = 0 := by have hh := count_mono hp k; omega
      have hck := count_sdiff_add hp k
      have hrestk : count (s \ p) k = 0 := by omega
      obtain ⟨D, hD, hc⟩ := ih (s \ p) (Finset.sdiff_ssubset hp hv.2.1)
        (target.diff hs hv.1 hp) k (by intro i; rw [hrestk]; omega)
      have hd : Disjoint p (s \ p) := by
        apply Finset.disjoint_left.mpr
        intro x hx hy
        exact (Finset.mem_sdiff.mp hy).2 hx
      obtain ⟨hP, hcard⟩ := (partition_singleton hv).join hD hd
      rw [Finset.union_sdiff_of_subset hp] at hP
      refine ⟨_, hP, ?_⟩
      have hsize := Finset.card_sdiff_add_card_eq_card hp
      have hp2 : p.card = 2 := by
        apply Finset.card_pair
        exact fun h => hab (congrArg (fun p : Edge A => p.2) h)
      rw [hp2] at hsize
      simp only [Finset.card_singleton] at hcard
      omega
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
    subst s
    exact ⟨∅, partition_empty target, by simp [count, row]⟩

lemma count_le_card [Fintype A] (s : Finset (Edge A)) (i : Fin 3) :
    count s i ≤ Fintype.card A := by
  have hinj : Function.Injective (fun e : row s i => e.val.2) := by
    intro e f he
    apply Subtype.ext
    apply Prod.ext
    · exact (Finset.mem_filter.mp e.property).2.trans
        (Finset.mem_filter.mp f.property).2.symm
    · exact he
  have hh := Fintype.card_le_of_injective _ hinj
  simpa only [Fintype.card_coe, count] using hh

lemma target_hullBound [Fintype A] : HullBound (target (A := A)) (Fintype.card A) := by
  intro s hs
  obtain ⟨k, _, hk⟩ := Finset.exists_min_image Finset.univ (count s) ⟨0, Finset.mem_univ _⟩
  obtain ⟨D, hD, hc⟩ := target_partition s hs k (fun i => hk i (Finset.mem_univ _))
  refine ⟨D, hD, ?_⟩
  have hsum := count_sum s
  have h0 := count_le_card s 0
  have h1 := count_le_card s 1
  have h2 := count_le_card s 2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
  change count s 0 + (count s 1 + count s 2) = s.card at hsum
  fin_cases k <;> dsimp at hc <;> omega

lemma source_not_hullBound_five : ¬ HullBound (source (A := Fin 4)) 5 := by
  intro h
  have hv : (source (A := Fin 4)).valid Finset.univ := by
    change ∀ i : Fin 3, count (Finset.univ : Finset (Edge (Fin 4))) i % 2 = 0
    decide +kernel
  obtain ⟨D, hD, hc⟩ := h Finset.univ hv
  have he := source_partition_card hD
  norm_num [Fintype.card_prod] at he
  omega

/-- The proposed unrestricted loss-at-most-one inequality is false. -/
theorem extension_hull_counterexample :
    ∃ (C B : Code (Edge (Fin 4))) (z : Finset (Edge (Fin 4))),
      XorClosed C ∧ ExtensionBy C B z ∧ HullBound B 4 ∧ ¬ HullBound C 5 := by
  exact ⟨source, target, triple (fun _ => 0), source_xorClosed,
    target_extension _, by simpa using target_hullBound (A := Fin 4), source_not_hullBound_five⟩

lemma count_univ [Fintype A] (i : Fin 3) :
    count (Finset.univ : Finset (Edge A)) i = Fintype.card A := by
  have he : row (Finset.univ : Finset (Edge A)) i =
      (Finset.univ : Finset A).image (fun a => (i, a)) := by
    ext e
    rcases e with ⟨j, a⟩
    simp [row, eq_comm]
  have hinj : Function.Injective (fun a : A => (i, a)) := by
    intro a b h
    exact (Prod.mk.inj h).2
  rw [count, he, Finset.card_image_of_injective _ hinj, Finset.card_univ]

lemma target_circuit_card_le_three {s : Finset (Edge A)} (hs : Circuit target s) :
    s.card ≤ 3 := by
  by_cases hall : ∀ i, count s i ≤ 1
  · have hh := count_sum s
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hh
    change count s 0 + (count s 1 + count s 2) = s.card at hh
    have h0 := hall 0
    have h1 := hall 1
    have h2 := hall 2
    omega
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    obtain ⟨a, b, hab, ha, hb⟩ := exists_row_pair (by omega : 2 ≤ count s i)
    have hsub : {(i, a), (i, b)} ⊆ s := by
      exact Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩
    have he := hs.2.2 _ hsub (source_to_target (pair_source_valid i hab)) (by simp)
    have hne : (i, a) ≠ (i, b) := fun hh => hab (Prod.mk.inj hh).2
    rw [← he, Finset.card_pair hne]
    omega

lemma target_full_lower [Fintype A] {D : Finset (Finset (Edge A))}
    (hD : Partition target Finset.univ D) : Fintype.card A ≤ D.card := by
  have hc := Finset.card_biUnion (s := D) (t := id) hD.2.1
  rw [hD.2.2] at hc
  change (Finset.univ : Finset (Edge A)).card = ∑ p ∈ D, p.card at hc
  have hb : (∑ p ∈ D, p.card) ≤ ∑ p ∈ D, 3 :=
    Finset.sum_le_sum (fun p hp => target_circuit_card_le_three (hD.1 p hp))
  simp only [Finset.sum_const, smul_eq_mul] at hb
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hc
  omega

lemma target_full_hasNumber [Fintype A] :
    HasNumber (target (A := A)) Finset.univ (Fintype.card A) := by
  have hv : (target (A := A)).valid Finset.univ := by intro i j; rw [count_univ, count_univ]
  obtain ⟨D, hD, hn⟩ := target_hullBound Finset.univ hv
  have hl := target_full_lower hD
  exact ⟨⟨D, hD, by omega⟩, fun P hP => target_full_lower hP⟩

lemma source_full_valid (r : ℕ) :
    (source (A := Fin (2 * r))).valid Finset.univ := by
  intro i
  rw [count_univ, Fintype.card_fin]
  omega

lemma source_full_rigid (r : ℕ) :
    Rigid (source (A := Fin (2 * r))) Finset.univ (3 * r) := by
  intro D hD
  have hc := source_partition_card hD
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hc
  omega

lemma source_full_minimalCore (r : ℕ) :
    MinimalCore (source (A := Fin (2 * r))) Finset.univ (3 * r) :=
  minimalCore_of_rigid (source_full_valid r) (source_full_rigid r)

lemma source_hullBound (r : ℕ) : HullBound (source (A := Fin (2 * r))) (3 * r) := by
  intro s hs
  obtain ⟨D, hD⟩ := exists_partition source hs
  refine ⟨D, hD, ?_⟩
  have hc := source_partition_card hD
  have hb := Finset.card_le_univ s
  simp only [Fintype.card_prod, Fintype.card_fin] at hb
  omega

/-- In fact there is no fixed additive bound for one-generator hull loss.
The source witnesses here are themselves rigid minimal cores. -/
theorem unbounded_extension_hull_loss (c : ℕ) :
    ∃ (C B : Code (Edge (Fin (2 * (c + 1)))) )
      (z : Finset (Edge (Fin (2 * (c + 1))))),
      XorClosed C ∧ ExtensionBy C B z ∧
      MinimalCore C Finset.univ (3 * (c + 1)) ∧
      HullBound B (2 * (c + 1)) ∧ ¬ HullBound C (2 * (c + 1) + c) := by
  let a : Fin 3 → Fin (2 * (c + 1)) := fun _ => ⟨0, by omega⟩
  refine ⟨source, target, triple a, source_xorClosed, target_extension a,
    source_full_minimalCore (c + 1), ?_, ?_⟩
  · simpa only [Fintype.card_fin] using target_hullBound (A := Fin (2 * (c + 1)))
  · intro h
    obtain ⟨D, hD, hn⟩ := h Finset.univ (source_full_valid (c + 1))
    have hc := source_full_rigid (c + 1) D hD
    omega

#print axioms target_full_hasNumber
#print axioms source_full_minimalCore
#print axioms unbounded_extension_hull_loss
#print axioms target_partition
#print axioms target_hullBound
#print axioms extension_hull_counterexample
#print axioms source_partition_card
#print axioms triple_circuit
#print axioms target_extension
end Erdos184Serial.TripleBundle
