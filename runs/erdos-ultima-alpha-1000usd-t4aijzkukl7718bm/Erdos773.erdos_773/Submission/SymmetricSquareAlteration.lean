import Submission.HypergraphLinearization
import Submission.ControlledSquareLinearization
import Submission.APBounds

/-! Symmetry-preserving alteration for square-Sidon sets. This auxiliary
construction does not prove the near-linear conjecture. -/
namespace Erdos773.SymmetricSquareAlteration
open Finset Filter SquareCollisionCodegrees
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option Elab.async false

/-- The smaller root in a reflection pair. -/
def orbit (s a : ℕ) : ℕ := min a (s - a)

def labels (s : ℕ) : Finset ℕ := Icc 1 ((s - 1) / 2)

def closure (s : ℕ) (B : Finset ℕ) : Finset ℕ := B ∪ B.image (fun a => s - a)

def carrier (s : ℕ) : Finset ℕ := closure s (labels s)

lemma orbit_eq_iff {s a b : ℕ} (ha : a ≤ s) (hb : b ≤ s) :
    orbit s a = orbit s b ↔ a = b ∨ a + b = s := by
  unfold orbit
  simp only [min_def]
  split_ifs <;> omega

lemma label_bounds {s a : ℕ} (ha : a ∈ labels s) : 1 ≤ a ∧ 2 * a < s := by
  simp only [labels, mem_Icc] at ha
  omega

lemma orbit_label {s a : ℕ} (ha : a ∈ labels s) : orbit s a = a := by
  have hh := label_bounds ha
  unfold orbit
  omega

lemma closure_mem {s : ℕ} {B : Finset ℕ} (hB : B ⊆ labels s) {a : ℕ} :
    a ∈ closure s B ↔ ∃ b ∈ B, a = b ∨ a + b = s := by
  constructor
  · intro ha
    rcases mem_union.mp ha with ha | ha
    · exact ⟨a, ha, Or.inl rfl⟩
    · obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
      have hh := label_bounds (hB hb)
      exact ⟨b, hb, Or.inr (by omega)⟩
  · rintro ⟨b, hb, hab | hab⟩
    · subst a; exact mem_union_left _ hb
    · have ha : a = s - b := by omega
      exact mem_union_right _ (mem_image.mpr ⟨b, hb, ha.symm⟩)

lemma carrier_bounds {s a : ℕ} (ha : a ∈ carrier s) :
    1 ≤ a ∧ a < s ∧ 2 * a ≠ s := by
  obtain ⟨b, hb, hab | hab⟩ := (closure_mem (Subset.refl _) ).mp ha
  all_goals have hh := label_bounds hb
  all_goals omega

lemma carrier_subset (s : ℕ) : carrier s ⊆ Icc 1 s := by
  intro a ha
  have hh := carrier_bounds ha
  exact mem_Icc.mpr ⟨hh.1, hh.2.1.le⟩

lemma orbit_carrier {s a : ℕ} (ha : a ∈ carrier s) : orbit s a ∈ labels s := by
  obtain ⟨b, hb, hab⟩ := (closure_mem (Subset.refl _)).mp ha
  have haS := (carrier_bounds ha).2.1.le
  have hbS : b ≤ s := by have hh := label_bounds hb; omega
  have he := (orbit_eq_iff haS hbS).mpr hab
  rwa [he, orbit_label hb]

lemma mem_closure_iff {s : ℕ} {B : Finset ℕ} (hB : B ⊆ labels s) {a : ℕ}
    (ha : a ∈ carrier s) : a ∈ closure s B ↔ orbit s a ∈ B := by
  rw [closure_mem hB]
  constructor
  · rintro ⟨b, hb, hab⟩
    have haS := (carrier_bounds ha).2.1.le
    have hbS : b ≤ s := by have hh := label_bounds (hB hb); omega
    have he := (orbit_eq_iff haS hbS).mpr hab
    simpa only [he, orbit_label (hB hb)] using hb
  · intro hb
    refine ⟨orbit s a, hb, ?_⟩
    have haS := (carrier_bounds ha).2.1.le
    have hoS : orbit s a ≤ s := (min_le_left _ _).trans haS
    apply (orbit_eq_iff haS hoS).mp
    rw [orbit_label (orbit_carrier ha)]

lemma closure_subset {s : ℕ} {B : Finset ℕ} (hB : B ⊆ labels s) :
    closure s B ⊆ carrier s := by
  exact union_subset_union hB (image_subset_image hB)

lemma closure_symmetric {s : ℕ} {B : Finset ℕ} (hB : B ⊆ labels s) :
    ∀ a ∈ closure s B, a ≤ s ∧ s - a ∈ closure s B := by
  intro a ha
  have haS := (carrier_bounds (closure_subset hB ha)).2.1.le
  refine ⟨haS, ?_⟩
  obtain ⟨b, hb, hab | hab⟩ := (closure_mem hB).mp ha
  · exact (closure_mem hB).mpr ⟨b, hb, Or.inr (by omega)⟩
  · exact (closure_mem hB).mpr ⟨b, hb, Or.inl (by omega)⟩

lemma closure_card {s : ℕ} {B : Finset ℕ} (hB : B ⊆ labels s) :
    (closure s B).card = 2 * B.card := by
  have hd : Disjoint B (B.image (fun a => s - a)) := by
    apply disjoint_left.mpr
    intro a ha hb
    obtain ⟨b, hb, he⟩ := mem_image.mp hb
    have hha := label_bounds (hB ha)
    have hhb := label_bounds (hB hb)
    change s - b = a at he
    omega
  have hi : Set.InjOn (fun a => s - a) B := by
    intro a ha b hb he
    have hha := label_bounds (hB ha)
    have hhb := label_bounds (hB hb)
    change s - a = s - b at he
    omega
  rw [closure, card_union_of_disjoint hd, card_image_of_injOn hi]
  omega

lemma four_distinct {a b c d : ℕ} (h4 : ({a,b,c,d} : Finset ℕ).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have ha : a ∉ ({b,c,d} : Finset ℕ) := by
    intro hh
    rw [insert_eq_of_mem hh] at h4
    have ht := card_le_three (a := b) (b := c) (c := d)
    omega
  rw [card_insert_of_notMem ha] at h4
  have hb : b ∉ ({c,d} : Finset ℕ) := by
    intro hh
    rw [insert_eq_of_mem hh] at h4
    have ht := card_le_two (a := c) (b := d)
    omega
  rw [card_insert_of_notMem hb] at h4
  have hc : c ≠ d := by intro hh; simp [hh] at h4
  simp only [mem_insert, mem_singleton, not_or] at ha hb
  exact ⟨ha.1, ha.2.1, ha.2.2, hb.1, hb.2, hc⟩

lemma edge_orbit_card {s : ℕ} {e : Finset ℕ} (he : e ∈ edges (carrier s)) :
    (e.image (orbit s)).card = 3 ∨ (e.image (orbit s)).card = 4 := by
  classical
  obtain ⟨heA, h4, heq⟩ := mem_filter.mp he
  have hsub := mem_powerset.mp heA
  by_cases hinj : Set.InjOn (orbit s) e
  · right
    rw [card_image_of_injOn hinj, h4]
  · obtain ⟨a, ha, b, hb, hab, ho⟩ :
        ∃ a ∈ e, ∃ b ∈ e, a ≠ b ∧ orbit s a = orbit s b := by
      simpa only [Set.InjOn, mem_coe, not_forall, _root_.not_imp, exists_prop, and_assoc,
        and_left_comm, and_comm] using hinj
    obtain ⟨c, hc, d, hd, he', hcase⟩ := relabel hab ha hb heq
    have haS := (carrier_bounds (hsub ha)).2.1.le
    have hbS := (carrier_bounds (hsub hb)).2.1.le
    have hcS := (carrier_bounds (hsub hc)).2.1.le
    have hdS := (carrier_bounds (hsub hd)).2.1.le
    have hsum : a + b = s := (orbit_eq_iff haS hbS).mp ho |>.resolve_left hab
    rw [he'] at h4
    obtain ⟨hab', hac, had, hbc, hbd, hcd⟩ := four_distinct h4
    have hoc : orbit s a ≠ orbit s c := by
      intro hh
      rcases (orbit_eq_iff haS hcS).mp hh with hh | hh
      · exact hac hh
      · apply hbc; omega
    have hod : orbit s a ≠ orbit s d := by
      intro hh
      rcases (orbit_eq_iff haS hdS).mp hh with hh | hh
      · exact had hh
      · apply hbd; omega
    have hcod : orbit s c ≠ orbit s d := by
      intro hh
      rcases (orbit_eq_iff hcS hdS).mp hh with hh | hh
      · exact hcd hh
      · rcases hcase with hcase | hcase | hcase
        · have hz : ((a:ℤ)-c)*((a:ℤ)-d)=0 := by nlinarith
          rcases mul_eq_zero.mp hz with hz | hz
          · apply hac; omega
          · apply had; omega
        · have hz : ((a:ℤ)+b)*((a:ℤ)-d)=0 := by nlinarith
          rcases mul_eq_zero.mp hz with hz | hz
          · have ha0 := (carrier_bounds (hsub ha)).1
            omega
          · apply had; omega
        · have hz : ((a:ℤ)+b)*((a:ℤ)-c)=0 := by nlinarith
          rcases mul_eq_zero.mp hz with hz | hz
          · have ha0 := (carrier_bounds (hsub ha)).1
            omega
          · apply hac; omega
    left
    rw [he']
    simp only [image_insert, image_singleton, ← ho, insert_idem]
    simp [hoc, hod, hcod]


def triple (t : (ℕ × ℕ) × ℕ) : Finset ℕ := {t.1.1, t.1.2, t.2}

def apEdges (s : ℕ) : Finset (Finset ℕ) :=
  ((squareAPs s).image triple).filter (fun e => e ⊆ carrier s)

def project (s : ℕ) (e : Finset ℕ) : Finset ℕ := e.image (orbit s)

noncomputable def projected (s : ℕ) : Finset (Finset ℕ) :=
  (apEdges s).image (project s) ∪ (edges (carrier s)).image (project s)

lemma ap_card_le (s : ℕ) : (apEdges s).card ≤ (squareAPs s).card :=
  (card_filter_le _ _).trans card_image_le

lemma ap_project_card {s : ℕ} {e : Finset ℕ} (he : e ∈ apEdges s) :
    2 ≤ (project s e).card := by
  obtain ⟨het, hsub⟩ := mem_filter.mp he
  obtain ⟨⟨⟨a,b⟩,c⟩, ht, rfl⟩ := mem_image.mp het
  obtain ⟨_, hab, hbc, heq⟩ := mem_filter.mp ht
  dsimp only at hab hbc heq
  have ha : a ∈ carrier s := hsub (by simp [triple])
  have hb : b ∈ carrier s := hsub (by simp [triple])
  have hc : c ∈ carrier s := hsub (by simp [triple])
  have haS := (carrier_bounds ha).2.1.le
  have hbS := (carrier_bounds hb).2.1.le
  have hcS := (carrier_bounds hc).2.1.le
  change 1 < (project s (triple ((a,b),c))).card
  by_cases ho : orbit s a = orbit s b
  · have habS : a + b = s := ((orbit_eq_iff haS hbS).mp ho).resolve_left hab.ne
    have hne : orbit s a ≠ orbit s c := by
      intro hh
      rcases (orbit_eq_iff haS hcS).mp hh with hh | hh <;> omega
    exact one_lt_card.mpr ⟨orbit s a, by simp [project,triple],
      orbit s c, by simp [project,triple], hne⟩
  · exact one_lt_card.mpr ⟨orbit s a, by simp [project,triple],
      orbit s b, by simp [project,triple], ho⟩

lemma ap_mem {s a b c : ℕ} (ha : a ∈ carrier s) (hb : b ∈ carrier s)
    (hc : c ∈ carrier s) (he : a^2+c^2=2*b^2) (hne : a ≠ c) :
    ({a,b,c} : Finset ℕ) ∈ apEdges s := by
  apply mem_filter.mpr
  refine ⟨?_, by simpa only [insert_subset_iff, singleton_subset_iff] using ⟨ha,hb,hc⟩⟩
  have hsort {a b c : ℕ} (ha : a ∈ carrier s) (hb : b ∈ carrier s)
      (hc : c ∈ carrier s) (hac : a < c) (he : a^2+c^2=2*b^2) :
      ({a,b,c} : Finset ℕ) ∈ (squareAPs s).image triple := by
    have hab : a < b := by nlinarith
    have hbc : b < c := by nlinarith
    refine mem_image.mpr ⟨((a,b),c), ?_, rfl⟩
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_product.mpr
      ⟨carrier_subset s ha, carrier_subset s hb⟩, carrier_subset s hc⟩, hab, hbc, he⟩
  rcases lt_or_gt_of_ne hne with hh | hh
  · exact hsort ha hb hc hh he
  · have hh := hsort hc hb ha hh (by omega)
    convert hh using 1
    ext x
    simp only [mem_insert, mem_singleton]
    tauto

lemma projected_subsets (s : ℕ) : ∀ e ∈ projected s, e ⊆ labels s := by
  classical
  intro e he
  rcases mem_union.mp he with he | he
  · obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    have hsub := (mem_filter.mp hf).2
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    exact orbit_carrier (hsub hb)
  · obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    have hsub := mem_powerset.mp (mem_filter.mp hf).1
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    exact orbit_carrier (hsub hb)

lemma projected_nonempty (s : ℕ) : ∀ e ∈ projected s, e.Nonempty := by
  classical
  intro e he
  apply card_pos.mp
  rcases mem_union.mp he with he | he
  · obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    have hh := ap_project_card hf
    omega
  · obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    have hh := edge_orbit_card hf
    change 0 < (f.image (orbit s)).card
    omega

lemma sidon_of_avoid {s : ℕ} {B : Finset ℕ} (hB : B ⊆ labels s)
    (havoid : ∀ e ∈ projected s, ¬ e ⊆ B) :
    IsSidon (((closure s B).image (fun n => n^2)) : Set ℕ) := by
  classical
  have hav (e : Finset ℕ) (he : e ∈ apEdges s ∨ e ∈ edges (carrier s)) :
      ¬ e ⊆ closure s B := by
    intro hsub
    have hp : project s e ∈ projected s := by
      rcases he with he | he
      · exact mem_union_left _ (mem_image.mpr ⟨e,he,rfl⟩)
      · exact mem_union_right _ (mem_image.mpr ⟨e,he,rfl⟩)
    apply havoid _ hp
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    exact (mem_closure_iff hB (closure_subset hB (hsub hb))).mp (hsub hb)
  intro aa haa cc hcc bb hbb dd hdd he
  obtain ⟨a, ha, rfl⟩ := mem_image.mp haa
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hcc
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hbb
  obtain ⟨d, hd, rfl⟩ := mem_image.mp hdd
  have haA := closure_subset hB ha
  have hbA := closure_subset hB hb
  have hcA := closure_subset hB hc
  have hdA := closure_subset hB hd
  by_cases hac : a = c
  · left
    subst c
    exact ⟨rfl, by omega⟩
  by_cases had : a = d
  · right
    subst d
    exact ⟨rfl, by omega⟩
  have hbc : b ≠ c := by
    intro hh
    subst c
    apply had
    nlinarith
  have hbd : b ≠ d := by
    intro hh
    subst d
    apply hac
    nlinarith
  by_cases hab : a = b
  · have hcd : c ≠ d := by
      intro hh
      subst d
      apply hac
      nlinarith
    have hAP := ap_mem hcA haA hdA (by rw [hab] at he ⊢; omega) hcd
    exact (hav {c,a,d} (Or.inl hAP) (by simpa only [insert_subset_iff, singleton_subset_iff] using ⟨hc,ha,hd⟩)).elim
  by_cases hcd : c = d
  · have hAP := ap_mem haA hcA hbA (by rw [hcd] at he ⊢; omega) hab
    exact (hav {a,c,b} (Or.inl hAP) (by simpa only [insert_subset_iff, singleton_subset_iff] using ⟨ha,hc,hb⟩)).elim
  have hE : ({a,b,c,d} : Finset ℕ) ∈ edges (carrier s) := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (by simpa only [insert_subset_iff, singleton_subset_iff] using ⟨haA,hbA,hcA,hdA⟩), ?_, a,b,c,d,rfl,he⟩
    simp [hab,hac,had,hbc,hbd,hcd]
  exact (hav {a,b,c,d} (Or.inr hE) (by simpa only [insert_subset_iff, singleton_subset_iff] using ⟨ha,hb,hc,hd⟩)).elim

noncomputable def collapsed (s : ℕ) : Finset (Finset ℕ) :=
  (edges (carrier s)).filter (fun e => (project s e).card = 3)

lemma collapsed_card {s : ℕ} (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ a ∈ Icc 1 s, ∀ b ∈ Icc 1 s, a ≠ b →
      ((pairEdges (Icc 1 s) a b).card : ℝ) ≤ K) :
    ((collapsed s).card : ℝ) ≤ s * K := by
  classical
  let F (a : ℕ) := if a = s-a then ∅ else pairEdges (Icc 1 s) a (s-a)
  have hcover : collapsed s ⊆ (Icc 1 s).biUnion F := by
    intro e he
    obtain ⟨he, h3⟩ := mem_filter.mp he
    have h4 := (mem_filter.mp he).2.1
    have hsub := mem_powerset.mp (mem_filter.mp he).1
    obtain ⟨a,ha,b,hb,hab,ho⟩ := exists_ne_map_eq_of_card_image_lt
      (show (e.image (orbit s)).card < e.card by change (project s e).card < e.card; omega)
    have haA := hsub ha
    have hbA := hsub hb
    have haS := (carrier_bounds haA).2.1.le
    have hbS := (carrier_bounds hbA).2.1.le
    have hsum : a+b=s := ((orbit_eq_iff haS hbS).mp ho).resolve_left hab
    have hb' : b=s-a := by omega
    apply mem_biUnion.mpr
    refine ⟨a, carrier_subset s haA, ?_⟩
    dsimp [F]
    rw [if_neg (by omega : a ≠ s-a)]
    exact mem_filter.mpr ⟨edges_mono (carrier_subset s) he, ha, hb' ▸ hb⟩
  have hcard := (card_le_card hcover).trans (card_biUnion_le (s := Icc 1 s) (t := F))
  calc
    _ ≤ ∑ a ∈ Icc 1 s, ((F a).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _a ∈ Icc 1 s, K := by
      apply sum_le_sum
      intro a ha
      dsimp [F]
      split_ifs with hh
      · simpa using hK0
      · by_cases hb : s-a ∈ Icc 1 s
        · exact hK a ha (s-a) hb hh
        · have he : pairEdges (Icc 1 s) a (s-a) = ∅ := by
            apply eq_empty_iff_forall_notMem.mpr
            intro e he
            have he' := mem_filter.mp he
            exact hb ((mem_powerset.mp (mem_filter.mp he'.1).1) he'.2.2)
          simp [he, hK0]
    _ = _ := by simp

lemma projected_cost {s : ℕ} (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ a ∈ Icc 1 s, ∀ b ∈ Icc 1 s, a ≠ b →
      ((pairEdges (Icc 1 s) a b).card : ℝ) ≤ K)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ e ∈ projected s, p^e.card) ≤
      p^2*(squareAPs s).card + p^3*s*K + p^4*(s:ℝ)^2*K := by
  classical
  have hapcard : ((apEdges s).card : ℝ) ≤ (squareAPs s).card := by
    exact_mod_cast ap_card_le s
  have hAP : (∑ e ∈ (apEdges s).image (project s), p^e.card) ≤ p^2*(squareAPs s).card := by
    calc
      _ ≤ ∑ e ∈ apEdges s, p^(project s e).card :=
        sum_image_le_of_nonneg (g := project s) (f := fun e : Finset ℕ => p^e.card) (fun _ _ => by positivity)
      _ ≤ ∑ _e ∈ apEdges s, p^2 := by
        apply sum_le_sum
        intro e he
        exact pow_le_pow_of_le_one hp hp1 (ap_project_card he)
      _ = p^2*(apEdges s).card := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hapcard (sq_nonneg p)
  have hE : (∑ e ∈ (edges (carrier s)).image (project s), p^e.card) ≤
      p^3*s*K + p^4*(s:ℝ)^2*K := by
    have hterm (e : Finset ℕ) (he : e ∈ edges (carrier s)) :
        p^(project s e).card ≤ (if (project s e).card=3 then p^3 else 0) + p^4 := by
      rcases edge_orbit_card he with hh | hh
      · change (project s e).card = 3 at hh
        rw [hh, if_pos rfl]
        have : 0 ≤ p^4 := by positivity
        linarith
      · change (project s e).card = 4 at hh
        simp [hh]
    have hcount : ((edges (carrier s)).card : ℝ) ≤ (s:ℝ)^2*K := by
      have hc : ((edges (carrier s)).card : ℝ) ≤ (edges (Icc 1 s)).card := by
        exact_mod_cast card_le_card (edges_mono (carrier_subset s))
      exact hc.trans (ControlledSquareLinearization.edges_card_le K hK0 hK)
    calc
      _ ≤ ∑ e ∈ edges (carrier s), p^(project s e).card :=
        sum_image_le_of_nonneg (g := project s) (f := fun e : Finset ℕ => p^e.card) (fun _ _ => by positivity)
      _ ≤ ∑ e ∈ edges (carrier s), ((if (project s e).card=3 then p^3 else 0) + p^4) :=
        sum_le_sum hterm
      _ = p^3*(collapsed s).card + p^4*(edges (carrier s)).card := by
        rw [sum_add_distrib, ← sum_filter]
        simp [collapsed, mul_comm]
      _ ≤ p^3*(s*K) + p^4*((s:ℝ)^2*K) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (collapsed_card K hK0 hK) (by positivity))
          (mul_le_mul_of_nonneg_left hcount (by positivity))
      _ = _ := by ring
  have hu : (∑ e ∈ projected s, p^e.card) ≤
      (∑ e ∈ (apEdges s).image (project s), p^e.card) +
      ∑ e ∈ (edges (carrier s)).image (project s), p^e.card := by
    have hid := sum_union_inter
      (s₁ := (apEdges s).image (project s))
      (s₂ := (edges (carrier s)).image (project s))
      (f := fun e : Finset ℕ => p^e.card)
    have hn : 0 ≤ ∑ e ∈ (apEdges s).image (project s) ∩
        (edges (carrier s)).image (project s), p^e.card :=
      sum_nonneg (fun _ _ => pow_nonneg hp _)
    change (∑ e ∈ (apEdges s).image (project s) ∪
      (edges (carrier s)).image (project s), p^e.card) ≤ _
    linarith only [hid,hn]
  exact hu.trans (by linarith)

/-- The selection is symmetric from the outset. No prime-center hypothesis
is required: four distinct roots in two reflection orbits cannot collide. -/
theorem finite_selection (s : ℕ) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ a ∈ Icc 1 s, ∀ b ∈ Icc 1 s, a ≠ b →
      ((pairEdges (Icc 1 s) a b).card : ℝ) ≤ K)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ C ⊆ Icc 1 s,
      (∀ a ∈ C, a ≤ s ∧ s-a ∈ C) ∧
      IsSidon ((C.image (fun n => n^2)) : Set ℕ) ∧
      2*(p*(labels s).card - p^2*(squareAPs s).card - p^3*s*K - p^4*(s:ℝ)^2*K)
        ≤ (C.card : ℝ) := by
  obtain ⟨B,hB,havoid,hcard⟩ := HypergraphLinearization.ambient_alteration
    (labels s) (projected s) (projected_subsets s) (projected_nonempty s) p hp hp1
  refine ⟨closure s B, (closure_subset hB).trans (carrier_subset s),
    closure_symmetric hB, sidon_of_avoid hB havoid, ?_⟩
  have hcost := projected_cost K hK0 hK p hp hp1
  rw [closure_card hB]
  push_cast
  linarith

lemma eventually_ap_bound (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ s : ℕ in atTop, ((squareAPs s).card : ℝ) ≤ (s : ℝ)^(1+δ) := by
  obtain ⟨C,hC,hbound⟩ := squareAPs_subpower (δ/4) (by positivity)
  have hg : ∀ᶠ s : ℕ in atTop, C ≤ (s : ℝ)^(δ/2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < δ/2)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun s : ℕ => (s : ℝ)) atTop atTop)).eventually_ge_atTop C
  filter_upwards [hg,eventually_ge_atTop 1] with s hs hs1
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  calc
    _ ≤ C*(s : ℝ)^(1+2*(δ/4)) := hbound s
    _ ≤ (s : ℝ)^(δ/2)*(s : ℝ)^(1+2*(δ/4)) :=
      mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hs0.le _)
    _ = _ := by rw [← Real.rpow_add hs0]; congr 1; ring

lemma labels_card_lower {s : ℕ} (hs : 4 ≤ s) : (s : ℝ)/4 ≤ (labels s).card := by
  have hc : (labels s).card = (s-1)/2 := by simp [labels]
  have hi : s ≤ 4*((s-1)/2) := by omega
  rw [hc]
  have hi' : (s : ℝ) ≤ 4 * (((s-1)/2 : ℕ) : ℝ) := by exact_mod_cast hi
  linarith only [hi']

/-- For every integer reflection center parameter, symmetric square-Sidon
sets attain the same subcritical two-thirds exponent as ordinary alteration.
This is not a near-linear construction. -/
theorem eventual_symmetric_lower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℕ in atTop, ∃ C ⊆ Icc 1 s,
      (∀ a ∈ C, a ≤ s ∧ s-a ∈ C) ∧
      IsSidon ((C.image (fun n => n^2)) : Set ℕ) ∧
      (s : ℝ)^(2/3-ε) ≤ (C.card : ℝ) := by
  let δ : ℝ := ε/8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have ht (r : ℝ) (hr : 0 < r) :
      Tendsto (fun s : ℕ => (s : ℝ)^(-r)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hr).comp tendsto_natCast_atTop_atTop
  have hb1 := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1/24)
    (ht (1/3) (by norm_num))
  have hb2 := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1/24)
    (ht (2/3+δ) (by linarith))
  have hb3 := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1/24)
    (ht (2*δ) (by positivity))
  have hb4 := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1/4)
    (ht (ε-δ) (by dsimp [δ]; linarith))
  filter_upwards [eventually_pair_codegree_bound δ hδ, eventually_ap_bound δ hδ,
    hb1,hb2,hb3,hb4,eventually_ge_atTop 4] with s hcodeg hAP hb1 hb2 hb3 hb4 hs4
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hs0 : (0 : ℝ) < s := by linarith
  let p : ℝ := (s : ℝ)^(-1/3-δ)
  let K : ℝ := (s : ℝ)^δ
  let S : ℝ := (s : ℝ)^(2/3-δ)
  have hp : 0 ≤ p := Real.rpow_nonneg hs0.le _
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs1 (by linarith)
  have hK : 0 ≤ K := Real.rpow_nonneg hs0.le _
  have hS : 0 ≤ S := Real.rpow_nonneg hs0.le _
  obtain ⟨C,hC,hSym,hSid,hcard⟩ := finite_selection s K hK hcodeg p hp hp1
  refine ⟨C,hC,hSym,hSid,?_⟩
  have hprod : p*(s : ℝ) = S := by
    dsimp [p,S]
    conv_lhs => rhs; rw [← Real.rpow_one (s : ℝ)]
    rw [← Real.rpow_add hs0]
    congr 1
    ring
  have hlead : S/4 ≤ p*(labels s).card := by
    have hh := mul_le_mul_of_nonneg_left (labels_card_lower hs4) hp
    rw [← mul_div_assoc, hprod] at hh
    exact hh
  have hc1 : p^2*(s : ℝ)^(1+δ) = S*(s : ℝ)^(-(1/3 : ℝ)) := by
    dsimp [p,S]
    rw [← Real.rpow_mul_natCast hs0.le, ← Real.rpow_add hs0, ← Real.rpow_add hs0]
    congr 1
    norm_num
    ring
  have hc2 : p^3*s*K = S*(s : ℝ)^(-(2/3+δ)) := by
    dsimp [p,K,S]
    conv_lhs => lhs; rhs; rw [← Real.rpow_one (s : ℝ)]
    rw [← Real.rpow_mul_natCast hs0.le, ← Real.rpow_add hs0,
      ← Real.rpow_add hs0, ← Real.rpow_add hs0]
    congr 1
    norm_num
    ring
  have hc3 : p^4*(s : ℝ)^2*K = S*(s : ℝ)^(-(2*δ)) := by
    dsimp [p,K,S]
    rw [← Real.rpow_mul_natCast hs0.le, ← Real.rpow_natCast (s : ℝ) 2,
      ← Real.rpow_add hs0, ← Real.rpow_add hs0, ← Real.rpow_add hs0]
    congr 1
    norm_num
    ring
  have hcost1 : p^2*(squareAPs s).card ≤ S/24 := by
    calc
      _ ≤ p^2*(s : ℝ)^(1+δ) := mul_le_mul_of_nonneg_left hAP (sq_nonneg p)
      _ = S*(s : ℝ)^(-(1/3 : ℝ)) := hc1
      _ ≤ S*(1/24) := mul_le_mul_of_nonneg_left hb1 hS
      _ = _ := by ring
  have hcost2 : p^3*s*K ≤ S/24 := by
    rw [hc2]
    have hh := mul_le_mul_of_nonneg_left hb2 hS
    linarith only [hh]
  have hcost3 : p^4*(s : ℝ)^2*K ≤ S/24 := by
    rw [hc3]
    have hh := mul_le_mul_of_nonneg_left hb3 hS
    linarith only [hh]
  have hmain : S/4 ≤ (C.card : ℝ) := by
    linarith only [hcard,hlead,hcost1,hcost2,hcost3]
  have htarget : (s : ℝ)^(2/3-ε) = S*(s : ℝ)^(-(ε-δ)) := by
    dsimp [S]
    rw [← Real.rpow_add hs0]
    congr 1
    ring
  rw [htarget]
  have hh := mul_le_mul_of_nonneg_left hb4 hS
  linarith only [hh,hmain]

end Erdos773.SymmetricSquareAlteration

#print axioms Erdos773.SymmetricSquareAlteration.edge_orbit_card
#print axioms Erdos773.SymmetricSquareAlteration.sidon_of_avoid
#print axioms Erdos773.SymmetricSquareAlteration.collapsed_card
#print axioms Erdos773.SymmetricSquareAlteration.finite_selection
#print axioms Erdos773.SymmetricSquareAlteration.eventual_symmetric_lower
