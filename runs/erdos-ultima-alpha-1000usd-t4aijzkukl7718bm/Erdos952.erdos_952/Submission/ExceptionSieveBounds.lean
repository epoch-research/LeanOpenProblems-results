import Submission.HalfPlaneSieveComponents

/-! Explicit finite-prefix tests for exception-retaining sieves. A finite
component cannot wander arbitrarily far into a periodic half-plane. This
makes each cutoff criterion finite, but does not supply a cutoff for all C. -/
namespace Erdos952Investigation
namespace ExceptionSieveBounds
open FiniteSieveReduction PeriodicSieveComponents ExceptionSieveReduction
open HalfPlaneSieveComponents
set_option maxHeartbeats 0

lemma halfGraph_le_candidate {C : ℤ} {N : ℕ} {l : GaussianInt →+ ℤ} {R : ℤ}
    (hlarge : ∀ z, R ≤ l z → (N : ℤ)^2 < z.norm) :
    halfGraph C N l R ≤ candidateGraph C N := by
  intro z w h
  exact ⟨(candidate_iff_allowed_of_large (hlarge z h.2.1)).mpr h.1.1,
    (candidate_iff_allowed_of_large (hlarge w h.2.2)).mpr h.1.2.1,h.1.2.2⟩

lemma candidate_adj_halfGraph {C : ℤ} {N : ℕ} {l : GaussianInt →+ ℤ} {R : ℤ}
    (hlarge : ∀ z, R ≤ l z → (N : ℤ)^2 < z.norm)
    {z w : GaussianInt} (h : (candidateGraph C N).Adj z w)
    (hz : R ≤ l z) (hw : R ≤ l w) : (halfGraph C N l R).Adj z w := by
  exact ⟨⟨(candidate_iff_allowed_of_large (hlarge z hz)).mp h.1,
    (candidate_iff_allowed_of_large (hlarge w hw)).mp h.2.1,h.2.2⟩,hz,hw⟩

/-- Entry into the last half-plane segment of a walk occurs either at its
initial vertex or immediately after an edge from below the half-plane. -/
lemma halfplane_entry {C : ℤ} {N : ℕ} {l : GaussianInt →+ ℤ} {R : ℤ}
    (hlarge : ∀ z, R ≤ l z → (N : ℤ)^2 < z.norm)
    {z w : GaussianInt} (p : (candidateGraph C N).Walk z w) :
    R ≤ l w → ∃ u, R ≤ l u ∧ (halfGraph C N l R).Reachable u w ∧
      (u = z ∨ ∃ v, (candidateGraph C N).Adj v u ∧ l v < R) := by
  induction p with
  | nil => exact fun hw => ⟨_,hw,SimpleGraph.Reachable.refl _,Or.inl rfl⟩
  | @cons z v w hzv p ih =>
    intro hw
    obtain ⟨u,hu,hr,he⟩ := ih hw
    rcases he with rfl | he
    · by_cases hz : R ≤ l z
      · exact ⟨z,hz,(candidate_adj_halfGraph hlarge hzv hz hu).reachable.trans hr,Or.inl rfl⟩
      · exact ⟨_,hu,hr,Or.inr ⟨z,hzv,lt_of_not_ge hz⟩⟩
    · exact ⟨u,hu,hr,Or.inr he⟩

lemma finite_component_projection_bound {C : ℤ} {N : ℕ} {l : GaussianInt →+ ℤ}
    {R D : ℤ} (hD : 0 ≤ D)
    (hlarge : ∀ z, R ≤ l z → (N : ℤ)^2 < z.norm)
    (hs : ∀ z w, (w-z).norm < C → l w-l z ≤ D)
    {z w : GaussianInt}
    (hf : {v | (candidateGraph C N).Reachable z v}.Finite)
    (hw : (candidateGraph C N).Reachable z w) :
    l w ≤ max (l z) R+D*((N.factorial^2 : ℕ)+1) := by
  by_cases hwR : R ≤ l w
  · obtain ⟨p⟩ := hw
    obtain ⟨u,hu,hr,he⟩ := halfplane_entry hlarge p hwR
    have hhalf : {v | (halfGraph C N l R).Reachable u v}.Finite := by
      apply hf.subset
      intro v hv
      exact p.reachable.trans ((hr.symm.trans hv).mono (halfGraph_le_candidate hlarge))
    have hd := HalfPlaneSieveComponents.finite_component_projection_bound hD
      (fun {a b} hab => hs a b hab.2.2.2) hhalf hr
    have huBound : l u ≤ max (l z) R+D := by
      rcases he with rfl | ⟨v,hvu,hv⟩
      · exact le_add_of_le_of_nonneg (le_max_left _ _) hD
      · have hh := hs v u hvu.2.2.2
        have hm : R ≤ max (l z) R := le_max_right _ _
        omega
    nlinarith
  · have hm : R ≤ max (l z) R := le_max_right _ _
    have hmul : 0 ≤ D*((N.factorial^2 : ℕ)+1 : ℤ) := by positivity
    omega

def reHom : GaussianInt →+ ℤ where
  toFun z := z.re
  map_zero' := rfl
  map_add' _ _ := rfl

def imHom : GaussianInt →+ ℤ where
  toFun z := z.im
  map_zero' := rfl
  map_add' _ _ := rfl

def coordinate : Fin 4 → GaussianInt →+ ℤ := ![reHom,-reHom,imHom,-imHom]

lemma coordinate_sq_le_norm (i : Fin 4) (z : GaussianInt) :
    (coordinate i z)^2 ≤ z.norm := by
  fin_cases i <;> simp [coordinate,reHom,imHom,gaussian_norm_sq] <;>
    nlinarith [sq_nonneg z.re,sq_nonneg z.im]

lemma coordinate_abs_le_norm (i : Fin 4) (z : GaussianInt) :
    |coordinate i z| ≤ z.norm := by
  have hh := coordinate_sq_le_norm i z
  have hs := Int.le_self_sq |coordinate i z|
  nlinarith [sq_abs (coordinate i z)]

lemma coordinate_large (N : ℕ) (i : Fin 4) (z : GaussianInt)
    (hz : (N : ℤ)+1 ≤ coordinate i z) : (N : ℤ)^2 < z.norm := by
  have hs := coordinate_sq_le_norm i z
  have hN := Int.natCast_nonneg N
  nlinarith

lemma coordinate_step (C : ℤ) (i : Fin 4) (z w : GaussianInt)
    (hs : (w-z).norm < C) : coordinate i w-coordinate i z ≤ max C 1 := by
  calc
    _ = coordinate i (w-z) := (map_sub (coordinate i) w z).symm
    _ ≤ |coordinate i (w-z)| := le_abs_self _
    _ ≤ (w-z).norm := coordinate_abs_le_norm _ _
    _ ≤ max C 1 := hs.le.trans (le_max_left _ _)

def radiusBound (C : ℤ) (N : ℕ) (z : GaussianInt) : ℤ :=
  max z.norm ((N : ℤ)+1)+max C 1*((N.factorial : ℤ)^2+1)

lemma radiusBound_nonneg (C : ℤ) (N : ℕ) (z : GaussianInt) :
    0 ≤ radiusBound C N z := by
  have hn := GaussianInt.norm_nonneg z
  have hD : 0 ≤ max C 1 := (by norm_num : (0 : ℤ) ≤ 1).trans (le_max_right _ _)
  unfold radiusBound
  positivity

lemma finite_component_coordinate_bound (C : ℤ) (N : ℕ) (z : GaussianInt)
    (hf : {v | (candidateGraph C N).Reachable z v}.Finite)
    {w : GaussianInt} (hw : (candidateGraph C N).Reachable z w) (i : Fin 4) :
    coordinate i w ≤ radiusBound C N z := by
  have hD : 0 ≤ max C 1 := (by norm_num : (0 : ℤ) ≤ 1).trans (le_max_right _ _)
  have hh := finite_component_projection_bound hD (coordinate_large N i)
    (coordinate_step C i) hf hw
  have hz : coordinate i z ≤ z.norm := (le_abs_self _).trans (coordinate_abs_le_norm i z)
  have hm := max_le_max_right ((N : ℤ)+1) hz
  dsimp [radiusBound]
  push_cast at hh
  exact hh.trans (add_le_add hm le_rfl)

lemma finite_component_box_bound (C : ℤ) (N : ℕ) (z : GaussianInt)
    (hf : {v | (candidateGraph C N).Reachable z v}.Finite)
    {w : GaussianInt} (hw : (candidateGraph C N).Reachable z w) :
    -(radiusBound C N z) ≤ w.re ∧ w.re ≤ radiusBound C N z ∧
      -(radiusBound C N z) ≤ w.im ∧ w.im ≤ radiusBound C N z := by
  have h0 := finite_component_coordinate_bound C N z hf hw 0
  have h1 := finite_component_coordinate_bound C N z hf hw 1
  have h2 := finite_component_coordinate_bound C N z hf hw 2
  have h3 := finite_component_coordinate_bound C N z hf hw 3
  change w.re ≤ radiusBound C N z at h0
  change -w.re ≤ radiusBound C N z at h1
  change w.im ≤ radiusBound C N z at h2
  change -w.im ≤ radiusBound C N z at h3
  exact ⟨by omega,h0,by omega,h2⟩

def prefixBound (C : ℤ) (N : ℕ) (z : GaussianInt) : ℕ :=
  (2*(radiusBound C N z).toNat+1)^2

/-- Explicit cardinality bound for finite components of the graph with its
small-prime exceptions. No bound of this form is claimed for primeGraph. -/
theorem finite_component_card_le (C : ℤ) (N : ℕ) (z : GaussianInt)
    (hf : {w | (candidateGraph C N).Reachable z w}.Finite) :
    Nat.card {w | (candidateGraph C N).Reachable z w} ≤ prefixBound C N z := by
  let B := (radiusBound C N z).toNat
  have hB : (B : ℤ) = radiusBound C N z := Int.toNat_of_nonneg (radiusBound_nonneg C N z)
  let f : {w | (candidateGraph C N).Reachable z w} →
      Fin (2*B+1) × Fin (2*B+1) := fun w =>
    (⟨(w.val.re+(B : ℤ)).toNat,by
      have hh := finite_component_box_bound C N z hf w.property; omega⟩,
     ⟨(w.val.im+(B : ℤ)).toNat,by
      have hh := finite_component_box_bound C N z hf w.property; omega⟩)
  have hfi : Function.Injective f := by
    intro u v he
    have hu := finite_component_box_bound C N z hf u.property
    have hv := finite_component_box_bound C N z hf v.property
    have hr := congrArg (fun t => t.1.val) he
    have hi := congrArg (fun t => t.2.val) he
    dsimp [f] at hr hi
    apply Subtype.ext
    apply Zsqrtd.ext <;> omega
  have hc := Nat.card_le_card_of_injective f hfi
  simpa only [Nat.card_prod,Nat.card_fin,prefixBound,← pow_two,B] using hc

/-- Infinitude for a fixed cutoff is detected by one finite simple path of a
fully specified length. This does not assert that cutoff search terminates. -/
theorem infinite_component_iff_long_prefix (C : ℤ) (N : ℕ) (z : GaussianInt) :
    {w | (candidateGraph C N).Reachable z w}.Infinite ↔
      Nonempty (RayReduction.Prefix (candidateGraph C N) z (prefixBound C N z)) := by
  constructor
  · intro h
    exact RayReduction.prefixes_of_infinite_component (candidateGraph C N) z h _
  · rintro ⟨f⟩ hf
    let S := {w | (candidateGraph C N).Reachable z w}
    letI : Finite S := hf
    let g : Fin (prefixBound C N z+1) → S := fun i => ⟨f.val i,prefix_reachable f i⟩
    have hgi : Function.Injective g := by
      intro i j he
      exact f.property.2.1 (congrArg Subtype.val he)
    have hl := Nat.card_le_card_of_injective g hgi
    have hu := finite_component_card_le C N z hf
    simp only [Nat.card_fin] at hl
    change prefixBound C N z+1 ≤ Nat.card {w | (candidateGraph C N).Reachable z w} at hl
    omega

/-- An exact finite-prefix reformulation of the original negation, preserving
small-prime exceptions instead of imposing the stronger uniform-sieve goal. -/
theorem negation_iff_bounded_prefix_obstruction :
    (¬ ∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) ↔
    ∀ C : ℤ, ∃ N : ℕ,
      IsEmpty (RayReduction.Prefix (candidateGraph C N) (3 : GaussianInt)
        (prefixBound C N 3)) := by
  rw [negation_iff_seed_cutoffs]
  apply forall_congr'
  intro C
  apply exists_congr
  intro N
  have hh := not_congr (infinite_component_iff_long_prefix C N 3)
  simpa only [Set.not_infinite,not_nonempty_iff] using hh

#print axioms finite_component_box_bound
#print axioms finite_component_card_le
#print axioms infinite_component_iff_long_prefix
#print axioms negation_iff_bounded_prefix_obstruction

end ExceptionSieveBounds
end Erdos952Investigation
