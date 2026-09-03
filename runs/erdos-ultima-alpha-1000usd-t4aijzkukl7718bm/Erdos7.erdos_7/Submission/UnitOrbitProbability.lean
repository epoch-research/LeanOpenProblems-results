import FormalConjecturesUtil

/-! Exact finite group orbit-meeting probabilities. These are auxiliary
identities, not a small collision budget for arbitrary odd covers. -/
namespace Erdos7UnitOrbitProbability
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

variable {G H K L : Type*} [Group G] [Group H] [Group K] [Group L]

lemma card_mul_relIndex {A B : Subgroup G} (h : A ≤ B) :
    Nat.card A * A.relIndex B = Nat.card B := by
  simpa only [Subgroup.relIndex_bot_left] using
    Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) A B bot_le h

lemma card_inf_mul_card_sup (A B : Subgroup G) [B.Normal] :
    Nat.card ↥(A ⊓ B) * Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have ha := card_mul_relIndex (show A ⊓ B ≤ A from inf_le_left)
  have hb := card_mul_relIndex (show B ≤ A ⊔ B from le_sup_right)
  rw [Subgroup.inf_relIndex_left] at ha
  rw [Subgroup.relIndex_sup_right] at hb
  calc
    Nat.card ↥(A ⊓ B) * Nat.card ↥(A ⊔ B) =
        Nat.card ↥(A ⊓ B) * (Nat.card B * B.relIndex A) := by rw [hb]
    _ = (Nat.card ↥(A ⊓ B) * B.relIndex A) * Nat.card B := by ring
    _ = Nat.card A * Nat.card B := by rw [ha]

lemma card_comap_cross (f : G →* H) (hf : Function.Surjective f) (S : Subgroup H) :
    Nat.card (S.comap f) * Nat.card H = Nat.card S * Nat.card G := by
  have ha := card_mul_relIndex (S.ker_le_comap f)
  rw [Subgroup.relIndex_ker, Subgroup.map_comap_eq_self_of_surjective hf] at ha
  have hb := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf, Subgroup.card_top] at hb
  calc
    Nat.card (S.comap f) * Nat.card H =
        (Nat.card f.ker * Nat.card S) * Nat.card H := by rw [ha]
    _ = Nat.card S * (Nat.card f.ker * Nat.card H) := by ring
    _ = Nat.card S * Nat.card G := by rw [hb]

/-- The subgroup of translates whose orbit meets the identity fiber. -/
def meetingSubgroup (f : G →* H) (u : G) : Subgroup G :=
  (Subgroup.zpowers (f u)).comap f

def Meets (f : G →* H) (u : G) (a : H) (v : G) : Prop :=
  ∃ n : ℤ, f (v*u^n) = a

lemma meets_iff (f : G →* H) (u : G) (a : H) (v : G) :
    Meets f u a v ↔ (f v)⁻¹*a ∈ Subgroup.zpowers (f u) := by
  simp only [Meets, map_mul, map_zpow, ← eq_inv_mul_iff_mul_eq,
    Subgroup.mem_zpowers_iff]

lemma meetingSubgroup_eq (f : G →* H) (u : G) :
    meetingSubgroup f u = Subgroup.zpowers u ⊔ f.ker := by
  rw [meetingSubgroup, ← MonoidHom.map_zpowers, Subgroup.comap_map_eq]

/-- Once one point of a meeting set is known, the whole meeting set is its
coset of the meeting subgroup. No independence assumption is involved. -/
lemma meets_relative (f : G →* H) (u z : G) (a : H) (hz : Meets f u a z) (v : G) :
    Meets f u a v ↔ z⁻¹*v ∈ meetingSubgroup f u := by
  rw [meets_iff] at hz ⊢
  change _ ↔ f (z⁻¹*v) ∈ Subgroup.zpowers (f u)
  rw [map_mul, map_inv]
  constructor
  · intro hv
    have ht := (Subgroup.zpowers (f u)).mul_mem hz ((Subgroup.zpowers (f u)).inv_mem hv)
    convert ht using 1 <;> group
  · intro hv
    have ht := (Subgroup.zpowers (f u)).mul_mem ((Subgroup.zpowers (f u)).inv_mem hv) hz
    convert ht using 1 <;> group

/-- Intersection of two nonempty meeting cosets is a coset of the
intersection subgroup. -/
def pairEquiv (f : G →* H) (g : G →* K) (u z : G) (a : H) (b : K)
    (hf : Meets f u a z) (hg : Meets g u b z) :
    {v : G // Meets f u a v ∧ Meets g u b v} ≃
      ↥(meetingSubgroup f u ⊓ meetingSubgroup g u) where
  toFun v := ⟨z⁻¹*v.val,
    (meets_relative f u z a hf v.val).mp v.property.1,
    (meets_relative g u z b hg v.val).mp v.property.2⟩
  invFun v := ⟨z*v.val,
    (meets_relative f u z a hf (z*v.val)).mpr (by simpa using v.property.1),
    (meets_relative g u z b hg (z*v.val)).mpr (by simpa using v.property.2)⟩
  left_inv v := by apply Subtype.ext; simp
  right_inv v := by apply Subtype.ext; simp

lemma pair_card (f : G →* H) (g : G →* K) (u z : G) (a : H) (b : K)
    (hf : Meets f u a z) (hg : Meets g u b z) :
    Nat.card {v : G // Meets f u a v ∧ Meets g u b v} =
      Nat.card ↥(meetingSubgroup f u ⊓ meetingSubgroup g u) :=
  Nat.card_congr (pairEquiv f g u z a b hf hg)

/-- A single nonempty meeting set is a coset of its meeting subgroup. -/
def singleEquiv (f : G →* H) (u z : G) (a : H) (hz : Meets f u a z) :
    {v : G // Meets f u a v} ≃ ↥(meetingSubgroup f u) where
  toFun v := ⟨z⁻¹*v.val, (meets_relative f u z a hz v.val).mp v.property⟩
  invFun v := ⟨z*v.val, (meets_relative f u z a hz (z*v.val)).mpr (by simpa using v.property)⟩
  left_inv v := by apply Subtype.ext; simp
  right_inv v := by apply Subtype.ext; simp

section Finite
variable [Finite G] [Finite H] [Finite K] [Finite L]

lemma card_cast_pos (M : Type*) [Group M] [Finite M] : (0 : ℚ) < Nat.card M := by
  exact_mod_cast (Nat.card_pos : 0 < Nat.card M)

def mass (S : Subgroup G) : ℚ := (Nat.card S : ℚ) / Nat.card G

lemma mass_pos (S : Subgroup G) : 0 < mass S :=
  div_pos (card_cast_pos S) (card_cast_pos G)

lemma mass_comap (f : G →* H) (hf : Function.Surjective f) (S : Subgroup H) :
    mass (S.comap f) = (Nat.card S : ℚ) / Nat.card H := by
  apply (div_eq_div_iff (card_cast_pos G).ne' (card_cast_pos H).ne').mpr
  exact_mod_cast card_comap_cross f hf S

lemma meeting_mass (f : G →* H) (hf : Function.Surjective f) (u : G) :
    mass (meetingSubgroup f u) = (orderOf (f u) : ℚ) / Nat.card H := by
  rw [meetingSubgroup, mass_comap f hf, Nat.card_zpowers]

lemma single_probability (f : G →* H) (hf : Function.Surjective f) (u : G) (a : H) :
    (Nat.card {v : G // Meets f u a v} : ℚ) / Nat.card G =
      (orderOf (f u) : ℚ) / Nat.card H := by
  obtain ⟨z,hz⟩ := hf a
  have hzM : Meets f u a z := ⟨0, by simpa using hz⟩
  rw [Nat.card_congr (singleEquiv f u z a hzM)]
  exact meeting_mass f hf u

lemma mass_inf (A B : Subgroup G) [B.Normal] :
    mass (A ⊓ B) = mass A * mass B / mass (A ⊔ B) := by
  have h := card_inf_mul_card_sup A B
  have hc : (Nat.card ↥(A ⊓ B) : ℚ) * Nat.card ↥(A ⊔ B) =
      (Nat.card A : ℚ) * Nat.card B := by exact_mod_cast h
  unfold mass
  have hG := (card_cast_pos G).ne'
  have hAB := (card_cast_pos ↥(A ⊔ B)).ne'
  field_simp
  nlinarith

end Finite

section Commutative
variable [Finite G] [Finite H] [Finite K] [Finite L]

lemma meeting_sup (f : G →* H) (g : G →* K) (h : G →* L)
    (hker : h.ker = f.ker ⊔ g.ker) (u : G) :
    meetingSubgroup f u ⊔ meetingSubgroup g u = meetingSubgroup h u := by
  simp only [meetingSubgroup_eq, hker]
  ac_rfl

/-- Exact collision probability when the intersection is nonempty.
The common quotient contributes the denominator orderOf(h u). -/
theorem pair_probability (f : G →* H) (g : G →* K) (h : G →* L)
    (hf : Function.Surjective f) (hg : Function.Surjective g) (hh : Function.Surjective h)
    (hker : h.ker = f.ker ⊔ g.ker) (u z : G) (a : H) (b : K)
    (hzf : Meets f u a z) (hzg : Meets g u b z)
    [(meetingSubgroup g u).Normal] :
    (Nat.card {v : G // Meets f u a v ∧ Meets g u b v} : ℚ) / Nat.card G =
      ((orderOf (f u) : ℚ) / Nat.card H) *
        ((orderOf (g u) : ℚ) / Nat.card K) /
        ((orderOf (h u) : ℚ) / Nat.card L) := by
  rw [pair_card f g u z a b hzf hzg]
  change mass (meetingSubgroup f u ⊓ meetingSubgroup g u) = _
  rw [mass_inf, meeting_sup f g h hker, meeting_mass f hf,
    meeting_mass g hg, meeting_mass h hh]

end Commutative
#print axioms card_inf_mul_card_sup
#print axioms pair_card
#print axioms meeting_mass
#print axioms single_probability
#print axioms pair_probability
end
end Erdos7UnitOrbitProbability
