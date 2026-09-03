import Submission.CubicNormFour

/-! A global fixed-cross-ratio restriction permits at most q+1 point coordinates. -/
noncomputable section
open Classical Finset Polynomial
set_option maxHeartbeats 1000000
namespace Erdos714FixedCrossRatio
variable {E : Type*} [Field E]

/-- The projective coordinate taking a,b,c to infinity, zero, one. -/
def coordinate (a b c d : E) : E := ((c-a)/(c-b))*((d-b)/(d-a))

lemma coordinate_inj (a b c : E) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    {d e : E} (hd : d ≠ a) (he : e ≠ a)
    (h : coordinate a b c d = coordinate a b c e) : d = e := by
  have hk : (c-a)/(c-b) ≠ 0 := div_ne_zero (sub_ne_zero.mpr hca) (sub_ne_zero.mpr hcb)
  have hv := (div_eq_div_iff (sub_ne_zero.mpr hd) (sub_ne_zero.mpr he)).mp
    (mul_left_cancel₀ hk h)
  have hz : (a-b)*(d-e) = 0 := by linear_combination -hv
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab))

lemma coordinate_at_second (a b c : E) : coordinate a b c b = 0 := by
  simp [coordinate]

lemma coordinate_at_third (a b c : E) (hca : c ≠ a) (hcb : c ≠ b) :
    coordinate a b c c = 1 := by
  dsimp [coordinate]
  field_simp [sub_ne_zero.mpr hca,sub_ne_zero.mpr hcb]

/-- A fixed projective chart injects the point set minus its pole into the roots of X^q-X. -/
theorem card_le_of_chart_fixed (q : ℕ) (hq : 1 < q) (S : Finset E)
    (a b c : E) (ha : a ∈ S) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hfix : ∀ d ∈ S, d ≠ a → (coordinate a b c d)^q = coordinate a b c d) :
    S.card ≤ q+1 := by
  have hi : Set.InjOn (coordinate a b c) (S.erase a) := by
    intro d hd e he h
    exact coordinate_inj a b c hab hca hcb (mem_erase.mp hd).1 (mem_erase.mp he).1 h
  have hp : (X^q-X : E[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero E hq
  have hs : (S.erase a).image (coordinate a b c) ⊆ (X^q-X : E[X]).roots.toFinset := by
    intro z hz
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hz
    rw [Multiset.mem_toFinset,Polynomial.mem_roots hp]
    simp only [IsRoot.def,eval_sub,eval_pow,eval_X,sub_eq_zero]
    exact hfix d (mem_erase.mp hd).2 (mem_erase.mp hd).1
  have hc := (card_le_card hs).trans <| (Multiset.toFinset_card_le _).trans
    (Polynomial.card_roots' _)
  rw [card_image_of_injOn hi,FiniteField.X_pow_card_sub_X_natDegree_eq E hq] at hc
  have he := card_erase_add_one ha
  omega

/-- It suffices to impose the cross-ratio condition on distinct quadruples. -/
theorem card_le_of_all_quadruples_fixed (q : ℕ) (hq : 1 < q) (S : Finset E)
    (hfix : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        (coordinate a b c d)^q = coordinate a b c d) : S.card ≤ q+1 := by
  by_cases hsmall : S.card ≤ 2
  · omega
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := two_lt_card_iff.mp (by omega : 2 < S.card)
  apply card_le_of_chart_fixed q hq S a b c ha hab hac.symm hbc.symm
  intro d hd hda
  by_cases hdb : d = b
  · subst d
    rw [coordinate_at_second,zero_pow (by omega : q ≠ 0)]
  by_cases hdc : d = c
  · subst d
    rw [coordinate_at_third a b c hac.symm hbc.symm,one_pow]
  exact hfix a ha b hb c hc d hd hab hac hda.symm hbc (Ne.symm hdb) (Ne.symm hdc)

/-- The chart agrees with the exact row-normalization cross-ratio. -/
lemma coordinate_eq_parameter (x : Fin 4 → E) (hx : Function.Injective x) :
    coordinate (x 0) (x 1) (x 2) (x 3) =
      Erdos714CubicFour.affineParameter (Erdos714CubicFour.centers x) := by
  rw [Erdos714CubicFour.parameter_eq_crossRatio x hx]
  simp only [coordinate,div_mul_div_comm]

/-- In a finite cubic extension, a globally fixed-cross-ratio point restriction
has at most q+1 points, not the q^3 points of the full norm graph. -/
theorem finiteField_point_bound {F : Type*} [Field F] [Fintype F] [Algebra F E]
    (S : Finset E)
    (hfix : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        FiniteField.frobeniusAlgHom F E (coordinate a b c d) = coordinate a b c d) :
    S.card ≤ Fintype.card F+1 := by
  apply card_le_of_all_quadruples_fixed (Fintype.card F) Fintype.one_lt_card S
  exact hfix

open SimpleGraph
open Erdos714CubicSegre (normGraph)
variable {F : Type*} [Field F] [Fintype F] [Fintype E] [Algebra F E]

/-- The point coordinates of the neighbors retained at p. -/
def neighborPoints (H : SimpleGraph (Bool × (E × Fˣ))) (p : Bool × (E × Fˣ)) : Finset E :=
  (H.neighborFinset p).image (fun v => v.2.1)

/-- The local geometric rule that every distinct quadruple has fixed cross-ratio. -/
def AllFixed (q : ℕ) (S : Finset E) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      (coordinate a b c d)^q = coordinate a b c d

private lemma same_side {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- A shared neighbor and its nonzero weight make the point projection injective. -/
lemma neighbor_point_injective (H : SimpleGraph (Bool × (E × Fˣ)))
    (hH : H ≤ normGraph) (p : Bool × (E × Fˣ)) :
    Set.InjOn (fun v : Bool × (E × Fˣ) => v.2.1) (H.neighborFinset p) := by
  intro v hv w hw he
  change v.2.1 = w.2.1 at he
  have hv' := hH ((H.mem_neighborFinset p v).mp hv)
  have hw' := hH ((H.mem_neighborFinset p w).mp hw)
  have hwt : (v.2.2 : F) = (w.2.2 : F) := by
    apply mul_left_cancel₀ p.2.2.ne_zero
    rw [← hv'.2,← hw'.2,he]
  exact Prod.ext (same_side hv'.1.symm hw'.1.symm) (Prod.ext he (Units.ext hwt))

/-- The local fixed-cross-ratio rule reduces each retained degree from q^3-1 to at most q+1. -/
theorem local_degree_bound (H : SimpleGraph (Bool × (E × Fˣ)))
    (hH : H ≤ normGraph) (p : Bool × (E × Fˣ))
    (hfix : AllFixed (Fintype.card F) (neighborPoints H p)) :
    H.degree p ≤ Fintype.card F+1 := by
  have hb := card_le_of_all_quadruples_fixed (Fintype.card F)
    Fintype.one_lt_card (neighborPoints H p) hfix
  rw [neighborPoints,card_image_of_injOn (neighbor_point_injective H hH p)] at hb
  exact hb

/-- The same rule cannot retain a positive asymptotic fraction of the norm-graph edges. -/
theorem local_edge_bound (H : SimpleGraph (Bool × (E × Fˣ)))
    (hH : H ≤ normGraph)
    (hfix : ∀ p, AllFixed (Fintype.card F) (neighborPoints H p)) :
    H.edgeFinset.card ≤ Fintype.card E*(Fintype.card F-1)*(Fintype.card F+1) := by
  have hb := sum_le_sum (fun p (_ : p ∈ (univ : Finset (Bool × (E × Fˣ)))) =>
    local_degree_bound H hH p (hfix p))
  rw [H.sum_degrees_eq_twice_card_edges] at hb
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,
    Fintype.card_bool,Fintype.card_units,nsmul_eq_mul,Nat.cast_id] at hb
  nlinarith

/-- Exact relative loss for every finite cubic extension; the retained fraction
is at most (q+1)/(q^3-1). This concerns the local rule, not all K44-free subgraphs. -/
theorem local_relative_bound (hdim : Module.finrank F E = 3)
    (H : SimpleGraph (Bool × (E × Fˣ))) (hH : H ≤ normGraph)
    (hfix : ∀ p, AllFixed (Fintype.card F) (neighborPoints H p)) :
    (Fintype.card F^3-1)*H.edgeFinset.card ≤
      (Fintype.card F+1)*(normGraph (F := F) (E := E)).edgeFinset.card := by
  have hb := local_edge_bound H hH hfix
  rw [Module.card_eq_pow_finrank (K := F) (V := E),hdim] at hb
  calc
    (Fintype.card F^3-1)*H.edgeFinset.card ≤
        (Fintype.card F^3-1)*(Fintype.card F^3*(Fintype.card F-1)*(Fintype.card F+1)) :=
      Nat.mul_le_mul_left _ hb
    _ = (Fintype.card F+1)*(normGraph (F := F) (E := E)).edgeFinset.card := by
      rw [Erdos714CubicSegre.normGraph_edges hdim]
      ring

#print axioms card_le_of_all_quadruples_fixed
#print axioms finiteField_point_bound
#print axioms local_degree_bound
#print axioms local_edge_bound
#print axioms local_relative_bound
end Erdos714FixedCrossRatio
