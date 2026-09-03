import FormalConjecturesUtil
import Submission.Verified

open Filter SimpleGraph Asymptotics

namespace Erdos713Union
open Finset

open scoped Classical in
theorem edges_le_induce_compl_add {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    G.edgeFinset.card ≤ Nat.card (G.induce (S : Set V)ᶜ).edgeSet + S.card * Fintype.card V := by
  classical
  let B := (S ×ˢ (univ : Finset V)).image (fun p => s(p.1, p.2))
  have hcov : G.edgeFinset ⊆ (G.edgeFinset ∩ ((S : Set V)ᶜ).toFinset.sym2) ∪ B := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      by_cases hu : u ∈ S
      · exact mem_union_right _ (mem_image.mpr ⟨(u,v), mem_product.mpr ⟨hu, mem_univ _⟩, rfl⟩)
      by_cases hv : v ∈ S
      · exact mem_union_right _ (mem_image.mpr
          ⟨(v,u), mem_product.mpr ⟨hv, mem_univ _⟩, Sym2.eq_swap⟩)
      · exact mem_union_left _ (mem_inter.mpr ⟨he, by simp [hu, hv]⟩)
  have hB : B.card ≤ S.card * Fintype.card V := by
    exact card_image_le.trans (by rw [card_product, card_univ])
  have hinner : (G.edgeFinset ∩ ((S : Set V)ᶜ).toFinset.sym2).card =
      Nat.card (G.induce (S : Set V)ᶜ).edgeSet := by
    rw [← map_edgeFinset_induce, card_map, edgeFinset_card, Fintype.card_eq_nat_card]
  exact ((card_le_card hcov).trans (card_union_le _ _)).trans
    (by rw [hinner]; exact Nat.add_le_add_left hB _)

theorem sum_contained_of_disjoint_copies {A B V : Type*} {H₁ : SimpleGraph A} {H₂ : SimpleGraph B}
    {G : SimpleGraph V} (f : H₁.Copy G) (g : H₂.Copy G) (hdis : ∀ a b, f a ≠ g b) : H₁ ⊕g H₂ ⊑ G := by
  refine ⟨⟨⟨Sum.elim f g, ?_⟩, ?_⟩⟩
  · intro u v huv
    cases u with
    | inl a =>
      cases v with
      | inl a' => exact f.toHom.map_adj huv
      | inr b => simp at huv
    | inr b =>
      cases v with
      | inl a => simp at huv
      | inr b' => exact g.toHom.map_adj huv
  · intro u v huv
    change Sum.elim f g u = Sum.elim f g v at huv
    cases u with
    | inl a =>
      cases v with
      | inl a' => exact congrArg Sum.inl (f.injective huv)
      | inr b => exact (hdis a b huv).elim
    | inr b =>
      cases v with
      | inl a => exact (hdis a b huv.symm).elim
      | inr b' => exact congrArg Sum.inr (g.injective huv)

open scoped Classical in
theorem free_sum_bound {A B V : Type*} [Fintype A] [Fintype B] [Fintype V]
    (H₁ : SimpleGraph A) (H₂ : SimpleGraph B) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : (H₁ ⊕g H₂).Free G) : G.edgeFinset.card ≤
      extremalNumber (Fintype.card V) H₁ + extremalNumber (Fintype.card V - Fintype.card A) H₂ +
        Fintype.card A * Fintype.card V := by
  classical
  by_cases hf : H₁.Free G
  · exact (card_edgeFinset_le_extremalNumber hf).trans (by omega)
  obtain ⟨f⟩ := not_not.mp hf
  let S := (univ : Finset A).image f
  have hS : S.card = Fintype.card A := by
    change ((univ : Finset A).image f.toHom).card = _
    rw [card_image_of_injective _ f.injective, card_univ]
  have hcard : Fintype.card ↥((S : Set V)ᶜ) = Fintype.card V - Fintype.card A := by
    rw [Fintype.card_compl_set]
    have hh : Nat.card (S : Set V) = Fintype.card A := by
      simpa only [Nat.card_coe_set_eq, Set.ncard_coe_finset] using hS
    simp only [Fintype.card_eq_nat_card, hh] at hh ⊢
  have hKfree : H₂.Free (G.induce (S : Set V)ᶜ) := by
    rintro ⟨g⟩
    apply hfree
    apply sum_contained_of_disjoint_copies f ((Copy.induce G _).comp g)
    intro a b hab
    change f a = (g b).val at hab
    have hb : (g b).val ∉ S := (g b).prop
    exact hb (hab ▸ mem_image_of_mem f (mem_univ a))
  have he := card_edgeFinset_le_extremalNumber hKfree
  simp only [edgeFinset_card, Fintype.card_eq_nat_card] at he
  have hcard' : Nat.card ↥((S : Set V)ᶜ) = Fintype.card V - Fintype.card A := by
    simpa only [Fintype.card_eq_nat_card] using hcard
  rw [hcard'] at he
  have hb := edges_le_induce_compl_add G S
  rw [hS] at hb
  omega

open scoped Classical in
theorem extremal_sum_bound {A B : Type*} [Fintype A] [Fintype B]
    (H₁ : SimpleGraph A) (H₂ : SimpleGraph B) (n : ℕ) :
    extremalNumber n (H₁ ⊕g H₂) ≤ extremalNumber n H₁ +
      extremalNumber (n - Fintype.card A) H₂ + Fintype.card A * n := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ hG
  exact free_sum_bound H₁ H₂ G hG

end Erdos713Union

namespace Erdos713Rate
open Finset

/-- An attained upper growth exponent, with a matching lower threshold among
exponents at least one. No pure-power asymptotic is assumed for the graph. -/
structure HasRate {W : Type*} (H : SimpleGraph W) (r : ℝ) : Prop where
  one_le : 1 ≤ r
  upper : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ r)
  lower : ∀ a : ℝ, 1 ≤ a →
    ((fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ a)) → r ≤ a

theorem exponent_eq {W : Type*} {H : SimpleGraph W} {r a c : ℝ} (hr : HasRate H r)
    (ha : 1 ≤ a) (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = r := by
  apply le_antisymm
  · exact Erdos713Forest.exponent_le_of_isBigO
      (((isBigO_const_mul_left_iff hc).mp h.isBigO_symm).trans hr.upper)
  · exact hr.lower a ha ((isBigO_const_mul_right_iff hc).mp h.isBigO)

theorem rpow_mono_bigO {a b : ℝ} (hab : a ≤ b) :
    (fun n : ℕ => (n : ℝ) ^ a) =O[atTop] (fun n : ℕ => (n : ℝ) ^ b) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), one_mul]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hab

theorem cast_linear_bigO {r : ℝ} (hr : 1 ≤ r) (d : ℕ) :
    (fun n : ℕ => ((d * n : ℕ) : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ r) := by
  have h : (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ r) := by
    simpa only [Real.rpow_one] using rpow_mono_bigO hr
  simpa only [Nat.cast_mul] using h.const_mul_left (d : ℝ)

theorem shifted_upper {f : ℕ → ℝ} {r : ℝ} (hr : 0 ≤ r) (d : ℕ)
    (h : f =O[atTop] (fun n : ℕ => (n : ℝ) ^ r)) :
    (fun n : ℕ => f (n - d)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ r) := by
  have ht : Tendsto (fun n : ℕ => n - d) atTop atTop := tendsto_atTop.2 (fun N => by
    filter_upwards [eventually_ge_atTop (N + d)] with n hn
    omega)
  have hh : (fun n : ℕ => f (n - d)) =O[atTop] (fun n : ℕ => ((n - d : ℕ) : ℝ) ^ r) :=
    h.comp_tendsto ht
  apply hh.trans
  apply IsBigO.of_bound 1
  filter_upwards with n
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), one_mul]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le n d) hr

theorem extremal_mono_bigO {U W : Type*} {G : SimpleGraph U} {H : SimpleGraph W} (hGH : G ⊑ H) :
    (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (extremalNumber n H : ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards with n
  rw [Real.norm_natCast, Real.norm_natCast, one_mul]
  exact_mod_cast hGH.extremalNumber_le (n := n)

theorem sum_rate {A B : Type*} [Fintype A] [Fintype B] {H₁ : SimpleGraph A} {H₂ : SimpleGraph B}
    {r₁ r₂ : ℝ} (h₁ : HasRate H₁ r₁) (h₂ : HasRate H₂ r₂) : HasRate (H₁ ⊕g H₂) (max r₁ r₂) := by
  refine ⟨h₁.one_le.trans (le_max_left _ _), ?_, ?_⟩
  · have hA := h₁.upper.trans (rpow_mono_bigO (le_max_left r₁ r₂))
    have hB := (shifted_upper (by linarith [h₂.one_le] : 0 ≤ r₂) (Fintype.card A) h₂.upper).trans
      (rpow_mono_bigO (le_max_right r₁ r₂))
    have hC := cast_linear_bigO (h₁.one_le.trans (le_max_left r₁ r₂)) (Fintype.card A)
    apply IsBigO.trans _ ((hA.add hB).add hC)
    apply IsBigO.of_bound 1
    filter_upwards with n
    rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity), one_mul]
    exact_mod_cast Erdos713Union.extremal_sum_bound H₁ H₂ n
  · intro a ha h
    apply max_le
    · exact h₁.lower a ha ((extremal_mono_bigO ⟨Embedding.sumInl.toCopy⟩).trans h)
    · exact h₂.lower a ha ((extremal_mono_bigO ⟨Embedding.sumInr.toCopy⟩).trans h)

end Erdos713Rate

#print axioms Erdos713Union.extremal_sum_bound
#print axioms Erdos713Rate.sum_rate

namespace Erdos713Rate
open Finset

theorem upper_of_power_bound {f : ℕ → ℕ} {k m C : ℕ} (hk : k ≠ 0)
    (hb : ∀ n, f n ^ k ≤ C * n ^ m) :
    (fun n : ℕ => (f n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((m : ℝ) / k)) := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have he (n : ℕ) : ((n : ℝ) ^ ((m : ℝ) / k)) ^ k = (n : ℝ) ^ m := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _), div_mul_cancel₀ _ hk', Real.rpow_natCast]
  apply IsBigO.of_pow hk
  change (fun n : ℕ => (f n : ℝ) ^ k) =O[atTop]
    (fun n : ℕ => ((n : ℝ) ^ ((m : ℝ) / k)) ^ k)
  simp only [he]
  apply IsBigO.of_bound (C : ℝ)
  filter_upwards with n
  rw [Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _),
    Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
  exact_mod_cast hb n

theorem forest_rate {W : Type*} [Fintype W] (H : SimpleGraph W) (hF : H.IsAcyclic) : HasRate H 1 := by
  classical
  refine ⟨le_rfl, ?_, fun a ha _ => ha⟩
  by_cases hW : Nonempty W
  · letI := hW
    apply IsBigO.of_bound (Fintype.card W : ℝ)
    filter_upwards with n
    rw [Real.norm_natCast, Real.rpow_one, Real.norm_natCast]
    exact_mod_cast Erdos713Forest.extremal_forest_bound H hF n
  · letI : IsEmpty W := not_nonempty_iff.mp hW
    have hz (n : ℕ) : extremalNumber n H = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [← Fintype.card_fin n, extremalNumber_le_iff]
      intro K _ hfree
      exact (hfree IsContained.of_isEmpty).elim
    simp only [hz, Nat.cast_zero]
    exact isBigO_zero _ _

theorem iso_rate {U W : Type*} {G : SimpleGraph U} {H : SimpleGraph W}
    (e : G ≃g H) {r : ℝ} (h : HasRate H r) : HasRate G r := by
  refine ⟨h.one_le, (extremal_mono_bigO ⟨e.toCopy⟩).trans h.upper, ?_⟩
  intro a ha hG
  exact h.lower a ha ((extremal_mono_bigO ⟨e.symm.toCopy⟩).trans hG)

open scoped Classical in
theorem leaf_rate {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    {x y : W} (hx : H.degree x = 1) (hxy : H.Adj x y) {r : ℝ}
    (hr : HasRate (H.induce {x}ᶜ) r) : HasRate H r := by
  refine ⟨hr.one_le, ?_, ?_⟩
  · have hu := hr.upper.add (cast_linear_bigO hr.one_le (Fintype.card W))
    apply IsBigO.trans _ hu
    apply IsBigO.of_bound 1
    filter_upwards with n
    rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity), one_mul]
    exact_mod_cast Erdos713Leaf.extremal_leaf_upper H hx hxy n
  · intro a ha h
    exact hr.lower a ha ((extremal_mono_bigO ⟨Copy.induce H _⟩).trans h)

open scoped Classical in
theorem isolated_rate {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    {x : W} (hx : H.degree x = 0) {r : ℝ} (hr : HasRate (H.induce {x}ᶜ) r) : HasRate H r := by
  refine ⟨hr.one_le, ?_, ?_⟩
  · apply hr.upper.congr' _ Filter.EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (Fintype.card W)] with n hn
    rw [Erdos713Leaf.extremal_isolated_eq H hx hn]
  · intro a ha h
    exact hr.lower a ha ((extremal_mono_bigO ⟨Copy.induce H _⟩).trans h)

theorem rate_of_C4_upper {W : Type*} {H : SimpleGraph W} (hlo : Erdos713C4.K22 ⊑ H)
    (hu : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2))) : HasRate H ((3 : ℝ) / 2) := by
  refine ⟨by norm_num, hu, ?_⟩
  intro a _ h
  apply Erdos713C4.lower_exponent_of_prime_bound h
  intro p hp
  exact (Erdos713C4.extremal_lower_prime p hp).trans hlo.extremalNumber_le

theorem rate_of_C6_upper {W : Type*} {H : SimpleGraph W} (hlo : Erdos713C6.C6 ⊑ H)
    (hu : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 3))) : HasRate H ((4 : ℝ) / 3) := by
  refine ⟨by norm_num, hu, ?_⟩
  intro a _ h
  apply Erdos713C6.lower_exponent_of_prime_bound h
  intro p hp
  exact (Erdos713C6.extremal_lower_prime p hp).trans hlo.extremalNumber_le

theorem rate_of_K33_upper {W : Type*} {H : SimpleGraph W} (hlo : Erdos713Norm.K33 ⊑ H)
    (hu : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((5 : ℝ) / 3))) : HasRate H ((5 : ℝ) / 3) := by
  refine ⟨by norm_num, hu, ?_⟩
  intro a ha h
  apply Erdos713Norm.lower_exponent_of_prime_bound (by linarith) h
  intro p hp
  exact (Erdos713Norm.extremal_lower_prime p hp).trans (Nat.mul_le_mul_left 4 hlo.extremalNumber_le)

theorem k2t_rate {W : Type*} {H : SimpleGraph W} {t : ℕ}
    (hlo : Erdos713C4.K22 ⊑ H) (hhi : H ⊑ Erdos713K2t.K2t t) : HasRate H ((3 : ℝ) / 2) := by
  apply rate_of_C4_upper hlo
  apply (extremal_mono_bigO hhi).trans
  apply IsBigO.of_bound ((t : ℝ) + 1)
  filter_upwards with n
  rw [Real.norm_natCast, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact Erdos713K2t.extremal_upper t n

theorem k3t_rate {W : Type*} {H : SimpleGraph W} {t : ℕ}
    (hlo : Erdos713Norm.K33 ⊑ H) (hhi : H ⊑ Erdos713K3t.K3t t) : HasRate H ((5 : ℝ) / 3) := by
  apply rate_of_K33_upper hlo
  apply (extremal_mono_bigO hhi).trans
  simpa only [Nat.cast_ofNat] using upper_of_power_bound (by decide : 3 ≠ 0)
    (fun n => Erdos713KST.extremal_pow_le 3 t n (by decide))

theorem c6_rate {W : Type*} {H : SimpleGraph W}
    (hlo : Erdos713C6.C6 ⊑ H) (hhi : H ⊑ Erdos713C6.C6) : HasRate H ((4 : ℝ) / 3) := by
  apply rate_of_C6_upper hlo
  apply (extremal_mono_bigO hhi).trans
  simpa only [Nat.cast_ofNat] using upper_of_power_bound (by decide : 3 ≠ 0)
    Erdos713C6.extremal_cube_le

theorem minus_rate {W : Type*} {H : SimpleGraph W}
    (hlo : Erdos713C4.K22 ⊑ H) (hhi : H ⊑ Erdos713Minus.D33) : HasRate H ((3 : ℝ) / 2) := by
  apply rate_of_C4_upper hlo
  apply (extremal_mono_bigO hhi).trans
  simpa only [Nat.cast_ofNat] using upper_of_power_bound (by decide : 2 ≠ 0)
    Erdos713Minus.extremal_sq_le

end Erdos713Rate

#print axioms Erdos713Rate.leaf_rate
#print axioms Erdos713Rate.k3t_rate

namespace Erdos713Rate
open Finset Erdos713C6

theorem upper_exceptional_columns {A B W : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (R : A → B → Prop) {r : ℕ} (hr : 1 ≤ r) (E : Set B) (hE : Nat.card E ≤ r)
    (hR : ∀ b ∉ E, Nat.card {a // R a b} ≤ r) {H : SimpleGraph W} (hhi : H ⊑ bipGraph R) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (((r - 1 + r : ℕ) : ℝ) / r)) := by
  classical
  let R' : A → ↥(Eᶜ) → Prop := fun a b => R a b.val
  have hR' (b : ↥(Eᶜ)) : ∃ w : Fin r → A, ∀ a, R' a b → a ∈ Set.range w := by
    obtain ⟨w, hw⟩ := Erdos713GeneralDRC.cover_of_card_le {a | R a b.val} (hR b.val b.prop)
    exact ⟨w, fun a ha => hw ha⟩
  apply (extremal_mono_bigO (hhi.trans (Erdos713GeneralDRC.contained_in_augmented R E hE))).trans
  exact upper_of_power_bound (by omega) (fun n => Erdos713GeneralDRC.extremal_pow_le R' hr hR' n)

theorem upper_bipartition {W : Type*} [Fintype W] (H : SimpleGraph W)
    (S E : Set W) [Nonempty S] (hB : H.IsBipartiteWith S Sᶜ) {r : ℕ} (hr : 1 ≤ r)
    (hE : Nat.card E ≤ r) (hdeg : ∀ v ∈ Sᶜ, v ∉ E → Nat.card (H.neighborSet v) ≤ r) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (((r - 1 + r : ℕ) : ℝ) / r)) := by
  classical
  let R : S → ↥(Sᶜ) → Prop := fun u v => H.Adj u.val v.val
  let E' : Set ↥(Sᶜ) := {b | b.val ∈ E}
  have hE' : Nat.card E' ≤ r := by
    let f : E' ↪ E := ⟨fun b => ⟨b.val.val, b.prop⟩, by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : E => z.val) hxy⟩
    have hh := Fintype.card_le_of_embedding f
    simp only [Fintype.card_eq_nat_card] at hh
    exact hh.trans hE
  have hR (b : ↥(Sᶜ)) (hb : b ∉ E') : Nat.card {a : S // R a b} ≤ r := by
    let f : {a : S // R a b} ↪ H.neighborSet b.val :=
      ⟨fun a => ⟨a.val.val, a.prop.symm⟩, by
          intro x y hxy
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun z : H.neighborSet b.val => z.val) hxy⟩
    have hh := Fintype.card_le_of_embedding f
    simp only [Fintype.card_eq_nat_card] at hh
    exact hh.trans (hdeg b.val b.prop hb)
  have hhi : H ⊑ bipGraph R := by
    let e := (Equiv.Set.sumCompl S).symm
    refine ⟨⟨⟨e, ?_⟩, e.injective⟩⟩
    intro u v huv
    rcases hB.2 huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · have hv' : v ∉ S := hv
      simpa [e, Equiv.Set.sumCompl_symm_apply_of_mem hu,
        Equiv.Set.sumCompl_symm_apply_of_notMem hv', bipGraph, R] using huv
    · have hu' : u ∉ S := hu
      simpa [e, Equiv.Set.sumCompl_symm_apply_of_mem hv,
        Equiv.Set.sumCompl_symm_apply_of_notMem hu', bipGraph, R] using huv.symm
  exact upper_exceptional_columns R hr E' hE' hR hhi

theorem nonempty_left_of_copy {U W : Type*} {J : SimpleGraph U} (H : SimpleGraph W) (S : Set W)
    (hB : H.IsBipartiteWith S Sᶜ) (f : J.Copy H) {u v : U} (huv : J.Adj u v) : Nonempty S := by
  rcases hB.2 (f.toHom.map_adj huv) with ⟨hu, _⟩ | ⟨_, hv⟩
  · exact ⟨⟨_, hu⟩⟩
  · exact ⟨⟨_, hv⟩⟩

theorem two_exceptions_rate {W : Type*} [Fintype W] (H : SimpleGraph W) (S E : Set W)
    (hB : H.IsBipartiteWith S Sᶜ) (hE : Nat.card E ≤ 2)
    (hdeg : ∀ v ∈ Sᶜ, v ∉ E → Nat.card (H.neighborSet v) ≤ 2)
    (hlo : Erdos713C4.K22 ⊑ H) : HasRate H ((3 : ℝ) / 2) := by
  classical
  obtain ⟨f⟩ := hlo
  letI : Nonempty S := nonempty_left_of_copy H S hB f (u := Sum.inl 0) (v := Sum.inr 0)
    (by simp [Erdos713C4.K22, completeBipartiteGraph])
  apply rate_of_C4_upper ⟨f⟩
  simpa only [Nat.cast_ofNat] using upper_bipartition H S E hB (by decide : 1 ≤ 2) hE hdeg

theorem three_exceptions_rate {W : Type*} [Fintype W] (H : SimpleGraph W) (S E : Set W)
    (hB : H.IsBipartiteWith S Sᶜ) (hE : Nat.card E ≤ 3)
    (hdeg : ∀ v ∈ Sᶜ, v ∉ E → Nat.card (H.neighborSet v) ≤ 3)
    (hlo : Erdos713Norm.K33 ⊑ H) : HasRate H ((5 : ℝ) / 3) := by
  classical
  obtain ⟨f⟩ := hlo
  letI : Nonempty S := nonempty_left_of_copy H S hB f (u := Sum.inl 0) (v := Sum.inr 0)
    (by simp [Erdos713Norm.K33, completeBipartiteGraph])
  apply rate_of_K33_upper ⟨f⟩
  simpa only [Nat.cast_ofNat] using upper_bipartition H S E hB (by decide : 1 ≤ 3) hE hdeg

theorem minus4_rate {W : Type*} {H : SimpleGraph W}
    (hlo : Erdos713Norm.K33 ⊑ H) (hhi : H ⊑ Erdos713Minus44.D44) : HasRate H ((5 : ℝ) / 3) := by
  classical
  have hn : Nat.card {i : Fin 4 // i ≠ 3} ≤ 3 := by
    simpa only [Fintype.card_eq_nat_card, Nat.card_fin] using (Set.card_ne_eq (3 : Fin 4)).le
  apply rate_of_K33_upper hlo
  apply upper_exceptional_columns (fun i j : Fin 4 => i ≠ 3 ∨ j ≠ 3)
    (by decide : 1 ≤ 3) {j | j ≠ 3} hn ?_ hhi
  intro b hb
  have hb3 : b = 3 := by simpa using hb
  subst b
  simpa only [ne_eq, not_true_eq_false, or_false] using hn

end Erdos713Rate

#print axioms Erdos713Rate.two_exceptions_rate
#print axioms Erdos713Rate.three_exceptions_rate
#print axioms Erdos713Rate.minus4_rate
