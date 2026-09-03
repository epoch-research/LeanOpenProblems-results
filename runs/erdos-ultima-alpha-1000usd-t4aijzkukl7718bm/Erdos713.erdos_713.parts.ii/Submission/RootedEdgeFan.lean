import FormalConjecturesUtil
import Submission.CompactEdgeFan

/-! Same-edge fans preserve oriented rooted bounds. -/
open SimpleGraph Filter Asymptotics Finset
namespace Erdos713EdgeFan
open Erdos713RootPower

open scoped Classical in
lemma real_edges_le_of_keep_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) (B : V → V → Finset V) (k : ℕ) (M : ℝ)
    (hb : ∀ u v, u ∉ B u v ∧ v ∉ B u v) (hk : ∀ u v, (B u v).card ≤ k)
    (hM0 : 0 ≤ M) (hM : ∀ σ : V → Bool, ((keep G B σ).edgeFinset.card : ℝ) ≤ M) :
    (G.edgeFinset.card : ℝ) ≤ (2^(2*k+2) : ℕ)*M := by
  have hh := edges_le_of_keep_bound G B k ⌊M⌋₊ hb hk (fun σ => Nat.le_floor (hM σ))
  have hr : (G.edgeFinset.card : ℝ) ≤ (2^(2*k+2) : ℕ)*(⌊M⌋₊ : ℝ) := by
    exact_mod_cast hh
  exact hr.trans (mul_le_mul_of_nonneg_left (Nat.floor_le hM0) (by positivity))

/-- The exclusion is at every vertex of S, not at one individual host vertex. -/
lemma blockers_of_root_excluded {W V : Type*} [Fintype W]
    (H : SimpleGraph W) (G : SimpleGraph V) {x y : W} (hxy : x ≠ y)
    {t : ℕ} (ht : 1 ≤ t) (S : Set V)
    (hroot : ∀ f : (fan H x y t).Copy G, f (.inl false) ∉ S) :
    ∀ u v, ∃ B : Finset V, u ∉ B ∧ v ∉ B ∧ B.card ≤ t * Fintype.card W ∧
      ∀ f : H.Copy G, f x = u → f y = v → u ∈ S →
        ∃ a, (a ≠ x ∧ a ≠ y) ∧ f a ∈ B := by
  classical
  intro u v
  by_cases hu : u ∈ S
  · rcases packing_or_blocker H G x y u v t with hp | hB
    · obtain ⟨p⟩ := hp
      exact (hroot (p.toCopy hxy ht) (by simpa [Packing.toCopy] using hu)).elim
    · obtain ⟨B,hbu,hbv,hc,hB⟩ := hB
      exact ⟨B,hbu,hbv,hc,fun f hx hy _ => hB f hx hy⟩
  · exact ⟨∅,by simp,by simp,by simp,fun f hx hy hu' => (hu hu').elim⟩

/-- Ordinary fan bounds alone do not imply rooted bounds. This statement
explicitly assumes the rooted bound for the base. -/
lemma root_bound {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hNoIso : ∀ a, ∃ b, H.Adj a b) {x y : W} (hxy : H.Adj x y)
    {t : ℕ} (ht : 1 ≤ t) {r : ℝ} (hH : RootPowerBound H x r) :
    RootPowerBound (fan H x y t) (.inl false) r := by
  classical
  obtain ⟨C,hC,hbound⟩ := hH
  let L : ℕ := 2^(2*(t * Fintype.card W)+2)
  refine ⟨(L : ℝ)*C,by positivity,?_⟩
  intro n G S hBip hroot
  choose B hb₀ hb₁ hk hB using blockers_of_root_excluded H G hxy.ne ht S hroot
  have hkeep (σ : Fin n → Bool) :
      ((keep G B σ).edgeFinset.card : ℝ) ≤ C*(n : ℝ)^r := by
    have hKB : (keep G B σ).IsBipartiteWith S Sᶜ :=
      ⟨hBip.1,by intro u v h; exact hBip.2 h.1⟩
    have hRoot (f : H.Copy (keep G B σ)) : f x ∉ S := by
      intro hf
      let g : H.Copy G := (Copy.ofLE _ _ (keep_le G B σ)).comp f
      obtain ⟨a,_,ha⟩ := hB (g x) (g y) g rfl rfl hf
      have hfalse : σ (g a) = false := (f.toHom.map_adj hxy).2.2.2.1 (g a) ha
      obtain ⟨b,hab⟩ := hNoIso a
      have htrue : σ (g a) = true := (f.toHom.map_adj hab).2.1
      exact Bool.noConfusion (htrue.symm.trans hfalse)
    simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using hbound n (keep G B σ) S hKB hRoot
  have hh := real_edges_le_of_keep_bound G B (t * Fintype.card W) (C*(n : ℝ)^r)
    (fun u v => ⟨hb₀ u v,hb₁ u v⟩) hk (by positivity) hkeep
  simpa only [L,edgeFinset_card,Fintype.card_eq_nat_card,mul_assoc] using hh

#print axioms real_edges_le_of_keep_bound
#print axioms blockers_of_root_excluded
#print axioms root_bound
end Erdos713EdgeFan
