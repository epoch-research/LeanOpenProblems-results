import FormalConjecturesUtil
import Submission.CompactRootedInfrastructure
import Submission.OrientedKST

/-! Root-independent one-vertex gluing when one piece is complete bipartite.
The proof uses the one-sided KST estimate, not a root-moving automorphism. -/
open SimpleGraph Filter Asymptotics Finset
namespace Erdos713KstGluing
open Erdos713KST Erdos713Gluing Erdos713Blocking Erdos713Rate Erdos713SwitchGluing

lemma real_bound_of_power {e n s m C : ℕ} (hs : 1 ≤ s) (hC : 1 ≤ C)
    (h : e^s ≤ C*n^m) :
    (e : ℝ) ≤ (C : ℝ)*(n : ℝ)^((m : ℝ)/s) := by
  have hs0 : s ≠ 0 := by omega
  have hsR : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs0
  have hpow : ((n : ℝ)^((m : ℝ)/s))^s = (n : ℝ)^m := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _),div_mul_cancel₀ _ hsR,Real.rpow_natCast]
  apply le_of_pow_le_pow_left₀ hs0 (by positivity)
  rw [mul_pow,hpow]
  have hCpow : (C : ℝ) ≤ (C : ℝ)^s := le_self_pow₀ (by exact_mod_cast hC) hs0
  exact (show (e : ℝ)^s ≤ (C : ℝ)*(n : ℝ)^m by exact_mod_cast h).trans
    (mul_le_mul_of_nonneg_right hCpow (by positivity))

lemma index_ge_one {s : ℕ} (hs : 1 ≤ s) :
    (1 : ℝ) ≤ ((s-1+s : ℕ) : ℝ)/s := by
  apply (le_div_iff₀ (show (0 : ℝ) < s by exact_mod_cast (show 0 < s by omega))).mpr
  simp only [one_mul]
  exact_mod_cast (show s ≤ s-1+s by omega)

open scoped Classical in
lemma real_edges_le_of_keep_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) (B : V → Finset V) (k : ℕ) (M : ℝ)
    (hb : ∀ v, v ∉ B v) (hk : ∀ v, (B v).card ≤ k) (hM0 : 0 ≤ M)
    (hM : ∀ σ : V → Bool, ((keep G B σ).edgeFinset.card : ℝ) ≤ M) :
    (G.edgeFinset.card : ℝ) ≤ (2^(2*k+2) : ℕ)*M + (k*Fintype.card V : ℕ) := by
  have hh := edges_le_of_keep_bound G B k ⌊M⌋₊ hb hk
    (fun σ => Nat.le_floor (hM σ))
  have hr : (G.edgeFinset.card : ℝ) ≤ (2^(2*k+2) : ℕ)*(⌊M⌋₊ : ℝ) +
      (k*Fintype.card V : ℕ) := by exact_mod_cast hh
  have hmul := mul_le_mul_of_nonneg_left (Nat.floor_le hM0)
    (show (0 : ℝ) ≤ (2^(2*k+2) : ℕ) by positivity)
  linarith

lemma no_isolates {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    ∀ a, ∃ b, (Kst s t).Adj a b := by
  rintro (a | b)
  · exact ⟨Sum.inr ⟨0,by omega⟩,by simp⟩
  · exact ⟨Sum.inl ⟨0,by omega⟩,by simp⟩

lemma cross_isBipartiteWith {V : Type*} (G : SimpleGraph V) (S : Set V) :
    (cross G S).IsBipartiteWith S Sᶜ := by
  refine ⟨disjoint_compl_right,?_⟩
  intro u v huv
  exact huv.2.imp id And.symm

open scoped Classical in
lemma free_edge_bound {T V : Type*} [Fintype T] [Fintype V]
    (J : SimpleGraph T) (y : T) (hy : ∃ z, J.Adj y z) (G : SimpleGraph V)
    {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) (x : Fin s ⊕ Fin t)
    (hfree : (wedge (Kst s t) x J y).Free G) :
    (G.edgeFinset.card : ℝ) ≤
      (2^(2*((Fintype.card T+1)*(s+t))+2) : ℕ) *
        ((extremalNumber (Fintype.card V) (Kst s t) : ℝ) +
          (((s+1)^s*(t+1) : ℕ) : ℝ)*(Fintype.card V : ℝ)^(((s-1+s : ℕ) : ℝ)/s) +
          (extremalNumber (Fintype.card V) J : ℝ)) +
      (((Fintype.card T+1)*(s+t))*Fintype.card V : ℕ) := by
  classical
  choose B hb hk hB using blockers_or_no_right (Kst s t) x J y G hfree
  let S : Set V := {v | ∀ f : (Kst s t).Copy G, f x = v → ∃ a, a ≠ x ∧ f a ∈ B v}
  have hNoJ (v : V) (hv : v ∉ S) (g : J.Copy G) (hg : g y = v) : False := by
    rcases hB v with hleft | hright
    · exact hv hleft
    · exact hright g hg
  apply real_edges_le_of_keep_bound G B ((Fintype.card T+1)*(s+t)) _ hb
    (by simpa only [Fintype.card_sum,Fintype.card_fin] using hk) (by positivity)
  intro σ
  let K := keep G B σ
  have hsel (f : (Kst s t).Copy K) (a : Fin s ⊕ Fin t) : selected B σ (f a) := by
    obtain ⟨b,hab⟩ := no_isolates hs ht a
    exact (f.toHom.map_adj hab).2.1
  have hRoot (f : (Kst s t).Copy K) : f x ∉ S := by
    intro hfx
    let g : (Kst s t).Copy G := (Copy.ofLE _ _ (keep_le G B σ)).comp f
    obtain ⟨b,_,hmem⟩ := hfx g rfl
    exact Bool.noConfusion ((hsel f b).1.symm.trans ((hsel f x).2 (f b) hmem))
  have hInside : (Kst s t).Free (inside K S) := by
    rintro ⟨f⟩
    let g : (Kst s t).Copy K := (Copy.ofLE _ _ (inside_le K S)).comp f
    obtain ⟨b,hxb⟩ := no_isolates hs ht x
    exact hRoot g (f.toHom.map_adj hxb).2.1
  have hCross : ((cross K S).edgeFinset.card : ℝ) ≤
      (((s+1)^s*(t+1) : ℕ) : ℝ)*(Fintype.card V : ℝ)^(((s-1+s : ℕ) : ℝ)/s) := by
    apply real_bound_of_power hs (Nat.succ_le_of_lt (by positivity))
    exact Erdos713OrientedKST.edge_pow_le_of_root_excluded (cross K S) S
      (cross_isBipartiteWith K S) hs ht x
        (fun f => hRoot ((Copy.ofLE _ _ (cross_le K S)).comp f))
  have hRest : J.Free (rest K S) := by
    rintro ⟨f⟩
    let g : J.Copy G := (Copy.ofLE _ _ ((rest_le K S).trans (keep_le G B σ))).comp f
    obtain ⟨z,hyz⟩ := hy
    exact hNoJ (f y) (f.toHom.map_adj hyz).2.1 g rfl
  have hA := card_edgeFinset_le_extremalNumber hInside
  have hR := card_edgeFinset_le_extremalNumber hRest
  have hSplit := Erdos713SwitchGluing.edge_split K S
  have hA' : ((inside K S).edgeFinset.card : ℝ) ≤ extremalNumber (Fintype.card V) (Kst s t) := by
    exact_mod_cast hA
  have hR' : ((rest K S).edgeFinset.card : ℝ) ≤ extremalNumber (Fintype.card V) J := by
    exact_mod_cast hR
  have hSplit' : (K.edgeFinset.card : ℝ) ≤ (inside K S).edgeFinset.card +
      (cross K S).edgeFinset.card + (rest K S).edgeFinset.card := by exact_mod_cast hSplit
  exact hSplit'.trans (by linarith)

lemma wedge_upper {T : Type*} [Fintype T]
    (J : SimpleGraph T) (y : T) (hy : ∃ z, J.Adj y z)
    {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) (x : Fin s ⊕ Fin t)
    {b : ℝ} (hb : 1 ≤ b)
    (hJ : (fun n : ℕ => (extremalNumber n J : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^b)) :
    (fun n : ℕ => (extremalNumber n (wedge (Kst s t) x J y) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^(max (((s-1+s : ℕ) : ℝ)/s) b)) := by
  classical
  let k := (Fintype.card T+1)*(s+t)
  let C : ℕ := 2^(2*k+2)
  let r : ℝ := ((s-1+s : ℕ) : ℝ)/s
  let D : ℕ := (s+1)^s*(t+1)
  have hH : (fun n : ℕ => (extremalNumber n (Kst s t) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^r) :=
    upper_of_power_bound (by omega : s ≠ 0) (fun n => extremal_pow_le s t n hs)
  have hH' := hH.trans (rpow_mono_bigO (le_max_left r b))
  have hD := (rpow_mono_bigO (le_max_left r b)).const_mul_left (D : ℝ)
  have hJ' := hJ.trans (rpow_mono_bigO (le_max_right r b))
  have hA := ((hH'.add hD).add hJ').const_mul_left (C : ℝ)
  have hL := cast_linear_bigO (hb.trans (le_max_right r b)) k
  apply IsBigO.trans _ (hA.add hL)
  apply IsBigO.of_bound 1
  filter_upwards with n
  rw [Real.norm_natCast,Real.norm_of_nonneg (by positivity),one_mul]
  rw [← Fintype.card_fin n,extremalNumber_le_iff_of_nonneg _ (by positivity)]
  intro G _ hG
  simpa only [C,k,D,r,edgeFinset_card,Fintype.card_eq_nat_card,Nat.card_fin] using
    free_edge_bound J y hy G hs ht x hG

lemma wedge_rate {T : Type*} [Fintype T]
    (J : SimpleGraph T) (y : T) (hy : ∃ z, J.Adj y z)
    {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) (x : Fin s ⊕ Fin t)
    {b : ℝ} (hH : HasRate (Kst s t) (((s-1+s : ℕ) : ℝ)/s)) (hJ : HasRate J b) :
    HasRate (wedge (Kst s t) x J y) (max (((s-1+s : ℕ) : ℝ)/s) b) := by
  refine ⟨hJ.one_le.trans (le_max_right _ _),
    wedge_upper J y hy hs ht x hJ.one_le hJ.upper,?_⟩
  intro a ha h
  exact max_le (hH.lower a ha ((extremal_mono_bigO ⟨leftCopy _ _ _ _⟩).trans h))
    (hJ.lower a ha ((extremal_mono_bigO ⟨rightCopy _ _ _ _⟩).trans h))


/-- A copy of the left piece extends to a copy of the glued graph, with the
shared root mapped to the image of the old root. -/
def wedgeCopy {A B T : Type*} {H : SimpleGraph A} {L : SimpleGraph B}
    (f : H.Copy L) (x : A) (J : SimpleGraph T) (y : T) :
    (wedge H x J y).Copy (wedge L (f x) J y) := by
  refine ⟨⟨Sum.map f id,?_⟩,?_⟩
  · rintro (a | a) (b | b) hab
    · exact f.toHom.map_adj hab
    · exact ⟨congrArg f hab.1,hab.2⟩
    · exact ⟨congrArg f hab.1,hab.2⟩
    · exact hab
  · rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (f.injective (Sum.inl.inj hab))
    · change Sum.inl (f a) = (Sum.inr b : Erdos713Gluing.Vertex (f x) y) at hab
      cases hab
    · change Sum.inr a = (Sum.inl (f b) : Erdos713Gluing.Vertex (f x) y) at hab
      cases hab
    · exact congrArg Sum.inr (Sum.inr.inj hab)

lemma wedge_rate_of_containment {A T : Type*} [Fintype T]
    (H : SimpleGraph A) (x : A) (J : SimpleGraph T) (y : T) (hy : ∃ z, J.Adj y z)
    {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) (hhi : H ⊑ Kst s t)
    {b : ℝ} (hH : HasRate H (((s-1+s : ℕ) : ℝ)/s)) (hJ : HasRate J b) :
    HasRate (wedge H x J y) (max (((s-1+s : ℕ) : ℝ)/s) b) := by
  obtain ⟨f⟩ := hhi
  refine ⟨hJ.one_le.trans (le_max_right _ _),?_,?_⟩
  · exact (extremal_mono_bigO ⟨wedgeCopy f x J y⟩).trans
      (wedge_upper J y hy hs ht (f x) hJ.one_le hJ.upper)
  · intro a ha h
    exact max_le (hH.lower a ha ((extremal_mono_bigO ⟨leftCopy _ _ _ _⟩).trans h))
      (hJ.lower a ha ((extremal_mono_bigO ⟨rightCopy _ _ _ _⟩).trans h))

lemma wedge_k2t_rate {A T : Type*} [Fintype T]
    (H : SimpleGraph A) (x : A) (J : SimpleGraph T) (y : T) (hy : ∃ z, J.Adj y z)
    {t : ℕ} (ht : 1 ≤ t) (hlo : Erdos713C4.K22 ⊑ H) (hhi : H ⊑ Erdos713K2t.K2t t)
    {b : ℝ} (hJ : HasRate J b) : HasRate (wedge H x J y) (max ((3 : ℝ)/2) b) := by
  exact wedge_rate_of_containment H x J y hy (s := 2) (by decide) ht hhi
    (by simpa using k2t_rate hlo hhi) hJ

lemma wedge_k3t_rate {A T : Type*} [Fintype T]
    (H : SimpleGraph A) (x : A) (J : SimpleGraph T) (y : T) (hy : ∃ z, J.Adj y z)
    {t : ℕ} (ht : 1 ≤ t) (hlo : Erdos713Norm.K33 ⊑ H) (hhi : H ⊑ Erdos713K3t.K3t t)
    {b : ℝ} (hJ : HasRate J b) : HasRate (wedge H x J y) (max ((5 : ℝ)/3) b) := by
  exact wedge_rate_of_containment H x J y hy (s := 3) (by decide) ht hhi
    (by simpa using k3t_rate hlo hhi) hJ

#print axioms free_edge_bound
#print axioms wedge_rate
end Erdos713KstGluing
