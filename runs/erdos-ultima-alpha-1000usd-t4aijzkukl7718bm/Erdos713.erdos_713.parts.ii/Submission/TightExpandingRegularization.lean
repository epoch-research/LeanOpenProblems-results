import FormalConjecturesUtil
import Submission.UpToSuspension

/-! Expanding almost-regular witnesses that retain a positive lower coefficient
at the tight exponent itself. No rationality assertion is assumed here. -/
open Filter SimpleGraph Asymptotics Finset
namespace Erdos713TightExpansion
open Erdos713Expansion Erdos713ExpandingRegularization
set_option maxHeartbeats 2000000
universe u

lemma exists_tight_record {W : Type*} (H : SimpleGraph W) {α r c : ℝ}
    (hr : 0 < r) (hrα : r < α) (hc : 0 < c)
    (hLower : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ c*(n : ℝ)^α < (extremalNumber n H : ℝ))
    (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ 0 < n ∧ ∃ C : ℝ, 0 < C ∧
      (extremalNumber n H : ℝ) = C*(n : ℝ)^r ∧
      (∀ j : ℕ, j ≤ n → (extremalNumber j H : ℝ) ≤ C*(j : ℝ)^r) ∧
      c*(n : ℝ)^α < (extremalNumber n H : ℝ) := by
  classical
  have hPow := (tendsto_rpow_atTop (sub_pos.mpr hrα)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have he : ∀ᶠ n : ℕ in atTop, ((M : ℝ)^2+1)/c < (n : ℝ)^(α-r) :=
    hPow.eventually (eventually_gt_atTop _)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  obtain ⟨n,hn,hDense⟩ := hLower (max N 1)
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnpos : 0 < n := (by omega : 0 < max N 1).trans_le hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  let f : ℕ → ℝ := fun j => (extremalNumber j H : ℝ)/(j : ℝ)^r
  obtain ⟨m,hm,hMax⟩ := exists_max_image (range (n+1)) f ⟨n,by simp⟩
  have hmle : m ≤ n := by have := mem_range.mp hm; omega
  have hfn : c*(n : ℝ)^(α-r) < f n := by
    rw [Real.rpow_sub hnr, ← mul_div_assoc]
    exact (div_lt_div_iff_of_pos_right (Real.rpow_pos_of_pos hnr r)).mpr hDense
  have hBig : (M : ℝ)^2+1 < f m := by
    have hh : (M : ℝ)^2+1 < c*(n : ℝ)^(α-r) := by
      have hh := (div_lt_iff₀ hc).mp (hN n hnN)
      nlinarith
    exact (hh.trans hfn).trans_le (hMax n (by simp))
  have hmpos : 0 < m := by
    by_contra hz
    have hm0 : m = 0 := by omega
    have : f m = 0 := by simp [f,hm0,Real.zero_rpow hr.ne']
    rw [this] at hBig
    nlinarith [sq_nonneg (M : ℝ)]
  have hmr : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hSquare : f m ≤ (m : ℝ)^2 := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hmr r)).mpr
    have ht : (extremalNumber m H : ℝ) ≤ (m : ℝ)^2 := by
      exact_mod_cast Erdos713RateRegularization.extremal_sq_bound H m
    exact ht.trans (le_mul_of_one_le_right (by positivity)
      (Real.one_le_rpow (by exact_mod_cast hmpos) hr.le))
  have hM : M ≤ m := by
    by_contra hh
    have hle : (m : ℝ) ≤ M := by exact_mod_cast (Nat.lt_of_not_ge hh).le
    have := pow_le_pow_left₀ (Nat.cast_nonneg m) hle 2
    linarith
  have hRecord : (extremalNumber m H : ℝ) = f m*(m : ℝ)^r :=
    (div_mul_cancel₀ _ (Real.rpow_pos_of_pos hmr r).ne').symm
  refine ⟨m,hM,hmpos,f m,by nlinarith [sq_nonneg (M : ℝ)],hRecord,?_,?_⟩
  · intro j hj
    by_cases hj0 : j = 0
    · subst j
      have he0 : extremalNumber 0 H = 0 := by
        have := Erdos713RateRegularization.extremal_sq_bound H 0
        simpa using this
      simp [he0,Real.zero_rpow hr.ne']
    have hjr : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj0
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hjr r)).mp
    exact hMax j (by simp only [mem_range]; omega)
  · have hcm : c*(m : ℝ)^(α-r) < f m :=
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg m) (Nat.cast_le.mpr hmle) (sub_nonneg.mpr hrα.le))
        hc.le).trans_lt (hfn.trans_le (hMax n (by simp)))
    rw [Real.rpow_sub hmr, ← mul_div_assoc] at hcm
    rw [hRecord]
    exact (div_lt_iff₀ (Real.rpow_pos_of_pos hmr r)).mp hcm

lemma of_positive_lower_sequence {W : Type*} (H : SimpleGraph W) {α c : ℝ}
    (hα : 1 < α) (hc : 0 < c)
    (hLower : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ c*(n : ℝ)^α < (extremalNumber n H : ℝ)) :
    ∃ a R : ℝ, 0 < a ∧ 0 < R ∧ ∀ N : ℕ,
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (d : ℝ),
        N ≤ Fintype.card V ∧ 2 ≤ Fintype.card V ∧ H.Free G ∧ G.IsBipartite ∧
        a*(Fintype.card V : ℝ)^α ≤ (Nat.card G.edgeSet : ℝ) ∧
        0 < d ∧ a*(Fintype.card V : ℝ)^(α-1) ≤ d ∧
        (∀ v, d ≤ (Nat.card (G.neighborSet v) : ℝ) ∧
          (Nat.card (G.neighborSet v) : ℝ) ≤ R*d) ∧
        (∀ S : Finset V, 2*S.card ≤ Fintype.card V →
          d*S.card ≤ (Nat.card (Erdos713SwitchGluing.cross G (S : Set V)).edgeSet : ℝ)) := by
  classical
  let r := (1+α)/2
  have hr : 1 < r := by dsimp [r]; linarith
  have hrα : r < α := by dsimp [r]; linarith
  have hk := expansionConstant_pos hr
  obtain ⟨L,hL,hSmall⟩ := Erdos713Regularization.exists_partition_size
    (r := r) (d := expansionConstant r/4) (C := 1) hr (by positivity) (by norm_num)
  simp only [mul_one] at hSmall
  have hSmall' : (L : ℝ)*(3/(L : ℝ))^r ≤ expansionConstant r/32 := by
    convert hSmall using 1; ring
  let a : ℝ := expansionConstant r*c/16
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a,16*L/expansionConstant r,ha,by positivity,?_⟩
  intro N
  obtain ⟨n,hn,hnpos,C,hC,hRecord,hUpper,hDense⟩ :=
    exists_tight_record H (lt_trans zero_lt_one hr) hrα hc hLower (max (max (2*N) 4) L)
  have hnN : 2*N ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn4 : 4 ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnL : L ≤ n := (le_max_right _ _).trans hn
  obtain ⟨V,instV,G,hVbig,hVle,hVtwo,hFree,hBip,hDeg,hCuts⟩ :=
    local_regular_expander H hr hC n L hn4 hL hnL hSmall' hRecord hUpper
  let d : ℝ := expansionConstant r*C/8*(n : ℝ)^(r-1)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hvr : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hd : 0 < d := by dsimp [d]; positivity
  have hCoeff : c*(n : ℝ)^(α-1) ≤ C*(n : ℝ)^(r-1) := by
    rw [hRecord,rpow_factor hnr.le hα,rpow_factor hnr.le hr] at hDense
    apply (mul_le_mul_iff_right₀ hnr).mp
    nlinarith
  have hD : 2*a*(Fintype.card V : ℝ)^(α-1) ≤ d := by
    have hmono := Real.rpow_le_rpow hvr.le (Nat.cast_le.mpr hVle) (by linarith : 0 ≤ α-1)
    have h1 := mul_le_mul_of_nonneg_left hmono hc.le
    have h2 := mul_le_mul_of_nonneg_left (h1.trans hCoeff)
      (show 0 ≤ expansionConstant r/8 by positivity)
    dsimp [a,d]
    convert h2 using 1 <;> ring
  have hEdges : d*(Fintype.card V : ℝ) ≤ 2*(Nat.card G.edgeSet : ℝ) := by
    have he := sum_le_sum (s := (univ : Finset V)) (fun v _ => (hDeg v).1)
    have hs : (∑ v : V, (Nat.card (G.neighborSet v) : ℝ)) = 2*(Nat.card G.edgeSet : ℝ) := by
      exact_mod_cast (by simpa only [← card_neighborSet_eq_degree,edgeFinset_card,
        Fintype.card_eq_nat_card] using G.sum_degrees_eq_twice_card_edges)
    simp only [sum_const,card_univ,nsmul_eq_mul] at he
    rw [hs] at he
    dsimp only [d]
    nlinarith
  refine ⟨V,instV,G,d,by omega,hVtwo,hFree,hBip,?_,hd,?_,?_,hCuts⟩
  · have hh := mul_le_mul_of_nonneg_right hD hvr.le
    rw [rpow_factor hvr.le hα]
    nlinarith
  · have hp : 0 ≤ a*(Fintype.card V : ℝ)^(α-1) := by positivity
    linarith
  · intro v
    refine ⟨(hDeg v).1,((hDeg v).2).trans ?_⟩
    dsimp only [d]
    exact le_of_eq (by field_simp; ring)

lemma of_tight_rate {W : Type*} (H : SimpleGraph W) {α : ℝ}
    (hα : 1 < α) (h : Erdos713Tight.HasTightRate H α) :
    ∃ a R : ℝ, 0 < a ∧ 0 < R ∧ ∀ N : ℕ,
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (d : ℝ),
        N ≤ Fintype.card V ∧ 2 ≤ Fintype.card V ∧ H.Free G ∧ G.IsBipartite ∧
        a*(Fintype.card V : ℝ)^α ≤ (Nat.card G.edgeSet : ℝ) ∧
        0 < d ∧ a*(Fintype.card V : ℝ)^(α-1) ≤ d ∧
        (∀ v, d ≤ (Nat.card (G.neighborSet v) : ℝ) ∧
          (Nat.card (G.neighborSet v) : ℝ) ≤ R*d) ∧
        (∀ S : Finset V, 2*S.card ≤ Fintype.card V →
          d*S.card ≤ (Nat.card (Erdos713SwitchGluing.cross G (S : Set V)).edgeSet : ℝ)) := by
  obtain ⟨c,hc,hLower⟩ := Erdos713Tight.exists_positive_lower_constant h
  exact of_positive_lower_sequence H hα hc hLower

lemma uniform_proper_littleO {W : Type u} [Fintype W] (H : SimpleGraph W) {α : ℝ}
    (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (hProper : ∀ J : SimpleGraph W, J < H →
      (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)^α))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n →
      ∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → ¬ Nonempty (J ≃g H) →
        (extremalNumber n J : ℝ) ≤ ε*(n : ℝ)^α := by
  classical
  have hEach (J : SimpleGraph W) : ∀ᶠ n : ℕ in atTop,
      J < H → (extremalNumber n J : ℝ) ≤ ε*(n : ℝ)^α := by
    by_cases hJ : J < H
    · filter_upwards [(hProper J hJ).bound hε] with n hn
      intro _
      simpa only [Real.norm_natCast,
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) α)] using hn
    · exact Filter.Eventually.of_forall (fun _ hh => (hJ hh).elim)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (Filter.eventually_all.mpr hEach)
  refine ⟨M,?_⟩
  intro n hn T _ J hJH hNe
  obtain ⟨f⟩ := hJH
  have hle : J.map f.toEmbedding ≤ H :=
    (map_le_iff_le_comap f.toEmbedding J H).mpr (fun _ _ h => f.toHom.map_adj h)
  have hlt : J.map f.toEmbedding < H := lt_of_le_of_ne hle
    (fun he => hNe (Erdos713PowerCritical.iso_of_map_eq_of_no_isolates hNoIso f he))
  have hm : J ⊑ J.map f.toEmbedding := ⟨(Embedding.map f.toEmbedding J).toCopy⟩
  exact (Nat.cast_le.mpr hm.extremalNumber_le).trans (hM n hn _ hlt)

lemma robust_of_tight_rate {W : Type u} [Fintype W] (H : SimpleGraph W) {α : ℝ}
    (hα : 1 < α) (h : Erdos713Tight.HasTightRate H α)
    (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (hProper : ∀ J : SimpleGraph W, J < H →
      (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)^α)) :
    ∃ a R : ℝ, 0 < a ∧ 0 < R ∧ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (d : ℝ),
        N ≤ Fintype.card V ∧ 2 ≤ Fintype.card V ∧ H.Free G ∧ G.IsBipartite ∧
        a*(Fintype.card V : ℝ)^α ≤ (Nat.card G.edgeSet : ℝ) ∧
        0 < d ∧ a*(Fintype.card V : ℝ)^(α-1) ≤ d ∧
        (∀ v, d ≤ (Nat.card (G.neighborSet v) : ℝ) ∧
          (Nat.card (G.neighborSet v) : ℝ) ≤ R*d) ∧
        (∀ S : Finset V, 2*S.card ≤ Fintype.card V →
          d*S.card ≤ (Nat.card (Erdos713SwitchGluing.cross G (S : Set V)).edgeSet : ℝ)) ∧
        (∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → ¬ Nonempty (J ≃g H) →
          ∀ F : SimpleGraph V, ε*(Nat.card G.edgeSet : ℝ) ≤ (Nat.card F.edgeSet : ℝ) → J ⊑ F) := by
  classical
  obtain ⟨a,R,ha,hR,hReg⟩ := of_tight_rate H hα h
  refine ⟨a,R,ha,hR,?_⟩
  intro ε hε N
  obtain ⟨M,hM⟩ := uniform_proper_littleO H hNoIso hProper
    (show 0 < ε*a/2 by positivity)
  obtain ⟨V,instV,G,d,hV,hVtwo,hFree,hBip,hE,hd,hD,hDeg,hCuts⟩ := hReg (max N M)
  have hN : N ≤ Fintype.card V := (le_max_left _ _).trans hV
  have hM' : M ≤ Fintype.card V := (le_max_right _ _).trans hV
  refine ⟨V,instV,G,d,hN,hVtwo,hFree,hBip,hE,hd,hD,hDeg,hCuts,?_⟩
  intro T _ J hJH hNe F hF
  have hu := hM (Fintype.card V) hM' T J hJH hNe
  have hvr : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hp : 0 < ε*a*(Fintype.card V : ℝ)^α := by positivity
  have hl := mul_le_mul_of_nonneg_left hE hε.le
  have hlt : (extremalNumber (Fintype.card V) J : ℝ) < (Nat.card F.edgeSet : ℝ) := by
    nlinarith
  apply IsContained.of_extremalNumber_lt_card_edgeFinset
  simp only [edgeFinset_card,Fintype.card_eq_nat_card]
  simp only [Fintype.card_eq_nat_card] at hlt
  exact_mod_cast hlt

lemma robust_scaled {W : Type u} [Fintype W] (H : SimpleGraph W) {α : ℝ}
    (hα : 1 < α) (h : Erdos713Tight.HasTightRate H α)
    (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (hProper : ∀ J : SimpleGraph W, J < H →
      (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)^α)) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        N ≤ Fintype.card V ∧ 2 ≤ Fintype.card V ∧ H.Free G ∧ G.IsBipartite ∧
        a*(Fintype.card V : ℝ)^α ≤ (Nat.card G.edgeSet : ℝ) ∧
        (∀ v, a*(Fintype.card V : ℝ)^(α-1) ≤ (Nat.card (G.neighborSet v) : ℝ) ∧
          (Nat.card (G.neighborSet v) : ℝ) ≤ b*(Fintype.card V : ℝ)^(α-1)) ∧
        (∀ S : Finset V, 2*S.card ≤ Fintype.card V →
          a*(Fintype.card V : ℝ)^(α-1)*S.card ≤
            (Nat.card (Erdos713SwitchGluing.cross G (S : Set V)).edgeSet : ℝ)) ∧
        (∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → ¬ Nonempty (J ≃g H) →
          ∀ F : SimpleGraph V, ε*(Nat.card G.edgeSet : ℝ) ≤ (Nat.card F.edgeSet : ℝ) → J ⊑ F) := by
  classical
  obtain ⟨C,hC,hUpper⟩ := Erdos713Regularization.global_upper (lt_trans zero_lt_one hα) h.upper
  obtain ⟨a,R,ha,hR,hReg⟩ := robust_of_tight_rate H hα h hNoIso hProper
  refine ⟨a,2*R*C,ha,by positivity,?_⟩
  intro ε hε N
  obtain ⟨V,instV,G,d,hN,hVtwo,hFree,hBip,hE,hd,hD,hDeg,hCuts,hRobust⟩ := hReg ε hε N
  have hvr : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have he : (Nat.card G.edgeSet : ℝ) ≤ C*(Fintype.card V : ℝ)^α := by
    have hh := card_edgeFinset_le_extremalNumber hFree
    simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hh
    have hh' := hUpper (Fintype.card V)
    simp only [Fintype.card_eq_nat_card] at hh' ⊢
    exact (Nat.cast_le.mpr hh).trans hh'
  have hde : d*(Fintype.card V : ℝ) ≤ 2*(Nat.card G.edgeSet : ℝ) := by
    have hh := sum_le_sum (s := (univ : Finset V)) (fun v _ => (hDeg v).1)
    have hs : (∑ v : V, (Nat.card (G.neighborSet v) : ℝ)) = 2*(Nat.card G.edgeSet : ℝ) := by
      exact_mod_cast (by simpa only [← card_neighborSet_eq_degree,edgeFinset_card,
        Fintype.card_eq_nat_card] using G.sum_degrees_eq_twice_card_edges)
    simp only [sum_const,card_univ,nsmul_eq_mul] at hh
    rw [hs] at hh
    nlinarith
  have hdUpper : d ≤ 2*C*(Fintype.card V : ℝ)^(α-1) := by
    apply (mul_le_mul_iff_left₀ hvr).mp
    rw [rpow_factor hvr.le hα] at he
    nlinarith
  refine ⟨V,instV,G,hN,hVtwo,hFree,hBip,hE,?_,?_,hRobust⟩
  · intro v
    refine ⟨hD.trans (hDeg v).1, (hDeg v).2 |>.trans ?_⟩
    have hh := mul_le_mul_of_nonneg_left hdUpper hR.le
    nlinarith
  · intro S hS
    exact (mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg S.card)).trans (hCuts S hS)

#print axioms exists_tight_record
#print axioms of_positive_lower_sequence
#print axioms of_tight_rate
#print axioms uniform_proper_littleO
#print axioms robust_of_tight_rate
#print axioms robust_scaled
end Erdos713TightExpansion
