import Submission.TripleCommonDensity

/-!
Universal necessary common-neighbor counts at every balanced Zarankiewicz
critical exponent. These theorems do not construct an extremal family or
prove/disprove Erdős714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714CriticalCommonDensity
open Erdos714Packing Erdos714TripleCommonDensity
variable {A B : Type*} [Fintype A] [Fintype B]

def stars (S : A → Finset B) (s : ℕ) : ℕ :=
  ∑ g : Fin s ↪ B, (common (dual S) g).card

def maximalCommon (S : A → Finset B) (r : ℕ) : Finset (Fin r ↪ A) :=
  univ.filter (fun f => (common S f).card = r-1)

lemma first_moment (S : A → Finset B) (s : ℕ) (hs : 1 ≤ s) :
    ((∑ a, (S a).card) - (s-1)*Fintype.card A)^s ≤
      Fintype.card A^(s-1) * stars S s := by
  have h := truncated_moment (fun a => (S a).card) s hs
  have hc := Fintype.card_congr (Erdos714Unbalanced.starEquiv S s)
  simp only [Fintype.card_sigma, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_coe] at hc
  simpa only [hc, stars] using h

lemma second_moment (S : A → Finset B) (s : ℕ)
    (hfree : (completeBipartiteGraph (Fin (s+1)) (Fin (s+1))).Free (incidence S)) :
    (stars S s - s*Fintype.card (Fin s ↪ B))^(s+1) ≤
      Fintype.card (Fin s ↪ B)^s * (s.factorial*(maximalCommon S (s+1)).card) := by
  have h := truncated_moment
    (fun g : Fin s ↪ B => (common (dual S) g).card) (s+1) (by omega)
  have hc : (∑ f : Fin (s+1) ↪ A, (common S f).card.descFactorial s) =
      s.factorial*(maximalCommon S (s+1)).card := by
    have hb := (free_iff_common_card S (by omega : 0 < s+1)).mp hfree
    have hterm (f : Fin (s+1) ↪ A) : (common S f).card.descFactorial s =
        if (common S f).card = s then s.factorial else 0 := by
      by_cases he : (common S f).card = s
      · simp [he, Nat.descFactorial_self]
      · have hl : (common S f).card < s := by have := hb f; omega
        simp [he, Nat.descFactorial_of_lt hl]
    simp_rw [hterm]
    rw [← sum_filter]
    simp [maximalCommon, mul_comm]
  rw [← rectangle_count S (s+1) s, hc] at h
  simpa only [Nat.add_sub_cancel, stars] using h

/-- The critical common-neighbor bound, written with r=s+1 to keep all
exponent arithmetic explicit. Constants are deliberately nonsharp. -/
theorem critical_successor (S : A → Finset B) (s q C : ℕ) (hs : 1 ≤ s)
    (hC : 0 < C) (hq : 2*s*(2*C)^s ≤ q)
    (hA : Fintype.card A ≤ q^(s+1)) (hB : Fintype.card B ≤ q^(s+1))
    (hfree : (completeBipartiteGraph (Fin (s+1)) (Fin (s+1))).Free (incidence S))
    (he : q^(2*s+1) ≤ C*(∑ a, (S a).card)) :
    q^((s+1)^2) ≤ (2*(2*C)^s)^(s+1)*s.factorial*(maximalCommon S (s+1)).card := by
  let m := Fintype.card A
  let n := Fintype.card (Fin s ↪ B)
  let e := ∑ a, (S a).card
  let T := stars S s
  let Z := (maximalCommon S (s+1)).card
  let K := (2*C)^s
  let d := (s+1)*s
  have hK : 0 < K := by dsimp [K]; positivity
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity : 0 < 2*s*(2*C)^s) hq
  have hCK : 2*C ≤ K := by
    simpa only [pow_one] using
      pow_le_pow_right' (show 1 ≤ 2*C by omega) hs
  have hoffcoef : 2*C*(s-1) ≤ q := by
    calc
      _ ≤ K*s := Nat.mul_le_mul hCK (by omega)
      _ ≤ 2*s*K := by nlinarith
      _ ≤ q := hq
  have hm : m ≤ q^(s+1) := hA
  have hn : n ≤ q^d := by
    calc
      n = (Fintype.card B).descFactorial s := by simp [n]
      _ ≤ (Fintype.card B)^s := Nat.descFactorial_le_pow _ _
      _ ≤ (q^(s+1))^s := Nat.pow_le_pow_left hB s
      _ = _ := by rw [← pow_mul]
  have hoff : 2*C*(s-1)*m ≤ q^(2*s+1) := by
    calc
      _ ≤ q*q^(s+1) := Nat.mul_le_mul hoffcoef hm
      _ = q^(s+2) := by rw [pow_succ]; ring
      _ ≤ _ := pow_le_pow_right' hq0 (by omega)
  have he' : q^(2*s+1) ≤ 2*C*(e-(s-1)*m) := by
    have ht : e ≤ (e-(s-1)*m)+(s-1)*m := by omega
    have ht' := Nat.mul_le_mul_left C ht
    change q^(2*s+1) ≤ C*e at he
    nlinarith
  have hfirst : (e-(s-1)*m)^s ≤ m^(s-1)*T := first_moment S s hs
  have hexp : (s+1)*(s-1)+(d+1) = (2*s+1)*s := by
    dsimp [d]
    have : s-1+1=s := by omega
    nlinarith
  have hT : q^(d+1) ≤ K*T := by
    have hh : q^((s+1)*(s-1))*q^(d+1) ≤
        q^((s+1)*(s-1))*(K*T) := by
      calc
        _ = (q^(2*s+1))^s := by rw [← pow_add, hexp, pow_mul]
        _ ≤ (2*C*(e-(s-1)*m))^s := Nat.pow_le_pow_left he' s
        _ = K*(e-(s-1)*m)^s := by rw [mul_pow]
        _ ≤ K*(m^(s-1)*T) := Nat.mul_le_mul_left _ hfirst
        _ ≤ K*((q^(s+1))^(s-1)*T) := by gcongr
        _ = _ := by rw [← pow_mul]; ring
    exact Nat.le_of_mul_le_mul_left hh (by positivity)
  have hToff : 2*s*K*n ≤ q^(d+1) := by
    calc
      _ ≤ q*q^d := Nat.mul_le_mul hq hn
      _ = _ := by rw [pow_succ]; ring
  have hT' : q^(d+1) ≤ 2*K*(T-s*n) := by
    have ht : T ≤ (T-s*n)+s*n := by omega
    have ht' := Nat.mul_le_mul_left K ht
    nlinarith
  have hsecond : (T-s*n)^(s+1) ≤ n^s*(s.factorial*Z) := second_moment S s hfree
  have hexp' : d*s+(s+1)^2 = (d+1)*(s+1) := by dsimp [d]; ring
  have hh : q^(d*s)*q^((s+1)^2) ≤
      q^(d*s)*((2*K)^(s+1)*s.factorial*Z) := by
    calc
      _ = (q^(d+1))^(s+1) := by rw [← pow_add, hexp', pow_mul]
      _ ≤ (2*K*(T-s*n))^(s+1) := Nat.pow_le_pow_left hT' (s+1)
      _ = (2*K)^(s+1)*(T-s*n)^(s+1) := mul_pow _ _ _
      _ ≤ (2*K)^(s+1)*(n^s*(s.factorial*Z)) := Nat.mul_le_mul_left _ hsecond
      _ ≤ (2*K)^(s+1)*((q^d)^s*(s.factorial*Z)) := by gcongr
      _ = _ := by rw [← pow_mul]; ring
  exact Nat.le_of_mul_le_mul_left hh (by positivity)

/-- An r-tuple attaining the maximum allowed common-neighbor size must occur
on a positive proportion of the critical q^(r*r) scale. -/
theorem critical_maximal_common (S : A → Finset B) (r q C : ℕ) (hr : 2 ≤ r)
    (hC : 0 < C) (hq : 2*(r-1)*(2*C)^(r-1) ≤ q)
    (hA : Fintype.card A ≤ q^r) (hB : Fintype.card B ≤ q^r)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free (incidence S))
    (he : q^(2*r-1) ≤ C*(∑ a, (S a).card)) :
    q^(r^2) ≤ (2*(2*C)^(r-1))^r*(r-1).factorial*(maximalCommon S r).card := by
  obtain ⟨s, rfl⟩ : ∃ s, r=s+1 := ⟨r-1, by omega⟩
  have he' : 2*(s+1)-1=2*s+1 := by omega
  simpa only [Nat.add_sub_cancel] using
    critical_successor S s q C (by omega) hC
      (by simpa only [Nat.add_sub_cancel] using hq) hA hB hfree
      (by simpa only [he'] using he)

/-- A bound on the exceptional r-tuples is an explicit hypothesis; no
geometric dimension estimate or counting theorem is assumed implicitly. -/
theorem exceptional_budget (S : A → Finset B) (r q C D : ℕ) (hr : 2 ≤ r)
    (hC : 0 < C) (hq : 2*(r-1)*(2*C)^(r-1) ≤ q)
    (hA : Fintype.card A ≤ q^r) (hB : Fintype.card B ≤ q^r)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free (incidence S))
    (he : q^(2*r-1) ≤ C*(∑ a, (S a).card))
    (X : Finset (Fin r ↪ A)) (hX : X.card ≤ D*q^(r^2-1))
    (hgood : ∀ f, f ∉ X → (common S f).card ≤ r-2) :
    q ≤ (2*(2*C)^(r-1))^r*(r-1).factorial*D := by
  have hsub : maximalCommon S r ⊆ X := by
    intro f hf
    have hf' := (mem_filter.mp hf).2
    by_contra hn
    have := hgood f hn
    omega
  have hb := critical_maximal_common S r q C hr hC hq hA hB hfree he
  have hq0 : 0 < q := by
    have hs : 0 < r-1 := by omega
    exact lt_of_lt_of_le (by positivity : 0 < 2*(r-1)*(2*C)^(r-1)) hq
  have hr2 : 1 ≤ r^2 := by nlinarith
  have hh : q^(r^2-1)*q ≤
      q^(r^2-1)*((2*(2*C)^(r-1))^r*(r-1).factorial*D) := by
    calc
      _ = q^(r^2) := by rw [← pow_succ, Nat.sub_add_cancel hr2]
      _ ≤ (2*(2*C)^(r-1))^r*(r-1).factorial*(maximalCommon S r).card := hb
      _ ≤ (2*(2*C)^(r-1))^r*(r-1).factorial*(D*q^(r^2-1)) :=
        Nat.mul_le_mul_left _ ((card_le_card hsub).trans hX)
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (by positivity)

variable {F : Type*} [Field F]

lemma separable_not_degree_sub_one (p : Polynomial F) (r : ℕ) (hr : 1 ≤ r)
    (hd : p.natDegree = r) (hs : p.Separable) :
    p.roots.toFinset.card ≠ r-1 := by
  intro hc
  have hc' : p.roots.card = r-1 := by
    simpa only [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs)] using hc
  obtain ⟨u, _, hsum, hu⟩ := p.exists_prod_multiset_X_sub_C_mul
  have hud : u.natDegree ≤ 1 := by omega
  have hsplit := (Polynomial.Splits.of_natDegree_le_one hud).natDegree_eq_card_roots
  rw [hu, Multiset.card_zero] at hsplit
  omega

/-- Conditional exclusion of exact degree-r separable root models. Equality
with the ALL-root count is essential; a root injection is not sufficient. -/
theorem separable_root_model_budget (S : A → Finset B) (r q C D : ℕ) (hr : 2 ≤ r)
    (hC : 0 < C) (hq : 2*(r-1)*(2*C)^(r-1) ≤ q)
    (hA : Fintype.card A ≤ q^r) (hB : Fintype.card B ≤ q^r)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free (incidence S))
    (he : q^(2*r-1) ≤ C*(∑ a, (S a).card))
    (X : Finset (Fin r ↪ A)) (hX : X.card ≤ D*q^(r^2-1))
    (p : (Fin r ↪ A) → Polynomial F)
    (hmodel : ∀ f, f ∉ X → (p f).natDegree = r ∧ (p f).Separable ∧
      (common S f).card = (p f).roots.toFinset.card) :
    q ≤ (2*(2*C)^(r-1))^r*(r-1).factorial*D := by
  apply exceptional_budget S r q C D hr hC hq hA hB hfree he X hX
  intro f hf
  obtain ⟨hd, hs, hc⟩ := hmodel f hf
  have hb := (free_iff_common_card S (by omega : 0 < r)).mp hfree f
  have hn := separable_not_degree_sub_one (p f) r (by omega) hd hs
  omega

variable {V : Type*} [Fintype V]

lemma neighbor_incidence_free (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (hr : 0 < r)
    (hG : (completeBipartiteGraph (Fin r) (Fin r)).Free G) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free
      (incidence (fun v => G.neighborFinset v)) := by
  apply (free_iff_no_rectangle _ hr).mpr
  intro f g h
  apply hG
  refine ⟨Copy.completeBipartiteGraph (univ.map f) (univ.map g)
    (by simp) (by simp) ?_⟩
  intro v hv w hw
  change v ∈ univ.map f at hv
  change w ∈ univ.map g at hw
  obtain ⟨i, _, rfl⟩ := mem_map.mp hv
  obtain ⟨j, _, rfl⟩ := mem_map.mp hw
  exact (G.mem_neighborFinset _ _).mp (h i j)

/-- Direct version for arbitrary simple graphs, using their actual common
neighbors. The graph itself need not be bipartite. -/
theorem graph_critical_maximal_common (G : SimpleGraph V) [DecidableRel G.Adj]
    (r q C : ℕ) (hr : 2 ≤ r) (hC : 0 < C)
    (hq : 2*(r-1)*(2*C)^(r-1) ≤ q) (hV : Fintype.card V ≤ q^r)
    (hG : (completeBipartiteGraph (Fin r) (Fin r)).Free G)
    (he : q^(2*r-1) ≤ C*G.edgeFinset.card) :
    q^(r^2) ≤ (2*(2*C)^(r-1))^r*(r-1).factorial*
      (maximalCommon (fun v => G.neighborFinset v) r).card := by
  apply critical_maximal_common (fun v => G.neighborFinset v) r q C hr hC hq hV hV
    (neighbor_incidence_free G r (by omega) hG)
  have hd : (∑ v, (G.neighborFinset v).card) = 2*G.edgeFinset.card := by
    simpa only [card_neighborFinset_eq_degree] using G.sum_degrees_eq_twice_card_edges
  rw [hd]
  exact he.trans (Nat.mul_le_mul_left C (by omega))

#print axioms neighbor_incidence_free
#print axioms graph_critical_maximal_common
#print axioms first_moment
#print axioms second_moment
#print axioms critical_successor
#print axioms critical_maximal_common
#print axioms exceptional_budget
#print axioms separable_not_degree_sub_one
#print axioms separable_root_model_budget
end Erdos714CriticalCommonDensity
