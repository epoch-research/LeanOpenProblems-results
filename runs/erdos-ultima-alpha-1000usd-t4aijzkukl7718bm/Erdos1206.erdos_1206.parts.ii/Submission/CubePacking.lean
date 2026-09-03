import Submission.SmoothHarmonicFinite

/-! Finite fractional packings give global upper density bounds. No vanishing
family of such bounds is asserted. -/

namespace Erdos1206
open Finset

structure CubePackingEdge where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  weight : ℕ
  deriving DecidableEq, Repr

namespace CubePackingEdge

def roots (e : CubePackingEdge) : List ℕ := [e.a,e.b,e.c,e.d]
def Good (e : CubePackingEdge) : Prop :=
  0 < e.a ∧ e.a < e.b ∧ e.b < e.c ∧ e.c < e.d ∧
  e.a^3+e.d^3=e.b^3+e.c^3
instance (e : CubePackingEdge) : Decidable e.Good := inferInstanceAs (Decidable
  (0 < e.a ∧ e.a < e.b ∧ e.b < e.c ∧ e.c < e.d ∧ e.a^3+e.d^3=e.b^3+e.c^3))

lemma missing {e : CubePackingEdge} (he : e.Good) {S : Finset ℕ}
    (hS : IsSidon ((fun n : ℕ => n^3) '' (S : Set ℕ))) :
    ∃ n ∈ e.roots, n ∉ S := by
  by_contra! h
  have ha := h e.a (by simp [roots])
  have hb := h e.b (by simp [roots])
  have hc := h e.c (by simp [roots])
  have hd := h e.d (by simp [roots])
  have hh := hS _ ⟨e.a,ha,rfl⟩ _ ⟨e.b,hb,rfl⟩ _ ⟨e.d,hd,rfl⟩
    _ ⟨e.c,hc,rfl⟩ he.2.2.2.2
  have hab : e.a^3 ≠ e.b^3 := (Nat.pow_lt_pow_left he.2.1 (by decide)).ne
  have hac : e.a^3 ≠ e.c^3 :=
    (Nat.pow_lt_pow_left (he.2.1.trans he.2.2.1) (by decide)).ne
  exact hh.elim (fun q => hab q.1) (fun q => hac q.1)

end CubePackingEdge

def cubePackingMass (L : List CubePackingEdge) : ℕ := (L.map (·.weight)).sum

def cubePackingLoad (L : List CubePackingEdge) (n : ℕ) : ℕ :=
  (L.map (fun e => if n ∈ e.roots then e.weight else 0)).sum

def cubePackingLoadFast : List CubePackingEdge → ℕ → ℕ
  | [], _ => 0
  | e :: L, n =>
      (if n == e.a || n == e.b || n == e.c || n == e.d then e.weight else 0) +
        cubePackingLoadFast L n

lemma cubePackingLoadFast_eq (L : List CubePackingEdge) (n : ℕ) :
    cubePackingLoadFast L n = cubePackingLoad L n := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp [cubePackingLoadFast,cubePackingLoad,CubePackingEdge.roots,ih,or_assoc]

lemma cubePacking_missing_mass {L : List CubePackingEdge} {V S : Finset ℕ}
    (hV : ∀ e ∈ L, ∀ n ∈ e.roots, n ∈ V)
    (hL : ∀ e ∈ L, e.Good)
    (hS : IsSidon ((fun n : ℕ => n^3) '' (S : Set ℕ))) :
    cubePackingMass L ≤ ∑ n ∈ V \ S, cubePackingLoad L n := by
  induction L with
  | nil => simp [cubePackingMass,cubePackingLoad]
  | cons e L ih =>
    have he := hL e (by simp)
    obtain ⟨n,hn,hnS⟩ := e.missing he hS
    have hnV : n ∈ V \ S := mem_sdiff.mpr ⟨hV e (by simp) n hn,hnS⟩
    have hw : e.weight ≤ ∑ m ∈ V \ S, if m ∈ e.roots then e.weight else 0 := by
      have hh := single_le_sum (f := fun m => if m ∈ e.roots then e.weight else 0)
        (fun _ _ => Nat.zero_le _) hnV
      simpa [hn] using hh
    have hi := ih (fun e he => hV e (by simp [he])) (fun e he => hL e (by simp [he]))
    simp only [cubePackingMass,List.map_cons,List.sum_cons] at hi ⊢
    have heq : (∑ n ∈ V \ S, cubePackingLoad (e :: L) n) =
        (∑ n ∈ V \ S, if n ∈ e.roots then e.weight else 0) +
        ∑ n ∈ V \ S, cubePackingLoad L n := by
      simp [cubePackingLoad,Finset.sum_add_distrib]
    rw [heq]
    exact add_le_add hw hi

/-- The capacity condition is integral, so concrete certificates do not need
floating-point arithmetic. -/
lemma smooth_harmonic_bound_of_cube_packing (P : Finset ℕ) (M : ℕ) (hM : 0 < M)
    (L : List CubePackingEdge)
    (hL : ∀ e ∈ L, e.Good)
    (hP : ∀ e ∈ L, ∀ n ∈ e.roots, n ∈ Nat.factoredNumbers P)
    (hcap : ∀ e ∈ L, ∀ n ∈ e.roots, n * cubePackingLoad L n ≤ M) :
    SmoothCubeHarmonicBound P
      (smoothReciprocalMass P - (cubePackingMass L : ℝ) / M) := by
  classical
  intro S hS hsid
  let V : Finset ℕ := (L.flatMap (·.roots)).toFinset
  have hV (n : ℕ) : n ∈ V ↔ ∃ e ∈ L, n ∈ e.roots := by
    simp [V]
  have hvP {n : ℕ} (hn : n ∈ V) : n ∈ Nat.factoredNumbers P := by
    obtain ⟨e,he,hn⟩ := (hV n).mp hn
    exact hP e he n hn
  have hvpos {n : ℕ} (hn : n ∈ V) : 0 < n :=
    Nat.pos_of_ne_zero (hvP hn).1
  have hc {n : ℕ} (hn : n ∈ V) :
      (cubePackingLoad L n : ℝ) ≤ (M : ℝ) / n := by
    obtain ⟨e,he,hne⟩ := (hV n).mp hn
    have hh : (n : ℝ) * cubePackingLoad L n ≤ M := by exact_mod_cast hcap e he n hne
    apply (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hvpos hn)).mpr
    nlinarith
  have hm := cubePacking_missing_mass
    (fun e he n hn => (hV n).mpr ⟨e,he,hn⟩) hL hsid
  have hmR : (cubePackingMass L : ℝ) ≤ ∑ n ∈ V \ S, (cubePackingLoad L n : ℝ) := by
    exact_mod_cast hm
  have hcapR : (cubePackingMass L : ℝ) ≤
      (M : ℝ) * ∑ n ∈ V \ S, (1 : ℝ) / n := by
    calc
      _ ≤ ∑ n ∈ V \ S, (cubePackingLoad L n : ℝ) := hmR
      _ ≤ ∑ n ∈ V \ S, (M : ℝ) / n :=
        sum_le_sum fun n hn => hc (mem_sdiff.mp hn).1
      _ = _ := by simp [mul_sum,div_eq_mul_inv]
  have hmiss : (cubePackingMass L : ℝ) / M ≤ ∑ n ∈ V \ S, (1 : ℝ) / n := by
    apply (div_le_iff₀ (show (0 : ℝ) < M by exact_mod_cast hM)).mpr
    nlinarith
  have hu := finite_smooth_reciprocal_bound (P := P) (S := S ∪ (V \ S)) (by
    intro n hn
    rcases mem_union.mp hn with hn | hn
    · exact hS n hn
    · exact hvP (mem_sdiff.mp hn).1)
  rw [sum_union (disjoint_left.mpr (by
    intro n hn hm
    exact (mem_sdiff.mp hm).2 hn))] at hu
  linarith

lemma cubePacking_total_load {L : List CubePackingEdge} {V : Finset ℕ}
    (hV : ∀ e ∈ L, ∀ n ∈ e.roots, n ∈ V)
    (hL : ∀ e ∈ L, e.Good) :
    (∑ n ∈ V, cubePackingLoad L n) = 4 * cubePackingMass L := by
  induction L with
  | nil => simp [cubePackingLoad,cubePackingMass]
  | cons e L ih =>
    have he := hL e (by simp)
    have hn : e.roots.Nodup := by
      rcases he with ⟨ha,hab,hbc,hcd,heq⟩
      simp [CubePackingEdge.roots]
      omega
    have hcard : e.roots.toFinset.card = 4 := by
      rw [List.toFinset_card_of_nodup hn]
      rfl
    have hf : V.filter (fun n => n ∈ e.roots) = e.roots.toFinset := by
      ext n
      simp only [mem_filter,List.mem_toFinset]
      exact ⟨And.right,fun hh => ⟨hV e (by simp) n hh,hh⟩⟩
    have hfirst : (∑ n ∈ V, if n ∈ e.roots then e.weight else 0) = 4 * e.weight := by
      rw [← sum_filter,hf,sum_const,hcard,nsmul_eq_mul]
      norm_num
    have hi := ih (fun e he => hV e (by simp [he])) (fun e he => hL e (by simp [he]))
    have hsplit : (∑ n ∈ V, cubePackingLoad (e :: L) n) =
        (∑ n ∈ V, if n ∈ e.roots then e.weight else 0) + ∑ n ∈ V, cubePackingLoad L n := by
      simp [cubePackingLoad,sum_add_distrib]
    rw [hsplit,hfirst,hi]
    simp [cubePackingMass,mul_add]

/-- Four-vertex fractional packings cannot remove more than one quarter of
all smooth reciprocal mass. In particular this method alone cannot produce
vanishing normalized upper bounds. -/
lemma cube_packing_fractional_barrier (P : Finset ℕ) (M : ℕ) (hM : 0 < M)
    (L : List CubePackingEdge)
    (hL : ∀ e ∈ L, e.Good)
    (hP : ∀ e ∈ L, ∀ n ∈ e.roots, n ∈ Nat.factoredNumbers P)
    (hcap : ∀ e ∈ L, ∀ n ∈ e.roots, n * cubePackingLoad L n ≤ M) :
    (cubePackingMass L : ℝ) / M ≤ smoothReciprocalMass P / 4 := by
  classical
  let V : Finset ℕ := (L.flatMap (·.roots)).toFinset
  have hV (n : ℕ) : n ∈ V ↔ ∃ e ∈ L, n ∈ e.roots := by simp [V]
  have hvP {n : ℕ} (hn : n ∈ V) : n ∈ Nat.factoredNumbers P := by
    obtain ⟨e,he,hn⟩ := (hV n).mp hn
    exact hP e he n hn
  have htotal := cubePacking_total_load
    (fun e he n hn => (hV n).mpr ⟨e,he,hn⟩) hL
  have htotalR : (∑ n ∈ V, (cubePackingLoad L n : ℝ)) = 4 * cubePackingMass L := by
    exact_mod_cast htotal
  have hload : (4 : ℝ) * cubePackingMass L ≤ (M : ℝ) * smoothReciprocalMass P := by
    rw [← htotalR]
    calc
      _ ≤ ∑ n ∈ V, (M : ℝ) / n := by
        apply sum_le_sum
        intro n hn
        have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (hvP hn).1
        obtain ⟨e,he,hne⟩ := (hV n).mp hn
        apply (le_div_iff₀ hnpos).mpr
        have hh : (n : ℝ) * cubePackingLoad L n ≤ M := by exact_mod_cast hcap e he n hne
        nlinarith
      _ = (M : ℝ) * ∑ n ∈ V, (1 : ℝ) / n := by simp [mul_sum,div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left (finite_smooth_reciprocal_bound (fun n hn => hvP hn))
        (Nat.cast_nonneg M)
  apply (div_le_iff₀ (show (0 : ℝ) < M by exact_mod_cast hM)).mpr
  nlinarith

#print axioms cube_packing_fractional_barrier

#print axioms smooth_harmonic_bound_of_cube_packing
end Erdos1206
