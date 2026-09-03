import Submission.BinaryWeightedCertificates

/-! A short lower-mean cycle is necessary for a successful binary weighted
certificate. This is a proof-method condition, not a settlement of Erdős406. -/

namespace Erdos406BinaryWeightedCycles
open Erdos406BinaryWeighted Erdos406AffinePotential Erdos406GroupedCertificate

abbrev Binary (w : List ℕ) : Prop := ∀ d ∈ w, d < 2

def cost {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ) (a : ℝ)
    (s : σ) (L : List ℕ) : ℝ := weightFrom D w s L - a * L.length

lemma weight_append {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ)
    (s : σ) (u v : List ℕ) :
    weightFrom D w s (u ++ v) = weightFrom D w s u + weightFrom D w (D.evalFrom s u) v := by
  induction u generalizing s with
  | nil => simp [weightFrom]
  | cons d u ih => simp only [List.cons_append, weightFrom, DFA.evalFrom_cons, ih]; ring

lemma cost_append {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℝ) (a : ℝ)
    (s : σ) (u v : List ℕ) :
    cost D w a s (u ++ v) = cost D w a s u + cost D w a (D.evalFrom s u) v := by
  simp only [cost, weight_append, List.length_append, Nat.cast_add]
  ring

variable {σ : Type*} [Fintype σ]

/-- If every short reachable loop has nonnegative adjusted cost, loop removal
reduces an arbitrary word to a shorter one without increasing its cost. -/
lemma shorten (D : DFA ℕ σ) (w : σ → ℕ → ℝ) (a : ℝ) (G : σ → Prop)
    (hG : ∀ s d, d < 2 → G s → G (D.step s d))
    (hloop : ∀ s, G s → ∀ L : List ℕ, Binary L → L.length ≤ Fintype.card σ →
      D.evalFrom s L = s → 0 ≤ cost D w a s L) (L : List ℕ) :
    ∀ s, G s → Binary L → ∃ U : List ℕ, Binary U ∧ U.length < Fintype.card σ ∧
      D.evalFrom s U = D.evalFrom s L ∧ cost D w a s U ≤ cost D w a s L := by
  induction hLlen : L.length using Nat.strong_induction_on generalizing L with
  | h k ih =>
    intro s hs hL
    by_cases hsmall : L.length < Fintype.card σ
    · exact ⟨L, hL, hsmall, rfl, le_rfl⟩
    obtain ⟨q, u, v, z, he, huv, hv, huq, hvq, hzq⟩ :=
      D.evalFrom_split (s := s) (by omega : Fintype.card σ ≤ L.length) rfl
    have hu : Binary u := by
      intro d hd
      apply hL d
      rw [he]
      simp only [List.mem_append]
      exact Or.inl (Or.inl hd)
    have hvm : Binary v := by
      intro d hd
      apply hL d
      rw [he]
      simp only [List.mem_append]
      exact Or.inl (Or.inr hd)
    have hz : Binary z := by
      intro d hd
      apply hL d
      rw [he]
      simp only [List.mem_append]
      exact Or.inr hd
    have hnew : Binary (u ++ z) := by
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hu d hd
      · exact hz d hd
    have hlen : (u ++ z).length < L.length := by
      have hvpos : 0 < v.length := List.length_pos_iff.mpr hv
      rw [he]
      simp only [List.length_append]
      omega
    have hGq : G q := by
      rw [← huq]
      exact reachable_word D (fun d => d < 2) G hG u hu s hs
    have hvnonneg := hloop q hGq v hvm (by omega) hvq
    obtain ⟨U, hU, hUs, hUeval, hUcost⟩ := ih (u ++ z).length (by omega) (u ++ z) rfl s hs hnew
    refine ⟨U, hU, hUs, ?_, ?_⟩
    · rw [hUeval, DFA.evalFrom_of_append, huq]
      exact hzq
    · apply hUcost.trans
      rw [he]
      simp only [cost_append, DFA.evalFrom_of_append, huq, hvq]
      linarith

/-- Nonnegative short loop costs imply a uniform lower bound on all valid
paths from the reachable predicate. -/
lemma lower_bound_of_short_loops (D : DFA ℕ σ) (w : σ → ℕ → ℝ) (a : ℝ) (G : σ → Prop)
    (hG : ∀ s d, d < 2 → G s → G (D.step s d))
    (hloop : ∀ s, G s → ∀ L : List ℕ, Binary L → L.length ≤ Fintype.card σ →
      D.evalFrom s L = s → 0 ≤ cost D w a s L) :
    ∃ B : ℝ, ∀ s, G s → ∀ L : List ℕ, Binary L → -B ≤ cost D w a s L := by
  classical
  obtain ⟨m, hm⟩ := (Set.finite_range (fun p : σ × Fin 2 => w p.1 p.2.val - a)).bddBelow
  have hedge (s : σ) (d : ℕ) (hd : d < 2) : -|m| ≤ w s d - a :=
    (neg_abs_le m).trans (hm ⟨(s, ⟨d, hd⟩), rfl⟩)
  have hall : ∀ L : List ℕ, Binary L → ∀ s, -|m| * L.length ≤ cost D w a s L := by
    intro L
    induction L with
    | nil => intro h s; simp [cost, weightFrom]
    | cons d L ih =>
      intro h s
      have hd := hedge s d (h d (List.mem_cons_self ..))
      have ht := ih (fun e he => h e (List.mem_cons_of_mem _ he)) (D.step s d)
      simp only [cost, weightFrom, List.length_cons, Nat.cast_add, Nat.cast_one] at ht ⊢
      linarith
  refine ⟨|m| * Fintype.card σ, ?_⟩
  intro s hs L hL
  obtain ⟨U, hU, hUs, _, hUcost⟩ := shorten D w a G hG hloop L s hs hL
  have hh := hall U hU s
  have hlen : (U.length : ℝ) ≤ Fintype.card σ := by exact_mod_cast hUs.le
  have hm0 : 0 ≤ |m| := abs_nonneg m
  nlinarith

lemma binary_digits_head {n : ℕ} (hn : 0 < n) :
    ∃ L : List ℕ, (Nat.digits 2 n).reverse = 1 :: L ∧ Binary L := by
  have hne : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (ne_of_gt hn)
  have hlast : (Nat.digits 2 n).getLast hne = 1 := by
    have hlt := Nat.digits_lt_base (by decide : 1 < 2) (List.getLast_mem hne)
    have hz := Nat.getLast_digit_ne_zero 2 (ne_of_gt hn)
    omega
  have he := List.dropLast_append_getLast hne
  rw [hlast] at he
  refine ⟨(Nat.digits 2 n).dropLast.reverse, ?_, ?_⟩
  · rw [← he, List.reverse_append]
    simp
  · intro d hd
    exact Nat.digits_lt_base (by decide) (List.mem_of_mem_dropLast (List.mem_reverse.mp hd))

lemma global_lower_of_short_loops (D : DFA ℕ σ) (w : σ → ℕ → ℝ) (a : ℝ) (G : σ → Prop)
    (hstart : G (D.step D.start 1))
    (hG : ∀ s d, d < 2 → G s → G (D.step s d))
    (hloop : ∀ s, G s → ∀ L : List ℕ, Binary L → L.length ≤ Fintype.card σ →
      D.evalFrom s L = s → 0 ≤ cost D w a s L) :
    ∃ B : ℝ, ∀ n : ℕ, 0 < n →
      a * (Nat.digits 2 n).length - B ≤ Erdos406BinaryWeighted.weightNat D w n := by
  obtain ⟨B, hB⟩ := lower_bound_of_short_loops D w a G hG hloop
  refine ⟨B + a - w D.start 1, ?_⟩
  intro n hn
  obtain ⟨L, hL, hbin⟩ := binary_digits_head hn
  have hh := hB _ hstart L hbin
  have hlen := congrArg List.length hL
  simp only [List.length_reverse, List.length_cons] at hlen
  rw [Erdos406BinaryWeighted.weightNat, hL, weightFrom, hlen]
  dsimp only [cost] at hh
  push_cast
  linarith

/-- A supercritical finite weighted certificate must have a reachable short
loop of strictly smaller mean. The start state's padding-zero loop is NOT
counted: reachability begins after the leading binary digit one. -/
theorem lower_mean_short_loop_necessary (C : Construction σ) (a : ℝ)
    (hcrit : Real.log 2 < a * Real.log 3) :
    ∃ u L : List ℕ, Binary u ∧ Binary L ∧ L ≠ [] ∧ L.length ≤ Fintype.card σ ∧
      let s := C.D.evalFrom (C.D.step C.D.start 1) u
      C.D.evalFrom s L = s ∧ weightFrom C.D C.w s L < a * L.length := by
  classical
  let G : σ → Prop := fun s => ∃ u : List ℕ, Binary u ∧
    C.D.evalFrom (C.D.step C.D.start 1) u = s
  have hgstart : G (C.D.step C.D.start 1) := ⟨[], by simp [Binary], rfl⟩
  have hgstep : ∀ s d, d < 2 → G s → G (C.D.step s d) := by
    rintro s d hd ⟨u, hu, rfl⟩
    refine ⟨u ++ [d], ?_, ?_⟩
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hu e he
      · simpa only [List.mem_singleton.mp he] using hd
    · exact C.D.evalFrom_append_singleton _ _ _
  by_contra hnot
  have hloop : ∀ s, G s → ∀ L : List ℕ, Binary L → L.length ≤ Fintype.card σ →
      C.D.evalFrom s L = s → 0 ≤ cost C.D C.w a s L := by
    rintro s ⟨u, hu, rfl⟩ L hL hlen he
    by_contra hn
    have hneg : cost C.D C.w a (C.D.evalFrom (C.D.step C.D.start 1) u) L < 0 := lt_of_not_ge hn
    have hne : L ≠ [] := by intro hz; simp [hz, cost, weightFrom] at hneg
    apply hnot
    refine ⟨u, L, hu, hL, hne, hlen, he, ?_⟩
    dsimp [cost] at hneg
    linarith
  obtain ⟨B, hB⟩ := global_lower_of_short_loops C.D C.w a G hgstart hgstep hloop
  exact not_supercritical_of_global_binary_lower_bound
    (Erdos406BinaryWeighted.weightNat C.D C.w) a B C.construction_bound hB hcrit

#print axioms lower_mean_short_loop_necessary
end Erdos406BinaryWeightedCycles
