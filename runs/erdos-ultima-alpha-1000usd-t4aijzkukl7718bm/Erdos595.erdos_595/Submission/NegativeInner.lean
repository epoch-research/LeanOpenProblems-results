import Submission.Work

/-!
Auxiliary obstruction for Erdős 595: finite-support real vectors with negative
inner product admit countable triangle-free edge covers. This file does not
settle the original conjecture.
-/

open SimpleGraph Set
open scoped BigOperators

namespace Erdos595NegativeInner

structure Packet (I : Type*) where
  size : ℕ
  coord : Fin size ↪ I
  value : Fin size → ℝ

abbrev Pattern := Σ n : ℕ, Σ m : ℕ,
  (Fin n → Bool) × (Fin m → Bool) × (Fin n → Fin m → Bool)

noncomputable def pairCode {I : Type*} (a b : Packet I) : Pattern := by
  classical
  exact ⟨a.size, b.size, (fun i => decide (0 ≤ a.value i)),
    (fun j => decide (0 ≤ b.value j)), (fun i j => decide (a.coord i = b.coord j))⟩

noncomputable def dot {I : Type*} (a b : Packet I) : ℝ := by
  classical
  exact ∑ i, ∑ j, if a.coord i = b.coord j then a.value i * b.value j else 0

/-- In a triple with identical ordered pair patterns, all coordinate
coincidences are diagonal, and the corresponding coefficients have equal signs. -/
theorem dot_nonneg_of_same_pattern {I : Type*} (a b c : Packet I)
    (habc : pairCode a b = pairCode a c)
    (habbc : pairCode a b = pairCode b c) : 0 ≤ dot a b := by
  classical
  have hsize₁ := congrArg Sigma.fst habbc
  have hsize₂ := congrArg (fun x : Pattern => x.2.1) habc
  rcases a with ⟨na, ia, va⟩
  rcases b with ⟨nb, ib, vb⟩
  rcases c with ⟨nc, ic, vc⟩
  dsimp only [pairCode] at hsize₁ hsize₂
  subst nb
  subst nc
  have h₁ : ((fun i => decide (0 ≤ va i)), (fun i => decide (0 ≤ vb i)),
      (fun i j => decide (ia i = ib j))) =
      ((fun i => decide (0 ≤ va i)), (fun i => decide (0 ≤ vc i)),
      (fun i j => decide (ia i = ic j))) := by
    simpa only [pairCode, Sigma.mk.inj_iff, heq_eq_eq, true_and] using habc
  have h₂ : ((fun i => decide (0 ≤ va i)), (fun i => decide (0 ≤ vb i)),
      (fun i j => decide (ia i = ib j))) =
      ((fun i => decide (0 ≤ vb i)), (fun i => decide (0 ≤ vc i)),
      (fun i j => decide (ib i = ic j))) := by
    simpa only [pairCode, Sigma.mk.inj_iff, heq_eq_eq, true_and] using habbc
  have hsign : ∀ i, (0 ≤ va i ↔ 0 ≤ vb i) := by
    intro i
    have hh := congrFun (congrArg Prod.fst h₂) i
    simpa only [decide_eq_decide] using hh
  have hm₁ : ∀ i j, (ia i = ib j ↔ ia i = ic j) := by
    intro i j
    have hh := congrFun (congrFun (congrArg (fun x => x.2.2) h₁) i) j
    simpa only [decide_eq_decide] using hh
  have hm₂ : ∀ i j, (ia i = ib j ↔ ib i = ic j) := by
    intro i j
    have hh := congrFun (congrFun (congrArg (fun x => x.2.2) h₂) i) j
    simpa only [decide_eq_decide] using hh
  unfold dot
  dsimp only
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs with hij
  · have he : i = j := ib.injective ((hm₂ i j).mp hij |>.trans
      (((hm₁ i j).mp hij).symm.trans hij))
    subst j
    by_cases hi : 0 ≤ va i
    · exact mul_nonneg hi ((hsign i).mp hi)
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hi)
        (le_of_not_ge (fun h => hi ((hsign i).mpr h)))
  · exact le_rfl

#print axioms dot_nonneg_of_same_pattern

/-- Countably many ordered edge patterns suffice when none is shared by all
three edges of an increasing triangle. -/
theorem cover_of_ordered_patterns {V C : Type*} [LinearOrder V] [Countable C]
    (G : SimpleGraph V) (code : V → V → C)
    (hc : ∀ a b c, a < b → b < c → G.Adj a b → G.Adj a c → G.Adj b c →
      ¬(code a b = code a c ∧ code a b = code b c)) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  classical
  letI : Encodable C := Encodable.ofCountable C
  let F : C → SimpleGraph V := fun k =>
    { Adj := fun a b => G.Adj a b ∧ code (min a b) (max a b) = k
      symm := fun a b h => ⟨h.1.symm, by simpa only [min_comm, max_comm] using h.2⟩
      loopless := fun a h => G.loopless a h.1 }
  have hF : ∀ k, (F k).CliqueFree 3 := by
    intro k T hT
    let f := T.orderIsoOfFin hT.card_eq
    have hlt : ∀ i j : Fin 3, i < j → (f i).val < (f j).val :=
      fun i j hij => f.strictMono hij
    have hadj : ∀ i j : Fin 3, i ≠ j → (F k).Adj (f i).val (f j).val := by
      intro i j hij
      exact hT.isClique (f i).property (f j).property
        (fun he => hij (f.injective (Subtype.ext he)))
    have h01 := hadj 0 1 (by decide)
    have h02 := hadj 0 2 (by decide)
    have h12 := hadj 1 2 (by decide)
    have h01' := h01.2
    have h02' := h02.2
    have h12' := h12.2
    simp only [min_eq_left (le_of_lt (hlt 0 1 (by decide))),
      max_eq_right (le_of_lt (hlt 0 1 (by decide)))] at h01'
    simp only [min_eq_left (le_of_lt (hlt 0 2 (by decide))),
      max_eq_right (le_of_lt (hlt 0 2 (by decide)))] at h02'
    simp only [min_eq_left (le_of_lt (hlt 1 2 (by decide))),
      max_eq_right (le_of_lt (hlt 1 2 (by decide)))] at h12'
    exact hc _ _ _ (hlt 0 1 (by decide)) (hlt 1 2 (by decide))
      h01.1 h02.1 h12.1 ⟨h01'.trans h02'.symm, h01'.trans h12'.symm⟩
  let H : ℕ → SimpleGraph V := fun n =>
    match Encodable.decode n with
    | some k => F k
    | none => ⊥
  refine ⟨H, ?_, ?_⟩
  · intro n
    dsimp only [H]
    cases Encodable.decode (α := C) n with
    | none => exact SimpleGraph.cliqueFree_bot (by omega)
    | some k => exact hF k
  · ext a b
    simp only [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      refine ⟨Encodable.encode (code (min a b) (max a b)), ?_⟩
      simp only [H, Encodable.encodek]
      exact ⟨hab, rfl⟩
    · rintro ⟨n, hn⟩
      dsimp only [H] at hn
      cases he : Encodable.decode (α := C) n with
      | none => simp only [he, SimpleGraph.bot_adj] at hn
      | some k => rw [he] at hn; exact hn.1

/-- Finite-support approximations only need to detect negativity at some
stage. No uniform bound on the dimension or cardinality is required. -/
theorem cover_of_packet_approximations {V I : Type*} (G : SimpleGraph V)
    (p : V → ℕ → Packet I)
    (hp : ∀ a b, G.Adj a b → ∃ n, dot (p a n) (p b n) < 0) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  classical
  letI : LinearOrder V := IsWellOrder.linearOrder (@WellOrderingRel V)
  let stage : V → V → ℕ := fun a b => if h : G.Adj a b then (hp a b h).choose else 0
  have hs : ∀ a b, G.Adj a b → dot (p a (stage a b)) (p b (stage a b)) < 0 := by
    intro a b hab
    simp only [stage, dif_pos hab]
    exact (hp a b hab).choose_spec
  let code : V → V → ℕ × Pattern := fun a b =>
    (stage a b, pairCode (p a (stage a b)) (p b (stage a b)))
  apply cover_of_ordered_patterns G code
  intro a b c _ _ hab _ _ ⟨he₁, he₂⟩
  have hn₁ : stage a b = stage a c := congrArg Prod.fst he₁
  have hn₂ : stage a b = stage b c := congrArg Prod.fst he₂
  have hp₁ := congrArg Prod.snd he₁
  have hp₂ := congrArg Prod.snd he₂
  dsimp only [code] at hp₁ hp₂
  rw [← hn₁] at hp₁
  rw [← hn₂] at hp₂
  exact (not_le_of_gt (hs a b hab))
    (dot_nonneg_of_same_pattern _ _ _ hp₁ hp₂)

#print axioms cover_of_packet_approximations

section Hilbert

variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def Packet.eval (b : I → E) (p : Packet I) : E :=
  ∑ i, p.value i • b (p.coord i)

noncomputable def Packet.ofFinsupp (f : I →₀ ℝ) : Packet I where
  size := f.support.card
  coord := ⟨fun i => (f.support.equivFin.symm i).val,
    fun _ _ he => f.support.equivFin.symm.injective (Subtype.ext he)⟩
  value := fun i => f (f.support.equivFin.symm i).val

theorem Packet.eval_ofFinsupp (b : I → E) (f : I →₀ ℝ) :
    (Packet.ofFinsupp f).eval b = f.sum (fun i a => a • b i) := by
  classical
  unfold Packet.eval Packet.ofFinsupp
  dsimp only [Function.Embedding.coeFn_mk]
  rw [f.support.equivFin.symm.sum_comp (fun i : f.support => f i.val • b i.val)]
  exact Finset.sum_coe_sort f.support (fun i => f i • b i)

theorem Packet.inner_eval (b : I → E) (hb : Orthonormal ℝ b) (p q : Packet I) :
    inner ℝ (p.eval b) (q.eval b) = dot p q := by
  classical
  unfold Packet.eval
  rw [sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right,
    orthonormal_iff_ite.mp hb]
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [mul_comm]

theorem exists_packet_approximation (b : HilbertBasis I ℝ E) (x : E) :
    ∃ p : ℕ → Packet I, Filter.Tendsto (fun n => (p n).eval b) Filter.atTop (nhds x) := by
  classical
  have hx : x ∈ closure (↑(Submodule.span ℝ (Set.range b)) : Set E) := by
    rw [← Submodule.topologicalClosure_coe, b.dense_span]
    trivial
  obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp hx
  have hf : ∀ n, ∃ f : I →₀ ℝ, f.sum (fun i a => a • b i) = u n :=
    fun n => Finsupp.mem_span_range_iff_exists_finsupp.mp (hu n)
  choose f hf using hf
  refine ⟨fun n => Packet.ofFinsupp (f n), ?_⟩
  simpa only [Packet.eval_ofFinsupp, hf] using ht

/-- Every graph represented by strictly negative real inner products has a
countable triangle-free edge cover, even in a nonseparable Hilbert space. -/
theorem countable_cover_of_negative_inner {V : Type*} [CompleteSpace E]
    (G : SimpleGraph V) (v : V → E)
    (hv : ∀ a b, G.Adj a b → inner ℝ (v a) (v b) < 0) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  classical
  obtain ⟨I, b, _⟩ := exists_hilbertBasis ℝ E
  choose p hp using fun a => exists_packet_approximation b (v a)
  apply cover_of_packet_approximations G p
  intro a c hac
  have ht := (hp a).inner (𝕜 := ℝ) (hp c)
  obtain ⟨n, hn⟩ := (ht.eventually_lt_const (hv a c hac)).exists
  exact ⟨n, by simpa only [Packet.inner_eval _ b.orthonormal] using hn⟩

#print axioms countable_cover_of_negative_inner

end Hilbert

end Erdos595NegativeInner
