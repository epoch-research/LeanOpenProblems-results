import Mathlib
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Hypercube

/-!
Independent, axiom-auditable lemmas for investigating the hypercube Ramsey conjecture.
This file deliberately does not import `Submission.Spec` and does not assert the conjecture.
-/

namespace CubeRecursionInvestigation

open SimpleGraph Finset Function

/-- The exact adjacency formula behind `Q_(n+1) = K₂ □ Q_n`. -/
theorem hypercube_cons_adj {n : ℕ} (a b : Bool) (u v : Fin n → Bool) :
    (hypercube (n + 1)).Adj (Fin.cons a u) (Fin.cons b v) ↔
      (a ≠ b ∧ u = v) ∨ ((hypercube n).Adj u v ∧ a = b) := by
  have hz : #{i : Fin n | u i ≠ v i} = 0 ↔ u = v := by
    simp [Finset.card_eq_zero, Finset.filter_eq_empty_iff, funext_iff]
  rw [hypercube_adj, Fin.card_filter_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  by_cases hab : a = b
  · simp [hab, hypercube_adj]
  · simp [hab, hz, hypercube_adj]

/-- The product decomposition is an isomorphism, not just a homomorphism. -/
def cubeSuccIso (n : ℕ) :
    (⊤ : SimpleGraph Bool) □ hypercube n ≃g hypercube (n + 1) where
  toEquiv := Fin.consEquiv (fun _ : Fin (n + 1) => Bool)
  map_rel_iff' := by
    rintro ⟨a, u⟩ ⟨b, v⟩
    change (hypercube (n + 1)).Adj (Fin.cons a u) (Fin.cons b v) ↔ _
    rw [hypercube_cons_adj]
    rfl

/-- Disjoint labelled copies lift a Cartesian product when corresponding vertices
are joined along every edge of the indexing graph. -/
def copyBoxOfCopies {ι α V : Type*} {H : SimpleGraph ι} {G : SimpleGraph α}
    {R : SimpleGraph V} (f : ι → Copy G R)
    (hdisj : ∀ i j, i ≠ j → ∀ a b, f i a ≠ f j b)
    (hmatch : ∀ ⦃i j⦄, H.Adj i j → ∀ a, R.Adj (f i a) (f j a)) :
    Copy (H □ G) R where
  toHom := {
    toFun := fun x => f x.1 x.2
    map_rel' := by
      rintro ⟨i, a⟩ ⟨j, b⟩ (⟨hij, hab⟩ | ⟨hab, hij⟩)
      · dsimp at *
        subst b
        exact hmatch hij a
      · dsimp at *
        subst j
        exact (f i).toHom.map_rel hab }
  injective' := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    change f i a = f j b at h
    have hij : i = j := by
      by_contra hn
      exact hdisj i j hn a b h
    subst j
    have hab : a = b := (f i).injective h
    subst b
    rfl

/-- Two red cubes can be glued if the red matching respects their labels.
An arbitrary perfect matching does not supply this hypothesis. -/
def cubeCopySucc {V : Type*} {R : SimpleGraph V} {n : ℕ}
    (f : Bool → Copy (hypercube n) R)
    (hdisj : ∀ u v, f false u ≠ f true v)
    (hmatch : ∀ u, R.Adj (f false u) (f true u)) :
    Copy (hypercube (n + 1)) R := by
  have hd : ∀ i j : Bool, i ≠ j → ∀ u v, f i u ≠ f j v := by
    intro i j hij u v
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hdisj u v
    · exact (hdisj v u).symm
    · exact (hij rfl).elim
  have hm : ∀ ⦃i j : Bool⦄, (⊤ : SimpleGraph Bool).Adj i j →
      ∀ u, R.Adj (f i u) (f j u) := by
    intro i j hij u
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hmatch u
    · exact (hmatch u).symm
    · exact (hij rfl).elim
  exact (copyBoxOfCopies f hd hm).comp (cubeSuccIso n).symm.toCopy

/-- Compress a red matching by intersecting the two transported red graphs.
A cube in that intersection lifts to a red cube one dimension larger. -/
def liftMatchedCube {α V : Type*} {R : SimpleGraph V} {n : ℕ}
    (l r : α ↪ V) (hdisj : ∀ a b, l a ≠ r b)
    (hmatch : ∀ a, R.Adj (l a) (r a))
    (g : Copy (hypercube n) (R.comap l ⊓ R.comap r)) :
    Copy (hypercube (n + 1)) R := by
  let f₀ : Copy (hypercube n) R := {
    toHom := {
      toFun := fun u => l (g u)
      map_rel' := fun h => (g.toHom.map_rel h).1 }
    injective' := l.injective.comp g.injective }
  let f₁ : Copy (hypercube n) R := {
    toHom := {
      toFun := fun u => r (g u)
      map_rel' := fun h => (g.toHom.map_rel h).2 }
    injective' := r.injective.comp g.injective }
  exact cubeCopySucc (fun b => Bool.rec f₀ f₁ b)
    (fun u v => hdisj (g u) (g v)) (fun u => hmatch (g u))

/-- Normalize an additive doubling recurrence. No sign assumption on the errors
is needed for the finite-sum identity/inequality. -/
theorem doubling_recurrence_bound (r e : ℕ → ℝ)
    (hstep : ∀ n, r (n + 1) ≤ 2 * r n + e n) (n : ℕ) :
    r n ≤ (2 : ℝ) ^ n * (r 0 + ∑ k ∈ Finset.range n, e k / 2 ^ (k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : (2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
    calc
      r (n + 1) ≤ 2 * r n + e n := hstep n
      _ ≤ 2 * ((2 : ℝ) ^ n *
          (r 0 + ∑ k ∈ Finset.range n, e k / 2 ^ (k + 1))) + e n := by
        linarith
      _ = (2 : ℝ) ^ (n + 1) *
          (r 0 + ∑ k ∈ Finset.range (n + 1), e k / 2 ^ (k + 1)) := by
        rw [Finset.sum_range_succ]
        rw [← add_assoc]
        conv_rhs => rw [mul_add]
        have hc : (2 : ℝ) ^ (n + 1) * (e n / 2 ^ (n + 1)) = e n := by
          field_simp
        rw [hc, pow_succ]
        ring

/-- Uniform bounded cumulative normalized error is sufficient for a linear
bound in `2^n`. This is the exact elementary condition used by the recurrence. -/
theorem doubling_recurrence_bounded_error (r e : ℕ → ℝ) (B : ℝ)
    (hstep : ∀ n, r (n + 1) ≤ 2 * r n + e n)
    (hbudget : ∀ n, (∑ k ∈ Finset.range n, e k / (2 : ℝ) ^ (k + 1)) ≤ B)
    (n : ℕ) : r n ≤ (r 0 + B) * 2 ^ n := by
  calc
    r n ≤ (2 : ℝ) ^ n * (r 0 + ∑ k ∈ Finset.range n, e k / 2 ^ (k + 1)) :=
      doubling_recurrence_bound r e hstep n
    _ ≤ (2 : ℝ) ^ n * (r 0 + B) := by
      gcongr
      exact hbudget n
    _ = (r 0 + B) * 2 ^ n := mul_comm _ _

/-- In particular, a summable series of nonnegative relative errors suffices. -/
theorem doubling_recurrence_summable (r e : ℕ → ℝ)
    (hstep : ∀ n, r (n + 1) ≤ 2 * r n + e n)
    (he : ∀ n, 0 ≤ e n)
    (hsum : Summable (fun k => e k / (2 : ℝ) ^ (k + 1))) (n : ℕ) :
    r n ≤ (r 0 + ∑' k, e k / (2 : ℝ) ^ (k + 1)) * 2 ^ n := by
  apply doubling_recurrence_bounded_error r e _ hstep _ n
  intro m
  exact hsum.sum_le_tsum (Finset.range m) (fun k _ => div_nonneg (he k) (by positivity))

/-- A multiscale alternative: normalized errors of order `1/n` are sufficient
if the dimension is halved at each recursive step. This is only a conditional
numerical lemma; no such recurrence for Ramsey numbers is asserted. -/
theorem halving_recurrence_normalized_bound (a : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hstep : ∀ n, 2 ≤ n → a n ≤ a (n / 2) + A / (n : ℝ)) :
    ∀ n, 1 ≤ n → a n ≤ a 1 + A * (1 - 1 / (n : ℝ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hn1 : n = 1
    · subst n
      simp
    have hn2 : 2 ≤ n := by omega
    have hmpos : 0 < n / 2 := Nat.div_pos hn2 (by omega)
    have hmlt : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hmreal : 0 < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hmpos
    have htwom : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.mul_div_le n 2
    have hfrac : 2 * A / (n : ℝ) ≤ A / ((n / 2 : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ hnreal hmreal).mpr
      nlinarith [mul_le_mul_of_nonneg_left htwom hA]
    have hi := ih (n / 2) hmlt (by omega)
    calc
      a n ≤ a (n / 2) + A / (n : ℝ) := hstep n hn2
      _ ≤ a 1 + A * (1 - 1 / ((n / 2 : ℕ) : ℝ)) + A / (n : ℝ) := by
        linarith
      _ ≤ a 1 + A * (1 - 1 / (n : ℝ)) := by
        simp only [div_eq_mul_inv, one_mul] at hfrac ⊢
        nlinarith

/-- A counterexample to the claim that little-o relative error is enough. -/
noncomputable def harmonicGrowth (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * (1 + ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1))

theorem harmonicGrowth_recurrence (n : ℕ) :
    harmonicGrowth (n + 1) = 2 * harmonicGrowth n +
      (2 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) := by
  simp only [harmonicGrowth, Finset.sum_range_succ, pow_succ]
  ring

theorem harmonicGrowth_normalized (n : ℕ) :
    harmonicGrowth n / (2 : ℝ) ^ n =
      1 + ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) := by
  simp [harmonicGrowth]

theorem harmonicGrowth_relative_error (n : ℕ) :
    (harmonicGrowth (n + 1) - 2 * harmonicGrowth n) / (2 : ℝ) ^ (n + 1) =
      1 / ((n : ℝ) + 1) := by
  rw [harmonicGrowth_recurrence, add_sub_cancel_left]
  field_simp

theorem harmonicGrowth_relative_error_tends_to_zero :
    Filter.Tendsto
      (fun n => (harmonicGrowth (n + 1) - 2 * harmonicGrowth n) / (2 : ℝ) ^ (n + 1))
      Filter.atTop (nhds 0) := by
  simp_rw [harmonicGrowth_relative_error]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem harmonicGrowth_not_bounded :
    ¬ ∃ C : ℝ, ∀ n, harmonicGrowth n ≤ C * (2 : ℝ) ^ n := by
  rintro ⟨C, hC⟩
  obtain ⟨n, _, hn⟩ := Filter.exists_lt_of_tendsto_atTop
    Real.tendsto_sum_range_one_div_nat_succ_atTop 0 C
  have hh : harmonicGrowth n / (2 : ℝ) ^ n ≤ C :=
    (div_le_iff₀ (by positivity)).mpr (hC n)
  rw [harmonicGrowth_normalized] at hh
  linarith

/-- A degree-saturating injective homomorphism reflects adjacency. This is why
noninduced containment between equally-sized regular graphs of the same degree
cannot evade the twisted-cube counterexample. -/
theorem copy_reflects_adj_at_of_degree_eq {α β : Type*} [Fintype α] [Fintype β]
    {G : SimpleGraph α} {H : SimpleGraph β} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : Copy G H) {x y : α} (hdeg : G.degree x = H.degree (f x))
    (hxy : H.Adj (f x) (f y)) : G.Adj x y := by
  have hc : Fintype.card (G.neighborSet x) = Fintype.card (H.neighborSet (f x)) := by
    simpa only [card_neighborSet_eq_degree] using hdeg
  have hs : Surjective (f.mapNeighborSet x) :=
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨(f.mapNeighborSet x).injective, hc⟩).2
  obtain ⟨z, hz⟩ := hs ⟨f y, hxy⟩
  have he : f z.val = f y := congrArg Subtype.val hz
  have he' : z.val = y := f.injective he
  exact he' ▸ z.prop

theorem copy_reflects_adj_of_degree_eq {α β : Type*} [Fintype α] [Fintype β]
    {G : SimpleGraph α} {H : SimpleGraph β} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : Copy G H) (hdeg : ∀ x, G.degree x = H.degree (f x))
    {x y : α} (hxy : H.Adj (f x) (f y)) : G.Adj x y :=
  copy_reflects_adj_at_of_degree_eq f (hdeg x) hxy

instance cubeDecidableAdj (n : ℕ) : DecidableRel (hypercube n).Adj :=
  fun u v => inferInstanceAs (Decidable (#{i | u i ≠ v i} = 1))

/-- Two 4-cycles, with a matching that swaps two adjacent labels. -/
def twistedNeighbors : Fin 8 → Finset (Fin 8) :=
  ![{1, 3, 5}, {0, 2, 4}, {1, 3, 6}, {0, 2, 7},
    {1, 5, 7}, {0, 4, 6}, {2, 5, 7}, {3, 4, 6}]

def twisted3 : SimpleGraph (Fin 8) where
  Adj a b := b ∈ twistedNeighbors a
  symm := by
    change ∀ a b : Fin 8, b ∈ twistedNeighbors a → a ∈ twistedNeighbors b
    decide
  loopless := by
    change ∀ a : Fin 8, a ∉ twistedNeighbors a
    decide

instance : DecidableRel twisted3.Adj :=
  fun a b => inferInstanceAs (Decidable (b ∈ twistedNeighbors a))

theorem twisted3_degree : ∀ v, twisted3.degree v = 3 := by decide

theorem cube3_degree : ∀ v, (hypercube 3).degree v = 3 := by decide

def cube3Parity (u : Fin 3 → Bool) : Bool := (u 0 ^^ u 1) ^^ u 2

theorem cube3Parity_adj : ∀ u v, (hypercube 3).Adj u v → cube3Parity u ≠ cube3Parity v := by
  decide

/-- Despite noninduced containment, the twisted cubic graph cannot contain Q₃.
The proof uses degree saturation and the 5-cycle 0,1,2,6,5,0. -/
theorem twisted3_no_cube : ¬ (hypercube 3).IsContained twisted3 := by
  rintro ⟨f⟩
  have hf : Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr
    ⟨f.injective, by decide⟩
  let e := Equiv.ofBijective f hf
  let c : Fin 8 → Bool := fun v => cube3Parity (e.symm v)
  have hc : ∀ a b, twisted3.Adj a b → c a ≠ c b := by
    intro a b hab
    apply cube3Parity_adj
    apply copy_reflects_adj_of_degree_eq f
      (fun x => (cube3_degree x).trans (twisted3_degree (f x)).symm)
    change twisted3.Adj (e (e.symm a)) (e (e.symm b))
    simpa only [Equiv.apply_symm_apply] using hab
  have hodd : ∀ a b c d e : Bool,
      a ≠ b → b ≠ c → c ≠ d → d ≠ e → e ≠ a → False := by
    intro a b c d e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide
  exact hodd (c 0) (c 1) (c 2) (c 6) (c 5)
    (hc 0 1 (by decide)) (hc 1 2 (by decide)) (hc 2 6 (by decide))
    (hc 6 5 (by decide)) (hc 5 0 (by decide))

/-- Gray-code cyclic ordering of the vertices of Q₂. -/
def squareLabel (u : Fin 2 → Bool) : Fin 4 :=
  if u 0 then (if u 1 then 2 else 3) else (if u 1 then 1 else 0)

def lowerSquare : Copy (hypercube 2) twisted3 where
  toHom := {
    toFun := fun u => (![0, 1, 2, 3] : Fin 4 → Fin 8) (squareLabel u)
    map_rel' := by decide }
  injective' := by decide

def upperSquare : Copy (hypercube 2) twisted3 where
  toHom := {
    toFun := fun u => (![4, 5, 6, 7] : Fin 4 → Fin 8) (squareLabel u)
    map_rel' := by decide }
  injective' := by decide

def twistPerm : Equiv.Perm (Fin 2 → Bool) :=
  Equiv.swap ![false, false] ![false, true]

theorem twisted3_squares_disjoint : ∀ u v, lowerSquare u ≠ upperSquare v := by decide

theorem twisted3_perfect_matching :
    ∀ u, twisted3.Adj (lowerSquare u) (upperSquare (twistPerm u)) := by decide

/-- Fully explicit counterexample to arbitrary-matching gluing of two red cubes.
This refutes only that simplification, not the red-or-blue Ramsey conjecture. -/
theorem arbitrary_matching_not_sufficient :
    ∃ (G : SimpleGraph (Fin 8)) (f₀ f₁ : Copy (hypercube 2) G)
      (p : Equiv.Perm (Fin 2 → Bool)),
      (∀ u v, f₀ u ≠ f₁ v) ∧
      (∀ u, G.Adj (f₀ u) (f₁ (p u))) ∧ ¬ (hypercube 3).IsContained G :=
  ⟨twisted3, lowerSquare, upperSquare, twistPerm,
    twisted3_squares_disjoint, twisted3_perfect_matching, twisted3_no_cube⟩

/-- Adding just the red edge 0--6 also destroys all blue Q₃'s. -/
def augmentedNeighbors : Fin 8 → Finset (Fin 8) :=
  ![{1, 3, 5, 6}, {0, 2, 4}, {1, 3, 6}, {0, 2, 7},
    {1, 5, 7}, {0, 4, 6}, {0, 2, 5, 7}, {3, 4, 6}]

def augmentedTwisted3 : SimpleGraph (Fin 8) where
  Adj a b := b ∈ augmentedNeighbors a
  symm := by
    change ∀ a b : Fin 8, b ∈ augmentedNeighbors a → a ∈ augmentedNeighbors b
    decide
  loopless := by
    change ∀ a : Fin 8, a ∉ augmentedNeighbors a
    decide

instance : DecidableRel augmentedTwisted3.Adj :=
  fun a b => inferInstanceAs (Decidable (b ∈ augmentedNeighbors a))

theorem twisted3_le_augmented : twisted3 ≤ augmentedTwisted3 := by
  change ∀ a b : Fin 8, b ∈ twistedNeighbors a → b ∈ augmentedNeighbors a
  decide

/-- The old red 5-cycle is still forced by vertices of degree 3. -/
theorem augmentedTwisted3_no_red_cube : ¬ (hypercube 3).IsContained augmentedTwisted3 := by
  rintro ⟨f⟩
  have hf : Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr
    ⟨f.injective, by decide⟩
  let e := Equiv.ofBijective f hf
  let c : Fin 8 → Bool := fun v => cube3Parity (e.symm v)
  have heval (v : Fin 8) : f (e.symm v) = v := e.apply_symm_apply v
  have hc (a b : Fin 8) (ha : augmentedTwisted3.degree a = 3)
      (hab : augmentedTwisted3.Adj a b) : c a ≠ c b := by
    apply cube3Parity_adj
    apply copy_reflects_adj_at_of_degree_eq f
    · rw [cube3_degree, heval, ha]
    · simpa only [heval] using hab
  have hodd : ∀ a b c d e : Bool,
      a ≠ b → b ≠ c → c ≠ d → d ≠ e → e ≠ a → False := by
    intro a b c d e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide
  exact hodd (c 0) (c 1) (c 2) (c 6) (c 5)
    (hc 1 0 (by decide) (by decide)).symm
    (hc 1 2 (by decide) (by decide))
    (hc 2 6 (by decide) (by decide))
    (hc 5 6 (by decide) (by decide)).symm
    (hc 5 0 (by decide) (by decide))

set_option synthInstance.maxSize 512 in
/-- Distinct vertices of Q₃ cannot have exactly one common neighbor. -/
theorem cube3_other_common_neighbor :
    ∀ u v w : Fin 3 → Bool, u ≠ v → (hypercube 3).Adj u w → (hypercube 3).Adj v w →
      ∃ z, z ≠ w ∧ (hypercube 3).Adj u z ∧ (hypercube 3).Adj v z := by
  decide

/-- Blue vertices 0 and 6 have degree 3 and exactly one common neighbor, 4.
Their neighborhoods would be saturated by any spanning cube. -/
theorem augmentedTwisted3_no_blue_cube : ¬ (hypercube 3).IsContained augmentedTwisted3ᶜ := by
  rintro ⟨f⟩
  have hf : Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr
    ⟨f.injective, by decide⟩
  let e := Equiv.ofBijective f hf
  have heval (v : Fin 8) : f (e.symm v) = v := e.apply_symm_apply v
  have lift (a b : Fin 8) (ha : augmentedTwisted3ᶜ.degree a = 3)
      (hab : augmentedTwisted3ᶜ.Adj a b) : (hypercube 3).Adj (e.symm a) (e.symm b) := by
    apply copy_reflects_adj_at_of_degree_eq f
    · rw [cube3_degree, heval, ha]
    · simpa only [heval] using hab
  have hne : e.symm (0 : Fin 8) ≠ e.symm 6 := e.symm.injective.ne (by decide)
  obtain ⟨z, hnz, hz0, hz6⟩ := cube3_other_common_neighbor
    (e.symm 0) (e.symm 6) (e.symm 4) hne
    (lift 0 4 (by decide) (by decide)) (lift 6 4 (by decide) (by decide))
  have huniq : ∀ w : Fin 8,
      augmentedTwisted3ᶜ.Adj 0 w → augmentedTwisted3ᶜ.Adj 6 w → w = 4 := by decide
  have hz0' : augmentedTwisted3ᶜ.Adj 0 (f z) := by
    simpa only [Copy.toHom_apply, heval] using f.toHom.map_rel hz0
  have hz6' : augmentedTwisted3ᶜ.Adj 6 (f z) := by
    simpa only [Copy.toHom_apply, heval] using f.toHom.map_rel hz6
  have hz : f z = 4 := huniq (f z) hz0' hz6'
  exact hnz (f.injective (hz.trans (heval 4).symm))

/-- Even the weaker "a larger cube in either color" conclusion cannot follow
merely from two red cubes and a red perfect matching between them. -/
theorem arbitrary_matching_not_sufficient_even_two_colors :
    ∃ (G : SimpleGraph (Fin 8)) (f₀ f₁ : Copy (hypercube 2) G)
      (p : Equiv.Perm (Fin 2 → Bool)),
      (∀ u v, f₀ u ≠ f₁ v) ∧ (∀ u, G.Adj (f₀ u) (f₁ (p u))) ∧
      ¬ (hypercube 3).IsContained G ∧ ¬ (hypercube 3).IsContained Gᶜ := by
  let inc := Copy.ofLE twisted3 augmentedTwisted3 twisted3_le_augmented
  refine ⟨augmentedTwisted3, inc.comp lowerSquare, inc.comp upperSquare, twistPerm,
    ?_, ?_, augmentedTwisted3_no_red_cube, augmentedTwisted3_no_blue_cube⟩
  · simpa [inc] using twisted3_squares_disjoint
  · intro u
    simpa [inc] using twisted3_le_augmented (twisted3_perfect_matching u)

/-- Degree monotonicity for injective, not necessarily induced graph copies. -/
theorem copy_degree_le {α β : Type*} [Fintype α] [Fintype β]
    {G : SimpleGraph α} {H : SimpleGraph β} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : Copy G H) (x : α) : G.degree x ≤ H.degree (f x) := by
  simpa only [card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective (f.mapNeighborSet x) (f.mapNeighborSet x).injective

def firstMatching : SimpleGraph (Fin 4) where
  Adj a b := a ≠ b ∧ a.val / 2 = b.val / 2
  symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless := fun _ h => h.1 rfl

def secondMatching : SimpleGraph (Fin 4) where
  Adj a b := a ≠ b ∧ a.val + b.val = 3
  symm := fun _ _ h => ⟨h.1.symm, (Nat.add_comm _ _).trans h.2⟩
  loopless := fun _ h => h.1 rfl

instance : DecidableRel firstMatching.Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ a.val / 2 = b.val / 2))

instance : DecidableRel secondMatching.Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ a.val + b.val = 3))

theorem cube2_not_in_degree_one {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v = 1) :
    ¬ (hypercube 2).IsContained G := by
  rintro ⟨f⟩
  have h := copy_degree_le f ![false, false]
  have htwo : (hypercube 2).degree ![false, false] = 2 := by decide
  rw [htwo, hdeg] at h
  omega

def squareInMatchingUnion : Copy (hypercube 2) (firstMatching ⊔ secondMatching) where
  toHom := { toFun := squareLabel, map_rel' := by decide }
  injective' := by decide

/-- The blue graph after matching compression is a union of transported blue graphs.
Even a union of two cube-free graphs need not be cube-free. -/
theorem union_does_not_preserve_cube_freeness :
    ∃ B₀ B₁ : SimpleGraph (Fin 4),
      ¬ (hypercube 2).IsContained B₀ ∧ ¬ (hypercube 2).IsContained B₁ ∧
        (hypercube 2).IsContained (B₀ ⊔ B₁) :=
  ⟨firstMatching, secondMatching, cube2_not_in_degree_one firstMatching (by decide),
    cube2_not_in_degree_one secondMatching (by decide), ⟨squareInMatchingUnion⟩⟩

end CubeRecursionInvestigation
