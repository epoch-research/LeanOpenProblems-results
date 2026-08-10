import FormalConjectures.Util.ProblemImports

open scoped BigOperators
open Finset

namespace DOneStepNoAxiom

def NondecreasingFin {l : ℕ} (δ : Fin l → ℕ) : Prop :=
  ∀ i j : Fin l, (i : ℕ) ≤ (j : ℕ) → δ i ≤ δ j

noncomputable def support (l N : ℕ) : Finset (Fin l → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin l => Finset.range (N + 1)).filter
    (fun δ => NondecreasingFin δ ∧ (∑ i : Fin l, δ i) = N)

noncomputable def weight (a l : ℕ) (δ : Fin l → ℕ) : ℚ :=
  ∏ i : Fin l,
    ((Nat.factorial (a + (i : ℕ)) : ℚ) /
      (Nat.factorial (a + (i : ℕ) + δ i) : ℚ))

noncomputable def D (a l N : ℕ) : ℚ :=
  ∑ δ ∈ support l N, weight a l δ

def lastFin (l : ℕ) (hl : 0 < l) : Fin l :=
  ⟨l - 1, Nat.sub_one_lt (Nat.ne_of_gt hl)⟩

noncomputable def maxIndexSet {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) : Finset (Fin l) :=
  Finset.univ.filter fun i => δ i = δ (lastFin l hl)

lemma lastFin_mem_maxIndexSet {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) :
    lastFin l hl ∈ maxIndexSet hl δ := by
  classical
  simp [maxIndexSet]

lemma maxIndexSet_nonempty {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) :
    (maxIndexSet hl δ).Nonempty :=
  ⟨lastFin l hl, lastFin_mem_maxIndexSet hl δ⟩

noncomputable def leftmostMax {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) : Fin l :=
  (maxIndexSet hl δ).min' (maxIndexSet_nonempty hl δ)

lemma leftmostMax_mem {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) :
    leftmostMax hl δ ∈ maxIndexSet hl δ := by
  classical
  exact Finset.min'_mem _ _

lemma leftmostMax_value {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) :
    δ (leftmostMax hl δ) = δ (lastFin l hl) := by
  classical
  simpa [maxIndexSet] using leftmostMax_mem hl δ

lemma leftmostMax_le_of_value {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) {i : Fin l}
    (hi : δ i = δ (lastFin l hl)) : (leftmostMax hl δ : ℕ) ≤ (i : ℕ) := by
  classical
  exact Finset.min'_le _ _ (by
    change i ∈ Finset.univ.filter (fun x => δ x = δ (lastFin l hl))
    simp [hi])

def lowerAt {l : ℕ} (δ : Fin l → ℕ) (k : Fin l) : Fin l → ℕ :=
  fun i => if i = k then δ i - 1 else δ i

def raiseAt {l : ℕ} (η : Fin l → ℕ) (k : Fin l) : Fin l → ℕ :=
  fun i => if i = k then η i + 1 else η i

noncomputable def lowerLeftmostMax {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) : Fin l → ℕ :=
  lowerAt δ (leftmostMax hl δ)

lemma eq_raiseAt_of_lowerAt_eq {l : ℕ} {δ η : Fin l → ℕ} {k : Fin l}
    (hkpos : 0 < δ k) (h : lowerAt δ k = η) : δ = raiseAt η k := by
  funext i
  by_cases hi : i = k
  · subst i
    have hk : δ k - 1 = η k := by simpa [lowerAt] using congrFun h k
    have hk' : δ k = η k + 1 := by omega
    simpa [raiseAt, hk']
  · have hi' : δ i = η i := by simpa [lowerAt, hi] using congrFun h i
    simp [raiseAt, hi, hi']

-- If lowering leftmost max maps δ to η, then δ is obtained by raising the lowered coordinate.
lemma eq_raiseAt_of_lowerLeftmostMax_eq {l N : ℕ} (hl : 0 < l) {δ η : Fin l → ℕ}
    (hnd : NondecreasingFin δ) (hsum : (∑ i : Fin l, δ i) = N + 1)
    (h : lowerLeftmostMax hl δ = η) : δ = raiseAt η (leftmostMax hl δ) := by
  apply eq_raiseAt_of_lowerAt_eq ?_ h
  -- Need positivity of leftmost max value if total positive; dummy hsum for now
  have hval_nonzero : δ (leftmostMax hl δ) ≠ 0 := by
    intro hz
    have allzero : ∀ i : Fin l, δ i = 0 := by
      intro i
      have hlemax : δ i ≤ δ (leftmostMax hl δ) := by
        -- since nondecreasing and last is max; prove δ i ≤ last = leftmost
        have hi_le_last : (i : ℕ) ≤ (lastFin l hl : ℕ) := by
          dsimp [lastFin]
          omega
        have h1 := hnd i (lastFin l hl) hi_le_last
        simpa [leftmostMax_value hl δ] using h1
      omega
    have : (∑ i : Fin l, δ i) = 0 := by simp [allzero]
    omega
  omega


/-- Corrected predecessor candidate: indices whose successor is the leftmost maximum. -/
noncomputable def predecessorRaiseIndices {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) : Finset (Fin l) :=
  Finset.univ.filter fun k =>
    ∃ hk : (k : ℕ) + 1 < l, leftmostMax hl η = ⟨(k : ℕ) + 1, hk⟩

noncomputable def correctedCandidateRaiseIndices {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    Finset (Fin l) :=
  insert (lastFin l hl) (predecessorRaiseIndices hl η)


/-- Legal raise indices among the corrected candidates: either the last index, or a
predecessor whose value is exactly one below the last value of the target. -/
noncomputable def legalRaiseIndices {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    Finset (Fin l) :=
  (correctedCandidateRaiseIndices hl η).filter
    (fun k => k = lastFin l hl ∨ η k + 1 = η (lastFin l hl))

lemma value_lt_leftmostMax {l : ℕ} (hl : 0 < l) {δ : Fin l → ℕ}
    (hnd : NondecreasingFin δ) {i : Fin l}
    (hi : (i : ℕ) < (leftmostMax hl δ : ℕ)) : δ i < δ (leftmostMax hl δ) := by
  have hle_last : (i : ℕ) ≤ (lastFin l hl : ℕ) := by
    dsimp [lastFin]
    omega
  have hle : δ i ≤ δ (leftmostMax hl δ) := by
    have h := hnd i (lastFin l hl) hle_last
    simpa [leftmostMax_value hl δ] using h
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hleft : (leftmostMax hl δ : ℕ) ≤ (i : ℕ) := by
    apply leftmostMax_le_of_value hl δ
    simpa [leftmostMax_value hl δ] using heq
  omega

lemma value_eq_leftmostMax_of_ge {l : ℕ} (hl : 0 < l) {δ : Fin l → ℕ}
    (hnd : NondecreasingFin δ) {i : Fin l}
    (hi : (leftmostMax hl δ : ℕ) ≤ (i : ℕ)) : δ i = δ (leftmostMax hl δ) := by
  have h1 : δ (leftmostMax hl δ) ≤ δ i := hnd (leftmostMax hl δ) i hi
  have hle_last : (i : ℕ) ≤ (lastFin l hl : ℕ) := by
    dsimp [lastFin]
    omega
  have h2 : δ i ≤ δ (leftmostMax hl δ) := by
    have h := hnd i (lastFin l hl) hle_last
    simpa [leftmostMax_value hl δ] using h
  exact le_antisymm h2 h1

lemma lowered_index_mem_correctedCandidates {l N : ℕ} (hl : 0 < l) {δ η : Fin l → ℕ}
    (hnd : NondecreasingFin δ) (hsum : (∑ i : Fin l, δ i) = N + 1)
    (h : lowerLeftmostMax hl δ = η) :
    leftmostMax hl δ ∈ correctedCandidateRaiseIndices hl η := by
  classical
  let k := leftmostMax hl δ
  by_cases hlast : k = lastFin l hl
  · change k ∈ correctedCandidateRaiseIndices hl η
    rw [hlast, correctedCandidateRaiseIndices]
    exact Finset.mem_insert_self _ _
  · have hk_le_last : (k : ℕ) ≤ (lastFin l hl : ℕ) := by
      have := leftmostMax_le_of_value hl δ (i := lastFin l hl) rfl
      simpa [k] using this
    have hk_succ_lt : (k : ℕ) + 1 < l := by
      dsimp [lastFin] at hk_le_last hlast ⊢
      have hklt : (k : ℕ) < l - 1 := by
        have : (k : ℕ) ≠ l - 1 := by
          intro hv
          apply hlast
          apply Fin.ext
          simpa [lastFin] using hv
        omega
      omega
    let kp : Fin l := ⟨(k : ℕ) + 1, hk_succ_lt⟩
    have h_eta_kp : η kp = η (lastFin l hl) := by
      have hkp_ne : kp ≠ k := by
        intro heq
        have : (k : ℕ) + 1 = (k : ℕ) := by simpa [kp] using congrArg Fin.val heq
        omega
      have hlast_ne : lastFin l hl ≠ k := by exact fun h' => hlast h'.symm
      have hkp_ne_lm : kp ≠ leftmostMax hl δ := by simpa [k] using hkp_ne
      have hlast_ne_lm : lastFin l hl ≠ leftmostMax hl δ := by simpa [k] using hlast_ne
      have hkple : (k : ℕ) ≤ (kp : ℕ) := by simp [kp]
      have hkpval : δ kp = δ k := value_eq_leftmostMax_of_ge hl hnd hkple
      have hlastval : δ (lastFin l hl) = δ k := by rw [leftmostMax_value hl δ]
      calc
        η kp = lowerLeftmostMax hl δ kp := by rw [h]
        _ = δ kp := by simp [lowerLeftmostMax, lowerAt, hkp_ne_lm]
        _ = δ k := hkpval
        _ = δ (lastFin l hl) := hlastval.symm
        _ = lowerLeftmostMax hl δ (lastFin l hl) := by simp [lowerLeftmostMax, lowerAt, hlast_ne_lm]
        _ = η (lastFin l hl) := by rw [h]
    have h_lm_eta_le_kp : (leftmostMax hl η : ℕ) ≤ (kp : ℕ) := by
      apply leftmostMax_le_of_value hl η
      exact h_eta_kp
    have h_kp_le_lm_eta : (kp : ℕ) ≤ (leftmostMax hl η : ℕ) := by
      by_contra hcontra
      have hlt : (leftmostMax hl η : ℕ) < (kp : ℕ) := by omega
      have hle_k : (leftmostMax hl η : ℕ) ≤ (k : ℕ) := by
        simp [kp] at hlt
        omega
      have h_eta_lm_lt : η (leftmostMax hl η) < η (lastFin l hl) := by
        by_cases heqk : (leftmostMax hl η : ℕ) = (k : ℕ)
        · have hfin : leftmostMax hl η = k := Fin.ext heqk
          have hηk : η k = δ k - 1 := by simp [← h, lowerLeftmostMax, lowerAt, k]
          have hηlast : η (lastFin l hl) = δ k := by
            have hlast_ne : lastFin l hl ≠ k := fun h' => hlast h'.symm
            have hlast_ne_lm : lastFin l hl ≠ leftmostMax hl δ := by simpa [k] using hlast_ne

            calc
              η (lastFin l hl) = lowerLeftmostMax hl δ (lastFin l hl) := by rw [h]
              _ = δ (lastFin l hl) := by simp [lowerLeftmostMax, lowerAt, hlast_ne_lm]
              _ = δ k := by rw [leftmostMax_value hl δ]
          have hkpos : 0 < δ k := by
            by_contra hz
            have hz' : δ k = 0 := by omega
            have allzero : ∀ i : Fin l, δ i = 0 := by
              intro i
              have hlemax : δ i ≤ δ k := by
                have hle_last : (i : ℕ) ≤ (lastFin l hl : ℕ) := by dsimp [lastFin]; omega
                have ht := hnd i (lastFin l hl) hle_last
                calc
                  δ i ≤ δ (lastFin l hl) := ht
                  _ = δ k := by rw [← leftmostMax_value hl δ]
              omega
            have : (∑ i : Fin l, δ i) = 0 := by simp [allzero]
            omega
          rw [hfin, hηk, hηlast]
          omega
        · have hlt_k : (leftmostMax hl η : ℕ) < (k : ℕ) := by omega
          have hηlm : η (leftmostMax hl η) = δ (leftmostMax hl η) := by
            have hne : leftmostMax hl η ≠ k := by intro hfin; exact heqk (congrArg Fin.val hfin)
            have hne_lm : leftmostMax hl η ≠ leftmostMax hl δ := by simpa [k] using hne
            calc
              η (leftmostMax hl η) = lowerLeftmostMax hl δ (leftmostMax hl η) := by rw [h]
              _ = δ (leftmostMax hl η) := by simp [lowerLeftmostMax, lowerAt, hne_lm]
          have hδlt : δ (leftmostMax hl η) < δ k := value_lt_leftmostMax hl hnd hlt_k
          have hηlast : η (lastFin l hl) = δ k := by
            have hlast_ne : lastFin l hl ≠ k := fun h' => hlast h'.symm
            have hlast_ne_lm : lastFin l hl ≠ leftmostMax hl δ := by simpa [k] using hlast_ne

            calc
              η (lastFin l hl) = lowerLeftmostMax hl δ (lastFin l hl) := by rw [h]
              _ = δ (lastFin l hl) := by simp [lowerLeftmostMax, lowerAt, hlast_ne_lm]
              _ = δ k := by rw [leftmostMax_value hl δ]
          rw [hηlm, hηlast]
          exact hδlt
      have h_eq := leftmostMax_value hl η
      omega
    have hkp_eq : leftmostMax hl η = kp := by
      apply Fin.ext
      omega
    simp [correctedCandidateRaiseIndices, predecessorRaiseIndices]
    right
    exact ⟨hk_succ_lt, hkp_eq⟩


lemma lowered_index_mem_legalRaiseIndices {l N : ℕ} (hl : 0 < l) {δ η : Fin l → ℕ}
    (hnd : NondecreasingFin δ) (hsum : (∑ i : Fin l, δ i) = N + 1)
    (h : lowerLeftmostMax hl δ = η) :
    leftmostMax hl δ ∈ legalRaiseIndices hl η := by
  classical
  let k := leftmostMax hl δ
  have hcorr : k ∈ correctedCandidateRaiseIndices hl η := by
    simpa [k] using lowered_index_mem_correctedCandidates hl hnd hsum h
  rw [legalRaiseIndices]
  simp only [Finset.mem_filter]
  refine ⟨by simpa [k] using hcorr, ?_⟩
  by_cases hlast : k = lastFin l hl
  · exact Or.inl hlast
  · right
    have hηk : η k = δ k - 1 := by
      simp [← h, lowerLeftmostMax, lowerAt, k]
    have hηlast : η (lastFin l hl) = δ k := by
      have hlast_ne : lastFin l hl ≠ k := fun h' => hlast h'.symm
      have hlast_ne_lm : lastFin l hl ≠ leftmostMax hl δ := by simpa [k] using hlast_ne
      calc
        η (lastFin l hl) = lowerLeftmostMax hl δ (lastFin l hl) := by rw [h]
        _ = δ (lastFin l hl) := by simp [lowerLeftmostMax, lowerAt, hlast_ne_lm]
        _ = δ k := by rw [leftmostMax_value hl δ]
    have hkpos : 0 < δ k := by
      by_contra hz
      have hz' : δ k = 0 := by omega
      have allzero : ∀ i : Fin l, δ i = 0 := by
        intro i
        have hlemax : δ i ≤ δ k := by
          have hle_last : (i : ℕ) ≤ (lastFin l hl : ℕ) := by dsimp [lastFin]; omega
          have ht := hnd i (lastFin l hl) hle_last
          calc
            δ i ≤ δ (lastFin l hl) := ht
            _ = δ k := by rw [← leftmostMax_value hl δ]
        omega
      have : (∑ i : Fin l, δ i) = 0 := by simp [allzero]
      omega
    rw [hηk, hηlast]
    omega

lemma card_predecessorRaiseIndices_le_one {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    (predecessorRaiseIndices hl η).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro a ha b hb
  simp [predecessorRaiseIndices] at ha hb
  rcases ha with ⟨haLt, haEq⟩
  rcases hb with ⟨hbLt, hbEq⟩
  apply Fin.ext
  have hval : (a : ℕ) + 1 = (b : ℕ) + 1 := by
    calc
      (a : ℕ) + 1 = (leftmostMax hl η : ℕ) := by simpa using congrArg Fin.val haEq.symm
      _ = (b : ℕ) + 1 := by simpa using congrArg Fin.val hbEq
  omega

lemma card_correctedCandidateRaiseIndices_le_two {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    (correctedCandidateRaiseIndices hl η).card ≤ 2 := by
  classical
  unfold correctedCandidateRaiseIndices
  calc
    (insert (lastFin l hl) (predecessorRaiseIndices hl η)).card ≤
        (predecessorRaiseIndices hl η).card + 1 := Finset.card_insert_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add_right (card_predecessorRaiseIndices_le_one hl η) 1
    _ = 2 := by norm_num

noncomputable def loweringFiber {l : ℕ} (hl : 0 < l) (N : ℕ) (η : Fin l → ℕ) :
    Finset (Fin l → ℕ) :=
  (support l (N + 1)).filter fun δ => lowerLeftmostMax hl δ = η

noncomputable def candidatePreimages {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    Finset (Fin l → ℕ) :=
  (correctedCandidateRaiseIndices hl η).image (fun k => raiseAt η k)


noncomputable def legalCandidatePreimages {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    Finset (Fin l → ℕ) :=
  (legalRaiseIndices hl η).image (fun k => raiseAt η k)

lemma loweringFiber_subset_candidatePreimages {l N : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    loweringFiber hl N η ⊆ candidatePreimages hl η := by
  classical
  intro δ hδ
  have hmem : δ ∈ support l (N + 1) := (Finset.mem_filter.mp hδ).1
  have hmap : lowerLeftmostMax hl δ = η := (Finset.mem_filter.mp hδ).2
  simp [support] at hmem
  rcases hmem with ⟨hbox, hnd, hsum⟩
  have hidx : leftmostMax hl δ ∈ correctedCandidateRaiseIndices hl η :=
    lowered_index_mem_correctedCandidates hl hnd hsum hmap
  have heq : δ = raiseAt η (leftmostMax hl δ) :=
    eq_raiseAt_of_lowerLeftmostMax_eq hl hnd hsum hmap
  rw [heq]
  exact Finset.mem_image.mpr ⟨leftmostMax hl δ, hidx, rfl⟩

lemma loweringFiber_subset_legalCandidatePreimages {l N : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    loweringFiber hl N η ⊆ legalCandidatePreimages hl η := by
  classical
  intro δ hδ
  have hmem : δ ∈ support l (N + 1) := (Finset.mem_filter.mp hδ).1
  have hmap : lowerLeftmostMax hl δ = η := (Finset.mem_filter.mp hδ).2
  simp [support] at hmem
  rcases hmem with ⟨hbox, hnd, hsum⟩
  have hidx : leftmostMax hl δ ∈ legalRaiseIndices hl η :=
    lowered_index_mem_legalRaiseIndices hl hnd hsum hmap
  have heq : δ = raiseAt η (leftmostMax hl δ) :=
    eq_raiseAt_of_lowerLeftmostMax_eq hl hnd hsum hmap
  rw [heq]
  exact Finset.mem_image.mpr ⟨leftmostMax hl δ, hidx, rfl⟩


lemma card_loweringFiber_le_two {l N : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    (loweringFiber hl N η).card ≤ 2 := by
  classical
  calc
    (loweringFiber hl N η).card ≤ (candidatePreimages hl η).card :=
      Finset.card_le_card (loweringFiber_subset_candidatePreimages hl η)

    _ ≤ (correctedCandidateRaiseIndices hl η).card := Finset.card_image_le
    _ ≤ 2 := card_correctedCandidateRaiseIndices_le_two hl η

lemma weight_raiseAt_eq {l a : ℕ} (η : Fin l → ℕ) (k : Fin l) :
    weight a l (raiseAt η k) =
      weight a l η * ((a + (k : ℕ) + η k : ℕ).factorial : ℚ) /
        ((a + (k : ℕ) + η k + 1 : ℕ).factorial : ℚ) := by
  classical
  unfold weight raiseAt
  rw [show (∏ i : Fin l, ((Nat.factorial (a + (i : ℕ)) : ℚ) /
      (Nat.factorial (a + (i : ℕ) + (if i = k then η i + 1 else η i)) : ℚ))) =
      ((Nat.factorial (a + (k : ℕ)) : ℚ) /
      (Nat.factorial (a + (k : ℕ) + (η k + 1)) : ℚ)) *
      ∏ i ∈ (Finset.univ.erase k), ((Nat.factorial (a + (i : ℕ)) : ℚ) /
      (Nat.factorial (a + (i : ℕ) + (if i = k then η i + 1 else η i)) : ℚ)) by
        simpa using (Finset.mul_prod_erase Finset.univ (fun i : Fin l => ((Nat.factorial (a + (i : ℕ)) : ℚ) /
      (Nat.factorial (a + (i : ℕ) + (if i = k then η i + 1 else η i)) : ℚ))) (by simp : k ∈ (Finset.univ : Finset (Fin l)))).symm]
  rw [show (∏ i : Fin l, ((Nat.factorial (a + (i : ℕ)) : ℚ) /
      (Nat.factorial (a + (i : ℕ) + η i) : ℚ))) =
      ((Nat.factorial (a + (k : ℕ)) : ℚ) /
      (Nat.factorial (a + (k : ℕ) + η k) : ℚ)) *
      ∏ i ∈ (Finset.univ.erase k), ((Nat.factorial (a + (i : ℕ)) : ℚ) /
      (Nat.factorial (a + (i : ℕ) + η i) : ℚ)) by
        simpa using (Finset.mul_prod_erase Finset.univ (fun i : Fin l => ((Nat.factorial (a + (i : ℕ)) : ℚ) /
      (Nat.factorial (a + (i : ℕ) + η i) : ℚ))) (by simp : k ∈ (Finset.univ : Finset (Fin l)))).symm]
  have hprodq : (∏ x ∈ (Finset.univ.erase k), ((Nat.factorial (a + (x : ℕ)) : ℚ) /
      (Nat.factorial (a + (x : ℕ) + (if x = k then η x + 1 else η x)) : ℚ))) =
      (∏ x ∈ (Finset.univ.erase k), ((Nat.factorial (a + (x : ℕ)) : ℚ) /
      (Nat.factorial (a + (x : ℕ) + η x) : ℚ))) := by
    refine Finset.prod_congr rfl ?_
    intro x hx
    simp at hx
    simp [hx]
  rw [hprodq]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + (k : ℕ) + η k)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + (k : ℕ) + η k + 1))]
  ring_nf

lemma factorial_ratio_le_inv_succ (m a : ℕ) (ha : a ≤ m) :
    ((Nat.factorial m : ℚ) / (Nat.factorial (m + 1) : ℚ)) ≤ 1 / ((a + 1 : ℕ) : ℚ) := by
  have hmpos : (0 : ℚ) < (m + 1 : ℕ) := by positivity
  have hapos : (0 : ℚ) < (a + 1 : ℕ) := by positivity
  have hmfac : (Nat.factorial m : ℚ) / (Nat.factorial (m + 1) : ℚ) = 1 / ((m + 1 : ℕ) : ℚ) := by
    have hsucc : (Nat.factorial (m + 1) : ℚ) = ((m + 1 : ℕ) : ℚ) * (Nat.factorial m : ℚ) := by
      rw [Nat.factorial_succ]
      norm_num [Nat.succ_eq_add_one, mul_comm]
    rw [hsucc]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)]
  rw [hmfac]
  have hle : ((a + 1 : ℕ) : ℚ) ≤ ((m + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_le_succ ha
  exact one_div_le_one_div_of_le hapos hle

lemma weight_raiseAt_le {l a : ℕ} (η : Fin l → ℕ) (k : Fin l) :
    weight a l (raiseAt η k) ≤ (1 / ((a + 1 : ℕ) : ℚ)) * weight a l η := by
  rw [weight_raiseAt_eq]
  have hratio := factorial_ratio_le_inv_succ (a + (k : ℕ) + η k) a (by omega)
  have hw_nonneg : 0 ≤ weight a l η := by
    unfold weight
    exact Finset.prod_nonneg (by intro i hi; positivity)
  calc
    weight a l η * (↑(a + ↑k + η k).factorial : ℚ) / ↑(a + ↑k + η k + 1).factorial
        = weight a l η * ((↑(a + ↑k + η k).factorial : ℚ) / ↑(a + ↑k + η k + 1).factorial) := by ring
    _ ≤ weight a l η * (1 / ((a + 1 : ℕ) : ℚ)) := by
          exact mul_le_mul_of_nonneg_left hratio hw_nonneg
    _ = (1 / ((a + 1 : ℕ) : ℚ)) * weight a l η := by ring

lemma weight_nonneg (a l : ℕ) (δ : Fin l → ℕ) : 0 ≤ weight a l δ := by
  unfold weight
  exact Finset.prod_nonneg (by intro i hi; positivity)

lemma loweringFiber_weight_sum_le {a l N : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    (∑ δ ∈ loweringFiber hl N η, weight a l δ) ≤
      ((2 : ℚ) / (a + 1 : ℕ)) * weight a l η := by
  classical
  let C : ℚ := (1 / ((a + 1 : ℕ) : ℚ)) * weight a l η
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by positivity) (weight_nonneg a l η)
  have heach : ∀ δ ∈ loweringFiber hl N η, weight a l δ ≤ C := by
    intro δ hδ
    have hmem : δ ∈ support l (N + 1) := (Finset.mem_filter.mp hδ).1
    have hmap : lowerLeftmostMax hl δ = η := (Finset.mem_filter.mp hδ).2
    simp [support] at hmem
    rcases hmem with ⟨hbox, hnd, hsum⟩
    have heq : δ = raiseAt η (leftmostMax hl δ) :=
      eq_raiseAt_of_lowerLeftmostMax_eq hl hnd hsum hmap
    rw [heq]
    exact weight_raiseAt_le η (leftmostMax hl δ)
  calc
    (∑ δ ∈ loweringFiber hl N η, weight a l δ) ≤ ∑ δ ∈ loweringFiber hl N η, C := by
      exact Finset.sum_le_sum heach
    _ = ((loweringFiber hl N η).card : ℚ) * C := by simp
    _ ≤ (2 : ℚ) * C := by
      have hcard := card_loweringFiber_le_two (N := N) hl η
      have hcardQ : (((loweringFiber hl N η).card : ℕ) : ℚ) ≤ (2 : ℚ) := by exact_mod_cast hcard
      exact mul_le_mul_of_nonneg_right hcardQ hC_nonneg
    _ = ((2 : ℚ) / (a + 1 : ℕ)) * weight a l η := by
      dsimp [C]
      ring


lemma lowerLeftmostMax_nondecreasing {l : ℕ} (hl : 0 < l) {δ : Fin l → ℕ}
    (hnd : NondecreasingFin δ) : NondecreasingFin (lowerLeftmostMax hl δ) := by
  intro i j hij
  unfold lowerLeftmostMax lowerAt
  by_cases hik : i = leftmostMax hl δ
  · subst i
    by_cases hjk : j = leftmostMax hl δ
    · subst j
      simp
    · simp [hjk]
      have hle : δ (leftmostMax hl δ) ≤ δ j := hnd (leftmostMax hl δ) j hij
      omega
  · by_cases hjk : j = leftmostMax hl δ
    · subst j
      simp [hik]
      have hltij : (i : ℕ) < (leftmostMax hl δ : ℕ) := by
        have hne : (i : ℕ) ≠ (leftmostMax hl δ : ℕ) := by
          intro hv; exact hik (Fin.ext hv)
        omega
      have hlt := value_lt_leftmostMax hl hnd hltij
      omega
    · simp [hik, hjk]
      exact hnd i j hij

lemma sum_lowerAt {l : ℕ} (δ : Fin l → ℕ) (k : Fin l) (hkpos : 0 < δ k) :
    (∑ i : Fin l, lowerAt δ k i) = (∑ i : Fin l, δ i) - 1 := by
  classical
  rw [show (∑ i : Fin l, lowerAt δ k i) = (δ k - 1) + ∑ i ∈ ((Finset.univ : Finset (Fin l)) \ {k}), δ i by
    unfold lowerAt
    rw [show (∑ i : Fin l, (if i = k then δ i - 1 else δ i)) =
        (if k = k then δ k - 1 else δ k) + ∑ i ∈ ((Finset.univ : Finset (Fin l)) \ {k}), (if i = k then δ i - 1 else δ i) by
      simpa using (Finset.sum_eq_add_sum_diff_singleton (s := (Finset.univ : Finset (Fin l))) (i := k) (by simp) (fun i => if i = k then δ i - 1 else δ i))]
    simp
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp at hx
    simp [hx]]
  rw [show (∑ i : Fin l, δ i) = δ k + ∑ i ∈ ((Finset.univ : Finset (Fin l)) \ {k}), δ i by
    simpa using (Finset.sum_eq_add_sum_diff_singleton (s := (Finset.univ : Finset (Fin l))) (i := k) (by simp) δ)]
  omega

lemma lowerLeftmostMax_mem_support {l N : ℕ} (hl : 0 < l) {δ : Fin l → ℕ}
    (hδ : δ ∈ support l (N + 1)) : lowerLeftmostMax hl δ ∈ support l N := by
  classical
  simp [support] at hδ ⊢
  rcases hδ with ⟨hbox, hnd, hsum⟩
  have hkpos : 0 < δ (leftmostMax hl δ) := by
    by_contra hz
    have hz' : δ (leftmostMax hl δ) = 0 := by omega
    have allzero : ∀ i : Fin l, δ i = 0 := by
      intro i
      have hlemax : δ i ≤ δ (leftmostMax hl δ) := by
        have hi_le_last : (i : ℕ) ≤ (lastFin l hl : ℕ) := by dsimp [lastFin]; omega
        have h1 := hnd i (lastFin l hl) hi_le_last
        simpa [leftmostMax_value hl δ] using h1
      omega
    have : (∑ i : Fin l, δ i) = 0 := by simp [allzero]
    omega
  have hsumlower : (∑ i : Fin l, lowerLeftmostMax hl δ i) = N := by
    unfold lowerLeftmostMax
    rw [sum_lowerAt δ (leftmostMax hl δ) hkpos]
    omega
  refine ⟨?_, lowerLeftmostMax_nondecreasing hl hnd, hsumlower⟩
  intro i
  have hle_sum : lowerLeftmostMax hl δ i ≤ ∑ j : Fin l, lowerLeftmostMax hl δ j := by
    simpa using (Finset.single_le_sum (s := (Finset.univ : Finset (Fin l))) (f := lowerLeftmostMax hl δ)
      (by intro x hx; exact Nat.zero_le _) (by simp : i ∈ (Finset.univ : Finset (Fin l))))
  rw [hsumlower] at hle_sum
  omega

lemma D_one_step_bound_pos_l (a l N : ℕ) (hl : 0 < l) :
    D a l (N + 1) ≤ ((2 : ℚ) / (a + 1 : ℕ)) * D a l N := by
  classical
  unfold D
  calc
    (∑ δ ∈ support l (N + 1), weight a l δ)
        = ∑ η ∈ support l N, ∑ δ ∈ (support l (N + 1)).filter (fun δ => lowerLeftmostMax hl δ = η), weight a l δ := by
          rw [Finset.sum_fiberwise_of_maps_to]
          intro δ hδ
          exact lowerLeftmostMax_mem_support hl hδ
    _ ≤ ∑ η ∈ support l N, ((2 : ℚ) / (a + 1 : ℕ)) * weight a l η := by
          refine Finset.sum_le_sum ?_
          intro η hη
          exact loweringFiber_weight_sum_le (a := a) (N := N) hl η
    _ = ((2 : ℚ) / (a + 1 : ℕ)) * (∑ η ∈ support l N, weight a l η) := by
          rw [Finset.mul_sum]

lemma D_one_step_bound_l_zero (a N : ℕ) :
    D a 0 (N + 1) ≤ ((2 : ℚ) / (a + 1 : ℕ)) * D a 0 N := by
  have hleft : D a 0 (N + 1) = 0 := by
    simp [D, support]
  rw [hleft]
  have hnonneg : 0 ≤ D a 0 N := by
    unfold D
    exact Finset.sum_nonneg (by intro δ hδ; exact weight_nonneg a 0 δ)
  exact mul_nonneg (by positivity) hnonneg

lemma D_one_step_bound (a l N : ℕ) :
    D a l (N + 1) ≤ ((2 : ℚ) / (a + 1 : ℕ)) * D a l N := by
  cases l with
  | zero => exact D_one_step_bound_l_zero a N
  | succ l => exact D_one_step_bound_pos_l a (l+1) N (Nat.succ_pos l)

lemma iterated_contraction
    (E : ℕ → ℚ) (c : ℚ)
    (hc : 0 ≤ c)
    (hstep : ∀ n, E (n + 1) ≤ c * E n) :
    ∀ j N : ℕ, E (N + j) ≤ c ^ j * E N := by
  intro j
  induction j with
  | zero => intro N; simp
  | succ j ih =>
      intro N
      calc
        E (N + (j + 1)) = E ((N + j) + 1) := by ring_nf
        _ ≤ c * E (N + j) := hstep (N + j)
        _ ≤ c * (c ^ j * E N) := by
          exact mul_le_mul_of_nonneg_left (ih N) hc
        _ = c ^ (j + 1) * E N := by ring

lemma D_iterated_bound (a l j N : ℕ) :
    D a l (N + j) ≤ (((2 : ℚ) / (a + 1 : ℕ)) ^ j) * D a l N := by
  exact iterated_contraction (D a l) ((2 : ℚ) / (a + 1 : ℕ)) (by positivity)
    (D_one_step_bound a l) j N

lemma sum_image_le_sum {α β M} [DecidableEq β] [AddCommMonoid M] [PartialOrder M] [AddLeftMono M]
    {s : Finset α} {f : α → β} {g : β → M}
    (hg : ∀ b, 0 ≤ g b) :
    (∑ b ∈ s.image f, g b) ≤ ∑ a ∈ s, g (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      by_cases hmem : f a ∈ s.image f
      · have himg : (insert a s).image f = s.image f := by
          ext b
          simp [hmem]
        rw [himg]
        simp [ha]
        exact le_trans ih (le_add_of_nonneg_left (hg (f a)))
      · have himg : (insert a s).image f = insert (f a) (s.image f) := by
          simp
        rw [himg]
        rw [Finset.sum_insert hmem]
        simp [ha]
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left ih (g (f a))

lemma weight_raiseAt_le_index {l a : ℕ} (η : Fin l → ℕ) (k : Fin l) :
    weight a l (raiseAt η k) ≤ (1 / ((a + (k : ℕ) + 1 : ℕ) : ℚ)) * weight a l η := by
  rw [weight_raiseAt_eq]
  have hratio := factorial_ratio_le_inv_succ (a + (k : ℕ) + η k) (a + (k : ℕ)) (by omega)
  have hw_nonneg : 0 ≤ weight a l η := weight_nonneg a l η
  calc
    weight a l η * (↑(a + ↑k + η k).factorial : ℚ) / ↑(a + ↑k + η k + 1).factorial
        = weight a l η * ((↑(a + ↑k + η k).factorial : ℚ) / ↑(a + ↑k + η k + 1).factorial) := by ring
    _ ≤ weight a l η * (1 / ((a + (k : ℕ) + 1 : ℕ) : ℚ)) := by
          exact mul_le_mul_of_nonneg_left hratio hw_nonneg
    _ = (1 / ((a + (k : ℕ) + 1 : ℕ) : ℚ)) * weight a l η := by ring


lemma factorial_ratio_eq_inv_succ (m : ℕ) :
    ((Nat.factorial m : ℚ) / (Nat.factorial (m + 1) : ℚ)) =
      1 / (((m + 1 : ℕ) : ℚ)) := by
  have hsucc : (Nat.factorial (m + 1) : ℚ) =
      (((m + 1 : ℕ) : ℚ)) * (Nat.factorial m : ℚ) := by
    rw [Nat.factorial_succ]
    norm_num [Nat.succ_eq_add_one, mul_comm]
  rw [hsucc]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)]

lemma weight_raiseAt_eq_inv {l a : ℕ} (η : Fin l → ℕ) (k : Fin l) :
    weight a l (raiseAt η k) =
      (1 / (((a + (k : ℕ) + η k + 1 : ℕ) : ℚ))) * weight a l η := by
  rw [weight_raiseAt_eq]
  have hratio := factorial_ratio_eq_inv_succ (a + (k : ℕ) + η k)
  calc
    weight a l η * (↑(a + ↑k + η k).factorial : ℚ) /
        ↑(a + ↑k + η k + 1).factorial
        = weight a l η *
            ((↑(a + ↑k + η k).factorial : ℚ) /
              ↑(a + ↑k + η k + 1).factorial) := by ring
    _ = weight a l η * (1 / (((a + (k : ℕ) + η k + 1 : ℕ) : ℚ))) := by
      rw [hratio]
    _ = (1 / (((a + (k : ℕ) + η k + 1 : ℕ) : ℚ))) * weight a l η := by ring

lemma leftmostMax_raiseAt_last_of_nondecreasing {l : ℕ} (hl : 0 < l)
    {η : Fin l → ℕ} (hnd : NondecreasingFin η) :
    leftmostMax hl (raiseAt η (lastFin l hl)) = lastFin l hl := by
  let δ := raiseAt η (lastFin l hl)
  apply Fin.ext
  change (leftmostMax hl δ : ℕ) = (lastFin l hl : ℕ)
  have hle : (leftmostMax hl δ : ℕ) ≤ (lastFin l hl : ℕ) :=
    leftmostMax_le_of_value hl δ (i := lastFin l hl) rfl
  by_contra hne
  have hlt : (leftmostMax hl δ : ℕ) < (lastFin l hl : ℕ) := by omega
  have hne_fin : leftmostMax hl δ ≠ lastFin l hl := by
    intro h
    exact hne (congrArg Fin.val h)
  have hδ_lm : δ (leftmostMax hl δ) = η (leftmostMax hl δ) := by
    simp [δ, raiseAt, hne_fin]
  have hδ_last : δ (lastFin l hl) = η (lastFin l hl) + 1 := by
    simp [δ, raiseAt]
  have hη_le : η (leftmostMax hl δ) ≤ η (lastFin l hl) := hnd _ _ hle
  have hval := leftmostMax_value hl δ
  rw [hδ_lm, hδ_last] at hval
  omega

/-- After the first legal raise is the last index, for `a = 3` the remaining
legal branch consists of raising the last index once more and possibly raising
its unique predecessor.  This gives the exact two-denominator bound used for the
`R`-branch. -/
lemma legalRaise_sum_after_raise_last_a3 {l N : ℕ} (hl : 0 < l)
    {η : Fin l → ℕ} (hη : η ∈ support l N) :
    let M : ℕ := η (lastFin l hl)
    ∑ j ∈ legalRaiseIndices hl (raiseAt η (lastFin l hl)),
        weight 3 l (raiseAt (raiseAt η (lastFin l hl)) j)
      ≤ ((1 / (((M + l + 3 : ℕ) : ℚ))) *
          (1 / (((M + l + 4 : ℕ) : ℚ)) +
            1 / (((M + l + 2 : ℕ) : ℚ)))) * weight 3 l η := by
  classical
  rw [support] at hη
  rcases (Finset.mem_filter.mp hη).2 with ⟨hnd, hsum⟩
  let last := lastFin l hl
  let M : ℕ := η last
  let δ : Fin l → ℕ := raiseAt η last
  have hδlast : δ last = M + 1 := by
    dsimp [δ, M, last]
    simp [raiseAt]
  have hleft : leftmostMax hl δ = last := by
    simpa [δ, last] using leftmostMax_raiseAt_last_of_nondecreasing hl hnd
  let P : Finset (Fin l) := (predecessorRaiseIndices hl δ).filter
    (fun k => k = lastFin l hl ∨ δ k + 1 = δ (lastFin l hl))
  have hlast_notin_pred : lastFin l hl ∉ predecessorRaiseIndices hl δ := by
    simp [predecessorRaiseIndices, lastFin]
    intro hbad
    omega
  have hlegal_eq : legalRaiseIndices hl δ = insert (lastFin l hl) P := by
    ext k
    by_cases hk : k = lastFin l hl
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, P, hk]
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, P, hk]
  have hlast_bound : weight 3 l (raiseAt δ (lastFin l hl)) ≤
      (1 / (((M + l + 4 : ℕ) : ℚ))) * weight 3 l δ := by
    have h := weight_raiseAt_eq_inv (a := 3) δ (lastFin l hl)
    have hden : 3 + (lastFin l hl : ℕ) + δ (lastFin l hl) + 1 = M + l + 4 := by
      have hδlast' : δ (lastFin l hl) = M + 1 := by simpa [last] using hδlast
      rw [hδlast']
      dsimp [lastFin]
      omega
    rw [h]
    exact le_of_eq (by simp [hden])
  have hpred_each : ∀ k ∈ P,
      weight 3 l (raiseAt δ k) ≤
        (1 / (((M + l + 2 : ℕ) : ℚ))) * weight 3 l δ := by
    intro k hkP
    have hkpred : k ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hkP).1
    have hkcond : k = lastFin l hl ∨ δ k + 1 = δ (lastFin l hl) :=
      (Finset.mem_filter.mp hkP).2
    have hk_ne_last : k ≠ lastFin l hl := by
      intro hkl
      exact hlast_notin_pred (by simpa [hkl] using hkpred)
    have hδk : δ k = M := by
      cases hkcond with
      | inl hkl => exact False.elim (hk_ne_last hkl)
      | inr hval =>
          rw [hδlast] at hval
          omega
    have hk_succ_last : (k : ℕ) + 1 = (lastFin l hl : ℕ) := by
      rw [predecessorRaiseIndices] at hkpred
      rcases (Finset.mem_filter.mp hkpred).2 with ⟨hklt, hkeq⟩
      have hv : lastFin l hl = (⟨(k : ℕ) + 1, hklt⟩ : Fin l) := by
        simpa [hleft] using hkeq
      exact (congrArg Fin.val hv).symm
    have h := weight_raiseAt_eq_inv (a := 3) δ k
    have hden : 3 + (k : ℕ) + δ k + 1 = M + l + 2 := by
      dsimp [lastFin] at hk_succ_last
      omega
    rw [h]
    exact le_of_eq (by simp [hden])
  have hP_card : P.card ≤ 1 := by
    exact le_trans (Finset.card_filter_le _ _) (card_predecessorRaiseIndices_le_one hl δ)
  have hP_cardQ : (P.card : ℚ) ≤ (1 : ℚ) := by exact_mod_cast hP_card
  have hpred_nonneg : 0 ≤ (1 / (((M + l + 2 : ℕ) : ℚ))) * weight 3 l δ :=
    mul_nonneg (by positivity) (weight_nonneg 3 l δ)
  have hsum_delta :
      (∑ j ∈ legalRaiseIndices hl δ, weight 3 l (raiseAt δ j)) ≤
        (1 / (((M + l + 4 : ℕ) : ℚ))) * weight 3 l δ +
          (1 / (((M + l + 2 : ℕ) : ℚ))) * weight 3 l δ := by
    calc
      (∑ j ∈ legalRaiseIndices hl δ, weight 3 l (raiseAt δ j))
          = ∑ j ∈ insert (lastFin l hl) P, weight 3 l (raiseAt δ j) := by rw [hlegal_eq]
      _ = weight 3 l (raiseAt δ (lastFin l hl)) + ∑ j ∈ P, weight 3 l (raiseAt δ j) := by
        rw [Finset.sum_insert]
        intro hmem
        have : lastFin l hl ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hmem).1
        exact hlast_notin_pred this
      _ ≤ (1 / (((M + l + 4 : ℕ) : ℚ))) * weight 3 l δ +
            ∑ j ∈ P, (1 / (((M + l + 2 : ℕ) : ℚ))) * weight 3 l δ := by
        exact add_le_add hlast_bound (Finset.sum_le_sum hpred_each)
      _ ≤ (1 / (((M + l + 4 : ℕ) : ℚ))) * weight 3 l δ +
            (1 / (((M + l + 2 : ℕ) : ℚ))) * weight 3 l δ := by
        rw [Finset.sum_const]
        simp
        exact mul_le_of_le_one_left (by simpa using hpred_nonneg) hP_cardQ
  have hfirst : weight 3 l δ =
      (1 / (((M + l + 3 : ℕ) : ℚ))) * weight 3 l η := by
    have h := weight_raiseAt_eq_inv (a := 3) η (lastFin l hl)
    have hden : 3 + (lastFin l hl : ℕ) + η (lastFin l hl) + 1 = M + l + 3 := by
      have hMlast : η (lastFin l hl) = M := by simp [M, last]
      rw [hMlast]
      dsimp [lastFin]
      omega
    rw [h]
    simp [hden, M, last]
  dsimp [M, last, δ] at hsum_delta hfirst ⊢
  rw [hfirst] at hsum_delta
  convert hsum_delta using 1
  ring


/-- After the first legal raise is a non-last predecessor index `k`, for `a = 3`
the next legal raises are the last index and possibly the unique predecessor of
`k`.  This is the value-dependent `L`-branch analogue of
`legalRaise_sum_after_raise_last_a3`. -/
lemma legalRaise_sum_after_raise_nonlast_a3 {l N : ℕ} (hl : 0 < l)
    {η : Fin l → ℕ} (hη : η ∈ support l N) {k : Fin l}
    (hklegal : k ∈ legalRaiseIndices hl η) (hk_ne_last : k ≠ lastFin l hl) :
    let M : ℕ := η (lastFin l hl)
    ∑ j ∈ legalRaiseIndices hl (raiseAt η k),
        weight 3 l (raiseAt (raiseAt η k) j)
      ≤ ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
          (1 / (((M + l + 3 : ℕ) : ℚ)) +
            1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ)))) * weight 3 l η := by
  classical
  rw [support] at hη
  rcases (Finset.mem_filter.mp hη).2 with ⟨hnd, hsum⟩
  let last := lastFin l hl
  let M : ℕ := η last
  let δ : Fin l → ℕ := raiseAt η k
  have hδlast : δ last = M := by
    dsimp [δ, M, last]
    by_cases h : lastFin l hl = k
    · exact False.elim (hk_ne_last h.symm)
    · simp [raiseAt, h]
  have hk_mem_corr : k ∈ correctedCandidateRaiseIndices hl η :=
    (Finset.mem_filter.mp hklegal).1
  have hk_cond : k = lastFin l hl ∨ η k + 1 = η (lastFin l hl) :=
    (Finset.mem_filter.mp hklegal).2
  have hηk_succ : η k + 1 = M := by
    cases hk_cond with
    | inl hkl => exact False.elim (hk_ne_last hkl)
    | inr hval => simpa [M, last] using hval
  have hηk : η k = M - 1 := by omega
  have hδk : δ k = M := by
    dsimp [δ]
    simp [raiseAt, hηk_succ]
  have hk_mem_pred : k ∈ predecessorRaiseIndices hl η := by
    rw [correctedCandidateRaiseIndices] at hk_mem_corr
    exact (Finset.mem_insert.mp hk_mem_corr).resolve_left hk_ne_last
  have hk_succ_lt : (k : ℕ) + 1 < l := by
    rw [predecessorRaiseIndices] at hk_mem_pred
    exact (Finset.mem_filter.mp hk_mem_pred).2.1
  let ksucc : Fin l := ⟨(k : ℕ) + 1, hk_succ_lt⟩
  have hleft_eta : leftmostMax hl η = ksucc := by
    rw [predecessorRaiseIndices] at hk_mem_pred
    exact (Finset.mem_filter.mp hk_mem_pred).2.2
  have hη_ksucc : η ksucc = M := by
    calc
      η ksucc = η (leftmostMax hl η) := by rw [hleft_eta]
      _ = η (lastFin l hl) := leftmostMax_value hl η
      _ = M := by simp [M, last]
  have hleft : leftmostMax hl δ = k := by
    apply Fin.ext
    have hle_k : (leftmostMax hl δ : ℕ) ≤ (k : ℕ) := by
      apply leftmostMax_le_of_value hl δ
      rw [hδk, hδlast]
    by_contra hne_val
    have hlt_k : (leftmostMax hl δ : ℕ) < (k : ℕ) := by omega
    have hlt_lm_eta : (leftmostMax hl δ : ℕ) < (leftmostMax hl η : ℕ) := by
      rw [hleft_eta]
      simp [ksucc]
      omega
    have hlm_ne_k : leftmostMax hl δ ≠ k := by
      intro h
      exact hne_val (congrArg Fin.val h)
    have hδ_lm : δ (leftmostMax hl δ) = η (leftmostMax hl δ) := by
      dsimp [δ]
      by_cases h : leftmostMax hl (raiseAt η k) = k
      · exact False.elim (hlm_ne_k h)
      · simp [raiseAt, h]
    have hlt_val : η (leftmostMax hl δ) < M := by
      have h := value_lt_leftmostMax hl hnd hlt_lm_eta
      simpa [hη_ksucc, hleft_eta] using h
    have hδ_lm_eq_M : δ (leftmostMax hl δ) = M := by
      calc
        δ (leftmostMax hl δ) = δ (lastFin l hl) := leftmostMax_value hl δ
        _ = M := hδlast
    rw [hδ_lm] at hδ_lm_eq_M
    omega
  let P : Finset (Fin l) := (predecessorRaiseIndices hl δ).filter
    (fun j => j = lastFin l hl ∨ δ j + 1 = δ (lastFin l hl))
  have hlast_notin_pred : lastFin l hl ∉ predecessorRaiseIndices hl δ := by
    simp [predecessorRaiseIndices, lastFin]
    intro hbad
    omega
  have hlegal_eq : legalRaiseIndices hl δ = insert (lastFin l hl) P := by
    ext j
    by_cases hj : j = lastFin l hl
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, P, hj]
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, P, hj]
  have hlast_bound : weight 3 l (raiseAt δ (lastFin l hl)) ≤
      (1 / (((M + l + 3 : ℕ) : ℚ))) * weight 3 l δ := by
    have h := weight_raiseAt_eq_inv (a := 3) δ (lastFin l hl)
    have hden : 3 + (lastFin l hl : ℕ) + δ (lastFin l hl) + 1 = M + l + 3 := by
      have hδlast' : δ (lastFin l hl) = M := by simpa [last] using hδlast
      rw [hδlast']
      dsimp [lastFin]
      omega
    rw [h]
    exact le_of_eq (by simp [hden])
  have hpred_each : ∀ j ∈ P,
      weight 3 l (raiseAt δ j) ≤
        (1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ))) * weight 3 l δ := by
    intro j hjP
    have hjpred : j ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hjP).1
    have hjcond : j = lastFin l hl ∨ δ j + 1 = δ (lastFin l hl) :=
      (Finset.mem_filter.mp hjP).2
    have hj_ne_last : j ≠ lastFin l hl := by
      intro hjl
      exact hlast_notin_pred (by simpa [hjl] using hjpred)
    have hδj_succ : δ j + 1 = M := by
      cases hjcond with
      | inl hjl => exact False.elim (hj_ne_last hjl)
      | inr hval =>
          have hδlast' : δ (lastFin l hl) = M := by simpa [last] using hδlast
          simpa [hδlast'] using hval
    have hj_succ_k : (j : ℕ) + 1 = (k : ℕ) := by
      rw [predecessorRaiseIndices] at hjpred
      rcases (Finset.mem_filter.mp hjpred).2 with ⟨hjlt, hjeq⟩
      have hv : k = (⟨(j : ℕ) + 1, hjlt⟩ : Fin l) := by
        simpa [hleft] using hjeq
      exact (congrArg Fin.val hv).symm
    have h := weight_raiseAt_eq_inv (a := 3) δ j
    have hden : 3 + (j : ℕ) + δ j + 1 = M + (k : ℕ) + 2 := by
      omega
    rw [h]
    exact le_of_eq (by simp [hden])
  have hP_card : P.card ≤ 1 := by
    exact le_trans (Finset.card_filter_le _ _) (card_predecessorRaiseIndices_le_one hl δ)
  have hP_cardQ : (P.card : ℚ) ≤ (1 : ℚ) := by exact_mod_cast hP_card
  have hpred_nonneg : 0 ≤ (1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ))) * weight 3 l δ :=
    mul_nonneg (by positivity) (weight_nonneg 3 l δ)
  have hsum_delta :
      (∑ j ∈ legalRaiseIndices hl δ, weight 3 l (raiseAt δ j)) ≤
        (1 / (((M + l + 3 : ℕ) : ℚ))) * weight 3 l δ +
          (1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ))) * weight 3 l δ := by
    calc
      (∑ j ∈ legalRaiseIndices hl δ, weight 3 l (raiseAt δ j))
          = ∑ j ∈ insert (lastFin l hl) P, weight 3 l (raiseAt δ j) := by rw [hlegal_eq]
      _ = weight 3 l (raiseAt δ (lastFin l hl)) + ∑ j ∈ P, weight 3 l (raiseAt δ j) := by
        rw [Finset.sum_insert]
        intro hmem
        have : lastFin l hl ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hmem).1
        exact hlast_notin_pred this
      _ ≤ (1 / (((M + l + 3 : ℕ) : ℚ))) * weight 3 l δ +
            ∑ j ∈ P, (1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ))) * weight 3 l δ := by
        exact add_le_add hlast_bound (Finset.sum_le_sum hpred_each)
      _ ≤ (1 / (((M + l + 3 : ℕ) : ℚ))) * weight 3 l δ +
            (1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ))) * weight 3 l δ := by
        rw [Finset.sum_const]
        simp
        exact mul_le_of_le_one_left (by simpa using hpred_nonneg) hP_cardQ
  have hfirst : weight 3 l δ =
      (1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * weight 3 l η := by
    have h := weight_raiseAt_eq_inv (a := 3) η k
    have hden : 3 + (k : ℕ) + η k + 1 = M + (k : ℕ) + 3 := by
      omega
    rw [h]
    simp [hden, M, last]
  dsimp [M, last, δ] at hsum_delta hfirst ⊢
  rw [hfirst] at hsum_delta
  convert hsum_delta using 1
  ring

/-- Sharpened `L`-branch for the boundary predecessor `k = 0`: after raising `k`,
there is no predecessor of the new leftmost maximum, so the second-step legal
raises contain only the last index. -/
lemma legalRaise_sum_after_raise_nonlast_k_zero_a3 {l N : ℕ} (hl : 0 < l)
    {η : Fin l → ℕ} (hη : η ∈ support l N) {k : Fin l}
    (hklegal : k ∈ legalRaiseIndices hl η) (hk_ne_last : k ≠ lastFin l hl)
    (hk_zero : (k : ℕ) = 0) :
    let M : ℕ := η (lastFin l hl)
    ∑ j ∈ legalRaiseIndices hl (raiseAt η k),
        weight 3 l (raiseAt (raiseAt η k) j)
      ≤ ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
          (1 / (((M + l + 3 : ℕ) : ℚ)))) * weight 3 l η := by
  classical
  rw [support] at hη
  rcases (Finset.mem_filter.mp hη).2 with ⟨hnd, hsum⟩
  let last := lastFin l hl
  let M : ℕ := η last
  let δ : Fin l → ℕ := raiseAt η k
  have hδlast : δ last = M := by
    dsimp [δ, M, last]
    by_cases h : lastFin l hl = k
    · exact False.elim (hk_ne_last h.symm)
    · simp [raiseAt, h]
  have hk_mem_corr : k ∈ correctedCandidateRaiseIndices hl η :=
    (Finset.mem_filter.mp hklegal).1
  have hk_cond : k = lastFin l hl ∨ η k + 1 = η (lastFin l hl) :=
    (Finset.mem_filter.mp hklegal).2
  have hηk_succ : η k + 1 = M := by
    cases hk_cond with
    | inl hkl => exact False.elim (hk_ne_last hkl)
    | inr hval => simpa [M, last] using hval
  have hδk : δ k = M := by
    dsimp [δ]
    simp [raiseAt, hηk_succ]
  have hk_mem_pred : k ∈ predecessorRaiseIndices hl η := by
    rw [correctedCandidateRaiseIndices] at hk_mem_corr
    exact (Finset.mem_insert.mp hk_mem_corr).resolve_left hk_ne_last
  have hk_succ_lt : (k : ℕ) + 1 < l := by
    rw [predecessorRaiseIndices] at hk_mem_pred
    exact (Finset.mem_filter.mp hk_mem_pred).2.1
  let ksucc : Fin l := ⟨(k : ℕ) + 1, hk_succ_lt⟩
  have hleft_eta : leftmostMax hl η = ksucc := by
    rw [predecessorRaiseIndices] at hk_mem_pred
    exact (Finset.mem_filter.mp hk_mem_pred).2.2
  have hη_ksucc : η ksucc = M := by
    calc
      η ksucc = η (leftmostMax hl η) := by rw [hleft_eta]
      _ = η (lastFin l hl) := leftmostMax_value hl η
      _ = M := by simp [M, last]
  have hleft : leftmostMax hl δ = k := by
    apply Fin.ext
    have hle_k : (leftmostMax hl δ : ℕ) ≤ (k : ℕ) := by
      apply leftmostMax_le_of_value hl δ
      rw [hδk, hδlast]
    by_contra hne_val
    have hlt_k : (leftmostMax hl δ : ℕ) < (k : ℕ) := by omega
    have hlt_lm_eta : (leftmostMax hl δ : ℕ) < (leftmostMax hl η : ℕ) := by
      rw [hleft_eta]
      simp [ksucc]
      omega
    have hlm_ne_k : leftmostMax hl δ ≠ k := by
      intro h
      exact hne_val (congrArg Fin.val h)
    have hδ_lm : δ (leftmostMax hl δ) = η (leftmostMax hl δ) := by
      dsimp [δ]
      by_cases h : leftmostMax hl (raiseAt η k) = k
      · exact False.elim (hlm_ne_k h)
      · simp [raiseAt, h]
    have hlt_val : η (leftmostMax hl δ) < M := by
      have h := value_lt_leftmostMax hl hnd hlt_lm_eta
      simpa [hη_ksucc, hleft_eta] using h
    have hδ_lm_eq_M : δ (leftmostMax hl δ) = M := by
      calc
        δ (leftmostMax hl δ) = δ (lastFin l hl) := leftmostMax_value hl δ
        _ = M := hδlast
    rw [hδ_lm] at hδ_lm_eq_M
    omega
  let P : Finset (Fin l) := (predecessorRaiseIndices hl δ).filter
    (fun j => j = lastFin l hl ∨ δ j + 1 = δ (lastFin l hl))
  have hlast_notin_pred : lastFin l hl ∉ predecessorRaiseIndices hl δ := by
    simp [predecessorRaiseIndices, lastFin]
    intro hbad
    omega
  have hlegal_eq : legalRaiseIndices hl δ = insert (lastFin l hl) P := by
    ext j
    by_cases hj : j = lastFin l hl
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, P, hj]
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, P, hj]
  have hP_empty : P = ∅ := by
    ext j
    simp
    intro hjP
    have hjpred : j ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hjP).1
    rw [predecessorRaiseIndices] at hjpred
    rcases (Finset.mem_filter.mp hjpred).2 with ⟨hjlt, hjeq⟩
    have hj_succ_k : (j : ℕ) + 1 = (k : ℕ) := by
      have hv : k = (⟨(j : ℕ) + 1, hjlt⟩ : Fin l) := by
        simpa [hleft] using hjeq
      exact (congrArg Fin.val hv).symm
    omega
  have hlast_bound : weight 3 l (raiseAt δ (lastFin l hl)) ≤
      (1 / (((M + l + 3 : ℕ) : ℚ))) * weight 3 l δ := by
    have h := weight_raiseAt_eq_inv (a := 3) δ (lastFin l hl)
    have hden : 3 + (lastFin l hl : ℕ) + δ (lastFin l hl) + 1 = M + l + 3 := by
      have hδlast' : δ (lastFin l hl) = M := by simpa [last] using hδlast
      rw [hδlast']
      dsimp [lastFin]
      omega
    rw [h]
    exact le_of_eq (by simp [hden])
  have hsum_delta :
      (∑ j ∈ legalRaiseIndices hl δ, weight 3 l (raiseAt δ j)) ≤
        (1 / (((M + l + 3 : ℕ) : ℚ))) * weight 3 l δ := by
    calc
      (∑ j ∈ legalRaiseIndices hl δ, weight 3 l (raiseAt δ j))
          = ∑ j ∈ insert (lastFin l hl) P, weight 3 l (raiseAt δ j) := by rw [hlegal_eq]
      _ = weight 3 l (raiseAt δ (lastFin l hl)) + ∑ j ∈ P, weight 3 l (raiseAt δ j) := by
        rw [Finset.sum_insert]
        intro hmem
        have : lastFin l hl ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hmem).1
        exact hlast_notin_pred this
      _ = weight 3 l (raiseAt δ (lastFin l hl)) := by
        rw [hP_empty]
        simp
      _ ≤ (1 / (((M + l + 3 : ℕ) : ℚ))) * weight 3 l δ := hlast_bound
  have hfirst : weight 3 l δ =
      (1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * weight 3 l η := by
    have h := weight_raiseAt_eq_inv (a := 3) η k
    have hden : 3 + (k : ℕ) + η k + 1 = M + (k : ℕ) + 3 := by
      omega
    rw [h]
    simp [hden, M, last]
  dsimp [M, last, δ] at hsum_delta hfirst ⊢
  rw [hfirst] at hsum_delta
  convert hsum_delta using 1
  ring

/-- Sharpened `R`-branch when a legal predecessor is immediately before the last
index.  After raising the last index, that predecessor is still two below the new
last value, so no predecessor term is legal in the second step. -/
lemma legalRaise_sum_after_raise_last_no_pred_a3 {l N : ℕ} (hl : 0 < l)
    {η : Fin l → ℕ} (hη : η ∈ support l N) {k : Fin l}
    (hklegal : k ∈ legalRaiseIndices hl η) (hk_ne_last : k ≠ lastFin l hl)
    (hk_succ_last : (k : ℕ) + 1 = (lastFin l hl : ℕ)) :
    let M : ℕ := η (lastFin l hl)
    ∑ j ∈ legalRaiseIndices hl (raiseAt η (lastFin l hl)),
        weight 3 l (raiseAt (raiseAt η (lastFin l hl)) j)
      ≤ ((1 / (((M + l + 3 : ℕ) : ℚ))) *
          (1 / (((M + l + 4 : ℕ) : ℚ)))) * weight 3 l η := by
  classical
  rw [support] at hη
  rcases (Finset.mem_filter.mp hη).2 with ⟨hnd, hsum⟩
  let last := lastFin l hl
  let M : ℕ := η last
  let δ : Fin l → ℕ := raiseAt η last
  have hδlast : δ last = M + 1 := by
    dsimp [δ, M, last]
    simp [raiseAt]
  have hk_cond : k = lastFin l hl ∨ η k + 1 = η (lastFin l hl) :=
    (Finset.mem_filter.mp hklegal).2
  have hηk_succ : η k + 1 = M := by
    cases hk_cond with
    | inl hkl => exact False.elim (hk_ne_last hkl)
    | inr hval => simpa [M, last] using hval
  have hleft : leftmostMax hl δ = last := by
    simpa [δ, last] using leftmostMax_raiseAt_last_of_nondecreasing hl hnd
  let P : Finset (Fin l) := (predecessorRaiseIndices hl δ).filter
    (fun j => j = lastFin l hl ∨ δ j + 1 = δ (lastFin l hl))
  have hlast_notin_pred : lastFin l hl ∉ predecessorRaiseIndices hl δ := by
    simp [predecessorRaiseIndices, lastFin]
    intro hbad
    omega
  have hlegal_eq : legalRaiseIndices hl δ = insert (lastFin l hl) P := by
    ext j
    by_cases hj : j = lastFin l hl
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, P, hj]
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, P, hj]
  have hP_empty : P = ∅ := by
    ext j
    simp
    intro hjP
    have hjpred : j ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hjP).1
    have hjcond : j = lastFin l hl ∨ δ j + 1 = δ (lastFin l hl) :=
      (Finset.mem_filter.mp hjP).2
    have hj_ne_last : j ≠ lastFin l hl := by
      intro hjl
      exact hlast_notin_pred (by simpa [hjl] using hjpred)
    have hδj_succ : δ j + 1 = M + 1 := by
      cases hjcond with
      | inl hjl => exact False.elim (hj_ne_last hjl)
      | inr hval =>
          have hδlast' : δ (lastFin l hl) = M + 1 := by simpa [last] using hδlast
          simpa [hδlast'] using hval
    have hj_succ_last : (j : ℕ) + 1 = (lastFin l hl : ℕ) := by
      rw [predecessorRaiseIndices] at hjpred
      rcases (Finset.mem_filter.mp hjpred).2 with ⟨hjlt, hjeq⟩
      have hv : lastFin l hl = (⟨(j : ℕ) + 1, hjlt⟩ : Fin l) := by
        simpa [hleft] using hjeq
      exact (congrArg Fin.val hv).symm
    have hj_eq_k : j = k := by
      apply Fin.ext
      omega
    have hδj_eq : δ j = η k := by
      subst j
      dsimp [δ]
      have hkl : k ≠ last := by simpa [last] using hk_ne_last
      simp [raiseAt, hkl]
    rw [hδj_eq] at hδj_succ
    omega
  have hlast_bound : weight 3 l (raiseAt δ (lastFin l hl)) ≤
      (1 / (((M + l + 4 : ℕ) : ℚ))) * weight 3 l δ := by
    have h := weight_raiseAt_eq_inv (a := 3) δ (lastFin l hl)
    have hden : 3 + (lastFin l hl : ℕ) + δ (lastFin l hl) + 1 = M + l + 4 := by
      have hδlast' : δ (lastFin l hl) = M + 1 := by simpa [last] using hδlast
      rw [hδlast']
      dsimp [lastFin]
      omega
    rw [h]
    exact le_of_eq (by simp [hden])
  have hsum_delta :
      (∑ j ∈ legalRaiseIndices hl δ, weight 3 l (raiseAt δ j)) ≤
        (1 / (((M + l + 4 : ℕ) : ℚ))) * weight 3 l δ := by
    calc
      (∑ j ∈ legalRaiseIndices hl δ, weight 3 l (raiseAt δ j))
          = ∑ j ∈ insert (lastFin l hl) P, weight 3 l (raiseAt δ j) := by rw [hlegal_eq]
      _ = weight 3 l (raiseAt δ (lastFin l hl)) + ∑ j ∈ P, weight 3 l (raiseAt δ j) := by
        rw [Finset.sum_insert]
        intro hmem
        have : lastFin l hl ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hmem).1
        exact hlast_notin_pred this
      _ = weight 3 l (raiseAt δ (lastFin l hl)) := by
        rw [hP_empty]
        simp
      _ ≤ (1 / (((M + l + 4 : ℕ) : ℚ))) * weight 3 l δ := hlast_bound
  have hfirst : weight 3 l δ =
      (1 / (((M + l + 3 : ℕ) : ℚ))) * weight 3 l η := by
    have h := weight_raiseAt_eq_inv (a := 3) η (lastFin l hl)
    have hden : 3 + (lastFin l hl : ℕ) + η (lastFin l hl) + 1 = M + l + 3 := by
      have hMlast : η (lastFin l hl) = M := by simp [M, last]
      rw [hMlast]
      dsimp [lastFin]
      omega
    rw [h]
    simp [hden, M, last]
  dsimp [M, last, δ] at hsum_delta hfirst ⊢
  rw [hfirst] at hsum_delta
  convert hsum_delta using 1
  ring


lemma sum_candidatePreimages_le_sum_indices {a l : ℕ} (η : Fin l → ℕ) (A : Finset (Fin l)) :
    (∑ δ ∈ A.image (fun k => raiseAt η k), weight a l δ) ≤
      ∑ k ∈ A, weight a l (raiseAt η k) := by
  classical
  exact sum_image_le_sum (s := A) (f := fun k => raiseAt η k) (g := weight a l) (weight_nonneg a l)

lemma loweringFiber_weight_sum_le_sharp_a2 {l N : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    (∑ δ ∈ loweringFiber hl N η, weight 2 l δ) ≤
      ((1 : ℚ) / 3 + (1 : ℚ) / (l + 2 : ℕ)) * weight 2 l η := by
  classical
  have hsubset := loweringFiber_subset_candidatePreimages (N := N) hl η
  have hsubsum : (∑ δ ∈ loweringFiber hl N η, weight 2 l δ) ≤
      ∑ δ ∈ candidatePreimages hl η, weight 2 l δ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by intro x hx hnot; exact weight_nonneg 2 l x)
  have himage : (∑ δ ∈ candidatePreimages hl η, weight 2 l δ) ≤
      ∑ k ∈ correctedCandidateRaiseIndices hl η, weight 2 l (raiseAt η k) := by
    exact sum_candidatePreimages_le_sum_indices η (correctedCandidateRaiseIndices hl η)
  have hlast_bound : weight 2 l (raiseAt η (lastFin l hl)) ≤
      (1 / ((l + 2 : ℕ) : ℚ)) * weight 2 l η := by
    have h := weight_raiseAt_le_index (a := 2) η (lastFin l hl)
    have hden_nat : 2 + (lastFin l hl : ℕ) + 1 = l + 2 := by
      dsimp [lastFin]
      omega
    simpa [hden_nat] using h
  have hpred_each : ∀ k ∈ predecessorRaiseIndices hl η,
      weight 2 l (raiseAt η k) ≤ (1 / (3 : ℚ)) * weight 2 l η := by
    intro k hk
    simpa using (weight_raiseAt_le (a := 2) η k)
  have hlast_notin : lastFin l hl ∉ predecessorRaiseIndices hl η := by
    simp [predecessorRaiseIndices, lastFin]
    intro hbad
    omega
  calc
    (∑ δ ∈ loweringFiber hl N η, weight 2 l δ) ≤
        ∑ k ∈ correctedCandidateRaiseIndices hl η, weight 2 l (raiseAt η k) := le_trans hsubsum himage
    _ = weight 2 l (raiseAt η (lastFin l hl)) + ∑ k ∈ predecessorRaiseIndices hl η, weight 2 l (raiseAt η k) := by
      unfold correctedCandidateRaiseIndices
      rw [Finset.sum_insert hlast_notin]
    _ ≤ (1 / ((l + 2 : ℕ) : ℚ)) * weight 2 l η + ∑ k ∈ predecessorRaiseIndices hl η, (1 / (3 : ℚ)) * weight 2 l η := by
      exact add_le_add hlast_bound (Finset.sum_le_sum hpred_each)
    _ ≤ (1 / ((l + 2 : ℕ) : ℚ)) * weight 2 l η + (1 / (3 : ℚ)) * weight 2 l η := by
      have hcard := card_predecessorRaiseIndices_le_one hl η
      have hcardQ : ((predecessorRaiseIndices hl η).card : ℚ) ≤ (1 : ℚ) := by exact_mod_cast hcard
      have hnon : 0 ≤ (1 / (3 : ℚ)) * weight 2 l η := mul_nonneg (by norm_num) (weight_nonneg 2 l η)
      rw [Finset.sum_const]
      simp
      exact mul_le_of_le_one_left (by simpa using hnon) hcardQ
    _ = ((1 : ℚ) / 3 + (1 : ℚ) / (l + 2 : ℕ)) * weight 2 l η := by ring

lemma D_one_step_bound_sharp_a2_pos_l (l N : ℕ) (hl : 0 < l) :
    D 2 l (N + 1) ≤ (((1 : ℚ) / 3 + (1 : ℚ) / (l + 2 : ℕ))) * D 2 l N := by
  classical
  unfold D
  calc
    (∑ δ ∈ support l (N + 1), weight 2 l δ)
        = ∑ η ∈ support l N, ∑ δ ∈ (support l (N + 1)).filter (fun δ => lowerLeftmostMax hl δ = η), weight 2 l δ := by
          rw [Finset.sum_fiberwise_of_maps_to]
          intro δ hδ
          exact lowerLeftmostMax_mem_support hl hδ
    _ ≤ ∑ η ∈ support l N, (((1 : ℚ) / 3 + (1 : ℚ) / (l + 2 : ℕ))) * weight 2 l η := by
          refine Finset.sum_le_sum ?_
          intro η hη
          exact loweringFiber_weight_sum_le_sharp_a2 (N := N) hl η
    _ = (((1 : ℚ) / 3 + (1 : ℚ) / (l + 2 : ℕ))) * (∑ η ∈ support l N, weight 2 l η) := by
          rw [Finset.mul_sum]

lemma D_one_step_bound_sharp_a2 (l N : ℕ) :
    D 2 l (N + 1) ≤ (((1 : ℚ) / 3 + (1 : ℚ) / (l + 2 : ℕ))) * D 2 l N := by
  cases l with
  | zero =>
      have h := D_one_step_bound_l_zero 2 N
      have hnon : 0 ≤ D 2 0 N := by
        unfold D
        exact Finset.sum_nonneg (by intro δ hδ; exact weight_nonneg 2 0 δ)
      have hcoef : ((2 : ℚ) / (2 + 1 : ℕ)) ≤ ((1 : ℚ) / 3 + (1 : ℚ) / (0 + 2 : ℕ)) := by norm_num
      exact le_trans h (mul_le_mul_of_nonneg_right hcoef hnon)
  | succ l => exact D_one_step_bound_sharp_a2_pos_l (l+1) N (Nat.succ_pos l)




end DOneStepNoAxiom


namespace DOneStepNoAxiom

lemma loweringFiber_weight_sum_le_sharp_general {a l N : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    (∑ δ ∈ loweringFiber hl N η, weight a l δ) ≤
      ((1 : ℚ) / (a + 1 : ℕ) + (1 : ℚ) / (a + l : ℕ)) * weight a l η := by
  classical
  have hsubset := loweringFiber_subset_candidatePreimages (N := N) hl η
  have hsubsum : (∑ δ ∈ loweringFiber hl N η, weight a l δ) ≤
      ∑ δ ∈ candidatePreimages hl η, weight a l δ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by intro x hx hnot; exact weight_nonneg a l x)
  have himage : (∑ δ ∈ candidatePreimages hl η, weight a l δ) ≤
      ∑ k ∈ correctedCandidateRaiseIndices hl η, weight a l (raiseAt η k) := by
    exact sum_candidatePreimages_le_sum_indices η (correctedCandidateRaiseIndices hl η)
  have hlast_bound : weight a l (raiseAt η (lastFin l hl)) ≤
      (1 / ((a + l : ℕ) : ℚ)) * weight a l η := by
    have h := weight_raiseAt_le_index (a := a) η (lastFin l hl)
    have hden_nat : a + (lastFin l hl : ℕ) + 1 = a + l := by
      dsimp [lastFin]
      omega
    simpa [hden_nat] using h
  have hpred_each : ∀ k ∈ predecessorRaiseIndices hl η,
      weight a l (raiseAt η k) ≤ (1 / ((a + 1 : ℕ) : ℚ)) * weight a l η := by
    intro k hk
    simpa using (weight_raiseAt_le (a := a) η k)
  have hlast_notin : lastFin l hl ∉ predecessorRaiseIndices hl η := by
    simp [predecessorRaiseIndices, lastFin]
    intro hbad
    omega
  calc
    (∑ δ ∈ loweringFiber hl N η, weight a l δ) ≤
        ∑ k ∈ correctedCandidateRaiseIndices hl η, weight a l (raiseAt η k) := le_trans hsubsum himage
    _ = weight a l (raiseAt η (lastFin l hl)) + ∑ k ∈ predecessorRaiseIndices hl η, weight a l (raiseAt η k) := by
      unfold correctedCandidateRaiseIndices
      rw [Finset.sum_insert hlast_notin]
    _ ≤ (1 / ((a + l : ℕ) : ℚ)) * weight a l η + ∑ k ∈ predecessorRaiseIndices hl η, (1 / ((a + 1 : ℕ) : ℚ)) * weight a l η := by
      exact add_le_add hlast_bound (Finset.sum_le_sum hpred_each)
    _ ≤ (1 / ((a + l : ℕ) : ℚ)) * weight a l η + (1 / ((a + 1 : ℕ) : ℚ)) * weight a l η := by
      have hcard := card_predecessorRaiseIndices_le_one hl η
      have hcardQ : ((predecessorRaiseIndices hl η).card : ℚ) ≤ (1 : ℚ) := by exact_mod_cast hcard
      have hnon : 0 ≤ (1 / ((a + 1 : ℕ) : ℚ)) * weight a l η := mul_nonneg (by positivity) (weight_nonneg a l η)
      rw [Finset.sum_const]
      simp
      exact mul_le_of_le_one_left (by simpa using hnon) hcardQ
    _ = ((1 : ℚ) / (a + 1 : ℕ) + (1 : ℚ) / (a + l : ℕ)) * weight a l η := by ring

lemma D_one_step_bound_sharp_general_pos_l (a l N : ℕ) (hl : 0 < l) :
    D a l (N + 1) ≤ (((1 : ℚ) / (a + 1 : ℕ) + (1 : ℚ) / (a + l : ℕ))) * D a l N := by
  classical
  unfold D
  calc
    (∑ δ ∈ support l (N + 1), weight a l δ)
        = ∑ η ∈ support l N, ∑ δ ∈ (support l (N + 1)).filter (fun δ => lowerLeftmostMax hl δ = η), weight a l δ := by
          rw [Finset.sum_fiberwise_of_maps_to]
          intro δ hδ
          exact lowerLeftmostMax_mem_support hl hδ
    _ ≤ ∑ η ∈ support l N, (((1 : ℚ) / (a + 1 : ℕ) + (1 : ℚ) / (a + l : ℕ))) * weight a l η := by
          refine Finset.sum_le_sum ?_
          intro η hη
          exact loweringFiber_weight_sum_le_sharp_general (a := a) (N := N) hl η
    _ = (((1 : ℚ) / (a + 1 : ℕ) + (1 : ℚ) / (a + l : ℕ))) * (∑ η ∈ support l N, weight a l η) := by
          rw [Finset.mul_sum]

lemma fun_fin_one_eq_iff {N : ℕ} {δ : Fin 1 → ℕ} : δ = (fun _ => N) ↔ δ 0 = N := by
  constructor
  · intro h; rw [h]
  · intro h; funext i; fin_cases i; exact h

lemma support_one_eq_singleton (N : ℕ) : support 1 N = {fun _ : Fin 1 => N} := by
  classical
  ext δ
  rw [support]
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · intro h
    apply fun_fin_one_eq_iff.mpr
    have hs := h.2.2
    simp at hs
    exact hs
  · intro h
    rw [fun_fin_one_eq_iff] at h
    constructor
    · simp [h]
    · constructor
      · intro i j hij
        fin_cases i; fin_cases j; simp
      · simpa [h]

lemma weight_l_one (a N : ℕ) : weight a 1 (fun _ : Fin 1 => N) =
    (Nat.factorial a : ℚ) / (Nat.factorial (a + N) : ℚ) := by
  unfold weight
  simp

lemma D_l_one (a N : ℕ) :
    D a 1 N = (Nat.factorial a : ℚ) / (Nat.factorial (a + N) : ℚ) := by
  classical
  rw [D, support_one_eq_singleton]
  simp [weight_l_one]

/-- Explicit formula for `D b 2 N` as a one-dimensional finite sum.  A
nondecreasing pair `(δ 0, δ 1)` with total `N` is uniquely determined by
`x = δ 0`, and the nondecreasing condition is exactly `2*x ≤ N`. -/
lemma D_b_two_explicit_formula (b N : ℕ) :
    D b 2 N =
      ∑ x ∈ (Finset.range (N+1)).filter (fun x => 2*x <= N),
        ((Nat.factorial b : ℚ) / (Nat.factorial (b+x) : ℚ)) *
          ((Nat.factorial (b+1) : ℚ) / (Nat.factorial (b+1+N-x) : ℚ)) := by
  classical
  unfold D
  refine Finset.sum_bij' (fun δ _ => δ 0)
      (fun x _ => Fin.cons x (fun _ : Fin 1 => N - x)) ?_ ?_ ?_ ?_ ?_
  · intro δ hδ
    change δ 0 ∈ (Finset.range (N+1)).filter (fun x => 2*x <= N)

    rw [Finset.mem_filter]
    have hmem := hδ
    rw [support] at hmem
    have hnd : NondecreasingFin δ := (Finset.mem_filter.mp hmem).2.1
    have hsum : (∑ i : Fin 2, δ i) = N := (Finset.mem_filter.mp hmem).2.2
    have hs01 : δ 0 + δ 1 = N := by
      simpa [Fin.sum_univ_two] using hsum
    constructor
    · rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (by omega)
    · have h01 : δ 0 ≤ δ 1 := hnd 0 1 (by decide)
      omega
  · intro x hx
    rw [Finset.mem_filter] at hx
    have hxleN : x ≤ N := by omega
    rw [support]
    rw [Finset.mem_filter]
    constructor
    · rw [Fintype.mem_piFinset]
      intro i
      fin_cases i
      · simp [hxleN]
      · simp
    · constructor
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
      · rw [Fin.sum_univ_two]
        simp [hxleN]
  · intro δ hδ
    have hmem := hδ
    rw [support] at hmem
    have hsum : (∑ i : Fin 2, δ i) = N := (Finset.mem_filter.mp hmem).2.2
    have hs01 : δ 0 + δ 1 = N := by
      simpa [Fin.sum_univ_two] using hsum
    funext i
    fin_cases i
    · simp
    · have hsub : N - δ 0 = δ 1 := by omega
      simp [hsub]
  · intro x hx
    simp
  · intro δ hδ
    have hmem := hδ
    rw [support] at hmem
    have hsum : (∑ i : Fin 2, δ i) = N := (Finset.mem_filter.mp hmem).2.2
    have hs01 : δ 0 + δ 1 = N := by
      simpa [Fin.sum_univ_two] using hsum
    have hden : b + (1 + N) - δ 0 = b + (1 + δ 1) := by omega
    unfold weight
    rw [Fin.prod_univ_two]
    simp [hden, Nat.add_assoc]


lemma mul_factorial_lt_shift (a s : ℕ) (ha : 1 ≤ a) :
    a * Nat.factorial (s + a + 1) < Nat.factorial (s + 2 * a + 1) := by
  let n := s + a + 1
  have ha_lt : a < n + 1 := by
    dsimp [n]
    omega
  have hpos : 0 < Nat.factorial n := Nat.factorial_pos n
  have h1 : a * Nat.factorial n < (n + 1) * Nat.factorial n :=
    Nat.mul_lt_mul_of_pos_right ha_lt hpos
  have h1' : a * Nat.factorial n < Nat.factorial (n + 1) := by
    simpa [Nat.factorial_succ] using h1
  have hle : Nat.factorial (n + 1) ≤ Nat.factorial (n + a) := by
    exact Nat.factorial_le (by omega)
  have h := lt_of_lt_of_le h1' hle
  dsimp [n] at h
  convert h using 2; omega

lemma factorial_product_l_one_lt (a s : ℕ) (ha : 1 ≤ a) :
    Nat.factorial a * Nat.factorial (a + 1 + s) <
      Nat.factorial (a - 1) * Nat.factorial (a + (s + 1 + a)) := by
  have hfac : Nat.factorial a = a * Nat.factorial (a - 1) := by
    have hs := Nat.factorial_succ (a - 1)
    have hpred : a - 1 + 1 = a := by omega
    simpa [hpred] using hs
  have hcore : a * Nat.factorial (a + 1 + s) < Nat.factorial (a + (s + 1 + a)) := by
    have h := mul_factorial_lt_shift a s ha
    simpa [add_comm, add_left_comm, add_assoc, two_mul] using h
  have hm := Nat.mul_lt_mul_of_pos_left hcore (Nat.factorial_pos (a - 1))
  simpa [hfac, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hm

lemma G_l_one (a s : ℕ) (ha : 1 ≤ a) :
    ((Nat.factorial (a+1) : ℚ)/(Nat.factorial (a-1):ℚ)) * D a 1 (s+1+a) < D (a+1) 1 s := by
  rw [D_l_one, D_l_one]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a - 1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + (s + 1 + a))),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + 1 + s))]
  exact_mod_cast factorial_product_l_one_lt a s ha

/-- Add one to every coordinate. -/
def shiftUp {l : Nat} (η : Fin l → Nat) : Fin l → Nat := fun i => η i + 1

/-- Subtract one from every coordinate. -/
def shiftDown {l : Nat} (δ : Fin l → Nat) : Fin l → Nat := fun i => δ i - 1

lemma support_zero_of_pos {N : Nat} (hN : 0 < N) : support 0 N = ∅ := by
  classical
  ext δ
  rw [support]
  simp
  omega

lemma D_zero_of_pos {a N : Nat} (hN : 0 < N) : D a 0 N = 0 := by
  rw [D, support_zero_of_pos hN]
  simp

lemma nd_cons_zero {m : Nat} {η : Fin m → Nat} (hη : NondecreasingFin η) :
    NondecreasingFin (Fin.cons 0 η) := by
  intro i j hij
  cases i using Fin.cases with
  | zero => simp [Fin.cons_zero]
  | succ i =>
    cases j using Fin.cases with
    | zero => simp at hij
    | succ j => simpa [Fin.cons_succ] using hη i j (by simpa using hij)

lemma support_cons_zero_mem {m N : Nat} {η : Fin m → Nat} (hη : η ∈ support m N) :
    Fin.cons 0 η ∈ support (m+1) N := by
  rw [support] at hη ⊢
  simp only [Finset.mem_filter] at hη ⊢
  rw [Fintype.mem_piFinset] at hη
  constructor
  · rw [Fintype.mem_piFinset]
    intro i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simpa using hη.1 i
  · constructor
    · exact nd_cons_zero hη.2.1
    · rw [Fin.sum_univ_succ]
      simpa using hη.2.2

lemma support_tail_mem_of_cons_zero {m N : Nat} {δ : Fin (m+1) → Nat}
    (hδ : δ ∈ support (m+1) N) (h0 : δ 0 = 0) :
    Fin.tail δ ∈ support m N := by
  rw [support] at hδ ⊢
  simp only [Finset.mem_filter] at hδ ⊢
  rw [Fintype.mem_piFinset] at hδ
  constructor
  · rw [Fintype.mem_piFinset]
    intro i
    simpa [Fin.tail] using hδ.1 i.succ
  · constructor
    · intro i j hij
      exact hδ.2.1 i.succ j.succ (by simpa using hij)
    · have hs := hδ.2.2
      rw [Fin.sum_univ_succ] at hs
      simpa [Fin.tail, h0] using hs

lemma weight_cons_zero (m : Nat) (η : Fin m → Nat) :
    weight 1 (m+1) (Fin.cons 0 η) = weight 2 m η := by
  unfold weight
  rw [Fin.prod_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ, Nat.add_comm, Nat.add_left_comm]

lemma weight_eq_tail_of_zero {m : Nat} {δ : Fin (m+1) → Nat} (h0 : δ 0 = 0) :
    weight 1 (m+1) δ = weight 2 m (Fin.tail δ) := by
  have hc : Fin.cons 0 (Fin.tail δ) = δ := by
    rw [← Fin.cons_self_tail δ]
    simp [h0]
  rw [← hc]
  exact weight_cons_zero m (Fin.tail δ)

lemma nd_shiftUp {l : Nat} {η : Fin l → Nat} (hη : NondecreasingFin η) :
    NondecreasingFin (shiftUp η) := by
  intro i j hij
  simp [shiftUp, hη i j hij]

lemma sum_shiftUp {l : Nat} (η : Fin l → Nat) :
    (∑ i : Fin l, shiftUp η i) = (∑ i : Fin l, η i) + l := by
  unfold shiftUp
  rw [Finset.sum_add_distrib]
  simp

lemma nd_shiftDown {l : Nat} {δ : Fin l → Nat} (hδ : NondecreasingFin δ) :
    NondecreasingFin (shiftDown δ) := by
  intro i j hij
  exact Nat.sub_le_sub_right (hδ i j hij) 1

lemma sum_shiftDown_of_pos {l N : Nat} {δ : Fin l → Nat}
    (hpos : ∀ i, 0 < δ i) (hsum : (∑ i : Fin l, δ i) = N + l) :
    (∑ i : Fin l, shiftDown δ i) = N := by
  unfold shiftDown
  have hsum_add : (∑ i : Fin l, δ i) = (∑ i : Fin l, (δ i - 1)) + l := by
    calc
      (∑ i : Fin l, δ i) = ∑ i : Fin l, ((δ i - 1) + 1) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have := hpos i
        omega
      _ = (∑ i : Fin l, (δ i - 1)) + ∑ i : Fin l, (1 : Nat) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ i : Fin l, (δ i - 1)) + l := by simp
  omega

lemma support_shiftUp_mem {l N : Nat} {η : Fin l → Nat} (hη : η ∈ support l N) :
    shiftUp η ∈ support l (N + l) := by
  rw [support] at hη ⊢
  simp only [Finset.mem_filter] at hη ⊢
  rw [Fintype.mem_piFinset] at hη
  constructor
  · rw [Fintype.mem_piFinset]
    intro i
    have hi : η i < N + 1 := by simpa using hη.1 i
    have hlpos : 0 < l := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
    simp [shiftUp]
    omega
  · constructor
    · exact nd_shiftUp hη.2.1
    · rw [sum_shiftUp, hη.2.2]

lemma support_shiftDown_mem {m N : Nat} {δ : Fin (m+1) → Nat}
    (hδ : δ ∈ support (m+1) (N + (m+1))) (h0 : 0 < δ 0) :
    shiftDown δ ∈ support (m+1) N := by
  rw [support] at hδ ⊢
  simp only [Finset.mem_filter] at hδ ⊢
  rw [Fintype.mem_piFinset] at hδ
  have hpos : ∀ i : Fin (m+1), 0 < δ i := by
    intro i
    exact lt_of_lt_of_le h0 (hδ.2.1 0 i (by simp))
  have hs : (∑ j : Fin (m+1), shiftDown δ j) = N := sum_shiftDown_of_pos hpos hδ.2.2
  constructor
  · rw [Fintype.mem_piFinset]
    intro i
    have hle : shiftDown δ i ≤ ∑ j : Fin (m+1), shiftDown δ j :=
      Finset.single_le_sum (by intro x hx; exact Nat.zero_le _) (Finset.mem_univ i)
    have hleN : shiftDown δ i ≤ N := by omega
    simpa using Nat.lt_succ_of_le hleN
  · constructor
    · exact nd_shiftDown hδ.2.1
    · exact hs

lemma shiftDown_shiftUp {l : Nat} (η : Fin l → Nat) : shiftDown (shiftUp η) = η := by
  funext i
  simp [shiftDown, shiftUp]

lemma shiftUp_shiftDown_of_pos {l : Nat} {δ : Fin l → Nat} (hpos : ∀ i, 0 < δ i) :
    shiftUp (shiftDown δ) = δ := by
  funext i
  simp [shiftUp, shiftDown]
  have := hpos i
  omega

lemma weight_shiftUp_factorial (a l : Nat) (η : Fin l → Nat) :
    ((Nat.factorial (a + l) : ℚ) / (Nat.factorial a : ℚ)) * weight a l (shiftUp η) =
      weight (a+1) l η := by
  induction l generalizing a with
  | zero =>
    unfold weight
    simp
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
  | succ m ih =>
    rw [← Fin.cons_self_tail η]
    unfold weight
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, shiftUp]
    have hih := ih (a+1) (Fin.tail η)
    unfold weight at hih
    have hih' :
        ((Nat.factorial (a + 1 + m) : ℚ) / (Nat.factorial (a + 1) : ℚ)) *
          (∏ x : Fin m, (Nat.factorial (a + (x.succ : ℕ)) : ℚ) /
            (Nat.factorial (a + (x.succ : ℕ) + (Fin.tail η x + 1)) : ℚ)) =
          (∏ x : Fin m, (Nat.factorial (a + 1 + (x.succ : ℕ)) : ℚ) /
            (Nat.factorial (a + 1 + (x.succ : ℕ) + Fin.tail η x) : ℚ)) := by
      simpa [shiftUp, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hih
    rw [← hih']
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + 1)),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + η 0 + 1))]
    norm_num
    ring_nf

lemma weight_shiftUp_factorial_one (l : Nat) (η : Fin l → Nat) :
    (Nat.factorial (l+1) : ℚ) * weight 1 l (shiftUp η) = weight 2 l η := by
  have h := weight_shiftUp_factorial 1 l η
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

lemma D_one_zero_part (m N : Nat) :
    (∑ δ ∈ (support (m+1) N).filter (fun δ => δ 0 = 0), weight 1 (m+1) δ) =
      D 2 m N := by
  classical
  rw [D]
  refine Finset.sum_bij' (fun δ hδ => Fin.tail δ) (fun η hη => Fin.cons 0 η) ?_ ?_ ?_ ?_ ?_
  · intro δ hδ
    exact support_tail_mem_of_cons_zero (Finset.mem_filter.mp hδ).1 (Finset.mem_filter.mp hδ).2
  · intro η hη
    exact Finset.mem_filter.mpr ⟨support_cons_zero_mem hη, by simp [Fin.cons_zero]⟩
  · intro δ hδ
    change Fin.cons 0 (Fin.tail δ) = δ
    have h0 : δ 0 = 0 := (Finset.mem_filter.mp hδ).2
    calc
      Fin.cons 0 (Fin.tail δ) = Fin.cons (δ 0) (Fin.tail δ) := by simp [h0]
      _ = δ := Fin.cons_self_tail δ
  · intro η hη
    change Fin.tail (Fin.cons 0 η : Fin (m+1) → Nat) = η
    simp
  · intro δ hδ
    exact weight_eq_tail_of_zero (Finset.mem_filter.mp hδ).2

lemma D_one_positive_part (m s : Nat) :
    (Nat.factorial (m+2) : ℚ) *
      (∑ δ ∈ (support (m+1) (s + m + 2)).filter (fun δ => ¬ δ 0 = 0), weight 1 (m+1) δ) =
        D 2 (m+1) (s+1) := by
  classical
  rw [Finset.mul_sum, D]
  have hbij :
      (∑ δ ∈ (support (m+1) (s + m + 2)).filter (fun δ => ¬ δ 0 = 0),
          (Nat.factorial (m+2) : ℚ) * weight 1 (m+1) δ) =
        ∑ η ∈ support (m+1) (s+1), weight 2 (m+1) η := by
    refine Finset.sum_bij' (fun δ hδ => shiftDown δ) (fun η hη => shiftUp η) ?_ ?_ ?_ ?_ ?_
    · intro δ hδ
      have hmem : δ ∈ support (m+1) ((s+1) + (m+1)) := by
        convert (Finset.mem_filter.mp hδ).1 using 2
        omega
      have hn0 : ¬ δ 0 = 0 := (Finset.mem_filter.mp hδ).2
      have h0 : 0 < δ 0 := Nat.pos_of_ne_zero hn0
      exact support_shiftDown_mem hmem h0
    · intro η hη
      have hmem : shiftUp η ∈ support (m+1) ((s+1) + (m+1)) := support_shiftUp_mem hη
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · convert hmem using 2
        omega
      · simp [shiftUp]
    · intro δ hδ
      change shiftUp (shiftDown δ) = δ
      apply shiftUp_shiftDown_of_pos
      intro i
      have hnd : NondecreasingFin δ := by
        exact (by
          rw [support] at hδ
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp hδ).1).2.1)
      have hn0 : ¬ δ 0 = 0 := (Finset.mem_filter.mp hδ).2
      have h0 : 0 < δ 0 := Nat.pos_of_ne_zero hn0
      exact lt_of_lt_of_le h0 (hnd 0 i (by simp))
    · intro η hη
      exact shiftDown_shiftUp η
    · intro δ hδ
      have hpos : ∀ i : Fin (m+1), 0 < δ i := by
        intro i
        have hnd : NondecreasingFin δ := by
          exact (by
            rw [support] at hδ
            exact (Finset.mem_filter.mp (Finset.mem_filter.mp hδ).1).2.1)
        have hn0 : ¬ δ 0 = 0 := (Finset.mem_filter.mp hδ).2
        have h0 : 0 < δ 0 := Nat.pos_of_ne_zero hn0
        exact lt_of_lt_of_le h0 (hnd 0 i (by simp))
      change (Nat.factorial (m+2) : ℚ) * weight 1 (m+1) δ = weight 2 (m+1) (shiftDown δ)
      have hδeq : shiftUp (shiftDown δ) = δ := shiftUp_shiftDown_of_pos hpos
      calc
        (Nat.factorial (m+2) : ℚ) * weight 1 (m+1) δ =
            (Nat.factorial (m+2) : ℚ) * weight 1 (m+1) (shiftUp (shiftDown δ)) := by rw [hδeq]
        _ = weight 2 (m+1) (shiftDown δ) := weight_shiftUp_factorial_one (m+1) (shiftDown δ)
  exact hbij

lemma D_one_split_succ (m s : Nat) :
    (Nat.factorial (m+2) : ℚ) * D 1 (m+1) (s + m + 2) =
      D 2 (m+1) (s+1) + (Nat.factorial (m+2) : ℚ) * D 2 m (s + m + 2) := by
  classical
  rw [D]
  have hpart := Finset.sum_filter_add_sum_filter_not (support (m+1) (s + m + 2)) (fun δ => δ 0 = 0) (fun δ => weight 1 (m+1) δ)
  calc
    (Nat.factorial (m+2) : ℚ) * (∑ δ ∈ support (m+1) (s + m + 2), weight 1 (m+1) δ)
        = (Nat.factorial (m+2) : ℚ) *
            ((∑ δ ∈ (support (m+1) (s + m + 2)).filter (fun δ => δ 0 = 0), weight 1 (m+1) δ) +
             (∑ δ ∈ (support (m+1) (s + m + 2)).filter (fun δ => ¬ δ 0 = 0), weight 1 (m+1) δ)) := by
          rw [hpart]
    _ = (Nat.factorial (m+2) : ℚ) *
            (∑ δ ∈ (support (m+1) (s + m + 2)).filter (fun δ => ¬ δ 0 = 0), weight 1 (m+1) δ) +
          (Nat.factorial (m+2) : ℚ) *
            (∑ δ ∈ (support (m+1) (s + m + 2)).filter (fun δ => δ 0 = 0), weight 1 (m+1) δ) := by ring
    _ = D 2 (m+1) (s+1) + (Nat.factorial (m+2) : ℚ) * D 2 m (s + m + 2) := by
          rw [D_one_positive_part m s, D_one_zero_part m (s + m + 2)]

lemma D_one_split (l s : Nat) :
    (Nat.factorial (l+1) : ℚ) * D 1 l (s+l+1) =
      D 2 l (s+1) + (Nat.factorial (l+1) : ℚ) * D 2 (l-1) (s+l+1) := by
  cases l with
  | zero =>
    simp [D_zero_of_pos (a := 1) (N := s+1) (by omega),
      D_zero_of_pos (a := 2) (N := s+1) (by omega)]
  | succ m =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using D_one_split_succ m s

end DOneStepNoAxiom


namespace DOneStepNoAxiom

lemma D_nonneg (a l N : ℕ) : 0 ≤ D a l N := by
  classical
  unfold D
  exact Finset.sum_nonneg (by intro δ hδ; exact weight_nonneg a l δ)

lemma weight_pos (a l : ℕ) (δ : Fin l → ℕ) : 0 < weight a l δ := by
  classical
  unfold weight
  exact Finset.prod_pos (by intro i hi; positivity)

lemma D_pos (a l N : ℕ) (hl : 0 < l) : 0 < D a l N := by
  classical
  let δ : Fin l → ℕ := fun i => if i = lastFin l hl then N else 0
  have hδmem : δ ∈ support l N := by
    rw [support]
    simp only [Finset.mem_filter]
    constructor
    · rw [Fintype.mem_piFinset]
      intro i
      by_cases hi : i = lastFin l hl
      · simp [δ, hi]
      · simp [δ, hi]
    · constructor
      · intro i j hij
        by_cases hi : i = lastFin l hl
        · have hj : j = lastFin l hl := by
            apply Fin.ext
            have hlast : (lastFin l hl : ℕ) = l - 1 := rfl
            have hjle : (j : ℕ) ≤ l - 1 := by omega
            have hige : (i : ℕ) = l - 1 := by simpa [lastFin] using congrArg Fin.val hi
            omega
          simp [δ, hi, hj]
        · simp [δ, hi]
      · have hsum : (∑ i : Fin l, δ i) = ∑ i : Fin l, if i = lastFin l hl then N else 0 := rfl
        rw [hsum]
        rw [Finset.sum_eq_single (lastFin l hl)]
        · simp
        · intro b hb hbne
          simp [hbne]
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ _))
  have hle : weight a l δ ≤ D a l N := by
    unfold D
    exact Finset.single_le_sum (by intro x hx; exact weight_nonneg a l x) hδmem
  exact lt_of_lt_of_le (weight_pos a l δ) hle

lemma D_one_split_sharp_conditional
    (l s : ℕ) (K : ℚ) (hD : 0 < D 2 l s)
    (zero_bound : (Nat.factorial (l+1) : ℚ) * D 2 (l-1) (s+l+1) ≤ K * D 2 l s)
    (hK : K < (2 : ℚ) / 3 - (1 : ℚ) / (l+2 : ℕ)) :
    (Nat.factorial (l+1) : ℚ) * D 1 l (s+l+1) < D 2 l s := by
  classical
  let c : ℚ := (1 : ℚ) / 3 + (1 : ℚ) / (l+2 : ℕ)
  have hstep : D 2 l (s+1) ≤ c * D 2 l s := by
    simpa [c] using D_one_step_bound_sharp_a2 l s
  have hcoef : c + K < 1 := by
    dsimp [c]
    linarith
  calc
    (Nat.factorial (l+1) : ℚ) * D 1 l (s+l+1)
        = D 2 l (s+1) + (Nat.factorial (l+1) : ℚ) * D 2 (l-1) (s+l+1) :=
          D_one_split l s
    _ ≤ c * D 2 l s + K * D 2 l s := add_le_add hstep zero_bound
    _ = (c + K) * D 2 l s := by ring
    _ < 1 * D 2 l s := mul_lt_mul_of_pos_right hcoef hD
    _ = D 2 l s := by ring

lemma D_one_split_sharp_conditional_of_K
    (l s : ℕ) (K : ℚ) (hl : 0 < l)
    (zero_bound : (Nat.factorial (l+1) : ℚ) * D 2 (l-1) (s+l+1) ≤ K * D 2 l s)
    (hK : K < (2 : ℚ) / 3 - (1 : ℚ) / (l+2 : ℕ)) :
    (Nat.factorial (l+1) : ℚ) * D 1 l (s+l+1) < D 2 l s := by
  exact D_one_split_sharp_conditional l s K (D_pos 2 l s hl) zero_bound hK


lemma weight_cons_zero_general (a m : Nat) (η : Fin m → Nat) :
    weight a (m+1) (Fin.cons 0 η) = weight (a+1) m η := by
  unfold weight
  rw [Fin.prod_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ, Nat.add_comm, Nat.add_left_comm]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)]

lemma weight_eq_tail_of_zero_general {a m : Nat} {δ : Fin (m+1) → Nat} (h0 : δ 0 = 0) :
    weight a (m+1) δ = weight (a+1) m (Fin.tail δ) := by
  have hc : Fin.cons 0 (Fin.tail δ) = δ := by
    rw [← Fin.cons_self_tail δ]
    simp [h0]
  rw [← hc]
  exact weight_cons_zero_general a m (Fin.tail δ)

lemma D_two_ge_zero_term (a N : Nat) : D a 2 N ≥ D (a+1) 1 N := by
  classical
  rw [D_l_one]
  let δ : Fin 2 → Nat := Fin.cons 0 (fun _ : Fin 1 => N)
  have hδmem : δ ∈ support 2 N := by
    have h : (fun _ : Fin 1 => N) ∈ support 1 N := by
      rw [support_one_eq_singleton]
      simp
    simpa [δ] using (support_cons_zero_mem (m := 1) (N := N) h)
  have hw : weight a 2 δ = (Nat.factorial (a+1) : ℚ) / (Nat.factorial (a+1+N) : ℚ) := by
    rw [weight_cons_zero_general]
    exact weight_l_one (a+1) N
  have hle : weight a 2 δ ≤ D a 2 N := by
    unfold D
    exact Finset.single_le_sum (by intro x hx; exact weight_nonneg a 2 x) hδmem
  simpa [hw, Nat.add_assoc] using hle

lemma D_zero_part_general_two (a N : Nat) :
    (∑ δ ∈ (support 2 N).filter (fun δ => δ 0 = 0), weight a 2 δ) =
      D (a+1) 1 N := by
  classical
  rw [D]
  refine Finset.sum_bij' (fun δ hδ => Fin.tail δ) (fun η hη => Fin.cons 0 η) ?_ ?_ ?_ ?_ ?_
  · intro δ hδ
    exact support_tail_mem_of_cons_zero (m := 1) (N := N) (Finset.mem_filter.mp hδ).1 (Finset.mem_filter.mp hδ).2
  · intro η hη
    exact Finset.mem_filter.mpr ⟨support_cons_zero_mem (m := 1) (N := N) hη, by simp [Fin.cons_zero]⟩
  · intro δ hδ
    change Fin.cons 0 (Fin.tail δ) = δ
    have h0 : δ 0 = 0 := (Finset.mem_filter.mp hδ).2
    calc
      Fin.cons 0 (Fin.tail δ) = Fin.cons (δ 0) (Fin.tail δ) := by simp [h0]
      _ = δ := Fin.cons_self_tail δ
  · intro η hη
    change Fin.tail (Fin.cons 0 η : Fin 2 → Nat) = η
    simp
  · intro δ hδ
    exact weight_eq_tail_of_zero_general (a := a) (m := 1) (Finset.mem_filter.mp hδ).2

lemma D_positive_part_general_two (a T : Nat) :
    ((Nat.factorial (a+2) : ℚ) / (Nat.factorial a : ℚ)) *
      (∑ δ ∈ (support 2 (T+2)).filter (fun δ => ¬ δ 0 = 0), weight a 2 δ) =
        D (a+1) 2 T := by
  classical
  rw [Finset.mul_sum, D]
  refine Finset.sum_bij' (fun δ hδ => shiftDown δ) (fun η hη => shiftUp η) ?_ ?_ ?_ ?_ ?_
  · intro δ hδ
    have hmem : δ ∈ support 2 (T + 2) := (Finset.mem_filter.mp hδ).1
    have hn0 : ¬ δ 0 = 0 := (Finset.mem_filter.mp hδ).2
    have h0 : 0 < δ 0 := Nat.pos_of_ne_zero hn0
    have hmem' : δ ∈ support (1+1) (T + (1+1)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmem
    simpa using (support_shiftDown_mem (m := 1) (N := T) hmem' h0)
  · intro η hη
    have hmem : shiftUp η ∈ support 2 (T + 2) := by
      have h := support_shiftUp_mem (l := 2) (N := T) hη
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    exact Finset.mem_filter.mpr ⟨hmem, by simp [shiftUp]⟩
  · intro δ hδ
    change shiftUp (shiftDown δ) = δ
    apply shiftUp_shiftDown_of_pos
    intro i
    have hnd : NondecreasingFin δ := by
      have hmem : δ ∈ support 2 (T+2) := (Finset.mem_filter.mp hδ).1
      rw [support] at hmem
      exact (Finset.mem_filter.mp hmem).2.1
    have hn0 : ¬ δ 0 = 0 := (Finset.mem_filter.mp hδ).2
    have h0 : 0 < δ 0 := Nat.pos_of_ne_zero hn0
    exact lt_of_lt_of_le h0 (hnd 0 i (by simp))
  · intro η hη
    exact shiftDown_shiftUp η
  · intro δ hδ
    have hpos : ∀ i : Fin 2, 0 < δ i := by
      intro i
      have hnd : NondecreasingFin δ := by
        have hmem : δ ∈ support 2 (T+2) := (Finset.mem_filter.mp hδ).1
        rw [support] at hmem
        exact (Finset.mem_filter.mp hmem).2.1
      have hn0 : ¬ δ 0 = 0 := (Finset.mem_filter.mp hδ).2
      have h0 : 0 < δ 0 := Nat.pos_of_ne_zero hn0
      exact lt_of_lt_of_le h0 (hnd 0 i (by simp))
    change ((Nat.factorial (a+2) : ℚ) / (Nat.factorial a : ℚ)) * weight a 2 δ = weight (a+1) 2 (shiftDown δ)
    have hδeq : shiftUp (shiftDown δ) = δ := shiftUp_shiftDown_of_pos hpos
    calc
      ((Nat.factorial (a+2) : ℚ) / (Nat.factorial a : ℚ)) * weight a 2 δ =
          ((Nat.factorial (a+2) : ℚ) / (Nat.factorial a : ℚ)) * weight a 2 (shiftUp (shiftDown δ)) := by rw [hδeq]
      _ = weight (a+1) 2 (shiftDown δ) := weight_shiftUp_factorial a 2 (shiftDown δ)

lemma D_split_general_two (a T : Nat) :
    ((Nat.factorial (a+2) : ℚ) / (Nat.factorial a : ℚ)) * D a 2 (T+2) =
      D (a+1) 2 T + ((Nat.factorial (a+2) : ℚ) / (Nat.factorial a : ℚ)) * D (a+1) 1 (T+2) := by
  classical
  rw [D]
  have hpart := Finset.sum_filter_add_sum_filter_not (support 2 (T+2)) (fun δ => δ 0 = 0) (fun δ => weight a 2 δ)
  calc
    ((Nat.factorial (a+2) : ℚ) / (Nat.factorial a : ℚ)) * (∑ δ ∈ support 2 (T+2), weight a 2 δ)
        = ((Nat.factorial (a+2) : ℚ) / (Nat.factorial a : ℚ)) *
          ((∑ δ ∈ (support 2 (T+2)).filter (fun δ => δ 0 = 0), weight a 2 δ) +
           (∑ δ ∈ (support 2 (T+2)).filter (fun δ => ¬ δ 0 = 0), weight a 2 δ)) := by
          rw [hpart]
    _ = ((Nat.factorial (a+2) : ℚ) / (Nat.factorial a : ℚ)) *
          (∑ δ ∈ (support 2 (T+2)).filter (fun δ => ¬ δ 0 = 0), weight a 2 δ) +
        ((Nat.factorial (a+2) : ℚ) / (Nat.factorial a : ℚ)) *
          (∑ δ ∈ (support 2 (T+2)).filter (fun δ => δ 0 = 0), weight a 2 δ) := by ring
    _ = D (a+1) 2 T + ((Nat.factorial (a+2) : ℚ) / (Nat.factorial a : ℚ)) * D (a+1) 1 (T+2) := by
          rw [D_positive_part_general_two a T, D_zero_part_general_two a (T+2)]

lemma contraction_coeff_le_five_six (a : Nat) (ha : 1 ≤ a) :
    (a : ℚ) * (((1 : ℚ) / (a + 1 : Nat) + (1 : ℚ) / (a + 2 : Nat)) ^ a) ≤ (5 : ℚ) / 6 := by
  by_cases ha1 : a = 1
  · subst a
    norm_num
  · have ha2 : 2 ≤ a := by omega
    have hc : ((1 : ℚ) / (a + 1 : Nat) + (1 : ℚ) / (a + 2 : Nat)) ≤ (7 : ℚ) / 12 := by
      have h1 : (0 : ℚ) < (a + 1 : Nat) := by positivity
      have h2 : (0 : ℚ) < (a + 2 : Nat) := by positivity
      field_simp
      norm_num at *
      have ha2q : (2 : ℚ) ≤ a := by exact_mod_cast ha2
      nlinarith [sq_nonneg ((a : ℚ) - 2)]
    have hcnon : 0 ≤ ((1 : ℚ) / (a + 1 : Nat) + (1 : ℚ) / (a + 2 : Nat)) := by positivity
    have hp : (((1 : ℚ) / (a + 1 : Nat) + (1 : ℚ) / (a + 2 : Nat)) ^ a) ≤ ((7 : ℚ) / 12) ^ a := by
      exact pow_le_pow_left₀ hcnon hc a
    have hseq : (a : ℚ) * ((7 : ℚ) / 12) ^ a ≤ (2 : ℚ) * ((7 : ℚ) / 12) ^ (2 : Nat) := by
      -- elementary monotonicity of n*(7/12)^n for n ≥ 2, proved by induction from `a`
      have hbase : ∀ n : Nat, 2 ≤ n → (n : ℚ) * ((7 : ℚ) / 12) ^ n ≤ (2 : ℚ) * ((7 : ℚ) / 12) ^ (2 : Nat) := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base => norm_num
        | succ n hn ih =>
            have hnon : 0 ≤ ((7 : ℚ) / 12) ^ n := by positivity
            calc
              ((n+1 : Nat) : ℚ) * ((7 : ℚ) / 12) ^ (n+1)
                  = (((n+1 : Nat) : ℚ) * ((7 : ℚ) / 12)) * ((7 : ℚ) / 12) ^ n := by ring
              _ ≤ (n : ℚ) * ((7 : ℚ) / 12) ^ n := by
                refine mul_le_mul_of_nonneg_right ?_ hnon
                have hnpos : (0 : ℚ) < n := by exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 0 < 2) hn)
                field_simp
                norm_num at *
                have hnq : (2 : ℚ) ≤ n := by exact_mod_cast hn
                nlinarith
              _ ≤ (2 : ℚ) * ((7 : ℚ) / 12) ^ (2 : Nat) := ih
      exact hbase a ha2
    calc
      (a : ℚ) * (((1 : ℚ) / (a + 1 : Nat) + (1 : ℚ) / (a + 2 : Nat)) ^ a)
          ≤ (a : ℚ) * ((7 : ℚ) / 12) ^ a := by exact mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ (2 : ℚ) * ((7 : ℚ) / 12) ^ (2 : Nat) := hseq
      _ ≤ (5 : ℚ) / 6 := by norm_num

lemma zero_extra_le_tenth (a s : Nat) (ha : 1 ≤ a) :
    (a : ℚ) * (((Nat.factorial (a+2) : ℚ) / (Nat.factorial a : ℚ)) * D (a+1) 1 (s+a+2)) ≤
      ((1 : ℚ) / 10) * D (a+1) 2 s := by
  rw [D_l_one]
  have hzero := D_two_ge_zero_term (a+1) s
  rw [D_l_one] at hzero
  have hratio : (a : ℚ) * (((Nat.factorial (a+2) : ℚ) / (Nat.factorial a : ℚ)) *
      ((Nat.factorial (a+1) : ℚ) / (Nat.factorial (a+1 + (s+a+2)) : ℚ))) ≤
      ((1 : ℚ) / 10) * ((Nat.factorial (a+2) : ℚ) / (Nat.factorial (a+2+s) : ℚ)) := by
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a+1+(s+a+2))),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a+2+s))]
    norm_num
    -- after clearing denominators this is a very weak factorial-growth estimate
    have hfac : a * Nat.factorial (a+1) * 10 * Nat.factorial (a+2+s) ≤
        Nat.factorial a * Nat.factorial (a+1+(s+a+2)) := by
      rw [Nat.factorial_succ]
      by_cases ha1 : a = 1
      · subst a
        norm_num
        rw [show 2 + (s + 1 + 2) = s + 5 by omega]
        rw [show s + 5 = (s + 4) + 1 by omega, Nat.factorial_succ]
        rw [show s + 4 = (s + 3) + 1 by omega, Nat.factorial_succ]
        have hsprod : 20 ≤ (s+5) * (s+4) := by
          nlinarith [sq_nonneg ((s : ℤ))]
        have hle := Nat.mul_le_mul_right (Nat.factorial (s+3)) hsprod
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hle
      · have ha2 : 2 ≤ a := by omega
        have hmain : 10 * a * (a+1) ≤ (a+3) * (a+4) * (a+5) := by
          nlinarith [sq_nonneg ((a : ℤ) - 2)]
        have hfacmono : (a+3) * (a+4) * (a+5) * Nat.factorial (a+2+s) ≤
            Nat.factorial (a+1+(s+a+2)) := by
          have hle1 : a+3 ≤ a+3+s := by omega
          have hle2 : a+4 ≤ a+4+s := by omega
          have hle3 : a+5 ≤ a+5+s := by omega
          have hprod : (a+3) * (a+4) * (a+5) * Nat.factorial (a+2+s) ≤
              (a+3+s) * (a+4+s) * (a+5+s) * Nat.factorial (a+2+s) := by
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul hle1 hle2) hle3)
          have hfact : (a+3+s) * (a+4+s) * (a+5+s) * Nat.factorial (a+2+s) = Nat.factorial (a+5+s) := by
            rw [show a+5+s = (a+4+s)+1 by omega, Nat.factorial_succ]
            rw [show a+4+s = (a+3+s)+1 by omega, Nat.factorial_succ]
            rw [show a+3+s = (a+2+s)+1 by omega, Nat.factorial_succ]
            ring
          have hmono : Nat.factorial (a+5+s) ≤ Nat.factorial (a+1+(s+a+2)) := Nat.factorial_le (by omega)
          exact le_trans (by simpa [hfact] using hprod) hmono
        have hstep : 10 * a * (a+1) * Nat.factorial (a+2+s) ≤
            (a+3) * (a+4) * (a+5) * Nat.factorial (a+2+s) := Nat.mul_le_mul_right _ hmain
        nlinarith [hstep, hfacmono]
    exact_mod_cast hfac
  exact le_trans hratio (mul_le_mul_of_nonneg_left hzero (by norm_num))

lemma shifted_contraction_coeff_le_seven_twelfths (a : Nat) (ha : 1 ≤ a) :
    (a : ℚ) * (((1 : ℚ) / (a + 2 : Nat) + (1 : ℚ) / (a + 3 : Nat)) ^ a) ≤ (7 : ℚ) / 12 := by
  by_cases ha1 : a = 1
  · subst a
    norm_num
  · have ha2 : 2 ≤ a := by omega
    have hc : ((1 : ℚ) / (a + 2 : Nat) + (1 : ℚ) / (a + 3 : Nat)) ≤ (9 : ℚ) / 20 := by
      field_simp
      norm_num at *
      have ha2q : (2 : ℚ) ≤ a := by exact_mod_cast ha2
      nlinarith [sq_nonneg ((a : ℚ) - 2)]
    have hcnon : 0 ≤ ((1 : ℚ) / (a + 2 : Nat) + (1 : ℚ) / (a + 3 : Nat)) := by positivity
    have hp : (((1 : ℚ) / (a + 2 : Nat) + (1 : ℚ) / (a + 3 : Nat)) ^ a) ≤ ((9 : ℚ) / 20) ^ a :=
      pow_le_pow_left₀ hcnon hc a
    have hbase : ∀ n : Nat, 2 ≤ n → (n : ℚ) * ((9 : ℚ) / 20) ^ n ≤ (2 : ℚ) * ((9 : ℚ) / 20) ^ (2 : Nat) := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => norm_num
      | succ n hn ih =>
          have hnon : 0 ≤ ((9 : ℚ) / 20) ^ n := by positivity
          calc
            ((n+1 : Nat) : ℚ) * ((9 : ℚ) / 20) ^ (n+1)
                = (((n+1 : Nat) : ℚ) * ((9 : ℚ) / 20)) * ((9 : ℚ) / 20) ^ n := by ring
            _ ≤ (n : ℚ) * ((9 : ℚ) / 20) ^ n := by
              refine mul_le_mul_of_nonneg_right ?_ hnon
              field_simp
              norm_num at *
              have hnq : (2 : ℚ) ≤ n := by exact_mod_cast hn
              nlinarith
            _ ≤ (2 : ℚ) * ((9 : ℚ) / 20) ^ (2 : Nat) := ih
    calc
      (a : ℚ) * (((1 : ℚ) / (a + 2 : Nat) + (1 : ℚ) / (a + 3 : Nat)) ^ a)
          ≤ (a : ℚ) * ((9 : ℚ) / 20) ^ a := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ (2 : ℚ) * ((9 : ℚ) / 20) ^ (2 : Nat) := hbase a ha2
      _ ≤ (7 : ℚ) / 12 := by norm_num


lemma G_l_two (a s : Nat) (ha : 1 <= a) :
    ((Nat.factorial (a+2) : ℚ)/(Nat.factorial (a-1) : ℚ))*D a 2 (s+a+2) < D (a+1) 2 s := by
  let c : ℚ := (1 : ℚ) / (a + 2 : Nat) + (1 : ℚ) / (a + 3 : Nat)
  have hstep : D (a+1) 2 (s + a) ≤ c ^ a * D (a+1) 2 s := by
    have h := iterated_contraction (D (a+1) 2) c (by positivity)
      (fun n => by simpa [c, Nat.add_assoc] using D_one_step_bound_sharp_general_pos_l (a+1) 2 n (by decide)) a s
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hsplit := D_split_general_two a (s+a)
  have hfac : ((Nat.factorial (a+2) : ℚ) / (Nat.factorial (a-1) : ℚ)) =
      (a : ℚ) * ((Nat.factorial (a+2) : ℚ) / (Nat.factorial a : ℚ)) := by
    have hsucc : Nat.factorial a = a * Nat.factorial (a-1) := by
      have h := Nat.factorial_succ (a-1)
      have : a - 1 + 1 = a := by omega
      simpa [this] using h
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a-1))]
    rw [hsucc]
    norm_num
    ring
  have hzero := zero_extra_le_tenth a s ha
  have hcoef := shifted_contraction_coeff_le_seven_twelfths a ha
  have htarget_pos : 0 < D (a+1) 2 s := D_pos (a+1) 2 s (by decide)
  calc
    ((Nat.factorial (a+2) : ℚ)/(Nat.factorial (a-1) : ℚ))*D a 2 (s+a+2)
        = (a : ℚ) * (((Nat.factorial (a+2) : ℚ) / (Nat.factorial a : ℚ)) * D a 2 ((s+a)+2)) := by
          rw [hfac]
          rw [show s+a+2 = (s+a)+2 by omega]
          ring
    _ = (a : ℚ) * (D (a+1) 2 (s+a) + ((Nat.factorial (a+2) : ℚ) / (Nat.factorial a : ℚ)) * D (a+1) 1 (s+a+2)) := by
          rw [hsplit]
    _ = (a : ℚ) * D (a+1) 2 (s+a) + (a : ℚ) * (((Nat.factorial (a+2) : ℚ) / (Nat.factorial a : ℚ)) * D (a+1) 1 (s+a+2)) := by ring
    _ ≤ (a : ℚ) * (c ^ a * D (a+1) 2 s) + ((1 : ℚ) / 10) * D (a+1) 2 s := by
          exact add_le_add (mul_le_mul_of_nonneg_left hstep (by positivity)) hzero
    _ = ((a : ℚ) * c ^ a) * D (a+1) 2 s + ((1 : ℚ) / 10) * D (a+1) 2 s := by ring
    _ ≤ ((7 : ℚ) / 12) * D (a+1) 2 s + ((1 : ℚ) / 10) * D (a+1) 2 s := by
          have hm := mul_le_mul_of_nonneg_right hcoef (le_of_lt htarget_pos)
          simpa [c, add_assoc, add_comm, add_left_comm] using
            add_le_add_right hm (((1 : ℚ) / 10) * D (a+1) 2 s)
    _ = ((41 : ℚ) / 60) * D (a+1) 2 s := by ring
    _ < 1 * D (a+1) 2 s := by
          exact mul_lt_mul_of_pos_right (by norm_num) htarget_pos
    _ = D (a+1) 2 s := by ring


lemma D_zero_part_general_succ (a m N : Nat) :
    (∑ δ ∈ (support (m+1) N).filter (fun δ => δ 0 = 0), weight a (m+1) δ) =
      D (a+1) m N := by
  classical
  rw [D]
  refine Finset.sum_bij' (fun δ hδ => Fin.tail δ) (fun η hη => Fin.cons 0 η) ?_ ?_ ?_ ?_ ?_
  · intro δ hδ
    exact support_tail_mem_of_cons_zero (m := m) (N := N) (Finset.mem_filter.mp hδ).1 (Finset.mem_filter.mp hδ).2
  · intro η hη
    exact Finset.mem_filter.mpr ⟨support_cons_zero_mem (m := m) (N := N) hη, by simp [Fin.cons_zero]⟩
  · intro δ hδ
    change Fin.cons 0 (Fin.tail δ) = δ
    have h0 : δ 0 = 0 := (Finset.mem_filter.mp hδ).2
    calc
      Fin.cons 0 (Fin.tail δ) = Fin.cons (δ 0) (Fin.tail δ) := by simp [h0]
      _ = δ := Fin.cons_self_tail δ
  · intro η hη
    change Fin.tail (Fin.cons 0 η : Fin (m+1) → Nat) = η
    simp
  · intro δ hδ
    exact weight_eq_tail_of_zero_general (a := a) (m := m) (Finset.mem_filter.mp hδ).2

lemma D_positive_part_general_succ (a m T : Nat) :
    ((Nat.factorial (a + (m+1)) : ℚ) / (Nat.factorial a : ℚ)) *
      (∑ δ ∈ (support (m+1) (T + (m+1))).filter (fun δ => ¬ δ 0 = 0), weight a (m+1) δ) =
        D (a+1) (m+1) T := by
  classical
  rw [Finset.mul_sum, D]
  refine Finset.sum_bij' (fun δ hδ => shiftDown δ) (fun η hη => shiftUp η) ?_ ?_ ?_ ?_ ?_
  · intro δ hδ
    have hmem : δ ∈ support (m+1) (T + (m+1)) := (Finset.mem_filter.mp hδ).1
    have hn0 : ¬ δ 0 = 0 := (Finset.mem_filter.mp hδ).2
    have h0 : 0 < δ 0 := Nat.pos_of_ne_zero hn0
    exact support_shiftDown_mem (m := m) (N := T) hmem h0
  · intro η hη
    have hmem : shiftUp η ∈ support (m+1) (T + (m+1)) := support_shiftUp_mem (l := m+1) (N := T) hη
    exact Finset.mem_filter.mpr ⟨hmem, by simp [shiftUp]⟩
  · intro δ hδ
    change shiftUp (shiftDown δ) = δ
    apply shiftUp_shiftDown_of_pos
    intro i
    have hnd : NondecreasingFin δ := by
      have hmem : δ ∈ support (m+1) (T + (m+1)) := (Finset.mem_filter.mp hδ).1
      rw [support] at hmem
      exact (Finset.mem_filter.mp hmem).2.1
    have hn0 : ¬ δ 0 = 0 := (Finset.mem_filter.mp hδ).2
    have h0 : 0 < δ 0 := Nat.pos_of_ne_zero hn0
    exact lt_of_lt_of_le h0 (hnd 0 i (by simp))
  · intro η hη
    exact shiftDown_shiftUp η
  · intro δ hδ
    have hpos : ∀ i : Fin (m+1), 0 < δ i := by
      intro i
      have hnd : NondecreasingFin δ := by
        have hmem : δ ∈ support (m+1) (T + (m+1)) := (Finset.mem_filter.mp hδ).1
        rw [support] at hmem
        exact (Finset.mem_filter.mp hmem).2.1
      have hn0 : ¬ δ 0 = 0 := (Finset.mem_filter.mp hδ).2
      have h0 : 0 < δ 0 := Nat.pos_of_ne_zero hn0
      exact lt_of_lt_of_le h0 (hnd 0 i (by simp))
    change ((Nat.factorial (a + (m+1)) : ℚ) / (Nat.factorial a : ℚ)) * weight a (m+1) δ =
      weight (a+1) (m+1) (shiftDown δ)
    have hδeq : shiftUp (shiftDown δ) = δ := shiftUp_shiftDown_of_pos hpos
    calc
      ((Nat.factorial (a + (m+1)) : ℚ) / (Nat.factorial a : ℚ)) * weight a (m+1) δ =
          ((Nat.factorial (a + (m+1)) : ℚ) / (Nat.factorial a : ℚ)) * weight a (m+1) (shiftUp (shiftDown δ)) := by rw [hδeq]
      _ = weight (a+1) (m+1) (shiftDown δ) := weight_shiftUp_factorial a (m+1) (shiftDown δ)

lemma D_split_general_succ (a m T : Nat) :
    ((Nat.factorial (a + (m+1)) : ℚ) / (Nat.factorial a : ℚ)) * D a (m+1) (T + (m+1)) =
      D (a+1) (m+1) T + ((Nat.factorial (a + (m+1)) : ℚ) / (Nat.factorial a : ℚ)) * D (a+1) m (T + (m+1)) := by
  classical
  rw [D]
  have hpart := Finset.sum_filter_add_sum_filter_not (support (m+1) (T + (m+1))) (fun δ => δ 0 = 0) (fun δ => weight a (m+1) δ)
  calc
    ((Nat.factorial (a + (m+1)) : ℚ) / (Nat.factorial a : ℚ)) * (∑ δ ∈ support (m+1) (T + (m+1)), weight a (m+1) δ)
        = ((Nat.factorial (a + (m+1)) : ℚ) / (Nat.factorial a : ℚ)) *
          ((∑ δ ∈ (support (m+1) (T + (m+1))).filter (fun δ => δ 0 = 0), weight a (m+1) δ) +
           (∑ δ ∈ (support (m+1) (T + (m+1))).filter (fun δ => ¬ δ 0 = 0), weight a (m+1) δ)) := by
          rw [hpart]
    _ = ((Nat.factorial (a + (m+1)) : ℚ) / (Nat.factorial a : ℚ)) *
          (∑ δ ∈ (support (m+1) (T + (m+1))).filter (fun δ => ¬ δ 0 = 0), weight a (m+1) δ) +
        ((Nat.factorial (a + (m+1)) : ℚ) / (Nat.factorial a : ℚ)) *
          (∑ δ ∈ (support (m+1) (T + (m+1))).filter (fun δ => δ 0 = 0), weight a (m+1) δ) := by ring
    _ = D (a+1) (m+1) T + ((Nat.factorial (a + (m+1)) : ℚ) / (Nat.factorial a : ℚ)) * D (a+1) m (T + (m+1)) := by
          rw [D_positive_part_general_succ a m T, D_zero_part_general_succ a m (T + (m+1))]

/-- Exact `l = 3` split useful for attacking `G_l_three`. -/
lemma D_split_general_three (a T : Nat) :
    ((Nat.factorial (a+3) : ℚ) / (Nat.factorial a : ℚ)) * D a 3 (T+3) =
      D (a+1) 3 T + ((Nat.factorial (a+3) : ℚ) / (Nat.factorial a : ℚ)) * D (a+1) 2 (T+3) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using D_split_general_succ a 2 T

lemma D_three_ge_zero_term (a N : Nat) : D a 3 N ≥ D (a+1) 2 N := by
  classical
  rw [← D_zero_part_general_succ a 2 N]
  unfold D
  let z := ∑ δ ∈ (support 3 N).filter (fun δ => δ 0 = 0), weight a 3 δ
  let p := ∑ δ ∈ (support 3 N).filter (fun δ => ¬ δ 0 = 0), weight a 3 δ
  have hpart := Finset.sum_filter_add_sum_filter_not (support 3 N) (fun δ => δ 0 = 0) (fun δ => weight a 3 δ)
  have hpnon : 0 ≤ p := by
    dsimp [p]
    exact Finset.sum_nonneg (by intro δ hδ; exact weight_nonneg a 3 δ)
  calc
    z ≤ z + p := le_add_of_nonneg_right hpnon
    _ = ∑ δ ∈ support 3 N, weight a 3 δ := by
      dsimp [z, p]
      rw [← hpart]


/-- Conditional `l = 3` one-step result: after the exact split, it remains to
bound the zero-first-coordinate contribution by `K`. -/
lemma G_l_three_conditional_zero_extra
    (a s : Nat) (ha : 1 <= a) (K : ℚ)
    (hzero : (a : ℚ) * (((Nat.factorial (a+3) : ℚ) / (Nat.factorial a : ℚ)) *
        D (a+1) 2 (s+a+3)) ≤ K * D (a+1) 3 s)
    (hcoef : (a : ℚ) *
        (((1 : ℚ) / (a + 2 : Nat) + (1 : ℚ) / (a + 4 : Nat)) ^ a) + K < 1) :
    ((Nat.factorial (a+3) : ℚ)/(Nat.factorial (a-1) : ℚ))*D a 3 (s+a+3) < D (a+1) 3 s := by
  let c : ℚ := (1 : ℚ) / (a + 2 : Nat) + (1 : ℚ) / (a + 4 : Nat)
  have hstep : D (a+1) 3 (s + a) ≤ c ^ a * D (a+1) 3 s := by
    have h := iterated_contraction (D (a+1) 3) c (by positivity)
      (fun n => by simpa [c, Nat.add_assoc] using D_one_step_bound_sharp_general_pos_l (a+1) 3 n (by decide)) a s
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hsplit := D_split_general_three a (s+a)
  have hfac : ((Nat.factorial (a+3) : ℚ) / (Nat.factorial (a-1) : ℚ)) =
      (a : ℚ) * ((Nat.factorial (a+3) : ℚ) / (Nat.factorial a : ℚ)) := by
    have hsucc : Nat.factorial a = a * Nat.factorial (a-1) := by
      have h := Nat.factorial_succ (a-1)
      have : a - 1 + 1 = a := by omega

      simpa [this] using h
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a-1))]
    rw [hsucc]
    norm_num
    ring
  have htarget_pos : 0 < D (a+1) 3 s := D_pos (a+1) 3 s (by decide)
  calc
    ((Nat.factorial (a+3) : ℚ)/(Nat.factorial (a-1) : ℚ))*D a 3 (s+a+3)
        = (a : ℚ) * (((Nat.factorial (a+3) : ℚ) / (Nat.factorial a : ℚ)) * D a 3 ((s+a)+3)) := by
          rw [hfac]
          rw [show s+a+3 = (s+a)+3 by omega]
          ring
    _ = (a : ℚ) * (D (a+1) 3 (s+a) + ((Nat.factorial (a+3) : ℚ) / (Nat.factorial a : ℚ)) * D (a+1) 2 (s+a+3)) := by
          rw [hsplit]
    _ = (a : ℚ) * D (a+1) 3 (s+a) + (a : ℚ) * (((Nat.factorial (a+3) : ℚ) / (Nat.factorial a : ℚ)) * D (a+1) 2 (s+a+3)) := by ring
    _ ≤ (a : ℚ) * (c ^ a * D (a+1) 3 s) + K * D (a+1) 3 s := by
          exact add_le_add (mul_le_mul_of_nonneg_left hstep (by positivity)) hzero
    _ = ((a : ℚ) * c ^ a + K) * D (a+1) 3 s := by ring
    _ < 1 * D (a+1) 3 s := mul_lt_mul_of_pos_right (by simpa [c] using hcoef) htarget_pos
    _ = D (a+1) 3 s := by ring

lemma shifted_contraction_coeff_l_three_le_eight_fifteenths (a : Nat) (ha : 1 ≤ a) :
    (a : ℚ) * (((1 : ℚ) / (a + 2 : Nat) + (1 : ℚ) / (a + 4 : Nat)) ^ a) ≤ (8 : ℚ) / 15 := by
  by_cases ha1 : a = 1
  · subst a
    norm_num
  · have ha2 : 2 ≤ a := by omega
    have hc : ((1 : ℚ) / (a + 2 : Nat) + (1 : ℚ) / (a + 4 : Nat)) ≤ (9 : ℚ) / 20 := by
      field_simp
      norm_num at *
      have ha2q : (2 : ℚ) ≤ a := by exact_mod_cast ha2
      nlinarith [sq_nonneg ((a : ℚ) - 2)]
    have hcnon : 0 ≤ ((1 : ℚ) / (a + 2 : Nat) + (1 : ℚ) / (a + 4 : Nat)) := by positivity
    have hp : (((1 : ℚ) / (a + 2 : Nat) + (1 : ℚ) / (a + 4 : Nat)) ^ a) ≤ ((9 : ℚ) / 20) ^ a :=
      pow_le_pow_left₀ hcnon hc a
    have hbase : ∀ n : Nat, 2 ≤ n → (n : ℚ) * ((9 : ℚ) / 20) ^ n ≤ (2 : ℚ) * ((9 : ℚ) / 20) ^ (2 : Nat) := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => norm_num
      | succ n hn ih =>
          have hnon : 0 ≤ ((9 : ℚ) / 20) ^ n := by positivity
          calc
            ((n+1 : Nat) : ℚ) * ((9 : ℚ) / 20) ^ (n+1)
                = (((n+1 : Nat) : ℚ) * ((9 : ℚ) / 20)) * ((9 : ℚ) / 20) ^ n := by ring
            _ ≤ (n : ℚ) * ((9 : ℚ) / 20) ^ n := by
              refine mul_le_mul_of_nonneg_right ?_ hnon
              field_simp
              norm_num at *
              have hnq : (2 : ℚ) ≤ n := by exact_mod_cast hn
              nlinarith
            _ ≤ (2 : ℚ) * ((9 : ℚ) / 20) ^ (2 : Nat) := ih
    calc
      (a : ℚ) * (((1 : ℚ) / (a + 2 : Nat) + (1 : ℚ) / (a + 4 : Nat)) ^ a)
          ≤ (a : ℚ) * ((9 : ℚ) / 20) ^ a := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ (2 : ℚ) * ((9 : ℚ) / 20) ^ (2 : Nat) := hbase a ha2
      _ ≤ (8 : ℚ) / 15 := by norm_num

lemma G_l_three_of_zero_extra_one_fifth
    (a s : Nat) (ha : 1 <= a)
    (hzero : (a : ℚ) * (((Nat.factorial (a+3) : ℚ) / (Nat.factorial a : ℚ)) *
        D (a+1) 2 (s+a+3)) ≤ ((1 : ℚ) / 5) * D (a+1) 3 s) :
    ((Nat.factorial (a+3) : ℚ)/(Nat.factorial (a-1) : ℚ))*D a 3 (s+a+3) < D (a+1) 3 s := by
  refine G_l_three_conditional_zero_extra a s ha ((1 : ℚ) / 5) hzero ?_
  have hcoef := shifted_contraction_coeff_l_three_le_eight_fifteenths a ha
  linarith


/-- Source summand for the desired `l = 3` zero-extra estimate after expanding
`D (a+1) 2 (s+a+3)` with `D_b_two_explicit_formula`. -/
noncomputable def zeroExtraLThreeA (a s x : Nat) : ℚ :=
  (a : ℚ) * (((Nat.factorial (a+3) : ℚ) / (Nat.factorial a : ℚ)) *
    (((Nat.factorial (a+1) : ℚ) / (Nat.factorial (a+1+x) : ℚ)) *
      ((Nat.factorial (a+2) : ℚ) /
        (Nat.factorial (a+2+(s+a+3)-x) : ℚ))))

/-- Target summand for `D (a+2) 2 s` after expanding with
`D_b_two_explicit_formula`. -/
noncomputable def zeroExtraLThreeB (a s y : Nat) : ℚ :=
  ((Nat.factorial (a+2) : ℚ) / (Nat.factorial (a+2+y) : ℚ)) *
    ((Nat.factorial (a+3) : ℚ) / (Nat.factorial (a+3+s-y) : ℚ))

lemma zeroExtraLThreeA_nonneg (a s x : Nat) : 0 ≤ zeroExtraLThreeA a s x := by
  dsimp [zeroExtraLThreeA]
  positivity

lemma zeroExtraLThreeB_nonneg (a s y : Nat) : 0 ≤ zeroExtraLThreeB a s y := by
  dsimp [zeroExtraLThreeB]
  positivity

/-- The left-hand side of the desired estimate as an explicit finite sum. -/
lemma zero_extra_l_three_source_sum_formula (a s : Nat) :
    (a : ℚ) * (((Nat.factorial (a+3) : ℚ) / (Nat.factorial a : ℚ)) *
        D (a+1) 2 (s+a+3)) =
      ∑ x ∈ (Finset.range (s+a+3+1)).filter (fun x => 2*x ≤ s+a+3),
        zeroExtraLThreeA a s x := by
  rw [D_b_two_explicit_formula]
  rw [← mul_assoc]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x hx
  dsimp [zeroExtraLThreeA]
  ring

/-- The right-hand `D (a+2) 2 s` as an explicit finite sum. -/
lemma zero_extra_l_three_target_sum_formula (a s : Nat) :
    D (a+2) 2 s =
      ∑ y ∈ (Finset.range (s+1)).filter (fun y => 2*y ≤ s),
        zeroExtraLThreeB a s y := by
  simpa [zeroExtraLThreeB, Nat.add_assoc] using D_b_two_explicit_formula (a+2) s

/-- Split the source sum into the small range `x ≤ a+1` and the large range.
The intended final proof bounds the small range with the `B_0` target term and
maps the large range by `y = x-a-1`. -/
lemma zero_extra_l_three_source_split (a s : Nat) :
    (∑ x ∈ (Finset.range (s+a+3+1)).filter (fun x => 2*x ≤ s+a+3),
        zeroExtraLThreeA a s x) =
      (∑ x ∈ ((Finset.range (s+a+3+1)).filter (fun x => 2*x ≤ s+a+3)).filter
          (fun x => x ≤ a+1), zeroExtraLThreeA a s x) +
      (∑ x ∈ ((Finset.range (s+a+3+1)).filter (fun x => 2*x ≤ s+a+3)).filter
          (fun x => ¬ x ≤ a+1), zeroExtraLThreeA a s x) := by
  classical
  symm
  exact Finset.sum_filter_add_sum_filter_not
    ((Finset.range (s+a+3+1)).filter (fun x => 2*x ≤ s+a+3))
    (fun x => x ≤ a+1) (fun x => zeroExtraLThreeA a s x)

/-- The target sum contains the `B_0` summand. -/
lemma zero_extra_l_three_target_ge_B0 (a s : Nat) :
    zeroExtraLThreeB a s 0 ≤ D (a+2) 2 s := by
  classical
  rw [zero_extra_l_three_target_sum_formula]
  exact Finset.single_le_sum
    (by intro y hy; exact zeroExtraLThreeB_nonneg a s y)
    (by simp)

/-- The large-source map `y = x-a-1` lands in the target index set. -/
lemma zero_extra_l_three_large_map_mem (a s x : Nat) (ha : 1 ≤ a)
    (hx : x ∈ (Finset.range (s+a+3+1)).filter (fun x => 2*x ≤ s+a+3))
    (hlarge : ¬ x ≤ a+1) :
    x - a - 1 ∈ (Finset.range (s+1)).filter (fun y => 2*y ≤ s) := by
  rw [Finset.mem_filter] at hx ⊢
  rw [Finset.mem_range] at hx ⊢
  constructor
  · omega
  · omega


/-- Termwise estimate for the large part of the `l = 3` zero-extra sum.
For `x ≥ a+2`, the change of variables `y = x-a-1` gives the factorial
ratio
`A/B = a(a+1)/((x+2)⋯(x+a+1)(2a+s+5-x))`, which is at most `1/5`. -/
lemma zero_extra_l_three_large_term (a s x : Nat) (ha : 1 ≤ a)
    (hx : x ∈ (Finset.range (s+a+3+1)).filter (fun x => 2*x ≤ s+a+3))
    (hlarge : ¬ x ≤ a+1) :
    zeroExtraLThreeA a s x ≤ ((1:ℚ)/5) * zeroExtraLThreeB a s (x-a-1) := by
  have hxlarge : a + 2 ≤ x := by omega
  have hxineq : 2*x ≤ s+a+3 := by
    rw [Finset.mem_filter] at hx
    exact hx.2
  have hy1 : a + 2 + (x - a - 1) = x + 1 := by omega
  have hy2 : a + 3 + s - (x - a - 1) = 2*a + s + 4 - x := by omega
  have hA2 : a + 2 + (s + a + 3) - x = 2*a + s + 5 - x := by omega
  dsimp [zeroExtraLThreeA, zeroExtraLThreeB]
  rw [hy1, hy2, hA2]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a+1+x)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2*a+s+5-x)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (x+1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2*a+s+4-x)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a+2)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a+3))]
  let N := 2*a+s+4-x
  have hN1 : 2*a+s+5-x = N+1 := by omega
  have hfac : a * Nat.factorial (a+1) * 5 * Nat.factorial (x+1) * Nat.factorial N ≤
      Nat.factorial a * Nat.factorial (a+1+x) * Nat.factorial (N+1) := by
    by_cases ha1 : a = 1
    · subst a
      have hNlower : x + 3 ≤ N + 1 := by omega
      have hcoef : 10 ≤ (x+2) * (N+1) := by nlinarith
      have hxfac1 : (x+2) * Nat.factorial (x+1) = Nat.factorial (1+1+x) := by
        symm
        rw [show 1+1+x = (x+1)+1 by omega, Nat.factorial_succ]
      have hNfac : (N+1) * Nat.factorial N = Nat.factorial (N+1) := by
        rw [Nat.factorial_succ]
      calc
        1 * Nat.factorial (1+1) * 5 * Nat.factorial (x+1) * Nat.factorial N
            = (10) * (Nat.factorial (x+1) * Nat.factorial N) := by norm_num; ring
        _ ≤ ((x+2) * (N+1)) * (Nat.factorial (x+1) * Nat.factorial N) :=
            Nat.mul_le_mul_right _ hcoef
        _ = ((x+2) * Nat.factorial (x+1)) * ((N+1) * Nat.factorial N) := by ring
        _ = Nat.factorial (1+1+x) * Nat.factorial (N+1) := by rw [hxfac1, hNfac]
        _ = Nat.factorial 1 * Nat.factorial (1+1+x) * Nat.factorial (N+1) := by norm_num
    · have ha2 : 2 ≤ a := by omega
      have hcoef : 5 * a * (a+1) ≤ (x+3) * (x+2) * (N+1) := by
        have hx2 : a + 4 ≤ x + 2 := by omega
        have hx3 : a + 5 ≤ x + 3 := by omega
        have hN : 2*a + 4 ≤ N + 1 := by omega
        have hpoly : 5 * a * (a+1) ≤ (a+5) * (a+4) * (2*a+4) := by
          nlinarith [sq_nonneg ((a : ℤ) - 2)]
        have hprod : (a+5) * (a+4) * (2*a+4) ≤ (x+3) * (x+2) * (N+1) := by
          exact Nat.mul_le_mul (Nat.mul_le_mul hx3 hx2) hN
        exact le_trans hpoly hprod
      have hxfac : (x+3) * (x+2) * Nat.factorial (x+1) ≤ Nat.factorial (a+1+x) := by
        have hmono : Nat.factorial (x+3) ≤ Nat.factorial (a+1+x) := Nat.factorial_le (by omega)
        have hrew : Nat.factorial (x+3) = (x+3) * (x+2) * Nat.factorial (x+1) := by
          rw [show x+3 = (x+2)+1 by omega, Nat.factorial_succ]
          rw [show x+2 = (x+1)+1 by omega, Nat.factorial_succ]
          ring
        simpa [hrew] using hmono
      calc
        a * Nat.factorial (a+1) * 5 * Nat.factorial (x+1) * Nat.factorial N
            = (5*a*(a+1)) * (Nat.factorial a * (Nat.factorial (x+1) * Nat.factorial N)) := by
              rw [Nat.factorial_succ]
              ring
        _ ≤ ((x+3)*(x+2)*(N+1)) * (Nat.factorial a * (Nat.factorial (x+1) * Nat.factorial N)) :=
            Nat.mul_le_mul_right _ hcoef
        _ = Nat.factorial a * (((x+3)*(x+2)*Nat.factorial (x+1)) * ((N+1)*Nat.factorial N)) := by ring
        _ ≤ Nat.factorial a * (Nat.factorial (a+1+x) * Nat.factorial (N+1)) := by
            apply Nat.mul_le_mul_left
            exact Nat.mul_le_mul hxfac (by rw [Nat.factorial_succ])
        _ = Nat.factorial a * Nat.factorial (a+1+x) * Nat.factorial (N+1) := by ring
  rw [hN1]
  exact_mod_cast hfac


lemma factorial_mul_pow_le_factorial_add (n m k : Nat) (hm : m ≤ n + 1) :
    Nat.factorial n * m ^ k ≤ Nat.factorial (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        Nat.factorial n * m ^ (k + 1) = m * (Nat.factorial n * m ^ k) := by ring
        _ ≤ m * Nat.factorial (n + k) := Nat.mul_le_mul_left m ih
        _ ≤ (n + k + 1) * Nat.factorial (n + k) := by
          exact Nat.mul_le_mul_right _ (by omega)
        _ = Nat.factorial (n + (k + 1)) := by
          rw [show n + (k + 1) = (n + k) + 1 by omega, Nat.factorial_succ]

lemma zero_extra_l_three_small_term_zero_bound (a s : Nat) :
    zeroExtraLThreeA a s 0 ≤
      (((a : ℚ) * (a+1 : Nat) * (a+2 : Nat)) / ((a+4 : Nat) ^ (a+2))) *
        zeroExtraLThreeB a s 0 := by
  dsimp [zeroExtraLThreeA, zeroExtraLThreeB]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a+1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a+2)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a+3)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a+3+s)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a+2+(s+a+3))),
    pow_ne_zero _ (by exact_mod_cast (show a+4 ≠ 0 by omega) : ((a+4 : Nat) : ℚ) ≠ 0)]
  have hfac : Nat.factorial (a + 3 + s) * (a + 4) ^ (a + 2) ≤
      Nat.factorial (a + 2 + (s + a + 3)) := by
    have h := factorial_mul_pow_le_factorial_add (a + 3 + s) (a + 4) (a + 2) (by omega)
    have hadd : a + 3 + s + (a + 2) = a + 2 + (s + a + 3) := by omega
    simpa [hadd] using h
  have hfac2 : (Nat.factorial (a+2) : ℚ) = (a+2 : Nat) * (a+1 : Nat) * (Nat.factorial a : ℚ) := by
    rw [show a+2 = (a+1)+1 by omega, Nat.factorial_succ]
    rw [show a+1 = a+1 by rfl, Nat.factorial_succ]
    norm_num
    ring

  have hfacQ : ((Nat.factorial (a + 3 + s) * (a + 4) ^ (a + 2) : Nat) : ℚ) ≤
      (Nat.factorial (a + 2 + (s + a + 3)) : ℚ) := by exact_mod_cast hfac
  calc
    (a : ℚ) * (Nat.factorial (a + 2) : ℚ) * ((a + 4 : Nat) : ℚ) ^ (a + 2) *
          (Nat.factorial (a + 3 + s) : ℚ)
        = ((a : ℚ) * ((a+2 : Nat) : ℚ) * ((a+1 : Nat) : ℚ) * (Nat.factorial a : ℚ)) *
            (((a + 4 : Nat) : ℚ) ^ (a + 2) * (Nat.factorial (a + 3 + s) : ℚ)) := by
          rw [hfac2]
          ring
    _ ≤ ((a : ℚ) * ((a+2 : Nat) : ℚ) * ((a+1 : Nat) : ℚ) * (Nat.factorial a : ℚ)) *
          (Nat.factorial (a + 2 + (s + a + 3)) : ℚ) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hfacQ
          · positivity
    _ = (a : ℚ) * (Nat.factorial a : ℚ) * (Nat.factorial (a + 2 + (s + a + 3)) : ℚ) *
          ((a+1 : Nat) : ℚ) * ((a+2 : Nat) : ℚ) := by ring


lemma zero_extra_l_three_small_term_pos_bound (a s x : Nat) (hxpos : 1 ≤ x) (hxle : x ≤ a+1) :
    zeroExtraLThreeA a s x ≤
      (((a : ℚ) * (a+1 : Nat)) / ((a+3 : Nat) ^ (a+1))) *
        zeroExtraLThreeB a s 0 := by
  dsimp [zeroExtraLThreeA, zeroExtraLThreeB]
  have hbig : a + 2 + (s + a + 3) - x = 2*a + s + 5 - x := by omega
  rw [hbig]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a+1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a+2)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a+3)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a+1+x)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2*a+s+5-x)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a+3+s)),
    pow_ne_zero _ (by exact_mod_cast (show a+3 ≠ 0 by omega) : ((a+3 : Nat) : ℚ) ≠ 0)]
  have h1 : Nat.factorial (a+2) * (a+3) ^ (x-1) ≤ Nat.factorial (a+1+x) := by
    have h := factorial_mul_pow_le_factorial_add (a+2) (a+3) (x-1) (by omega)
    have hadd : a+2 + (x-1) = a+1+x := by omega
    simpa [hadd] using h
  have h2 : Nat.factorial (a+3+s) * (a+3) ^ (a+2-x) ≤ Nat.factorial (2*a+s+5-x) := by
    have h := factorial_mul_pow_le_factorial_add (a+3+s) (a+3) (a+2-x) (by omega)
    have hadd : a+3+s + (a+2-x) = 2*a+s+5-x := by omega
    simpa [hadd] using h
  have hpow : (x-1) + (a+2-x) = a+1 := by omega
  have hprodNat : Nat.factorial (a+2) * Nat.factorial (a+3+s) * (a+3)^(a+1) ≤
      Nat.factorial (a+1+x) * Nat.factorial (2*a+s+5-x) := by
    calc
      Nat.factorial (a+2) * Nat.factorial (a+3+s) * (a+3)^(a+1)
          = (Nat.factorial (a+2) * (a+3)^(x-1)) *
              (Nat.factorial (a+3+s) * (a+3)^(a+2-x)) := by
            rw [← hpow, pow_add]
            ring
      _ ≤ Nat.factorial (a+1+x) * Nat.factorial (2*a+s+5-x) := Nat.mul_le_mul h1 h2
  have hprodQ : ((Nat.factorial (a+2) * Nat.factorial (a+3+s) * (a+3)^(a+1) : Nat) : ℚ) ≤
      ((Nat.factorial (a+1+x) * Nat.factorial (2*a+s+5-x) : Nat) : ℚ) := by exact_mod_cast hprodNat
  have hfac1 : (Nat.factorial (a+1) : ℚ) = (a+1 : Nat) * (Nat.factorial a : ℚ) := by
    have hfac1Nat : Nat.factorial (a+1) = (a+1) * Nat.factorial a := by
      rw [Nat.factorial_succ]
    exact_mod_cast hfac1Nat
  calc
    (a : ℚ) * (Nat.factorial (a + 1) : ℚ) * (Nat.factorial (a + 2) : ℚ) *
          ((a + 3 : Nat) : ℚ) ^ (a + 1) * (Nat.factorial (a + 3 + s) : ℚ)
        = ((a : ℚ) * ((a+1 : Nat) : ℚ) * (Nat.factorial a : ℚ)) *
            ((Nat.factorial (a+2) : ℚ) * (Nat.factorial (a+3+s) : ℚ) *
              ((a+3 : Nat) : ℚ)^(a+1)) := by
          rw [hfac1]
          ring
    _ ≤ ((a : ℚ) * ((a+1 : Nat) : ℚ) * (Nat.factorial a : ℚ)) *
          ((Nat.factorial (a+1+x) : ℚ) * (Nat.factorial (2*a+s+5-x) : ℚ)) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hprodQ
          · positivity
    _ = (a : ℚ) * (Nat.factorial a : ℚ) * (Nat.factorial (a+1+x) : ℚ) *
          (Nat.factorial (2*a+s+5-x) : ℚ) * ((a+1 : Nat) : ℚ) := by ring

lemma small_coeff_all_le_one_fifth_aux (a : Nat) (ha2 : 2 ≤ a) :
    5 * (a * (a+1) * (a+2)) ≤ (a+3)^(a+1) := by
  induction a, ha2 using Nat.le_induction with
  | base => norm_num
  | succ a ha ih =>
      calc
        5 * ((a+1) * ((a+1)+1) * ((a+1)+2))
            = 5 * ((a+1) * (a+2) * (a+3)) := by ring
        _ ≤ 5 * (a * ((a+1) * (a+2) * (a+3))) := by
          apply Nat.mul_le_mul_left
          exact Nat.le_mul_of_pos_left _ (by omega)
        _ = (a+3) * (5 * (a * (a+1) * (a+2))) := by ring
        _ ≤ (a+3) * (a+3)^(a+1) := Nat.mul_le_mul_left _ ih
        _ = (a+3)^(a+2) := by
          rw [show a+2 = (a+1)+1 by omega, pow_succ]
          ring
        _ ≤ (a+4)^(a+2) := pow_le_pow_left₀ (by positivity) (by omega) (a+2)

lemma small_coeff_all_le_one_fifth (a : Nat) (ha2 : 2 ≤ a) :
    ((a+2 : Nat) : ℚ) * (((a : ℚ) * (a+1 : Nat)) / ((a+3 : Nat) ^ (a+1))) ≤ (1:ℚ)/5 := by
  have h := small_coeff_all_le_one_fifth_aux a ha2
  have hq0 : ((5 * (a * (a+1) * (a+2)) : Nat) : ℚ) ≤ ((a+3 : Nat) : ℚ)^(a+1) := by exact_mod_cast h
  have hq : (5:ℚ) * (a : ℚ) * (a+1 : Nat) * (a+2 : Nat) ≤ ((a+3 : Nat) : ℚ)^(a+1) := by
    simpa [Nat.cast_mul, Nat.cast_pow, mul_assoc] using hq0
  field_simp [pow_ne_zero _ (by exact_mod_cast (show a+3 ≠ 0 by omega) : ((a+3 : Nat) : ℚ) ≠ 0)]
  simpa [Nat.cast_mul, Nat.cast_pow, mul_comm, mul_left_comm, mul_assoc] using hq

lemma small_coeff_zero_le_pos_coeff (a : Nat) :
    (((a : ℚ) * (a+1 : Nat) * (a+2 : Nat)) / ((a+4 : Nat) ^ (a+2))) ≤
      (((a : ℚ) * (a+1 : Nat)) / ((a+3 : Nat) ^ (a+1))) := by
  have hnat : (a+2) * (a+3)^(a+1) ≤ (a+4)^(a+2) := by
    calc
      (a+2) * (a+3)^(a+1) ≤ (a+4) * (a+3)^(a+1) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (a+4) * (a+4)^(a+1) := Nat.mul_le_mul_left _ (pow_le_pow_left₀ (by positivity) (by omega) (a+1))
      _ = (a+4)^(a+2) := by
        rw [show a+2 = (a+1)+1 by omega, pow_succ]
        ring
  have hq : ((a+2 : Nat) : ℚ) * ((a+3 : Nat) : ℚ)^(a+1) ≤ ((a+4 : Nat) : ℚ)^(a+2) := by exact_mod_cast hnat
  field_simp [pow_ne_zero _ (by exact_mod_cast (show a+3 ≠ 0 by omega) : ((a+3 : Nat) : ℚ) ≠ 0),
    pow_ne_zero _ (by exact_mod_cast (show a+4 ≠ 0 by omega) : ((a+4 : Nat) : ℚ) ≠ 0)]
  ring_nf at hq ⊢
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hq (show 0 ≤ (a:ℚ) by positivity)


lemma zero_extra_l_three_small_sum_of_two_le_a (a s : Nat) (ha2 : 2 ≤ a) :
    (∑ x ∈ ((Finset.range (s+a+3+1)).filter (fun x => 2*x <= s+a+3)).filter (fun x => x <= a+1), zeroExtraLThreeA a s x)
      ≤ ((1:ℚ)/5) * zeroExtraLThreeB a s 0 := by
  classical
  let S := ((Finset.range (s+a+3+1)).filter (fun x => 2*x <= s+a+3)).filter (fun x => x <= a+1)
  let c : ℚ := (((a : ℚ) * (a+1 : Nat)) / ((a+3 : Nat) ^ (a+1)))
  have hc_nonneg : 0 ≤ c := by dsimp [c]; positivity
  have hB_nonneg : 0 ≤ zeroExtraLThreeB a s 0 := zeroExtraLThreeB_nonneg a s 0
  have hterm : ∀ x ∈ S, zeroExtraLThreeA a s x ≤ c * zeroExtraLThreeB a s 0 := by
    intro x hx
    have hxle : x ≤ a+1 := by
      dsimp [S] at hx
      simp only [Finset.mem_filter] at hx
      exact hx.2
    by_cases hx0 : x = 0
    · subst x
      exact le_trans (zero_extra_l_three_small_term_zero_bound a s)
        (mul_le_mul_of_nonneg_right (small_coeff_zero_le_pos_coeff a) hB_nonneg)
    · have hxpos : 1 ≤ x := by omega
      exact zero_extra_l_three_small_term_pos_bound a s x hxpos hxle
  have hsum_le : (∑ x ∈ S, zeroExtraLThreeA a s x) ≤ (S.card : ℚ) * (c * zeroExtraLThreeB a s 0) := by
    calc
      (∑ x ∈ S, zeroExtraLThreeA a s x) ≤ ∑ x ∈ S, c * zeroExtraLThreeB a s 0 := by
        exact Finset.sum_le_sum hterm
      _ = (S.card : ℚ) * (c * zeroExtraLThreeB a s 0) := by simp
  have hcard : S.card ≤ a+2 := by
    have hsub : S ⊆ Finset.range (a+2) := by
      intro x hx
      dsimp [S] at hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
      omega
    have := Finset.card_le_card hsub
    simpa using this
  have hcardQ : (S.card : ℚ) ≤ (a+2 : Nat) := by exact_mod_cast hcard
  have hcoef : (S.card : ℚ) * c ≤ (1:ℚ)/5 := by
    calc
      (S.card : ℚ) * c ≤ ((a+2 : Nat) : ℚ) * c := mul_le_mul_of_nonneg_right hcardQ hc_nonneg
      _ ≤ (1:ℚ)/5 := small_coeff_all_le_one_fifth a ha2
  calc
    (∑ x ∈ S, zeroExtraLThreeA a s x) ≤ (S.card : ℚ) * (c * zeroExtraLThreeB a s 0) := hsum_le
    _ = ((S.card : ℚ) * c) * zeroExtraLThreeB a s 0 := by ring
    _ ≤ ((1:ℚ)/5) * zeroExtraLThreeB a s 0 := mul_le_mul_of_nonneg_right hcoef hB_nonneg


lemma zero_extra_l_three_small_term_a_one_zero (s : Nat) :
    zeroExtraLThreeA 1 s 0 ≤ ((1:ℚ)/35) * zeroExtraLThreeB 1 s 0 := by
  dsimp [zeroExtraLThreeA, zeroExtraLThreeB]
  norm_num [Nat.factorial]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (4+s))]
  have hcoef : 6 * 35 ≤ (s+7)*(s+6)*(s+5) := by
    calc
      6 * 35 = 7*6*5 := by norm_num
      _ ≤ (s+7)*(s+6)*(s+5) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
  have hnat : 6 * 35 * Nat.factorial (4+s) ≤
      (3 + (s + 3) + 1) * (3 + (s + 2) + 1) * (3 + (s + 1) + 1) *
        (3 + s + 1) * Nat.factorial (3+s) := by
    rw [show 4+s = (3+s)+1 by omega, Nat.factorial_succ]
    calc
      6 * 35 * ((3 + s + 1) * Nat.factorial (3 + s))
          = (6*35) * ((s+4) * Nat.factorial (3+s)) := by ring
      _ ≤ ((s+7)*(s+6)*(s+5)) * ((s+4) * Nat.factorial (3+s)) :=
          Nat.mul_le_mul_right _ hcoef
      _ = (3 + (s + 3) + 1) * (3 + (s + 2) + 1) * (3 + (s + 1) + 1) *
          (3 + s + 1) * Nat.factorial (3+s) := by ring
  exact_mod_cast hnat

lemma zero_extra_l_three_small_term_a_one_one (s : Nat) :
    zeroExtraLThreeA 1 s 1 ≤ ((1:ℚ)/15) * zeroExtraLThreeB 1 s 0 := by
  dsimp [zeroExtraLThreeA, zeroExtraLThreeB]
  norm_num [Nat.factorial]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (4+s))]
  have hcoef : 6 * 15 ≤ 3 * ((s+6)*(s+5)) := by
    calc
      6 * 15 = 3 * (6*5) := by norm_num
      _ ≤ 3 * ((s+6)*(s+5)) := by
        exact Nat.mul_le_mul_left 3 (Nat.mul_le_mul (by omega) (by omega))
  have hnat : 6 * 15 * Nat.factorial (4+s) ≤
      3 * (3 + (s + 2) + 1) * (3 + (s + 1) + 1) * (3 + s + 1) *
        Nat.factorial (3+s) := by
    rw [show 4+s = (3+s)+1 by omega, Nat.factorial_succ]
    calc
      6 * 15 * ((3 + s + 1) * Nat.factorial (3 + s))
          = (6*15) * ((s+4) * Nat.factorial (3+s)) := by ring
      _ ≤ (3*((s+6)*(s+5))) * ((s+4) * Nat.factorial (3+s)) :=
          Nat.mul_le_mul_right _ hcoef
      _ = 3 * (3 + (s + 2) + 1) * (3 + (s + 1) + 1) * (3 + s + 1) *
          Nat.factorial (3+s) := by ring
  exact_mod_cast hnat

lemma zero_extra_l_three_small_term_a_one_two (s : Nat) :
    zeroExtraLThreeA 1 s 2 ≤ ((1:ℚ)/10) * zeroExtraLThreeB 1 s 0 := by
  dsimp [zeroExtraLThreeA, zeroExtraLThreeB]
  norm_num [Nat.factorial]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (4+s))]
  have hcoef : 6 * 10 ≤ 12 * (s+5) := by
    calc
      6 * 10 = 12*5 := by norm_num
      _ ≤ 12*(s+5) := by exact Nat.mul_le_mul_left 12 (by omega)
  have hnat : 6 * 10 * Nat.factorial (4+s) ≤
      12 * Nat.factorial (3 + (s + 1 + 3) - 2) := by
    rw [show 4+s = (3+s)+1 by omega, Nat.factorial_succ]
    rw [show 3 + (s + 1 + 3) - 2 = (4+s)+1 by omega, Nat.factorial_succ]
    calc
      6 * 10 * ((3 + s + 1) * Nat.factorial (3 + s))
          = (6*10) * ((s+4) * Nat.factorial (3+s)) := by ring
      _ ≤ (12*(s+5)) * ((s+4) * Nat.factorial (3+s)) :=
          Nat.mul_le_mul_right _ hcoef
      _ = 12 * ((4 + s + 1) * Nat.factorial (4+s)) := by
          rw [show 4+s = (3+s)+1 by omega, Nat.factorial_succ]
          ring
  exact_mod_cast hnat

lemma zero_extra_l_three_small_sum_a_one (s : Nat) :
    (∑ x ∈ ((Finset.range (s+1+3+1)).filter (fun x => 2*x <= s+1+3)).filter (fun x => x <= 1+1), zeroExtraLThreeA 1 s x)
      ≤ ((1:ℚ)/5) * zeroExtraLThreeB 1 s 0 := by
  classical
  let S := ((Finset.range (s+1+3+1)).filter (fun x => 2*x <= s+1+3)).filter (fun x => x <= 1+1)
  have hsub : S ⊆ Finset.range 3 := by
    intro x hx
    dsimp [S] at hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    omega
  have hB_nonneg : 0 ≤ zeroExtraLThreeB 1 s 0 := zeroExtraLThreeB_nonneg 1 s 0
  have hle_range : (∑ x ∈ S, zeroExtraLThreeA 1 s x) ≤
      ∑ x ∈ Finset.range 3, zeroExtraLThreeA 1 s x := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (by intro x hx hnot; exact zeroExtraLThreeA_nonneg 1 s x)
  have hrange : (∑ x ∈ Finset.range 3, zeroExtraLThreeA 1 s x) ≤
      ((1:ℚ)/35) * zeroExtraLThreeB 1 s 0 +
        ((1:ℚ)/15) * zeroExtraLThreeB 1 s 0 +
          ((1:ℚ)/10) * zeroExtraLThreeB 1 s 0 := by
    calc
      (∑ x ∈ Finset.range 3, zeroExtraLThreeA 1 s x)
          = zeroExtraLThreeA 1 s 0 + zeroExtraLThreeA 1 s 1 + zeroExtraLThreeA 1 s 2 := by
            norm_num [Finset.sum_range_succ]
      _ ≤ ((1:ℚ)/35) * zeroExtraLThreeB 1 s 0 +
          ((1:ℚ)/15) * zeroExtraLThreeB 1 s 0 +
            ((1:ℚ)/10) * zeroExtraLThreeB 1 s 0 := by
            exact add_le_add (add_le_add (zero_extra_l_three_small_term_a_one_zero s)
              (zero_extra_l_three_small_term_a_one_one s))
              (zero_extra_l_three_small_term_a_one_two s)
  calc
    (∑ x ∈ S, zeroExtraLThreeA 1 s x) ≤
        (∑ x ∈ Finset.range 3, zeroExtraLThreeA 1 s x) := hle_range
    _ ≤ ((1:ℚ)/35) * zeroExtraLThreeB 1 s 0 +
        ((1:ℚ)/15) * zeroExtraLThreeB 1 s 0 +
          ((1:ℚ)/10) * zeroExtraLThreeB 1 s 0 := hrange
    _ = ((41:ℚ)/210) * zeroExtraLThreeB 1 s 0 := by ring
    _ ≤ ((1:ℚ)/5) * zeroExtraLThreeB 1 s 0 := by
      exact mul_le_mul_of_nonneg_right (by norm_num) hB_nonneg



lemma zero_extra_l_three_small_sum (a s : Nat) (ha : 1 ≤ a) :
    (∑ x ∈ ((Finset.range (s+a+3+1)).filter (fun x => 2*x <= s+a+3)).filter (fun x => x <= a+1), zeroExtraLThreeA a s x)
      ≤ ((1:ℚ)/5) * zeroExtraLThreeB a s 0 := by
  by_cases ha1 : a = 1
  · subst a
    simpa using zero_extra_l_three_small_sum_a_one s
  · have ha2 : 2 ≤ a := by omega
    exact zero_extra_l_three_small_sum_of_two_le_a a s ha2

lemma zero_extra_l_three_large_sum (a s : Nat) (ha : 1 ≤ a) :
    (∑ x ∈ ((Finset.range (s+a+3+1)).filter (fun x => 2*x <= s+a+3)).filter (fun x => ¬ x <= a+1), zeroExtraLThreeA a s x)
      ≤ ((1:ℚ)/5) *
        (∑ y ∈ ((Finset.range (s+1)).filter (fun y => 2*y ≤ s)).filter (fun y => y ≠ 0), zeroExtraLThreeB a s y) := by
  classical
  let S := ((Finset.range (s+a+3+1)).filter (fun x => 2*x <= s+a+3)).filter (fun x => ¬ x <= a+1)
  let T := ((Finset.range (s+1)).filter (fun y => 2*y ≤ s)).filter (fun y => y ≠ 0)
  let f : Nat → Nat := fun x => x - a - 1
  have hinj : Set.InjOn f S := by
    intro x hx z hz hxz
    change x ∈ S at hx
    change z ∈ S at hz
    dsimp [f] at hxz
    have hxnot : ¬ x ≤ a+1 := (Finset.mem_filter.mp hx).2
    have hznot : ¬ z ≤ a+1 := (Finset.mem_filter.mp hz).2
    have hxlarge : a + 2 ≤ x := by omega
    have hzlarge : a + 2 ≤ z := by omega
    omega
  have hterm : ∀ x ∈ S, zeroExtraLThreeA a s x ≤ ((1:ℚ)/5) * zeroExtraLThreeB a s (f x) := by
    intro x hx
    have hxmem : x ∈ (Finset.range (s+a+3+1)).filter (fun x => 2*x ≤ s+a+3) := (Finset.mem_filter.mp hx).1
    have hxlarge : ¬ x ≤ a+1 := (Finset.mem_filter.mp hx).2
    exact zero_extra_l_three_large_term a s x ha hxmem hxlarge
  have himg_subset : S.image f ⊆ T := by
    intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨x, hxS, rfl⟩
    have hxmem : x ∈ (Finset.range (s+a+3+1)).filter (fun x => 2*x ≤ s+a+3) := (Finset.mem_filter.mp hxS).1
    have hxlarge : ¬ x ≤ a+1 := (Finset.mem_filter.mp hxS).2
    dsimp [T]
    simp only [Finset.mem_filter]
    constructor
    · simpa [f] using zero_extra_l_three_large_map_mem a s x ha hxmem hxlarge
    · dsimp [f]
      omega
  calc
    (∑ x ∈ S, zeroExtraLThreeA a s x)
        ≤ ∑ x ∈ S, ((1:ℚ)/5) * zeroExtraLThreeB a s (f x) := by
          exact Finset.sum_le_sum hterm
    _ = ∑ y ∈ S.image f, ((1:ℚ)/5) * zeroExtraLThreeB a s y := by
          rw [Finset.sum_image]
          exact hinj
    _ ≤ ∑ y ∈ T, ((1:ℚ)/5) * zeroExtraLThreeB a s y := by
          exact Finset.sum_le_sum_of_subset_of_nonneg himg_subset
            (by intro y hy hnot; exact mul_nonneg (by norm_num) (zeroExtraLThreeB_nonneg a s y))
    _ = ((1:ℚ)/5) * (∑ y ∈ T, zeroExtraLThreeB a s y) := by
          rw [Finset.mul_sum]

lemma zero_extra_l_three_le_one_fifth (a s : Nat) (ha : 1 ≤ a) :
    (a : ℚ) * (((Nat.factorial (a+3) : ℚ) / (Nat.factorial a : ℚ)) *
        D (a+1) 2 (s+a+3)) ≤ ((1 : ℚ) / 5) * D (a+2) 2 s := by
  classical
  let Src := (Finset.range (s+a+3+1)).filter (fun x => 2*x <= s+a+3)
  let Small := Src.filter (fun x => x <= a+1)
  let Large := Src.filter (fun x => ¬ x <= a+1)
  let Tgt := (Finset.range (s+1)).filter (fun y => 2*y ≤ s)
  let TgtPos := Tgt.filter (fun y => y ≠ 0)
  have hsrc_split : (∑ x ∈ Src, zeroExtraLThreeA a s x) =
      (∑ x ∈ Small, zeroExtraLThreeA a s x) + (∑ x ∈ Large, zeroExtraLThreeA a s x) := by
    dsimp [Small, Large, Src]
    exact zero_extra_l_three_source_split a s
  have hsmall := zero_extra_l_three_small_sum a s ha
  have hlarge := zero_extra_l_three_large_sum a s ha
  have htarget_split : (∑ y ∈ Tgt, zeroExtraLThreeB a s y) =
      zeroExtraLThreeB a s 0 + (∑ y ∈ TgtPos, zeroExtraLThreeB a s y) := by
    have h0 : 0 ∈ Tgt := by
      dsimp [Tgt]
      simp
    calc
      (∑ y ∈ Tgt, zeroExtraLThreeB a s y)
          = ∑ y ∈ insert 0 TgtPos, zeroExtraLThreeB a s y := by
            congr 1
            ext y
            dsimp [TgtPos]
            by_cases hy0 : y = 0 <;> simp [hy0, Tgt, h0]
      _ = zeroExtraLThreeB a s 0 + ∑ y ∈ TgtPos, zeroExtraLThreeB a s y := by
            rw [Finset.sum_insert]
            dsimp [TgtPos]
            simp
  calc
    (a : ℚ) * (((Nat.factorial (a+3) : ℚ) / (Nat.factorial a : ℚ)) * D (a+1) 2 (s+a+3))
        = ∑ x ∈ Src, zeroExtraLThreeA a s x := by
          dsimp [Src]
          exact zero_extra_l_three_source_sum_formula a s
    _ = (∑ x ∈ Small, zeroExtraLThreeA a s x) + (∑ x ∈ Large, zeroExtraLThreeA a s x) := hsrc_split
    _ ≤ ((1:ℚ)/5) * zeroExtraLThreeB a s 0 +
          ((1:ℚ)/5) * (∑ y ∈ TgtPos, zeroExtraLThreeB a s y) := add_le_add hsmall hlarge
    _ = ((1:ℚ)/5) * (zeroExtraLThreeB a s 0 + ∑ y ∈ TgtPos, zeroExtraLThreeB a s y) := by ring
    _ = ((1:ℚ)/5) * (∑ y ∈ Tgt, zeroExtraLThreeB a s y) := by rw [htarget_split]
    _ = ((1:ℚ)/5) * D (a+2) 2 s := by
          rw [zero_extra_l_three_target_sum_formula]

/-- Bridge from the sharper zero-extra estimate against the denominator
`D (a+2) 2 s` to the existing conditional `l = 3` result.  The remaining
unconditional task is precisely to prove the hypothesis of this lemma. -/
lemma G_l_three_of_zero_extra_l_three_le_one_fifth
    (a s : Nat) (ha : 1 <= a)
    (hzero : (a : ℚ) * (((Nat.factorial (a+3) : ℚ) / (Nat.factorial a : ℚ)) *
        D (a+1) 2 (s+a+3)) ≤ ((1 : ℚ) / 5) * D (a+2) 2 s) :
    ((Nat.factorial (a+3) : ℚ)/(Nat.factorial (a-1) : ℚ))*D a 3 (s+a+3) < D (a+1) 3 s := by
  have hden : D (a+2) 2 s ≤ D (a+1) 3 s := by
    simpa using D_three_ge_zero_term (a+1) s
  have hzero' : (a : ℚ) * (((Nat.factorial (a+3) : ℚ) / (Nat.factorial a : ℚ)) *
        D (a+1) 2 (s+a+3)) ≤ ((1 : ℚ) / 5) * D (a+1) 3 s := by
    exact le_trans hzero (mul_le_mul_of_nonneg_left hden (by norm_num))
  exact G_l_three_of_zero_extra_one_fifth a s ha hzero'

lemma G_l_three (a s : Nat) (ha : 1 <= a) :
    ((Nat.factorial (a+3) : ℚ)/(Nat.factorial (a-1) : ℚ))*D a 3 (s+a+3) < D (a+1) 3 s := by
  exact G_l_three_of_zero_extra_l_three_le_one_fifth a s ha (zero_extra_l_three_le_one_fifth a s ha)




/-- The zero-first-coordinate slice gives a general monotone-in-dimension lower bound.
This is often the cleanest way to reduce the desired `D 2 l s` target to the
same dimension as the zero-extra term. -/
lemma D_ge_zero_tail_general (a m N : ℕ) :
    D (a+1) m N ≤ D a (m+1) N := by
  classical
  rw [← D_zero_part_general_succ a m N]
  unfold D
  exact Finset.sum_le_sum_of_subset_of_nonneg (by intro x hx; exact (Finset.mem_filter.mp hx).1)
    (by intro x hx hnot; exact weight_nonneg a (m+1) x)

/-- A useful reduction: it suffices to prove the zero-extra estimate against
`D 3 (l-1) s`; the actual denominator `D 2 l s` is larger by the zero-slice
embedding. -/
lemma zero_bound_one_third_from_D3_tail
    (l s : ℕ) (hl : 0 < l)
    (hD3 : (Nat.factorial (l+1) : ℚ) * D 2 (l-1) (s+l+1) ≤
      ((1 : ℚ) / 3) * D 3 (l-1) s) :
    (Nat.factorial (l+1) : ℚ) * D 2 (l-1) (s+l+1) ≤
      ((1 : ℚ) / 3) * D 2 l s := by
  cases l with
  | zero => omega
  | succ m =>
      have htail : D 3 m s ≤ D 2 (m+1) s := by
        simpa using D_ge_zero_tail_general 2 m s
      exact le_trans hD3 (mul_le_mul_of_nonneg_left htail (by norm_num))

lemma one_third_lt_sharp_slack (l : ℕ) (hl : 1 < l) :
    (1 : ℚ) / 3 < (2 : ℚ) / 3 - (1 : ℚ) / (l+2 : ℕ) := by
  have hden : (3 : ℚ) < (l + 2 : ℕ) := by exact_mod_cast (by omega : 3 < l + 2)
  have hinv : (1 : ℚ) / (l+2 : ℕ) < (1 : ℚ) / 3 := by
    exact one_div_lt_one_div_of_lt (by norm_num) hden
  linarith

/-- Conditional all-`l` sharp split with the concrete constant `1/3`, reduced
to the same-dimension `D3` zero-extra inequality. -/
lemma D_one_split_sharp_of_D3_zero_extra
    (l s : ℕ) (hl : 1 < l)
    (hD3 : (Nat.factorial (l+1) : ℚ) * D 2 (l-1) (s+l+1) ≤
      ((1 : ℚ) / 3) * D 3 (l-1) s) :
    (Nat.factorial (l+1) : ℚ) * D 1 l (s+l+1) < D 2 l s := by
  have hlpos : 0 < l := by omega
  exact D_one_split_sharp_conditional_of_K l s ((1 : ℚ) / 3) hlpos
    (zero_bound_one_third_from_D3_tail l s hlpos hD3)
    (one_third_lt_sharp_slack l hl)


/-- The `l = 1` endpoint of the sharp split is elementary and does not use the
`K < 2/3 - 1/(l+2)` conditional (which has no strict slack at `l=1`). -/
lemma D_one_split_sharp_l_one (s : ℕ) :
    (Nat.factorial (1+1) : ℚ) * D 1 1 (s+1+1) < D 2 1 s := by
  have hsplit : (Nat.factorial (1+1) : ℚ) * D 1 1 (s+1+1) = D 2 1 (s+1) := by
    calc
      (Nat.factorial (1+1) : ℚ) * D 1 1 (s+1+1)
          = D 2 1 (s+1) + (Nat.factorial (1+1) : ℚ) * D 2 (1-1) (s+1+1) :=
            D_one_split 1 s
      _ = D 2 1 (s+1) := by
        have hz : D 2 (1-1) (s+1+1) = 0 := by
          simpa using D_zero_of_pos (a := 2) (N := s+1+1) (by omega)
        rw [hz]
        ring
  rw [hsplit]
  have hstep : D 2 1 (s+1) ≤ ((1 : ℚ) / 3 + (1 : ℚ) / (1+2 : ℕ)) * D 2 1 s := by
    simpa using D_one_step_bound_sharp_a2 1 s
  have hcoef : ((1 : ℚ) / 3 + (1 : ℚ) / (1+2 : ℕ)) < 1 := by norm_num
  have hpos : 0 < D 2 1 s := D_pos 2 1 s (by decide)
  exact lt_of_le_of_lt hstep (by simpa using mul_lt_mul_of_pos_right hcoef hpos)



private lemma tuple_0002_mem_support_4_2 : (![0,0,0,2] : Fin 4 → ℕ) ∈ support 4 2 := by
  rw [support]
  simp only [Finset.mem_filter]
  refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_four]

private lemma tuple_0011_mem_support_4_2 : (![0,0,1,1] : Fin 4 → ℕ) ∈ support 4 2 := by
  rw [support]
  simp only [Finset.mem_filter]
  refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_four]


private lemma support_4_2_eq : support 4 2 = {(![0,0,0,2] : Fin 4 → ℕ), (![0,0,1,1] : Fin 4 → ℕ)} := by
  classical
  ext δ
  constructor
  · intro h
    rw [support] at h
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with ⟨hbox, hnd, hsum⟩
    norm_num [Fin.sum_univ_four] at hsum
    have h01 : δ 0 ≤ δ 1 := hnd 0 1 (by decide)
    have h12 : δ 1 ≤ δ 2 := hnd 1 2 (by decide)
    have h23 : δ 2 ≤ δ 3 := hnd 2 3 (by decide)
    have h0 : δ 0 = 0 := by omega
    have h1 : δ 1 = 0 := by omega
    have hsum' : δ 2 + δ 3 = 2 := by omega
    have h23' : δ 2 ≤ δ 3 := h23
    have h2cases : δ 2 = 0 ∨ δ 2 = 1 := by omega
    rcases h2cases with h2 | h2
    · left
      funext i
      fin_cases i <;> simp [h0, h1, h2] at hsum' ⊢ <;> omega
    · right
      funext i
      fin_cases i <;> simp [h0, h1, h2] at hsum' ⊢ <;> omega
  · intro h
    rw [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · exact tuple_0002_mem_support_4_2
    · exact tuple_0011_mem_support_4_2

lemma D_3_4_2_exact : D 3 4 2 = (1 : ℚ) / 24 := by
  classical
  rw [D, support_4_2_eq]
  simp [weight, Fin.prod_univ_four]
  norm_num


private lemma tuple_0004_mem_support_4_4 : (![0,0,0,4] : Fin 4 → ℕ) ∈ support 4 4 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_four]

private lemma tuple_0013_mem_support_4_4 : (![0,0,1,3] : Fin 4 → ℕ) ∈ support 4 4 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_four]

private lemma tuple_0022_mem_support_4_4 : (![0,0,2,2] : Fin 4 → ℕ) ∈ support 4 4 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_four]

private lemma tuple_0112_mem_support_4_4 : (![0,1,1,2] : Fin 4 → ℕ) ∈ support 4 4 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_four]

private lemma tuple_1111_mem_support_4_4 : (![1,1,1,1] : Fin 4 → ℕ) ∈ support 4 4 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_four]

private lemma support_4_4_eq : support 4 4 =
    {(![0,0,0,4] : Fin 4 → ℕ), (![0,0,1,3] : Fin 4 → ℕ), (![0,0,2,2] : Fin 4 → ℕ),
      (![0,1,1,2] : Fin 4 → ℕ), (![1,1,1,1] : Fin 4 → ℕ)} := by
  classical
  ext δ
  constructor
  · intro h
    rw [support] at h
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with ⟨hbox, hnd, hsum⟩
    norm_num [Fin.sum_univ_four] at hsum
    have h01 : δ 0 ≤ δ 1 := hnd 0 1 (by decide)
    have h12 : δ 1 ≤ δ 2 := hnd 1 2 (by decide)
    have h23 : δ 2 ≤ δ 3 := hnd 2 3 (by decide)
    have h0cases : δ 0 = 0 ∨ δ 0 = 1 := by omega
    rcases h0cases with h0 | h0
    · have h1cases : δ 1 = 0 ∨ δ 1 = 1 := by omega
      rcases h1cases with h1 | h1
      · have hsum' : δ 2 + δ 3 = 4 := by omega
        have h2cases : δ 2 = 0 ∨ δ 2 = 1 ∨ δ 2 = 2 := by omega
        rcases h2cases with h2 | h2 | h2
        · left
          funext i
          fin_cases i <;> simp [h0, h1, h2] at hsum' ⊢ <;> omega
        · right; left
          funext i
          fin_cases i <;> simp [h0, h1, h2] at hsum' ⊢ <;> omega
        · right; right; left
          funext i
          fin_cases i <;> simp [h0, h1, h2] at hsum' ⊢ <;> omega
      · right; right; right; left
        funext i
        fin_cases i <;> simp [h0, h1] at hsum h12 h23 ⊢ <;> omega
    · right; right; right; right
      funext i
      fin_cases i <;> simp [h0] at hsum h01 h12 h23 ⊢ <;> omega
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact tuple_0004_mem_support_4_4
    · exact tuple_0013_mem_support_4_4
    · exact tuple_0022_mem_support_4_4
    · exact tuple_0112_mem_support_4_4
    · exact tuple_1111_mem_support_4_4

lemma D_3_4_4_exact : D 3 4 4 = (29 : ℚ) / 10584 := by
  classical
  rw [D, support_4_4_eq]
  simp [weight, Fin.prod_univ_four]
  norm_num

lemma D_three_four_two_step_exception :
    D 3 4 (2+2) ≤ ((1:ℚ)/10) * D 3 4 2 := by
  rw [D_3_4_4_exact, D_3_4_2_exact]
  norm_num


/-- Lower the leftmost maximum twice.  This is the map underlying sharper
second-difference contraction estimates. -/
noncomputable def lowerLeftmostMaxTwice {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) : Fin l → ℕ :=
  lowerLeftmostMax hl (lowerLeftmostMax hl δ)

/-- The fiber of the two-step lowering map over a target of total `N`. -/
noncomputable def loweringTwiceFiber {l : ℕ} (hl : 0 < l) (N : ℕ) (η : Fin l → ℕ) :
    Finset (Fin l → ℕ) :=
  (support l (N + 2)).filter fun δ => lowerLeftmostMaxTwice hl δ = η

lemma lowerLeftmostMaxTwice_mem_support {l N : ℕ} (hl : 0 < l) {δ : Fin l → ℕ}
    (hδ : δ ∈ support l (N + 2)) : lowerLeftmostMaxTwice hl δ ∈ support l N := by
  unfold lowerLeftmostMaxTwice
  have h₁ : lowerLeftmostMax hl δ ∈ support l (N + 1) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (lowerLeftmostMax_mem_support (N := N + 1) hl (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hδ))
  exact lowerLeftmostMax_mem_support (N := N) hl h₁

lemma D_eq_sum_loweringTwiceFibers (a l N : ℕ) (hl : 0 < l) :
    D a l (N + 2) =
      ∑ η ∈ support l N, ∑ δ ∈ loweringTwiceFiber hl N η, weight a l δ := by
  classical
  unfold D loweringTwiceFiber
  rw [Finset.sum_fiberwise_of_maps_to]
  intro δ hδ
  exact lowerLeftmostMaxTwice_mem_support hl hδ

/-- A fallback two-step estimate obtained by iterating the existing sharp one-step
contraction.  It is not sharp enough for the final argument in small dimensions,
but is useful for large-dimension tails and for checking the two-step setup. -/
lemma D_two_step_bound_sharp_general_pos_l (a l N : ℕ) (hl : 0 < l) :
    D a l (N + 2) ≤
      (((1 : ℚ) / (a + 1 : ℕ) + (1 : ℚ) / (a + l : ℕ)) ^ 2) * D a l N := by
  let c : ℚ := (1 : ℚ) / (a + 1 : ℕ) + (1 : ℚ) / (a + l : ℕ)
  have h := iterated_contraction (D a l) c (by positivity)
    (fun n => by simpa [c] using D_one_step_bound_sharp_general_pos_l a l n hl) 2 N
  simpa [c, pow_two, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h


/-- Two-step candidate preimages: choose a one-step candidate `θ` above `η`,
then a one-step candidate `δ` above `θ`.  This is represented as the image of
candidate pairs, so repeated `δ`s are counted once in the finset. -/
noncomputable def twiceCandidatePreimages {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    Finset (Fin l → ℕ) :=
  ((candidatePreimages hl η).sigma (fun θ => candidatePreimages hl θ)).image
    (fun p => p.2)

/-- Legal two-step candidate preimages: choose legal one-step candidates in both
steps. -/
noncomputable def legalTwiceCandidatePreimages {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    Finset (Fin l → ℕ) :=
  ((legalCandidatePreimages hl η).sigma (fun θ => legalCandidatePreimages hl θ)).image
    (fun p => p.2)


lemma loweringTwiceFiber_subset_twiceCandidatePreimages {l N : ℕ} (hl : 0 < l)
    (η : Fin l → ℕ) :
    loweringTwiceFiber hl N η ⊆ twiceCandidatePreimages hl η := by
  classical
  intro δ hδ
  have hδsupp : δ ∈ support l (N + 2) := (Finset.mem_filter.mp hδ).1
  have htwice : lowerLeftmostMaxTwice hl δ = η := (Finset.mem_filter.mp hδ).2
  let θ : Fin l → ℕ := lowerLeftmostMax hl δ
  have hδsupp' : δ ∈ support l ((N + 1) + 1) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hδsupp
  have hθsupp : θ ∈ support l (N + 1) := by
    dsimp [θ]
    exact lowerLeftmostMax_mem_support (N := N + 1) hl hδsupp'
  have hθmap : lowerLeftmostMax hl θ = η := by
    dsimp [θ]
    simpa [lowerLeftmostMaxTwice] using htwice
  have hθfiber : θ ∈ loweringFiber hl N η := by
    simp [loweringFiber, hθsupp, hθmap]
  have hθcand : θ ∈ candidatePreimages hl η :=
    loweringFiber_subset_candidatePreimages (N := N) hl η hθfiber
  have hδfiber : δ ∈ loweringFiber hl (N + 1) θ := by
    simp [loweringFiber, hδsupp', θ]
  have hδcand : δ ∈ candidatePreimages hl θ :=
    loweringFiber_subset_candidatePreimages (N := N + 1) hl θ hδfiber
  unfold twiceCandidatePreimages
  refine Finset.mem_image.mpr ?_
  refine ⟨⟨θ, δ⟩, ?_, rfl⟩
  simpa using And.intro hθcand hδcand

lemma loweringTwiceFiber_subset_legalTwiceCandidatePreimages {l N : ℕ} (hl : 0 < l)
    (η : Fin l → ℕ) :
    loweringTwiceFiber hl N η ⊆ legalTwiceCandidatePreimages hl η := by
  classical
  intro δ hδ
  have hδsupp : δ ∈ support l (N + 2) := (Finset.mem_filter.mp hδ).1
  have htwice : lowerLeftmostMaxTwice hl δ = η := (Finset.mem_filter.mp hδ).2
  let θ : Fin l → ℕ := lowerLeftmostMax hl δ
  have hδsupp' : δ ∈ support l ((N + 1) + 1) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hδsupp
  have hθsupp : θ ∈ support l (N + 1) := by
    dsimp [θ]
    exact lowerLeftmostMax_mem_support (N := N + 1) hl hδsupp'
  have hθmap : lowerLeftmostMax hl θ = η := by
    dsimp [θ]
    simpa [lowerLeftmostMaxTwice] using htwice
  have hθfiber : θ ∈ loweringFiber hl N η := by
    simp [loweringFiber, hθsupp, hθmap]
  have hθcand : θ ∈ legalCandidatePreimages hl η :=
    loweringFiber_subset_legalCandidatePreimages (N := N) hl η hθfiber
  have hδfiber : δ ∈ loweringFiber hl (N + 1) θ := by
    simp [loweringFiber, hδsupp', θ]
  have hδcand : δ ∈ legalCandidatePreimages hl θ :=
    loweringFiber_subset_legalCandidatePreimages (N := N + 1) hl θ hδfiber
  unfold legalTwiceCandidatePreimages
  refine Finset.mem_image.mpr ?_
  refine ⟨⟨θ, δ⟩, ?_, rfl⟩
  simpa using And.intro hθcand hδcand


lemma loweringTwiceFiber_weight_sum_le_twiceCandidatePreimages_sum {l N : ℕ} (hl : 0 < l)
    (η : Fin l → ℕ) :
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤
      ∑ θ ∈ candidatePreimages hl η, ∑ δ ∈ candidatePreimages hl θ, weight 3 l δ := by
  classical
  have hsubset := loweringTwiceFiber_subset_twiceCandidatePreimages (N := N) hl η
  have hsubsum :
      (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤
        ∑ δ ∈ twiceCandidatePreimages hl η, weight 3 l δ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by intro x hx hnot; exact weight_nonneg 3 l x)
  have himage :
      (∑ δ ∈ twiceCandidatePreimages hl η, weight 3 l δ) ≤
        ∑ p ∈ (candidatePreimages hl η).sigma (fun θ => candidatePreimages hl θ),
          weight 3 l p.2 := by
    unfold twiceCandidatePreimages
    exact sum_image_le_sum
      (s := (candidatePreimages hl η).sigma (fun θ => candidatePreimages hl θ))
      (f := fun p => p.2) (g := weight 3 l) (weight_nonneg 3 l)
  have hsigma :
      (∑ p ∈ (candidatePreimages hl η).sigma (fun θ => candidatePreimages hl θ),
          weight 3 l p.2) =
        ∑ θ ∈ candidatePreimages hl η, ∑ δ ∈ candidatePreimages hl θ, weight 3 l δ := by
    exact Finset.sum_sigma (candidatePreimages hl η) (fun θ => candidatePreimages hl θ)
      (fun p => weight 3 l p.2)
  exact le_trans hsubsum (le_trans himage (le_of_eq hsigma))

lemma loweringTwiceFiber_weight_sum_le_legalTwiceCandidatePreimages_sum {l N : ℕ} (hl : 0 < l)
    (η : Fin l → ℕ) :
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤
      ∑ θ ∈ legalCandidatePreimages hl η, ∑ δ ∈ legalCandidatePreimages hl θ, weight 3 l δ := by
  classical
  have hsubset := loweringTwiceFiber_subset_legalTwiceCandidatePreimages (N := N) hl η
  have hsubsum :
      (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤
        ∑ δ ∈ legalTwiceCandidatePreimages hl η, weight 3 l δ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by intro x hx hnot; exact weight_nonneg 3 l x)
  have himage :
      (∑ δ ∈ legalTwiceCandidatePreimages hl η, weight 3 l δ) ≤
        ∑ p ∈ (legalCandidatePreimages hl η).sigma (fun θ => legalCandidatePreimages hl θ),
          weight 3 l p.2 := by
    unfold legalTwiceCandidatePreimages
    exact sum_image_le_sum
      (s := (legalCandidatePreimages hl η).sigma (fun θ => legalCandidatePreimages hl θ))
      (f := fun p => p.2) (g := weight 3 l) (weight_nonneg 3 l)
  have hsigma :
      (∑ p ∈ (legalCandidatePreimages hl η).sigma (fun θ => legalCandidatePreimages hl θ),
          weight 3 l p.2) =
        ∑ θ ∈ legalCandidatePreimages hl η, ∑ δ ∈ legalCandidatePreimages hl θ, weight 3 l δ := by
    exact Finset.sum_sigma (legalCandidatePreimages hl η) (fun θ => legalCandidatePreimages hl θ)
      (fun p => weight 3 l p.2)
  exact le_trans hsubsum (le_trans himage (le_of_eq hsigma))

lemma loweringTwiceFiber_weight_sum_le_legal_candidate_index_pairs {l N : ℕ} (hl : 0 < l)
    (η : Fin l → ℕ) :
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤
      ∑ k ∈ legalRaiseIndices hl η,
        ∑ j ∈ legalRaiseIndices hl (raiseAt η k),
          weight 3 l (raiseAt (raiseAt η k) j) := by
  classical
  calc
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ)
        ≤ ∑ θ ∈ legalCandidatePreimages hl η, ∑ δ ∈ legalCandidatePreimages hl θ, weight 3 l δ :=
          loweringTwiceFiber_weight_sum_le_legalTwiceCandidatePreimages_sum (N := N) hl η
    _ ≤ ∑ θ ∈ legalCandidatePreimages hl η,
          ∑ j ∈ legalRaiseIndices hl θ, weight 3 l (raiseAt θ j) := by
          exact Finset.sum_le_sum (by
            intro θ hθ
            exact sum_candidatePreimages_le_sum_indices θ (legalRaiseIndices hl θ))
    _ ≤ ∑ k ∈ legalRaiseIndices hl η,
          ∑ j ∈ legalRaiseIndices hl (raiseAt η k),
            weight 3 l (raiseAt (raiseAt η k) j) := by
          exact sum_image_le_sum
            (s := legalRaiseIndices hl η)
            (f := fun k => raiseAt η k)
            (g := fun θ => ∑ j ∈ legalRaiseIndices hl θ, weight 3 l (raiseAt θ j))
            (by
              intro θ
              exact Finset.sum_nonneg (by intro j hj; exact weight_nonneg 3 l (raiseAt θ j)))



/-- Lower the leftmost maximum three times.  This is the three-step analogue of
`lowerLeftmostMaxTwice` used for local legal-fiber estimates. -/
noncomputable def lowerLeftmostMaxThrice {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) : Fin l → ℕ :=
  lowerLeftmostMax hl (lowerLeftmostMaxTwice hl δ)

/-- The fiber of the three-step lowering map over a target of total `N`. -/
noncomputable def loweringThriceFiber {l : ℕ} (hl : 0 < l) (N : ℕ) (η : Fin l → ℕ) :
    Finset (Fin l → ℕ) :=
  (support l (N + 3)).filter fun δ => lowerLeftmostMaxThrice hl δ = η

lemma lowerLeftmostMaxThrice_mem_support {l N : ℕ} (hl : 0 < l) {δ : Fin l → ℕ}
    (hδ : δ ∈ support l (N + 3)) : lowerLeftmostMaxThrice hl δ ∈ support l N := by
  unfold lowerLeftmostMaxThrice
  have h₂ : lowerLeftmostMaxTwice hl δ ∈ support l (N + 1) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (lowerLeftmostMaxTwice_mem_support (N := N + 1) hl (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hδ))
  exact lowerLeftmostMax_mem_support (N := N) hl h₂

lemma D_eq_sum_loweringThriceFibers (a l N : ℕ) (hl : 0 < l) :
    D a l (N + 3) =
      ∑ η ∈ support l N, ∑ δ ∈ loweringThriceFiber hl N η, weight a l δ := by
  classical
  unfold D loweringThriceFiber
  rw [Finset.sum_fiberwise_of_maps_to]
  intro δ hδ
  exact lowerLeftmostMaxThrice_mem_support hl hδ

/-- Legal three-step candidate preimages: choose legal one-step candidates in three
successive raising steps.  The image removes duplicate final preimages. -/
noncomputable def legalThriceCandidatePreimages {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    Finset (Fin l → ℕ) :=
  ((legalCandidatePreimages hl η).sigma (fun ξ =>
    (legalCandidatePreimages hl ξ).sigma (fun θ => legalCandidatePreimages hl θ))).image
      (fun p => p.2.2)

lemma loweringThriceFiber_subset_legalThriceCandidatePreimages {l N : ℕ} (hl : 0 < l)
    (η : Fin l → ℕ) :
    loweringThriceFiber hl N η ⊆ legalThriceCandidatePreimages hl η := by
  classical
  intro δ hδ
  have hδsupp : δ ∈ support l (N + 3) := (Finset.mem_filter.mp hδ).1
  have hthrice : lowerLeftmostMaxThrice hl δ = η := (Finset.mem_filter.mp hδ).2
  let θ : Fin l → ℕ := lowerLeftmostMax hl δ
  let ξ : Fin l → ℕ := lowerLeftmostMaxTwice hl δ
  have hδsupp' : δ ∈ support l ((N + 2) + 1) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hδsupp
  have hθsupp : θ ∈ support l (N + 2) := by
    dsimp [θ]
    exact lowerLeftmostMax_mem_support (N := N + 2) hl hδsupp'
  have hθsupp' : θ ∈ support l ((N + 1) + 1) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hθsupp
  have hξ_eq : lowerLeftmostMax hl θ = ξ := by
    dsimp [θ, ξ, lowerLeftmostMaxTwice]
  have hξsupp : ξ ∈ support l (N + 1) := by
    dsimp [ξ]
    exact lowerLeftmostMaxTwice_mem_support (N := N + 1) hl (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hδsupp)
  have hξmap : lowerLeftmostMax hl ξ = η := by
    dsimp [ξ]
    simpa [lowerLeftmostMaxThrice] using hthrice
  have hξfiber : ξ ∈ loweringFiber hl N η := by
    simp [loweringFiber, hξsupp, hξmap]
  have hξcand : ξ ∈ legalCandidatePreimages hl η :=
    loweringFiber_subset_legalCandidatePreimages (N := N) hl η hξfiber
  have hθfiber : θ ∈ loweringFiber hl (N + 1) ξ := by
    simp [loweringFiber, hθsupp', hξ_eq]
  have hθcand : θ ∈ legalCandidatePreimages hl ξ :=
    loweringFiber_subset_legalCandidatePreimages (N := N + 1) hl ξ hθfiber
  have hδfiber : δ ∈ loweringFiber hl (N + 2) θ := by
    simp [loweringFiber, hδsupp', θ]
  have hδcand : δ ∈ legalCandidatePreimages hl θ :=
    loweringFiber_subset_legalCandidatePreimages (N := N + 2) hl θ hδfiber
  unfold legalThriceCandidatePreimages
  refine Finset.mem_image.mpr ?_
  refine ⟨⟨ξ, ⟨θ, δ⟩⟩, ?_, rfl⟩
  simpa using And.intro hξcand (And.intro hθcand hδcand)

lemma loweringThriceFiber_weight_sum_le_legalThriceCandidatePreimages_sum {l N : ℕ}
    (hl : 0 < l) (η : Fin l → ℕ) :
    (∑ δ ∈ loweringThriceFiber hl N η, weight 4 l δ) ≤
      ∑ ξ ∈ legalCandidatePreimages hl η,
        ∑ θ ∈ legalCandidatePreimages hl ξ,
          ∑ δ ∈ legalCandidatePreimages hl θ, weight 4 l δ := by
  classical
  have hsubset := loweringThriceFiber_subset_legalThriceCandidatePreimages (N := N) hl η
  have hsubsum :
      (∑ δ ∈ loweringThriceFiber hl N η, weight 4 l δ) ≤
        ∑ δ ∈ legalThriceCandidatePreimages hl η, weight 4 l δ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by intro x hx hnot; exact weight_nonneg 4 l x)
  have himage :
      (∑ δ ∈ legalThriceCandidatePreimages hl η, weight 4 l δ) ≤
        ∑ p ∈ (legalCandidatePreimages hl η).sigma (fun ξ =>
            (legalCandidatePreimages hl ξ).sigma (fun θ => legalCandidatePreimages hl θ)),
          weight 4 l p.2.2 := by
    unfold legalThriceCandidatePreimages
    exact sum_image_le_sum
      (s := (legalCandidatePreimages hl η).sigma (fun ξ =>
            (legalCandidatePreimages hl ξ).sigma (fun θ => legalCandidatePreimages hl θ)))
      (f := fun p => p.2.2) (g := weight 4 l) (weight_nonneg 4 l)
  have hsigma_inner :
      (∑ p ∈ (legalCandidatePreimages hl η).sigma (fun ξ =>
            (legalCandidatePreimages hl ξ).sigma (fun θ => legalCandidatePreimages hl θ)),
          weight 4 l p.2.2) =
        ∑ ξ ∈ legalCandidatePreimages hl η,
          ∑ q ∈ (legalCandidatePreimages hl ξ).sigma (fun θ => legalCandidatePreimages hl θ),
            weight 4 l q.2 := by
    exact Finset.sum_sigma (legalCandidatePreimages hl η)
      (fun ξ => (legalCandidatePreimages hl ξ).sigma (fun θ => legalCandidatePreimages hl θ))
      (fun p => weight 4 l p.2.2)
  have hsigma :
      (∑ ξ ∈ legalCandidatePreimages hl η,
          ∑ q ∈ (legalCandidatePreimages hl ξ).sigma (fun θ => legalCandidatePreimages hl θ),
            weight 4 l q.2) =
        ∑ ξ ∈ legalCandidatePreimages hl η,
          ∑ θ ∈ legalCandidatePreimages hl ξ,
            ∑ δ ∈ legalCandidatePreimages hl θ, weight 4 l δ := by
    exact Finset.sum_congr rfl (by
      intro ξ hξ
      exact Finset.sum_sigma (legalCandidatePreimages hl ξ) (fun θ => legalCandidatePreimages hl θ)
        (fun q => weight 4 l q.2))
  exact le_trans hsubsum (le_trans himage (le_of_eq (hsigma_inner.trans hsigma)))

lemma loweringThriceFiber_weight_sum_le_legal_candidate_index_triples {l N : ℕ}
    (hl : 0 < l) (η : Fin l → ℕ) :
    (∑ δ ∈ loweringThriceFiber hl N η, weight 4 l δ) ≤
      ∑ k ∈ legalRaiseIndices hl η,
        ∑ j ∈ legalRaiseIndices hl (raiseAt η k),
          ∑ i ∈ legalRaiseIndices hl (raiseAt (raiseAt η k) j),
            weight 4 l (raiseAt (raiseAt (raiseAt η k) j) i) := by
  classical
  calc
    (∑ δ ∈ loweringThriceFiber hl N η, weight 4 l δ)
        ≤ ∑ ξ ∈ legalCandidatePreimages hl η,
            ∑ θ ∈ legalCandidatePreimages hl ξ,
              ∑ δ ∈ legalCandidatePreimages hl θ, weight 4 l δ :=
          loweringThriceFiber_weight_sum_le_legalThriceCandidatePreimages_sum (N := N) hl η
    _ ≤ ∑ ξ ∈ legalCandidatePreimages hl η,
          ∑ θ ∈ legalCandidatePreimages hl ξ,
            ∑ i ∈ legalRaiseIndices hl θ, weight 4 l (raiseAt θ i) := by
          exact Finset.sum_le_sum (by
            intro ξ hξ
            exact Finset.sum_le_sum (by
              intro θ hθ
              exact sum_candidatePreimages_le_sum_indices θ (legalRaiseIndices hl θ)))
    _ ≤ ∑ ξ ∈ legalCandidatePreimages hl η,
          ∑ j ∈ legalRaiseIndices hl ξ,
            ∑ i ∈ legalRaiseIndices hl (raiseAt ξ j),
              weight 4 l (raiseAt (raiseAt ξ j) i) := by
          exact Finset.sum_le_sum (by
            intro ξ hξ
            exact sum_image_le_sum
              (s := legalRaiseIndices hl ξ)
              (f := fun j => raiseAt ξ j)
              (g := fun θ => ∑ i ∈ legalRaiseIndices hl θ, weight 4 l (raiseAt θ i))
              (by
                intro θ
                exact Finset.sum_nonneg (by intro i hi; exact weight_nonneg 4 l (raiseAt θ i))))
    _ ≤ ∑ k ∈ legalRaiseIndices hl η,
          ∑ j ∈ legalRaiseIndices hl (raiseAt η k),
            ∑ i ∈ legalRaiseIndices hl (raiseAt (raiseAt η k) j),
              weight 4 l (raiseAt (raiseAt (raiseAt η k) j) i) := by
          exact sum_image_le_sum
            (s := legalRaiseIndices hl η)
            (f := fun k => raiseAt η k)
            (g := fun ξ =>
              ∑ j ∈ legalRaiseIndices hl ξ,
                ∑ i ∈ legalRaiseIndices hl (raiseAt ξ j),
                  weight 4 l (raiseAt (raiseAt ξ j) i))
            (by
              intro ξ
              exact Finset.sum_nonneg (by
                intro j hj
                exact Finset.sum_nonneg (by intro i hi; exact weight_nonneg 4 l _)))


/-- If the local three-step fiber estimate is available for every fiber at level `N`,
then the global `D 4` three-step contraction follows.  This isolates the remaining
coefficient arithmetic from the fiber decomposition. -/
lemma D_four_three_step_contraction_l_ge_six_of_local_thrice_fiber_bound
    (l s : ℕ) (hl : 6 ≤ l)
    (hlocal : ∀ ⦃η : Fin l → ℕ⦄, η ∈ support l s →
      (∑ δ ∈ loweringThriceFiber (by omega : 0 < l) s η, weight 4 l δ) ≤
        ((1 : ℚ) / 75) * weight 4 l η) :
    D 4 l (s + 3) ≤ ((1 : ℚ) / 75) * D 4 l s := by
  classical
  have hlpos : 0 < l := by omega
  rw [D_eq_sum_loweringThriceFibers 4 l s hlpos]
  unfold D
  calc
    (∑ η ∈ support l s, ∑ δ ∈ loweringThriceFiber hlpos s η, weight 4 l δ)
        ≤ ∑ η ∈ support l s, ((1 : ℚ) / 75) * weight 4 l η := by
          exact Finset.sum_le_sum (by
            intro η hη
            simpa using hlocal hη)
    _ = ((1 : ℚ) / 75) * ∑ η ∈ support l s, weight 4 l η := by
          rw [Finset.mul_sum]





/-- One-step legal raise sums obey the same coarse sharp bound as corrected
candidate sums, since legal indices are a sub-finset of corrected candidate
indices.  This helper is used to get a compiled three-step `R`-first branch
estimate for the `a = 4`, `l ≥ 6` case. -/
lemma legalRaiseIndices_weight_sum_le_sharp_general {a l : ℕ} (hl : 0 < l)
    (η : Fin l → ℕ) :
    (∑ k ∈ legalRaiseIndices hl η, weight a l (raiseAt η k)) ≤
      (((1 : ℚ) / (a + 1 : ℕ) + (1 : ℚ) / (a + l : ℕ))) * weight a l η := by
  classical
  have hsubset : legalRaiseIndices hl η ⊆ correctedCandidateRaiseIndices hl η := by
    intro k hk
    exact (Finset.mem_filter.mp hk).1
  have hsubsum :
      (∑ k ∈ legalRaiseIndices hl η, weight a l (raiseAt η k)) ≤
        ∑ k ∈ correctedCandidateRaiseIndices hl η, weight a l (raiseAt η k) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by intro x hx hnot; exact weight_nonneg a l (raiseAt η x))
  have hlast_bound : weight a l (raiseAt η (lastFin l hl)) ≤
      (1 / ((a + l : ℕ) : ℚ)) * weight a l η := by
    have h := weight_raiseAt_le_index (a := a) η (lastFin l hl)
    have hden_nat : a + (lastFin l hl : ℕ) + 1 = a + l := by
      dsimp [lastFin]
      omega
    simpa [hden_nat] using h
  have hpred_each : ∀ k ∈ predecessorRaiseIndices hl η,
      weight a l (raiseAt η k) ≤ (1 / ((a + 1 : ℕ) : ℚ)) * weight a l η := by
    intro k hk
    simpa using (weight_raiseAt_le (a := a) η k)
  have hlast_notin : lastFin l hl ∉ predecessorRaiseIndices hl η := by
    simp [predecessorRaiseIndices, lastFin]
    intro hbad
    omega
  calc
    (∑ k ∈ legalRaiseIndices hl η, weight a l (raiseAt η k))
        ≤ ∑ k ∈ correctedCandidateRaiseIndices hl η, weight a l (raiseAt η k) := hsubsum
    _ = weight a l (raiseAt η (lastFin l hl)) +
        ∑ k ∈ predecessorRaiseIndices hl η, weight a l (raiseAt η k) := by
          unfold correctedCandidateRaiseIndices
          rw [Finset.sum_insert hlast_notin]
    _ ≤ (1 / ((a + l : ℕ) : ℚ)) * weight a l η +
        ∑ k ∈ predecessorRaiseIndices hl η, (1 / ((a + 1 : ℕ) : ℚ)) * weight a l η := by
          exact add_le_add hlast_bound (Finset.sum_le_sum hpred_each)
    _ ≤ (1 / ((a + l : ℕ) : ℚ)) * weight a l η +
        (1 / ((a + 1 : ℕ) : ℚ)) * weight a l η := by
          have hcard := card_predecessorRaiseIndices_le_one hl η
          have hcardQ : ((predecessorRaiseIndices hl η).card : ℚ) ≤ (1 : ℚ) := by exact_mod_cast hcard
          have hnon : 0 ≤ (1 / ((a + 1 : ℕ) : ℚ)) * weight a l η :=
            mul_nonneg (by positivity) (weight_nonneg a l η)
          rw [Finset.sum_const]
          simp
          exact mul_le_of_le_one_left (by simpa using hnon) hcardQ
    _ = (((1 : ℚ) / (a + 1 : ℕ) + (1 : ℚ) / (a + l : ℕ))) * weight a l η := by ring


/-- One-step legal raise sum after raising the last index, specialized to `a = 4`.
If `M` is the last value before the displayed last raise, the next legal raises
have denominators `M + l + 5` (raise last again) and `M + l + 3` (the unique
predecessor, if present). -/
lemma legalRaise_sum_after_raise_last_oneStep_a4 {l : ℕ} (hl : 0 < l)
    {η : Fin l → ℕ} (hnd : NondecreasingFin η) :
    let M : ℕ := η (lastFin l hl)
    ∑ j ∈ legalRaiseIndices hl (raiseAt η (lastFin l hl)),
        weight 4 l (raiseAt (raiseAt η (lastFin l hl)) j)
      ≤ ((1 / (((M + l + 5 : ℕ) : ℚ))) +
          (1 / (((M + l + 3 : ℕ) : ℚ)))) *
          weight 4 l (raiseAt η (lastFin l hl)) := by
  classical
  let last := lastFin l hl
  let M : ℕ := η last
  let δ : Fin l → ℕ := raiseAt η last
  have hδlast : δ last = M + 1 := by
    dsimp [δ, M, last]
    simp [raiseAt]
  have hleft : leftmostMax hl δ = last := by
    simpa [δ, last] using leftmostMax_raiseAt_last_of_nondecreasing hl hnd
  let P : Finset (Fin l) := (predecessorRaiseIndices hl δ).filter
    (fun k => k = lastFin l hl ∨ δ k + 1 = δ (lastFin l hl))
  have hlast_notin_pred : lastFin l hl ∉ predecessorRaiseIndices hl δ := by
    simp [predecessorRaiseIndices, lastFin]
    intro hbad
    omega
  have hlegal_eq : legalRaiseIndices hl δ = insert (lastFin l hl) P := by
    ext k
    by_cases hk : k = lastFin l hl
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, P, hk]
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, P, hk]
  have hlast_bound : weight 4 l (raiseAt δ (lastFin l hl)) ≤
      (1 / (((M + l + 5 : ℕ) : ℚ))) * weight 4 l δ := by
    have h := weight_raiseAt_eq_inv (a := 4) δ (lastFin l hl)
    have hden : 4 + (lastFin l hl : ℕ) + δ (lastFin l hl) + 1 = M + l + 5 := by
      have hδlast' : δ (lastFin l hl) = M + 1 := by simpa [last] using hδlast
      rw [hδlast']
      dsimp [lastFin]
      omega
    rw [h]
    exact le_of_eq (by simp [hden])
  have hpred_each : ∀ k ∈ P,
      weight 4 l (raiseAt δ k) ≤
        (1 / (((M + l + 3 : ℕ) : ℚ))) * weight 4 l δ := by
    intro k hkP
    have hkpred : k ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hkP).1
    have hkcond : k = lastFin l hl ∨ δ k + 1 = δ (lastFin l hl) :=
      (Finset.mem_filter.mp hkP).2
    have hk_ne_last : k ≠ lastFin l hl := by
      intro hkl
      exact hlast_notin_pred (by simpa [hkl] using hkpred)
    have hδk : δ k = M := by
      cases hkcond with
      | inl hkl => exact False.elim (hk_ne_last hkl)
      | inr hval =>
          rw [hδlast] at hval
          omega
    have hk_succ_last : (k : ℕ) + 1 = (lastFin l hl : ℕ) := by
      rw [predecessorRaiseIndices] at hkpred
      rcases (Finset.mem_filter.mp hkpred).2 with ⟨hklt, hkeq⟩
      have hv : lastFin l hl = (⟨(k : ℕ) + 1, hklt⟩ : Fin l) := by
        simpa [hleft] using hkeq
      exact (congrArg Fin.val hv).symm
    have h := weight_raiseAt_eq_inv (a := 4) δ k
    have hden : 4 + (k : ℕ) + δ k + 1 = M + l + 3 := by
      dsimp [lastFin] at hk_succ_last
      omega
    rw [h]
    exact le_of_eq (by simp [hden])
  have hP_card : P.card ≤ 1 := by
    exact le_trans (Finset.card_filter_le _ _) (card_predecessorRaiseIndices_le_one hl δ)
  have hP_cardQ : (P.card : ℚ) ≤ (1 : ℚ) := by exact_mod_cast hP_card
  have hpred_nonneg : 0 ≤ (1 / (((M + l + 3 : ℕ) : ℚ))) * weight 4 l δ :=
    mul_nonneg (by positivity) (weight_nonneg 4 l δ)
  have hsum_delta :
      (∑ j ∈ legalRaiseIndices hl δ, weight 4 l (raiseAt δ j)) ≤
        (1 / (((M + l + 5 : ℕ) : ℚ))) * weight 4 l δ +
          (1 / (((M + l + 3 : ℕ) : ℚ))) * weight 4 l δ := by
    calc
      (∑ j ∈ legalRaiseIndices hl δ, weight 4 l (raiseAt δ j))
          = ∑ j ∈ insert (lastFin l hl) P, weight 4 l (raiseAt δ j) := by rw [hlegal_eq]
      _ = weight 4 l (raiseAt δ (lastFin l hl)) + ∑ j ∈ P, weight 4 l (raiseAt δ j) := by
        rw [Finset.sum_insert]
        intro hmem
        have : lastFin l hl ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hmem).1
        exact hlast_notin_pred this
      _ ≤ (1 / (((M + l + 5 : ℕ) : ℚ))) * weight 4 l δ +
            ∑ j ∈ P, (1 / (((M + l + 3 : ℕ) : ℚ))) * weight 4 l δ := by
        exact add_le_add hlast_bound (Finset.sum_le_sum hpred_each)
      _ ≤ (1 / (((M + l + 5 : ℕ) : ℚ))) * weight 4 l δ +
            (1 / (((M + l + 3 : ℕ) : ℚ))) * weight 4 l δ := by
        rw [Finset.sum_const]
        simp
        exact mul_le_of_le_one_left (by simpa using hpred_nonneg) hP_cardQ
  dsimp [M, last, δ] at hsum_delta ⊢
  convert hsum_delta using 1
  ring

/-- One-step legal raise sum after a legal non-last raise, specialized to `a = 4`.
If `M` is the last value before the displayed non-last raise, the next legal
raises have denominators `M + l + 4` (last) and `M + k + 3` (the predecessor of
`k`, if present). -/
lemma legalRaise_sum_after_raise_nonlast_oneStep_a4 {l : ℕ} (hl : 0 < l)
    {η : Fin l → ℕ} (hnd : NondecreasingFin η) {k : Fin l}
    (hklegal : k ∈ legalRaiseIndices hl η) (hk_ne_last : k ≠ lastFin l hl) :
    let M : ℕ := η (lastFin l hl)
    ∑ j ∈ legalRaiseIndices hl (raiseAt η k),
        weight 4 l (raiseAt (raiseAt η k) j)
      ≤ ((1 / (((M + l + 4 : ℕ) : ℚ))) +
          (1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ)))) *
          weight 4 l (raiseAt η k) := by
  classical
  let last := lastFin l hl
  let M : ℕ := η last
  let δ : Fin l → ℕ := raiseAt η k
  have hδlast : δ last = M := by
    dsimp [δ, M, last]
    by_cases h : lastFin l hl = k
    · exact False.elim (hk_ne_last h.symm)
    · simp [raiseAt, h]
  have hk_mem_corr : k ∈ correctedCandidateRaiseIndices hl η :=
    (Finset.mem_filter.mp hklegal).1
  have hk_cond : k = lastFin l hl ∨ η k + 1 = η (lastFin l hl) :=
    (Finset.mem_filter.mp hklegal).2
  have hηk_succ : η k + 1 = M := by
    cases hk_cond with
    | inl hkl => exact False.elim (hk_ne_last hkl)
    | inr hval => simpa [M, last] using hval
  have hδk : δ k = M := by
    dsimp [δ]
    simp [raiseAt, hηk_succ]
  have hk_mem_pred : k ∈ predecessorRaiseIndices hl η := by
    rw [correctedCandidateRaiseIndices] at hk_mem_corr
    exact (Finset.mem_insert.mp hk_mem_corr).resolve_left hk_ne_last
  have hk_succ_lt : (k : ℕ) + 1 < l := by
    rw [predecessorRaiseIndices] at hk_mem_pred
    exact (Finset.mem_filter.mp hk_mem_pred).2.1
  let ksucc : Fin l := ⟨(k : ℕ) + 1, hk_succ_lt⟩
  have hleft_eta : leftmostMax hl η = ksucc := by
    rw [predecessorRaiseIndices] at hk_mem_pred
    exact (Finset.mem_filter.mp hk_mem_pred).2.2
  have hη_ksucc : η ksucc = M := by
    calc
      η ksucc = η (leftmostMax hl η) := by rw [hleft_eta]
      _ = η (lastFin l hl) := leftmostMax_value hl η
      _ = M := by simp [M, last]
  have hleft : leftmostMax hl δ = k := by
    apply Fin.ext
    have hle_k : (leftmostMax hl δ : ℕ) ≤ (k : ℕ) := by
      apply leftmostMax_le_of_value hl δ
      rw [hδk, hδlast]
    by_contra hne_val
    have hlt_k : (leftmostMax hl δ : ℕ) < (k : ℕ) := by omega
    have hlt_lm_eta : (leftmostMax hl δ : ℕ) < (leftmostMax hl η : ℕ) := by
      rw [hleft_eta]
      simp [ksucc]
      omega
    have hlm_ne_k : leftmostMax hl δ ≠ k := by
      intro h
      exact hne_val (congrArg Fin.val h)
    have hδ_lm : δ (leftmostMax hl δ) = η (leftmostMax hl δ) := by
      dsimp [δ]
      by_cases h : leftmostMax hl (raiseAt η k) = k
      · exact False.elim (hlm_ne_k h)
      · simp [raiseAt, h]
    have hlt_val : η (leftmostMax hl δ) < M := by
      have h := value_lt_leftmostMax hl hnd hlt_lm_eta
      simpa [hη_ksucc, hleft_eta] using h
    have hδ_lm_eq_M : δ (leftmostMax hl δ) = M := by
      calc
        δ (leftmostMax hl δ) = δ (lastFin l hl) := leftmostMax_value hl δ
        _ = M := hδlast
    rw [hδ_lm] at hδ_lm_eq_M
    omega
  let P : Finset (Fin l) := (predecessorRaiseIndices hl δ).filter
    (fun j => j = lastFin l hl ∨ δ j + 1 = δ (lastFin l hl))
  have hlast_notin_pred : lastFin l hl ∉ predecessorRaiseIndices hl δ := by
    simp [predecessorRaiseIndices, lastFin]
    intro hbad
    omega
  have hlegal_eq : legalRaiseIndices hl δ = insert (lastFin l hl) P := by
    ext j
    by_cases hj : j = lastFin l hl
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, P, hj]
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, P, hj]
  have hlast_bound : weight 4 l (raiseAt δ (lastFin l hl)) ≤
      (1 / (((M + l + 4 : ℕ) : ℚ))) * weight 4 l δ := by
    have h := weight_raiseAt_eq_inv (a := 4) δ (lastFin l hl)
    have hden : 4 + (lastFin l hl : ℕ) + δ (lastFin l hl) + 1 = M + l + 4 := by
      have hδlast' : δ (lastFin l hl) = M := by simpa [last] using hδlast
      rw [hδlast']
      dsimp [lastFin]
      omega
    rw [h]
    exact le_of_eq (by simp [hden])
  have hpred_each : ∀ j ∈ P,
      weight 4 l (raiseAt δ j) ≤
        (1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * weight 4 l δ := by
    intro j hjP
    have hjpred : j ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hjP).1
    have hjcond : j = lastFin l hl ∨ δ j + 1 = δ (lastFin l hl) :=
      (Finset.mem_filter.mp hjP).2
    have hj_ne_last : j ≠ lastFin l hl := by
      intro hjl
      exact hlast_notin_pred (by simpa [hjl] using hjpred)
    have hδj_succ : δ j + 1 = M := by
      cases hjcond with
      | inl hjl => exact False.elim (hj_ne_last hjl)
      | inr hval =>
          have hδlast' : δ (lastFin l hl) = M := by simpa [last] using hδlast
          simpa [hδlast'] using hval
    have hj_succ_k : (j : ℕ) + 1 = (k : ℕ) := by
      rw [predecessorRaiseIndices] at hjpred
      rcases (Finset.mem_filter.mp hjpred).2 with ⟨hjlt, hjeq⟩
      have hv : k = (⟨(j : ℕ) + 1, hjlt⟩ : Fin l) := by
        simpa [hleft] using hjeq
      exact (congrArg Fin.val hv).symm
    have h := weight_raiseAt_eq_inv (a := 4) δ j
    have hden : 4 + (j : ℕ) + δ j + 1 = M + (k : ℕ) + 3 := by
      omega
    rw [h]
    exact le_of_eq (by simp [hden])
  have hP_card : P.card ≤ 1 := by
    exact le_trans (Finset.card_filter_le _ _) (card_predecessorRaiseIndices_le_one hl δ)
  have hP_cardQ : (P.card : ℚ) ≤ (1 : ℚ) := by exact_mod_cast hP_card
  have hpred_nonneg : 0 ≤ (1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * weight 4 l δ :=
    mul_nonneg (by positivity) (weight_nonneg 4 l δ)
  have hsum_delta :
      (∑ j ∈ legalRaiseIndices hl δ, weight 4 l (raiseAt δ j)) ≤
        (1 / (((M + l + 4 : ℕ) : ℚ))) * weight 4 l δ +
          (1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * weight 4 l δ := by
    calc
      (∑ j ∈ legalRaiseIndices hl δ, weight 4 l (raiseAt δ j))
          = ∑ j ∈ insert (lastFin l hl) P, weight 4 l (raiseAt δ j) := by rw [hlegal_eq]
      _ = weight 4 l (raiseAt δ (lastFin l hl)) + ∑ j ∈ P, weight 4 l (raiseAt δ j) := by
        rw [Finset.sum_insert]
        intro hmem
        have : lastFin l hl ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hmem).1
        exact hlast_notin_pred this
      _ ≤ (1 / (((M + l + 4 : ℕ) : ℚ))) * weight 4 l δ +
            ∑ j ∈ P, (1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * weight 4 l δ := by
        exact add_le_add hlast_bound (Finset.sum_le_sum hpred_each)
      _ ≤ (1 / (((M + l + 4 : ℕ) : ℚ))) * weight 4 l δ +
            (1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * weight 4 l δ := by
        rw [Finset.sum_const]
        simp
        exact mul_le_of_le_one_left (by simpa using hpred_nonneg) hP_cardQ
  dsimp [M, last, δ] at hsum_delta ⊢
  convert hsum_delta using 1
  ring


/-- Sharpened one-step `a = 4` branch for a boundary non-last raise `k = 0`:
after raising `k`, the new leftmost maximum is at `0`, so there is no predecessor
branch and the next legal raise can only be the last index. -/
lemma legalRaise_sum_after_raise_nonlast_k_zero_oneStep_a4 {l : ℕ} (hl : 0 < l)
    {η : Fin l → ℕ} (hnd : NondecreasingFin η) {k : Fin l}
    (hklegal : k ∈ legalRaiseIndices hl η) (hk_ne_last : k ≠ lastFin l hl)
    (hk_zero : (k : ℕ) = 0) :
    let M : ℕ := η (lastFin l hl)
    ∑ j ∈ legalRaiseIndices hl (raiseAt η k),
        weight 4 l (raiseAt (raiseAt η k) j)
      ≤ (1 / (((M + l + 4 : ℕ) : ℚ))) * weight 4 l (raiseAt η k) := by
  classical
  let last := lastFin l hl
  let M : ℕ := η last
  let δ : Fin l → ℕ := raiseAt η k
  have hδlast : δ last = M := by
    dsimp [δ, M, last]
    by_cases h : lastFin l hl = k
    · exact False.elim (hk_ne_last h.symm)
    · simp [raiseAt, h]
  have hk_mem_corr : k ∈ correctedCandidateRaiseIndices hl η :=
    (Finset.mem_filter.mp hklegal).1
  have hk_cond : k = lastFin l hl ∨ η k + 1 = η (lastFin l hl) :=
    (Finset.mem_filter.mp hklegal).2
  have hηk_succ : η k + 1 = M := by
    cases hk_cond with
    | inl hkl => exact False.elim (hk_ne_last hkl)
    | inr hval => simpa [M, last] using hval
  have hδk : δ k = M := by
    dsimp [δ]
    simp [raiseAt, hηk_succ]
  have hk_mem_pred : k ∈ predecessorRaiseIndices hl η := by
    rw [correctedCandidateRaiseIndices] at hk_mem_corr
    exact (Finset.mem_insert.mp hk_mem_corr).resolve_left hk_ne_last
  have hk_succ_lt : (k : ℕ) + 1 < l := by
    rw [predecessorRaiseIndices] at hk_mem_pred
    exact (Finset.mem_filter.mp hk_mem_pred).2.1
  let ksucc : Fin l := ⟨(k : ℕ) + 1, hk_succ_lt⟩
  have hleft_eta : leftmostMax hl η = ksucc := by
    rw [predecessorRaiseIndices] at hk_mem_pred
    exact (Finset.mem_filter.mp hk_mem_pred).2.2
  have hη_ksucc : η ksucc = M := by
    calc
      η ksucc = η (leftmostMax hl η) := by rw [hleft_eta]
      _ = η (lastFin l hl) := leftmostMax_value hl η
      _ = M := by simp [M, last]
  have hleft : leftmostMax hl δ = k := by
    apply Fin.ext
    have hle_k : (leftmostMax hl δ : ℕ) ≤ (k : ℕ) := by
      apply leftmostMax_le_of_value hl δ
      rw [hδk, hδlast]
    by_contra hne_val
    have hlt_k : (leftmostMax hl δ : ℕ) < (k : ℕ) := by omega
    have hlt_lm_eta : (leftmostMax hl δ : ℕ) < (leftmostMax hl η : ℕ) := by
      rw [hleft_eta]
      simp [ksucc]
      omega
    have hlm_ne_k : leftmostMax hl δ ≠ k := by
      intro h
      exact hne_val (congrArg Fin.val h)
    have hδ_lm : δ (leftmostMax hl δ) = η (leftmostMax hl δ) := by
      dsimp [δ]
      by_cases h : leftmostMax hl (raiseAt η k) = k
      · exact False.elim (hlm_ne_k h)
      · simp [raiseAt, h]
    have hlt_val : η (leftmostMax hl δ) < M := by
      have h := value_lt_leftmostMax hl hnd hlt_lm_eta
      simpa [hη_ksucc, hleft_eta] using h
    have hδ_lm_eq_M : δ (leftmostMax hl δ) = M := by
      calc
        δ (leftmostMax hl δ) = δ (lastFin l hl) := leftmostMax_value hl δ
        _ = M := hδlast
    rw [hδ_lm] at hδ_lm_eq_M
    omega
  let P : Finset (Fin l) := (predecessorRaiseIndices hl δ).filter
    (fun j => j = lastFin l hl ∨ δ j + 1 = δ (lastFin l hl))
  have hlast_notin_pred : lastFin l hl ∉ predecessorRaiseIndices hl δ := by
    simp [predecessorRaiseIndices, lastFin]
    intro hbad
    omega
  have hlegal_eq : legalRaiseIndices hl δ = insert (lastFin l hl) P := by
    ext j
    by_cases hj : j = lastFin l hl
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, P, hj]
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, P, hj]
  have hP_empty : P = ∅ := by
    ext j
    simp
    intro hjP
    have hjpred : j ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hjP).1
    rw [predecessorRaiseIndices] at hjpred
    rcases (Finset.mem_filter.mp hjpred).2 with ⟨hjlt, hjeq⟩
    have hj_succ_k : (j : ℕ) + 1 = (k : ℕ) := by
      have hv : k = (⟨(j : ℕ) + 1, hjlt⟩ : Fin l) := by
        simpa [hleft] using hjeq
      exact (congrArg Fin.val hv).symm
    omega
  have hlast_bound : weight 4 l (raiseAt δ (lastFin l hl)) ≤
      (1 / (((M + l + 4 : ℕ) : ℚ))) * weight 4 l δ := by
    have h := weight_raiseAt_eq_inv (a := 4) δ (lastFin l hl)
    have hden : 4 + (lastFin l hl : ℕ) + δ (lastFin l hl) + 1 = M + l + 4 := by
      have hδlast' : δ (lastFin l hl) = M := by simpa [last] using hδlast
      rw [hδlast']
      dsimp [lastFin]
      omega
    rw [h]
    exact le_of_eq (by simp [hden])
  have hsum_delta :
      (∑ j ∈ legalRaiseIndices hl δ, weight 4 l (raiseAt δ j)) ≤
        (1 / (((M + l + 4 : ℕ) : ℚ))) * weight 4 l δ := by
    calc
      (∑ j ∈ legalRaiseIndices hl δ, weight 4 l (raiseAt δ j))
          = ∑ j ∈ insert (lastFin l hl) P, weight 4 l (raiseAt δ j) := by rw [hlegal_eq]
      _ = weight 4 l (raiseAt δ (lastFin l hl)) + ∑ j ∈ P, weight 4 l (raiseAt δ j) := by
        rw [Finset.sum_insert]
        intro hmem
        have : lastFin l hl ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hmem).1
        exact hlast_notin_pred this
      _ = weight 4 l (raiseAt δ (lastFin l hl)) := by
        rw [hP_empty]
        simp
      _ ≤ (1 / (((M + l + 4 : ℕ) : ℚ))) * weight 4 l δ := hlast_bound
  dsimp [M, last, δ] at hsum_delta ⊢
  simpa using hsum_delta

lemma triple_R_first_coeff_le_1_250 {M l : ℕ} (hM : 1 ≤ M) (hl6 : 6 ≤ l) :
    (1 / (((M + l + 4 : ℕ) : ℚ))) *
      ((1 / (((M + l + 5 : ℕ) : ℚ))) *
          (1 / (((M + l + 6 : ℕ) : ℚ)) + 1 / (((M + l + 4 : ℕ) : ℚ))) +
        (1 / (((M + l + 3 : ℕ) : ℚ))) *
          (1 / (((M + l + 5 : ℕ) : ℚ)) + 1 / (((M + l + 2 : ℕ) : ℚ))))
      ≤ (1 : ℚ) / 250 := by
  have hx4 : (11 : ℚ) ≤ ((M + l + 4 : ℕ) : ℚ) := by exact_mod_cast (by omega : 11 ≤ M + l + 4)
  have hx5 : (12 : ℚ) ≤ ((M + l + 5 : ℕ) : ℚ) := by exact_mod_cast (by omega : 12 ≤ M + l + 5)
  have hx6 : (13 : ℚ) ≤ ((M + l + 6 : ℕ) : ℚ) := by exact_mod_cast (by omega : 13 ≤ M + l + 6)
  have hx3 : (10 : ℚ) ≤ ((M + l + 3 : ℕ) : ℚ) := by exact_mod_cast (by omega : 10 ≤ M + l + 3)
  have hx2 : (9 : ℚ) ≤ ((M + l + 2 : ℕ) : ℚ) := by exact_mod_cast (by omega : 9 ≤ M + l + 2)
  have hi4 : (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) ≤ 1 / 11 := one_div_le_one_div_of_le (by norm_num) hx4
  have hi5 : (1 : ℚ) / ((M + l + 5 : ℕ) : ℚ) ≤ 1 / 12 := one_div_le_one_div_of_le (by norm_num) hx5
  have hi6 : (1 : ℚ) / ((M + l + 6 : ℕ) : ℚ) ≤ 1 / 13 := one_div_le_one_div_of_le (by norm_num) hx6
  have hi3 : (1 : ℚ) / ((M + l + 3 : ℕ) : ℚ) ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hx3
  have hi2 : (1 : ℚ) / ((M + l + 2 : ℕ) : ℚ) ≤ 1 / 9 := one_div_le_one_div_of_le (by norm_num) hx2
  have hsumR : (1 : ℚ) / ((M + l + 6 : ℕ) : ℚ) + 1 / ((M + l + 4 : ℕ) : ℚ) ≤ 1 / 13 + 1 / 11 :=
    add_le_add hi6 hi4
  have hsumL : (1 : ℚ) / ((M + l + 5 : ℕ) : ℚ) + 1 / ((M + l + 2 : ℕ) : ℚ) ≤ 1 / 12 + 1 / 9 :=
    add_le_add hi5 hi2
  have hRR : (1 : ℚ) / ((M + l + 5 : ℕ) : ℚ) *
      (1 / ((M + l + 6 : ℕ) : ℚ) + 1 / ((M + l + 4 : ℕ) : ℚ)) ≤
      (1 / 12) * (1 / 13 + 1 / 11) :=
    mul_le_mul hi5 hsumR (by positivity) (by norm_num)
  have hRL : (1 : ℚ) / ((M + l + 3 : ℕ) : ℚ) *
      (1 / ((M + l + 5 : ℕ) : ℚ) + 1 / ((M + l + 2 : ℕ) : ℚ)) ≤
      (1 / 10) * (1 / 12 + 1 / 9) :=
    mul_le_mul hi3 hsumL (by positivity) (by norm_num)
  have hbr : (1 : ℚ) / ((M + l + 5 : ℕ) : ℚ) *
          (1 / ((M + l + 6 : ℕ) : ℚ) + 1 / ((M + l + 4 : ℕ) : ℚ)) +
        (1 / ((M + l + 3 : ℕ) : ℚ)) *
          (1 / ((M + l + 5 : ℕ) : ℚ) + 1 / ((M + l + 2 : ℕ) : ℚ)) ≤
      (1 / 12) * (1 / 13 + 1 / 11) + (1 / 10) * (1 / 12 + 1 / 9) :=
    add_le_add hRR hRL
  have hmul := mul_le_mul hi4 hbr (by positivity)
    (by norm_num : (0 : ℚ) ≤ (1 : ℚ) / 11)
  calc
    (1 / (((M + l + 4 : ℕ) : ℚ))) *
      ((1 / (((M + l + 5 : ℕ) : ℚ))) *
          (1 / (((M + l + 6 : ℕ) : ℚ)) + 1 / (((M + l + 4 : ℕ) : ℚ))) +
        (1 / (((M + l + 3 : ℕ) : ℚ))) *
          (1 / (((M + l + 5 : ℕ) : ℚ)) + 1 / (((M + l + 2 : ℕ) : ℚ))))
        ≤ (1 / 11) * ((1 / 12) * (1 / 13 + 1 / 11) + (1 / 10) * (1 / 12 + 1 / 9)) := hmul
    _ ≤ (1 : ℚ) / 250 := by norm_num

/-- Sharper compiled `R`-first triple branch under positive last value.  The
coefficient `1/250` is strong enough to combine with the existing `43/4620`
`L`-branch bound. -/
lemma legalRaise_triple_sum_first_last_a4_l_ge_six_hMpos {l N : ℕ} (hl6 : 6 ≤ l)
    {η : Fin l → ℕ} (hη : η ∈ support l N)
    (hMpos : 1 ≤ η (lastFin l (by omega : 0 < l))) :
    (∑ j ∈ legalRaiseIndices (by omega : 0 < l) (raiseAt η (lastFin l (by omega : 0 < l))),
        ∑ i ∈ legalRaiseIndices (by omega : 0 < l)
            (raiseAt (raiseAt η (lastFin l (by omega : 0 < l))) j),
          weight 4 l (raiseAt (raiseAt (raiseAt η (lastFin l (by omega : 0 < l))) j) i))
      ≤ ((1 : ℚ) / 250) * weight 4 l η := by
  classical
  let hl : 0 < l := by omega
  let last := lastFin l hl
  let M : ℕ := η last
  let δ : Fin l → ℕ := raiseAt η last
  let F : Fin l → ℚ := fun j =>
    ∑ i ∈ legalRaiseIndices hl (raiseAt δ j), weight 4 l (raiseAt (raiseAt δ j) i)
  have hη_unfold := hη
  rw [support] at hη_unfold
  rcases (Finset.mem_filter.mp hη_unfold).2 with ⟨hnd, hsum⟩
  have hδnd : NondecreasingFin δ := by
    intro i j hij
    by_cases hj : j = last
    · subst j
      by_cases hi : i = last
      · subst i
        simp [δ, raiseAt]
      · have hle := hnd i last (by dsimp [last, lastFin]; omega)
        simp [δ, raiseAt, hi]
        omega
    · have hi : i ≠ last := by
        intro hi
        subst i
        have hj_le_last : (j : ℕ) ≤ (last : ℕ) := by dsimp [last, lastFin]; omega
        have : j = last := Fin.ext (le_antisymm hj_le_last hij)
        exact hj this
      simp [δ, raiseAt, hi, hj]
      exact hnd i j hij
  have hlegal_eq : legalRaiseIndices hl δ = insert last ((predecessorRaiseIndices hl δ).filter
      (fun k => k = lastFin l hl ∨ δ k + 1 = δ (lastFin l hl))) := by
    ext k
    by_cases hk : k = last
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, last, hk]
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, last, hk]
  let P : Finset (Fin l) := (predecessorRaiseIndices hl δ).filter
      (fun k => k = lastFin l hl ∨ δ k + 1 = δ (lastFin l hl))
  have hlast_notin_pred : last ∉ predecessorRaiseIndices hl δ := by
    simp [predecessorRaiseIndices, last, lastFin]
    intro hbad
    omega
  have hsum_split : (∑ j ∈ legalRaiseIndices hl δ, F j) ≤ F last + ∑ j ∈ P, F j := by
    apply le_of_eq
    calc
      (∑ j ∈ legalRaiseIndices hl δ, F j) = ∑ j ∈ insert last P, F j := by
        rw [hlegal_eq]
      _ = F last + ∑ j ∈ P, F j := by
        rw [Finset.sum_insert]
        intro hmem
        exact hlast_notin_pred (Finset.mem_filter.mp hmem).1
  have hlast_inner : F last ≤
      ((1 / (((M + l + 5 : ℕ) : ℚ))) *
        ((1 / (((M + l + 6 : ℕ) : ℚ))) + (1 / (((M + l + 4 : ℕ) : ℚ))))) * weight 4 l δ := by
    have h := legalRaise_sum_after_raise_last_oneStep_a4 hl (η := δ) hδnd
    have hδlast : δ last = M + 1 := by simp [δ, M, last, raiseAt]
    have hδ_last_weight : weight 4 l (raiseAt δ last) =
        (1 / (((M + l + 5 : ℕ) : ℚ))) * weight 4 l δ := by
      have hw := weight_raiseAt_eq_inv (a := 4) δ last
      have hden : 4 + (last : ℕ) + δ last + 1 = M + l + 5 := by
        rw [hδlast]
        dsimp [last, lastFin]
        omega
      rw [hw]
      simp [hden]
    dsimp [F]
    calc
      (∑ i ∈ legalRaiseIndices hl (raiseAt δ last), weight 4 l (raiseAt (raiseAt δ last) i))
          ≤ (((1 / (((δ last + l + 5 : ℕ) : ℚ))) + (1 / (((δ last + l + 3 : ℕ) : ℚ)))) * weight 4 l (raiseAt δ last)) := by
            simpa [last] using h
      _ = ((1 / (((M + l + 5 : ℕ) : ℚ))) *
        ((1 / (((M + l + 6 : ℕ) : ℚ))) + (1 / (((M + l + 4 : ℕ) : ℚ))))) * weight 4 l δ := by
          rw [hδlast, hδ_last_weight]
          ring
  have hpred_each : ∀ j ∈ P, F j ≤
      ((1 / (((M + l + 3 : ℕ) : ℚ))) *
        ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 2 : ℕ) : ℚ))))) * weight 4 l δ := by
    intro j hjP
    have hjlegal : j ∈ legalRaiseIndices hl δ := by
      rw [hlegal_eq]
      exact Finset.mem_insert_of_mem hjP
    have hjpred : j ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hjP).1
    have hj_ne_last : j ≠ last := by
      intro h
      exact hlast_notin_pred (by simpa [h] using hjpred)
    have hj_succ_last : (j : ℕ) + 1 = (last : ℕ) := by
      have hleftδ : leftmostMax hl δ = last := by
        simpa [δ, last] using leftmostMax_raiseAt_last_of_nondecreasing hl hnd
      rw [predecessorRaiseIndices] at hjpred
      rcases (Finset.mem_filter.mp hjpred).2 with ⟨hjlt, hjeq⟩
      have hv : last = (⟨(j : ℕ) + 1, hjlt⟩ : Fin l) := by
        simpa [hleftδ, last] using hjeq
      exact (congrArg Fin.val hv).symm
    have h := legalRaise_sum_after_raise_nonlast_oneStep_a4 hl (η := δ) hδnd hjlegal hj_ne_last
    have hδlast : δ last = M + 1 := by simp [δ, M, last, raiseAt]
    have hjcond : j = lastFin l hl ∨ δ j + 1 = δ (lastFin l hl) := (Finset.mem_filter.mp hjP).2
    have hδj : δ j = M := by
      cases hjcond with
      | inl hjl => exact False.elim (hj_ne_last (by simpa [last] using hjl))
      | inr hval =>
          rw [hδlast] at hval
          omega
    have hj_weight : weight 4 l (raiseAt δ j) =
        (1 / (((M + l + 3 : ℕ) : ℚ))) * weight 4 l δ := by
      have hw := weight_raiseAt_eq_inv (a := 4) δ j
      have hden : 4 + (j : ℕ) + δ j + 1 = M + l + 3 := by
        dsimp [last, lastFin] at hj_succ_last
        omega
      rw [hw]
      simp [hden]
    dsimp [F]
    have hdenLastInner : M + 1 + l + 4 = M + l + 5 := by omega
    have hdenPredInner : M + 1 + (j : ℕ) + 3 = M + l + 2 := by
      dsimp [last, lastFin] at hj_succ_last
      omega
    calc
      (∑ i ∈ legalRaiseIndices hl (raiseAt δ j), weight 4 l (raiseAt (raiseAt δ j) i))
          ≤ (((1 / (((δ last + l + 4 : ℕ) : ℚ))) + (1 / (((δ last + (j : ℕ) + 3 : ℕ) : ℚ)))) * weight 4 l (raiseAt δ j)) := by
            simpa [last] using h
      _ = ((1 / (((M + l + 3 : ℕ) : ℚ))) *
        ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 2 : ℕ) : ℚ))))) * weight 4 l δ := by
          rw [hj_weight]
          rw [hδlast, hdenLastInner, hdenPredInner]
          ring
  have hP_card : P.card ≤ 1 := by
    exact le_trans (Finset.card_filter_le _ _) (card_predecessorRaiseIndices_le_one hl δ)
  have hP_cardQ : (P.card : ℚ) ≤ (1 : ℚ) := by exact_mod_cast hP_card
  have hpred_coeff_nonneg : 0 ≤ ((1 / (((M + l + 3 : ℕ) : ℚ))) *
        ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 2 : ℕ) : ℚ))))) * weight 4 l δ := by
    exact mul_nonneg (mul_nonneg (by positivity) (add_nonneg (by positivity) (by positivity)))
      (weight_nonneg 4 l δ)
  have hsumP : (∑ j ∈ P, F j) ≤
      ((1 / (((M + l + 3 : ℕ) : ℚ))) *
        ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 2 : ℕ) : ℚ))))) * weight 4 l δ := by
    calc
      (∑ j ∈ P, F j) ≤ ∑ j ∈ P,
        ((1 / (((M + l + 3 : ℕ) : ℚ))) *
        ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 2 : ℕ) : ℚ))))) * weight 4 l δ :=
          Finset.sum_le_sum hpred_each
      _ ≤ ((1 / (((M + l + 3 : ℕ) : ℚ))) *
        ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 2 : ℕ) : ℚ))))) * weight 4 l δ := by
          rw [Finset.sum_const]
          simp
          exact mul_le_of_le_one_left (by simpa using hpred_coeff_nonneg) hP_cardQ
  have hsecond : (∑ j ∈ legalRaiseIndices hl δ, F j) ≤
      (((1 / (((M + l + 5 : ℕ) : ℚ))) *
        ((1 / (((M + l + 6 : ℕ) : ℚ))) + (1 / (((M + l + 4 : ℕ) : ℚ))))) +
       ((1 / (((M + l + 3 : ℕ) : ℚ))) *
        ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 2 : ℕ) : ℚ)))))) * weight 4 l δ := by
    calc
      (∑ j ∈ legalRaiseIndices hl δ, F j) ≤ F last + ∑ j ∈ P, F j := hsum_split
      _ ≤ ((1 / (((M + l + 5 : ℕ) : ℚ))) *
        ((1 / (((M + l + 6 : ℕ) : ℚ))) + (1 / (((M + l + 4 : ℕ) : ℚ))))) * weight 4 l δ +
        ((1 / (((M + l + 3 : ℕ) : ℚ))) *
        ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 2 : ℕ) : ℚ))))) * weight 4 l δ :=
          add_le_add hlast_inner hsumP
      _ = (((1 / (((M + l + 5 : ℕ) : ℚ))) *
        ((1 / (((M + l + 6 : ℕ) : ℚ))) + (1 / (((M + l + 4 : ℕ) : ℚ))))) +
       ((1 / (((M + l + 3 : ℕ) : ℚ))) *
        ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 2 : ℕ) : ℚ)))))) * weight 4 l δ := by ring
  have hfirst : weight 4 l δ = (1 / (((M + l + 4 : ℕ) : ℚ))) * weight 4 l η := by
    have hw := weight_raiseAt_eq_inv (a := 4) η last
    have hden : 4 + (last : ℕ) + η last + 1 = M + l + 4 := by
      dsimp [M, last, lastFin]
      omega
    rw [hw]
    simp [hden]
  have hcoeff := triple_R_first_coeff_le_1_250 (M := M) (l := l) (by simpa [M, last] using hMpos) hl6
  have hwη : 0 ≤ weight 4 l η := weight_nonneg 4 l η
  calc
    (∑ j ∈ legalRaiseIndices (by omega : 0 < l) (raiseAt η (lastFin l (by omega : 0 < l))),
        ∑ i ∈ legalRaiseIndices (by omega : 0 < l)
            (raiseAt (raiseAt η (lastFin l (by omega : 0 < l))) j),
          weight 4 l (raiseAt (raiseAt (raiseAt η (lastFin l (by omega : 0 < l))) j) i))
      = ∑ j ∈ legalRaiseIndices hl δ, F j := by
          simp [F, δ, last]
    _ ≤ (((1 / (((M + l + 5 : ℕ) : ℚ))) *
        ((1 / (((M + l + 6 : ℕ) : ℚ))) + (1 / (((M + l + 4 : ℕ) : ℚ))))) +
       ((1 / (((M + l + 3 : ℕ) : ℚ))) *
        ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 2 : ℕ) : ℚ)))))) * weight 4 l δ := hsecond
    _ = ((1 / (((M + l + 4 : ℕ) : ℚ))) *
      (((1 / (((M + l + 5 : ℕ) : ℚ))) *
        ((1 / (((M + l + 6 : ℕ) : ℚ))) + (1 / (((M + l + 4 : ℕ) : ℚ))))) +
       ((1 / (((M + l + 3 : ℕ) : ℚ))) *
        ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 2 : ℕ) : ℚ))))))) * weight 4 l η := by
          rw [hfirst]
          ring
    _ ≤ ((1 : ℚ) / 250) * weight 4 l η := by
          exact mul_le_mul_of_nonneg_right hcoeff hwη

/-- Coarse compiled bound for the legal three-step branch whose first raise is the
last index, in dimensions `l ≥ 6`.  The coefficient `1/100` is weaker than the
researched `1721/566280`, but is already below `1/75` for this branch alone. -/
lemma legalRaise_triple_sum_first_last_a4_l_ge_six {l : ℕ} (hl6 : 6 ≤ l)
    (η : Fin l → ℕ) :
    (∑ j ∈ legalRaiseIndices (by omega : 0 < l) (raiseAt η (lastFin l (by omega : 0 < l))),
        ∑ i ∈ legalRaiseIndices (by omega : 0 < l)
            (raiseAt (raiseAt η (lastFin l (by omega : 0 < l))) j),
          weight 4 l (raiseAt (raiseAt (raiseAt η (lastFin l (by omega : 0 < l))) j) i))
      ≤ ((1 : ℚ) / 100) * weight 4 l η := by
  classical
  let hl : 0 < l := by omega
  let last := lastFin l hl
  let δ : Fin l → ℕ := raiseAt η last
  let c : ℚ := (1 : ℚ) / (4 + 1 : ℕ) + (1 : ℚ) / (4 + l : ℕ)
  have hc_nonneg : 0 ≤ c := by dsimp [c]; positivity
  have hc_le : c ≤ (3 : ℚ) / 10 := by
    have hden : (10 : ℚ) ≤ ((4 + l : ℕ) : ℚ) := by exact_mod_cast (by omega : 10 ≤ 4 + l)
    have hinv : (1 : ℚ) / ((4 + l : ℕ) : ℚ) ≤ (1 : ℚ) / 10 :=
      one_div_le_one_div_of_le (by norm_num) hden
    calc
      c = (1 : ℚ) / 5 + (1 : ℚ) / ((4 + l : ℕ) : ℚ) := by norm_num [c]
      _ ≤ (1 : ℚ) / 5 + (1 : ℚ) / 10 := add_le_add_right hinv ((1 : ℚ) / 5)
      _ = (3 : ℚ) / 10 := by norm_num
  have hinner : ∀ θ : Fin l → ℕ,
      (∑ i ∈ legalRaiseIndices hl θ, weight 4 l (raiseAt θ i)) ≤ c * weight 4 l θ := by
    intro θ
    simpa [c] using legalRaiseIndices_weight_sum_le_sharp_general (a := 4) hl θ
  have hsum_inner :
      (∑ j ∈ legalRaiseIndices hl δ,
          ∑ i ∈ legalRaiseIndices hl (raiseAt δ j), weight 4 l (raiseAt (raiseAt δ j) i)) ≤
        ∑ j ∈ legalRaiseIndices hl δ, c * weight 4 l (raiseAt δ j) := by
    exact Finset.sum_le_sum (by intro j hj; exact hinner (raiseAt δ j))
  have hsum_factor :
      (∑ j ∈ legalRaiseIndices hl δ, c * weight 4 l (raiseAt δ j)) =
        c * (∑ j ∈ legalRaiseIndices hl δ, weight 4 l (raiseAt δ j)) := by
    rw [Finset.mul_sum]
  have hsecond :
      (∑ j ∈ legalRaiseIndices hl δ,
          ∑ i ∈ legalRaiseIndices hl (raiseAt δ j), weight 4 l (raiseAt (raiseAt δ j) i)) ≤
        c * (c * weight 4 l δ) := by
    calc
      (∑ j ∈ legalRaiseIndices hl δ,
          ∑ i ∈ legalRaiseIndices hl (raiseAt δ j), weight 4 l (raiseAt (raiseAt δ j) i))
          ≤ ∑ j ∈ legalRaiseIndices hl δ, c * weight 4 l (raiseAt δ j) := hsum_inner
      _ = c * (∑ j ∈ legalRaiseIndices hl δ, weight 4 l (raiseAt δ j)) := hsum_factor
      _ ≤ c * (c * weight 4 l δ) :=
        mul_le_mul_of_nonneg_left (hinner δ) hc_nonneg
  have hfirst : weight 4 l δ ≤ ((1 : ℚ) / 10) * weight 4 l η := by
    have h := weight_raiseAt_le_index (a := 4) η last
    have hden_nat : 4 + (last : ℕ) + 1 = 4 + l := by
      dsimp [last, lastFin]
      omega
    have hden : (10 : ℚ) ≤ ((4 + l : ℕ) : ℚ) := by exact_mod_cast (by omega : 10 ≤ 4 + l)
    have hinv : (1 : ℚ) / ((4 + l : ℕ) : ℚ) ≤ (1 : ℚ) / 10 :=
      one_div_le_one_div_of_le (by norm_num) hden
    have hw : 0 ≤ weight 4 l η := weight_nonneg 4 l η
    calc
      weight 4 l δ ≤ (1 / ((4 + l : ℕ) : ℚ)) * weight 4 l η := by
        simpa [δ, hden_nat] using h
      _ ≤ ((1 : ℚ) / 10) * weight 4 l η := mul_le_mul_of_nonneg_right hinv hw
  have hcoeff : c * (c * (((1 : ℚ) / 10) * weight 4 l η)) ≤
      ((1 : ℚ) / 100) * weight 4 l η := by
    have hc2 : c * c ≤ (9 : ℚ) / 100 := by
      have hmul := mul_le_mul hc_le hc_le hc_nonneg (by norm_num : (0 : ℚ) ≤ (3 : ℚ) / 10)
      norm_num at hmul ⊢
      exact hmul
    have hc2_nonneg : 0 ≤ c * c := mul_nonneg hc_nonneg hc_nonneg
    have hten_nonneg : 0 ≤ ((1 : ℚ) / 10) * weight 4 l η :=
      mul_nonneg (by norm_num) (weight_nonneg 4 l η)
    have hmul := mul_le_mul_of_nonneg_right hc2 hten_nonneg
    calc
      c * (c * (((1 : ℚ) / 10) * weight 4 l η)) = (c * c) * (((1 : ℚ) / 10) * weight 4 l η) := by ring
      _ ≤ ((9 : ℚ) / 100) * (((1 : ℚ) / 10) * weight 4 l η) := hmul
      _ ≤ ((1 : ℚ) / 100) * weight 4 l η := by
        have hw : 0 ≤ weight 4 l η := weight_nonneg 4 l η
        nlinarith
  calc
    (∑ j ∈ legalRaiseIndices (by omega : 0 < l) (raiseAt η (lastFin l (by omega : 0 < l))),
        ∑ i ∈ legalRaiseIndices (by omega : 0 < l)
            (raiseAt (raiseAt η (lastFin l (by omega : 0 < l))) j),
          weight 4 l (raiseAt (raiseAt (raiseAt η (lastFin l (by omega : 0 < l))) j) i))
        = ∑ j ∈ legalRaiseIndices hl δ,
            ∑ i ∈ legalRaiseIndices hl (raiseAt δ j), weight 4 l (raiseAt (raiseAt δ j) i) := by
          simp [last, δ]
    _ ≤ c * (c * weight 4 l δ) := hsecond
    _ ≤ c * (c * (((1 : ℚ) / 10) * weight 4 l η)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfirst hc_nonneg) hc_nonneg
    _ ≤ ((1 : ℚ) / 100) * weight 4 l η := hcoeff

lemma thrice_local_arithmetic_R_plus_L_q_zero_le_one_75 :
    ((1721 : ℚ) / 566280) + ((1 : ℚ) / 300) ≤ (1 : ℚ) / 75 := by
  norm_num

lemma thrice_local_arithmetic_R_plus_L_q_one_le_one_75 :
    ((1721 : ℚ) / 566280) + ((23 : ℚ) / 3960) ≤ (1 : ℚ) / 75 := by
  norm_num

lemma thrice_local_arithmetic_R_plus_L_q_ge_two_le_one_75 :
    ((1721 : ℚ) / 566280) + ((43 : ℚ) / 4620) ≤ (1 : ℚ) / 75 := by
  norm_num


/-- The coefficient for the branch whose first raise is the last index, as supplied by
`legalRaise_sum_after_raise_last_a3`. -/
def twoStepLastCoeff (M l : ℕ) : ℚ :=
  (1 / (((M + l + 3 : ℕ) : ℚ))) *
    (1 / (((M + l + 4 : ℕ) : ℚ)) + 1 / (((M + l + 2 : ℕ) : ℚ)))

/-- The coefficient for a branch whose first raise is a non-last legal index `k`, as
supplied by `legalRaise_sum_after_raise_nonlast_a3`. -/
def twoStepNonlastCoeff (M l : ℕ) (k : Fin l) : ℚ :=
  (1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
    (1 / (((M + l + 3 : ℕ) : ℚ)) +
      1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ)))

lemma twoStepLastCoeff_le_tenth_of_two_le_l (M l : ℕ) (hl : 2 ≤ l) :
    twoStepLastCoeff M l ≤ (1 : ℚ) / 10 := by
  have hx : (5 : ℚ) ≤ ((M + l + 3 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : 5 ≤ M + l + 3)
  have hy : (6 : ℚ) ≤ ((M + l + 4 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : 6 ≤ M + l + 4)
  have hz : (4 : ℚ) ≤ ((M + l + 2 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : 4 ≤ M + l + 2)
  have hxinv : (1 : ℚ) / ((M + l + 3 : ℕ) : ℚ) ≤ (1 : ℚ) / 5 :=
    one_div_le_one_div_of_le (by norm_num) hx
  have hyinv : (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) ≤ (1 : ℚ) / 6 :=
    one_div_le_one_div_of_le (by norm_num) hy
  have hzinv : (1 : ℚ) / ((M + l + 2 : ℕ) : ℚ) ≤ (1 : ℚ) / 4 :=
    one_div_le_one_div_of_le (by norm_num) hz
  have hsum : (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) +
        (1 : ℚ) / ((M + l + 2 : ℕ) : ℚ) ≤ (1 : ℚ) / 6 + (1 : ℚ) / 4 :=
    add_le_add hyinv hzinv
  have hsum_nonneg : 0 ≤ (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) +
        (1 : ℚ) / ((M + l + 2 : ℕ) : ℚ) := by positivity
  have hmul := mul_le_mul hxinv hsum hsum_nonneg (by norm_num : (0 : ℚ) ≤ (1 : ℚ) / 5)
  calc
    twoStepLastCoeff M l ≤ (1 : ℚ) / 5 * ((1 : ℚ) / 6 + (1 : ℚ) / 4) := by
      simpa [twoStepLastCoeff] using hmul
    _ ≤ (1 : ℚ) / 10 := by norm_num


lemma twoStepCoeff_sum_le_tenth_of_five_le_y_nine_le_x {l : ℕ} (M : ℕ) (k : Fin l)
    (hy : 5 ≤ M + (k : ℕ) + 3) (hx : 9 ≤ M + l + 3) :
    twoStepLastCoeff M l + twoStepNonlastCoeff M l k ≤ (1 : ℚ) / 10 := by
  have hx3 : (9 : ℚ) ≤ ((M + l + 3 : ℕ) : ℚ) := by exact_mod_cast hx
  have hx4 : (10 : ℚ) ≤ ((M + l + 4 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : 10 ≤ M + l + 4)
  have hx2 : (8 : ℚ) ≤ ((M + l + 2 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : 8 ≤ M + l + 2)
  have hy3 : (5 : ℚ) ≤ ((M + (k : ℕ) + 3 : ℕ) : ℚ) := by exact_mod_cast hy
  have hy2 : (4 : ℚ) ≤ ((M + (k : ℕ) + 2 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : 4 ≤ M + (k : ℕ) + 2)
  have hx3inv : (1 : ℚ) / ((M + l + 3 : ℕ) : ℚ) ≤ (1 : ℚ) / 9 :=
    one_div_le_one_div_of_le (by norm_num) hx3
  have hx4inv : (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) ≤ (1 : ℚ) / 10 :=
    one_div_le_one_div_of_le (by norm_num) hx4
  have hx2inv : (1 : ℚ) / ((M + l + 2 : ℕ) : ℚ) ≤ (1 : ℚ) / 8 :=
    one_div_le_one_div_of_le (by norm_num) hx2
  have hy3inv : (1 : ℚ) / ((M + (k : ℕ) + 3 : ℕ) : ℚ) ≤ (1 : ℚ) / 5 :=
    one_div_le_one_div_of_le (by norm_num) hy3
  have hy2inv : (1 : ℚ) / ((M + (k : ℕ) + 2 : ℕ) : ℚ) ≤ (1 : ℚ) / 4 :=
    one_div_le_one_div_of_le (by norm_num) hy2
  have hRsum : (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) +
        (1 : ℚ) / ((M + l + 2 : ℕ) : ℚ) ≤ (1 : ℚ) / 10 + (1 : ℚ) / 8 :=
    add_le_add hx4inv hx2inv
  have hRsum_nonneg : 0 ≤ (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) +
        (1 : ℚ) / ((M + l + 2 : ℕ) : ℚ) := by positivity
  have hRmul := mul_le_mul hx3inv hRsum hRsum_nonneg (by norm_num : (0 : ℚ) ≤ (1 : ℚ) / 9)
  have hR : twoStepLastCoeff M l ≤ (1 : ℚ) / 9 * ((1 : ℚ) / 10 + (1 : ℚ) / 8) := by
    simpa [twoStepLastCoeff] using hRmul
  have hLsum : (1 : ℚ) / ((M + l + 3 : ℕ) : ℚ) +
        (1 : ℚ) / ((M + (k : ℕ) + 2 : ℕ) : ℚ) ≤ (1 : ℚ) / 9 + (1 : ℚ) / 4 :=
    add_le_add hx3inv hy2inv
  have hLsum_nonneg : 0 ≤ (1 : ℚ) / ((M + l + 3 : ℕ) : ℚ) +
        (1 : ℚ) / ((M + (k : ℕ) + 2 : ℕ) : ℚ) := by positivity
  have hLmul := mul_le_mul hy3inv hLsum hLsum_nonneg (by norm_num : (0 : ℚ) ≤ (1 : ℚ) / 5)
  have hL : twoStepNonlastCoeff M l k ≤ (1 : ℚ) / 5 * ((1 : ℚ) / 9 + (1 : ℚ) / 4) := by
    simpa [twoStepNonlastCoeff] using hLmul
  calc
    twoStepLastCoeff M l + twoStepNonlastCoeff M l k
        ≤ (1 : ℚ) / 9 * ((1 : ℚ) / 10 + (1 : ℚ) / 8) +
          (1 : ℚ) / 5 * ((1 : ℚ) / 9 + (1 : ℚ) / 4) := add_le_add hR hL
    _ ≤ (1 : ℚ) / 10 := by norm_num

/-- Local two-step estimate in the easy case where every legal first raise is the
last index.  The `2 ≤ l` hypothesis lets us use the existing `R`-branch bound
without separating the vacuous predecessor in dimension one. -/
lemma loweringTwiceFiber_weight_sum_le_tenth_only_last_of_two_le_l
    {l N : ℕ} (hl : 0 < l) (hl2 : 2 ≤ l) {η : Fin l → ℕ} (hη : η ∈ support l N)
    (honly : ∀ k ∈ legalRaiseIndices hl η, k = lastFin l hl) :
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤
      ((1 : ℚ) / 10) * weight 3 l η := by
  classical
  let last := lastFin l hl
  let M : ℕ := η last
  let F : Fin l → ℚ := fun k =>
    ∑ j ∈ legalRaiseIndices hl (raiseAt η k), weight 3 l (raiseAt (raiseAt η k) j)
  have hpair := loweringTwiceFiber_weight_sum_le_legal_candidate_index_pairs (N := N) hl η
  have hsubset : legalRaiseIndices hl η ⊆ ({last} : Finset (Fin l)) := by
    intro k hk
    simp [honly k hk, last]
  have hsum_single : (∑ k ∈ legalRaiseIndices hl η, F k) ≤ F last := by
    calc
      (∑ k ∈ legalRaiseIndices hl η, F k) ≤ ∑ k ∈ ({last} : Finset (Fin l)), F k := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (by intro x hx hnot; exact Finset.sum_nonneg (by intro j hj; exact weight_nonneg 3 l _))
      _ = F last := by simp
  have hR : F last ≤ twoStepLastCoeff M l * weight 3 l η := by
    simpa [F, twoStepLastCoeff, M, last] using
      (legalRaise_sum_after_raise_last_a3 (N := N) hl (η := η) hη)
  have hcoeff : twoStepLastCoeff M l ≤ (1 : ℚ) / 10 :=
    twoStepLastCoeff_le_tenth_of_two_le_l M l hl2
  have hw : 0 ≤ weight 3 l η := weight_nonneg 3 l η
  calc
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤ ∑ k ∈ legalRaiseIndices hl η, F k := hpair
    _ ≤ F last := hsum_single
    _ ≤ twoStepLastCoeff M l * weight 3 l η := hR
    _ ≤ ((1 : ℚ) / 10) * weight 3 l η := mul_le_mul_of_nonneg_right hcoeff hw

/-- A reusable local reduction: if the legal first raises are covered by the last
index and one non-last index, and the corresponding two branch coefficients add to
at most `1/10`, then the desired fiber estimate follows. -/
lemma loweringTwiceFiber_weight_sum_le_tenth_of_one_nonlast_coeff
    {l N : ℕ} (hl : 0 < l) {η : Fin l → ℕ} (hη : η ∈ support l N) {k : Fin l}
    (hklegal : k ∈ legalRaiseIndices hl η) (hk_ne_last : k ≠ lastFin l hl)
    (hcover : ∀ i ∈ legalRaiseIndices hl η, i = lastFin l hl ∨ i = k)
    (hcoeff : twoStepLastCoeff (η (lastFin l hl)) l +
        twoStepNonlastCoeff (η (lastFin l hl)) l k ≤ (1 : ℚ) / 10) :
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤
      ((1 : ℚ) / 10) * weight 3 l η := by
  classical
  let last := lastFin l hl
  let M : ℕ := η last
  let F : Fin l → ℚ := fun i =>
    ∑ j ∈ legalRaiseIndices hl (raiseAt η i), weight 3 l (raiseAt (raiseAt η i) j)
  have hpair := loweringTwiceFiber_weight_sum_le_legal_candidate_index_pairs (N := N) hl η
  have hsubset : legalRaiseIndices hl η ⊆ insert last ({k} : Finset (Fin l)) := by
    intro i hi
    rcases hcover i hi with hi_last | hi_k
    · simp [last, hi_last]
    · simp [hi_k]
  have hsum_two : (∑ i ∈ legalRaiseIndices hl η, F i) ≤ F last + F k := by
    calc
      (∑ i ∈ legalRaiseIndices hl η, F i) ≤ ∑ i ∈ insert last ({k} : Finset (Fin l)), F i := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (by intro x hx hnot; exact Finset.sum_nonneg (by intro j hj; exact weight_nonneg 3 l _))
      _ = F last + F k := by
        rw [Finset.sum_insert]
        · simp
        · simpa [last] using hk_ne_last.symm
  have hR : F last ≤ twoStepLastCoeff M l * weight 3 l η := by
    simpa [F, twoStepLastCoeff, M, last] using
      (legalRaise_sum_after_raise_last_a3 (N := N) hl (η := η) hη)
  have hL : F k ≤ twoStepNonlastCoeff M l k * weight 3 l η := by
    simpa [F, twoStepNonlastCoeff, M, last] using
      (legalRaise_sum_after_raise_nonlast_a3 (N := N) hl (η := η) hη hklegal hk_ne_last)
  have hw : 0 ≤ weight 3 l η := weight_nonneg 3 l η
  calc
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤ ∑ i ∈ legalRaiseIndices hl η, F i := hpair
    _ ≤ F last + F k := hsum_two
    _ ≤ twoStepLastCoeff M l * weight 3 l η +
          twoStepNonlastCoeff M l k * weight 3 l η := add_le_add hR hL
    _ = (twoStepLastCoeff M l + twoStepNonlastCoeff M l k) * weight 3 l η := by ring
    _ ≤ ((1 : ℚ) / 10) * weight 3 l η := by
      exact mul_le_mul_of_nonneg_right (by simpa [M, last] using hcoeff) hw


lemma loweringTwiceFiber_weight_sum_le_candidate_index_pairs {l N : ℕ} (hl : 0 < l)
    (η : Fin l → ℕ) :
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤
      ∑ k ∈ correctedCandidateRaiseIndices hl η,
        ∑ j ∈ correctedCandidateRaiseIndices hl (raiseAt η k),
          weight 3 l (raiseAt (raiseAt η k) j) := by
  classical
  calc
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ)
        ≤ ∑ θ ∈ candidatePreimages hl η, ∑ δ ∈ candidatePreimages hl θ, weight 3 l δ :=
          loweringTwiceFiber_weight_sum_le_twiceCandidatePreimages_sum (N := N) hl η
    _ ≤ ∑ θ ∈ candidatePreimages hl η,
          ∑ j ∈ correctedCandidateRaiseIndices hl θ, weight 3 l (raiseAt θ j) := by
          exact Finset.sum_le_sum (by
            intro θ hθ
            exact sum_candidatePreimages_le_sum_indices θ (correctedCandidateRaiseIndices hl θ))

    _ ≤ ∑ k ∈ correctedCandidateRaiseIndices hl η,
          ∑ j ∈ correctedCandidateRaiseIndices hl (raiseAt η k),
            weight 3 l (raiseAt (raiseAt η k) j) := by
          exact sum_image_le_sum
            (s := correctedCandidateRaiseIndices hl η)
            (f := fun k => raiseAt η k)
            (g := fun θ => ∑ j ∈ correctedCandidateRaiseIndices hl θ, weight 3 l (raiseAt θ j))
            (by
              intro θ
              exact Finset.sum_nonneg (by intro j hj; exact weight_nonneg 3 l (raiseAt θ j)))


lemma legalRaiseIndices_nonlast_eq_of_nonlast {l : ℕ} (hl : 0 < l) {η : Fin l → ℕ}
    {i k : Fin l} (hilegal : i ∈ legalRaiseIndices hl η) (hiklegal : k ∈ legalRaiseIndices hl η)
    (hi_ne_last : i ≠ lastFin l hl) (hk_ne_last : k ≠ lastFin l hl) : i = k := by
  classical
  have hicorr : i ∈ correctedCandidateRaiseIndices hl η := (Finset.mem_filter.mp hilegal).1
  have hkcorr : k ∈ correctedCandidateRaiseIndices hl η := (Finset.mem_filter.mp hiklegal).1
  have hipred : i ∈ predecessorRaiseIndices hl η := by
    rw [correctedCandidateRaiseIndices] at hicorr
    exact (Finset.mem_insert.mp hicorr).resolve_left hi_ne_last
  have hkpred : k ∈ predecessorRaiseIndices hl η := by
    rw [correctedCandidateRaiseIndices] at hkcorr
    exact (Finset.mem_insert.mp hkcorr).resolve_left hk_ne_last
  have hcard := card_predecessorRaiseIndices_le_one hl η
  rw [Finset.card_le_one] at hcard
  exact hcard i hipred k hkpred

lemma loweringTwiceFiber_weight_sum_le_tenth_of_one_nonlast_coeff_auto
    {l N : ℕ} (hl : 0 < l) {η : Fin l → ℕ} (hη : η ∈ support l N) {k : Fin l}
    (hklegal : k ∈ legalRaiseIndices hl η) (hk_ne_last : k ≠ lastFin l hl)
    (hcoeff : twoStepLastCoeff (η (lastFin l hl)) l +
        twoStepNonlastCoeff (η (lastFin l hl)) l k ≤ (1 : ℚ) / 10) :
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤
      ((1 : ℚ) / 10) * weight 3 l η := by
  apply loweringTwiceFiber_weight_sum_le_tenth_of_one_nonlast_coeff hl hη hklegal hk_ne_last ?_ hcoeff
  intro i hilegal
  by_cases hi : i = lastFin l hl
  · exact Or.inl hi
  · exact Or.inr (legalRaiseIndices_nonlast_eq_of_nonlast hl hilegal hklegal hi hk_ne_last)

/-- A concrete one-nonlast-index local estimate using the coarse four-denominator
branch coefficients.  It covers all cases where `y = M+k+3 ≥ 5` and
`x = M+l+3 ≥ 9`; in particular it excludes the small coarse-coefficient corner
`x = 8, y = 5` that contains the true exceptional `(M,k,l)=(1,1,4)` case. -/
lemma loweringTwiceFiber_weight_sum_le_tenth_of_one_nonlast_five_le_y_nine_le_x
    {l N : ℕ} (hl : 0 < l) {η : Fin l → ℕ} (hη : η ∈ support l N) {k : Fin l}
    (hklegal : k ∈ legalRaiseIndices hl η) (hk_ne_last : k ≠ lastFin l hl)
    (hy : 5 ≤ η (lastFin l hl) + (k : ℕ) + 3)
    (hx : 9 ≤ η (lastFin l hl) + l + 3) :
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤
      ((1 : ℚ) / 10) * weight 3 l η := by
  exact loweringTwiceFiber_weight_sum_le_tenth_of_one_nonlast_coeff_auto hl hη hklegal hk_ne_last
    (twoStepCoeff_sum_le_tenth_of_five_le_y_nine_le_x (η (lastFin l hl)) k hy hx)


/-- A legal non-last raise has last value at least one. -/
lemma last_value_pos_of_legal_nonlast {l : ℕ} (hl : 0 < l) {η : Fin l → ℕ} {k : Fin l}
    (hklegal : k ∈ legalRaiseIndices hl η) (hk_ne_last : k ≠ lastFin l hl) :
    1 ≤ η (lastFin l hl) := by
  have hk_cond : k = lastFin l hl ∨ η k + 1 = η (lastFin l hl) :=
    (Finset.mem_filter.mp hklegal).2
  cases hk_cond with
  | inl hkl => exact False.elim (hk_ne_last hkl)
  | inr hval => omega


/-- A legal non-last raise is precisely the predecessor of the current leftmost
maximum, at the level of indices.  This is the structural support needed for
value-dependent denominator estimates in the `L` branch. -/
lemma legal_nonlast_succ_eq_leftmostMax {l : ℕ} (hl : 0 < l) {η : Fin l → ℕ} {k : Fin l}
    (hklegal : k ∈ legalRaiseIndices hl η) (hk_ne_last : k ≠ lastFin l hl) :
    ∃ hklt : (k : ℕ) + 1 < l, leftmostMax hl η = ⟨(k : ℕ) + 1, hklt⟩ := by
  classical
  have hcorr : k ∈ correctedCandidateRaiseIndices hl η := (Finset.mem_filter.mp hklegal).1
  have hpred : k ∈ predecessorRaiseIndices hl η := by
    rw [correctedCandidateRaiseIndices] at hcorr
    exact (Finset.mem_insert.mp hcorr).resolve_left hk_ne_last
  rw [predecessorRaiseIndices] at hpred
  exact (Finset.mem_filter.mp hpred).2

/-- Denominator lower bounds forced by `support`/non-last legality in the
`a = 4`, `l ≥ 6` triple `L` branch.  Here `M` is the last (maximal) value. -/
lemma legal_nonlast_a4_l_ge_six_denominator_lowers
    {l N : ℕ} (hl6 : 6 ≤ l) {η : Fin l → ℕ} (hη : η ∈ support l N) {k : Fin l}
    (hklegal : k ∈ legalRaiseIndices (by omega : 0 < l) η)
    (hk_ne_last : k ≠ lastFin l (by omega : 0 < l)) :
    let M : ℕ := η (lastFin l (by omega : 0 < l))
    1 ≤ M ∧
      5 ≤ M + (k : ℕ) + 4 ∧
      11 ≤ M + l + 4 ∧
      12 ≤ M + l + 5 ∧
      10 ≤ M + l + 3 ∧
      ((k : ℕ) = 0 ∨ 6 ≤ M + (k : ℕ) + 4) ∧
      (2 ≤ (k : ℕ) → 7 ≤ M + (k : ℕ) + 4) ∧
      (2 ≤ (k : ℕ) → 6 ≤ M + (k : ℕ) + 3) ∧
      (2 ≤ (k : ℕ) → 5 ≤ M + (k : ℕ) + 2) := by
  classical
  let hl : 0 < l := by omega
  let M : ℕ := η (lastFin l hl)
  have hM : 1 ≤ M := by
    simpa [M, hl] using last_value_pos_of_legal_nonlast hl hklegal hk_ne_last
  dsimp [M]
  constructor
  · exact hM
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · by_cases hk0 : (k : ℕ) = 0
    · exact Or.inl hk0
    · exact Or.inr (by omega)
  constructor
  · intro hk2; omega
  constructor
  · intro hk2; omega
  · intro hk2; omega

/-- The `q = 0` (boundary predecessor) arithmetic coefficient is below the
researched `43/4620` constant. -/
lemma triple_L_coeff_q_zero_le_43_4620 {M l : ℕ} (hM : 1 ≤ M) (hl6 : 6 ≤ l) :
    (1 / (((M + 4 : ℕ) : ℚ))) *
        ((1 / (((M + l + 4 : ℕ) : ℚ))) *
          (1 / (((M + l + 5 : ℕ) : ℚ)) + 1 / (((M + l + 3 : ℕ) : ℚ))))
      ≤ (43 : ℚ) / 4620 := by
  have hA : (5 : ℚ) ≤ ((M + 4 : ℕ) : ℚ) := by exact_mod_cast (by omega : 5 ≤ M + 4)
  have hB : (11 : ℚ) ≤ ((M + l + 4 : ℕ) : ℚ) := by exact_mod_cast (by omega : 11 ≤ M + l + 4)
  have hC : (12 : ℚ) ≤ ((M + l + 5 : ℕ) : ℚ) := by exact_mod_cast (by omega : 12 ≤ M + l + 5)
  have hD : (10 : ℚ) ≤ ((M + l + 3 : ℕ) : ℚ) := by exact_mod_cast (by omega : 10 ≤ M + l + 3)
  have hAi : (1 : ℚ) / ((M + 4 : ℕ) : ℚ) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hA
  have hBi : (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) ≤ 1 / 11 := one_div_le_one_div_of_le (by norm_num) hB
  have hCi : (1 : ℚ) / ((M + l + 5 : ℕ) : ℚ) ≤ 1 / 12 := one_div_le_one_div_of_le (by norm_num) hC
  have hDi : (1 : ℚ) / ((M + l + 3 : ℕ) : ℚ) ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hD
  have hsum : (1 : ℚ) / ((M + l + 5 : ℕ) : ℚ) + 1 / ((M + l + 3 : ℕ) : ℚ) ≤ 1 / 12 + 1 / 10 :=
    add_le_add hCi hDi
  have hmul1 : (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) *
        (1 / ((M + l + 5 : ℕ) : ℚ) + 1 / ((M + l + 3 : ℕ) : ℚ)) ≤
      (1 / 11) * (1 / 12 + 1 / 10) := by
    exact mul_le_mul hBi hsum (by positivity) (by norm_num)
  have hmul2 := mul_le_mul hAi hmul1 (by positivity)
    (by norm_num : (0 : ℚ) ≤ 1 / 5)
  calc
    (1 / (((M + 4 : ℕ) : ℚ))) *
        ((1 / (((M + l + 4 : ℕ) : ℚ))) *
          (1 / (((M + l + 5 : ℕ) : ℚ)) + 1 / (((M + l + 3 : ℕ) : ℚ))))
        ≤ (1 / 5) * ((1 / 11) * (1 / 12 + 1 / 10)) := hmul2
    _ ≤ (43 : ℚ) / 4620 := by norm_num

/-- The `q = 1` arithmetic coefficient (where the new predecessor is index `0`,
so there is no further predecessor term) is below `43/4620`. -/
lemma triple_L_coeff_q_one_le_43_4620 {M l : ℕ} (hM : 1 ≤ M) (hl6 : 6 ≤ l) :
    (1 / (((M + 5 : ℕ) : ℚ))) *
      ((1 / (((M + l + 4 : ℕ) : ℚ))) *
          (1 / (((M + l + 5 : ℕ) : ℚ)) + 1 / (((M + l + 3 : ℕ) : ℚ))) +
        (1 / (((M + 4 : ℕ) : ℚ))) * (1 / (((M + l + 4 : ℕ) : ℚ))))
      ≤ (43 : ℚ) / 4620 := by
  have hA : (6 : ℚ) ≤ ((M + 5 : ℕ) : ℚ) := by exact_mod_cast (by omega : 6 ≤ M + 5)
  have hB : (11 : ℚ) ≤ ((M + l + 4 : ℕ) : ℚ) := by exact_mod_cast (by omega : 11 ≤ M + l + 4)
  have hC : (12 : ℚ) ≤ ((M + l + 5 : ℕ) : ℚ) := by exact_mod_cast (by omega : 12 ≤ M + l + 5)
  have hD : (10 : ℚ) ≤ ((M + l + 3 : ℕ) : ℚ) := by exact_mod_cast (by omega : 10 ≤ M + l + 3)
  have hE : (5 : ℚ) ≤ ((M + 4 : ℕ) : ℚ) := by exact_mod_cast (by omega : 5 ≤ M + 4)
  have hAi : (1 : ℚ) / ((M + 5 : ℕ) : ℚ) ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) hA
  have hBi : (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) ≤ 1 / 11 := one_div_le_one_div_of_le (by norm_num) hB
  have hCi : (1 : ℚ) / ((M + l + 5 : ℕ) : ℚ) ≤ 1 / 12 := one_div_le_one_div_of_le (by norm_num) hC
  have hDi : (1 : ℚ) / ((M + l + 3 : ℕ) : ℚ) ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hD
  have hEi : (1 : ℚ) / ((M + 4 : ℕ) : ℚ) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hE
  have hsum : (1 : ℚ) / ((M + l + 5 : ℕ) : ℚ) + 1 / ((M + l + 3 : ℕ) : ℚ) ≤ 1 / 12 + 1 / 10 :=
    add_le_add hCi hDi
  have hlast : (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) *
        (1 / ((M + l + 5 : ℕ) : ℚ) + 1 / ((M + l + 3 : ℕ) : ℚ)) ≤
      (1 / 11) * (1 / 12 + 1 / 10) :=
    mul_le_mul hBi hsum (by positivity) (by norm_num)
  have hpred : (1 : ℚ) / ((M + 4 : ℕ) : ℚ) * (1 / ((M + l + 4 : ℕ) : ℚ)) ≤
      (1 / 5) * (1 / 11) :=
    mul_le_mul hEi hBi (by positivity) (by norm_num)
  have hbr : (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) *
          (1 / ((M + l + 5 : ℕ) : ℚ) + 1 / ((M + l + 3 : ℕ) : ℚ)) +
        (1 / ((M + 4 : ℕ) : ℚ)) * (1 / ((M + l + 4 : ℕ) : ℚ)) ≤
      (1 / 11) * (1 / 12 + 1 / 10) + (1 / 5) * (1 / 11) :=
    add_le_add hlast hpred
  have hmul := mul_le_mul hAi hbr (by positivity) (by norm_num : (0 : ℚ) ≤ 1 / 6)
  calc
    (1 / (((M + 5 : ℕ) : ℚ))) *
      ((1 / (((M + l + 4 : ℕ) : ℚ))) *
          (1 / (((M + l + 5 : ℕ) : ℚ)) + 1 / (((M + l + 3 : ℕ) : ℚ))) +
        (1 / (((M + 4 : ℕ) : ℚ))) * (1 / (((M + l + 4 : ℕ) : ℚ))))
        ≤ (1 / 6) * ((1 / 11) * (1 / 12 + 1 / 10) + (1 / 5) * (1 / 11)) := hmul
    _ ≤ (43 : ℚ) / 4620 := by norm_num

/-- The `q ≥ 2` arithmetic coefficient has worst value exactly `43/4620`,
achieved at the minimal denominators `(M,l,q) = (1,6,2)`. -/
lemma triple_L_coeff_q_ge_two_le_43_4620 {M l q : ℕ}
    (hM : 1 ≤ M) (hl6 : 6 ≤ l) (hq2 : 2 ≤ q) :
    (1 / (((M + q + 4 : ℕ) : ℚ))) *
      ((1 / (((M + l + 4 : ℕ) : ℚ))) *
          (1 / (((M + l + 5 : ℕ) : ℚ)) + 1 / (((M + l + 3 : ℕ) : ℚ))) +
        (1 / (((M + q + 3 : ℕ) : ℚ))) *
          (1 / (((M + l + 4 : ℕ) : ℚ)) + 1 / (((M + q + 2 : ℕ) : ℚ))))
      ≤ (43 : ℚ) / 4620 := by
  have hA : (7 : ℚ) ≤ ((M + q + 4 : ℕ) : ℚ) := by exact_mod_cast (by omega : 7 ≤ M + q + 4)
  have hB : (11 : ℚ) ≤ ((M + l + 4 : ℕ) : ℚ) := by exact_mod_cast (by omega : 11 ≤ M + l + 4)
  have hC : (12 : ℚ) ≤ ((M + l + 5 : ℕ) : ℚ) := by exact_mod_cast (by omega : 12 ≤ M + l + 5)
  have hD : (10 : ℚ) ≤ ((M + l + 3 : ℕ) : ℚ) := by exact_mod_cast (by omega : 10 ≤ M + l + 3)
  have hE : (6 : ℚ) ≤ ((M + q + 3 : ℕ) : ℚ) := by exact_mod_cast (by omega : 6 ≤ M + q + 3)
  have hF : (5 : ℚ) ≤ ((M + q + 2 : ℕ) : ℚ) := by exact_mod_cast (by omega : 5 ≤ M + q + 2)
  have hAi : (1 : ℚ) / ((M + q + 4 : ℕ) : ℚ) ≤ 1 / 7 := one_div_le_one_div_of_le (by norm_num) hA
  have hBi : (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) ≤ 1 / 11 := one_div_le_one_div_of_le (by norm_num) hB
  have hCi : (1 : ℚ) / ((M + l + 5 : ℕ) : ℚ) ≤ 1 / 12 := one_div_le_one_div_of_le (by norm_num) hC
  have hDi : (1 : ℚ) / ((M + l + 3 : ℕ) : ℚ) ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hD
  have hEi : (1 : ℚ) / ((M + q + 3 : ℕ) : ℚ) ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) hE
  have hFi : (1 : ℚ) / ((M + q + 2 : ℕ) : ℚ) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hF
  have hsumL : (1 : ℚ) / ((M + l + 5 : ℕ) : ℚ) + 1 / ((M + l + 3 : ℕ) : ℚ) ≤ 1 / 12 + 1 / 10 :=
    add_le_add hCi hDi
  have hsumP : (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) + 1 / ((M + q + 2 : ℕ) : ℚ) ≤ 1 / 11 + 1 / 5 :=
    add_le_add hBi hFi
  have hlast : (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) *
        (1 / ((M + l + 5 : ℕ) : ℚ) + 1 / ((M + l + 3 : ℕ) : ℚ)) ≤
      (1 / 11) * (1 / 12 + 1 / 10) :=
    mul_le_mul hBi hsumL (by positivity) (by norm_num)
  have hpred : (1 : ℚ) / ((M + q + 3 : ℕ) : ℚ) *
        (1 / ((M + l + 4 : ℕ) : ℚ) + 1 / ((M + q + 2 : ℕ) : ℚ)) ≤
      (1 / 6) * (1 / 11 + 1 / 5) :=
    mul_le_mul hEi hsumP (by positivity) (by norm_num)
  have hbr : (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) *
          (1 / ((M + l + 5 : ℕ) : ℚ) + 1 / ((M + l + 3 : ℕ) : ℚ)) +
        (1 / ((M + q + 3 : ℕ) : ℚ)) *
          (1 / ((M + l + 4 : ℕ) : ℚ) + 1 / ((M + q + 2 : ℕ) : ℚ)) ≤
      (1 / 11) * (1 / 12 + 1 / 10) + (1 / 6) * (1 / 11 + 1 / 5) :=
    add_le_add hlast hpred
  have hmul := mul_le_mul hAi hbr (by positivity) (by norm_num : (0 : ℚ) ≤ 1 / 7)
  calc
    (1 / (((M + q + 4 : ℕ) : ℚ))) *
      ((1 / (((M + l + 4 : ℕ) : ℚ))) *
          (1 / (((M + l + 5 : ℕ) : ℚ)) + 1 / (((M + l + 3 : ℕ) : ℚ))) +
        (1 / (((M + q + 3 : ℕ) : ℚ))) *
          (1 / (((M + l + 4 : ℕ) : ℚ)) + 1 / (((M + q + 2 : ℕ) : ℚ))))
        ≤ (1 / 7) * ((1 / 11) * (1 / 12 + 1 / 10) + (1 / 6) * (1 / 11 + 1 / 5)) := hmul
    _ = (43 : ℚ) / 4620 := by norm_num


/-- Compiled `L`-first triple branch for `a = 4`, `l ≥ 6`: if the first
legal raise is a non-last index, its total two-step continuation is at most
`43/4620` of the original weight. -/
lemma legalRaise_triple_sum_first_nonlast_a4_l_ge_six {l N : ℕ} (hl6 : 6 ≤ l)
    {η : Fin l → ℕ} (hη : η ∈ support l N) {k : Fin l}
    (hklegal : k ∈ legalRaiseIndices (by omega : 0 < l) η)
    (hk_ne_last : k ≠ lastFin l (by omega : 0 < l)) :
    (∑ j ∈ legalRaiseIndices (by omega : 0 < l) (raiseAt η k),
        ∑ i ∈ legalRaiseIndices (by omega : 0 < l) (raiseAt (raiseAt η k) j),
          weight 4 l (raiseAt (raiseAt (raiseAt η k) j) i))
      ≤ ((43 : ℚ) / 4620) * weight 4 l η := by
  classical
  let hl : 0 < l := by omega
  let last := lastFin l hl
  let M : ℕ := η last
  let δ : Fin l → ℕ := raiseAt η k
  let F : Fin l → ℚ := fun j =>
    ∑ i ∈ legalRaiseIndices hl (raiseAt δ j), weight 4 l (raiseAt (raiseAt δ j) i)
  have hη_unfold := hη
  rw [support] at hη_unfold
  rcases (Finset.mem_filter.mp hη_unfold).2 with ⟨hnd, hsum⟩
  have hk_cond : k = lastFin l hl ∨ η k + 1 = η (lastFin l hl) :=
    (Finset.mem_filter.mp hklegal).2
  have hηk_succ : η k + 1 = M := by
    cases hk_cond with
    | inl hkl => exact False.elim (hk_ne_last (by simpa [hl] using hkl))
    | inr hval => simpa [M, last] using hval
  have hδlast : δ last = M := by
    dsimp [δ, M, last]
    by_cases h : lastFin l hl = k
    · exact False.elim (hk_ne_last h.symm)
    · simp [raiseAt, h]
  have hδk : δ k = M := by
    dsimp [δ]
    simp [raiseAt, hηk_succ]
  have hk_mem_corr : k ∈ correctedCandidateRaiseIndices hl η :=
    (Finset.mem_filter.mp hklegal).1
  have hk_mem_pred : k ∈ predecessorRaiseIndices hl η := by
    rw [correctedCandidateRaiseIndices] at hk_mem_corr
    exact (Finset.mem_insert.mp hk_mem_corr).resolve_left hk_ne_last
  have hk_succ_lt : (k : ℕ) + 1 < l := by
    rw [predecessorRaiseIndices] at hk_mem_pred
    exact (Finset.mem_filter.mp hk_mem_pred).2.1
  let ksucc : Fin l := ⟨(k : ℕ) + 1, hk_succ_lt⟩
  have hleft_eta : leftmostMax hl η = ksucc := by
    rw [predecessorRaiseIndices] at hk_mem_pred
    exact (Finset.mem_filter.mp hk_mem_pred).2.2
  have hη_ksucc : η ksucc = M := by
    calc
      η ksucc = η (leftmostMax hl η) := by rw [hleft_eta]
      _ = η (lastFin l hl) := leftmostMax_value hl η
      _ = M := by simp [M, last]
  have hδnd : NondecreasingFin δ := by
    intro i j hij
    by_cases hi : i = k
    · subst i
      by_cases hj : j = k
      · subst j
        simp [δ]
      · have hlt : (k : ℕ) < (j : ℕ) := by
          have hne : (j : ℕ) ≠ (k : ℕ) := by
            intro hv
            exact hj (Fin.ext hv)
          omega
        have hksucc_le : (ksucc : ℕ) ≤ (j : ℕ) := by
          simp [ksucc]
          omega
        have hηj : η j = M := by
          have hv := value_eq_leftmostMax_of_ge hl hnd (i := j) (by simpa [hleft_eta] using hksucc_le)
          calc
            η j = η (leftmostMax hl η) := hv
            _ = η ksucc := by rw [hleft_eta]
            _ = M := hη_ksucc
        calc
          δ k = M := hδk
          _ = η j := hηj.symm
          _ = δ j := by simp [δ, hj]
    · by_cases hj : j = k
      · subst j
        have hi_le_last : (i : ℕ) ≤ (last : ℕ) := by
          dsimp [last, lastFin]
          omega
        have hv := hnd i last hi_le_last
        calc
          δ i = η i := by simp [δ, hi]
          _ ≤ M := by simpa [M] using hv
          _ = δ k := hδk.symm
      · calc
          δ i = η i := by simp [δ, hi]
          _ ≤ η j := hnd i j hij
          _ = δ j := by simp [δ, hj]
  have hleft : leftmostMax hl δ = k := by
    apply Fin.ext
    have hle_k : (leftmostMax hl δ : ℕ) ≤ (k : ℕ) := by
      apply leftmostMax_le_of_value hl δ
      rw [hδk, hδlast]
    by_contra hne_val
    have hlt_lm_eta : (leftmostMax hl δ : ℕ) < (leftmostMax hl η : ℕ) := by
      rw [hleft_eta]
      simp [ksucc]
      omega
    have hlm_ne_k : leftmostMax hl δ ≠ k := by
      intro h
      exact hne_val (congrArg Fin.val h)
    have hδ_lm : δ (leftmostMax hl δ) = η (leftmostMax hl δ) := by
      dsimp [δ]
      by_cases h : leftmostMax hl (raiseAt η k) = k
      · exact False.elim (hlm_ne_k h)
      · simp [raiseAt, h]
    have hlt_val : η (leftmostMax hl δ) < M := by
      have h := value_lt_leftmostMax hl hnd hlt_lm_eta
      simpa [hη_ksucc, hleft_eta] using h
    have hδ_lm_eq_M : δ (leftmostMax hl δ) = M := by
      calc
        δ (leftmostMax hl δ) = δ (lastFin l hl) := leftmostMax_value hl δ
        _ = M := hδlast
    rw [hδ_lm] at hδ_lm_eq_M
    omega
  let P : Finset (Fin l) := (predecessorRaiseIndices hl δ).filter
    (fun j => j = lastFin l hl ∨ δ j + 1 = δ (lastFin l hl))
  have hlast_notin_pred : last ∉ predecessorRaiseIndices hl δ := by
    simp [predecessorRaiseIndices, last, lastFin]
    intro hbad
    omega
  have hlegal_eq : legalRaiseIndices hl δ = insert last P := by
    ext j
    by_cases hj : j = last
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, P, last, hj]
    · simp [legalRaiseIndices, correctedCandidateRaiseIndices, P, last, hj]
  have hsum_split : (∑ j ∈ legalRaiseIndices hl δ, F j) ≤ F last + ∑ j ∈ P, F j := by
    apply le_of_eq
    calc
      (∑ j ∈ legalRaiseIndices hl δ, F j) = ∑ j ∈ insert last P, F j := by rw [hlegal_eq]
      _ = F last + ∑ j ∈ P, F j := by
        rw [Finset.sum_insert]
        intro hmem
        exact hlast_notin_pred (Finset.mem_filter.mp hmem).1
  have hlast_inner : F last ≤
      ((1 / (((M + l + 4 : ℕ) : ℚ))) *
        ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ))))) * weight 4 l δ := by
    have h := legalRaise_sum_after_raise_last_oneStep_a4 hl (η := δ) hδnd
    have hδ_last_weight : weight 4 l (raiseAt δ last) =
        (1 / (((M + l + 4 : ℕ) : ℚ))) * weight 4 l δ := by
      have hw := weight_raiseAt_eq_inv (a := 4) δ last
      have hden : 4 + (last : ℕ) + δ last + 1 = M + l + 4 := by
        rw [hδlast]
        dsimp [last, lastFin]
        omega
      rw [hw]
      simp [hden]
    dsimp [F]
    calc
      (∑ i ∈ legalRaiseIndices hl (raiseAt δ last), weight 4 l (raiseAt (raiseAt δ last) i))
          ≤ (((1 / (((δ last + l + 5 : ℕ) : ℚ))) + (1 / (((δ last + l + 3 : ℕ) : ℚ)))) * weight 4 l (raiseAt δ last)) := by
            simpa [last] using h
      _ = ((1 / (((M + l + 4 : ℕ) : ℚ))) *
        ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ))))) * weight 4 l δ := by
          rw [hδlast, hδ_last_weight]
          ring
  have hP_card : P.card ≤ 1 := by
    exact le_trans (Finset.card_filter_le _ _) (card_predecessorRaiseIndices_le_one hl δ)
  have hP_cardQ : (P.card : ℚ) ≤ (1 : ℚ) := by exact_mod_cast hP_card
  have hfirst : weight 4 l δ = (1 / (((M + (k : ℕ) + 4 : ℕ) : ℚ))) * weight 4 l η := by
    have hw := weight_raiseAt_eq_inv (a := 4) η k
    have hden : 4 + (k : ℕ) + η k + 1 = M + (k : ℕ) + 4 := by omega
    rw [hw]
    simp [hden, M, last]
  have hwη : 0 ≤ weight 4 l η := weight_nonneg 4 l η
  by_cases hk0 : (k : ℕ) = 0
  · have hP_empty : P = ∅ := by
      ext j
      simp
      intro hjP
      have hjpred : j ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hjP).1
      rw [predecessorRaiseIndices] at hjpred
      rcases (Finset.mem_filter.mp hjpred).2 with ⟨hjlt, hjeq⟩
      have hj_succ_k : (j : ℕ) + 1 = (k : ℕ) := by
        have hv : k = (⟨(j : ℕ) + 1, hjlt⟩ : Fin l) := by
          simpa [hleft] using hjeq
        exact (congrArg Fin.val hv).symm
      omega
    have hsecond : (∑ j ∈ legalRaiseIndices hl δ, F j) ≤
        ((1 / (((M + l + 4 : ℕ) : ℚ))) *
          ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ))))) * weight 4 l δ := by
      calc
        (∑ j ∈ legalRaiseIndices hl δ, F j) ≤ F last + ∑ j ∈ P, F j := hsum_split
        _ = F last := by rw [hP_empty]; simp
        _ ≤ ((1 / (((M + l + 4 : ℕ) : ℚ))) *
          ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ))))) * weight 4 l δ := hlast_inner
    have hcoeff := triple_L_coeff_q_zero_le_43_4620 (M := M) (l := l)
      (by simpa [M, last] using last_value_pos_of_legal_nonlast hl hklegal hk_ne_last) hl6
    calc
      (∑ j ∈ legalRaiseIndices (by omega : 0 < l) (raiseAt η k),
        ∑ i ∈ legalRaiseIndices (by omega : 0 < l) (raiseAt (raiseAt η k) j),
          weight 4 l (raiseAt (raiseAt (raiseAt η k) j) i))
          = ∑ j ∈ legalRaiseIndices hl δ, F j := by simp [F, δ]
      _ ≤ ((1 / (((M + l + 4 : ℕ) : ℚ))) *
          ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ))))) * weight 4 l δ := hsecond
      _ = ((1 / (((M + (k : ℕ) + 4 : ℕ) : ℚ))) *
          ((1 / (((M + l + 4 : ℕ) : ℚ))) *
          ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ)))))) * weight 4 l η := by
            rw [hfirst]
            ring
      _ = ((1 / (((M + 4 : ℕ) : ℚ))) *
          ((1 / (((M + l + 4 : ℕ) : ℚ))) *
          ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ)))))) * weight 4 l η := by
            rw [hk0]
      _ ≤ ((43 : ℚ) / 4620) * weight 4 l η := mul_le_mul_of_nonneg_right hcoeff hwη
  · by_cases hk1 : (k : ℕ) = 1
    · have hpred_each : ∀ j ∈ P, F j ≤
          ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * (1 / (((M + l + 4 : ℕ) : ℚ)))) * weight 4 l δ := by
        intro j hjP
        have hjlegal : j ∈ legalRaiseIndices hl δ := by rw [hlegal_eq]; exact Finset.mem_insert_of_mem hjP
        have hjpred : j ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hjP).1
        have hj_ne_last : j ≠ last := by intro h; exact hlast_notin_pred (by simpa [h] using hjpred)
        have hj_succ_k : (j : ℕ) + 1 = (k : ℕ) := by
          rw [predecessorRaiseIndices] at hjpred
          rcases (Finset.mem_filter.mp hjpred).2 with ⟨hjlt, hjeq⟩
          have hv : k = (⟨(j : ℕ) + 1, hjlt⟩ : Fin l) := by simpa [hleft] using hjeq
          exact (congrArg Fin.val hv).symm
        have hj_zero : (j : ℕ) = 0 := by omega
        have hjcond : j = lastFin l hl ∨ δ j + 1 = δ (lastFin l hl) := (Finset.mem_filter.mp hjP).2
        have hδj : δ j + 1 = M := by
          cases hjcond with
          | inl hjl => exact False.elim (hj_ne_last (by simpa [last] using hjl))
          | inr hval => simpa [hδlast, last] using hval
        have hj_weight : weight 4 l (raiseAt δ j) =
            (1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * weight 4 l δ := by
          have hw := weight_raiseAt_eq_inv (a := 4) δ j
          have hden : 4 + (j : ℕ) + δ j + 1 = M + (k : ℕ) + 3 := by omega
          rw [hw]
          simp [hden]
        have h := legalRaise_sum_after_raise_nonlast_k_zero_oneStep_a4 hl (η := δ) hδnd hjlegal hj_ne_last hj_zero
        dsimp [F]
        calc
          (∑ i ∈ legalRaiseIndices hl (raiseAt δ j), weight 4 l (raiseAt (raiseAt δ j) i))
              ≤ (1 / (((δ (lastFin l hl) + l + 4 : ℕ) : ℚ))) * weight 4 l (raiseAt δ j) := by
                simpa [last] using h
          _ = ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * (1 / (((M + l + 4 : ℕ) : ℚ)))) * weight 4 l δ := by
                rw [hδlast, hj_weight]
                ring
      have hpred_coeff_nonneg : 0 ≤ ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * (1 / (((M + l + 4 : ℕ) : ℚ)))) * weight 4 l δ := by
        exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (weight_nonneg 4 l δ)
      have hsumP : (∑ j ∈ P, F j) ≤
          ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * (1 / (((M + l + 4 : ℕ) : ℚ)))) * weight 4 l δ := by
        calc
          (∑ j ∈ P, F j) ≤ ∑ j ∈ P, ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * (1 / (((M + l + 4 : ℕ) : ℚ)))) * weight 4 l δ := Finset.sum_le_sum hpred_each
          _ ≤ ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * (1 / (((M + l + 4 : ℕ) : ℚ)))) * weight 4 l δ := by
            rw [Finset.sum_const]
            simp
            exact mul_le_of_le_one_left (by simpa using hpred_coeff_nonneg) hP_cardQ
      have hsecond : (∑ j ∈ legalRaiseIndices hl δ, F j) ≤
          (((1 / (((M + l + 4 : ℕ) : ℚ))) *
            ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ))))) +
            ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * (1 / (((M + l + 4 : ℕ) : ℚ))))) * weight 4 l δ := by
        calc
          (∑ j ∈ legalRaiseIndices hl δ, F j) ≤ F last + ∑ j ∈ P, F j := hsum_split
          _ ≤ ((1 / (((M + l + 4 : ℕ) : ℚ))) *
            ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ))))) * weight 4 l δ +
            ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * (1 / (((M + l + 4 : ℕ) : ℚ)))) * weight 4 l δ := add_le_add hlast_inner hsumP
          _ = (((1 / (((M + l + 4 : ℕ) : ℚ))) *
            ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ))))) +
            ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * (1 / (((M + l + 4 : ℕ) : ℚ))))) * weight 4 l δ := by ring
      have hcoeff1 := triple_L_coeff_q_one_le_43_4620 (M := M) (l := l)
        (by simpa [M, last] using last_value_pos_of_legal_nonlast hl hklegal hk_ne_last) hl6
      have hcoeff : (1 / (((M + (k : ℕ) + 4 : ℕ) : ℚ))) *
          (((1 / (((M + l + 4 : ℕ) : ℚ))) *
            ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ))))) +
            ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * (1 / (((M + l + 4 : ℕ) : ℚ))))) ≤ (43 : ℚ) / 4620 := by
        simpa [hk1] using hcoeff1
      calc
        (∑ j ∈ legalRaiseIndices (by omega : 0 < l) (raiseAt η k),
          ∑ i ∈ legalRaiseIndices (by omega : 0 < l) (raiseAt (raiseAt η k) j),
            weight 4 l (raiseAt (raiseAt (raiseAt η k) j) i)) = ∑ j ∈ legalRaiseIndices hl δ, F j := by simp [F, δ]
        _ ≤ (((1 / (((M + l + 4 : ℕ) : ℚ))) *
            ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ))))) +
            ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * (1 / (((M + l + 4 : ℕ) : ℚ))))) * weight 4 l δ := hsecond
        _ = ((1 / (((M + (k : ℕ) + 4 : ℕ) : ℚ))) *
          (((1 / (((M + l + 4 : ℕ) : ℚ))) *
            ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ))))) +
            ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * (1 / (((M + l + 4 : ℕ) : ℚ)))))) * weight 4 l η := by rw [hfirst]; ring
        _ ≤ ((43 : ℚ) / 4620) * weight 4 l η := mul_le_mul_of_nonneg_right hcoeff hwη
    · have hcoarse : (∑ j ∈ legalRaiseIndices hl δ, F j) ≤
        (((1 / (((M + l + 4 : ℕ) : ℚ))) *
          ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ))))) +
          ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
          ((1 / (((M + l + 4 : ℕ) : ℚ))) + (1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ)))))) * weight 4 l δ := by
      have hpred_each : ∀ j ∈ P, F j ≤
          ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
            ((1 / (((M + l + 4 : ℕ) : ℚ))) + (1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ))))) * weight 4 l δ := by
        intro j hjP
        have hjlegal : j ∈ legalRaiseIndices hl δ := by rw [hlegal_eq]; exact Finset.mem_insert_of_mem hjP
        have hjpred : j ∈ predecessorRaiseIndices hl δ := (Finset.mem_filter.mp hjP).1
        have hj_ne_last : j ≠ last := by intro h; exact hlast_notin_pred (by simpa [h] using hjpred)
        have hj_succ_k : (j : ℕ) + 1 = (k : ℕ) := by
          rw [predecessorRaiseIndices] at hjpred
          rcases (Finset.mem_filter.mp hjpred).2 with ⟨hjlt, hjeq⟩
          have hv : k = (⟨(j : ℕ) + 1, hjlt⟩ : Fin l) := by simpa [hleft] using hjeq
          exact (congrArg Fin.val hv).symm
        have hjcond : j = lastFin l hl ∨ δ j + 1 = δ (lastFin l hl) := (Finset.mem_filter.mp hjP).2
        have hδj : δ j + 1 = M := by
          cases hjcond with
          | inl hjl => exact False.elim (hj_ne_last (by simpa [last] using hjl))
          | inr hval => simpa [hδlast, last] using hval
        have hj_weight : weight 4 l (raiseAt δ j) =
            (1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) * weight 4 l δ := by
          have hw := weight_raiseAt_eq_inv (a := 4) δ j
          have hden : 4 + (j : ℕ) + δ j + 1 = M + (k : ℕ) + 3 := by omega
          rw [hw]
          simp [hden]
        have h := legalRaise_sum_after_raise_nonlast_oneStep_a4 hl (η := δ) hδnd hjlegal hj_ne_last
        have hdenPredInner : M + (j : ℕ) + 3 = M + (k : ℕ) + 2 := by omega
        dsimp [F]
        calc
          (∑ i ∈ legalRaiseIndices hl (raiseAt δ j), weight 4 l (raiseAt (raiseAt δ j) i))
              ≤ (((1 / (((δ last + l + 4 : ℕ) : ℚ))) + (1 / (((δ last + (j : ℕ) + 3 : ℕ) : ℚ)))) * weight 4 l (raiseAt δ j)) := by
                simpa [last] using h
          _ = ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
            ((1 / (((M + l + 4 : ℕ) : ℚ))) + (1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ))))) * weight 4 l δ := by
                rw [hj_weight]
                rw [hδlast, hdenPredInner]
                ring
      have hpred_coeff_nonneg : 0 ≤ ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
            ((1 / (((M + l + 4 : ℕ) : ℚ))) + (1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ))))) * weight 4 l δ := by
        exact mul_nonneg (mul_nonneg (by positivity) (add_nonneg (by positivity) (by positivity))) (weight_nonneg 4 l δ)
      have hsumP : (∑ j ∈ P, F j) ≤
          ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
            ((1 / (((M + l + 4 : ℕ) : ℚ))) + (1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ))))) * weight 4 l δ := by
        calc
          (∑ j ∈ P, F j) ≤ ∑ j ∈ P, ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
            ((1 / (((M + l + 4 : ℕ) : ℚ))) + (1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ))))) * weight 4 l δ := Finset.sum_le_sum hpred_each
          _ ≤ ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
            ((1 / (((M + l + 4 : ℕ) : ℚ))) + (1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ))))) * weight 4 l δ := by
            rw [Finset.sum_const]
            simp
            exact mul_le_of_le_one_left (by simpa using hpred_coeff_nonneg) hP_cardQ
      calc
        (∑ j ∈ legalRaiseIndices hl δ, F j) ≤ F last + ∑ j ∈ P, F j := hsum_split
        _ ≤ ((1 / (((M + l + 4 : ℕ) : ℚ))) *
          ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ))))) * weight 4 l δ +
          ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
          ((1 / (((M + l + 4 : ℕ) : ℚ))) + (1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ))))) * weight 4 l δ := add_le_add hlast_inner hsumP
        _ = (((1 / (((M + l + 4 : ℕ) : ℚ))) *
          ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ))))) +
          ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
          ((1 / (((M + l + 4 : ℕ) : ℚ))) + (1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ)))))) * weight 4 l δ := by ring
    have hk2 : 2 ≤ (k : ℕ) := by omega
    have hcoeff := triple_L_coeff_q_ge_two_le_43_4620 (M := M) (l := l) (q := (k : ℕ))
      (by simpa [M, last] using last_value_pos_of_legal_nonlast hl hklegal hk_ne_last) hl6 hk2
    calc
      (∑ j ∈ legalRaiseIndices (by omega : 0 < l) (raiseAt η k),
        ∑ i ∈ legalRaiseIndices (by omega : 0 < l) (raiseAt (raiseAt η k) j),
          weight 4 l (raiseAt (raiseAt (raiseAt η k) j) i)) = ∑ j ∈ legalRaiseIndices hl δ, F j := by simp [F, δ]
      _ ≤ (((1 / (((M + l + 4 : ℕ) : ℚ))) *
          ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ))))) +
          ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
          ((1 / (((M + l + 4 : ℕ) : ℚ))) + (1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ)))))) * weight 4 l δ := hcoarse
      _ = ((1 / (((M + (k : ℕ) + 4 : ℕ) : ℚ))) *
        (((1 / (((M + l + 4 : ℕ) : ℚ))) *
          ((1 / (((M + l + 5 : ℕ) : ℚ))) + (1 / (((M + l + 3 : ℕ) : ℚ))))) +
          ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
          ((1 / (((M + l + 4 : ℕ) : ℚ))) + (1 / (((M + (k : ℕ) + 2 : ℕ) : ℚ))))))) * weight 4 l η := by rw [hfirst]; ring
      _ ≤ ((43 : ℚ) / 4620) * weight 4 l η := mul_le_mul_of_nonneg_right hcoeff hwη

lemma twoStepCoeff_sum_le_tenth_k_zero_sharp {l : ℕ} (M : ℕ) (k : Fin l)
    (hM : 1 ≤ M) (hl2 : 2 ≤ l) :
    twoStepLastCoeff M l +
        ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
          (1 / (((M + l + 3 : ℕ) : ℚ)))) ≤ (1 : ℚ) / 10 := by
  have hx3 : (6 : ℚ) ≤ ((M + l + 3 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : 6 ≤ M + l + 3)
  have hx4 : (7 : ℚ) ≤ ((M + l + 4 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : 7 ≤ M + l + 4)
  have hx2 : (5 : ℚ) ≤ ((M + l + 2 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : 5 ≤ M + l + 2)
  have hy3 : (4 : ℚ) ≤ ((M + (k : ℕ) + 3 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : 4 ≤ M + (k : ℕ) + 3)
  have hx3inv : (1 : ℚ) / ((M + l + 3 : ℕ) : ℚ) ≤ (1 : ℚ) / 6 :=
    one_div_le_one_div_of_le (by norm_num) hx3
  have hx4inv : (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) ≤ (1 : ℚ) / 7 :=
    one_div_le_one_div_of_le (by norm_num) hx4
  have hx2inv : (1 : ℚ) / ((M + l + 2 : ℕ) : ℚ) ≤ (1 : ℚ) / 5 :=
    one_div_le_one_div_of_le (by norm_num) hx2
  have hy3inv : (1 : ℚ) / ((M + (k : ℕ) + 3 : ℕ) : ℚ) ≤ (1 : ℚ) / 4 :=
    one_div_le_one_div_of_le (by norm_num) hy3
  have hRsum : (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) +
        (1 : ℚ) / ((M + l + 2 : ℕ) : ℚ) ≤ (1 : ℚ) / 7 + (1 : ℚ) / 5 :=
    add_le_add hx4inv hx2inv
  have hRsum_nonneg : 0 ≤ (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) +
        (1 : ℚ) / ((M + l + 2 : ℕ) : ℚ) := by positivity
  have hRmul := mul_le_mul hx3inv hRsum hRsum_nonneg (by norm_num : (0 : ℚ) ≤ (1 : ℚ) / 6)
  have hR : twoStepLastCoeff M l ≤ (1 : ℚ) / 6 * ((1 : ℚ) / 7 + (1 : ℚ) / 5) := by
    simpa [twoStepLastCoeff] using hRmul
  have hLmul := mul_le_mul hy3inv hx3inv (by positivity : 0 ≤ (1 : ℚ) / ((M + l + 3 : ℕ) : ℚ))
    (by norm_num : (0 : ℚ) ≤ (1 : ℚ) / 4)
  have hL : ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
          (1 / (((M + l + 3 : ℕ) : ℚ)))) ≤ (1 : ℚ) / 4 * ((1 : ℚ) / 6) := by
    simpa using hLmul
  calc
    twoStepLastCoeff M l +
        ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
          (1 / (((M + l + 3 : ℕ) : ℚ))))
        ≤ (1 : ℚ) / 6 * ((1 : ℚ) / 7 + (1 : ℚ) / 5) +
          (1 : ℚ) / 4 * ((1 : ℚ) / 6) := add_le_add hR hL
    _ ≤ (1 : ℚ) / 10 := by norm_num

lemma twoStepCoeff_sum_le_tenth_immediate_sharp {l : ℕ} (M : ℕ) (k : Fin l)
    (hx : 7 ≤ M + l + 3) (hy : 5 ≤ M + (k : ℕ) + 3) :
    ((1 / (((M + l + 3 : ℕ) : ℚ))) *
        (1 / (((M + l + 4 : ℕ) : ℚ)))) +
        twoStepNonlastCoeff M l k ≤ (1 : ℚ) / 10 := by
  have hx3 : (7 : ℚ) ≤ ((M + l + 3 : ℕ) : ℚ) := by exact_mod_cast hx
  have hx4 : (8 : ℚ) ≤ ((M + l + 4 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : 8 ≤ M + l + 4)
  have hy3 : (5 : ℚ) ≤ ((M + (k : ℕ) + 3 : ℕ) : ℚ) := by exact_mod_cast hy
  have hy2 : (4 : ℚ) ≤ ((M + (k : ℕ) + 2 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : 4 ≤ M + (k : ℕ) + 2)
  have hx3inv : (1 : ℚ) / ((M + l + 3 : ℕ) : ℚ) ≤ (1 : ℚ) / 7 :=
    one_div_le_one_div_of_le (by norm_num) hx3
  have hx4inv : (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ) ≤ (1 : ℚ) / 8 :=
    one_div_le_one_div_of_le (by norm_num) hx4
  have hy3inv : (1 : ℚ) / ((M + (k : ℕ) + 3 : ℕ) : ℚ) ≤ (1 : ℚ) / 5 :=
    one_div_le_one_div_of_le (by norm_num) hy3
  have hy2inv : (1 : ℚ) / ((M + (k : ℕ) + 2 : ℕ) : ℚ) ≤ (1 : ℚ) / 4 :=
    one_div_le_one_div_of_le (by norm_num) hy2
  have hRmul := mul_le_mul hx3inv hx4inv (by positivity : 0 ≤ (1 : ℚ) / ((M + l + 4 : ℕ) : ℚ))
    (by norm_num : (0 : ℚ) ≤ (1 : ℚ) / 7)
  have hR : ((1 / (((M + l + 3 : ℕ) : ℚ))) *
        (1 / (((M + l + 4 : ℕ) : ℚ)))) ≤ (1 : ℚ) / 7 * ((1 : ℚ) / 8) := by
    simpa using hRmul
  have hLsum : (1 : ℚ) / ((M + l + 3 : ℕ) : ℚ) +
        (1 : ℚ) / ((M + (k : ℕ) + 2 : ℕ) : ℚ) ≤ (1 : ℚ) / 7 + (1 : ℚ) / 4 :=
    add_le_add hx3inv hy2inv
  have hLsum_nonneg : 0 ≤ (1 : ℚ) / ((M + l + 3 : ℕ) : ℚ) +
        (1 : ℚ) / ((M + (k : ℕ) + 2 : ℕ) : ℚ) := by positivity
  have hLmul := mul_le_mul hy3inv hLsum hLsum_nonneg (by norm_num : (0 : ℚ) ≤ (1 : ℚ) / 5)
  have hL : twoStepNonlastCoeff M l k ≤ (1 : ℚ) / 5 * ((1 : ℚ) / 7 + (1 : ℚ) / 4) := by
    simpa [twoStepNonlastCoeff] using hLmul
  calc
    ((1 / (((M + l + 3 : ℕ) : ℚ))) *
        (1 / (((M + l + 4 : ℕ) : ℚ)))) + twoStepNonlastCoeff M l k
        ≤ (1 : ℚ) / 7 * ((1 : ℚ) / 8) + (1 : ℚ) / 5 * ((1 : ℚ) / 7 + (1 : ℚ) / 4) :=
          add_le_add hR hL
    _ ≤ (1 : ℚ) / 10 := by norm_num

lemma loweringTwiceFiber_weight_sum_le_tenth_of_one_nonlast_k_zero
    {l N : ℕ} (hl : 0 < l) {η : Fin l → ℕ} (hη : η ∈ support l N) {k : Fin l}
    (hklegal : k ∈ legalRaiseIndices hl η) (hk_ne_last : k ≠ lastFin l hl)
    (hk_zero : (k : ℕ) = 0) :
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤
      ((1 : ℚ) / 10) * weight 3 l η := by
  classical
  let last := lastFin l hl
  let M : ℕ := η last
  let F : Fin l → ℚ := fun i =>
    ∑ j ∈ legalRaiseIndices hl (raiseAt η i), weight 3 l (raiseAt (raiseAt η i) j)
  have hpair := loweringTwiceFiber_weight_sum_le_legal_candidate_index_pairs (N := N) hl η
  have hsubset : legalRaiseIndices hl η ⊆ insert last ({k} : Finset (Fin l)) := by
    intro i hi
    by_cases hilast : i = last
    · simp [hilast]
    · have hik : i = k := legalRaiseIndices_nonlast_eq_of_nonlast hl hi hklegal (by simpa [last] using hilast) hk_ne_last
      simp [hik]
  have hsum_two : (∑ i ∈ legalRaiseIndices hl η, F i) ≤ F last + F k := by
    calc
      (∑ i ∈ legalRaiseIndices hl η, F i) ≤ ∑ i ∈ insert last ({k} : Finset (Fin l)), F i := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (by intro x hx hnot; exact Finset.sum_nonneg (by intro j hj; exact weight_nonneg 3 l _))
      _ = F last + F k := by
        rw [Finset.sum_insert]
        · simp
        · simpa [last] using hk_ne_last.symm
  have hR : F last ≤ twoStepLastCoeff M l * weight 3 l η := by
    simpa [F, twoStepLastCoeff, M, last] using
      (legalRaise_sum_after_raise_last_a3 (N := N) hl (η := η) hη)
  have hL : F k ≤ (((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
          (1 / (((M + l + 3 : ℕ) : ℚ)))) * weight 3 l η) := by
    simpa [F, M, last] using
      (legalRaise_sum_after_raise_nonlast_k_zero_a3 (N := N) hl (η := η) hη hklegal hk_ne_last hk_zero)
  have hMpos : 1 ≤ M := by simpa [M, last] using last_value_pos_of_legal_nonlast hl hklegal hk_ne_last
  have hl2 : 2 ≤ l := by
    have hval_ne : (k : ℕ) ≠ (lastFin l hl : ℕ) := by
      intro hval
      exact hk_ne_last (Fin.ext hval)
    dsimp [lastFin] at hval_ne
    omega
  have hcoeff := twoStepCoeff_sum_le_tenth_k_zero_sharp M k hMpos hl2
  have hw : 0 ≤ weight 3 l η := weight_nonneg 3 l η
  calc
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤ ∑ i ∈ legalRaiseIndices hl η, F i := hpair
    _ ≤ F last + F k := hsum_two
    _ ≤ twoStepLastCoeff M l * weight 3 l η +
          ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
          (1 / (((M + l + 3 : ℕ) : ℚ)))) * weight 3 l η := add_le_add hR hL
    _ = (twoStepLastCoeff M l +
          ((1 / (((M + (k : ℕ) + 3 : ℕ) : ℚ))) *
          (1 / (((M + l + 3 : ℕ) : ℚ))))) * weight 3 l η := by ring
    _ ≤ ((1 : ℚ) / 10) * weight 3 l η := mul_le_mul_of_nonneg_right hcoeff hw

lemma loweringTwiceFiber_weight_sum_le_tenth_of_one_nonlast_immediate_before_last_pos
    {l N : ℕ} (hl : 0 < l) {η : Fin l → ℕ} (hη : η ∈ support l N) {k : Fin l}
    (hklegal : k ∈ legalRaiseIndices hl η) (hk_ne_last : k ≠ lastFin l hl)
    (hk_succ_last : (k : ℕ) + 1 = (lastFin l hl : ℕ)) (hkpos : 0 < (k : ℕ)) :
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤
      ((1 : ℚ) / 10) * weight 3 l η := by
  classical
  let last := lastFin l hl
  let M : ℕ := η last
  let F : Fin l → ℚ := fun i =>
    ∑ j ∈ legalRaiseIndices hl (raiseAt η i), weight 3 l (raiseAt (raiseAt η i) j)
  have hpair := loweringTwiceFiber_weight_sum_le_legal_candidate_index_pairs (N := N) hl η
  have hsubset : legalRaiseIndices hl η ⊆ insert last ({k} : Finset (Fin l)) := by
    intro i hi
    by_cases hilast : i = last
    · simp [hilast]
    · have hik : i = k := legalRaiseIndices_nonlast_eq_of_nonlast hl hi hklegal (by simpa [last] using hilast) hk_ne_last
      simp [hik]
  have hsum_two : (∑ i ∈ legalRaiseIndices hl η, F i) ≤ F last + F k := by
    calc
      (∑ i ∈ legalRaiseIndices hl η, F i) ≤ ∑ i ∈ insert last ({k} : Finset (Fin l)), F i := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (by intro x hx hnot; exact Finset.sum_nonneg (by intro j hj; exact weight_nonneg 3 l _))
      _ = F last + F k := by
        rw [Finset.sum_insert]
        · simp
        · simpa [last] using hk_ne_last.symm
  have hR : F last ≤ (((1 / (((M + l + 3 : ℕ) : ℚ))) *
          (1 / (((M + l + 4 : ℕ) : ℚ)))) * weight 3 l η) := by
    simpa [F, M, last] using
      (legalRaise_sum_after_raise_last_no_pred_a3 (N := N) hl (η := η) hη hklegal hk_ne_last hk_succ_last)
  have hL : F k ≤ twoStepNonlastCoeff M l k * weight 3 l η := by
    simpa [F, twoStepNonlastCoeff, M, last] using
      (legalRaise_sum_after_raise_nonlast_a3 (N := N) hl (η := η) hη hklegal hk_ne_last)
  have hMpos : 1 ≤ M := by simpa [M, last] using last_value_pos_of_legal_nonlast hl hklegal hk_ne_last
  have hx : 7 ≤ M + l + 3 := by
    dsimp [lastFin] at hk_succ_last
    omega
  have hy : 5 ≤ M + (k : ℕ) + 3 := by omega
  have hcoeff := twoStepCoeff_sum_le_tenth_immediate_sharp M k hx hy
  have hw : 0 ≤ weight 3 l η := weight_nonneg 3 l η
  calc
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤ ∑ i ∈ legalRaiseIndices hl η, F i := hpair
    _ ≤ F last + F k := hsum_two
    _ ≤ ((1 / (((M + l + 3 : ℕ) : ℚ))) *
          (1 / (((M + l + 4 : ℕ) : ℚ)))) * weight 3 l η +
          twoStepNonlastCoeff M l k * weight 3 l η := add_le_add hR hL
    _ = (((1 / (((M + l + 3 : ℕ) : ℚ))) *
          (1 / (((M + l + 4 : ℕ) : ℚ)))) + twoStepNonlastCoeff M l k) * weight 3 l η := by ring
    _ ≤ ((1 : ℚ) / 10) * weight 3 l η := mul_le_mul_of_nonneg_right hcoeff hw

lemma loweringTwiceFiber_weight_sum_le_tenth_of_one_nonlast_immediate_before_last
    {l N : ℕ} (hl : 0 < l) {η : Fin l → ℕ} (hη : η ∈ support l N) {k : Fin l}
    (hklegal : k ∈ legalRaiseIndices hl η) (hk_ne_last : k ≠ lastFin l hl)
    (hk_succ_last : (k : ℕ) + 1 = (lastFin l hl : ℕ)) :
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤
      ((1 : ℚ) / 10) * weight 3 l η := by
  by_cases hk0 : (k : ℕ) = 0
  · exact loweringTwiceFiber_weight_sum_le_tenth_of_one_nonlast_k_zero hl hη hklegal hk_ne_last hk0
  · have hkpos : 0 < (k : ℕ) := by omega
    exact loweringTwiceFiber_weight_sum_le_tenth_of_one_nonlast_immediate_before_last_pos hl hη hklegal hk_ne_last hk_succ_last hkpos

lemma loweringTwiceFiber_weight_sum_le_tenth_of_one_nonlast_small_x_except_bad
    {l N : ℕ} (hl : 0 < l) {η : Fin l → ℕ} (hη : η ∈ support l N) {k : Fin l}
    (hklegal : k ∈ legalRaiseIndices hl η) (hk_ne_last : k ≠ lastFin l hl)
    (hxlt : η (lastFin l hl) + l + 3 < 9)
    (hnotbad : ¬ (η (lastFin l hl) = 1 ∧ (k : ℕ) = 1 ∧ l = 4)) :
    (∑ δ ∈ loweringTwiceFiber hl N η, weight 3 l δ) ≤
      ((1 : ℚ) / 10) * weight 3 l η := by
  by_cases hk0 : (k : ℕ) = 0
  · exact loweringTwiceFiber_weight_sum_le_tenth_of_one_nonlast_k_zero hl hη hklegal hk_ne_last hk0
  · have hk_mem_corr : k ∈ correctedCandidateRaiseIndices hl η := (Finset.mem_filter.mp hklegal).1
    have hk_mem_pred : k ∈ predecessorRaiseIndices hl η := by
      rw [correctedCandidateRaiseIndices] at hk_mem_corr
      exact (Finset.mem_insert.mp hk_mem_corr).resolve_left hk_ne_last
    have hk_succ_lt : (k : ℕ) + 1 < l := by
      rw [predecessorRaiseIndices] at hk_mem_pred
      exact (Finset.mem_filter.mp hk_mem_pred).2.1
    by_cases himm : (k : ℕ) + 1 = (lastFin l hl : ℕ)
    · exact loweringTwiceFiber_weight_sum_le_tenth_of_one_nonlast_immediate_before_last hl hη hklegal hk_ne_last himm
    · have hMpos : 1 ≤ η (lastFin l hl) := last_value_pos_of_legal_nonlast hl hklegal hk_ne_last
      have hkpos : 0 < (k : ℕ) := by omega
      have hbad : η (lastFin l hl) = 1 ∧ (k : ℕ) = 1 ∧ l = 4 := by
        dsimp [lastFin] at himm
        omega
      exact False.elim (hnotbad hbad)



lemma D_three_two_step_contraction_large (m s : ℕ) (hm : 13 ≤ m) :
    D 3 m (s + 2) ≤ ((1 : ℚ) / 10) * D 3 m s := by
  have hmpos : 0 < m := by omega
  let c : ℚ := (1 : ℚ) / (3 + 1 : ℕ) + (1 : ℚ) / (3 + m : ℕ)
  have hstep : D 3 m (s + 2) ≤ c ^ 2 * D 3 m s := by
    simpa [c, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      D_two_step_bound_sharp_general_pos_l 3 m s hmpos
  have hnonD : 0 ≤ D 3 m s := D_nonneg 3 m s
  have hc_nonneg : 0 ≤ c := by dsimp [c]; positivity
  have hden : (16 : ℚ) ≤ (3 + m : ℕ) := by exact_mod_cast (by omega : 16 ≤ 3 + m)
  have hinv : (1 : ℚ) / (3 + m : ℕ) ≤ (1 : ℚ) / 16 := by
    exact one_div_le_one_div_of_le (by norm_num) hden
  have hc_le : c ≤ (5 : ℚ) / 16 := by
    calc
      c = (1 : ℚ) / 4 + (1 : ℚ) / (3 + m : ℕ) := by norm_num [c]
      _ ≤ (1 : ℚ) / 4 + (1 : ℚ) / 16 := by
        linarith [add_le_add_left hinv ((1 : ℚ) / 4)]
      _ = (5 : ℚ) / 16 := by norm_num
  have hc2 : c ^ 2 ≤ (1 : ℚ) / 10 := by


    have hsq := mul_le_mul hc_le hc_le hc_nonneg (by norm_num : (0 : ℚ) ≤ (5 / 16 : ℚ))
    rw [← pow_two] at hsq
    norm_num at hsq ⊢
    linarith
  exact le_trans hstep (mul_le_mul_of_nonneg_right hc2 hnonD)


/-- Local two-step estimate for every non-exceptional fiber in dimensions at least two.
The only excluded local configuration is `η last = 1`, non-last raise index `1`,
and `l = 4`. -/
lemma loweringTwiceFiber_weight_sum_le_tenth_nonexceptional
    {l N : ℕ} (hl2 : 2 ≤ l) {η : Fin l → ℕ} (hη : η ∈ support l N)
    (hnotbad : ∀ k : Fin l, k ∈ legalRaiseIndices (by omega : 0 < l) η →
      k ≠ lastFin l (by omega : 0 < l) →
      ¬ (η (lastFin l (by omega : 0 < l)) = 1 ∧ (k : ℕ) = 1 ∧ l = 4)) :
    (∑ δ ∈ loweringTwiceFiber (by omega : 0 < l) N η, weight 3 l δ) ≤
      ((1 : ℚ) / 10) * weight 3 l η := by
  classical
  let hl : 0 < l := by omega
  by_cases hex : ∃ k : Fin l, k ∈ legalRaiseIndices hl η ∧ k ≠ lastFin l hl
  · rcases hex with ⟨k, hklegal, hk_ne_last⟩
    by_cases hk0 : (k : ℕ) = 0
    · simpa [hl] using
        (loweringTwiceFiber_weight_sum_le_tenth_of_one_nonlast_k_zero hl hη hklegal hk_ne_last hk0)
    · by_cases hx : 9 ≤ η (lastFin l hl) + l + 3
      · have hMpos : 1 ≤ η (lastFin l hl) :=
          last_value_pos_of_legal_nonlast hl hklegal hk_ne_last
        have hy : 5 ≤ η (lastFin l hl) + (k : ℕ) + 3 := by omega
        simpa [hl] using
          (loweringTwiceFiber_weight_sum_le_tenth_of_one_nonlast_five_le_y_nine_le_x
            hl hη hklegal hk_ne_last hy hx)
      · have hxlt : η (lastFin l hl) + l + 3 < 9 := by omega
        have hnb : ¬ (η (lastFin l hl) = 1 ∧ (k : ℕ) = 1 ∧ l = 4) :=
          hnotbad k (by simpa [hl] using hklegal) (by simpa [hl] using hk_ne_last)
        simpa [hl] using
          (loweringTwiceFiber_weight_sum_le_tenth_of_one_nonlast_small_x_except_bad
            hl hη hklegal hk_ne_last hxlt hnb)
  · have honly : ∀ k ∈ legalRaiseIndices hl η, k = lastFin l hl := by
      intro k hk
      by_contra hk_ne
      exact hex ⟨k, hk, hk_ne⟩
    simpa [hl] using
      (loweringTwiceFiber_weight_sum_le_tenth_only_last_of_two_le_l hl hl2 hη honly)

/-- In the unique bad local configuration, membership in the support forces total
weight level `N = 2` (indeed the tuple is `![0,0,1,1]`). -/
lemma bad_local_triple_support_eq_two {l N : ℕ} (hl : 0 < l) {η : Fin l → ℕ} {k : Fin l}
    (hη : η ∈ support l N) (hklegal : k ∈ legalRaiseIndices hl η)
    (hk_ne_last : k ≠ lastFin l hl)
    (hbad : η (lastFin l hl) = 1 ∧ (k : ℕ) = 1 ∧ l = 4) :
    N = 2 := by
  classical
  rcases hbad with ⟨hlast, hkval, hl4⟩
  subst l
  have hnd : NondecreasingFin η := (Finset.mem_filter.mp hη).2.1
  have hsum : (∑ i : Fin 4, η i) = N := (Finset.mem_filter.mp hη).2.2
  have hk_mem_corr : k ∈ correctedCandidateRaiseIndices hl η := (Finset.mem_filter.mp hklegal).1
  have hk_mem_pred : k ∈ predecessorRaiseIndices hl η := by
    rw [correctedCandidateRaiseIndices] at hk_mem_corr
    exact (Finset.mem_insert.mp hk_mem_corr).resolve_left hk_ne_last
  have hlast_val : (lastFin 4 hl : ℕ) = 3 := by
    dsimp [lastFin]
  have hlast_fin : lastFin 4 hl = (⟨3, by omega⟩ : Fin 4) := Fin.ext hlast_val
  have hleft_val : (leftmostMax hl η : ℕ) = 2 := by
    rw [predecessorRaiseIndices] at hk_mem_pred
    rcases (Finset.mem_filter.mp hk_mem_pred).2 with ⟨hk_succ_lt, hleft⟩
    have hleft_val' := congrArg Fin.val hleft
    change (leftmostMax hl η : ℕ) = (k : ℕ) + 1 at hleft_val'
    omega
  have hleft : leftmostMax hl η = (⟨2, by omega⟩ : Fin 4) := Fin.ext hleft_val
  have h0 : η (⟨0, by omega⟩ : Fin 4) = 0 := by
    have hlt : η (⟨0, by omega⟩ : Fin 4) < η (leftmostMax hl η) :=
      value_lt_leftmostMax hl hnd (by rw [hleft_val]; norm_num)
    have hval : η (leftmostMax hl η) = 1 := by simpa [hlast] using leftmostMax_value hl η
    omega
  have h1 : η (⟨1, by omega⟩ : Fin 4) = 0 := by
    have hlt : η (⟨1, by omega⟩ : Fin 4) < η (leftmostMax hl η) :=
      value_lt_leftmostMax hl hnd (by rw [hleft_val]; norm_num)
    have hval : η (leftmostMax hl η) = 1 := by simpa [hlast] using leftmostMax_value hl η
    omega
  have h2 : η (⟨2, by omega⟩ : Fin 4) = 1 := by
    simpa [hleft, hlast] using leftmostMax_value hl η
  have h3 : η (⟨3, by omega⟩ : Fin 4) = 1 := by
    simpa [hlast_fin] using hlast
  have h0' : η 0 = 0 := by simpa using h0
  have h1' : η 1 = 0 := by simpa using h1
  have h2' : η 2 = 1 := by simpa using h2
  have h3' : η 3 = 1 := by simpa using h3
  have hsum' : η 0 + η 1 + η 2 + η 3 = N := by
    simpa [Fin.sum_univ_four] using hsum
  omega

/-- Global two-step contraction in all dimensions at least two, except for the one
local/global exceptional point, which is handled separately below. -/
lemma D_three_two_step_contraction_nonexceptional (m s : ℕ) (hm2 : 2 ≤ m)
    (hne : ¬ (m = 4 ∧ s = 2)) :
    D 3 m (s + 2) ≤ ((1 : ℚ) / 10) * D 3 m s := by
  classical
  have hmpos : 0 < m := by omega
  rw [D_eq_sum_loweringTwiceFibers 3 m s hmpos]
  calc
    (∑ η ∈ support m s, ∑ δ ∈ loweringTwiceFiber hmpos s η, weight 3 m δ)
        ≤ ∑ η ∈ support m s, ((1 : ℚ) / 10) * weight 3 m η := by
          refine Finset.sum_le_sum ?_
          intro η hη
          exact loweringTwiceFiber_weight_sum_le_tenth_nonexceptional hm2 hη (by
            intro k hklegal hk_ne_last hbad
            have hs2 : s = 2 :=
              bad_local_triple_support_eq_two hmpos hη hklegal hk_ne_last hbad
            exact hne ⟨hbad.2.2, hs2⟩)
    _ = ((1 : ℚ) / 10) * D 3 m s := by
          rw [D]
          exact (Finset.mul_sum (s := support m s) (f := fun η => weight 3 m η) ((1 : ℚ) / 10)).symm

lemma D_three_two_step_contraction_one (s : ℕ) :
    D 3 1 (s + 2) ≤ ((1 : ℚ) / 10) * D 3 1 s := by
  rw [D_l_one, D_l_one]
  rw [show 3 + (s + 2) = s + 5 by omega, show 3 + s = s + 3 by omega]
  have hfac_nat : Nat.factorial (s + 5) = (s + 5) * (s + 4) * Nat.factorial (s + 3) := by
    rw [show s + 5 = (s + 4) + 1 by omega, Nat.factorial_succ]
    rw [show s + 4 = (s + 3) + 1 by omega, Nat.factorial_succ]
    ring
  rw [hfac_nat]
  field_simp
  have hprod : (10 : ℚ) ≤ (((s + 5) * (s + 4) : ℕ) : ℚ) := by
    have h4 : (4 : ℚ) ≤ ((s + 4 : ℕ) : ℚ) := by exact_mod_cast (by omega : 4 ≤ s + 4)
    have h5 : (5 : ℚ) ≤ ((s + 5 : ℕ) : ℚ) := by exact_mod_cast (by omega : 5 ≤ s + 5)
    have hcast : (((s + 5) * (s + 4) : ℕ) : ℚ) = ((s + 5 : ℕ) : ℚ) * ((s + 4 : ℕ) : ℚ) := by
      norm_num
    nlinarith
  have hfac_ge_one : (1 : ℚ) ≤ (Nat.factorial (s + 3) : ℚ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos (s + 3)))
  have hcast_fac : (((s + 5) * (s + 4) * Nat.factorial (s + 3) : ℕ) : ℚ) =
      (((s + 5) * (s + 4) : ℕ) : ℚ) * (Nat.factorial (s + 3) : ℚ) := by
    norm_num
  nlinarith

/-- The assembled all-`m` two-step contraction for `a = 3`. -/
lemma D_three_two_step_contraction (m s : ℕ) (hm : 1 ≤ m) :
    D 3 m (s + 2) ≤ ((1 : ℚ) / 10) * D 3 m s := by
  by_cases hm1 : m = 1
  · subst m
    exact D_three_two_step_contraction_one s
  · have hm2 : 2 ≤ m := by omega
    by_cases hbad : m = 4 ∧ s = 2
    · rcases hbad with ⟨rfl, rfl⟩
      simpa using D_three_four_two_step_exception
    · exact D_three_two_step_contraction_nonexceptional m s hm2 hbad

/-- Reduction of the main `a=2` zero-extra estimate to the next-level
`a=3` estimate.  The first summand is controlled by the sharp two-step
contraction for `D 3`; the remaining tail is exactly the supplied `F3` bound
and embeds as the zero first-coordinate slice. -/
lemma zero_extra_all_m_from_F3
    (hF3 : ∀ r s : ℕ, 1 ≤ r →
      ((Nat.factorial (r+3) : ℚ) / (Nat.factorial 2 : ℚ)) * D 3 r (s+r+3) ≤
        ((1 : ℚ) / 15) * D 4 r s) :
    ∀ m s : ℕ,
      (Nat.factorial (m+2) : ℚ) * D 2 m (s+m+2) ≤ ((1 : ℚ) / 3) * D 3 m s := by
  intro m s
  cases m with
  | zero =>
      have hz : D 2 0 (s + 0 + 2) = 0 := by
        simpa using D_zero_of_pos (a := 2) (N := s + 0 + 2) (by omega)
      rw [hz]
      simp
      exact D_nonneg 3 0 s
  | succ r =>
      by_cases hr0 : r = 0
      · subst r
        have hsplit := D_split_general_succ 2 0 (s+2)
        have hz : D 3 0 (s + 2 + 1) = 0 := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            D_zero_of_pos (a := 3) (N := s + 3) (by omega)
        have hEqHalf : ((Nat.factorial (1+2) : ℚ) / (Nat.factorial 2 : ℚ)) * D 2 1 (s+1+2) = D 3 1 (s+2) := by
          simpa [hz, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit
        have hEq : (Nat.factorial (1+2) : ℚ) * D 2 1 (s+1+2) = (2:ℚ) * D 3 1 (s+2) := by
          have hfac2 : (Nat.factorial 2 : ℚ) = (2:ℚ) := by norm_num
          have := congrArg (fun x : ℚ => (Nat.factorial 2 : ℚ) * x) hEqHalf
          norm_num at this ⊢
          linarith
        have hstep := D_three_two_step_contraction 1 s (by decide)
        have hnon : 0 ≤ (2:ℚ) := by norm_num
        calc
          (Nat.factorial (1+2) : ℚ) * D 2 1 (s+1+2) = (2:ℚ) * D 3 1 (s+2) := hEq
          _ ≤ (2:ℚ) * (((1:ℚ)/10) * D 3 1 s) := mul_le_mul_of_nonneg_left hstep hnon
          _ ≤ ((1:ℚ)/3) * D 3 1 s := by
            have hD : 0 ≤ D 3 1 s := D_nonneg 3 1 s
            nlinarith
      · have hrpos : 1 ≤ r := by omega
        have hmpos : 1 ≤ r+1 := by omega
        have hsplit := D_split_general_succ 2 r (s+2)
        have hhalf : ((Nat.factorial (r + 3) : ℚ) / (Nat.factorial 2 : ℚ)) * D 2 (r+1) (s + (r+1) + 2) =
            D 3 (r+1) (s+2) + ((Nat.factorial (r + 3) : ℚ) / (Nat.factorial 2 : ℚ)) * D 3 r (s+r+3) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit
        have hmain_eq : (Nat.factorial ((r+1)+2) : ℚ) * D 2 (r+1) (s+(r+1)+2) =
            (2:ℚ) * D 3 (r+1) (s+2) + (Nat.factorial (r+3) : ℚ) * D 3 r (s+r+3) := by
          have h2 : (Nat.factorial 2 : ℚ) = (2:ℚ) := by norm_num
          have := congrArg (fun x : ℚ => (Nat.factorial 2 : ℚ) * x) hhalf
          norm_num [h2] at this ⊢
          linarith
        have hstep := D_three_two_step_contraction (r+1) s hmpos
        have htailF := hF3 r s hrpos
        have htail_embed : D 4 r s ≤ D 3 (r+1) s := by
          simpa using D_ge_zero_tail_general 3 r s
        have htail : (Nat.factorial (r+3) : ℚ) * D 3 r (s+r+3) ≤ ((2:ℚ)/15) * D 3 (r+1) s := by
          have hmul := mul_le_mul_of_nonneg_left htailF (by norm_num : (0:ℚ) ≤ 2)
          have htailF2 : (2:ℚ) * (((Nat.factorial (r+3) : ℚ) / (Nat.factorial 2 : ℚ)) * D 3 r (s+r+3)) ≤
              (2:ℚ) * (((1:ℚ)/15) * D 4 r s) := hmul
          have h2 : (Nat.factorial 2 : ℚ) = (2:ℚ) := by norm_num
          have hnon : 0 ≤ ((2:ℚ)/15) := by norm_num
          calc
            (Nat.factorial (r+3) : ℚ) * D 3 r (s+r+3) =
                (2:ℚ) * (((Nat.factorial (r+3) : ℚ) / (Nat.factorial 2 : ℚ)) * D 3 r (s+r+3)) := by
                  rw [h2]
                  ring
            _ ≤ (2:ℚ) * (((1:ℚ)/15) * D 4 r s) := htailF2
            _ = ((2:ℚ)/15) * D 4 r s := by ring
            _ ≤ ((2:ℚ)/15) * D 3 (r+1) s := mul_le_mul_of_nonneg_left htail_embed hnon
        have hfirst : (2:ℚ) * D 3 (r+1) (s+2) ≤ ((1:ℚ)/5) * D 3 (r+1) s := by
          calc
            (2:ℚ) * D 3 (r+1) (s+2) ≤ (2:ℚ) * (((1:ℚ)/10) * D 3 (r+1) s) :=
              mul_le_mul_of_nonneg_left hstep (by norm_num)
            _ = ((1:ℚ)/5) * D 3 (r+1) s := by ring
        calc
          (Nat.factorial ((r+1)+2) : ℚ) * D 2 (r+1) (s+(r+1)+2)
              = (2:ℚ) * D 3 (r+1) (s+2) + (Nat.factorial (r+3) : ℚ) * D 3 r (s+r+3) := hmain_eq
          _ ≤ ((1:ℚ)/5) * D 3 (r+1) s + ((2:ℚ)/15) * D 3 (r+1) s := add_le_add hfirst htail
          _ = ((1:ℚ)/3) * D 3 (r+1) s := by ring


/-- Factor-scaled shifted `D` quantity used for recursive zero-extra estimates. -/
noncomputable def Fscaled (a l s : ℕ) : ℚ :=
  ((Nat.factorial (a+l) : ℚ) / (Nat.factorial (a-1) : ℚ)) * D a l (s+l+a)


lemma Fscaled_split_succ (a l s : ℕ) (ha : 1 ≤ a) :
    Fscaled a (l+1) s =
      (a : ℚ) * D (a+1) (l+1) (s+a) + (a : ℚ) * Fscaled (a+1) l s := by
  unfold Fscaled
  have hsplit := D_split_general_succ a l (s+a)
  have hfac : ((Nat.factorial (a + (l + 1)) : ℚ) / (Nat.factorial (a - 1) : ℚ)) =
      (a : ℚ) * ((Nat.factorial (a + (l + 1)) : ℚ) / (Nat.factorial a : ℚ)) := by
    have hfactNat : Nat.factorial a = a * Nat.factorial (a-1) := by
      calc
        Nat.factorial a = Nat.factorial ((a-1)+1) := by congr; omega
        _ = ((a-1)+1) * Nat.factorial (a-1) := Nat.factorial_succ (a-1)
        _ = a * Nat.factorial (a-1) := by congr; omega
    have hfactQ : (Nat.factorial a : ℚ) = (a : ℚ) * (Nat.factorial (a-1) : ℚ) := by
      exact_mod_cast hfactNat
    rw [hfactQ]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a-1)),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (a + (l+1)))]
  have hargD : D a (l+1) (s + (l+1) + a) = D a (l+1) ((s+a)+(l+1)) := by
    have h : s + (l+1) + a = (s+a)+(l+1) := by omega
    rw [h]
  have hcoef_tail : ((Nat.factorial (a + (l + 1)) : ℚ) / (Nat.factorial a : ℚ)) =
      ((Nat.factorial ((a+1)+l) : ℚ) / (Nat.factorial ((a+1)-1) : ℚ)) := by
    have hnum : a + (l+1) = (a+1)+l := by omega
    have hden : (a+1)-1 = a := by omega
    rw [hnum, hden]
  have harg_tail : D (a+1) l ((s+a)+(l+1)) = D (a+1) l (s+l+(a+1)) := by
    have h : (s+a)+(l+1) = s+l+(a+1) := by omega
    rw [h]
  calc
    ((Nat.factorial (a + (l + 1)) : ℚ) / (Nat.factorial (a - 1) : ℚ)) *
        D a (l + 1) (s + (l + 1) + a)
        = (a : ℚ) * (((Nat.factorial (a + (l + 1)) : ℚ) / (Nat.factorial a : ℚ)) *
          D a (l+1) ((s+a)+(l+1))) := by
            rw [hfac, hargD]
            ring
    _ = (a : ℚ) * (D (a+1) (l+1) (s+a) +
          ((Nat.factorial (a + (l + 1)) : ℚ) / (Nat.factorial a : ℚ)) * D (a+1) l ((s+a)+(l+1))) := by
            rw [hsplit]
    _ = (a : ℚ) * D (a+1) (l+1) (s+a) + (a : ℚ) *
          (((Nat.factorial ((a+1)+l) : ℚ) / (Nat.factorial ((a+1)-1) : ℚ)) * D (a+1) l (s+l+(a+1))) := by
            rw [hcoef_tail, harg_tail]
            ring

lemma F3_one_fifteenth_r_one (s : ℕ) :
    ((Nat.factorial (1+3) : ℚ) / (Nat.factorial 2 : ℚ)) * D 3 1 (s+1+3) ≤
      ((1 : ℚ) / 15) * D 4 1 s := by
  rw [D_l_one, D_l_one]
  norm_num
  rw [show 3 + (s + 1 + 3) = s + 7 by omega, show 4 + s = s + 4 by omega]

  have hfac : Nat.factorial (s + 7) = (s+7) * (s+6) * (s+5) * Nat.factorial (s+4) := by
    rw [show s+7 = (s+6)+1 by omega, Nat.factorial_succ]
    rw [show s+6 = (s+5)+1 by omega, Nat.factorial_succ]
    rw [show s+5 = (s+4)+1 by omega, Nat.factorial_succ]
    ring
  rw [hfac]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (s+4))]
  have hprod : (45 : ℚ) ≤ (((s+7)*(s+6)*(s+5) : ℕ) : ℚ) := by
    have hprod_nat : 45 ≤ (s+7)*(s+6)*(s+5) := by
      have h1 : 5*6*7 ≤ (s+5)*(s+6)*(s+7) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      have h2 : (s+5)*(s+6)*(s+7) = (s+7)*(s+6)*(s+5) := by ring
      omega
    exact_mod_cast hprod_nat
  have hfac_nonneg : 0 ≤ (Nat.factorial (s+4) : ℚ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hprod hfac_nonneg
  norm_num at hmul ⊢
  nlinarith [hmul]


/-- The requested `1/75` three-step contraction in the one-dimensional case. -/
lemma D_four_three_step_contraction_one_one_seventy_fifth (s : ℕ) :
    D 4 1 (s + 3) ≤ ((1 : ℚ) / 75) * D 4 1 s := by
  rw [D_l_one, D_l_one]
  rw [show 4 + (s + 3) = s + 7 by omega, show 4 + s = s + 4 by omega]
  have hfac : Nat.factorial (s + 7) =
      (s + 7) * (s + 6) * (s + 5) * Nat.factorial (s + 4) := by
    rw [show s + 7 = (s + 6) + 1 by omega, Nat.factorial_succ]
    rw [show s + 6 = (s + 5) + 1 by omega, Nat.factorial_succ]
    rw [show s + 5 = (s + 4) + 1 by omega, Nat.factorial_succ]
    ring
  rw [hfac]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (s + 4))]
  have hprod : (75 : ℚ) ≤ (((s + 7) * (s + 6) * (s + 5) : ℕ) : ℚ) := by
    have hprod_nat : 75 ≤ (s + 7) * (s + 6) * (s + 5) := by
      have h1 : 5 * 6 * 7 ≤ (s + 5) * (s + 6) * (s + 7) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      have h2 : (s + 5) * (s + 6) * (s + 7) = (s + 7) * (s + 6) * (s + 5) := by ring
      omega
    exact_mod_cast hprod_nat
  have hfac_nonneg : 0 ≤ (Nat.factorial (s + 4) : ℚ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hprod hfac_nonneg
  norm_num at hmul ⊢
  nlinarith [hmul]


noncomputable def D42term (N x : ℕ) : ℚ :=
  ((Nat.factorial 4 : ℚ) / (Nat.factorial (4+x) : ℚ)) *
    ((Nat.factorial 5 : ℚ) / (Nat.factorial (5+N-x) : ℚ))

lemma D_4_2_explicit_formula (N : ℕ) :
    D 4 2 N = ∑ x ∈ (Finset.range (N+1)).filter (fun x => 2*x <= N), D42term N x := by
  simpa [D42term] using D_b_two_explicit_formula 4 N

lemma D42term_same_shift_le_one_three336 (x k : ℕ) :
    D42term (x + k + 3) x ≤ ((1 : ℚ) / 336) * D42term (x + k) x := by
  dsimp [D42term]
  rw [show 4 + x = x + 4 by omega,
      show 5 + (x + k + 3) - x = k + 8 by omega,
      show 5 + (x + k) - x = k + 5 by omega]
  have hfac : Nat.factorial (k + 8) =
      (k + 8) * (k + 7) * (k + 6) * Nat.factorial (k + 5) := by
    rw [show k + 8 = (k + 7) + 1 by omega, Nat.factorial_succ]
    rw [show k + 7 = (k + 6) + 1 by omega, Nat.factorial_succ]
    rw [show k + 6 = (k + 5) + 1 by omega, Nat.factorial_succ]
    ring
  rw [hfac]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (x + 4)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k + 5))]
  have hprod : (336 : ℚ) ≤ (((k + 8) * (k + 7) * (k + 6) : ℕ) : ℚ) := by
    have hprod_nat : 336 ≤ (k + 8) * (k + 7) * (k + 6) := by
      have h1 : 8 * 7 * 6 ≤ (k + 8) * (k + 7) * (k + 6) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      norm_num at h1 ⊢
      exact h1
    exact_mod_cast hprod_nat
  have hfact_pos : (0 : ℚ) < (Nat.factorial (k + 5) : ℚ) := by positivity
  norm_num [Nat.cast_mul] at hprod ⊢
  nlinarith [hprod, hfact_pos]

lemma D42term_nonneg (N x : ℕ) : 0 ≤ D42term N x := by
  dsimp [D42term]
  positivity

lemma D42term_even_extra_le_one210 (m : ℕ) :
    D42term (2*m + 3) (m + 1) ≤ ((1 : ℚ) / 210) * D42term (2*m) m := by
  dsimp [D42term]
  rw [show 4 + (m + 1) = m + 5 by omega,
      show 5 + (2*m + 3) - (m + 1) = m + 7 by omega,
      show 4 + m = m + 4 by omega,
      show 5 + (2*m) - m = m + 5 by omega]
  have hfac5 : Nat.factorial (m + 5) = (m + 5) * Nat.factorial (m + 4) := by
    rw [show m + 5 = (m + 4) + 1 by omega, Nat.factorial_succ]
  have hfac7 : Nat.factorial (m + 7) =
      (m + 7) * (m + 6) * (m + 5) * Nat.factorial (m + 4) := by
    rw [show m + 7 = (m + 6) + 1 by omega, Nat.factorial_succ]
    rw [show m + 6 = (m + 5) + 1 by omega, Nat.factorial_succ]
    rw [show m + 5 = (m + 4) + 1 by omega, Nat.factorial_succ]
    ring
  rw [hfac5, hfac7]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 4))]
  have hprod : (210 : ℚ) ≤ (((m + 7) * (m + 6) * (m + 5) : ℕ) : ℚ) := by
    have hprod_nat : 210 ≤ (m + 7) * (m + 6) * (m + 5) := by
      have h1 : 7 * 6 * 5 ≤ (m + 7) * (m + 6) * (m + 5) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      norm_num at h1 ⊢
      exact h1
    exact_mod_cast hprod_nat
  have hfact_pos : (0 : ℚ) < (Nat.factorial (m + 4) : ℚ) := by positivity
  norm_num [Nat.cast_mul] at hprod ⊢
  nlinarith [hprod, hfact_pos]

lemma D42term_odd_extra1_le_one280 (m : ℕ) :
    D42term (2*m + 4) (m + 1) ≤ ((1 : ℚ) / 280) * D42term (2*m + 1) m := by
  dsimp [D42term]
  rw [show 4 + (m + 1) = m + 5 by omega,
      show 5 + (2*m + 4) - (m + 1) = m + 8 by omega,
      show 4 + m = m + 4 by omega,
      show 5 + (2*m + 1) - m = m + 6 by omega]
  have hfac5 : Nat.factorial (m + 5) = (m + 5) * Nat.factorial (m + 4) := by
    rw [show m + 5 = (m + 4) + 1 by omega, Nat.factorial_succ]
  have hfac6 : Nat.factorial (m + 6) = (m + 6) * (m + 5) * Nat.factorial (m + 4) := by
    rw [show m + 6 = (m + 5) + 1 by omega, Nat.factorial_succ]
    rw [show m + 5 = (m + 4) + 1 by omega, Nat.factorial_succ]
    ring
  have hfac8 : Nat.factorial (m + 8) =
      (m + 8) * (m + 7) * Nat.factorial (m + 6) := by
    rw [show m + 8 = (m + 7) + 1 by omega, Nat.factorial_succ]
    rw [show m + 7 = (m + 6) + 1 by omega, Nat.factorial_succ]
    ring
  rw [hfac5, hfac8, hfac6]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 4)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 6))]
  have hprod : (280 : ℚ) ≤ (((m + 5) * (m + 8) * (m + 7) : ℕ) : ℚ) := by
    have hprod_nat : 280 ≤ (m + 5) * (m + 8) * (m + 7) := by
      have h1 : 5 * 8 * 7 ≤ (m + 5) * (m + 8) * (m + 7) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      norm_num at h1 ⊢
      exact h1
    exact_mod_cast hprod_nat
  have h1pos : (0 : ℚ) < (Nat.factorial (m + 4) : ℚ) := by positivity
  have h2pos : (0 : ℚ) < (Nat.factorial (m + 6) : ℚ) := by positivity
  norm_num [Nat.cast_mul] at hprod ⊢
  have hcommon_nonneg : 0 ≤ (↑m + 6) * (↑m + 5) *
      (Nat.factorial (m + 4) : ℚ) * (Nat.factorial (m + 4) : ℚ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hprod hcommon_nonneg
  nlinarith [hmul, h1pos, h2pos]

lemma D42term_odd_extra2_le_one210 (m : ℕ) :
    D42term (2*m + 4) (m + 2) ≤ ((1 : ℚ) / 210) * D42term (2*m + 1) m := by
  dsimp [D42term]
  rw [show 4 + (m + 2) = m + 6 by omega,
      show 5 + (2*m + 4) - (m + 2) = m + 7 by omega,
      show 4 + m = m + 4 by omega,
      show 5 + (2*m + 1) - m = m + 6 by omega]
  have hfac6 : Nat.factorial (m + 6) =
      (m + 6) * (m + 5) * Nat.factorial (m + 4) := by
    rw [show m + 6 = (m + 5) + 1 by omega, Nat.factorial_succ]
    rw [show m + 5 = (m + 4) + 1 by omega, Nat.factorial_succ]
    ring
  have hfac7 : Nat.factorial (m + 7) = (m + 7) * Nat.factorial (m + 6) := by
    rw [show m + 7 = (m + 6) + 1 by omega, Nat.factorial_succ]
  rw [hfac7]
  repeat rw [hfac6]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 4)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 6))]
  have hprod : (210 : ℚ) ≤ (((m + 6) * (m + 5) * (m + 7) : ℕ) : ℚ) := by
    have hprod_nat : 210 ≤ (m + 6) * (m + 5) * (m + 7) := by
      have h1 : 6 * 5 * 7 ≤ (m + 6) * (m + 5) * (m + 7) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)


      norm_num at h1 ⊢
      exact h1
    exact_mod_cast hprod_nat
  have h1pos : (0 : ℚ) < (Nat.factorial (m + 4) : ℚ) := by positivity
  have h2pos : (0 : ℚ) < (Nat.factorial (m + 6) : ℚ) := by positivity
  norm_num [Nat.cast_mul] at hprod ⊢
  nlinarith [hprod, h1pos, h2pos]

private lemma D42_even_source_filter (m : ℕ) :
    (Finset.range (2*m + 3 + 1)).filter (fun x => 2*x ≤ 2*m + 3) = Finset.range (m + 2) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro hx
    omega
  · intro hx
    omega

private lemma D42_even_target_filter (m : ℕ) :
    (Finset.range (2*m + 1)).filter (fun x => 2*x ≤ 2*m) = Finset.range (m + 1) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro hx
    omega
  · intro hx
    omega

private lemma D42_odd_source_filter (m : ℕ) :
    (Finset.range (2*m + 4 + 1)).filter (fun x => 2*x ≤ 2*m + 4) = Finset.range (m + 3) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro hx
    omega
  · intro hx
    omega

private lemma D42_odd_target_filter (m : ℕ) :
    (Finset.range (2*m + 1 + 1)).filter (fun x => 2*x ≤ 2*m + 1) = Finset.range (m + 1) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro hx
    omega
  · intro hx
    omega

lemma D_four_three_step_contraction_two_one_seventy_fifth_even (m : ℕ) :
    D 4 2 (2*m + 3) ≤ ((1 : ℚ) / 75) * D 4 2 (2*m) := by
  rw [D_4_2_explicit_formula, D_4_2_explicit_formula]
  rw [D42_even_source_filter, D42_even_target_filter]
  rw [show m + 2 = (m + 1) + 1 by omega, Finset.sum_range_succ]
  set T : ℚ := ∑ x ∈ Finset.range (m + 1), D42term (2*m) x
  have hmain : (∑ x ∈ Finset.range (m + 1), D42term (2*m + 3) x) ≤ ((1 : ℚ) / 336) * T := by
    dsimp [T]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro x hx
    have hxlt : x < m + 1 := Finset.mem_range.mp hx
    have hxle : x ≤ 2*m := by omega
    simpa [show x + (2*m - x) = 2*m by omega,
      show x + (2*m - x) + 3 = 2*m + 3 by omega] using
      D42term_same_shift_le_one_three336 x (2*m - x)
  have hlast_le : D42term (2*m) m ≤ T := by
    dsimp [T]
    exact Finset.single_le_sum (by intro x hx; exact D42term_nonneg (2*m) x)
      (by simp : m ∈ Finset.range (m + 1))
  have hextra : D42term (2*m + 3) (m + 1) ≤ ((1 : ℚ) / 210) * T := by
    exact le_trans (D42term_even_extra_le_one210 m)
      (mul_le_mul_of_nonneg_left hlast_le (by norm_num))
  have hTnon : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg (by intro x hx; exact D42term_nonneg (2*m) x)
  calc
    (∑ x ∈ Finset.range (m + 1), D42term (2*m + 3) x) + D42term (2*m + 3) (m + 1)
        ≤ ((1 : ℚ) / 336) * T + ((1 : ℚ) / 210) * T := add_le_add hmain hextra
    _ ≤ ((1 : ℚ) / 75) * T := by
      have hc : ((1 : ℚ) / 336) + ((1 : ℚ) / 210) ≤ (1 : ℚ) / 75 := by norm_num
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right hc hTnon

lemma D_four_three_step_contraction_two_one_seventy_fifth_odd (m : ℕ) :
    D 4 2 (2*m + 1 + 3) ≤ ((1 : ℚ) / 75) * D 4 2 (2*m + 1) := by
  rw [show 2*m + 1 + 3 = 2*m + 4 by omega]
  rw [D_4_2_explicit_formula, D_4_2_explicit_formula]
  rw [D42_odd_source_filter, D42_odd_target_filter]
  rw [show m + 3 = (m + 2) + 1 by omega, Finset.sum_range_succ]
  rw [show m + 2 = (m + 1) + 1 by omega, Finset.sum_range_succ]
  set T : ℚ := ∑ x ∈ Finset.range (m + 1), D42term (2*m + 1) x
  have hmain : (∑ x ∈ Finset.range (m + 1), D42term (2*m + 4) x) ≤ ((1 : ℚ) / 336) * T := by
    dsimp [T]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro x hx
    have hxlt : x < m + 1 := Finset.mem_range.mp hx
    have hxle : x ≤ 2*m + 1 := by omega
    simpa [show x + (2*m + 1 - x) = 2*m + 1 by omega,
      show x + (2*m + 1 - x) + 3 = 2*m + 4 by omega] using
      D42term_same_shift_le_one_three336 x (2*m + 1 - x)
  have hlast_le : D42term (2*m + 1) m ≤ T := by
    dsimp [T]
    exact Finset.single_le_sum (by intro x hx; exact D42term_nonneg (2*m + 1) x)
      (by simp : m ∈ Finset.range (m + 1))
  have hextra1 : D42term (2*m + 4) (m + 1) ≤ ((1 : ℚ) / 280) * T := by
    exact le_trans (D42term_odd_extra1_le_one280 m)
      (mul_le_mul_of_nonneg_left hlast_le (by norm_num))
  have hextra2 : D42term (2*m + 4) (m + 2) ≤ ((1 : ℚ) / 210) * T := by
    exact le_trans (D42term_odd_extra2_le_one210 m)
      (mul_le_mul_of_nonneg_left hlast_le (by norm_num))
  have hTnon : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg (by intro x hx; exact D42term_nonneg (2*m + 1) x)
  calc
    (∑ x ∈ Finset.range (m + 1), D42term (2*m + 4) x) + D42term (2*m + 4) (m + 1) +
        D42term (2*m + 4) (m + 2)
        ≤ ((1 : ℚ) / 336) * T + ((1 : ℚ) / 280) * T + ((1 : ℚ) / 210) * T := by
          exact add_le_add (add_le_add hmain hextra1) hextra2
    _ ≤ ((1 : ℚ) / 75) * T := by
      have hc : ((1 : ℚ) / 336) + ((1 : ℚ) / 280) + ((1 : ℚ) / 210) ≤ (1 : ℚ) / 75 := by norm_num
      rw [← add_mul, ← add_mul]
      exact mul_le_mul_of_nonneg_right hc hTnon

lemma D_four_three_step_contraction_two_one_seventy_fifth (s : ℕ) :
    D 4 2 (s+3) ≤ ((1:ℚ)/75) * D 4 2 s := by
  rcases Nat.even_or_odd s with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      D_four_three_step_contraction_two_one_seventy_fifth_even m
  · simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      D_four_three_step_contraction_two_one_seventy_fifth_odd m




noncomputable def D52term (N x : ℕ) : ℚ :=
  ((Nat.factorial 5 : ℚ) / (Nat.factorial (5+x) : ℚ)) *
    ((Nat.factorial 6 : ℚ) / (Nat.factorial (6+N-x) : ℚ))

lemma D_5_2_explicit_formula (N : ℕ) :
    D 5 2 N = ∑ x ∈ (Finset.range (N+1)).filter (fun x => 2*x <= N), D52term N x := by
  simpa [D52term] using D_b_two_explicit_formula 5 N

lemma D52term_nonneg (N x : ℕ) : 0 ≤ D52term N x := by
  dsimp [D52term]
  positivity

lemma D52term_same_shift_le_one_504 (x k : ℕ) :
    D52term (x + k + 3) x ≤ ((1 : ℚ) / 504) * D52term (x + k) x := by
  dsimp [D52term]
  rw [show 5 + x = x + 5 by omega,
      show 6 + (x + k + 3) - x = k + 9 by omega,
      show 6 + (x + k) - x = k + 6 by omega]
  have hfac : Nat.factorial (k + 9) =
      (k + 9) * (k + 8) * (k + 7) * Nat.factorial (k + 6) := by
    rw [show k + 9 = (k + 8) + 1 by omega, Nat.factorial_succ]
    rw [show k + 8 = (k + 7) + 1 by omega, Nat.factorial_succ]
    rw [show k + 7 = (k + 6) + 1 by omega, Nat.factorial_succ]
    ring
  rw [hfac]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (x + 5)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k + 6))]
  have hprod : (504 : ℚ) ≤ (((k + 9) * (k + 8) * (k + 7) : ℕ) : ℚ) := by
    have hprod_nat : 504 ≤ (k + 9) * (k + 8) * (k + 7) := by
      have h1 : 9 * 8 * 7 ≤ (k + 9) * (k + 8) * (k + 7) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      norm_num at h1 ⊢
      exact h1
    exact_mod_cast hprod_nat
  have hfact_pos : (0 : ℚ) < (Nat.factorial (k + 6) : ℚ) := by positivity
  norm_num [Nat.cast_mul] at hprod ⊢
  nlinarith [hprod, hfact_pos]

lemma D52term_even_extra_le_one336 (m : ℕ) :
    D52term (2*m + 3) (m + 1) ≤ ((1 : ℚ) / 336) * D52term (2*m) m := by
  dsimp [D52term]
  rw [show 5 + (m + 1) = m + 6 by omega,
      show 6 + (2*m + 3) - (m + 1) = m + 8 by omega,
      show 5 + m = m + 5 by omega,
      show 6 + (2*m) - m = m + 6 by omega]
  have hfac8 : Nat.factorial (m + 8) =
      (m + 8) * (m + 7) * (m + 6) * Nat.factorial (m + 5) := by
    rw [show m + 8 = (m + 7) + 1 by omega, Nat.factorial_succ]
    rw [show m + 7 = (m + 6) + 1 by omega, Nat.factorial_succ]
    rw [show m + 6 = (m + 5) + 1 by omega, Nat.factorial_succ]
    ring
  have hfac6 : Nat.factorial (m + 6) = (m + 6) * Nat.factorial (m + 5) := by
    rw [show m + 6 = (m + 5) + 1 by omega, Nat.factorial_succ]
  rw [hfac8, hfac6]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 5))]
  have hprod : (336 : ℚ) ≤ (((m + 8) * (m + 7) * (m + 6) : ℕ) : ℚ) := by
    have hprod_nat : 336 ≤ (m + 8) * (m + 7) * (m + 6) := by
      have h1 : 8 * 7 * 6 ≤ (m + 8) * (m + 7) * (m + 6) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      norm_num at h1 ⊢
      exact h1
    exact_mod_cast hprod_nat
  have hfact_pos : (0 : ℚ) < (Nat.factorial (m + 5) : ℚ) := by positivity
  norm_num [Nat.cast_mul] at hprod ⊢
  nlinarith [hprod, hfact_pos]

lemma D52term_odd_extra1_le_one432 (m : ℕ) :
    D52term (2*m + 4) (m + 1) ≤ ((1 : ℚ) / 432) * D52term (2*m + 1) m := by
  dsimp [D52term]
  rw [show 5 + (m + 1) = m + 6 by omega,
      show 6 + (2*m + 4) - (m + 1) = m + 9 by omega,
      show 5 + m = m + 5 by omega,
      show 6 + (2*m + 1) - m = m + 7 by omega]
  have hfac6 : Nat.factorial (m + 6) = (m + 6) * Nat.factorial (m + 5) := by
    rw [show m + 6 = (m + 5) + 1 by omega, Nat.factorial_succ]
  have hfac7 : Nat.factorial (m + 7) = (m + 7) * (m + 6) * Nat.factorial (m + 5) := by
    rw [show m + 7 = (m + 6) + 1 by omega, Nat.factorial_succ]
    rw [show m + 6 = (m + 5) + 1 by omega, Nat.factorial_succ]
    ring
  have hfac9 : Nat.factorial (m + 9) =
      (m + 9) * (m + 8) * Nat.factorial (m + 7) := by
    rw [show m + 9 = (m + 8) + 1 by omega, Nat.factorial_succ]
    rw [show m + 8 = (m + 7) + 1 by omega, Nat.factorial_succ]
    ring
  rw [hfac6, hfac9, hfac7]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 5)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 7))]
  have hprod : (432 : ℚ) ≤ (((m + 6) * (m + 9) * (m + 8) : ℕ) : ℚ) := by
    have hprod_nat : 432 ≤ (m + 6) * (m + 9) * (m + 8) := by
      have h1 : 6 * 9 * 8 ≤ (m + 6) * (m + 9) * (m + 8) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      norm_num at h1 ⊢
      exact h1
    exact_mod_cast hprod_nat
  have h1pos : (0 : ℚ) < (Nat.factorial (m + 5) : ℚ) := by positivity
  have h2pos : (0 : ℚ) < (Nat.factorial (m + 7) : ℚ) := by positivity
  norm_num [Nat.cast_mul] at hprod ⊢
  have hcommon_nonneg : 0 ≤ (↑m + 7) * (↑m + 6) *
      (Nat.factorial (m + 5) : ℚ) * (Nat.factorial (m + 5) : ℚ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hprod hcommon_nonneg
  nlinarith [hmul, h1pos, h2pos]

lemma D52term_odd_extra2_le_one336 (m : ℕ) :
    D52term (2*m + 4) (m + 2) ≤ ((1 : ℚ) / 336) * D52term (2*m + 1) m := by
  dsimp [D52term]
  rw [show 5 + (m + 2) = m + 7 by omega,
      show 6 + (2*m + 4) - (m + 2) = m + 8 by omega,
      show 5 + m = m + 5 by omega,
      show 6 + (2*m + 1) - m = m + 7 by omega]
  have hfac7 : Nat.factorial (m + 7) =
      (m + 7) * (m + 6) * Nat.factorial (m + 5) := by
    rw [show m + 7 = (m + 6) + 1 by omega, Nat.factorial_succ]
    rw [show m + 6 = (m + 5) + 1 by omega, Nat.factorial_succ]
    ring
  have hfac8 : Nat.factorial (m + 8) = (m + 8) * Nat.factorial (m + 7) := by
    rw [show m + 8 = (m + 7) + 1 by omega, Nat.factorial_succ]
  rw [hfac8]
  repeat rw [hfac7]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 5)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 7))]
  have hprod : (336 : ℚ) ≤ (((m + 7) * (m + 6) * (m + 8) : ℕ) : ℚ) := by
    have hprod_nat : 336 ≤ (m + 7) * (m + 6) * (m + 8) := by
      have h1 : 7 * 6 * 8 ≤ (m + 7) * (m + 6) * (m + 8) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      norm_num at h1 ⊢
      exact h1
    exact_mod_cast hprod_nat
  have h1pos : (0 : ℚ) < (Nat.factorial (m + 5) : ℚ) := by positivity
  have h2pos : (0 : ℚ) < (Nat.factorial (m + 7) : ℚ) := by positivity
  norm_num [Nat.cast_mul] at hprod ⊢
  nlinarith [hprod, h1pos, h2pos]

lemma D_five_two_step_contraction_three_three_fiftieths_even (m : ℕ) :
    D 5 2 (2*m + 3) ≤ ((3 : ℚ) / 350) * D 5 2 (2*m) := by
  rw [D_5_2_explicit_formula, D_5_2_explicit_formula]
  rw [D42_even_source_filter, D42_even_target_filter]
  rw [show m + 2 = (m + 1) + 1 by omega, Finset.sum_range_succ]
  set T : ℚ := ∑ x ∈ Finset.range (m + 1), D52term (2*m) x
  have hmain : (∑ x ∈ Finset.range (m + 1), D52term (2*m + 3) x) ≤ ((1 : ℚ) / 504) * T := by
    dsimp [T]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro x hx
    have hxlt : x < m + 1 := Finset.mem_range.mp hx
    have hxle : x ≤ 2*m := by omega
    simpa [show x + (2*m - x) = 2*m by omega,
      show x + (2*m - x) + 3 = 2*m + 3 by omega] using
      D52term_same_shift_le_one_504 x (2*m - x)
  have hlast_le : D52term (2*m) m ≤ T := by
    dsimp [T]
    exact Finset.single_le_sum (by intro x hx; exact D52term_nonneg (2*m) x)
      (by simp : m ∈ Finset.range (m + 1))
  have hextra : D52term (2*m + 3) (m + 1) ≤ ((1 : ℚ) / 336) * T := by
    exact le_trans (D52term_even_extra_le_one336 m)
      (mul_le_mul_of_nonneg_left hlast_le (by norm_num))
  have hTnon : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg (by intro x hx; exact D52term_nonneg (2*m) x)
  calc
    (∑ x ∈ Finset.range (m + 1), D52term (2*m + 3) x) + D52term (2*m + 3) (m + 1)
        ≤ ((1 : ℚ) / 504) * T + ((1 : ℚ) / 336) * T := add_le_add hmain hextra
    _ ≤ ((3 : ℚ) / 350) * T := by
      have hc : ((1 : ℚ) / 504) + ((1 : ℚ) / 336) ≤ (3 : ℚ) / 350 := by norm_num
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right hc hTnon

lemma D_five_two_step_contraction_three_three_fiftieths_odd (m : ℕ) :
    D 5 2 (2*m + 1 + 3) ≤ ((3 : ℚ) / 350) * D 5 2 (2*m + 1) := by
  rw [show 2*m + 1 + 3 = 2*m + 4 by omega]
  rw [D_5_2_explicit_formula, D_5_2_explicit_formula]
  rw [D42_odd_source_filter, D42_odd_target_filter]
  rw [show m + 3 = (m + 2) + 1 by omega, Finset.sum_range_succ]
  rw [show m + 2 = (m + 1) + 1 by omega, Finset.sum_range_succ]
  set T : ℚ := ∑ x ∈ Finset.range (m + 1), D52term (2*m + 1) x
  have hmain : (∑ x ∈ Finset.range (m + 1), D52term (2*m + 4) x) ≤ ((1 : ℚ) / 504) * T := by
    dsimp [T]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro x hx
    have hxlt : x < m + 1 := Finset.mem_range.mp hx
    have hxle : x ≤ 2*m + 1 := by omega
    simpa [show x + (2*m + 1 - x) = 2*m + 1 by omega,
      show x + (2*m + 1 - x) + 3 = 2*m + 4 by omega] using
      D52term_same_shift_le_one_504 x (2*m + 1 - x)
  have hlast_le : D52term (2*m + 1) m ≤ T := by
    dsimp [T]
    exact Finset.single_le_sum (by intro x hx; exact D52term_nonneg (2*m + 1) x)
      (by simp : m ∈ Finset.range (m + 1))
  have hextra1 : D52term (2*m + 4) (m + 1) ≤ ((1 : ℚ) / 432) * T := by
    exact le_trans (D52term_odd_extra1_le_one432 m)
      (mul_le_mul_of_nonneg_left hlast_le (by norm_num))
  have hextra2 : D52term (2*m + 4) (m + 2) ≤ ((1 : ℚ) / 336) * T := by
    exact le_trans (D52term_odd_extra2_le_one336 m)
      (mul_le_mul_of_nonneg_left hlast_le (by norm_num))
  have hTnon : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg (by intro x hx; exact D52term_nonneg (2*m + 1) x)
  calc
    (∑ x ∈ Finset.range (m + 1), D52term (2*m + 4) x) + D52term (2*m + 4) (m + 1) +
        D52term (2*m + 4) (m + 2)
        ≤ ((1 : ℚ) / 504) * T + ((1 : ℚ) / 432) * T + ((1 : ℚ) / 336) * T := by
          exact add_le_add (add_le_add hmain hextra1) hextra2
    _ ≤ ((3 : ℚ) / 350) * T := by
      have hc : ((1 : ℚ) / 504) + ((1 : ℚ) / 432) + ((1 : ℚ) / 336) ≤ (3 : ℚ) / 350 := by norm_num
      rw [← add_mul, ← add_mul]
      exact mul_le_mul_of_nonneg_right hc hTnon

lemma D_five_two_step_contraction_three_three_fiftieths (s : ℕ) :
    D 5 2 (s+3) ≤ ((3:ℚ)/350) * D 5 2 s := by
  rcases Nat.even_or_odd s with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      D_five_two_step_contraction_three_three_fiftieths_even m
  · simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      D_five_two_step_contraction_three_three_fiftieths_odd m



noncomputable def D62term (N x : ℕ) : ℚ :=
  ((Nat.factorial 6 : ℚ) / (Nat.factorial (6+x) : ℚ)) *
    ((Nat.factorial 7 : ℚ) / (Nat.factorial (7+N-x) : ℚ))

lemma D_6_2_explicit_formula (N : ℕ) :
    D 6 2 N = ∑ x ∈ (Finset.range (N+1)).filter (fun x => 2*x <= N), D62term N x := by
  simpa [D62term] using D_b_two_explicit_formula 6 N

lemma D62term_nonneg (N x : ℕ) : 0 ≤ D62term N x := by
  dsimp [D62term]
  positivity

lemma D62term_same_shift_le_one_720 (x k : ℕ) :
    D62term (x + k + 3) x ≤ ((1 : ℚ) / 720) * D62term (x + k) x := by
  dsimp [D62term]
  rw [show 6 + x = x + 6 by omega,
      show 7 + (x + k + 3) - x = k + 10 by omega,
      show 7 + (x + k) - x = k + 7 by omega]
  have hfac : Nat.factorial (k + 10) =
      (k + 10) * (k + 9) * (k + 8) * Nat.factorial (k + 7) := by
    rw [show k + 10 = (k + 9) + 1 by omega, Nat.factorial_succ]
    rw [show k + 9 = (k + 8) + 1 by omega, Nat.factorial_succ]
    rw [show k + 8 = (k + 7) + 1 by omega, Nat.factorial_succ]
    ring
  rw [hfac]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (x + 6)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k + 7))]
  have hprod : (720 : ℚ) ≤ (((k + 10) * (k + 9) * (k + 8) : ℕ) : ℚ) := by
    have hprod_nat : 720 ≤ (k + 10) * (k + 9) * (k + 8) := by
      have h1 : 10 * 9 * 8 ≤ (k + 10) * (k + 9) * (k + 8) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      norm_num at h1 ⊢
      exact h1
    exact_mod_cast hprod_nat
  have hfact_pos : (0 : ℚ) < (Nat.factorial (k + 7) : ℚ) := by positivity
  norm_num [Nat.cast_mul] at hprod ⊢
  nlinarith [hprod, hfact_pos]

lemma D62term_even_extra_le_one504 (m : ℕ) :
    D62term (2*m + 3) (m + 1) ≤ ((1 : ℚ) / 504) * D62term (2*m) m := by
  dsimp [D62term]
  rw [show 6 + (m + 1) = m + 7 by omega,
      show 7 + (2*m + 3) - (m + 1) = m + 9 by omega,
      show 6 + m = m + 6 by omega,
      show 7 + (2*m) - m = m + 7 by omega]
  have hfac9 : Nat.factorial (m + 9) =
      (m + 9) * (m + 8) * (m + 7) * Nat.factorial (m + 6) := by
    rw [show m + 9 = (m + 8) + 1 by omega, Nat.factorial_succ]
    rw [show m + 8 = (m + 7) + 1 by omega, Nat.factorial_succ]
    rw [show m + 7 = (m + 6) + 1 by omega, Nat.factorial_succ]
    ring
  have hfac7 : Nat.factorial (m + 7) = (m + 7) * Nat.factorial (m + 6) := by
    rw [show m + 7 = (m + 6) + 1 by omega, Nat.factorial_succ]
  rw [hfac9, hfac7]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 6))]
  have hprod : (504 : ℚ) ≤ (((m + 9) * (m + 8) * (m + 7) : ℕ) : ℚ) := by
    have hprod_nat : 504 ≤ (m + 9) * (m + 8) * (m + 7) := by
      have h1 : 9 * 8 * 7 ≤ (m + 9) * (m + 8) * (m + 7) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      norm_num at h1 ⊢
      exact h1
    exact_mod_cast hprod_nat
  have hfact_pos : (0 : ℚ) < (Nat.factorial (m + 6) : ℚ) := by positivity
  norm_num [Nat.cast_mul] at hprod ⊢
  nlinarith [hprod, hfact_pos]

lemma D62term_odd_extra1_le_one630 (m : ℕ) :
    D62term (2*m + 4) (m + 1) ≤ ((1 : ℚ) / 630) * D62term (2*m + 1) m := by
  dsimp [D62term]
  rw [show 6 + (m + 1) = m + 7 by omega,
      show 7 + (2*m + 4) - (m + 1) = m + 10 by omega,
      show 6 + m = m + 6 by omega,
      show 7 + (2*m + 1) - m = m + 8 by omega]
  have hfac7 : Nat.factorial (m + 7) = (m + 7) * Nat.factorial (m + 6) := by
    rw [show m + 7 = (m + 6) + 1 by omega, Nat.factorial_succ]
  have hfac8 : Nat.factorial (m + 8) = (m + 8) * (m + 7) * Nat.factorial (m + 6) := by
    rw [show m + 8 = (m + 7) + 1 by omega, Nat.factorial_succ]
    rw [show m + 7 = (m + 6) + 1 by omega, Nat.factorial_succ]
    ring
  have hfac10 : Nat.factorial (m + 10) =
      (m + 10) * (m + 9) * Nat.factorial (m + 8) := by
    rw [show m + 10 = (m + 9) + 1 by omega, Nat.factorial_succ]
    rw [show m + 9 = (m + 8) + 1 by omega, Nat.factorial_succ]
    ring
  rw [hfac7, hfac10, hfac8]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 6)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 8))]
  have hprod : (630 : ℚ) ≤ (((m + 7) * (m + 10) * (m + 9) : ℕ) : ℚ) := by
    have hprod_nat : 630 ≤ (m + 7) * (m + 10) * (m + 9) := by
      have h1 : 7 * 10 * 9 ≤ (m + 7) * (m + 10) * (m + 9) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      norm_num at h1 ⊢
      exact h1
    exact_mod_cast hprod_nat
  have h1pos : (0 : ℚ) < (Nat.factorial (m + 6) : ℚ) := by positivity
  have h2pos : (0 : ℚ) < (Nat.factorial (m + 8) : ℚ) := by positivity
  norm_num [Nat.cast_mul] at hprod ⊢
  have hcommon_nonneg : 0 ≤ (↑m + 8) * (↑m + 7) *
      (Nat.factorial (m + 6) : ℚ) * (Nat.factorial (m + 6) : ℚ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hprod hcommon_nonneg
  nlinarith [hmul, h1pos, h2pos]

lemma D62term_odd_extra2_le_one504 (m : ℕ) :
    D62term (2*m + 4) (m + 2) ≤ ((1 : ℚ) / 504) * D62term (2*m + 1) m := by
  dsimp [D62term]
  rw [show 6 + (m + 2) = m + 8 by omega,
      show 7 + (2*m + 4) - (m + 2) = m + 9 by omega,
      show 6 + m = m + 6 by omega,
      show 7 + (2*m + 1) - m = m + 8 by omega]
  have hfac8 : Nat.factorial (m + 8) =
      (m + 8) * (m + 7) * Nat.factorial (m + 6) := by
    rw [show m + 8 = (m + 7) + 1 by omega, Nat.factorial_succ]
    rw [show m + 7 = (m + 6) + 1 by omega, Nat.factorial_succ]
    ring
  have hfac9 : Nat.factorial (m + 9) = (m + 9) * Nat.factorial (m + 8) := by
    rw [show m + 9 = (m + 8) + 1 by omega, Nat.factorial_succ]
  rw [hfac9]
  repeat rw [hfac8]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 6)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 8))]
  have hprod : (504 : ℚ) ≤ (((m + 8) * (m + 7) * (m + 9) : ℕ) : ℚ) := by
    have hprod_nat : 504 ≤ (m + 8) * (m + 7) * (m + 9) := by
      have h1 : 8 * 7 * 9 ≤ (m + 8) * (m + 7) * (m + 9) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      norm_num at h1 ⊢
      exact h1
    exact_mod_cast hprod_nat
  have h1pos : (0 : ℚ) < (Nat.factorial (m + 6) : ℚ) := by positivity
  have h2pos : (0 : ℚ) < (Nat.factorial (m + 8) : ℚ) := by positivity
  norm_num [Nat.cast_mul] at hprod ⊢
  nlinarith [hprod, h1pos, h2pos]

lemma D_six_two_step_contraction_fortyseven_over_8400_even (m : ℕ) :
    D 6 2 (2*m + 3) ≤ ((47 : ℚ) / 8400) * D 6 2 (2*m) := by
  rw [D_6_2_explicit_formula, D_6_2_explicit_formula]
  rw [D42_even_source_filter, D42_even_target_filter]
  rw [show m + 2 = (m + 1) + 1 by omega, Finset.sum_range_succ]
  set T : ℚ := ∑ x ∈ Finset.range (m + 1), D62term (2*m) x
  have hmain : (∑ x ∈ Finset.range (m + 1), D62term (2*m + 3) x) ≤ ((1 : ℚ) / 720) * T := by
    dsimp [T]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro x hx
    have hxlt : x < m + 1 := Finset.mem_range.mp hx
    have hxle : x ≤ 2*m := by omega
    simpa [show x + (2*m - x) = 2*m by omega,
      show x + (2*m - x) + 3 = 2*m + 3 by omega] using
      D62term_same_shift_le_one_720 x (2*m - x)
  have hlast_le : D62term (2*m) m ≤ T := by
    dsimp [T]
    exact Finset.single_le_sum (by intro x hx; exact D62term_nonneg (2*m) x)
      (by simp : m ∈ Finset.range (m + 1))
  have hextra : D62term (2*m + 3) (m + 1) ≤ ((1 : ℚ) / 504) * T := by
    exact le_trans (D62term_even_extra_le_one504 m)
      (mul_le_mul_of_nonneg_left hlast_le (by norm_num))
  have hTnon : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg (by intro x hx; exact D62term_nonneg (2*m) x)
  calc
    (∑ x ∈ Finset.range (m + 1), D62term (2*m + 3) x) + D62term (2*m + 3) (m + 1)
        ≤ ((1 : ℚ) / 720) * T + ((1 : ℚ) / 504) * T := add_le_add hmain hextra
    _ ≤ ((47 : ℚ) / 8400) * T := by
      have hc : ((1 : ℚ) / 720) + ((1 : ℚ) / 504) ≤ (47 : ℚ) / 8400 := by norm_num
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right hc hTnon

lemma D_six_two_step_contraction_fortyseven_over_8400_odd (m : ℕ) :
    D 6 2 (2*m + 1 + 3) ≤ ((47 : ℚ) / 8400) * D 6 2 (2*m + 1) := by
  rw [show 2*m + 1 + 3 = 2*m + 4 by omega]
  rw [D_6_2_explicit_formula, D_6_2_explicit_formula]
  rw [D42_odd_source_filter, D42_odd_target_filter]
  rw [show m + 3 = (m + 2) + 1 by omega, Finset.sum_range_succ]
  rw [show m + 2 = (m + 1) + 1 by omega, Finset.sum_range_succ]
  set T : ℚ := ∑ x ∈ Finset.range (m + 1), D62term (2*m + 1) x
  have hmain : (∑ x ∈ Finset.range (m + 1), D62term (2*m + 4) x) ≤ ((1 : ℚ) / 720) * T := by
    dsimp [T]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro x hx
    have hxlt : x < m + 1 := Finset.mem_range.mp hx
    have hxle : x ≤ 2*m + 1 := by omega
    simpa [show x + (2*m + 1 - x) = 2*m + 1 by omega,
      show x + (2*m + 1 - x) + 3 = 2*m + 4 by omega] using
      D62term_same_shift_le_one_720 x (2*m + 1 - x)
  have hlast_le : D62term (2*m + 1) m ≤ T := by
    dsimp [T]
    exact Finset.single_le_sum (by intro x hx; exact D62term_nonneg (2*m + 1) x)
      (by simp : m ∈ Finset.range (m + 1))
  have hextra1 : D62term (2*m + 4) (m + 1) ≤ ((1 : ℚ) / 630) * T := by
    exact le_trans (D62term_odd_extra1_le_one630 m)
      (mul_le_mul_of_nonneg_left hlast_le (by norm_num))
  have hextra2 : D62term (2*m + 4) (m + 2) ≤ ((1 : ℚ) / 504) * T := by
    exact le_trans (D62term_odd_extra2_le_one504 m)
      (mul_le_mul_of_nonneg_left hlast_le (by norm_num))
  have hTnon : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg (by intro x hx; exact D62term_nonneg (2*m + 1) x)
  calc
    (∑ x ∈ Finset.range (m + 1), D62term (2*m + 4) x) + D62term (2*m + 4) (m + 1) +
        D62term (2*m + 4) (m + 2)
        ≤ ((1 : ℚ) / 720) * T + ((1 : ℚ) / 630) * T + ((1 : ℚ) / 504) * T := by
          exact add_le_add (add_le_add hmain hextra1) hextra2
    _ ≤ ((47 : ℚ) / 8400) * T := by
      have hc : ((1 : ℚ) / 720) + ((1 : ℚ) / 630) + ((1 : ℚ) / 504) ≤ (47 : ℚ) / 8400 := by norm_num
      rw [← add_mul, ← add_mul]
      exact mul_le_mul_of_nonneg_right hc hTnon

lemma D_six_two_step_contraction_fortyseven_over_8400 (s : ℕ) :
    D 6 2 (s+3) ≤ ((47:ℚ)/8400) * D 6 2 s := by
  rcases Nat.even_or_odd s with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      D_six_two_step_contraction_fortyseven_over_8400_even m
  · simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      D_six_two_step_contraction_fortyseven_over_8400_odd m



noncomputable def D72term (N x : ℕ) : ℚ :=
  ((Nat.factorial 7 : ℚ) / (Nat.factorial (7+x) : ℚ)) *
    ((Nat.factorial 8 : ℚ) / (Nat.factorial (8+N-x) : ℚ))

lemma D_7_2_explicit_formula (N : ℕ) :
    D 7 2 N = ∑ x ∈ (Finset.range (N+1)).filter (fun x => 2*x <= N), D72term N x := by
  simpa [D72term] using D_b_two_explicit_formula 7 N

lemma D72term_nonneg (N x : ℕ) : 0 ≤ D72term N x := by
  dsimp [D72term]
  positivity

lemma D72term_same_shift_le_one_990 (x k : ℕ) :
    D72term (x + k + 3) x ≤ ((1 : ℚ) / 990) * D72term (x + k) x := by
  dsimp [D72term]
  rw [show 7 + x = x + 7 by omega,
      show 8 + (x + k + 3) - x = k + 11 by omega,
      show 8 + (x + k) - x = k + 8 by omega]
  have hfac : Nat.factorial (k + 11) =
      (k + 11) * (k + 10) * (k + 9) * Nat.factorial (k + 8) := by
    rw [show k + 11 = (k + 10) + 1 by omega, Nat.factorial_succ]
    rw [show k + 10 = (k + 9) + 1 by omega, Nat.factorial_succ]
    rw [show k + 9 = (k + 8) + 1 by omega, Nat.factorial_succ]
    ring
  rw [hfac]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (x + 7)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k + 8))]
  have hprod : (990 : ℚ) ≤ (((k + 11) * (k + 10) * (k + 9) : ℕ) : ℚ) := by
    have hprod_nat : 990 ≤ (k + 11) * (k + 10) * (k + 9) := by
      have h1 : 11 * 10 * 9 ≤ (k + 11) * (k + 10) * (k + 9) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      norm_num at h1 ⊢
      exact h1
    exact_mod_cast hprod_nat
  have hfact_pos : (0 : ℚ) < (Nat.factorial (k + 8) : ℚ) := by positivity
  norm_num [Nat.cast_mul] at hprod ⊢
  nlinarith [hprod, hfact_pos]

lemma D72term_even_extra_le_one720 (m : ℕ) :
    D72term (2*m + 3) (m + 1) ≤ ((1 : ℚ) / 720) * D72term (2*m) m := by
  dsimp [D72term]
  rw [show 7 + (m + 1) = m + 8 by omega,
      show 8 + (2*m + 3) - (m + 1) = m + 10 by omega,
      show 7 + m = m + 7 by omega,
      show 8 + (2*m) - m = m + 8 by omega]
  have hfac10 : Nat.factorial (m + 10) =
      (m + 10) * (m + 9) * (m + 8) * Nat.factorial (m + 7) := by
    rw [show m + 10 = (m + 9) + 1 by omega, Nat.factorial_succ]
    rw [show m + 9 = (m + 8) + 1 by omega, Nat.factorial_succ]
    rw [show m + 8 = (m + 7) + 1 by omega, Nat.factorial_succ]
    ring
  have hfac8 : Nat.factorial (m + 8) = (m + 8) * Nat.factorial (m + 7) := by
    rw [show m + 8 = (m + 7) + 1 by omega, Nat.factorial_succ]
  rw [hfac10, hfac8]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 7))]
  have hprod : (720 : ℚ) ≤ (((m + 10) * (m + 9) * (m + 8) : ℕ) : ℚ) := by
    have hprod_nat : 720 ≤ (m + 10) * (m + 9) * (m + 8) := by
      have h1 : 10 * 9 * 8 ≤ (m + 10) * (m + 9) * (m + 8) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      norm_num at h1 ⊢
      exact h1
    exact_mod_cast hprod_nat
  have hfact_pos : (0 : ℚ) < (Nat.factorial (m + 7) : ℚ) := by positivity
  norm_num [Nat.cast_mul] at hprod ⊢
  nlinarith [hprod, hfact_pos]

lemma D72term_odd_extra1_le_one880 (m : ℕ) :
    D72term (2*m + 4) (m + 1) ≤ ((1 : ℚ) / 880) * D72term (2*m + 1) m := by
  dsimp [D72term]
  rw [show 7 + (m + 1) = m + 8 by omega,
      show 8 + (2*m + 4) - (m + 1) = m + 11 by omega,
      show 7 + m = m + 7 by omega,
      show 8 + (2*m + 1) - m = m + 9 by omega]
  have hfac8 : Nat.factorial (m + 8) = (m + 8) * Nat.factorial (m + 7) := by
    rw [show m + 8 = (m + 7) + 1 by omega, Nat.factorial_succ]
  have hfac9 : Nat.factorial (m + 9) = (m + 9) * (m + 8) * Nat.factorial (m + 7) := by
    rw [show m + 9 = (m + 8) + 1 by omega, Nat.factorial_succ]
    rw [show m + 8 = (m + 7) + 1 by omega, Nat.factorial_succ]
    ring
  have hfac11 : Nat.factorial (m + 11) =
      (m + 11) * (m + 10) * Nat.factorial (m + 9) := by
    rw [show m + 11 = (m + 10) + 1 by omega, Nat.factorial_succ]
    rw [show m + 10 = (m + 9) + 1 by omega, Nat.factorial_succ]
    ring
  rw [hfac8, hfac11, hfac9]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 7)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 9))]
  have hprod : (880 : ℚ) ≤ (((m + 8) * (m + 11) * (m + 10) : ℕ) : ℚ) := by
    have hprod_nat : 880 ≤ (m + 8) * (m + 11) * (m + 10) := by
      have h1 : 8 * 11 * 10 ≤ (m + 8) * (m + 11) * (m + 10) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      norm_num at h1 ⊢
      exact h1
    exact_mod_cast hprod_nat
  have h1pos : (0 : ℚ) < (Nat.factorial (m + 7) : ℚ) := by positivity
  have h2pos : (0 : ℚ) < (Nat.factorial (m + 9) : ℚ) := by positivity
  norm_num [Nat.cast_mul] at hprod ⊢
  have hcommon_nonneg : 0 ≤ (↑m + 9) * (↑m + 8) *
      (Nat.factorial (m + 7) : ℚ) * (Nat.factorial (m + 7) : ℚ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hprod hcommon_nonneg
  nlinarith [hmul, h1pos, h2pos]

lemma D72term_odd_extra2_le_one720 (m : ℕ) :
    D72term (2*m + 4) (m + 2) ≤ ((1 : ℚ) / 720) * D72term (2*m + 1) m := by
  dsimp [D72term]
  rw [show 7 + (m + 2) = m + 9 by omega,
      show 8 + (2*m + 4) - (m + 2) = m + 10 by omega,
      show 7 + m = m + 7 by omega,
      show 8 + (2*m + 1) - m = m + 9 by omega]
  have hfac9 : Nat.factorial (m + 9) =
      (m + 9) * (m + 8) * Nat.factorial (m + 7) := by
    rw [show m + 9 = (m + 8) + 1 by omega, Nat.factorial_succ]
    rw [show m + 8 = (m + 7) + 1 by omega, Nat.factorial_succ]
    ring
  have hfac10 : Nat.factorial (m + 10) = (m + 10) * Nat.factorial (m + 9) := by
    rw [show m + 10 = (m + 9) + 1 by omega, Nat.factorial_succ]
  rw [hfac10]
  repeat rw [hfac9]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 7)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 9))]
  have hprod : (720 : ℚ) ≤ (((m + 9) * (m + 8) * (m + 10) : ℕ) : ℚ) := by
    have hprod_nat : 720 ≤ (m + 9) * (m + 8) * (m + 10) := by
      have h1 : 9 * 8 * 10 ≤ (m + 9) * (m + 8) * (m + 10) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      norm_num at h1 ⊢
      exact h1
    exact_mod_cast hprod_nat
  have h1pos : (0 : ℚ) < (Nat.factorial (m + 7) : ℚ) := by positivity
  have h2pos : (0 : ℚ) < (Nat.factorial (m + 9) : ℚ) := by positivity
  norm_num [Nat.cast_mul] at hprod ⊢
  nlinarith [hprod, h1pos, h2pos]

lemma D_seven_two_step_contraction_thirteen_over_3600_even (m : ℕ) :
    D 7 2 (2*m + 3) ≤ ((13 : ℚ) / 3600) * D 7 2 (2*m) := by
  rw [D_7_2_explicit_formula, D_7_2_explicit_formula]
  rw [D42_even_source_filter, D42_even_target_filter]
  rw [show m + 2 = (m + 1) + 1 by omega, Finset.sum_range_succ]
  set T : ℚ := ∑ x ∈ Finset.range (m + 1), D72term (2*m) x
  have hmain : (∑ x ∈ Finset.range (m + 1), D72term (2*m + 3) x) ≤ ((1 : ℚ) / 990) * T := by
    dsimp [T]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro x hx
    have hxlt : x < m + 1 := Finset.mem_range.mp hx
    have hxle : x ≤ 2*m := by omega
    simpa [show x + (2*m - x) = 2*m by omega,
      show x + (2*m - x) + 3 = 2*m + 3 by omega] using
      D72term_same_shift_le_one_990 x (2*m - x)
  have hlast_le : D72term (2*m) m ≤ T := by
    dsimp [T]
    exact Finset.single_le_sum (by intro x hx; exact D72term_nonneg (2*m) x)
      (by simp : m ∈ Finset.range (m + 1))
  have hextra : D72term (2*m + 3) (m + 1) ≤ ((1 : ℚ) / 720) * T := by
    exact le_trans (D72term_even_extra_le_one720 m)
      (mul_le_mul_of_nonneg_left hlast_le (by norm_num))
  have hTnon : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg (by intro x hx; exact D72term_nonneg (2*m) x)
  calc
    (∑ x ∈ Finset.range (m + 1), D72term (2*m + 3) x) + D72term (2*m + 3) (m + 1)
        ≤ ((1 : ℚ) / 990) * T + ((1 : ℚ) / 720) * T := add_le_add hmain hextra
    _ ≤ ((13 : ℚ) / 3600) * T := by
      have hc : ((1 : ℚ) / 990) + ((1 : ℚ) / 720) ≤ (13 : ℚ) / 3600 := by norm_num
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right hc hTnon

lemma D_seven_two_step_contraction_thirteen_over_3600_odd (m : ℕ) :
    D 7 2 (2*m + 1 + 3) ≤ ((13 : ℚ) / 3600) * D 7 2 (2*m + 1) := by
  rw [show 2*m + 1 + 3 = 2*m + 4 by omega]
  rw [D_7_2_explicit_formula, D_7_2_explicit_formula]
  rw [D42_odd_source_filter, D42_odd_target_filter]
  rw [show m + 3 = (m + 2) + 1 by omega, Finset.sum_range_succ]
  rw [show m + 2 = (m + 1) + 1 by omega, Finset.sum_range_succ]
  set T : ℚ := ∑ x ∈ Finset.range (m + 1), D72term (2*m + 1) x
  have hmain : (∑ x ∈ Finset.range (m + 1), D72term (2*m + 4) x) ≤ ((1 : ℚ) / 990) * T := by
    dsimp [T]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro x hx
    have hxlt : x < m + 1 := Finset.mem_range.mp hx
    have hxle : x ≤ 2*m + 1 := by omega
    simpa [show x + (2*m + 1 - x) = 2*m + 1 by omega,
      show x + (2*m + 1 - x) + 3 = 2*m + 4 by omega] using
      D72term_same_shift_le_one_990 x (2*m + 1 - x)
  have hlast_le : D72term (2*m + 1) m ≤ T := by
    dsimp [T]
    exact Finset.single_le_sum (by intro x hx; exact D72term_nonneg (2*m + 1) x)
      (by simp : m ∈ Finset.range (m + 1))
  have hextra1 : D72term (2*m + 4) (m + 1) ≤ ((1 : ℚ) / 880) * T := by
    exact le_trans (D72term_odd_extra1_le_one880 m)
      (mul_le_mul_of_nonneg_left hlast_le (by norm_num))
  have hextra2 : D72term (2*m + 4) (m + 2) ≤ ((1 : ℚ) / 720) * T := by
    exact le_trans (D72term_odd_extra2_le_one720 m)
      (mul_le_mul_of_nonneg_left hlast_le (by norm_num))
  have hTnon : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg (by intro x hx; exact D72term_nonneg (2*m + 1) x)
  calc
    (∑ x ∈ Finset.range (m + 1), D72term (2*m + 4) x) + D72term (2*m + 4) (m + 1) +
        D72term (2*m + 4) (m + 2)
        ≤ ((1 : ℚ) / 990) * T + ((1 : ℚ) / 880) * T + ((1 : ℚ) / 720) * T := by
          exact add_le_add (add_le_add hmain hextra1) hextra2
    _ ≤ ((13 : ℚ) / 3600) * T := by
      have hc : ((1 : ℚ) / 990) + ((1 : ℚ) / 880) + ((1 : ℚ) / 720) ≤ (13 : ℚ) / 3600 := by norm_num
      rw [← add_mul, ← add_mul]
      exact mul_le_mul_of_nonneg_right hc hTnon

lemma D_seven_two_step_contraction_thirteen_over_3600 (s : ℕ) :
    D 7 2 (s+3) ≤ ((13:ℚ)/3600) * D 7 2 s := by
  rcases Nat.even_or_odd s with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      D_seven_two_step_contraction_thirteen_over_3600_even m
  · simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      D_seven_two_step_contraction_thirteen_over_3600_odd m
lemma D_five_three_le_D_four_three (s : ℕ) : D 5 3 s ≤ D 4 3 s := by
  classical
  unfold D
  refine Finset.sum_le_sum ?_
  intro δ hδ
  unfold weight
  rw [Fin.prod_univ_three, Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  have hfac0 : Nat.factorial (5 + δ 0) = (5 + δ 0) * Nat.factorial (4 + δ 0) := by
    rw [show 5 + δ 0 = (4 + δ 0) + 1 by omega, Nat.factorial_succ]
  have hfac1 : Nat.factorial (6 + δ 1) = (6 + δ 1) * Nat.factorial (5 + δ 1) := by
    rw [show 6 + δ 1 = (5 + δ 1) + 1 by omega, Nat.factorial_succ]
  have hfac2 : Nat.factorial (7 + δ 2) = (7 + δ 2) * Nat.factorial (6 + δ 2) := by
    rw [show 7 + δ 2 = (6 + δ 2) + 1 by omega, Nat.factorial_succ]
  rw [hfac0, hfac1, hfac2]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (4 + δ 0)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (5 + δ 1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (6 + δ 2))]
  have hprod : (210 : ℚ) ≤ ((5 + δ 0 : ℕ) : ℚ) * ((6 + δ 1 : ℕ) : ℚ) * ((7 + δ 2 : ℕ) : ℚ) := by
    have hprod_nat : 210 ≤ (5 + δ 0) * (6 + δ 1) * (7 + δ 2) := by
      have h1 : 5 * 6 * 7 ≤ (5 + δ 0) * (6 + δ 1) * (7 + δ 2) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      norm_num at h1 ⊢
      exact h1
    exact_mod_cast hprod_nat
  have h0 : (0 : ℚ) < (Nat.factorial (4 + δ 0) : ℚ) := by positivity
  have h1 : (0 : ℚ) < (Nat.factorial (5 + δ 1) : ℚ) := by positivity
  have h2 : (0 : ℚ) < (Nat.factorial (6 + δ 2) : ℚ) := by positivity
  norm_num [Nat.cast_mul] at hprod ⊢
  have hcommon_nonneg : 0 ≤ (Nat.factorial (4 + δ 0) : ℚ) *
      (Nat.factorial (5 + δ 1) : ℚ) * (Nat.factorial (6 + δ 2) : ℚ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hprod hcommon_nonneg
  nlinarith [hmul, h0, h1, h2]

lemma D_five_two_le_D_four_three (s : ℕ) : D 5 2 s ≤ D 4 3 s := by
  simpa using D_three_ge_zero_term 4 s

lemma D_four_three_step_contraction_three_one_seventy_fifth (s : ℕ) :
    D 4 3 (s+3) ≤ ((1:ℚ)/75) * D 4 3 s := by
  have hsplit := D_split_general_three 4 s
  have hdecomp : D 4 3 (s+3) = ((1 : ℚ) / 210) * D 5 3 s + D 5 2 (s+3) := by
    norm_num at hsplit
    linarith
  have hmain : ((1 : ℚ) / 210) * D 5 3 s ≤ ((1 : ℚ) / 210) * D 4 3 s := by
    exact mul_le_mul_of_nonneg_left (D_five_three_le_D_four_three s) (by norm_num)
  have hzero : D 5 2 (s+3) ≤ ((3 : ℚ) / 350) * D 4 3 s := by

    exact le_trans (D_five_two_step_contraction_three_three_fiftieths s)
      (mul_le_mul_of_nonneg_left (D_five_two_le_D_four_three s) (by norm_num))
  calc
    D 4 3 (s+3) = ((1 : ℚ) / 210) * D 5 3 s + D 5 2 (s+3) := hdecomp
    _ ≤ ((1 : ℚ) / 210) * D 4 3 s + ((3 : ℚ) / 350) * D 4 3 s := add_le_add hmain hzero
    _ = ((1 : ℚ) / 75) * D 4 3 s := by ring


lemma factorial_succ_ratio_le_self (n d : ℕ) :
    ((Nat.factorial (n+1) : ℚ) / (Nat.factorial (n+1+d) : ℚ)) ≤
      ((Nat.factorial n : ℚ) / (Nat.factorial (n+d) : ℚ)) := by
  have hfacA : (Nat.factorial (n + 1) : ℚ) = ((n + 1 : ℕ) : ℚ) * (Nat.factorial n : ℚ) := by
    rw [Nat.factorial_succ]
    norm_num [Nat.cast_mul]
  have hfacB : (Nat.factorial (n + 1 + d) : ℚ) = ((n + d + 1 : ℕ) : ℚ) * (Nat.factorial (n+d) : ℚ) := by
    rw [show n + 1 + d = (n + d) + 1 by omega, Nat.factorial_succ]
    norm_num [Nat.cast_mul]
  rw [hfacA, hfacB]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n+d))]
  have hle : ((n + 1 : ℕ) : ℚ) ≤ ((n + d + 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : n + 1 ≤ n + d + 1)
  have hfacpos : (0 : ℚ) < (Nat.factorial n : ℚ) := by positivity
  have hfacpos2 : (0 : ℚ) < (Nat.factorial (n+d) : ℚ) := by positivity
  nlinarith

lemma weight_succ_a_le (a l : ℕ) (δ : Fin l → ℕ) : weight (a+1) l δ ≤ weight a l δ := by
  classical
  unfold weight
  refine Finset.prod_le_prod ?_ ?_
  · intro i hi
    positivity
  · intro i hi
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      factorial_succ_ratio_le_self (a + (i : ℕ)) (δ i)

lemma D_succ_a_le (a l N : ℕ) : D (a+1) l N ≤ D a l N := by
  classical
  unfold D
  exact Finset.sum_le_sum (by intro δ hδ; exact weight_succ_a_le a l δ)

lemma D_six_three_le_D_five_three (s : ℕ) : D 6 3 s ≤ D 5 3 s := by
  simpa using D_succ_a_le 5 3 s

lemma D_six_two_le_D_five_three (s : ℕ) : D 6 2 s ≤ D 5 3 s := by
  simpa using D_three_ge_zero_term 5 s

lemma D_five_three_three_step_contraction_three_350 (s : ℕ) :
    D 5 3 (s+3) ≤ ((3:ℚ)/350) * D 5 3 s := by
  have hsplit := D_split_general_three 5 s
  have hdecomp : D 5 3 (s+3) = ((1 : ℚ) / 336) * D 6 3 s + D 6 2 (s+3) := by
    norm_num at hsplit
    linarith
  have hmain : ((1 : ℚ) / 336) * D 6 3 s ≤ ((1 : ℚ) / 336) * D 5 3 s := by
    exact mul_le_mul_of_nonneg_left (D_six_three_le_D_five_three s) (by norm_num)


  have hzero : D 6 2 (s+3) ≤ ((47 : ℚ) / 8400) * D 5 3 s := by
    exact le_trans (D_six_two_step_contraction_fortyseven_over_8400 s)
      (mul_le_mul_of_nonneg_left (D_six_two_le_D_five_three s) (by norm_num))
  calc
    D 5 3 (s+3) = ((1 : ℚ) / 336) * D 6 3 s + D 6 2 (s+3) := hdecomp
    _ ≤ ((1 : ℚ) / 336) * D 5 3 s + ((47 : ℚ) / 8400) * D 5 3 s := add_le_add hmain hzero
    _ = ((3 : ℚ) / 350) * D 5 3 s := by ring

lemma D_seven_three_le_D_six_three (s : ℕ) : D 7 3 s ≤ D 6 3 s := by
  simpa using D_succ_a_le 6 3 s

lemma D_seven_two_le_D_six_three (s : ℕ) : D 7 2 s ≤ D 6 3 s := by
  simpa using D_three_ge_zero_term 6 s

lemma D_six_three_three_step_contraction_fortyseven_over_8400 (s : ℕ) :
    D 6 3 (s+3) ≤ ((47:ℚ)/8400) * D 6 3 s := by
  have hsplit := D_split_general_three 6 s
  have hdecomp : D 6 3 (s+3) = ((1 : ℚ) / 504) * D 7 3 s + D 7 2 (s+3) := by
    norm_num at hsplit
    linarith
  have hmain : ((1 : ℚ) / 504) * D 7 3 s ≤ ((1 : ℚ) / 504) * D 6 3 s := by
    exact mul_le_mul_of_nonneg_left (D_seven_three_le_D_six_three s) (by norm_num)
  have hzero : D 7 2 (s+3) ≤ ((13 : ℚ) / 3600) * D 6 3 s := by
    exact le_trans (D_seven_two_step_contraction_thirteen_over_3600 s)
      (mul_le_mul_of_nonneg_left (D_seven_two_le_D_six_three s) (by norm_num))
  have hnon : 0 ≤ D 6 3 s := D_nonneg 6 3 s
  calc
    D 6 3 (s+3) = ((1 : ℚ) / 504) * D 7 3 s + D 7 2 (s+3) := hdecomp
    _ ≤ ((1 : ℚ) / 504) * D 6 3 s + ((13 : ℚ) / 3600) * D 6 3 s := add_le_add hmain hzero
    _ = (((1 : ℚ) / 504) + ((13 : ℚ) / 3600)) * D 6 3 s := by ring
    _ ≤ ((47 : ℚ) / 8400) * D 6 3 s := by
      exact mul_le_mul_of_nonneg_right (by norm_num : ((1 : ℚ) / 504) + ((13 : ℚ) / 3600) ≤ (47 : ℚ) / 8400) hnon

private lemma raiseAt_last_injective_4 :
    Function.Injective (fun δ : Fin 4 → ℕ => raiseAt δ (3 : Fin 4)) := by
  intro δ η h
  funext i
  have hi := congrFun h i
  fin_cases i <;> simp [raiseAt] at hi ⊢ <;> omega

private lemma raiseAt_last_mem_support_4_succ {t : ℕ} {δ : Fin 4 → ℕ}
    (hδ : δ ∈ support 4 t) : raiseAt δ (3 : Fin 4) ∈ support 4 (t+1) := by
  rw [support] at hδ ⊢
  simp only [Finset.mem_filter] at hδ ⊢
  rcases hδ with ⟨hbox, hnd, hsum⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]
    intro i
    have hi := Fintype.mem_piFinset.mp hbox i
    simp only [Finset.mem_range] at hi ⊢
    fin_cases i
    · simpa [raiseAt] using Nat.lt.step hi
    · simpa [raiseAt] using Nat.lt.step hi
    · simpa [raiseAt] using Nat.lt.step hi
    · simpa [raiseAt] using Nat.succ_lt_succ hi
  · intro i j hij
    have h01 : δ 0 ≤ δ 1 := hnd 0 1 (by decide)
    have h02 : δ 0 ≤ δ 2 := hnd 0 2 (by decide)
    have h03 : δ 0 ≤ δ 3 := hnd 0 3 (by decide)
    have h12 : δ 1 ≤ δ 2 := hnd 1 2 (by decide)
    have h13 : δ 1 ≤ δ 3 := hnd 1 3 (by decide)
    have h23 : δ 2 ≤ δ 3 := hnd 2 3 (by decide)
    fin_cases i <;> fin_cases j <;> simp [raiseAt] at hij ⊢ <;> omega
  · simp [Fin.sum_univ_four, raiseAt] at hsum ⊢
    omega

private lemma weight_five_four_le_eight_weight_four_four_raise_last (δ : Fin 4 → ℕ) :
    weight 5 4 δ ≤ (8 : ℚ) * weight 4 4 (raiseAt δ (3 : Fin 4)) := by
  unfold weight
  rw [Fin.prod_univ_four, Fin.prod_univ_four]
  simp [raiseAt]
  let b0 : ℚ := (Nat.factorial 5 : ℚ) / (Nat.factorial (5 + δ 0) : ℚ)
  let b1 : ℚ := (Nat.factorial 6 : ℚ) / (Nat.factorial (6 + δ 1) : ℚ)
  let b2 : ℚ := (Nat.factorial 7 : ℚ) / (Nat.factorial (7 + δ 2) : ℚ)
  let b3 : ℚ := (Nat.factorial 8 : ℚ) / (Nat.factorial (8 + δ 3) : ℚ)
  let a0 : ℚ := (Nat.factorial 4 : ℚ) / (Nat.factorial (4 + δ 0) : ℚ)
  let a1 : ℚ := (Nat.factorial 5 : ℚ) / (Nat.factorial (5 + δ 1) : ℚ)
  let a2 : ℚ := (Nat.factorial 6 : ℚ) / (Nat.factorial (6 + δ 2) : ℚ)
  let a3 : ℚ := (Nat.factorial 7 : ℚ) / (Nat.factorial (7 + (δ 3 + 1)) : ℚ)
  change b0 * b1 * b2 * b3 ≤ (8 : ℚ) * (a0 * a1 * a2 * a3)
  have hb0 : 0 ≤ b0 := by dsimp [b0]; positivity
  have hb1 : 0 ≤ b1 := by dsimp [b1]; positivity
  have hb2 : 0 ≤ b2 := by dsimp [b2]; positivity
  have ha0 : 0 ≤ a0 := by dsimp [a0]; positivity
  have ha1 : 0 ≤ a1 := by dsimp [a1]; positivity
  have ha2 : 0 ≤ a2 := by dsimp [a2]; positivity
  have ha3 : 0 ≤ a3 := by dsimp [a3]; positivity
  have h0 : b0 ≤ a0 := by
    dsimp [b0, a0]
    simpa using factorial_succ_ratio_le_self 4 (δ 0)
  have h1 : b1 ≤ a1 := by
    dsimp [b1, a1]
    simpa using factorial_succ_ratio_le_self 5 (δ 1)
  have h2 : b2 ≤ a2 := by
    dsimp [b2, a2]
    simpa using factorial_succ_ratio_le_self 6 (δ 2)
  have h3 : b3 = (8 : ℚ) * a3 := by
    dsimp [b3, a3]
    rw [show 7 + (δ 3 + 1) = 8 + δ 3 by omega]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (8 + δ 3))]
    norm_num
  have h01 : b0 * b1 ≤ a0 * a1 := mul_le_mul h0 h1 hb1 ha0
  have h012 : b0 * b1 * b2 ≤ a0 * a1 * a2 := mul_le_mul h01 h2 hb2 (mul_nonneg ha0 ha1)
  calc
    b0 * b1 * b2 * b3 = (b0 * b1 * b2) * b3 := by ring
    _ = (b0 * b1 * b2) * ((8 : ℚ) * a3) := by rw [h3]
    _ ≤ (a0 * a1 * a2) * ((8 : ℚ) * a3) := by
      exact mul_le_mul_of_nonneg_right h012 (mul_nonneg (by norm_num) ha3)
    _ = (8 : ℚ) * (a0 * a1 * a2 * a3) := by ring

lemma D_five_four_to_D_four_four_succ_eight (t : ℕ) :
    D 5 4 t ≤ (8:ℚ) * D 4 4 (t+1) := by
  classical
  unfold D
  let f : (Fin 4 → ℕ) → (Fin 4 → ℕ) := fun δ => raiseAt δ (3 : Fin 4)
  have hinj : Set.InjOn f (support 4 t) := by
    intro δ hδ η hη h
    exact raiseAt_last_injective_4 h
  have himage_subset : (support 4 t).image f ⊆ support 4 (t+1) := by
    intro η hη
    rcases Finset.mem_image.mp hη with ⟨δ, hδ, rfl⟩
    exact raiseAt_last_mem_support_4_succ hδ
  have hnon_image : ∀ η ∈ support 4 (t+1), η ∉ (support 4 t).image f → 0 ≤ weight 4 4 η := by
    intro η hη hnot
    exact weight_nonneg 4 4 η
  calc
    (∑ δ ∈ support 4 t, weight 5 4 δ)
        ≤ ∑ δ ∈ support 4 t, (8 : ℚ) * weight 4 4 (f δ) := by
          exact Finset.sum_le_sum (by intro δ hδ; exact weight_five_four_le_eight_weight_four_four_raise_last δ)
    _ = (8 : ℚ) * (∑ δ ∈ support 4 t, weight 4 4 (f δ)) := by
          rw [Finset.mul_sum]
    _ = (8 : ℚ) * (∑ η ∈ (support 4 t).image f, weight 4 4 η) := by
          rw [Finset.sum_image hinj]
    _ ≤ (8 : ℚ) * (∑ η ∈ support 4 (t+1), weight 4 4 η) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg himage_subset hnon_image) (by norm_num)

private lemma tuple_0001_mem_support_4_1 : (![0,0,0,1] : Fin 4 → ℕ) ∈ support 4 1 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_four]

private lemma weight_six_four_le_nine_weight_five_four_raise_last (δ : Fin 4 → ℕ) :
    weight 6 4 δ ≤ (9 : ℚ) * weight 5 4 (raiseAt δ (3 : Fin 4)) := by
  unfold weight
  rw [Fin.prod_univ_four, Fin.prod_univ_four]
  simp [raiseAt]
  let b0 : ℚ := (Nat.factorial 6 : ℚ) / (Nat.factorial (6 + δ 0) : ℚ)
  let b1 : ℚ := (Nat.factorial 7 : ℚ) / (Nat.factorial (7 + δ 1) : ℚ)
  let b2 : ℚ := (Nat.factorial 8 : ℚ) / (Nat.factorial (8 + δ 2) : ℚ)
  let b3 : ℚ := (Nat.factorial 9 : ℚ) / (Nat.factorial (9 + δ 3) : ℚ)
  let a0 : ℚ := (Nat.factorial 5 : ℚ) / (Nat.factorial (5 + δ 0) : ℚ)
  let a1 : ℚ := (Nat.factorial 6 : ℚ) / (Nat.factorial (6 + δ 1) : ℚ)
  let a2 : ℚ := (Nat.factorial 7 : ℚ) / (Nat.factorial (7 + δ 2) : ℚ)
  let a3 : ℚ := (Nat.factorial 8 : ℚ) / (Nat.factorial (8 + (δ 3 + 1)) : ℚ)
  change b0 * b1 * b2 * b3 ≤ (9 : ℚ) * (a0 * a1 * a2 * a3)
  have hb1 : 0 ≤ b1 := by dsimp [b1]; positivity
  have hb2 : 0 ≤ b2 := by dsimp [b2]; positivity
  have ha0 : 0 ≤ a0 := by dsimp [a0]; positivity
  have ha1 : 0 ≤ a1 := by dsimp [a1]; positivity
  have ha2 : 0 ≤ a2 := by dsimp [a2]; positivity
  have ha3 : 0 ≤ a3 := by dsimp [a3]; positivity
  have h0 : b0 ≤ a0 := by
    dsimp [b0, a0]
    simpa using factorial_succ_ratio_le_self 5 (δ 0)
  have h1 : b1 ≤ a1 := by
    dsimp [b1, a1]
    simpa using factorial_succ_ratio_le_self 6 (δ 1)
  have h2 : b2 ≤ a2 := by
    dsimp [b2, a2]
    simpa using factorial_succ_ratio_le_self 7 (δ 2)
  have h3 : b3 = (9 : ℚ) * a3 := by
    dsimp [b3, a3]
    rw [show 8 + (δ 3 + 1) = 9 + δ 3 by omega]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (9 + δ 3))]
    norm_num
  have h01 : b0 * b1 ≤ a0 * a1 := mul_le_mul h0 h1 hb1 ha0
  have h012 : b0 * b1 * b2 ≤ a0 * a1 * a2 := mul_le_mul h01 h2 hb2 (mul_nonneg ha0 ha1)
  calc
    b0 * b1 * b2 * b3 = (b0 * b1 * b2) * b3 := by ring
    _ = (b0 * b1 * b2) * ((9 : ℚ) * a3) := by rw [h3]
    _ ≤ (a0 * a1 * a2) * ((9 : ℚ) * a3) := by
      exact mul_le_mul_of_nonneg_right h012 (mul_nonneg (by norm_num) ha3)
    _ = (9 : ℚ) * (a0 * a1 * a2 * a3) := by ring

lemma D_six_four_to_D_five_four_succ_nine (t : ℕ) :
    D 6 4 t ≤ (9:ℚ) * D 5 4 (t+1) := by
  classical
  unfold D
  let f : (Fin 4 → ℕ) → (Fin 4 → ℕ) := fun δ => raiseAt δ (3 : Fin 4)
  have hinj : Set.InjOn f (support 4 t) := by
    intro δ hδ η hη h
    exact raiseAt_last_injective_4 h
  have himage_subset : (support 4 t).image f ⊆ support 4 (t+1) := by
    intro η hη
    rcases Finset.mem_image.mp hη with ⟨δ, hδ, rfl⟩
    exact raiseAt_last_mem_support_4_succ hδ
  have hnon_image : ∀ η ∈ support 4 (t+1), η ∉ (support 4 t).image f → 0 ≤ weight 5 4 η := by
    intro η hη hnot
    exact weight_nonneg 5 4 η
  calc
    (∑ δ ∈ support 4 t, weight 6 4 δ)
        ≤ ∑ δ ∈ support 4 t, (9 : ℚ) * weight 5 4 (f δ) := by
          exact Finset.sum_le_sum (by intro δ hδ; exact weight_six_four_le_nine_weight_five_four_raise_last δ)
    _ = (9 : ℚ) * (∑ δ ∈ support 4 t, weight 5 4 (f δ)) := by
          rw [Finset.mul_sum]
    _ = (9 : ℚ) * (∑ η ∈ (support 4 t).image f, weight 5 4 η) := by
          rw [Finset.sum_image hinj]
    _ ≤ (9 : ℚ) * (∑ η ∈ support 4 (t+1), weight 5 4 η) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg himage_subset hnon_image) (by norm_num)

private lemma support_4_1_eq : support 4 1 = {(![0,0,0,1] : Fin 4 → ℕ)} := by
  classical
  ext δ
  constructor
  · intro h
    rw [support] at h
    simp only [Finset.mem_filter, Finset.mem_singleton] at h ⊢
    rcases h with ⟨hbox, hnd, hsum⟩
    norm_num [Fin.sum_univ_four] at hsum
    have h01 : δ 0 ≤ δ 1 := hnd 0 1 (by decide)
    have h12 : δ 1 ≤ δ 2 := hnd 1 2 (by decide)
    have h23 : δ 2 ≤ δ 3 := hnd 2 3 (by decide)
    have h0 : δ 0 = 0 := by omega
    have h1 : δ 1 = 0 := by omega
    have h2 : δ 2 = 0 := by omega
    have h3 : δ 3 = 1 := by omega
    funext i
    fin_cases i <;> simp [h0, h1, h2, h3]
  · intro h
    rw [Finset.mem_singleton] at h
    rw [h]
    exact tuple_0001_mem_support_4_1

lemma D_4_4_1_exact : D 4 4 1 = (1 : ℚ) / 8 := by
  classical
  rw [D, support_4_1_eq]
  simp [weight, Fin.prod_univ_four]
  norm_num

lemma D_4_4_4_exact : D 4 4 4 = (997 : ℚ) / 665280 := by
  classical
  rw [D, support_4_4_eq]
  simp [weight, Fin.prod_univ_four]
  norm_num

/-- The empirically worst small point mentioned in the problem statement. -/
lemma D_four_four_three_step_s_one_one_seventy_fifth :
    D 4 4 (1 + 3) ≤ ((1 : ℚ) / 75) * D 4 4 1 := by
  rw [D_4_4_4_exact, D_4_4_1_exact]
  norm_num


private lemma tuple_0000_mem_support_4_0 : (![0,0,0,0] : Fin 4 → ℕ) ∈ support 4 0 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_four]

private lemma support_4_0_eq : support 4 0 = {(![0,0,0,0] : Fin 4 → ℕ)} := by
  classical
  ext δ
  constructor
  · intro h
    rw [support] at h
    simp only [Finset.mem_filter, Finset.mem_singleton] at h ⊢
    rcases h with ⟨hbox, hnd, hsum⟩
    norm_num [Fin.sum_univ_four] at hsum
    have h0 : δ 0 = 0 := by omega
    have h1 : δ 1 = 0 := by omega
    have h2 : δ 2 = 0 := by omega
    have h3 : δ 3 = 0 := by omega
    funext i
    fin_cases i <;> simp [h0, h1, h2, h3]
  · intro h
    rw [Finset.mem_singleton] at h
    rw [h]
    exact tuple_0000_mem_support_4_0

private lemma tuple_0003_mem_support_4_3 : (![0,0,0,3] : Fin 4 → ℕ) ∈ support 4 3 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_four]

private lemma tuple_0012_mem_support_4_3 : (![0,0,1,2] : Fin 4 → ℕ) ∈ support 4 3 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_four]

private lemma tuple_0111_mem_support_4_3 : (![0,1,1,1] : Fin 4 → ℕ) ∈ support 4 3 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_four]

private lemma support_4_3_eq : support 4 3 =
    {(![0,0,0,3] : Fin 4 → ℕ), (![0,0,1,2] : Fin 4 → ℕ), (![0,1,1,1] : Fin 4 → ℕ)} := by
  classical
  ext δ
  constructor
  · intro h
    rw [support] at h
    simp only [Finset.mem_filter] at h
    rcases h with ⟨hbox, hnd, hsum⟩
    norm_num [Fin.sum_univ_four] at hsum
    have h01 : δ 0 ≤ δ 1 := hnd 0 1 (by decide)
    have h12 : δ 1 ≤ δ 2 := hnd 1 2 (by decide)
    have h23 : δ 2 ≤ δ 3 := hnd 2 3 (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hδ0 : δ 0 = 0
    · by_cases hδ1 : δ 1 = 0
      · by_cases hδ2 : δ 2 = 0
        · have hδ3 : δ 3 = 3 := by omega
          left
          funext i
          fin_cases i <;> simp [hδ0, hδ1, hδ2, hδ3]
        · have hδ2' : δ 2 = 1 := by omega
          have hδ3 : δ 3 = 2 := by omega
          right; left
          funext i
          fin_cases i <;> simp [hδ0, hδ1, hδ2', hδ3]
      · have hδ1' : δ 1 = 1 := by omega
        have hδ2 : δ 2 = 1 := by omega
        have hδ3 : δ 3 = 1 := by omega
        right; right


        funext i
        fin_cases i <;> simp [hδ0, hδ1', hδ2, hδ3]
    · omega
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · rw [h]; exact tuple_0003_mem_support_4_3
    · rw [h]; exact tuple_0012_mem_support_4_3
    · rw [h]; exact tuple_0111_mem_support_4_3

lemma D_4_4_0_exact : D 4 4 0 = (1 : ℚ) := by
  classical
  rw [D, support_4_0_eq]
  simp [weight, Fin.prod_univ_four]
  norm_num

lemma D_4_4_3_exact : D 4 4 3 = (2 : ℚ) / 315 := by
  classical
  rw [D, support_4_3_eq]
  simp [weight, Fin.prod_univ_four]
  norm_num

lemma D_four_four_three_step_s_zero_one_seventy_fifth :
    D 4 4 (0 + 3) ≤ ((1 : ℚ) / 75) * D 4 4 0 := by
  rw [D_4_4_3_exact, D_4_4_0_exact]
  norm_num

/-- Exact `l = 4` split.  With `a = 4`, this is the main identity reducing
`D 4 4 (T+4)` to a shifted four-dimensional term and a three-dimensional tail. -/
lemma D_split_general_four (a T : Nat) :
    ((Nat.factorial (a+4) : ℚ) / (Nat.factorial a : ℚ)) * D a 4 (T+4) =
      D (a+1) 4 T + ((Nat.factorial (a+4) : ℚ) / (Nat.factorial a : ℚ)) * D (a+1) 3 (T+4) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using D_split_general_succ a 3 T

/-- The zero first-coordinate slice embeds `D (a+1) 3 N` into `D a 4 N`. -/
lemma D_four_ge_zero_term (a N : Nat) : D (a+1) 3 N ≤ D a 4 N := by
  simpa using D_ge_zero_tail_general a 3 N

/-- A normalized form of the `a=4,l=4` split. -/
lemma D_four_four_three_step_split_succ (t : ℕ) :
    D 4 4 (t + 4) = ((1 : ℚ) / 1680) * D 5 4 t + D 5 3 (t + 4) := by
  have hsplit := D_split_general_four 4 t
  norm_num at hsplit
  linarith

/-- Reduction of the desired `r=4` contraction at positive `s` to the two tail
bounds naturally exposed by the split identity. -/
lemma D_four_four_three_step_contraction_succ_of_split_bound (t : ℕ)
    (h : ((1 : ℚ) / 1680) * D 5 4 t + D 5 3 (t + 4) ≤
      ((1 : ℚ) / 75) * D 4 4 (t + 1)) :
    D 4 4 ((t + 1) + 3) ≤ ((1 : ℚ) / 75) * D 4 4 (t + 1) := by
  rw [show (t + 1) + 3 = t + 4 by omega, D_four_four_three_step_split_succ]
  exact h

/-- The same split reduction phrased with the original positive index `s`.
This is intended as the reusable `s ≥ 2` (indeed `s ≥ 1`) tail-reduction
entry point for the remaining `r=4` proof. -/
lemma D_four_four_three_step_contraction_pos_of_split_bound (s : ℕ) (hs : 1 ≤ s)
    (h : ((1 : ℚ) / 1680) * D 5 4 (s - 1) + D 5 3 (s + 3) ≤
      ((1 : ℚ) / 75) * D 4 4 s) :
    D 4 4 (s + 3) ≤ ((1 : ℚ) / 75) * D 4 4 s := by
  cases s with
  | zero => omega
  | succ t =>
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        D_four_four_three_step_contraction_succ_of_split_bound t h

lemma D_four_three_step_contraction_four_one_seventy_fifth (s : ℕ) :
    D 4 4 (s + 3) ≤ ((1 : ℚ) / 75) * D 4 4 s := by
  cases s with
  | zero =>
      exact D_four_four_three_step_s_zero_one_seventy_fifth
  | succ t =>
      apply D_four_four_three_step_contraction_succ_of_split_bound t
      have hA0 := D_five_four_to_D_four_four_succ_eight t
      have hA : ((1 : ℚ) / 1680) * D 5 4 t ≤ ((1 : ℚ) / 210) * D 4 4 (t + 1) := by
        calc
          ((1 : ℚ) / 1680) * D 5 4 t ≤ ((1 : ℚ) / 1680) * ((8 : ℚ) * D 4 4 (t + 1)) := by
            exact mul_le_mul_of_nonneg_left hA0 (by norm_num)
          _ = ((1 : ℚ) / 210) * D 4 4 (t + 1) := by ring
      have hB0 : D 5 3 (t + 4) ≤ ((3 : ℚ) / 350) * D 5 3 (t + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          D_five_three_three_step_contraction_three_350 (t + 1)
      have hB : D 5 3 (t + 4) ≤ ((3 : ℚ) / 350) * D 4 4 (t + 1) := by
        exact le_trans hB0
          (mul_le_mul_of_nonneg_left (D_four_ge_zero_term 4 (t + 1)) (by norm_num))
      calc
        ((1 : ℚ) / 1680) * D 5 4 t + D 5 3 (t + 4)
            ≤ ((1 : ℚ) / 210) * D 4 4 (t + 1) + ((3 : ℚ) / 350) * D 4 4 (t + 1) := add_le_add hA hB
        _ = ((1 : ℚ) / 75) * D 4 4 (t + 1) := by ring


/-- Exact `l = 5` split.  This is the analogue of `D_split_general_four` one
level up, separating the zero first-coordinate tail from the positive part. -/
lemma D_split_general_five (a T : Nat) :
    ((Nat.factorial (a+5) : ℚ) / (Nat.factorial a : ℚ)) * D a 5 (T+5) =
      D (a+1) 5 T + ((Nat.factorial (a+5) : ℚ) / (Nat.factorial a : ℚ)) * D (a+1) 4 (T+5) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using D_split_general_succ a 4 T

/-- The zero first-coordinate slice embeds `D (a+1) 4 N` into `D a 5 N`. -/
lemma D_five_ge_zero_term (a N : Nat) : D (a+1) 4 N ≤ D a 5 N := by
  simpa using D_ge_zero_tail_general a 4 N

/-- The `a=4,l=5` split in the normalized form needed for the `r=5` case.
For a source index `s=t+2`, the target `s+3` is exactly `t+5`. -/
lemma D_four_five_three_step_split_ge_two (t : ℕ) :
    D 4 5 ((t + 2) + 3) = ((1 : ℚ) / 15120) * D 5 5 t + D 5 4 ((t + 2) + 3) := by
  have hsplit := D_split_general_five 4 t
  norm_num at hsplit
  rw [show (t + 2) + 3 = t + 5 by omega]
  linarith

/-- Reusable reduction for the still-open `r=5` contraction at indices `s ≥ 2`:
a bound on the two terms exposed by the `l=5` split implies the desired
three-step contraction. -/
lemma D_four_five_three_step_contraction_ge_two_of_split_bound (t : ℕ)
    (h : ((1 : ℚ) / 15120) * D 5 5 t + D 5 4 ((t + 2) + 3) ≤
      ((1 : ℚ) / 75) * D 4 5 (t + 2)) :
    D 4 5 ((t + 2) + 3) ≤ ((1 : ℚ) / 75) * D 4 5 (t + 2) := by
  rw [D_four_five_three_step_split_ge_two]
  exact h

/-- The same `r=5` split reduction phrased with an arbitrary index `s` and an
explicit hypothesis `2 ≤ s`. -/
lemma D_four_five_three_step_contraction_of_split_bound (s : ℕ) (hs : 2 ≤ s)
    (h : ((1 : ℚ) / 15120) * D 5 5 (s - 2) + D 5 4 (s + 3) ≤
      ((1 : ℚ) / 75) * D 4 5 s) :
    D 4 5 (s + 3) ≤ ((1 : ℚ) / 75) * D 4 5 s := by
  rcases Nat.exists_eq_add_of_le hs with ⟨t, rfl⟩
  have h' : ((1 : ℚ) / 15120) * D 5 5 t + D 5 4 ((t + 2) + 3) ≤
      ((1 : ℚ) / 75) * D 4 5 (t + 2) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    D_four_five_three_step_contraction_ge_two_of_split_bound t h'


private lemma tuple_00000_mem_support_5_0 : (![0,0,0,0,0] : Fin 5 → ℕ) ∈ support 5 0 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma support_5_0_eq : support 5 0 = {(![0,0,0,0,0] : Fin 5 → ℕ)} := by
  classical
  ext δ
  constructor
  · intro h
    rw [support] at h
    simp only [Finset.mem_filter, Finset.mem_singleton] at h ⊢
    rcases h with ⟨hbox, hnd, hsum⟩
    norm_num [Fin.sum_univ_five] at hsum
    have h0 : δ 0 = 0 := by omega
    have h1 : δ 1 = 0 := by omega
    have h2 : δ 2 = 0 := by omega
    have h3 : δ 3 = 0 := by omega
    have h4 : δ 4 = 0 := by omega
    funext i
    fin_cases i <;> simp [h0, h1, h2, h3, h4]
  · intro h
    rw [Finset.mem_singleton] at h
    rw [h]
    exact tuple_00000_mem_support_5_0

private lemma tuple_00001_mem_support_5_1 : (![0,0,0,0,1] : Fin 5 → ℕ) ∈ support 5 1 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma support_5_1_eq : support 5 1 = {(![0,0,0,0,1] : Fin 5 → ℕ)} := by
  classical
  ext δ
  constructor
  · intro h
    rw [support] at h
    simp only [Finset.mem_filter, Finset.mem_singleton] at h ⊢
    rcases h with ⟨hbox, hnd, hsum⟩
    norm_num [Fin.sum_univ_five] at hsum
    have h01 : δ 0 ≤ δ 1 := hnd 0 1 (by decide)
    have h12 : δ 1 ≤ δ 2 := hnd 1 2 (by decide)
    have h23 : δ 2 ≤ δ 3 := hnd 2 3 (by decide)
    have h34 : δ 3 ≤ δ 4 := hnd 3 4 (by decide)
    have h0 : δ 0 = 0 := by omega
    have h1 : δ 1 = 0 := by omega
    have h2 : δ 2 = 0 := by omega
    have h3 : δ 3 = 0 := by omega
    have h4 : δ 4 = 1 := by omega
    funext i
    fin_cases i <;> simp [h0, h1, h2, h3, h4]
  · intro h
    rw [Finset.mem_singleton] at h
    rw [h]
    exact tuple_00001_mem_support_5_1


private lemma tuple_00002_mem_support_5_2 : (![0,0,0,0,2] : Fin 5 → ℕ) ∈ support 5 2 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma tuple_00011_mem_support_5_2 : (![0,0,0,1,1] : Fin 5 → ℕ) ∈ support 5 2 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma support_5_2_eq : support 5 2 =
    {(![0,0,0,0,2] : Fin 5 → ℕ), (![0,0,0,1,1] : Fin 5 → ℕ)} := by
  classical
  ext δ
  constructor
  · intro h
    rw [support] at h
    simp only [Finset.mem_filter] at h
    rcases h with ⟨hbox, hnd, hsum⟩
    norm_num [Fin.sum_univ_five] at hsum
    have h01 : δ 0 ≤ δ 1 := hnd 0 1 (by decide)
    have h12 : δ 1 ≤ δ 2 := hnd 1 2 (by decide)
    have h23 : δ 2 ≤ δ 3 := hnd 2 3 (by decide)
    have h34 : δ 3 ≤ δ 4 := hnd 3 4 (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hδ0 : δ 0 = 0
    · by_cases hδ1 : δ 1 = 0
      · by_cases hδ2 : δ 2 = 0
        · by_cases hδ3 : δ 3 = 0
          · have hδ4 : δ 4 = 2 := by omega
            left; funext i; fin_cases i <;> simp [hδ0, hδ1, hδ2, hδ3, hδ4]
          · have hδ3one : δ 3 = 1 := by omega
            have hδ4 : δ 4 = 1 := by omega
            right; funext i; fin_cases i <;> simp [hδ0, hδ1, hδ2, hδ3one, hδ4]
        · omega
      · omega
    · omega
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · rw [h]; exact tuple_00002_mem_support_5_2
    · rw [h]; exact tuple_00011_mem_support_5_2

private lemma tuple_00003_mem_support_5_3 : (![0,0,0,0,3] : Fin 5 → ℕ) ∈ support 5 3 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma tuple_00012_mem_support_5_3 : (![0,0,0,1,2] : Fin 5 → ℕ) ∈ support 5 3 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma tuple_00111_mem_support_5_3 : (![0,0,1,1,1] : Fin 5 → ℕ) ∈ support 5 3 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma support_5_3_eq : support 5 3 =
    {(![0,0,0,0,3] : Fin 5 → ℕ), (![0,0,0,1,2] : Fin 5 → ℕ), (![0,0,1,1,1] : Fin 5 → ℕ)} := by
  classical
  ext δ
  constructor
  · intro h
    rw [support] at h
    simp only [Finset.mem_filter] at h
    rcases h with ⟨hbox, hnd, hsum⟩
    norm_num [Fin.sum_univ_five] at hsum
    have h01 : δ 0 ≤ δ 1 := hnd 0 1 (by decide)
    have h12 : δ 1 ≤ δ 2 := hnd 1 2 (by decide)
    have h23 : δ 2 ≤ δ 3 := hnd 2 3 (by decide)
    have h34 : δ 3 ≤ δ 4 := hnd 3 4 (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hδ0 : δ 0 = 0
    · by_cases hδ1 : δ 1 = 0
      · by_cases hδ2 : δ 2 = 0
        · by_cases hδ3 : δ 3 = 0
          · have hδ4 : δ 4 = 3 := by omega
            left; funext i; fin_cases i <;> simp [hδ0, hδ1, hδ2, hδ3, hδ4]
          · have hδ3' : δ 3 = 1 := by omega
            have hδ4 : δ 4 = 2 := by omega
            right; left; funext i; fin_cases i <;> simp [hδ0, hδ1, hδ2, hδ3', hδ4]
        · have hδ2' : δ 2 = 1 := by omega
          have hδ3 : δ 3 = 1 := by omega
          have hδ4 : δ 4 = 1 := by omega
          right; right; funext i; fin_cases i <;> simp [hδ0, hδ1, hδ2', hδ3, hδ4]
      · omega
    · omega
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · rw [h]; exact tuple_00003_mem_support_5_3
    · rw [h]; exact tuple_00012_mem_support_5_3
    · rw [h]; exact tuple_00111_mem_support_5_3

private lemma tuple_00004_mem_support_5_4 : (![0,0,0,0,4] : Fin 5 → ℕ) ∈ support 5 4 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma tuple_00013_mem_support_5_4 : (![0,0,0,1,3] : Fin 5 → ℕ) ∈ support 5 4 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma tuple_00022_mem_support_5_4 : (![0,0,0,2,2] : Fin 5 → ℕ) ∈ support 5 4 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma tuple_00112_mem_support_5_4 : (![0,0,1,1,2] : Fin 5 → ℕ) ∈ support 5 4 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma tuple_01111_mem_support_5_4 : (![0,1,1,1,1] : Fin 5 → ℕ) ∈ support 5 4 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma support_5_4_eq : support 5 4 =
    {(![0,0,0,0,4] : Fin 5 → ℕ), (![0,0,0,1,3] : Fin 5 → ℕ),
      (![0,0,0,2,2] : Fin 5 → ℕ), (![0,0,1,1,2] : Fin 5 → ℕ), (![0,1,1,1,1] : Fin 5 → ℕ)} := by
  classical
  ext δ
  constructor
  · intro h
    rw [support] at h
    simp only [Finset.mem_filter] at h
    rcases h with ⟨hbox, hnd, hsum⟩
    norm_num [Fin.sum_univ_five] at hsum
    have h01 : δ 0 ≤ δ 1 := hnd 0 1 (by decide)
    have h12 : δ 1 ≤ δ 2 := hnd 1 2 (by decide)
    have h23 : δ 2 ≤ δ 3 := hnd 2 3 (by decide)
    have h34 : δ 3 ≤ δ 4 := hnd 3 4 (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hδ0 : δ 0 = 0
    · by_cases hδ1 : δ 1 = 0
      · by_cases hδ2 : δ 2 = 0
        · by_cases hδ3 : δ 3 = 0
          · have hδ4 : δ 4 = 4 := by omega
            left; funext i; fin_cases i <;> simp [hδ0, hδ1, hδ2, hδ3, hδ4]
          · by_cases hδ3one : δ 3 = 1
            · have hδ4 : δ 4 = 3 := by omega
              right; left; funext i; fin_cases i <;> simp [hδ0, hδ1, hδ2, hδ3one, hδ4]
            · have hδ3two : δ 3 = 2 := by omega
              have hδ4 : δ 4 = 2 := by omega
              right; right; left; funext i; fin_cases i <;> simp [hδ0, hδ1, hδ2, hδ3two, hδ4]
        · have hδ2one : δ 2 = 1 := by omega
          have hδ3 : δ 3 = 1 := by omega
          have hδ4 : δ 4 = 2 := by omega
          right; right; right; left; funext i; fin_cases i <;> simp [hδ0, hδ1, hδ2one, hδ3, hδ4]
      · have hδ1one : δ 1 = 1 := by omega
        have hδ2 : δ 2 = 1 := by omega
        have hδ3 : δ 3 = 1 := by omega
        have hδ4 : δ 4 = 1 := by omega
        right; right; right; right; funext i; fin_cases i <;> simp [hδ0, hδ1one, hδ2, hδ3, hδ4]
    · omega
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h
    · rw [h]; exact tuple_00004_mem_support_5_4
    · rw [h]; exact tuple_00013_mem_support_5_4
    · rw [h]; exact tuple_00022_mem_support_5_4
    · rw [h]; exact tuple_00112_mem_support_5_4
    · rw [h]; exact tuple_01111_mem_support_5_4

private lemma tuple_00005_mem_support_5_5 : (![0,0,0,0,5] : Fin 5 → ℕ) ∈ support 5 5 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma tuple_00014_mem_support_5_5 : (![0,0,0,1,4] : Fin 5 → ℕ) ∈ support 5 5 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma tuple_00023_mem_support_5_5 : (![0,0,0,2,3] : Fin 5 → ℕ) ∈ support 5 5 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma tuple_00113_mem_support_5_5 : (![0,0,1,1,3] : Fin 5 → ℕ) ∈ support 5 5 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma tuple_00122_mem_support_5_5 : (![0,0,1,2,2] : Fin 5 → ℕ) ∈ support 5 5 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma tuple_01112_mem_support_5_5 : (![0,1,1,1,2] : Fin 5 → ℕ) ∈ support 5 5 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma tuple_11111_mem_support_5_5 : (![1,1,1,1,1] : Fin 5 → ℕ) ∈ support 5 5 := by
  rw [support]; simp only [Finset.mem_filter]; refine ⟨?_, ?_, ?_⟩
  · exact Fintype.mem_piFinset.mpr (by intro a; simp only [Finset.mem_range]; fin_cases a <;> simp)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [Fin.sum_univ_five]

private lemma support_5_5_eq : support 5 5 =
    {(![0,0,0,0,5] : Fin 5 → ℕ), (![0,0,0,1,4] : Fin 5 → ℕ),
      (![0,0,0,2,3] : Fin 5 → ℕ), (![0,0,1,1,3] : Fin 5 → ℕ),
      (![0,0,1,2,2] : Fin 5 → ℕ), (![0,1,1,1,2] : Fin 5 → ℕ),
      (![1,1,1,1,1] : Fin 5 → ℕ)} := by
  classical
  ext δ
  constructor
  · intro h
    rw [support] at h
    simp only [Finset.mem_filter] at h
    rcases h with ⟨hbox, hnd, hsum⟩
    norm_num [Fin.sum_univ_five] at hsum
    have h01 : δ 0 ≤ δ 1 := hnd 0 1 (by decide)
    have h12 : δ 1 ≤ δ 2 := hnd 1 2 (by decide)
    have h23 : δ 2 ≤ δ 3 := hnd 2 3 (by decide)
    have h34 : δ 3 ≤ δ 4 := hnd 3 4 (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hδ0 : δ 0 = 0
    · by_cases hδ1 : δ 1 = 0
      · by_cases hδ2 : δ 2 = 0
        · by_cases hδ3 : δ 3 = 0
          · have hδ4 : δ 4 = 5 := by omega
            left; funext i; fin_cases i <;> simp [hδ0, hδ1, hδ2, hδ3, hδ4]
          · by_cases hδ3one : δ 3 = 1
            · have hδ4 : δ 4 = 4 := by omega
              right; left; funext i; fin_cases i <;> simp [hδ0, hδ1, hδ2, hδ3one, hδ4]
            · have hδ3two : δ 3 = 2 := by omega
              have hδ4 : δ 4 = 3 := by omega
              right; right; left; funext i; fin_cases i <;> simp [hδ0, hδ1, hδ2, hδ3two, hδ4]
        · have hδ2one : δ 2 = 1 := by omega
          by_cases hδ3one : δ 3 = 1
          · have hδ4 : δ 4 = 3 := by omega
            right; right; right; left; funext i; fin_cases i <;> simp [hδ0, hδ1, hδ2one, hδ3one, hδ4]
          · have hδ3two : δ 3 = 2 := by omega
            have hδ4 : δ 4 = 2 := by omega
            right; right; right; right; left; funext i; fin_cases i <;> simp [hδ0, hδ1, hδ2one, hδ3two, hδ4]
      · have hδ1one : δ 1 = 1 := by omega
        have hδ2 : δ 2 = 1 := by omega
        have hδ3 : δ 3 = 1 := by omega
        have hδ4 : δ 4 = 2 := by omega
        right; right; right; right; right; left; funext i; fin_cases i <;> simp [hδ0, hδ1one, hδ2, hδ3, hδ4]
    · have hδ0one : δ 0 = 1 := by omega
      have hδ1 : δ 1 = 1 := by omega
      have hδ2 : δ 2 = 1 := by omega
      have hδ3 : δ 3 = 1 := by omega
      have hδ4 : δ 4 = 1 := by omega
      right; right; right; right; right; right; funext i; fin_cases i <;> simp [hδ0one, hδ1, hδ2, hδ3, hδ4]
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h | h | h
    · rw [h]; exact tuple_00005_mem_support_5_5
    · rw [h]; exact tuple_00014_mem_support_5_5
    · rw [h]; exact tuple_00023_mem_support_5_5
    · rw [h]; exact tuple_00113_mem_support_5_5
    · rw [h]; exact tuple_00122_mem_support_5_5
    · rw [h]; exact tuple_01112_mem_support_5_5
    · rw [h]; exact tuple_11111_mem_support_5_5


lemma D_4_5_0_exact : D 4 5 0 = (1 : ℚ) := by
  classical
  rw [D, support_5_0_eq]
  simp [weight, Fin.prod_univ_five]
  norm_num

lemma D_4_5_1_exact : D 4 5 1 = (1 : ℚ) / 9 := by
  classical
  rw [D, support_5_1_eq]
  simp [weight, Fin.prod_univ_five]
  norm_num

lemma D_4_5_2_exact : D 4 5 2 = (1 : ℚ) / 40 := by
  classical
  rw [D, support_5_2_eq]
  simp [weight, Fin.prod_univ_five]
  norm_num


lemma D_4_5_3_exact : D 4 5 3 = (27 : ℚ) / 6160 := by
  classical
  rw [D, support_5_3_eq]
  simp [weight, Fin.prod_univ_five]
  norm_num

lemma D_4_5_4_exact : D 4 5 4 = (223 : ℚ) / 249480 := by
  classical
  rw [D, support_5_4_eq]
  simp [weight, Fin.prod_univ_five]
  norm_num

lemma D_four_five_three_step_s_zero_one_seventy_fifth :
    D 4 5 (0 + 3) ≤ ((1 : ℚ) / 75) * D 4 5 0 := by
  rw [D_4_5_3_exact, D_4_5_0_exact]
  norm_num

lemma D_4_5_5_exact : D 4 5 5 = (491 : ℚ) / 2882880 := by
  classical
  rw [D, support_5_5_eq]
  simp [weight, Fin.prod_univ_five]
  norm_num

lemma D_4_5_5_le_one_over_3000 : D 4 5 5 ≤ (1 : ℚ) / 3000 := by
  rw [D_4_5_5_exact]
  norm_num


lemma D_four_five_three_step_s_one_one_seventy_fifth :
    D 4 5 (1 + 3) ≤ ((1 : ℚ) / 75) * D 4 5 1 := by
  rw [D_4_5_4_exact, D_4_5_1_exact]
  norm_num

lemma D_four_five_three_step_s_two_one_seventy_fifth :
    D 4 5 (2 + 3) ≤ ((1 : ℚ) / 75) * D 4 5 2 := by
  rw [D_4_5_5_exact, D_4_5_2_exact]
  norm_num

/-- Dispatcher for the `r = 5` three-step contraction that handles `s = 0,1,2`
by exact finite enumeration and leaves only the split inequality for `s ≥ 3`. -/
lemma D_four_three_step_contraction_five_one_seventy_fifth_of_split_bound_ge_three
    (hge3 : ∀ t : ℕ, 1 ≤ t →
      ((1 : ℚ) / 15120) * D 5 5 t + D 5 4 ((t + 2) + 3) ≤
        ((1 : ℚ) / 75) * D 4 5 (t + 2))
    (s : ℕ) :
    D 4 5 (s + 3) ≤ ((1 : ℚ) / 75) * D 4 5 s := by
  cases s with
  | zero =>
      simpa using D_four_five_three_step_s_zero_one_seventy_fifth
  | succ s1 =>
      cases s1 with
      | zero =>
          simpa using D_four_five_three_step_s_one_one_seventy_fifth
      | succ s2 =>
          cases s2 with
          | zero =>
              simpa using D_four_five_three_step_s_two_one_seventy_fifth
          | succ t =>
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                D_four_five_three_step_contraction_ge_two_of_split_bound (t + 1)
                  (hge3 (t + 1) (by omega))




/-- Raise the last two coordinates in length five.  This sends a nondecreasing
5-tuple of sum `t` to a nondecreasing 5-tuple of sum `t+2`. -/
private def raiseLastTwo5 (δ : Fin 5 → ℕ) : Fin 5 → ℕ :=
  fun i => if i = (3 : Fin 5) ∨ i = (4 : Fin 5) then δ i + 1 else δ i

private lemma raiseLastTwo5_injective :
    Function.Injective raiseLastTwo5 := by
  intro δ η h
  funext i
  have hi := congrFun h i
  fin_cases i <;> simp [raiseLastTwo5] at hi ⊢ <;> omega

private lemma raiseLastTwo5_mem_support_succ2 {t : ℕ} {δ : Fin 5 → ℕ}
    (hδ : δ ∈ support 5 t) : raiseLastTwo5 δ ∈ support 5 (t+2) := by
  rw [support] at hδ ⊢
  simp only [Finset.mem_filter] at hδ ⊢
  rcases hδ with ⟨hbox, hnd, hsum⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]
    intro i
    have hi := Fintype.mem_piFinset.mp hbox i
    simp only [Finset.mem_range] at hi ⊢
    fin_cases i <;> simp [raiseLastTwo5] at hi ⊢ <;> omega
  · intro i j hij
    have h01 : δ 0 ≤ δ 1 := hnd 0 1 (by decide)
    have h02 : δ 0 ≤ δ 2 := hnd 0 2 (by decide)
    have h03 : δ 0 ≤ δ 3 := hnd 0 3 (by decide)
    have h04 : δ 0 ≤ δ 4 := hnd 0 4 (by decide)
    have h12 : δ 1 ≤ δ 2 := hnd 1 2 (by decide)
    have h13 : δ 1 ≤ δ 3 := hnd 1 3 (by decide)
    have h14 : δ 1 ≤ δ 4 := hnd 1 4 (by decide)
    have h23 : δ 2 ≤ δ 3 := hnd 2 3 (by decide)
    have h24 : δ 2 ≤ δ 4 := hnd 2 4 (by decide)
    have h34 : δ 3 ≤ δ 4 := hnd 3 4 (by decide)
    fin_cases i <;> fin_cases j <;> simp [raiseLastTwo5] at hij ⊢ <;> omega
  · simp [Fin.sum_univ_five, raiseLastTwo5] at hsum ⊢
    omega

private lemma weight_five_five_le_seventytwo_weight_four_five_raiseLastTwo5
    (δ : Fin 5 → ℕ) :
    weight 5 5 δ ≤ (72 : ℚ) * weight 4 5 (raiseLastTwo5 δ) := by
  unfold weight
  rw [Fin.prod_univ_five, Fin.prod_univ_five]
  simp [raiseLastTwo5]
  let b0 : ℚ := (Nat.factorial 5 : ℚ) / (Nat.factorial (5 + δ 0) : ℚ)
  let b1 : ℚ := (Nat.factorial 6 : ℚ) / (Nat.factorial (6 + δ 1) : ℚ)
  let b2 : ℚ := (Nat.factorial 7 : ℚ) / (Nat.factorial (7 + δ 2) : ℚ)
  let b3 : ℚ := (Nat.factorial 8 : ℚ) / (Nat.factorial (8 + δ 3) : ℚ)
  let b4 : ℚ := (Nat.factorial 9 : ℚ) / (Nat.factorial (9 + δ 4) : ℚ)
  let a0 : ℚ := (Nat.factorial 4 : ℚ) / (Nat.factorial (4 + δ 0) : ℚ)
  let a1 : ℚ := (Nat.factorial 5 : ℚ) / (Nat.factorial (5 + δ 1) : ℚ)
  let a2 : ℚ := (Nat.factorial 6 : ℚ) / (Nat.factorial (6 + δ 2) : ℚ)
  let a3 : ℚ := (Nat.factorial 7 : ℚ) / (Nat.factorial (7 + (δ 3 + 1)) : ℚ)
  let a4 : ℚ := (Nat.factorial 8 : ℚ) / (Nat.factorial (8 + (δ 4 + 1)) : ℚ)
  change b0 * b1 * b2 * b3 * b4 ≤ (72 : ℚ) * (a0 * a1 * a2 * a3 * a4)
  have hb1 : 0 ≤ b1 := by dsimp [b1]; positivity
  have hb2 : 0 ≤ b2 := by dsimp [b2]; positivity
  have ha0 : 0 ≤ a0 := by dsimp [a0]; positivity
  have ha1 : 0 ≤ a1 := by dsimp [a1]; positivity
  have ha2 : 0 ≤ a2 := by dsimp [a2]; positivity
  have ha3 : 0 ≤ a3 := by dsimp [a3]; positivity
  have ha4 : 0 ≤ a4 := by dsimp [a4]; positivity
  have h0 : b0 ≤ a0 := by
    dsimp [b0, a0]
    simpa using factorial_succ_ratio_le_self 4 (δ 0)
  have h1 : b1 ≤ a1 := by
    dsimp [b1, a1]
    simpa using factorial_succ_ratio_le_self 5 (δ 1)
  have h2 : b2 ≤ a2 := by
    dsimp [b2, a2]
    simpa using factorial_succ_ratio_le_self 6 (δ 2)
  have h3 : b3 = (8 : ℚ) * a3 := by
    dsimp [b3, a3]
    rw [show 7 + (δ 3 + 1) = 8 + δ 3 by omega]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (8 + δ 3))]
    norm_num
  have h4 : b4 = (9 : ℚ) * a4 := by
    dsimp [b4, a4]
    rw [show 8 + (δ 4 + 1) = 9 + δ 4 by omega]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (9 + δ 4))]
    norm_num
  have h01 : b0 * b1 ≤ a0 * a1 := mul_le_mul h0 h1 hb1 ha0
  have h012 : b0 * b1 * b2 ≤ a0 * a1 * a2 := mul_le_mul h01 h2 hb2 (mul_nonneg ha0 ha1)
  calc
    b0 * b1 * b2 * b3 * b4 = (b0 * b1 * b2) * b3 * b4 := by ring
    _ = (b0 * b1 * b2) * ((8 : ℚ) * a3) * ((9 : ℚ) * a4) := by rw [h3, h4]
    _ ≤ (a0 * a1 * a2) * ((8 : ℚ) * a3) * ((9 : ℚ) * a4) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h012 (mul_nonneg (by norm_num) ha3))
        (mul_nonneg (by norm_num) ha4)
    _ = (72 : ℚ) * (a0 * a1 * a2 * a3 * a4) := by ring

/-- A uniform two-step `a`-contraction subbound for the remaining `r = 5` case.
It is weaker than the conjectured constant `40`, but already fits the split
budget when paired with the existing proposed `h54` constant: `72/15120 +
1/180 < 1/75`.  The proof injects each source tuple by raising the last two
coordinates. -/
lemma D5_5_to_D4_5_add2_seventytwo (t : ℕ) :
    D 5 5 t ≤ (72 : ℚ) * D 4 5 (t+2) := by
  classical
  unfold D
  let f : (Fin 5 → ℕ) → (Fin 5 → ℕ) := raiseLastTwo5
  have hinj : Set.InjOn f (support 5 t) := by
    intro δ hδ η hη h
    exact raiseLastTwo5_injective h
  have himage_subset : (support 5 t).image f ⊆ support 5 (t+2) := by
    intro η hη
    rcases Finset.mem_image.mp hη with ⟨δ, hδ, rfl⟩
    exact raiseLastTwo5_mem_support_succ2 hδ
  have hnon_image : ∀ η ∈ support 5 (t+2), η ∉ (support 5 t).image f → 0 ≤ weight 4 5 η := by
    intro η hη hnot
    exact weight_nonneg 4 5 η
  calc
    (∑ δ ∈ support 5 t, weight 5 5 δ)
        ≤ ∑ δ ∈ support 5 t, (72 : ℚ) * weight 4 5 (f δ) := by
          exact Finset.sum_le_sum (by intro δ hδ; exact weight_five_five_le_seventytwo_weight_four_five_raiseLastTwo5 δ)
    _ = (72 : ℚ) * (∑ δ ∈ support 5 t, weight 4 5 (f δ)) := by
          rw [Finset.mul_sum]
    _ = (72 : ℚ) * (∑ η ∈ (support 5 t).image f, weight 4 5 η) := by
          rw [Finset.sum_image hinj]
    _ ≤ (72 : ℚ) * (∑ η ∈ support 5 (t+2), weight 4 5 η) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg himage_subset hnon_image) (by norm_num)


/-- Normalized `a = 5, l = 4` split for the `h54` subproblem. -/
lemma D_five_four_three_step_from_two_split (t : ℕ) :
    D 5 4 (t + 5) = ((1 : ℚ) / 3024) * D 6 4 (t + 1) + D 6 3 (t + 5) := by
  have hsplit := D_split_general_four 5 (t + 1)
  norm_num at hsplit
  rw [show (t + 1) + 4 = t + 5 by omega] at hsplit
  linarith

/-- Conditional combination of the two natural `h54` split subbounds.  The
constants match the suggested budget: `1/504 + 1/350 < 1/180`. -/

lemma D_six_three_le_D_five_four (s : ℕ) : D 6 3 s ≤ D 5 4 s := by
  simpa using D_four_ge_zero_term 5 s

lemma D_five_four_three_step_from_two_three_350 (t : ℕ) :
    D 5 4 (t+5) ≤ ((3:ℚ)/350) * D 5 4 (t+2) := by
  rw [D_five_four_three_step_from_two_split t]
  have h64 := D_six_four_to_D_five_four_succ_nine (t + 1)
  have hA : ((1 : ℚ) / 3024) * D 6 4 (t + 1) ≤ ((1 : ℚ) / 336) * D 5 4 (t + 2) := by
    calc
      ((1 : ℚ) / 3024) * D 6 4 (t + 1)
          ≤ ((1 : ℚ) / 3024) * ((9 : ℚ) * D 5 4 (t + 2)) := by
            exact mul_le_mul_of_nonneg_left h64 (by norm_num)
      _ = ((1 : ℚ) / 336) * D 5 4 (t + 2) := by ring
  have h630 : D 6 3 (t + 5) ≤ ((47 : ℚ) / 8400) * D 6 3 (t + 2) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      D_six_three_three_step_contraction_fortyseven_over_8400 (t + 2)
  have h63 : D 6 3 (t + 5) ≤ ((47 : ℚ) / 8400) * D 5 4 (t + 2) := by
    exact le_trans h630
      (mul_le_mul_of_nonneg_left (D_six_three_le_D_five_four (t + 2)) (by norm_num))
  calc
    ((1 : ℚ) / 3024) * D 6 4 (t + 1) + D 6 3 (t + 5)
        ≤ ((1 : ℚ) / 336) * D 5 4 (t + 2) + ((47 : ℚ) / 8400) * D 5 4 (t + 2) :=
          add_le_add hA h63
    _ = ((3 : ℚ) / 350) * D 5 4 (t + 2) := by ring
lemma D_five_four_three_step_from_two_one_180_of_split_subbounds (t : ℕ)
    (h64 : D 6 4 (t + 1) ≤ (6 : ℚ) * D 5 4 (t + 2))
    (h63 : D 6 3 (t + 5) ≤ ((1 : ℚ) / 350) * D 5 4 (t + 2)) :
    D 5 4 (t + 5) ≤ ((1 : ℚ) / 180) * D 5 4 (t + 2) := by
  rw [D_five_four_three_step_from_two_split t]
  have hA : ((1 : ℚ) / 3024) * D 6 4 (t + 1) ≤ ((1 : ℚ) / 504) * D 5 4 (t + 2) := by
    calc
      ((1 : ℚ) / 3024) * D 6 4 (t + 1)
          ≤ ((1 : ℚ) / 3024) * ((6 : ℚ) * D 5 4 (t + 2)) := by
            exact mul_le_mul_of_nonneg_left h64 (by norm_num)
      _ = ((1 : ℚ) / 504) * D 5 4 (t + 2) := by ring
  have hnon : 0 ≤ D 5 4 (t + 2) := D_nonneg 5 4 (t + 2)
  calc
    ((1 : ℚ) / 3024) * D 6 4 (t + 1) + D 6 3 (t + 5)
        ≤ ((1 : ℚ) / 504) * D 5 4 (t + 2) + ((1 : ℚ) / 350) * D 5 4 (t + 2) :=
          add_le_add hA h63
    _ = (((1 : ℚ) / 504) + ((1 : ℚ) / 350)) * D 5 4 (t + 2) := by ring
    _ ≤ ((1 : ℚ) / 180) * D 5 4 (t + 2) := by
      exact mul_le_mul_of_nonneg_right
        (by norm_num : ((1 : ℚ) / 504) + ((1 : ℚ) / 350) ≤ (1 : ℚ) / 180) hnon

/-- The `72` two-step subbound is already small enough for the `r = 5` split,
provided the proposed `h54` three-step tail bound is available. -/
lemma D_four_five_three_step_contraction_ge_two_of_seventytwo_and_h54 (t : ℕ)
    (h54 : D 5 4 (t + 5) ≤ ((1 : ℚ) / 180) * D 5 4 (t + 2)) :
    D 4 5 ((t + 2) + 3) ≤ ((1 : ℚ) / 75) * D 4 5 (t + 2) := by
  apply D_four_five_three_step_contraction_ge_two_of_split_bound t
  have h55 := D5_5_to_D4_5_add2_seventytwo t
  have hA : ((1 : ℚ) / 15120) * D 5 5 t ≤ ((1 : ℚ) / 210) * D 4 5 (t + 2) := by
    calc
      ((1 : ℚ) / 15120) * D 5 5 t
          ≤ ((1 : ℚ) / 15120) * ((72 : ℚ) * D 4 5 (t + 2)) := by
            exact mul_le_mul_of_nonneg_left h55 (by norm_num)
      _ = ((1 : ℚ) / 210) * D 4 5 (t + 2) := by ring
  have hB0 : D 5 4 ((t + 2) + 3) ≤ ((1 : ℚ) / 180) * D 5 4 (t + 2) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h54
  have hB : D 5 4 ((t + 2) + 3) ≤ ((1 : ℚ) / 180) * D 4 5 (t + 2) := by
    exact le_trans hB0
      (mul_le_mul_of_nonneg_left (D_five_ge_zero_term 4 (t + 2)) (by norm_num))
  have hnon : 0 ≤ D 4 5 (t + 2) := D_nonneg 4 5 (t + 2)
  calc
    ((1 : ℚ) / 15120) * D 5 5 t + D 5 4 ((t + 2) + 3)
        ≤ ((1 : ℚ) / 210) * D 4 5 (t + 2) + ((1 : ℚ) / 180) * D 4 5 (t + 2) :=
          add_le_add hA hB
    _ = (((1 : ℚ) / 210) + ((1 : ℚ) / 180)) * D 4 5 (t + 2) := by ring
    _ ≤ ((1 : ℚ) / 75) * D 4 5 (t + 2) := by
      exact mul_le_mul_of_nonneg_right (by norm_num : ((1 : ℚ) / 210) + ((1 : ℚ) / 180) ≤ (1 : ℚ) / 75) hnon

lemma D_four_five_three_step_contraction_ge_two_of_seventytwo_and_h54_three_350 (t : ℕ)
    (h54 : D 5 4 (t + 5) ≤ ((3 : ℚ) / 350) * D 5 4 (t + 2)) :
    D 4 5 ((t + 2) + 3) ≤ ((1 : ℚ) / 75) * D 4 5 (t + 2) := by
  apply D_four_five_three_step_contraction_ge_two_of_split_bound t
  have h55 := D5_5_to_D4_5_add2_seventytwo t
  have hA : ((1 : ℚ) / 15120) * D 5 5 t ≤ ((1 : ℚ) / 210) * D 4 5 (t + 2) := by
    calc
      ((1 : ℚ) / 15120) * D 5 5 t
          ≤ ((1 : ℚ) / 15120) * ((72 : ℚ) * D 4 5 (t + 2)) := by
            exact mul_le_mul_of_nonneg_left h55 (by norm_num)
      _ = ((1 : ℚ) / 210) * D 4 5 (t + 2) := by ring
  have hB0 : D 5 4 ((t + 2) + 3) ≤ ((3 : ℚ) / 350) * D 5 4 (t + 2) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h54
  have hB : D 5 4 ((t + 2) + 3) ≤ ((3 : ℚ) / 350) * D 4 5 (t + 2) := by
    exact le_trans hB0
      (mul_le_mul_of_nonneg_left (D_five_ge_zero_term 4 (t + 2)) (by norm_num))
  calc
    ((1 : ℚ) / 15120) * D 5 5 t + D 5 4 ((t + 2) + 3)
        ≤ ((1 : ℚ) / 210) * D 4 5 (t + 2) + ((3 : ℚ) / 350) * D 4 5 (t + 2) :=
          add_le_add hA hB
    _ = ((1 : ℚ) / 75) * D 4 5 (t + 2) := by ring

lemma D_four_five_three_step_contraction_five_one_seventy_fifth (s : ℕ) :
    D 4 5 (s + 3) ≤ ((1 : ℚ) / 75) * D 4 5 s := by
  cases s with
  | zero =>
      simpa using D_four_five_three_step_s_zero_one_seventy_fifth
  | succ s1 =>
      cases s1 with
      | zero =>
          simpa using D_four_five_three_step_s_one_one_seventy_fifth
      | succ t =>
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            D_four_five_three_step_contraction_ge_two_of_seventytwo_and_h54_three_350 t
              (D_five_four_three_step_from_two_three_350 t)

/-- Consequently, after the two exact small cases, the only remaining uniform
subbound needed for the `r = 5` contraction is the `h54` tail estimate. -/
lemma D_four_three_step_contraction_five_one_seventy_fifth_of_h54
    (h54 : ∀ t : ℕ, D 5 4 (t + 5) ≤ ((1 : ℚ) / 180) * D 5 4 (t + 2))
    (s : ℕ) :
    D 4 5 (s + 3) ≤ ((1 : ℚ) / 75) * D 4 5 s := by
  cases s with
  | zero =>
      simpa using D_four_five_three_step_s_zero_one_seventy_fifth
  | succ s1 =>
      cases s1 with
      | zero =>
          simpa using D_four_five_three_step_s_one_one_seventy_fifth
      | succ t =>
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            D_four_five_three_step_contraction_ge_two_of_seventytwo_and_h54 t (h54 t)


/-- Formal combination of the two empirical tail estimates suggested for the
`r = 5`, `s = t + 2` case.  Proving the two hypotheses uniformly would finish
all remaining non-small indices, since `1/378 + 1/180 < 1/75`. -/
lemma D_four_five_three_step_contraction_ge_two_of_empirical_subbounds (t : ℕ)
    (h55 : D 5 5 t ≤ (40 : ℚ) * D 4 5 (t + 2))
    (h54 : D 5 4 (t + 5) ≤ ((1 : ℚ) / 180) * D 5 4 (t + 2)) :
    D 4 5 ((t + 2) + 3) ≤ ((1 : ℚ) / 75) * D 4 5 (t + 2) := by
  apply D_four_five_three_step_contraction_ge_two_of_split_bound t
  have hA : ((1 : ℚ) / 15120) * D 5 5 t ≤ ((1 : ℚ) / 378) * D 4 5 (t + 2) := by
    calc
      ((1 : ℚ) / 15120) * D 5 5 t
          ≤ ((1 : ℚ) / 15120) * ((40 : ℚ) * D 4 5 (t + 2)) := by
            exact mul_le_mul_of_nonneg_left h55 (by norm_num)
      _ = ((1 : ℚ) / 378) * D 4 5 (t + 2) := by ring
  have hB0 : D 5 4 ((t + 2) + 3) ≤ ((1 : ℚ) / 180) * D 5 4 (t + 2) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h54
  have hB : D 5 4 ((t + 2) + 3) ≤ ((1 : ℚ) / 180) * D 4 5 (t + 2) := by
    exact le_trans hB0
      (mul_le_mul_of_nonneg_left (D_five_ge_zero_term 4 (t + 2)) (by norm_num))
  have hnon : 0 ≤ D 4 5 (t + 2) := D_nonneg 4 5 (t + 2)
  calc
    ((1 : ℚ) / 15120) * D 5 5 t + D 5 4 ((t + 2) + 3)
        ≤ ((1 : ℚ) / 378) * D 4 5 (t + 2) + ((1 : ℚ) / 180) * D 4 5 (t + 2) :=
          add_le_add hA hB
    _ = (((1 : ℚ) / 378) + ((1 : ℚ) / 180)) * D 4 5 (t + 2) := by ring
    _ ≤ ((1 : ℚ) / 75) * D 4 5 (t + 2) := by
      exact mul_le_mul_of_nonneg_right (by norm_num : ((1 : ℚ) / 378) + ((1 : ℚ) / 180) ≤ (1 : ℚ) / 75) hnon

/-- If the two suggested tail subgoals are supplied for every `t`, the `r = 5`
three-step contraction follows for every `s`; the cases `s = 0, 1` are handled
below by exact enumeration. -/
lemma D_four_three_step_contraction_five_one_seventy_fifth_of_empirical_subbounds
    (h55 : ∀ t : ℕ, D 5 5 t ≤ (40 : ℚ) * D 4 5 (t + 2))
    (h54 : ∀ t : ℕ, D 5 4 (t + 5) ≤ ((1 : ℚ) / 180) * D 5 4 (t + 2))
    (s : ℕ) :
    D 4 5 (s + 3) ≤ ((1 : ℚ) / 75) * D 4 5 s := by
  cases s with
  | zero =>
      simpa using D_four_five_three_step_s_zero_one_seventy_fifth
  | succ s1 =>
      cases s1 with
      | zero =>
          simpa using D_four_five_three_step_s_one_one_seventy_fifth
      | succ t =>
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            D_four_five_three_step_contraction_ge_two_of_empirical_subbounds t (h55 t) (h54 t)







/-- A three-step contraction for `D 4` in the large-fiber range.  The originally
suggested constant `1/90` is not valid uniformly (already `r=4, s=1` is a
counterexample), but the existing sharp one-step estimate gives this useful
`1/75` contraction for `r ≥ 23`. -/
lemma D_four_three_step_contraction_large_one_seventy_fifth (r s : ℕ) (hr : 23 ≤ r) :
    D 4 r (s + 3) ≤ ((1 : ℚ) / 75) * D 4 r s := by
  have hrpos : 0 < r := by omega
  let c : ℚ := (1 : ℚ) / (4 + 1 : ℕ) + (1 : ℚ) / (4 + r : ℕ)
  have hc_nonneg : 0 ≤ c := by dsimp [c]; positivity
  have hstep : D 4 r (s + 3) ≤ c ^ 3 * D 4 r s := by
    simpa [c, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (iterated_contraction (D 4 r) c hc_nonneg
        (fun n => by
          simpa [c, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            D_one_step_bound_sharp_general_pos_l 4 r n hrpos) 3 s)
  have hnonD : 0 ≤ D 4 r s := D_nonneg 4 r s
  have hden : (27 : ℚ) ≤ (4 + r : ℕ) := by exact_mod_cast (by omega : 27 ≤ 4 + r)
  have hinv : (1 : ℚ) / (4 + r : ℕ) ≤ (1 : ℚ) / 27 := by
    exact one_div_le_one_div_of_le (by norm_num) hden
  have hc_le : c ≤ (32 : ℚ) / 135 := by
    calc
      c = (1 : ℚ) / 5 + (1 : ℚ) / (4 + r : ℕ) := by norm_num [c]
      _ ≤ (1 : ℚ) / 5 + (1 : ℚ) / 27 := add_le_add (le_refl ((1 : ℚ) / 5)) hinv
      _ = (32 : ℚ) / 135 := by norm_num
  have hc3 : c ^ 3 ≤ (1 : ℚ) / 75 := by
    have hA_nonneg : (0 : ℚ) ≤ (32 : ℚ) / 135 := by norm_num
    have hc2 : c ^ 2 ≤ ((32 : ℚ) / 135) ^ 2 := by
      simpa [pow_two] using mul_le_mul hc_le hc_le hc_nonneg hA_nonneg
    have hcube : c ^ 2 * c ≤ ((32 : ℚ) / 135) ^ 2 * ((32 : ℚ) / 135) := by
      exact mul_le_mul hc2 hc_le hc_nonneg (by positivity)
    norm_num at hcube ⊢
    linarith
  exact le_trans hstep (mul_le_mul_of_nonneg_right hc3 hnonD)

/-- Short-name alias for the usable `1/75` large-range `D 4` three-step contraction. -/
lemma D_four_three_step_contraction_large (r s : ℕ) (hr : 23 ≤ r) :
    D 4 r (s + 3) ≤ ((1 : ℚ) / 75) * D 4 r s :=
  D_four_three_step_contraction_large_one_seventy_fifth r s hr


-- The same large-r argument gives the sharper `1/80` constant from `r ≥ 28`.


/-- Partial dispatcher: the desired `1/75` three-step contraction is proved here
for the one-dimensional case and for the existing large range `r ≥ 23`. -/
lemma D_four_three_step_contraction_one_or_large_one_seventy_fifth (r s : ℕ)
    (hr : r = 1 ∨ 23 ≤ r) :
    D 4 r (s + 3) ≤ ((1 : ℚ) / 75) * D 4 r s := by
  rcases hr with rfl | hlarge
  · exact D_four_three_step_contraction_one_one_seventy_fifth s
  · exact D_four_three_step_contraction_large_one_seventy_fifth r s hlarge


lemma D_four_three_step_contraction_one_two_or_large_one_seventy_fifth (r s : ℕ)
    (hr : r = 1 ∨ r = 2 ∨ 23 ≤ r) :
    D 4 r (s + 3) ≤ ((1 : ℚ) / 75) * D 4 r s := by
  rcases hr with rfl | hr
  · exact D_four_three_step_contraction_one_one_seventy_fifth s
  rcases hr with rfl | hlarge
  · exact D_four_three_step_contraction_two_one_seventy_fifth s
  · exact D_four_three_step_contraction_large_one_seventy_fifth r s hlarge

lemma D_four_three_step_contraction_one_two_three_or_large_one_seventy_fifth (r s : ℕ)
    (hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ 23 ≤ r) :
    D 4 r (s + 3) ≤ ((1 : ℚ) / 75) * D 4 r s := by
  rcases hr with rfl | hr
  · exact D_four_three_step_contraction_one_one_seventy_fifth s
  rcases hr with rfl | hr
  · exact D_four_three_step_contraction_two_one_seventy_fifth s
  rcases hr with rfl | hlarge
  · exact D_four_three_step_contraction_three_one_seventy_fifth s
  · exact D_four_three_step_contraction_large_one_seventy_fifth r s hlarge




lemma D_four_three_step_contraction_one_two_three_four_or_large_one_seventy_fifth (r s : ℕ)
    (hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ 23 ≤ r) :
    D 4 r (s + 3) ≤ ((1 : ℚ) / 75) * D 4 r s := by
  rcases hr with rfl | hr
  · exact D_four_three_step_contraction_one_one_seventy_fifth s
  rcases hr with rfl | hr
  · exact D_four_three_step_contraction_two_one_seventy_fifth s
  rcases hr with rfl | hr
  · exact D_four_three_step_contraction_three_one_seventy_fifth s
  rcases hr with rfl | hlarge
  · exact D_four_three_step_contraction_four_one_seventy_fifth s
  · exact D_four_three_step_contraction_large_one_seventy_fifth r s hlarge


lemma D_four_three_step_contraction_one_two_three_four_five_or_large_one_seventy_fifth (r s : ℕ)
    (hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ 23 ≤ r) :
    D 4 r (s + 3) ≤ ((1 : ℚ) / 75) * D 4 r s := by
  rcases hr with rfl | hr
  · exact D_four_three_step_contraction_one_one_seventy_fifth s
  rcases hr with rfl | hr
  · exact D_four_three_step_contraction_two_one_seventy_fifth s
  rcases hr with rfl | hr
  · exact D_four_three_step_contraction_three_one_seventy_fifth s
  rcases hr with rfl | hr
  · exact D_four_three_step_contraction_four_one_seventy_fifth s
  rcases hr with rfl | hlarge
  · exact D_four_five_three_step_contraction_five_one_seventy_fifth s
  · exact D_four_three_step_contraction_large_one_seventy_fifth r s hlarge



/-- Generic recursive reduction for `Fscaled`: a contraction estimate for the
positive branch and a bound for the lower-dimensional tail imply a bound at the
previous level. -/
lemma Fscaled_bound_from_contraction_and_tail
    (a : ℕ) (ha : 1 ≤ a) (A B C : ℚ)
    (hBnon : 0 ≤ B)
    (hC : (a : ℚ) * A + (a : ℚ) * B ≤ C)
    (hD : ∀ r s : ℕ, 1 ≤ r → D (a+1) r (s+a) ≤ A * D (a+1) r s)
    (hF : ∀ r s : ℕ, 1 ≤ r → Fscaled (a+1) r s ≤ B * D (a+2) r s) :
    ∀ r s : ℕ, 1 ≤ r → Fscaled a r s ≤ C * D (a+1) r s := by
  intro r s hr
  cases r with
  | zero => omega
  | succ m =>
      have hsplit := Fscaled_split_succ a m s ha
      rw [hsplit]
      by_cases hm0 : m = 0
      · subst m
        have hz : Fscaled (a+1) 0 s = 0 := by
          unfold Fscaled
          have hzD : D (a+1) 0 (s+0+(a+1)) = 0 := by
            simpa using D_zero_of_pos (a := a+1) (N := s+0+(a+1)) (by omega)
          rw [hzD]
          ring
        rw [hz]
        have hpos := hD 1 s (by decide)
        have hDnon : 0 ≤ D (a+1) 1 s := D_nonneg (a+1) 1 s
        calc
          (a : ℚ) * D (a + 1) 1 (s + a) + (a : ℚ) * 0
              ≤ (a : ℚ) * (A * D (a+1) 1 s) + 0 := by
                exact add_le_add (mul_le_mul_of_nonneg_left hpos (by positivity)) (by simp)
          _ = ((a : ℚ) * A) * D (a+1) 1 s := by ring
          _ ≤ C * D (a+1) 1 s := by
                have hAB : (a : ℚ) * A ≤ (a : ℚ) * A + (a : ℚ) * B := by
                  have hterm : 0 ≤ (a : ℚ) * B := mul_nonneg (by positivity) hBnon
                  linarith
                exact mul_le_mul_of_nonneg_right (le_trans hAB hC) hDnon
      · have hmpos : 1 ≤ m := by omega
        have hpos := hD (m+1) s (by omega)
        have htail0 := hF m s hmpos
        have hembed : D (a+2) m s ≤ D (a+1) (m+1) s := by
          simpa using D_ge_zero_tail_general (a+1) m s
        have htail : Fscaled (a+1) m s ≤ B * D (a+1) (m+1) s := by
          exact le_trans htail0 (mul_le_mul_of_nonneg_left hembed hBnon)
        have hDnon : 0 ≤ D (a+1) (m+1) s := D_nonneg (a+1) (m+1) s
        calc
          (a : ℚ) * D (a + 1) (m + 1) (s + a) + (a : ℚ) * Fscaled (a+1) m s
              ≤ (a : ℚ) * (A * D (a+1) (m+1) s) +
                  (a : ℚ) * (B * D (a+1) (m+1) s) := by
                    exact add_le_add (mul_le_mul_of_nonneg_left hpos (by positivity))
                      (mul_le_mul_of_nonneg_left htail (by positivity))
          _ = ((a : ℚ) * A + (a : ℚ) * B) * D (a+1) (m+1) s := by ring
          _ ≤ C * D (a+1) (m+1) s := by
                exact mul_le_mul_of_nonneg_right hC hDnon


lemma D_five_four_step_contraction_large_one_ninehundred (r s : ℕ) (hr : 58 ≤ r) :
    D 5 r (s + 4) ≤ ((1 : ℚ) / 900) * D 5 r s := by
  have hrpos : 0 < r := by omega
  let c : ℚ := (1 : ℚ) / (5 + 1 : ℕ) + (1 : ℚ) / (5 + r : ℕ)
  have hstep : D 5 r (s + 4) ≤ c ^ 4 * D 5 r s := by
    have h := iterated_contraction (D 5 r) c (by positivity)
      (fun n => by simpa [c] using D_one_step_bound_sharp_general_pos_l 5 r n hrpos) 4 s
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hnonD : 0 ≤ D 5 r s := D_nonneg 5 r s
  have hc_nonneg : 0 ≤ c := by dsimp [c]; positivity
  have hden : (63 : ℚ) ≤ (5 + r : ℕ) := by exact_mod_cast (by omega : 63 ≤ 5 + r)
  have hinv : (1 : ℚ) / (5 + r : ℕ) ≤ (1 : ℚ) / 63 := by
    exact one_div_le_one_div_of_le (by norm_num) hden
  have hc_le : c ≤ (23 : ℚ) / 126 := by
    calc
      c = (1 : ℚ) / 6 + (1 : ℚ) / (5 + r : ℕ) := by norm_num [c]
      _ ≤ (1 : ℚ) / 6 + (1 : ℚ) / 63 := by
        linarith [add_le_add_left hinv ((1 : ℚ) / 6)]
      _ = (23 : ℚ) / 126 := by norm_num
  have hc4 : c ^ 4 ≤ (1 : ℚ) / 900 := by
    have hA_nonneg : (0 : ℚ) ≤ (23 : ℚ) / 126 := by norm_num
    have hc2 : c ^ 2 ≤ ((23 : ℚ) / 126) ^ 2 := by
      simpa [pow_two] using mul_le_mul hc_le hc_le hc_nonneg hA_nonneg
    have hc4' : c ^ 2 * c ^ 2 ≤ ((23 : ℚ) / 126) ^ 2 * ((23 : ℚ) / 126) ^ 2 := by
      exact mul_le_mul hc2 hc2 (by positivity) (by positivity)
    norm_num at hc4' ⊢
    linarith
  exact le_trans hstep (mul_le_mul_of_nonneg_right hc4 hnonD)


lemma F4_two_225_from_D5_F5
    (hD5 : ∀ r s : ℕ, 1 ≤ r → D 5 r (s+4) ≤ ((1 : ℚ) / 900) * D 5 r s)
    (hF5 : ∀ r s : ℕ, 1 ≤ r → Fscaled 5 r s ≤ ((1 : ℚ) / 900) * D 6 r s) :
    ∀ r s : ℕ, 1 ≤ r → Fscaled 4 r s ≤ ((2 : ℚ) / 225) * D 5 r s := by
  exact Fscaled_bound_from_contraction_and_tail 4 (by decide)
    ((1 : ℚ) / 900) ((1 : ℚ) / 900) ((2 : ℚ) / 225)
    (by norm_num) (by norm_num) hD5 hF5




lemma F3_one_fifteenth_from_D4_75_F4
    (hD4 : ∀ r s : ℕ, 1 ≤ r → D 4 r (s+3) ≤ ((1 : ℚ) / 75) * D 4 r s)
    (hF4 : ∀ r s : ℕ, 1 ≤ r → Fscaled 4 r s ≤ ((2 : ℚ) / 225) * D 5 r s) :
    ∀ r s : ℕ, 1 ≤ r → Fscaled 3 r s ≤ ((1 : ℚ) / 15) * D 4 r s := by
  intro r s hr
  cases r with
  | zero => omega
  | succ m =>
      have hsplit := Fscaled_split_succ 3 m s (by decide)
      rw [hsplit]
      by_cases hm0 : m = 0
      · subst m
        have hz : Fscaled 4 0 s = 0 := by
          unfold Fscaled
          have hzD : D 4 0 (s+0+4) = 0 := by
            simpa using D_zero_of_pos (a := 4) (N := s+0+4) (by omega)
          rw [hzD]
          ring
        rw [hz]
        have hfirst := hD4 1 s (by decide)
        have hDnon : 0 ≤ D 4 1 s := D_nonneg 4 1 s
        calc
          (3 : ℚ) * D 4 1 (s + 3) + (3 : ℚ) * 0
              ≤ (3 : ℚ) * (((1:ℚ)/75) * D 4 1 s) + 0 := by
                exact add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num)) (by norm_num)
          _ ≤ ((1:ℚ)/15) * D 4 1 s := by
                nlinarith
      · have hmpos : 1 ≤ m := by omega
        have hfirst := hD4 (m+1) s (by omega)
        have htail0 := hF4 m s hmpos
        have hembed : D 5 m s ≤ D 4 (m+1) s := by
          simpa using D_ge_zero_tail_general 4 m s
        have htail : Fscaled 4 m s ≤ ((2:ℚ)/225) * D 4 (m+1) s := by
          exact le_trans htail0 (mul_le_mul_of_nonneg_left hembed (by norm_num))
        have hDnon : 0 ≤ D 4 (m+1) s := D_nonneg 4 (m+1) s
        calc
          (3 : ℚ) * D 4 (m+1) (s + 3) + (3 : ℚ) * Fscaled 4 m s
              ≤ (3 : ℚ) * (((1:ℚ)/75) * D 4 (m+1) s) +
                  (3 : ℚ) * (((2:ℚ)/225) * D 4 (m+1) s) := by
                    exact add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num))
                      (mul_le_mul_of_nonneg_left htail (by norm_num))
          _ = ((1:ℚ)/15) * D 4 (m+1) s := by ring


lemma D_four_three_step_contraction_large_one_eightieth (r s : ℕ) (hr : 28 ≤ r) :
    D 4 r (s + 3) ≤ ((1 : ℚ) / 80) * D 4 r s := by
  have hrpos : 0 < r := by omega
  let c : ℚ := (1 : ℚ) / (4 + 1 : ℕ) + (1 : ℚ) / (4 + r : ℕ)
  have hc_nonneg : 0 ≤ c := by dsimp [c]; positivity
  have hstep : D 4 r (s + 3) ≤ c ^ 3 * D 4 r s := by
    simpa [c, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (iterated_contraction (D 4 r) c hc_nonneg
        (fun n => by
          simpa [c, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            D_one_step_bound_sharp_general_pos_l 4 r n hrpos) 3 s)
  have hnonD : 0 ≤ D 4 r s := D_nonneg 4 r s
  have hden : (32 : ℚ) ≤ (4 + r : ℕ) := by exact_mod_cast (by omega : 32 ≤ 4 + r)
  have hinv : (1 : ℚ) / (4 + r : ℕ) ≤ (1 : ℚ) / 32 := by
    exact one_div_le_one_div_of_le (by norm_num) hden
  have hc_le : c ≤ (37 : ℚ) / 160 := by
    calc
      c = (1 : ℚ) / 5 + (1 : ℚ) / (4 + r : ℕ) := by norm_num [c]
      _ ≤ (1 : ℚ) / 5 + (1 : ℚ) / 32 := add_le_add (le_refl ((1 : ℚ) / 5)) hinv
      _ = (37 : ℚ) / 160 := by norm_num
  have hc3 : c ^ 3 ≤ (1 : ℚ) / 80 := by
    have hA_nonneg : (0 : ℚ) ≤ (37 : ℚ) / 160 := by norm_num
    have hc2 : c ^ 2 ≤ ((37 : ℚ) / 160) ^ 2 := by
      simpa [pow_two] using mul_le_mul hc_le hc_le hc_nonneg hA_nonneg
    have hcube : c ^ 2 * c ≤ ((37 : ℚ) / 160) ^ 2 * ((37 : ℚ) / 160) := by
      exact mul_le_mul hc2 hc_le hc_nonneg (by positivity)
    norm_num at hcube ⊢
    linarith
  exact le_trans hstep (mul_le_mul_of_nonneg_right hc3 hnonD)

/-- For reference, the requested `1/90` constant follows from the one-step
machinery only in the still larger range `r ≥ 40`; it is false uniformly. -/
lemma D_four_three_step_contraction_large_one_ninetieth (r s : ℕ) (hr : 40 ≤ r) :
    D 4 r (s + 3) ≤ ((1 : ℚ) / 90) * D 4 r s := by
  have hrpos : 0 < r := by omega
  let c : ℚ := (1 : ℚ) / (4 + 1 : ℕ) + (1 : ℚ) / (4 + r : ℕ)
  have hc_nonneg : 0 ≤ c := by dsimp [c]; positivity
  have hstep : D 4 r (s + 3) ≤ c ^ 3 * D 4 r s := by
    simpa [c, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (iterated_contraction (D 4 r) c hc_nonneg
        (fun n => by
          simpa [c, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            D_one_step_bound_sharp_general_pos_l 4 r n hrpos) 3 s)
  have hnonD : 0 ≤ D 4 r s := D_nonneg 4 r s
  have hden : (44 : ℚ) ≤ (4 + r : ℕ) := by exact_mod_cast (by omega : 44 ≤ 4 + r)
  have hinv : (1 : ℚ) / (4 + r : ℕ) ≤ (1 : ℚ) / 44 := by
    exact one_div_le_one_div_of_le (by norm_num) hden
  have hc_le : c ≤ (49 : ℚ) / 220 := by
    calc
      c = (1 : ℚ) / 5 + (1 : ℚ) / (4 + r : ℕ) := by norm_num [c]
      _ ≤ (1 : ℚ) / 5 + (1 : ℚ) / 44 := add_le_add (le_refl ((1 : ℚ) / 5)) hinv
      _ = (49 : ℚ) / 220 := by norm_num
  have hc3 : c ^ 3 ≤ (1 : ℚ) / 90 := by
    have hA_nonneg : (0 : ℚ) ≤ (49 : ℚ) / 220 := by norm_num
    have hc2 : c ^ 2 ≤ ((49 : ℚ) / 220) ^ 2 := by
      simpa [pow_two] using mul_le_mul hc_le hc_le hc_nonneg hA_nonneg
    have hcube : c ^ 2 * c ≤ ((49 : ℚ) / 220) ^ 2 * ((49 : ℚ) / 220) := by
      exact mul_le_mul hc2 hc_le hc_nonneg (by positivity)
    norm_num at hcube ⊢
    linarith
  exact le_trans hstep (mul_le_mul_of_nonneg_right hc3 hnonD)



lemma F3_one_fifteenth_from_D4_F4
    (hD4 : ∀ r s : ℕ, 1 ≤ r → D 4 r (s+3) ≤ ((1 : ℚ) / 90) * D 4 r s)
    (hF4 : ∀ r s : ℕ, 1 ≤ r → Fscaled 4 r s ≤ ((1 : ℚ) / 90) * D 5 r s) :
    ∀ r s : ℕ, 1 ≤ r → Fscaled 3 r s ≤ ((1 : ℚ) / 15) * D 4 r s := by
  intro r s hr
  cases r with
  | zero => omega
  | succ m =>
      have hsplit := Fscaled_split_succ 3 m s (by decide)
      rw [hsplit]
      have hm_cases : m = 0 ∨ 1 ≤ m := by omega
      rcases hm_cases with rfl | hmpos
      · have hz : Fscaled 4 0 s = 0 := by
          unfold Fscaled
          have hzD : D 4 0 (s+0+4) = 0 := by
            simpa using D_zero_of_pos (a := 4) (N := s+0+4) (by omega)
          rw [hzD]
          ring
        rw [hz]
        have hfirst := hD4 1 s (by decide)
        have hDnon : 0 ≤ D 4 1 s := D_nonneg 4 1 s
        calc
          (3 : ℚ) * D 4 1 (s + 3) + (3 : ℚ) * 0
              ≤ (3 : ℚ) * (((1:ℚ)/90) * D 4 1 s) + 0 := by
                exact add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num)) (by norm_num)
          _ ≤ ((1:ℚ)/15) * D 4 1 s := by
                nlinarith
      · have hfirst := hD4 (m+1) s (by omega)
        have htail0 := hF4 m s hmpos
        have hembed : D 5 m s ≤ D 4 (m+1) s := by
          simpa using D_ge_zero_tail_general 4 m s
        have htail : Fscaled 4 m s ≤ ((1:ℚ)/90) * D 4 (m+1) s := by
          exact le_trans htail0 (mul_le_mul_of_nonneg_left hembed (by norm_num))
        have hDnon : 0 ≤ D 4 (m+1) s := D_nonneg 4 (m+1) s
        calc
          (3 : ℚ) * D 4 (m+1) (s + 3) + (3 : ℚ) * Fscaled 4 m s
              ≤ (3 : ℚ) * (((1:ℚ)/90) * D 4 (m+1) s) +
                  (3 : ℚ) * (((1:ℚ)/90) * D 4 (m+1) s) := by
                    exact add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num))
                      (mul_le_mul_of_nonneg_left htail (by norm_num))
          _ = ((1:ℚ)/15) * D 4 (m+1) s := by ring















end DOneStepNoAxiom
