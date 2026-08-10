import FormalConjectures.Util.ProblemImports

open Nat
open Filter Finset
open scoped BigOperators Topology


/--
A386660: $a(n) = \sum_{k=1}^n \binom{n}{k} \pmod{2^k}$.
-/
def a (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sum fun k => (n.choose k) % (2 ^ k)

namespace Proof

lemma a_pos {n : ℕ} (hn : 0 < n) : 0 < a n := by
  unfold a
  have hnmem : n ∈ Finset.Icc 1 n := by
    simp [Finset.mem_Icc]
    omega
  have hterm : ((n.choose n) % (2 ^ n)) = 1 := by
    rw [Nat.choose_self]
    exact Nat.mod_eq_of_lt (by have : 1 < 2 ^ n := Nat.one_lt_two_pow hn.ne'; exact this)
  have hle : 1 ≤ (Finset.Icc 1 n).sum (fun k => (n.choose k) % (2 ^ k)) := by
    calc
      1 = (n.choose n) % (2 ^ n) := hterm.symm
      _ ≤ (Finset.Icc 1 n).sum (fun k => (n.choose k) % (2 ^ k)) := by
        simpa using (Finset.single_le_sum
          (s := Finset.Icc 1 n)
          (f := fun k => (n.choose k) % (2 ^ k))
          (by intro b hb; exact Nat.zero_le _) hnmem)
  exact Nat.succ_le_iff.mp hle


noncomputable def g (x : ℝ) : ℝ := Real.binEntropy x - x * Real.log 2

lemma exists_entropyRoot : ∃ r : ℝ, r ∈ Set.Icc (2⁻¹ : ℝ) 1 ∧ g r = 0 := by
  have hcont : ContinuousOn g (Set.Icc (2⁻¹ : ℝ) 1) := by
    unfold g
    fun_prop
  have hhalf : 0 ≤ g (2⁻¹ : ℝ) := by
    unfold g
    rw [Real.binEntropy_two_inv]
    nlinarith [(Real.log_pos one_lt_two).le]
  have hone : g (1 : ℝ) ≤ 0 := by
    unfold g
    simp
    exact (Real.log_pos one_lt_two).le
  rcases intermediate_value_Icc' (show (2⁻¹ : ℝ) ≤ 1 by norm_num) hcont ⟨hone, hhalf⟩ with ⟨r, hrmem, hr⟩
  exact ⟨r, hrmem, hr⟩

noncomputable def entropyRoot : ℝ := Classical.choose exists_entropyRoot

lemma entropyRoot_mem : entropyRoot ∈ Set.Icc (2⁻¹ : ℝ) 1 :=
  (Classical.choose_spec exists_entropyRoot).1

lemma entropyRoot_eq : Real.binEntropy entropyRoot = entropyRoot * Real.log 2 := by
  have h := (Classical.choose_spec exists_entropyRoot).2
  change g entropyRoot = 0 at h
  unfold g at h
  linarith


lemma entropyRoot_lt_one : entropyRoot < (1 : ℝ) := by
  have hroot := (Classical.choose_spec exists_entropyRoot).2
  change g entropyRoot = 0 at hroot
  have hone : g (1 : ℝ) < 0 := by
    unfold g
    simp
    exact Real.log_pos one_lt_two
  by_contra h
  have : entropyRoot = 1 := le_antisymm entropyRoot_mem.2 (le_of_not_gt h)
  rw [this] at hroot
  linarith

lemma exists_right_entropy_gt {b : ℝ} (hb : b < entropyRoot * Real.log 2) :
    ∃ y : ℝ, entropyRoot < y ∧ y < 1 ∧ b < Real.binEntropy y := by
  have hb' : b < Real.binEntropy entropyRoot := by rwa [entropyRoot_eq]
  have hev : ∀ᶠ y in nhds entropyRoot, b < Real.binEntropy y := by
    have hopen : IsOpen {y : ℝ | b < Real.binEntropy y} :=
      isOpen_lt continuous_const Real.binEntropy_continuous
    exact hopen.mem_nhds hb'
  rcases Metric.mem_nhds_iff.mp hev with ⟨δ, hδpos, hδsub⟩
  let ε := min δ (1 - entropyRoot)
  have hεpos : 0 < ε := lt_min hδpos (sub_pos.mpr entropyRoot_lt_one)
  rcases exists_between (show (0:ℝ) < ε by exact hεpos) with ⟨t, ht0, htε⟩
  refine ⟨entropyRoot + t, by linarith, ?_, ?_⟩
  · have ht_lt_one : t < 1 - entropyRoot := lt_of_lt_of_le htε (min_le_right _ _)
    linarith
  · apply hδsub
    rw [Metric.mem_ball, Real.dist_eq]
    have htδ : t < δ := lt_of_lt_of_le htε (min_le_left _ _)
    rw [abs_lt]
    constructor <;> linarith

lemma half_le_entropyRoot : (2⁻¹ : ℝ) ≤ entropyRoot := entropyRoot_mem.1
lemma entropyRoot_le_one : entropyRoot ≤ (1 : ℝ) := entropyRoot_mem.2

lemma min_entropy_line_le_root (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    min (Real.binEntropy x) (x * Real.log 2) ≤ entropyRoot * Real.log 2 := by
  by_cases hxr : x ≤ entropyRoot
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right hxr (Real.log_pos one_lt_two).le)
  · have hrx : entropyRoot ≤ x := le_of_not_ge hxr
    have hxhalf : (2⁻¹ : ℝ) ≤ x := half_le_entropyRoot.trans hrx
    have hanti := Real.binEntropy_strictAntiOn.antitoneOn
    have hent : Real.binEntropy x ≤ Real.binEntropy entropyRoot := by
      exact hanti entropyRoot_mem ⟨hxhalf, hx1⟩ hrx
    rw [entropyRoot_eq] at hent
    exact (min_le_left _ _).trans hent



lemma choose_mul_prob_le_one (n k : ℕ) (hk : k ≤ n) :
    ((n.choose k : ℝ) * ((k : ℝ) / n) ^ k * (((n - k : ℕ) : ℝ) / n) ^ (n - k) ≤ 1) := by
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := by omega
    subst k
    norm_num
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnonneg1 : 0 ≤ (k : ℝ) / n := div_nonneg (by positivity) hnpos.le
  have hnonneg2 : 0 ≤ (((n - k : ℕ) : ℝ) / n) := div_nonneg (by positivity) hnpos.le
  have hsum : (∑ j ∈ range (n+1), (n.choose j : ℝ) * ((k : ℝ) / n) ^ j * (((n-k:ℕ):ℝ)/n) ^ (n-j)) = 1 := by
    have hb := add_pow ((k : ℝ) / n) (((n-k:ℕ):ℝ)/n) n
    -- hb: (x+y)^n = sum range...
    have hx : (k : ℝ) / n + (((n-k:ℕ):ℝ)/n) = 1 := by
      rw [← add_div]
      have hcast : (k : ℝ) + ((n-k:ℕ):ℝ) = n := by
        norm_cast
        omega
      rw [hcast, div_self hnpos.ne']
    calc
      (∑ j ∈ range (n+1), (n.choose j : ℝ) * ((k : ℝ) / n) ^ j * (((n-k:ℕ):ℝ)/n) ^ (n-j))
          = (∑ j ∈ range (n+1), ((k : ℝ) / n) ^ j * ((((n-k:ℕ):ℝ)/n) ^ (n-j)) * (n.choose j : ℝ)) := by
              apply sum_congr rfl
              intro j hj
              ring
      _ = ((k : ℝ) / n + (((n-k:ℕ):ℝ)/n)) ^ n := by rw [add_pow]
      _ = 1 := by rw [hx, one_pow]
  have hterm_mem : k ∈ range (n+1) := by simp [Nat.lt_succ_iff, hk]
  have hterm_le_sum : (n.choose k : ℝ) * ((k : ℝ) / n) ^ k * (((n-k:ℕ):ℝ)/n) ^ (n-k)
      ≤ ∑ j ∈ range (n+1), (n.choose j : ℝ) * ((k : ℝ) / n) ^ j * (((n-k:ℕ):ℝ)/n) ^ (n-j) := by
    simpa using
      (Finset.single_le_sum
        (s := range (n+1))
        (f := fun j => (n.choose j : ℝ) * ((k : ℝ) / n) ^ j * (((n-k:ℕ):ℝ)/n) ^ (n-j))
        (by intro b hb; positivity) hterm_mem)
  simpa [hsum] using hterm_le_sum


lemma log_choose_le_entropy (n k : ℕ) (hk : k ≤ n) :
    Real.log (n.choose k : ℝ) ≤ (n : ℝ) * Real.binEntropy ((k : ℝ) / n) := by
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := by omega
    subst k
    simp
  by_cases hk0 : k = 0
  · subst k
    simp [Real.binEntropy_zero]
  by_cases hkn : k = n
  · subst k
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [div_self hnpos.ne']
    simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hkpos_nat : 0 < k := Nat.pos_of_ne_zero hk0
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hkpos_nat
  have hnkpos_nat : 0 < n - k := Nat.sub_pos_of_lt (lt_of_le_of_ne hk hkn)
  have hnkpos : (0 : ℝ) < ((n-k:ℕ):ℝ) := by exact_mod_cast hnkpos_nat
  have hprobpos : 0 < ((k : ℝ)/n) ^ k * ((((n-k:ℕ):ℝ)/n) ^ (n-k)) := by positivity
  have hprob_le : ((n.choose k : ℝ) * ((k : ℝ) / n) ^ k * (((n-k:ℕ):ℝ) / n) ^ (n-k) ≤ 1) :=
    choose_mul_prob_le_one n k hk
  have hchoosepos : 0 < (n.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos hk
  have hle : (n.choose k : ℝ) ≤ (((k : ℝ) / n) ^ k * (((n-k:ℕ):ℝ) / n) ^ (n-k))⁻¹ := by
    let c := ((k : ℝ) / n) ^ k * (((n-k:ℕ):ℝ) / n) ^ (n-k)
    have hc : 0 < c := by dsimp [c]; positivity
    have hc_le : c * (n.choose k : ℝ) ≤ 1 := by
      dsimp [c]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hprob_le
    have := (le_inv_mul_iff₀ hc).2 hc_le
    simpa [c] using this
  have hlog := Real.log_le_log hchoosepos (hle.trans_eq (by rfl))
  -- Now simplify RHS log inv product to entropy
  rw [Real.log_inv, Real.log_mul (pow_ne_zero _ (div_ne_zero hkpos.ne' hnpos.ne'))
      (pow_ne_zero _ (div_ne_zero hnkpos.ne' hnpos.ne'))] at hlog
  rw [Real.log_pow, Real.log_pow] at hlog
  -- goal follows by algebra expanding `binEntropy`.
  have hp : 1 - (k : ℝ) / n = (((n - k : ℕ) : ℝ) / n) := by
    field_simp [hnpos.ne']
    norm_cast
  have hident :
      (n : ℝ) * Real.binEntropy ((k : ℝ) / n)
        = -((k : ℝ) * Real.log ((k : ℝ) / n) + ((n-k:ℕ):ℝ) * Real.log (((n-k:ℕ):ℝ) / n)) := by
    rw [Real.binEntropy, hp, Real.log_inv, Real.log_inv]
    field_simp [hnpos.ne']
    ring
  rwa [hident]

lemma mod_choose_le_exp_root (n k : ℕ) (hk : k ≤ n) :
    (((n.choose k) % (2 ^ k) : ℕ) : ℝ) ≤ Real.exp ((n : ℝ) * (entropyRoot * Real.log 2)) := by
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := by omega
    subst k
    norm_num
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  let x : ℝ := (k : ℝ) / n
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hnpos).2 (by exact_mod_cast hk)
  by_cases hxr : x ≤ entropyRoot
  · have hmod : (((n.choose k) % (2 ^ k) : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mod_lt _ (pow_pos (by omega : 0 < 2) k)).le
    have hpowpos : 0 < ((2 ^ k : ℕ) : ℝ) := by positivity
    have hlogle : Real.log (((2 ^ k : ℕ) : ℝ)) ≤ (n : ℝ) * (entropyRoot * Real.log 2) := by
      have hcast : (((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k := by norm_num
      rw [hcast, Real.log_pow]
      dsimp [x] at hxr
      have hk_le : (k : ℝ) ≤ (n : ℝ) * entropyRoot := by
        simpa [mul_comm] using (div_le_iff₀ hnpos).mp hxr
      have := mul_le_mul_of_nonneg_right hk_le (Real.log_pos one_lt_two).le
      nlinarith
    have hpowle : ((2 ^ k : ℕ) : ℝ) ≤ Real.exp ((n : ℝ) * (entropyRoot * Real.log 2)) := by
      exact (Real.log_le_iff_le_exp hpowpos).1 hlogle
    exact hmod.trans hpowle
  · have hrx : entropyRoot ≤ x := le_of_not_ge hxr
    have hchoosepos : 0 < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
    have hchoosele : (n.choose k : ℝ) ≤ Real.exp ((n : ℝ) * Real.binEntropy x) := by
      exact (Real.log_le_iff_le_exp hchoosepos).1 (by simpa [x] using log_choose_le_entropy n k hk)
    have hentle : (n : ℝ) * Real.binEntropy x ≤ (n : ℝ) * (entropyRoot * Real.log 2) := by
      have hxhalf : (2⁻¹ : ℝ) ≤ x := half_le_entropyRoot.trans hrx
      have hanti := Real.binEntropy_strictAntiOn.antitoneOn
      have : Real.binEntropy x ≤ Real.binEntropy entropyRoot := hanti entropyRoot_mem ⟨hxhalf, hx1⟩ hrx
      rw [entropyRoot_eq] at this
      exact mul_le_mul_of_nonneg_left this hnpos.le
    have hexp : Real.exp ((n : ℝ) * Real.binEntropy x) ≤ Real.exp ((n : ℝ) * (entropyRoot * Real.log 2)) := Real.exp_le_exp.2 hentle
    have hmod : (((n.choose k) % (2 ^ k) : ℕ) : ℝ) ≤ (n.choose k : ℝ) := by exact_mod_cast Nat.mod_le _ _
    exact hmod.trans (hchoosele.trans hexp)

lemma a_le_mul_exp_root (n : ℕ) :
    (a n : ℝ) ≤ (n : ℝ) * Real.exp ((n : ℝ) * (entropyRoot * Real.log 2)) := by
  unfold a
  rw [Nat.cast_sum]
  have hsum := Finset.sum_le_sum (s := Finset.Icc 1 n) (f := fun k => (((n.choose k) % (2 ^ k : ℕ) : ℕ) : ℝ))
    (g := fun _ => Real.exp ((n : ℝ) * (entropyRoot * Real.log 2))) ?_
  · simpa [Nat.card_Icc] using hsum.trans_eq (by simp [mul_comm])
  · intro k hk
    have hk' : k ≤ n := (Finset.mem_Icc.mp hk).2
    exact mod_choose_le_exp_root n k hk'

noncomputable def probTerm (n k j : ℕ) : ℝ :=
  (n.choose j : ℝ) * ((k : ℝ) / n) ^ j * (((n-k:ℕ):ℝ) / n) ^ (n-j)

lemma probTerm_succ_mul (n k j : ℕ) (hj : j < n) :
    probTerm n k (j+1) * (((j+1 : ℕ) : ℝ) * (((n-k:ℕ):ℝ) / n))
      = probTerm n k j * ((((n-j:ℕ):ℝ) * ((k : ℝ) / n))) := by
  unfold probTerm
  have hchoose := Nat.choose_succ_right_eq n j
  have hchooseR : (n.choose (j+1) : ℝ) * (j+1 : ℝ) = (n.choose j : ℝ) * (n-j : ℕ) := by
    exact_mod_cast hchoose
  by_cases hn : n = 0
  · omega
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hnj : n - (j+1) + 1 = n - j := by omega
  have hpowq : (((n-k:ℕ):ℝ) / n) ^ (n - (j+1)) * (((n-k:ℕ):ℝ) / n)
      = (((n-k:ℕ):ℝ) / n) ^ (n-j) := by
    rw [← pow_succ, show n - (j+1) + 1 = n-j by omega]
  have hp : ((k : ℝ) / n) ^ (j+1) = ((k : ℝ) / n) ^ j * ((k : ℝ) / n) := by rw [pow_succ]
  have hcastsucc : (((j+1:ℕ):ℝ)) = (j:ℝ) + 1 := by norm_num

  calc
    (n.choose (j + 1) : ℝ) * ((k : ℝ) / n) ^ (j + 1) * (((n - k : ℕ) : ℝ) / n) ^ (n - (j + 1)) * (((j + 1 : ℕ) : ℝ) * (((n - k : ℕ) : ℝ) / n))
        = ((n.choose (j+1) : ℝ) * ((j+1:ℕ) : ℝ)) * ((k : ℝ) / n) ^ (j+1) * ((((n-k:ℕ):ℝ)/n) ^ (n-(j+1)) * (((n-k:ℕ):ℝ)/n)) := by ring
    _ = ((n.choose j : ℝ) * ((n-j:ℕ):ℝ)) * (((k : ℝ) / n) ^ j * ((k : ℝ)/n)) * ((((n-k:ℕ):ℝ)/n) ^ (n-j)) := by rw [hcastsucc, hchooseR, hp, hpowq]
    _ = (n.choose j : ℝ) * ((k : ℝ) / n) ^ j * (((n - k : ℕ) : ℝ) / n) ^ (n - j) * (((n-j:ℕ):ℝ) * ((k : ℝ) / n)) := by ring


lemma probTerm_nonneg (n k j : ℕ) : 0 ≤ probTerm n k j := by
  unfold probTerm
  positivity

lemma probTerm_mono_up (n k j : ℕ) (hk : k < n) (hj : j < k) :
    probTerm n k j ≤ probTerm n k (j+1) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt (hj.trans hk))
  let c : ℝ := ((j+1:ℕ):ℝ) * (((n-k:ℕ):ℝ) / n)
  let d : ℝ := (((n-j:ℕ):ℝ) * ((k:ℝ) / n))
  have hcpos : 0 < c := by
    dsimp [c]
    have : 0 < (n-k:ℕ) := Nat.sub_pos_of_lt hk
    positivity
  have hlecd : c ≤ d := by
    dsimp [c, d]
    have hjle : ((j+1:ℕ):ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hj
    have hkn : (k:ℝ) ≤ n := by exact_mod_cast hk.le
    have hnonneg : 0 ≤ (n:ℝ) * ((k:ℝ) - ((j+1:ℕ):ℝ)) := mul_nonneg hnpos.le (sub_nonneg.mpr hjle)
    have hidentity : (((n-j:ℕ):ℝ) * ((k:ℝ) / n)) - (((j+1:ℕ):ℝ) * (((n-k:ℕ):ℝ) / n))
        = ((n:ℝ) * ((k:ℝ) - ((j+1:ℕ):ℝ)) + (k:ℝ)) / (n:ℝ) := by
      have hnj : ((n-j:ℕ):ℝ) = (n:ℝ) - j := by
        rw [Nat.cast_sub (le_of_lt (hj.trans hk))]
      have hnk : ((n-k:ℕ):ℝ) = (n:ℝ) - k := by
        rw [Nat.cast_sub hk.le]
      have hjs : (((j+1:ℕ):ℝ)) = (j:ℝ) + 1 := by norm_num
      rw [hnj, hnk, hjs]
      field_simp [hnpos.ne']
      ring
    rw [← sub_nonneg]
    rw [hidentity]
    positivity
  have hTnonneg := probTerm_nonneg n k j
  have hmul : probTerm n k j * c ≤ probTerm n k j * d := mul_le_mul_of_nonneg_left hlecd hTnonneg
  have heq : probTerm n k (j+1) * c = probTerm n k j * d := by
    dsimp [c, d]
    exact probTerm_succ_mul n k j (hj.trans hk)
  have hmul' : probTerm n k j * c ≤ probTerm n k (j+1) * c := by simpa [heq]
    using hmul
  exact (mul_le_mul_iff_left₀ hcpos).mp hmul'


lemma probTerm_mono_down (n k j : ℕ) (hk : k < n) (hkj : k ≤ j) (hj : j < n) :
    probTerm n k (j+1) ≤ probTerm n k j := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  let c : ℝ := ((j+1:ℕ):ℝ) * (((n-k:ℕ):ℝ) / n)
  let d : ℝ := (((n-j:ℕ):ℝ) * ((k:ℝ) / n))
  have hcpos : 0 < c := by
    dsimp [c]
    have : 0 < (n-k:ℕ) := Nat.sub_pos_of_lt hk
    positivity
  have hdlec : d ≤ c := by
    dsimp [c, d]
    have hkjR : (k:ℝ) ≤ (j:ℝ) := by exact_mod_cast hkj
    have hidentity : (((j+1:ℕ):ℝ) * (((n-k:ℕ):ℝ) / n)) - (((n-j:ℕ):ℝ) * ((k:ℝ) / n))
        = ((n:ℝ) * (((j+1:ℕ):ℝ) - (k:ℝ)) - (k:ℝ)) / (n:ℝ) := by
      have hnj : ((n-j:ℕ):ℝ) = (n:ℝ) - j := by rw [Nat.cast_sub hj.le]
      have hnk : ((n-k:ℕ):ℝ) = (n:ℝ) - k := by rw [Nat.cast_sub hk.le]
      have hjs : (((j+1:ℕ):ℝ)) = (j:ℝ) + 1 := by norm_num
      rw [hnj, hnk, hjs]
      field_simp [hnpos.ne']
      ring
    rw [← sub_nonneg]
    rw [hidentity]
    have hmain : 0 ≤ (n:ℝ) * (((j+1:ℕ):ℝ) - (k:ℝ)) - (k:ℝ) := by
      have hgap : 1 ≤ (((j+1:ℕ):ℝ) - (k:ℝ)) := by
        have hsub : (((j+1:ℕ):ℝ) - (k:ℝ)) = ((j+1-k:ℕ):ℝ) := by
          rw [Nat.cast_sub (by omega : k ≤ j+1)]
        rw [hsub]
        exact_mod_cast (by omega : 1 ≤ (j + 1 - k : ℕ))
      have hn_ge_k : (k:ℝ) ≤ n := by exact_mod_cast hk.le
      nlinarith [mul_le_mul_of_nonneg_left hgap hnpos.le]
    positivity
  have hTnonneg := probTerm_nonneg n k j
  have hmul : probTerm n k j * d ≤ probTerm n k j * c := mul_le_mul_of_nonneg_left hdlec hTnonneg
  have heq : probTerm n k (j+1) * c = probTerm n k j * d := by
    dsimp [c, d]
    exact probTerm_succ_mul n k j hj
  have hmul' : probTerm n k (j+1) * c ≤ probTerm n k j * c := by simpa [heq] using hmul

  exact (mul_le_mul_iff_left₀ hcpos).mp hmul'

lemma probTerm_le_mode_left (n k j : ℕ) (hk : k < n) (hj : j ≤ k) :
    probTerm n k j ≤ probTerm n k k := by
  let P : (m : ℕ) → j ≤ m → Prop := fun m _ => m ≤ k → probTerm n k j ≤ probTerm n k m
  have hP : P k hj := Nat.le_induction (m := j) (P := P)
    (by intro _; rfl)
    (by
      intro m hjm ih hm1k
      have hmk : m < k := Nat.lt_of_succ_le hm1k
      exact (ih hmk.le).trans (probTerm_mono_up n k m hk hmk))
    k hj
  exact hP le_rfl

lemma probTerm_le_mode_right (n k j : ℕ) (hk : k < n) (hkj : k ≤ j) (hj : j < n) :
    probTerm n k j ≤ probTerm n k k := by
  let P : (m : ℕ) → k ≤ m → Prop := fun m _ => m < n → probTerm n k m ≤ probTerm n k k
  have hP : P j hkj := Nat.le_induction (m := k) (P := P)
    (by intro _; rfl)
    (by
      intro m hkm ih hm1n
      have hm_n : m < n := lt_of_succ_lt hm1n
      exact (probTerm_mono_down n k m hk hkm hm_n).trans (ih hm_n))
    j hkj
  exact hP hj

lemma probTerm_le_mode (n k j : ℕ) (hk : k < n) (hj : j ≤ n) :
    probTerm n k j ≤ probTerm n k k := by
  by_cases hle : j ≤ k
  · exact probTerm_le_mode_left n k j hk hle
  · have hkj : k ≤ j := le_of_not_ge hle
    by_cases hjeq : j = n
    · subst j
      have hnpos : 0 < n := Nat.zero_lt_of_lt hk
      have hpred_lt : n - 1 < n := Nat.sub_one_lt hnpos.ne'
      have hknpred : k ≤ n - 1 := Nat.le_pred_of_lt hk
      have hchain := (probTerm_mono_down n k (n-1) hk hknpred hpred_lt).trans
        (probTerm_le_mode_right n k (n-1) hk hknpred hpred_lt)
      simpa [Nat.sub_one_add_one hnpos.ne'] using hchain
    · exact probTerm_le_mode_right n k j hk hkj (lt_of_le_of_ne hj hjeq)


lemma sum_probTerm (n k : ℕ) (hk : k ≤ n) :
    (∑ j ∈ Finset.range (n+1), probTerm n k j) = 1 := by
  unfold probTerm
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := by omega
    subst k
    norm_num
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hb := add_pow ((k : ℝ) / n) (((n-k:ℕ):ℝ)/n) n
  have hx : (k : ℝ) / n + (((n-k:ℕ):ℝ)/n) = 1 := by
    rw [← add_div]
    have hcast : (k : ℝ) + ((n-k:ℕ):ℝ) = n := by
      norm_cast
      omega
    rw [hcast, div_self hnpos.ne']
  calc
    (∑ j ∈ range (n+1), (n.choose j : ℝ) * ((k : ℝ) / n) ^ j * (((n-k:ℕ):ℝ)/n) ^ (n-j))
        = (∑ j ∈ range (n+1), ((k : ℝ) / n) ^ j * ((((n-k:ℕ):ℝ)/n) ^ (n-j)) * (n.choose j : ℝ)) := by
            apply sum_congr rfl
            intro j hj
            ring
    _ = ((k : ℝ) / n + (((n-k:ℕ):ℝ)/n)) ^ n := by rw [add_pow]
    _ = 1 := by rw [hx, one_pow]

lemma one_le_card_mul_probTerm_mode (n k : ℕ) (hk : k < n) :
    1 ≤ ((n+1:ℕ):ℝ) * probTerm n k k := by
  have hsum : (∑ j ∈ Finset.range (n+1), probTerm n k j) = 1 := sum_probTerm n k hk.le
  have hle : (∑ j ∈ Finset.range (n+1), probTerm n k j) ≤ ∑ j ∈ Finset.range (n+1), probTerm n k k := by
    apply Finset.sum_le_sum
    intro j hj
    exact probTerm_le_mode n k j hk (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  have hconst : (∑ j ∈ Finset.range (n+1), probTerm n k k) = ((n+1:ℕ):ℝ) * probTerm n k k := by
    simp [mul_comm]
  linarith


lemma entropy_sub_log_card_le_log_choose (n k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    (n : ℝ) * Real.binEntropy ((k : ℝ) / n) - Real.log ((n+1:ℕ) : ℝ)
      ≤ Real.log (n.choose k : ℝ) := by
  have hone := one_le_card_mul_probTerm_mode n k hkn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hkn)
  have hcardpos : 0 < (((n+1:ℕ):ℝ)) := by positivity
  have hchoosepos : 0 < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hkn.le
  have hppos : 0 < (k:ℝ) / n := div_pos (by exact_mod_cast hk0) hnpos
  have hqpos : 0 < (((n-k:ℕ):ℝ) / n) := by
    have : 0 < (n-k:ℕ) := Nat.sub_pos_of_lt hkn
    positivity
  have hprodpos : 0 < ((k:ℝ)/n)^k * ((((n-k:ℕ):ℝ)/n)^(n-k)) := by positivity
  have hargpos : 0 < (((n+1:ℕ):ℝ) * probTerm n k k) := by
    unfold probTerm
    positivity
  have hlog_nonneg : 0 ≤ Real.log (((n+1:ℕ):ℝ) * probTerm n k k) := by
    rw [← Real.log_one]
    exact Real.log_le_log zero_lt_one hone
  unfold probTerm at hlog_nonneg
  rw [Real.log_mul hcardpos.ne' (by positivity : ((n.choose k : ℝ) * ((k:ℝ)/n)^k * (((n-k:ℕ):ℝ)/n)^(n-k)) ≠ 0)] at hlog_nonneg
  rw [Real.log_mul (mul_ne_zero hchoosepos.ne' (pow_ne_zero _ hppos.ne')) (pow_ne_zero _ hqpos.ne')] at hlog_nonneg
  rw [Real.log_mul hchoosepos.ne' (pow_ne_zero _ hppos.ne')] at hlog_nonneg
  rw [Real.log_pow, Real.log_pow] at hlog_nonneg
  have hp : 1 - (k : ℝ) / n = (((n - k : ℕ) : ℝ) / n) := by
    field_simp [hnpos.ne']
    rw [Nat.cast_sub hkn.le]
  have hident :
      (n : ℝ) * Real.binEntropy ((k : ℝ) / n)
        = -((k : ℝ) * Real.log ((k : ℝ) / n) + ((n-k:ℕ):ℝ) * Real.log (((n-k:ℕ):ℝ) / n)) := by
    rw [Real.binEntropy, hp, Real.log_inv, Real.log_inv]
    field_simp [hnpos.ne']
    ring
  linarith

lemma eventually_lower_log_of_right {b y : ℝ} (hyr : entropyRoot < y) (hy1 : y < 1)
    (hb : b < Real.binEntropy y) :
    ∀ᶠ n : ℕ in Filter.atTop, b < Real.log (a n : ℝ) / (n : ℝ) := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2⁻¹) (half_le_entropyRoot.trans_lt hyr).le
  let kfun : ℕ → ℕ := fun n => ⌊y * (n:ℝ)⌋₊
  let xfun : ℕ → ℝ := fun n => (kfun n : ℝ) / (n : ℝ)
  have hx_tend : Tendsto xfun atTop (nhds y) := by
    simpa [xfun, kfun, Function.comp_def, mul_comm] using
      (tendsto_nat_floor_mul_div_atTop (R := ℝ) hy0.le).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hent_tend : Tendsto (fun n => Real.binEntropy (xfun n)) atTop (nhds (Real.binEntropy y)) :=
    Real.binEntropy_continuous.tendsto y |>.comp hx_tend
  have hg_tend : Tendsto (fun n => g (xfun n)) atTop (nhds (g y)) := by
    have hgcont : Continuous g := by unfold g; fun_prop
    exact hgcont.tendsto y |>.comp hx_tend
  have hyhalf : (2⁻¹ : ℝ) ≤ y := half_le_entropyRoot.trans hyr.le
  have hent_lt_root : Real.binEntropy y < Real.binEntropy entropyRoot :=
    Real.binEntropy_strictAntiOn entropyRoot_mem ⟨hyhalf, hy1.le⟩ hyr
  have hgy_neg : g y < 0 := by
    unfold g
    rw [entropyRoot_eq] at hent_lt_root
    nlinarith [Real.log_pos one_lt_two]
  have ev_kpos : ∀ᶠ n : ℕ in atTop, 0 < kfun n := by
    have ht := tendsto_nat_floor_mul_atTop (α := ℝ) y hy0
    exact (tendsto_atTop.1 ht 1)
  have ev_npos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_atTop.2 ⟨1, by intro n hn; omega⟩
  have ev_klt : ∀ᶠ n : ℕ in atTop, kfun n < n := by
    have evx : ∀ᶠ n : ℕ in atTop, xfun n < 1 := (tendsto_order.1 hx_tend).2 1 hy1
    filter_upwards [evx, ev_npos] with n hx hn
    dsimp [xfun] at hx
    by_contra hnot
    have hge : (n:ℝ) ≤ (kfun n : ℝ) := by exact_mod_cast (le_of_not_gt hnot)
    have : (1:ℝ) ≤ (kfun n : ℝ) / n := by
      exact (le_div_iff₀ (by exact_mod_cast hn : (0:ℝ)<n)).2 (by simpa using hge)
    linarith
  have ev_ent_gt : ∀ᶠ n : ℕ in atTop, b < Real.binEntropy (xfun n) :=
    (tendsto_order.1 hent_tend).1 b hb
  have ev_gneg : ∀ᶠ n : ℕ in atTop, g (xfun n) < 0 :=
    (tendsto_order.1 hg_tend).2 0 hgy_neg
  have hlogsmall : Tendsto (fun n : ℕ => Real.log ((n+1:ℕ):ℝ) / (n:ℝ)) atTop (nhds 0) := by
    have hbase : Tendsto (fun m : ℕ => Real.log (m : ℝ) / (m : ℝ)) atTop (nhds 0) := by
      simpa [Function.comp_def] using (Real.isLittleO_log_id_atTop.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero
    have h1 : Tendsto (fun n : ℕ => Real.log ((n+1:ℕ):ℝ) / ((n+1:ℕ):ℝ)) atTop (nhds 0) := hbase.comp (tendsto_add_atTop_nat 1)
    have hratio : Tendsto (fun n : ℕ => (((n+1:ℕ):ℝ) / (n:ℝ))) atTop (nhds 1) := by
      have hratio' : Tendsto (fun n : ℕ => (1:ℝ) + (n:ℝ)⁻¹) atTop (nhds 1) := by
        simpa using (tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
      refine hratio'.congr' ?_
      filter_upwards [eventually_atTop.2 ⟨1, by intro n hn; exact (by exact_mod_cast (by omega : n ≠ 0) : (n:ℝ) ≠ 0)⟩] with n hn0
      field_simp [Nat.cast_add, hn0]
      norm_num [Nat.cast_add]
    have hprod : Tendsto (fun n : ℕ => Real.log ((n+1:ℕ):ℝ) / (n:ℝ)) atTop (nhds (0 * 1)) := (h1.mul hratio).congr' ?_
    · simpa using hprod
    filter_upwards [eventually_atTop.2 ⟨1, by intro n hn; exact (by exact_mod_cast (by omega : n ≠ 0) : (n:ℝ) ≠ 0)⟩] with n hn0
    field_simp [Nat.cast_add, hn0]
    try ring
  have ev_logsmall : ∀ᶠ n : ℕ in atTop, Real.log ((n+1:ℕ):ℝ) / (n:ℝ) < Real.binEntropy (xfun n) - b := by
    have hdiff : Tendsto (fun n : ℕ => Real.binEntropy (xfun n) - b - Real.log ((n+1:ℕ):ℝ) / (n:ℝ)) atTop
        (nhds (Real.binEntropy y - b - 0)) := (hent_tend.sub_const b).sub hlogsmall
    have hpos : 0 < Real.binEntropy y - b - 0 := by linarith
    have hev := (tendsto_order.1 hdiff).1 0 hpos
    filter_upwards [hev] with n hn
    linarith
  filter_upwards [ev_kpos, ev_klt, ev_ent_gt, ev_gneg, ev_logsmall, ev_npos] with n hkpos hklt hentgt hgneg hsmall hnpos
  have hk_le_n : kfun n ≤ n := hklt.le
  have hchoose_lt_pow : n.choose (kfun n) < 2 ^ (kfun n) := by
    have hlog_choose := log_choose_le_entropy n (kfun n) hk_le_n
    have hgineq : Real.binEntropy (xfun n) < xfun n * Real.log 2 := by
      dsimp [g] at hgneg
      linarith
    have hlog_lt : Real.log (n.choose (kfun n) : ℝ) < Real.log ((2 ^ kfun n : ℕ) : ℝ) := by
      have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
      have h1 : (n:ℝ) * Real.binEntropy (xfun n) < (kfun n : ℝ) * Real.log 2 := by
        dsimp [xfun] at hgineq
        have := mul_lt_mul_of_pos_left hgineq hnR
        field_simp [hnR.ne'] at this
        simpa [mul_assoc, mul_comm, mul_left_comm] using this
      have h2 : Real.log ((2 ^ kfun n : ℕ) : ℝ) = (kfun n : ℝ) * Real.log 2 := by
        have hcast : (((2 ^ kfun n : ℕ) : ℝ)) = (2:ℝ) ^ kfun n := by norm_num
        rw [hcast, Real.log_pow]
      linarith
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast Nat.choose_pos hk_le_n) (by positivity : (0:ℝ) < (2 ^ kfun n : ℕ))).1 hlog_lt
  have hmodeq : (n.choose (kfun n)) % (2 ^ kfun n) = n.choose (kfun n) := Nat.mod_eq_of_lt hchoose_lt_pow
  have hk_mem : kfun n ∈ Finset.Icc 1 n := by
    simp [Finset.mem_Icc]
    exact ⟨Nat.succ_le_iff.mpr hkpos, hk_le_n⟩
  have ha_ge_choose_nat : n.choose (kfun n) ≤ a n := by
    unfold a
    calc
      n.choose (kfun n) = (n.choose (kfun n)) % (2 ^ kfun n) := hmodeq.symm
      _ ≤ (Finset.Icc 1 n).sum (fun k => (n.choose k) % (2 ^ k)) := by
        simpa using (Finset.single_le_sum (s := Finset.Icc 1 n)
          (f := fun k => (n.choose k) % (2 ^ k)) (by intro i hi; exact Nat.zero_le _) hk_mem)
  have hlog_choose_lower := entropy_sub_log_card_le_log_choose n (kfun n) hkpos hklt
  have hlog_a_lower : (n:ℝ) * Real.binEntropy (xfun n) - Real.log ((n+1:ℕ):ℝ) ≤ Real.log (a n : ℝ) := by
    exact hlog_choose_lower.trans (Real.log_le_log (by exact_mod_cast Nat.choose_pos hk_le_n) (by exact_mod_cast ha_ge_choose_nat))
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have : Real.binEntropy (xfun n) - Real.log ((n+1:ℕ):ℝ) / (n:ℝ) ≤ Real.log (a n : ℝ) / (n:ℝ) := by
    rw [le_div_iff₀ hnR]
    field_simp [hnR.ne']
    linarith
  have hb2 : b < Real.binEntropy (xfun n) - Real.log ((n+1:ℕ):ℝ) / (n:ℝ) := by
    linarith
  exact hb2.trans_le this





lemma tendsto_log_a_div :
    Tendsto (fun n : ℕ => Real.log (a n : ℝ) / (n : ℝ)) atTop
      (nhds (entropyRoot * Real.log 2)) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    rcases exists_right_entropy_gt hb with ⟨y, hyr, hy1, hby⟩
    exact eventually_lower_log_of_right hyr hy1 hby
  · intro b hb
    have hlogn : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
      simpa [Function.comp_def] using (Real.isLittleO_log_id_atTop.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero
    have hupper_tend : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) + entropyRoot * Real.log 2) atTop
        (nhds (0 + entropyRoot * Real.log 2)) := hlogn.add_const _
    have ev_upper_small : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) / (n : ℝ) + entropyRoot * Real.log 2 < b := by
      simpa using (tendsto_order.1 hupper_tend).2 b (by simpa using hb)
    have ev_npos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_atTop.2 ⟨1, by intro n hn; omega⟩
    filter_upwards [ev_upper_small, ev_npos] with n hup hnpos
    have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
    have hapos : 0 < (a n : ℝ) := by exact_mod_cast a_pos hnpos
    have hbound := a_le_mul_exp_root n
    have hRpos : 0 < (n : ℝ) * Real.exp ((n : ℝ) * (entropyRoot * Real.log 2)) := by positivity
    have hlog_le : Real.log (a n : ℝ) ≤ Real.log ((n : ℝ) * Real.exp ((n : ℝ) * (entropyRoot * Real.log 2))) :=
      Real.log_le_log hapos hbound
    have hsimp : Real.log ((n : ℝ) * Real.exp ((n : ℝ) * (entropyRoot * Real.log 2))) = Real.log (n : ℝ) + (n : ℝ) * (entropyRoot * Real.log 2) := by
      rw [Real.log_mul hnR.ne' (Real.exp_ne_zero _), Real.log_exp]
    have hdiv : Real.log (a n : ℝ) / (n : ℝ) ≤ Real.log (n : ℝ) / (n : ℝ) + entropyRoot * Real.log 2 := by
      rw [hsimp] at hlog_le
      have hdivle := div_le_div_of_nonneg_right hlog_le hnR.le
      field_simp [hnR.ne'] at hdivle ⊢
      linarith
    exact hdiv.trans_lt hup


lemma tendsto_root_a :
    Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (n : ℝ))) atTop
      (nhds (Real.exp (entropyRoot * Real.log 2))) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (Real.log (a n : ℝ) / (n : ℝ))) atTop
      (nhds (Real.exp (entropyRoot * Real.log 2))) :=
    Real.continuous_exp.tendsto _ |>.comp tendsto_log_a_div
  refine hexp.congr' ?_
  filter_upwards [eventually_atTop.2 ⟨1, by intro n hn; omega⟩] with n hnpos
  have hapos : 0 < (a n : ℝ) := by exact_mod_cast a_pos hnpos
  rw [Real.rpow_def_of_pos hapos]
  congr 1
  ring






end Proof


-- Conjecture based on OEIS A386660, comment C.
/--
oeis_386660_conjecture_0: The limit of $a(n)^{1/n}$ exists.
The numerical evidence suggests a limit of approximately $1.7086...$
-/
theorem oeis_386660_conjecture_0 :
  let f (n : ℕ) : ℝ := (a n : ℝ) ^ (1 / (n : ℝ))
  ∃ L : ℝ, Filter.Tendsto f Filter.atTop (nhds L) := by
  exact ⟨Real.exp (Proof.entropyRoot * Real.log 2), Proof.tendsto_root_a⟩
