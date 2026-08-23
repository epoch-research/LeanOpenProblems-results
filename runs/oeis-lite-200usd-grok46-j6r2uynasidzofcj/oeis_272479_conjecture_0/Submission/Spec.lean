import FormalConjectures.Util.ProblemImports
open Nat
open Classical
open Finset

/--
A272479: $a(n)$ is the smallest $k$ different from $n$ such that $(n, k)$ is a Harshad amicable pair.
Let $D(n)$ be the sum of digits of $n$.
$m$ and $k$ are Harshad amicable if they are distinct integers such that $D(m) \mid k$ and $D(k) \mid m$.
For any $n$ with no Harshad amicable partner, $a(n)=0$ (Conjecture: the sequence contains no zeros.)
-/
noncomputable def a (n : ℕ) : ℕ :=
  let dsum (m : ℕ) : ℕ := (digits 10 m).sum

  let partners : Set ℕ := {k | k > 0 ∧ k ≠ n ∧ dsum n ∣ k ∧ dsum k ∣ n}

  -- The set of partners is bounded below by 1. If it is non-empty, `sInf`
  -- correctly returns the smallest element. If empty, we return 0 as per the OEIS comment.
  if h : partners.Nonempty then
    sInf partners
  else
    0

/- Digit-sum helpers -/

lemma digitSum_pos {n : ℕ} (hn : 0 < n) : 0 < (digits 10 n).sum := by
  have hne : digits 10 n ≠ [] := digits_ne_nil_iff_ne_zero.mpr hn.ne'
  have hlast : (digits 10 n).getLast hne ≠ 0 := getLast_digit_ne_zero 10 hn.ne'
  have hmem : (digits 10 n).getLast hne ∈ digits 10 n := List.getLast_mem hne
  have hle : (digits 10 n).getLast hne ≤ (digits 10 n).sum := List.le_sum_of_mem hmem
  omega

lemma digitSum_lt_of_ge_ten {n : ℕ} (hn : 10 ≤ n) : (digits 10 n).sum < n := by
  have hb : 1 < 10 := by decide
  have hn0 : 0 < n := by omega
  rw [digits_def' hb hn0]
  have hsum : (digits 10 (n / 10)).sum ≤ n / 10 := digit_sum_le 10 (n / 10)
  simp only [List.sum_cons]
  have : 0 < n / 10 := Nat.div_pos hn (by decide)
  omega

lemma digitSum_eq_of_lt_ten {n : ℕ} (hn : n < 10) : (digits 10 n).sum = n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [digits_of_lt 10 n.succ (Nat.succ_ne_zero n) hn, List.sum_singleton]

lemma gcd_digitSum_nine_dvd (n : ℕ) : Nat.gcd (digits 10 n).sum 9 ∣ n := by
  have hmod : n % 9 = (digits 10 n).sum % 9 := modEq_nine_digits_sum n
  have hg_sum : Nat.gcd (digits 10 n).sum 9 ∣ (digits 10 n).sum := Nat.gcd_dvd_left _ _
  have hg9 : Nat.gcd (digits 10 n).sum 9 ∣ 9 := Nat.gcd_dvd_right _ _
  have h1 : n % Nat.gcd (digits 10 n).sum 9 =
      (n % 9) % Nat.gcd (digits 10 n).sum 9 := (Nat.mod_mod_of_dvd n hg9).symm
  have h2 : (digits 10 n).sum % Nat.gcd (digits 10 n).sum 9 = 0 :=
    Nat.mod_eq_zero_of_dvd hg_sum
  have h3 : ((digits 10 n).sum % 9) % Nat.gcd (digits 10 n).sum 9 =
      (digits 10 n).sum % Nat.gcd (digits 10 n).sum 9 := Nat.mod_mod_of_dvd _ hg9
  rw [Nat.dvd_iff_mod_eq_zero, h1, hmod, h3, h2]

/- Digit lists -/

lemma ofDigits_map_range (d : ℕ → ℕ) (N : ℕ) :
    ofDigits 10 ((List.range N).map d) = ∑ i ∈ Finset.range N, d i * 10 ^ i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, ofDigits_append,
      List.length_map, List.length_range, ofDigits_singleton, ih, Finset.sum_range_succ]
    ring

lemma sum_map_range (d : ℕ → ℕ) (N : ℕ) :
    ((List.range N).map d).sum = ∑ i ∈ Finset.range N, d i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
      List.sum_singleton, ih, Finset.sum_range_succ]

lemma digits_sum_ofDigits_of_lt {L : List ℕ} (hL : ∀ x ∈ L, x < 10) :
    (digits 10 (ofDigits 10 L)).sum = L.sum := by
  simpa using
    (sum_digits_ofDigits_eq_sum (b := 10) (by decide) (l := L.length) (L := L) ⟨rfl, hL⟩)

def ninesAndRest (t : ℕ) : List ℕ :=
  List.replicate (t / 9) 9 ++ if t % 9 = 0 then [] else [t % 9]

lemma ninesAndRest_sum (t : ℕ) : (ninesAndRest t).sum = t := by
  unfold ninesAndRest
  rw [List.sum_append]
  by_cases h : t % 9 = 0
  · simp [h, List.sum_replicate]
    rw [Nat.mul_comm]
    exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h)
  · simp [h, List.sum_replicate]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod t 9

lemma ninesAndRest_lt_ten (t : ℕ) {x : ℕ} (hx : x ∈ ninesAndRest t) : x < 10 := by
  unfold ninesAndRest at hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · rcases List.mem_replicate.mp hx with ⟨_, rfl⟩
    omega
  · by_cases h : t % 9 = 0
    · simp [h] at hx
    · simp [h] at hx
      omega

lemma getD_cons_succ (hd : ℕ) (tl : List ℕ) (j d : ℕ) :
    (hd :: tl).getD (j + 1) d = tl.getD j d := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_cons_zero (hd : ℕ) (tl : List ℕ) (d : ℕ) :
    (hd :: tl).getD 0 d = hd := by
  simp [List.getD_eq_getElem?_getD]

lemma sum_getD_length (L : List ℕ) :
    ∑ j ∈ Finset.range L.length, L.getD j 0 = L.sum := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons, getD_cons_zero]
    simp_rw [getD_cons_succ]
    rw [add_comm]
    exact congrArg (hd + ·) ih

lemma sum_getD_le (L : List ℕ) (M : ℕ) (hM : L.length ≤ M) :
    ∑ j ∈ Finset.range M, L.getD j 0 = L.sum := by
  have hsplit := Finset.sum_range_add (fun j => L.getD j 0) L.length (M - L.length)
  have : L.length + (M - L.length) = M := Nat.add_sub_of_le hM
  rw [this] at hsplit
  rw [hsplit, sum_getD_length]
  have htail : ∑ x ∈ Finset.range (M - L.length), L.getD (L.length + x) 0 = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x _
    exact List.getD_eq_default L 0 (by omega)
  rw [htail, add_zero]

lemma ninesAndRest_getD_lt_ten (t j : ℕ) : (ninesAndRest t).getD j 0 < 10 := by
  by_cases hj : j < (ninesAndRest t).length
  · rw [List.getD_eq_getElem (ninesAndRest t) 0 hj]
    exact ninesAndRest_lt_ten t (List.getElem_mem hj)
  · rw [List.getD_eq_default (ninesAndRest t) 0 (le_of_not_gt hj)]
    omega

lemma ofDigits_one_replicate_one (s : ℕ) :
    ofDigits (1 : ℕ) (List.replicate s 1) = s := by
  induction s with
  | zero => simp [ofDigits]
  | succ s ih =>
    simp [List.replicate_succ, ofDigits_cons, ih]
    omega

/- Linear congruence 9y + s ≡ 0 [MOD m] -/

lemma exists_nine_mul_add_eq_zero_mod {s m : ℕ} (hm : 0 < m)
    (hg : Nat.gcd 9 m ∣ s) :
    ∃ y, y < m ∧ 9 * y + s ≡ 0 [MOD m] := by
  by_cases hdiv : m ∣ 9
  · have hg_eq : Nat.gcd 9 m = m := Nat.gcd_eq_right_iff_dvd.mpr hdiv
    have hms : m ∣ s := by rwa [hg_eq] at hg
    refine ⟨0, hm, ?_⟩
    simp [Nat.ModEq, Nat.mod_eq_zero_of_dvd hms]
  · have hlt : Nat.gcd 9 m < m :=
      lt_of_le_of_ne (Nat.le_of_dvd hm (Nat.gcd_dvd_right 9 m))
        (fun heq => hdiv (Nat.gcd_eq_right_iff_dvd.mp heq))
    obtain ⟨t, _ht, htmod⟩ := exists_mul_mod_eq_gcd (n := 9) (k := m) hlt
    have hgt : 9 * t ≡ Nat.gcd 9 m [MOD m] := by
      rw [Nat.ModEq, htmod, Nat.mod_eq_of_lt hlt]
    have hprod : 9 * (t * (s / Nat.gcd 9 m)) ≡ s [MOD m] := by
      have : 9 * t * (s / Nat.gcd 9 m) ≡ Nat.gcd 9 m * (s / Nat.gcd 9 m) [MOD m] :=
        Nat.ModEq.mul_right _ hgt
      rw [Nat.mul_assoc] at this
      have hgs : Nat.gcd 9 m * (s / Nat.gcd 9 m) = s := Nat.mul_div_cancel' hg
      rwa [hgs] at this
    let z := (t * (s / Nat.gcd 9 m)) % m
    have hzlt : z < m := Nat.mod_lt _ hm
    have hz : 9 * z ≡ s [MOD m] := by
      have : z ≡ t * (s / Nat.gcd 9 m) [MOD m] := Nat.mod_modEq _ _
      exact (Nat.ModEq.mul_left 9 this).trans hprod
    refine ⟨(m - z) % m, Nat.mod_lt _ hm, ?_⟩
    by_cases hz0 : z = 0
    · have hz0' : z = 0 := hz0
      simp only [hz0', Nat.sub_zero, Nat.mod_self]
      have : 9 * 0 ≡ s [MOD m] := by
        convert hz
        exact hz0'.symm
      have hms : m ∣ s := (Nat.modEq_zero_iff_dvd).mp (by
        simpa [Nat.ModEq] using this.symm)
      simp [Nat.ModEq, Nat.mod_eq_zero_of_dvd hms]
    · have hsub : m - z < m := Nat.sub_lt hm (Nat.pos_of_ne_zero hz0)
      rw [Nat.mod_eq_of_lt hsub]
      have hmulsub : 9 * (m - z) = 9 * m - 9 * z := Nat.mul_sub 9 m z
      have hadd : 9 * (m - z) + s + 9 * z = 9 * m + s := by
        rw [hmulsub]
        have : 9 * z ≤ 9 * m := Nat.mul_le_mul_left 9 (le_of_lt hzlt)
        omega
      have hleft : 9 * (m - z) + s + 9 * z ≡ 9 * z [MOD m] := by
        rw [hadd]
        have : 9 * m + s ≡ s [MOD m] := by
          simp [Nat.ModEq, Nat.add_mod, Nat.mul_mod]
        exact this.trans hz.symm
      have hleft' : 9 * (m - z) + s + 9 * z ≡ 0 + 9 * z [MOD m] := by
        simpa using hleft
      exact Nat.ModEq.add_right_cancel' (9 * z) hleft'

/- Residue-class sums via induction on the number of blocks -/

lemma sum_ite_eq_zero {lam : ℕ} (hlam : 0 < lam) (c : ℕ) :
    ∑ i ∈ Finset.range lam, (if i = 0 then c else 0) = c := by
  rw [Finset.sum_ite_eq']
  simp [hlam]

lemma sum_ite_eq_one {lam : ℕ} (hlam : 1 < lam) (c : ℕ) :
    ∑ i ∈ Finset.range lam, (if i = 1 then c else 0) = c := by
  rw [Finset.sum_ite_eq']
  simp
  omega

lemma block_mod (lam q i : ℕ) (hlam : 0 < lam) (hi : i < lam) :
    (q * lam + i) % lam = i := by
  rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hi]

lemma block_div (lam q i : ℕ) (hlam : 0 < lam) :
    (q * lam + i) / lam = q + i / lam := by
  rw [Nat.add_comm, Nat.add_mul_div_right i q hlam, add_comm]

lemma sum_residue_zero (lam q : ℕ) (hlam : 0 < lam) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range (q * lam), (if i % lam = 0 then f (i / lam) else 0) =
      ∑ j ∈ Finset.range q, f j := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    have : ∑ i ∈ Finset.range lam,
        (if (q * lam + i) % lam = 0 then f ((q * lam + i) / lam) else 0) = f q := by
      have hcongr : ∑ i ∈ Finset.range lam,
          (if (q * lam + i) % lam = 0 then f ((q * lam + i) / lam) else 0) =
          ∑ i ∈ Finset.range lam, (if i = 0 then f q else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < lam := Finset.mem_range.mp hi
        rw [block_mod lam q i hlam hi', block_div lam q i hlam]
        split_ifs with h
        · rw [h, Nat.zero_div, Nat.add_zero]
        · rfl
      rw [hcongr, sum_ite_eq_zero hlam]
    rw [this]

lemma sum_residue_one (lam q : ℕ) (hlam : 1 < lam) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range (q * lam), (if i % lam = 1 then f (i / lam) else 0) =
      ∑ j ∈ Finset.range q, f j := by
  have hlam0 : 0 < lam := by omega
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    have : ∑ i ∈ Finset.range lam,
        (if (q * lam + i) % lam = 1 then f ((q * lam + i) / lam) else 0) = f q := by
      have hcongr : ∑ i ∈ Finset.range lam,
          (if (q * lam + i) % lam = 1 then f ((q * lam + i) / lam) else 0) =
          ∑ i ∈ Finset.range lam, (if i = 1 then f q else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < lam := Finset.mem_range.mp hi
        rw [block_mod lam q i hlam0 hi', block_div lam q i hlam0]
        split_ifs with h
        · rw [h, Nat.div_eq_of_lt hlam, Nat.add_zero]
        · rfl
      rw [hcongr, sum_ite_eq_one hlam]
    rw [this]

lemma sum_residue_zero_pow (lam q : ℕ) (hlam : 0 < lam) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range (q * lam),
      (if i % lam = 0 then f (i / lam) else 0) * 10 ^ i =
      ∑ j ∈ Finset.range q, f j * 10 ^ (j * lam) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    have : ∑ i ∈ Finset.range lam,
        (if (q * lam + i) % lam = 0 then f ((q * lam + i) / lam) else 0) * 10 ^ (q * lam + i) =
        f q * 10 ^ (q * lam) := by
      have hbase : ∑ i ∈ Finset.range lam,
          (if i = 0 then f q * 10 ^ (q * lam + i) else 0) = f q * 10 ^ (q * lam) := by
        rw [Finset.sum_ite_eq']
        simp [hlam]
      rw [← hbase]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < lam := Finset.mem_range.mp hi
      rw [block_mod lam q i hlam hi', block_div lam q i hlam]
      split_ifs with h
      · rw [h, Nat.zero_div, Nat.add_zero]
      · simp
    rw [this]

lemma sum_residue_one_pow (lam q : ℕ) (hlam : 1 < lam) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range (q * lam),
      (if i % lam = 1 then f (i / lam) else 0) * 10 ^ i =
      ∑ j ∈ Finset.range q, f j * 10 ^ (j * lam + 1) := by
  have hlam0 : 0 < lam := by omega
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    have : ∑ i ∈ Finset.range lam,
        (if (q * lam + i) % lam = 1 then f ((q * lam + i) / lam) else 0) * 10 ^ (q * lam + i) =
        f q * 10 ^ (q * lam + 1) := by
      have hbase : ∑ i ∈ Finset.range lam,
          (if i = 1 then f q * 10 ^ (q * lam + i) else 0) = f q * 10 ^ (q * lam + 1) := by
        rw [Finset.sum_ite_eq']
        simp [hlam]
      rw [← hbase]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < lam := Finset.mem_range.mp hi
      rw [block_mod lam q i hlam0 hi', block_div lam q i hlam0]
      split_ifs with h
      · rw [h, Nat.div_eq_of_lt hlam, Nat.add_zero]
      · simp
    rw [this]

lemma modEq_sum {ι : Type*} (s : Finset ι) (f g : ι → ℕ) (m : ℕ)
    (h : ∀ i ∈ s, f i ≡ g i [MOD m]) :
    ∑ i ∈ s, f i ≡ ∑ i ∈ s, g i [MOD m] := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro; simp [Nat.ModEq]
  · intro a s ha ih h
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Nat.ModEq.add (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- Existence when gcd(10, m) = 1 -/

lemma exists_digitSum_dvd_of_coprime {s m : ℕ}
    (hm : 0 < m) (hs : m ≤ s) (hcop : Coprime 10 m) (hg : Nat.gcd m 9 ∣ s) :
    ∃ k, (digits 10 k).sum = s ∧ m ∣ k := by
  have hg' : Nat.gcd 9 m ∣ s := by rwa [Nat.gcd_comm]
  by_cases hdiv : m ∣ 9
  · let L := List.replicate s 1
    let k := ofDigits 10 L
    refine ⟨k, ?_, ?_⟩
    · have hlt : ∀ x ∈ L, x < 10 := by
        intro x hx
        have := (List.mem_replicate.mp hx).2
        omega
      rw [digits_sum_ofDigits_of_lt hlt]
      simp [L, List.sum_replicate]
    · have h10 : 10 ≡ 1 [MOD m] :=
        ((Nat.modEq_iff_dvd' (by decide : (1 : ℕ) ≤ 10)).2 (by simpa using hdiv)).symm
      have hk : k ≡ ofDigits (1 : ℕ) L [MOD m] := ofDigits_modEq' 10 1 m h10 L
      have h1 : ofDigits (1 : ℕ) L = s := ofDigits_one_replicate_one s
      have hms : m ∣ s := by
        have : Nat.gcd 9 m = m := Nat.gcd_eq_right_iff_dvd.mpr hdiv
        rwa [Nat.gcd_comm, this] at hg
      have : k ≡ s [MOD m] := by rwa [h1] at hk
      exact (Nat.modEq_zero_iff_dvd).mp (this.trans ((Nat.modEq_zero_iff_dvd).mpr hms))
  · have hφ : 1 < m.totient := by
      have hne : m.totient ≠ 1 := by
        intro h1
        rcases totient_eq_one_iff.mp h1 with rfl | rfl
        · exact hdiv (by decide)
        · exact absurd hcop (by decide)
      have : 0 < m.totient := totient_pos.mpr hm
      omega
    obtain ⟨y0, hy0m, hy0⟩ := exists_nine_mul_add_eq_zero_mod hm hg'
    have hy0le : y0 ≤ s := (le_of_lt hy0m).trans hs
    set x := s - y0
    set A := ninesAndRest x
    set B := ninesAndRest y0
    set lam := m.totient
    have hlam0 : 0 < lam := by omega
    have hpow10 : 10 ^ lam ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop
    set q := A.length + B.length + 1
    set N := q * lam
    have hAlen : A.length ≤ q := by omega
    have hBlen : B.length ≤ q := by omega
    let d : ℕ → ℕ := fun i =>
      if i % lam = 0 then A.getD (i / lam) 0
      else if i % lam = 1 then B.getD (i / lam) 0
      else 0
    let L := (List.range N).map d
    let k := ofDigits 10 L
    have hd_split : ∀ i,
        d i = (if i % lam = 0 then A.getD (i / lam) 0 else 0) +
              (if i % lam = 1 then B.getD (i / lam) 0 else 0) := by
      intro i
      dsimp [d]
      by_cases h0 : i % lam = 0
      · have h1 : i % lam ≠ 1 := by omega
        simp [h0, h1]
      · by_cases h1 : i % lam = 1
        · simp [h0, h1]
        · simp [h0, h1]
    have hdlt : ∀ i, d i < 10 := by
      intro i
      dsimp [d]
      split_ifs
      · exact ninesAndRest_getD_lt_ten x _
      · exact ninesAndRest_getD_lt_ten y0 _
      · omega
    have hLlt : ∀ z ∈ L, z < 10 := by
      intro z hz
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
      exact hdlt i
    refine ⟨k, ?_, ?_⟩
    · rw [digits_sum_ofDigits_of_lt hLlt, sum_map_range]
      have hsplit : ∑ i ∈ Finset.range N, d i =
          ∑ i ∈ Finset.range N, (if i % lam = 0 then A.getD (i / lam) 0 else 0) +
          ∑ i ∈ Finset.range N, (if i % lam = 1 then B.getD (i / lam) 0 else 0) := by
        simp_rw [hd_split, Finset.sum_add_distrib]
      rw [hsplit]
      dsimp [N]
      rw [sum_residue_zero lam q hlam0 (fun j => A.getD j 0)]
      rw [sum_residue_one lam q hφ (fun j => B.getD j 0)]
      rw [sum_getD_le A q hAlen, sum_getD_le B q hBlen, ninesAndRest_sum, ninesAndRest_sum]
      omega
    · have hk_eq : k = ∑ i ∈ Finset.range N, d i * 10 ^ i := ofDigits_map_range d N
      have hsplit : ∑ i ∈ Finset.range N, d i * 10 ^ i =
          ∑ i ∈ Finset.range N,
            (if i % lam = 0 then A.getD (i / lam) 0 else 0) * 10 ^ i +
          ∑ i ∈ Finset.range N,
            (if i % lam = 1 then B.getD (i / lam) 0 else 0) * 10 ^ i := by
        have : ∀ i, d i * 10 ^ i =
            (if i % lam = 0 then A.getD (i / lam) 0 else 0) * 10 ^ i +
            (if i % lam = 1 then B.getD (i / lam) 0 else 0) * 10 ^ i := by
          intro i
          rw [hd_split]
          ring
        simp_rw [this, Finset.sum_add_distrib]
      rw [hk_eq, hsplit]
      dsimp [N]
      rw [sum_residue_zero_pow lam q hlam0 (fun j => A.getD j 0)]
      rw [sum_residue_one_pow lam q hφ (fun j => B.getD j 0)]
      have hpow : ∀ j, 10 ^ (j * lam) ≡ 1 [MOD m] := by
        intro j
        have : 10 ^ (j * lam) = (10 ^ lam) ^ j := by
          rw [mul_comm j lam, pow_mul]
        rw [this]
        simpa using Nat.ModEq.pow j hpow10
      have hA : ∑ j ∈ Finset.range q, A.getD j 0 * 10 ^ (j * lam) ≡
          ∑ j ∈ Finset.range q, A.getD j 0 [MOD m] := by
        refine modEq_sum _ _ _ _ ?_
        intro j _
        have : A.getD j 0 * 10 ^ (j * lam) ≡ A.getD j 0 * 1 [MOD m] :=
          Nat.ModEq.mul_left _ (hpow j)
        simpa using this
      have hB : ∑ j ∈ Finset.range q, B.getD j 0 * 10 ^ (j * lam + 1) ≡
          ∑ j ∈ Finset.range q, B.getD j 0 * 10 [MOD m] := by
        refine modEq_sum _ _ _ _ ?_
        intro j _
        have : 10 ^ (j * lam + 1) = 10 ^ (j * lam) * 10 := by rw [Nat.pow_succ]
        rw [this]
        have h1 : B.getD j 0 * (10 ^ (j * lam) * 10) ≡ B.getD j 0 * (1 * 10) [MOD m] :=
          Nat.ModEq.mul_left _ (Nat.ModEq.mul (hpow j) (Nat.ModEq.refl 10))
        simpa [Nat.one_mul] using h1
      have hAsum : ∑ j ∈ Finset.range q, A.getD j 0 = x := by
        rw [sum_getD_le A q hAlen, ninesAndRest_sum]
      have hBsum : ∑ j ∈ Finset.range q, B.getD j 0 = y0 := by
        rw [sum_getD_le B q hBlen, ninesAndRest_sum]
      have hB10 : ∑ j ∈ Finset.range q, B.getD j 0 * 10 =
          10 * ∑ j ∈ Finset.range q, B.getD j 0 := by
        simp [Finset.mul_sum, Nat.mul_comm]
      have hsum : ∑ j ∈ Finset.range q, A.getD j 0 * 10 ^ (j * lam) +
          ∑ j ∈ Finset.range q, B.getD j 0 * 10 ^ (j * lam + 1) ≡
          x + 10 * y0 [MOD m] := by
        have hB' : ∑ j ∈ Finset.range q, B.getD j 0 * 10 ^ (j * lam + 1) ≡
            10 * y0 [MOD m] := by
          have := hB.trans (by
            rw [hB10, hBsum])
          exact this
        have := Nat.ModEq.add hA hB'
        rwa [hAsum] at this
      have hx10y : x + 10 * y0 ≡ 0 [MOD m] := by
        have : x + 10 * y0 = s + 9 * y0 := by
          dsimp [x]
          omega
        rw [this, Nat.add_comm]
        exact hy0
      exact (Nat.modEq_zero_iff_dvd).mp (hsum.trans hx10y)

/- General existence -/

lemma two_pow_mul_five_pow_dvd (m : ℕ) :
    2 ^ padicValNat 2 m * 5 ^ padicValNat 5 m ∣ m := by
  have hcop : Coprime (2 ^ padicValNat 2 m) (5 ^ padicValNat 5 m) :=
    Nat.Coprime.pow _ _ (by decide)
  exact hcop.mul_dvd_of_dvd_of_dvd (pow_padicValNat_dvd (p := 2) (n := m))
    (pow_padicValNat_dvd (p := 5) (n := m))

lemma not_two_dvd_of_div_padic (m : ℕ) (hm : 0 < m) :
    ¬ 2 ∣ m / (2 ^ padicValNat 2 m * 5 ^ padicValNat 5 m) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro h
  obtain ⟨t, ht⟩ := h
  have h25 := two_pow_mul_five_pow_dvd m
  have : 2 ^ (padicValNat 2 m + 1) ∣ m := by
    refine ⟨t * 5 ^ padicValNat 5 m, ?_⟩
    have hm' : m / (2 ^ padicValNat 2 m * 5 ^ padicValNat 5 m) *
        (2 ^ padicValNat 2 m * 5 ^ padicValNat 5 m) = m := Nat.div_mul_cancel h25
    calc
      m = m / (2 ^ padicValNat 2 m * 5 ^ padicValNat 5 m) *
          (2 ^ padicValNat 2 m * 5 ^ padicValNat 5 m) := hm'.symm
      _ = (2 * t) * (2 ^ padicValNat 2 m * 5 ^ padicValNat 5 m) := by rw [ht]
      _ = 2 ^ (padicValNat 2 m + 1) * (t * 5 ^ padicValNat 5 m) := by ring
  exact (pow_succ_padicValNat_not_dvd hm.ne') this

lemma not_five_dvd_of_div_padic (m : ℕ) (hm : 0 < m) :
    ¬ 5 ∣ m / (2 ^ padicValNat 2 m * 5 ^ padicValNat 5 m) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro h
  obtain ⟨t, ht⟩ := h
  have h25 := two_pow_mul_five_pow_dvd m
  have : 5 ^ (padicValNat 5 m + 1) ∣ m := by
    refine ⟨t * 2 ^ padicValNat 2 m, ?_⟩
    have hm' : m / (2 ^ padicValNat 2 m * 5 ^ padicValNat 5 m) *
        (2 ^ padicValNat 2 m * 5 ^ padicValNat 5 m) = m := Nat.div_mul_cancel h25
    calc
      m = m / (2 ^ padicValNat 2 m * 5 ^ padicValNat 5 m) *
          (2 ^ padicValNat 2 m * 5 ^ padicValNat 5 m) := hm'.symm
      _ = (5 * t) * (2 ^ padicValNat 2 m * 5 ^ padicValNat 5 m) := by rw [ht]
      _ = 5 ^ (padicValNat 5 m + 1) * (t * 2 ^ padicValNat 2 m) := by ring
  exact (pow_succ_padicValNat_not_dvd hm.ne') this

lemma coprime_ten_of_div_padic (m : ℕ) (hm : 0 < m) :
    Coprime 10 (m / (2 ^ padicValNat 2 m * 5 ^ padicValNat 5 m)) := by
  set m' := m / (2 ^ padicValNat 2 m * 5 ^ padicValNat 5 m)
  have h2 : ¬ 2 ∣ m' := not_two_dvd_of_div_padic m hm
  have h5 : ¬ 5 ∣ m' := not_five_dvd_of_div_padic m hm
  rw [Nat.coprime_iff_gcd_eq_one]
  have hd : Nat.gcd 10 m' ∣ 10 := Nat.gcd_dvd_left _ _
  have hpos : 0 < Nat.gcd 10 m' := Nat.gcd_pos_of_pos_left _ (by decide)
  have hle : Nat.gcd 10 m' ≤ 10 := Nat.le_of_dvd (by decide) hd
  have hne2 : Nat.gcd 10 m' ≠ 2 := fun h => h2 (h ▸ Nat.gcd_dvd_right 10 m')
  have hne5 : Nat.gcd 10 m' ≠ 5 := fun h => h5 (h ▸ Nat.gcd_dvd_right 10 m')
  have hne10 : Nat.gcd 10 m' ≠ 10 := fun h => h2 (by
    have : 2 ∣ Nat.gcd 10 m' := by
      rw [h]
      decide
    exact Nat.dvd_trans this (Nat.gcd_dvd_right 10 m'))
  have hmem : Nat.gcd 10 m' ∈ Nat.divisors 10 :=
    Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hdivs : Nat.divisors 10 = {1, 2, 5, 10} := by decide
  rw [hdivs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact h
  · exact (hne2 h).elim
  · exact (hne5 h).elim
  · exact (hne10 h).elim

lemma exists_digitSum_dvd {s m : ℕ}
    (hm : 0 < m) (hs : m ≤ s) (hg : Nat.gcd m 9 ∣ s) :
    ∃ k, (digits 10 k).sum = s ∧ m ∣ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let v2 := padicValNat 2 m
  let v5 := padicValNat 5 m
  have hcop25 : Coprime (2 ^ v2) (5 ^ v5) :=
    Nat.Coprime.pow v2 v5 (by decide)
  have h25 : 2 ^ v2 * 5 ^ v5 ∣ m := two_pow_mul_five_pow_dvd m
  set m' := m / (2 ^ v2 * 5 ^ v5)
  have hm'mul : m' * (2 ^ v2 * 5 ^ v5) = m := Nat.div_mul_cancel h25
  have hm'pos : 0 < m' := by
    have hpos : 0 < 2 ^ v2 * 5 ^ v5 := by positivity
    have : 0 < m' * (2 ^ v2 * 5 ^ v5) := by
      rw [hm'mul]; exact hm
    exact (Nat.pos_iff_ne_zero.mpr fun h => by simp [h] at this)
  have hcop' : Coprime 10 m' := coprime_ten_of_div_padic m hm
  have hg' : Nat.gcd m' 9 ∣ s := by
    have hcop259 : Coprime (2 ^ v2 * 5 ^ v5) 9 :=
      Nat.Coprime.mul
        (Nat.Coprime.pow_left v2 (by decide : Coprime 2 9))
        (Nat.Coprime.pow_left v5 (by decide : Coprime 5 9))
    have : Nat.gcd m 9 = Nat.gcd m' 9 := by
      rw [← hm'mul, Nat.mul_comm]
      exact hcop259.gcd_mul_left_cancel m'
    rwa [← this]
  have hs' : m' ≤ s := (Nat.div_le_self _ _).trans hs
  obtain ⟨k', hk'sum, hk'dvd⟩ := exists_digitSum_dvd_of_coprime hm'pos hs' hcop' hg'
  have hk'pos : 0 < k' := by
    have : 0 < (digits 10 k').sum := by rw [hk'sum]; omega
    exact Nat.pos_of_ne_zero (fun h => by simp [h] at this)
  set t := max v2 v5
  refine ⟨k' * 10 ^ t, ?_, ?_⟩
  · have hb : 1 < 10 := by decide
    rw [mul_comm k', digits_base_pow_mul hb hk'pos, List.sum_append, List.sum_replicate, hk'sum]
    simp
  · have h25t : 2 ^ v2 * 5 ^ v5 ∣ 10 ^ t := by
      have h10 : 10 ^ t = 2 ^ t * 5 ^ t := by
        change (2 * 5) ^ t = 2 ^ t * 5 ^ t
        exact Nat.mul_pow 2 5 t
      rw [h10]
      have hv2t : 2 ^ v2 ∣ 2 ^ t := pow_dvd_pow 2 (le_max_left v2 v5)
      have hv5t : 5 ^ v5 ∣ 5 ^ t := pow_dvd_pow 5 (le_max_right v2 v5)
      exact hcop25.mul_dvd_of_dvd_of_dvd (dvd_mul_of_dvd_left hv2t _) (dvd_mul_of_dvd_right hv5t _)
    have : m' * (2 ^ v2 * 5 ^ v5) ∣ k' * 10 ^ t := mul_dvd_mul hk'dvd h25t
    rwa [hm'mul] at this

/- Partners are nonempty -/

lemma partners_nonempty {n : ℕ} (hn : 0 < n) :
    {k | 0 < k ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n}.Nonempty := by
  by_cases hsmall : n < 10
  · refine ⟨10 * n, ?_⟩
    have hb : 1 < 10 := by decide
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [digitSum_eq_of_lt_ten hsmall]
      simpa [mul_comm] using dvd_mul_right n 10
    · have : digits 10 (10 * n) = 0 :: digits 10 n := digits_base_mul hb hn
      rw [this, List.sum_cons, digitSum_eq_of_lt_ten hsmall, zero_add]
  · have hn10 : 10 ≤ n := le_of_not_gt hsmall
    have hm : 0 < (digits 10 n).sum := digitSum_pos hn
    have hs : (digits 10 n).sum ≤ n := digit_sum_le 10 n
    have hg : Nat.gcd (digits 10 n).sum 9 ∣ n := gcd_digitSum_nine_dvd n
    obtain ⟨k, hksum, hkdvd⟩ := exists_digitSum_dvd hm hs hg
    refine ⟨k, ?_⟩
    have hkpos : 0 < k := by
      have : 0 < (digits 10 k).sum := by rw [hksum]; omega
      exact Nat.pos_of_ne_zero (fun h => by simp [h] at this)
    have hkne : k ≠ n := by
      intro heq
      have h1 : (digits 10 n).sum = n := by
        rw [heq] at hksum
        exact hksum
      have h2 : (digits 10 n).sum < n := digitSum_lt_of_ge_ten hn10
      omega
    exact ⟨hkpos, hkne, hkdvd, by rw [hksum]⟩

/-- A272479 Conjecture: the sequence contains no zeros. -/
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hn
  have hne := partners_nonempty hn
  have ha : a n =
      if h : {k | 0 < k ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n}.Nonempty then
        sInf {k | 0 < k ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n}
      else 0 := rfl
  rw [ha, dif_pos hne]
  have hmem := Nat.sInf_mem hne
  simp only [Set.mem_setOf_eq] at hmem
  omega
