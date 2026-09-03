import Submission.PatternObstruction

/-! Arithmetic refinements of the pattern obstruction. Not a settlement of Erdős 406. -/

namespace Erdos406Work

lemma good_ofDigits {w : List ℕ} (hw : w ⊆ [0, 1]) :
    Nat.digits 3 (Nat.ofDigits 3 w) ⊆ [0, 1] := by
  induction w with
  | nil => simp [Nat.ofDigits]
  | cons d w ih =>
    have hd := hw (by simp : d ∈ d :: w)
    have ht : w ⊆ [0, 1] := fun a ha => hw (by simp [ha])
    have h := ih ht
    have hdlt : d < 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      omega
    rw [Nat.ofDigits_cons]
    by_cases hz : d = 0 ∧ Nat.ofDigits 3 w = 0
    · simp [hz.1, hz.2]
    · rw [Nat.digits_add 3 (by decide) d (Nat.ofDigits 3 w) hdlt (by tauto)]
      simpa using List.cons_subset.mpr ⟨hd, h⟩

/-- All residue classes modulo an integer coprime to three have a ternary
representative using only zero and one. This does not claim that the
representative is a power of two. -/
lemma good_representative_mod {q : ℕ} (hq : Nat.Coprime 3 q) (r : ℕ) :
    ∃ n : ℕ, Nat.digits 3 n ⊆ [0, 1] ∧ Nat.ModEq q n r := by
  have hqpos : 0 < q := by
    by_contra hh
    have hz : q = 0 := by omega
    simp [hz] at hq
  let T := q.totient
  have hT : 0 < T := Nat.totient_pos.mpr hqpos
  let block : List ℕ := 1 :: List.replicate (T - 1) 0
  have hlen : block.length = T := by simp only [block, List.length_cons, List.length_replicate]; omega
  have hval : Nat.ofDigits 3 block = 1 := by simp [block, Nat.ofDigits_cons]
  have hword : ∀ i : ℕ, (List.replicate i block).flatten ⊆ [0, 1] := by
    intro i d hd
    simp only [List.mem_flatten, List.mem_replicate] at hd
    obtain ⟨b, ⟨_, rfl⟩, hb⟩ := hd
    simp only [block, List.mem_cons, List.mem_replicate] at hb
    rcases hb with rfl | ⟨_, rfl⟩ <;> simp
  have hmod : ∀ i : ℕ, Nat.ModEq q (Nat.ofDigits 3 (List.replicate i block).flatten) i := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append, hlen, hval]
      have ht : Nat.ModEq q (3 ^ T) 1 := Nat.ModEq.pow_totient hq
      simpa [Nat.add_comm] using (Nat.ModEq.refl 1).add (ht.mul ih)
  exact ⟨_, good_ofDigits (hword r), hmod r⟩

/-- Arbitrary leading blocks can disappear even inside a prescribed residue
class modulo a number coprime to three. -/
lemma arbitrary_prefix_can_disappear_mod (A s q r B : ℕ)
    (hA : 0 < A) (hs : 0 < s) (hq : Nat.Coprime 3 q) :
    ∃ t n L : ℕ, 0 < t ∧ B < n ∧ n / 3 ^ L = A ∧
      Nat.digits 3 (4 ^ (s * t) * n) ⊆ [0, 1] ∧ Nat.ModEq q n r := by
  obtain ⟨t, E, ht, hlo, hhi⟩ := reciprocal_four_power_prefix A s hA hs
  let Q := 4 ^ (s * t)
  let D := Q * q
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hqpos : 0 < q := by
    by_contra hh
    have hz : q = 0 := by omega
    simp [hz] at hq
  have hD : 0 < D := Nat.mul_pos hQ hqpos
  have hcop : Nat.Coprime 3 D :=
    ((by decide : Nat.Coprime 3 4).pow_right _).mul_right hq
  obtain ⟨a, hgooda, ha⟩ := good_representative_mod hcop (D + Q * r - 1)
  let T := D.totient
  have hT : 0 < T := Nat.totient_pos.mpr hD
  let c := T * (E + B + a + (Nat.digits 3 a).length + 1)
  have hcle : E + B + a + (Nat.digits 3 a).length + 1 ≤ c := by
    exact Nat.le_mul_of_pos_left _ hT
  have hc : (Nat.digits 3 a).length ≤ c := by omega
  have hcmod : Nat.ModEq D (3 ^ c) 1 := by
    have hh := (Nat.ModEq.pow_totient hcop).pow
      (E + B + a + (Nat.digits 3 a).length + 1)
    simpa only [← pow_mul, one_pow] using hh
  have htarget : Nat.ModEq D (3 ^ c + a) (Q * r) := by
    have hh := hcmod.add ha
    have hnum : 1 + (D + Q * r - 1) = D + Q * r := by omega
    rw [hnum] at hh
    exact hh.trans (by simp [Nat.ModEq])
  have hd : Q ∣ 3 ^ c + a :=
    (htarget.dvd_iff (dvd_mul_right Q q)).mpr (dvd_mul_right Q r)
  obtain ⟨n, hn⟩ := hd
  have hnmod : Nat.ModEq q n r := by
    rw [hn] at htarget
    exact Nat.ModEq.mul_left_cancel' (ne_of_gt hQ) htarget
  let L := c - E
  have hLB : B < L := by dsimp [L]; omega
  have hLa : a < L := by dsimp [L]; omega
  have hpow : 3 ^ c = 3 ^ E * 3 ^ L := by
    rw [← pow_add]
    congr 1
    dsimp [L]
    omega
  have haL : a < 3 ^ L := hLa.trans (Nat.lt_pow_self (by decide))
  have hnlo : A * 3 ^ L ≤ n := by
    apply Nat.le_of_mul_le_mul_left (c := Q) _ hQ
    calc
      Q * (A * 3 ^ L) = (A * Q) * 3 ^ L := by ring
      _ ≤ 3 ^ E * 3 ^ L := Nat.mul_le_mul_right _ (le_of_lt hlo)
      _ ≤ Q * n := by rw [← hn, ← hpow]; omega
  have hnhi : n < (A + 1) * 3 ^ L := by
    apply Nat.lt_of_mul_lt_mul_left (a := Q)
    have hh := Nat.mul_le_mul_right (3 ^ L) (Nat.succ_le_of_lt hhi)
    calc
      Q * n = 3 ^ E * 3 ^ L + a := by rw [← hn, hpow]
      _ < (3 ^ E + 1) * 3 ^ L := by nlinarith
      _ ≤ ((A + 1) * Q) * 3 ^ L := hh
      _ = Q * ((A + 1) * 3 ^ L) := by ring
  have hnB : B < n := by
    have hh : L < 3 ^ L := Nat.lt_pow_self (by decide)
    have hAn : 3 ^ L ≤ A * 3 ^ L := Nat.le_mul_of_pos_left _ hA
    omega
  refine ⟨t, n, L, ht, hnB, Nat.div_eq_of_lt_le hnlo hnhi, ?_, hnmod⟩
  change Nat.digits 3 (Q * n) ⊆ [0, 1]
  rw [← hn, Nat.add_comm]
  have hword := Nat.digits_append_zeroes_append_digits (b := 3) (n := a) (m := 1)
    (k := c - (Nat.digits 3 a).length) (by decide) (by decide)
  rw [Nat.add_sub_of_le hc, mul_one] at hword
  rw [← hword]
  intro d hd
  simp only [List.mem_append, List.mem_replicate] at hd
  rcases hd with (hd | ⟨_, rfl⟩) | hd
  · exact hgooda hd
  · simp
  · have hd1 : Nat.digits 3 1 = [1] := by decide +kernel
    rw [hd1] at hd
    simp only [List.mem_singleton] at hd
    simp [hd]

/-- The preceding construction can retain an odd divisor. In particular the
constructed predecessors are not powers of two. -/
lemma arbitrary_nonpower_prefix_can_disappear_mod (A s q r B : ℕ)
    (hA : 0 < A) (hs : 0 < s) (hq : Nat.Coprime 3 q) :
    ∃ t n L : ℕ, 0 < t ∧ B < n ∧ n / 3 ^ L = A ∧
      Nat.digits 3 (4 ^ (s * t) * n) ⊆ [0, 1] ∧ Nat.ModEq q n r ∧
      ¬ n.isPowerOfTwo := by
  have hqpos : 0 < q := by
    by_contra hh
    have hz : q = 0 := by omega
    simp [hz] at hq
  obtain ⟨p, hpq, hp⟩ := Nat.exists_infinite_primes (q + 4)
  have hp3 : 3 < p := by omega
  have hcpq : Nat.Coprime p q := Nat.coprime_of_lt_prime (ne_of_gt hqpos) (by omega) hp
  have hc3p : Nat.Coprime 3 p :=
    (Nat.coprime_of_lt_prime (by decide : 3 ≠ 0) hp3 hp).symm
  let R := r * p ^ q.totient
  have hR : Nat.ModEq q R r := by
    have hh := (Nat.ModEq.pow_totient hcpq).mul_left r
    simpa only [mul_one] using hh
  have hpR : p ∣ R := by
    apply dvd_mul_of_dvd_right
    exact dvd_pow_self p (ne_of_gt (Nat.totient_pos.mpr hqpos))
  obtain ⟨t, n, L, ht, hnB, hlead, hgood, hmod⟩ :=
    arbitrary_prefix_can_disappear_mod A s (q * p) R B hA hs (hq.mul_right hc3p)
  have hnq : Nat.ModEq q n r :=
    (hmod.of_dvd (dvd_mul_right q p)).trans hR
  have hpn : p ∣ n := (hmod.dvd_iff (dvd_mul_left p q)).mpr hpR
  refine ⟨t, n, L, ht, hnB, hlead, hgood, hnq, ?_⟩
  rintro ⟨k, hk⟩
  rw [hk] at hpn
  have h2 := hp.dvd_of_dvd_pow hpn
  have hle := Nat.le_of_dvd (by decide : 0 < 2) h2
  omega

lemma arbitrary_nonpower_block_can_disappear_mod (w : List ℕ) (hw : ∀ d ∈ w, d < 3)
    (s q r B : ℕ) (hs : 0 < s) (hq : Nat.Coprime 3 q) :
    ∃ t n : ℕ, 0 < t ∧ B < n ∧ w <:+: Nat.digits 3 n ∧
      Nat.digits 3 (4 ^ (s * t) * n) ⊆ [0, 1] ∧ Nat.ModEq q n r ∧
      ¬ n.isPowerOfTwo := by
  let A := Nat.ofDigits 3 (w ++ [1])
  have hA : 0 < A := by
    dsimp [A]
    rw [Nat.ofDigits_append]
    simp only [Nat.ofDigits_singleton, mul_one]
    positivity
  have hdA : Nat.digits 3 A = w ++ [1] := by
    apply Nat.digits_ofDigits 3 (by decide)
    · intro d hd
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with hd | rfl
      · exact hw d hd
      · decide
    · intro h
      simp
  obtain ⟨t, n, L, ht, hnB, hnA, hgood, hmod, hnp⟩ :=
    arbitrary_nonpower_prefix_can_disappear_mod A s q r B hA hs hq
  have hdrop : (Nat.digits 3 n).drop L = w ++ [1] := by
    have hh := congrArg (Nat.digits 3) hnA
    rwa [digits_div_three_pow, hdA] at hh
  refine ⟨t, n, ht, hnB, ?_, hgood, hmod, hnp⟩
  refine ⟨(Nat.digits 3 n).take L, [1], ?_⟩
  rw [List.append_assoc, ← hdrop, List.take_append_drop]

/-- Fixed arithmetic residue tests, with modulus coprime to three, do not
repair a finite substring-presence certificate. This remains a restriction on
this particular template, not on arbitrary finite-state languages. -/
lemma finite_pattern_arithmetic_certificate_no_power_seed (P : ℕ → Prop)
    (F : List (List ℕ)) (hF : ∀ w ∈ F, ∀ d ∈ w, d < 3)
    (q : ℕ) (hq : Nat.Coprime 3 q)
    (B K s E : ℕ) (hs : 0 < s) (hKE : K ≤ E) (hBE : B < 4 ^ E)
    (hsame : ∀ n m : ℕ, B < n → B < m → 4 ^ K ∣ n → 4 ^ K ∣ m → Nat.ModEq q n m →
      (∀ w ∈ F, (w <:+: Nat.digits 3 n ↔ w <:+: Nat.digits 3 m)) → P n → P m)
    (hmul : ∀ n : ℕ, B < n → 4 ^ K ∣ n → P n → P (4 ^ s * n))
    (hsafe : ∀ n : ℕ, B < n → 4 ^ K ∣ n → Nat.digits 3 n ⊆ [0, 1] → ¬ P n) :
    ¬ P (4 ^ E) := by
  intro hseed
  have hflat : ∀ d ∈ F.flatten, d < 3 := by
    intro d hd
    obtain ⟨w, hw, hdw⟩ := List.mem_flatten.mp hd
    exact hF w hw d hdw
  have hpowB (j : ℕ) : B < 4 ^ (E + s * j) :=
    hBE.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hpowK (j : ℕ) : 4 ^ K ∣ 4 ^ (E + s * j) := pow_dvd_pow 4 (by omega)
  have hiterPow : ∀ j : ℕ, P (4 ^ (E + s * j)) := by
    intro j
    induction j with
    | zero => simpa using hseed
    | succ j ih =>
      have hh := hmul _ (hpowB j) (hpowK j) ih
      simpa only [Nat.mul_succ, pow_add, mul_assoc, mul_left_comm, mul_comm] using hh
  obtain ⟨j, _, hwordPow⟩ := power_in_progression_contains_block F.flatten hflat E s 0 hs
  obtain ⟨t, m, ht, hmB, hwordM, hgood, hmod, _⟩ :=
    arbitrary_nonpower_block_can_disappear_mod F.flatten hflat s (q * 4 ^ K)
      (4 ^ (E + s * j)) B hs
      (hq.mul_right ((by decide : Nat.Coprime 3 4).pow_right K))
  have hmK : 4 ^ K ∣ m :=
    (hmod.dvd_iff (dvd_mul_left (4 ^ K) q)).mpr (hpowK j)
  have hmQ : Nat.ModEq q (4 ^ (E + s * j)) m :=
    (hmod.of_dvd (dvd_mul_right q (4 ^ K))).symm
  have hPm : P m := by
    apply hsame (4 ^ (E + s * j)) m (hpowB j) hmB (hpowK j) hmK hmQ _ (hiterPow j)
    intro w hw
    have hh := infix_flatten_of_mem hw
    exact ⟨fun _ => hh.trans hwordM, fun _ => hh.trans hwordPow⟩
  have hmpos : 0 < m := by omega
  have horbitB (i : ℕ) : B < 4 ^ (s * i) * m :=
    hmB.trans_le (Nat.le_mul_of_pos_left m (by positivity))
  have horbitK (i : ℕ) : 4 ^ K ∣ 4 ^ (s * i) * m := dvd_mul_of_dvd_right hmK _
  have hiterM : ∀ i : ℕ, P (4 ^ (s * i) * m) := by
    intro i
    induction i with
    | zero => simpa using hPm
    | succ i ih =>
      have hh := hmul _ (horbitB i) (horbitK i) ih
      simpa only [Nat.mul_succ, pow_add, mul_assoc, mul_left_comm, mul_comm] using hh
  exact hsafe _ (horbitB t) (horbitK t) hgood (hiterM t)


#print axioms good_representative_mod
#print axioms arbitrary_prefix_can_disappear_mod
#print axioms arbitrary_nonpower_prefix_can_disappear_mod
#print axioms arbitrary_nonpower_block_can_disappear_mod
#print axioms finite_pattern_arithmetic_certificate_no_power_seed
end Erdos406Work
