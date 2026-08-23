import FormalConjectures.Util.ProblemImports

open Nat

/--
A223086: Trajectory of 64 under the map $n \to A006368(n)$.
The map is $f(n)$:
$$f(n) = \begin{cases} 3n/2 & \text{if } n \equiv 0 \pmod 2 \\ (3n+1)/4 & \text{if } n \equiv 1 \pmod 4 \\ (3n-1)/4 & \text{if } n \equiv 3 \pmod 4 \end{cases}$$
-/
def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

/--
A223086: Trajectory of 64 under the map $n \to A006368(n)$.
The sequence $a(n)$ is 1-indexed by $a(1)=64$ and recurrence $a(n+1) = f(a(n))$.
The $n$-th term is $f^{n-1}(64)$.
-/
def a (n : ℕ) : ℕ :=
  Nat.iterate A006368_map (n - 1) 64

open Function

/-! ### Inverse map and bijectivity -/

/-- Inverse of `A006368_map`, given by residue modulo 3. -/
def A006368_inv (m : ℕ) : ℕ :=
  if m % 3 = 0 then
    (2 * m) / 3
  else if m % 3 = 1 then
    (4 * m - 1) / 3
  else
    (4 * m + 1) / 3

lemma map_even (k : ℕ) : A006368_map (2 * k) = 3 * k := by
  simp [A006368_map]
  convert Nat.mul_div_cancel_left (3 * k) (by decide : 0 < 2) using 2
  ring

lemma map_mod4_one (k : ℕ) : A006368_map (4 * k + 1) = 3 * k + 1 := by
  have h2 : (4 * k + 1) % 2 = 1 := by omega
  have h4 : (4 * k + 1) % 4 = 1 := by omega
  simp [A006368_map, h2, h4]
  convert Nat.mul_div_cancel_left (3 * k + 1) (by decide : 0 < 4) using 2
  ring

lemma map_mod4_three (k : ℕ) : A006368_map (4 * k + 3) = 3 * k + 2 := by
  have h2 : (4 * k + 3) % 2 = 1 := by omega
  have h4 : ¬ (4 * k + 3) % 4 = 1 := by omega
  simp [A006368_map, h2, h4]
  convert Nat.mul_div_cancel_left (3 * k + 2) (by decide : 0 < 4) using 2
  have : 3 * (4 * k + 3) = 12 * k + 9 := by ring
  rw [this]
  have : 1 ≤ 12 * k + 9 := by omega
  rw [Nat.sub_eq_of_eq_add]
  ring

lemma inv_mod3_zero (t : ℕ) : A006368_inv (3 * t) = 2 * t := by
  simp [A006368_inv]
  convert Nat.mul_div_cancel_left (2 * t) (by decide : 0 < 3) using 2
  ring

lemma inv_mod3_one (t : ℕ) : A006368_inv (3 * t + 1) = 4 * t + 1 := by
  have h : (3 * t + 1) % 3 = 1 := by omega
  simp [A006368_inv, h]
  convert Nat.mul_div_cancel_left (4 * t + 1) (by decide : 0 < 3) using 2
  have : 4 * (3 * t + 1) = 12 * t + 4 := by ring
  rw [this]
  have : 1 ≤ 12 * t + 4 := by omega
  rw [Nat.sub_eq_of_eq_add]
  ring

lemma inv_mod3_two (t : ℕ) : A006368_inv (3 * t + 2) = 4 * t + 3 := by
  have h0 : ¬ (3 * t + 2) % 3 = 0 := by omega
  have h1 : ¬ (3 * t + 2) % 3 = 1 := by omega
  simp [A006368_inv, h0, h1]
  convert Nat.mul_div_cancel_left (4 * t + 3) (by decide : 0 < 3) using 2
  ring

lemma exists_form_even {n : ℕ} (h : n % 2 = 0) : ∃ k, n = 2 * k :=
  ⟨n / 2, (Nat.div_add_mod n 2).symm.trans (by rw [h]; ring)⟩

lemma exists_form_mod4_one {n : ℕ} (h : n % 4 = 1) : ∃ k, n = 4 * k + 1 :=
  ⟨n / 4, (Nat.div_add_mod n 4).symm.trans (by rw [h])⟩

lemma exists_form_mod4_three {n : ℕ} (h : n % 4 = 3) : ∃ k, n = 4 * k + 3 :=
  ⟨n / 4, (Nat.div_add_mod n 4).symm.trans (by rw [h])⟩

lemma exists_form_mod3_zero {n : ℕ} (h : n % 3 = 0) : ∃ t, n = 3 * t :=
  ⟨n / 3, (Nat.div_add_mod n 3).symm.trans (by rw [h]; ring)⟩

lemma exists_form_mod3_one {n : ℕ} (h : n % 3 = 1) : ∃ t, n = 3 * t + 1 :=
  ⟨n / 3, (Nat.div_add_mod n 3).symm.trans (by rw [h])⟩

lemma exists_form_mod3_two {n : ℕ} (h : n % 3 = 2) : ∃ t, n = 3 * t + 2 :=
  ⟨n / 3, (Nat.div_add_mod n 3).symm.trans (by rw [h])⟩

lemma even_or_mod4 (n : ℕ) : n % 2 = 0 ∨ n % 4 = 1 ∨ n % 4 = 3 := by
  omega

lemma mod3_cases (n : ℕ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
  omega

lemma leftInverse_inv_map : LeftInverse A006368_inv A006368_map := by
  intro n
  rcases even_or_mod4 n with h | h | h
  · obtain ⟨k, rfl⟩ := exists_form_even h
    rw [map_even, inv_mod3_zero]
  · obtain ⟨k, rfl⟩ := exists_form_mod4_one h
    rw [map_mod4_one, inv_mod3_one]
  · obtain ⟨k, rfl⟩ := exists_form_mod4_three h
    rw [map_mod4_three, inv_mod3_two]

lemma rightInverse_inv_map : RightInverse A006368_inv A006368_map := by
  intro m
  rcases mod3_cases m with h | h | h
  · obtain ⟨t, rfl⟩ := exists_form_mod3_zero h
    rw [inv_mod3_zero, map_even]
  · obtain ⟨t, rfl⟩ := exists_form_mod3_one h
    rw [inv_mod3_one, map_mod4_one]
  · obtain ⟨t, rfl⟩ := exists_form_mod3_two h
    rw [inv_mod3_two, map_mod4_three]

lemma map_injective : Injective A006368_map :=
  LeftInverse.injective leftInverse_inv_map

lemma map_surjective : Surjective A006368_map :=
  RightInverse.surjective rightInverse_inv_map

lemma map_bijective : Bijective A006368_map :=
  ⟨map_injective, map_surjective⟩

lemma iterate_eq_implies_periodic {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (heq : A006368_map^[i - 1] 64 = A006368_map^[j - 1] 64) :
    i = j ∨ ∃ k > 0, A006368_map^[k] 64 = 64 := by
  wlog hle : i ≤ j generalizing i j
  · rcases this hj hi heq.symm (le_of_not_ge hle) with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hidx : i + d - 1 = d + (i - 1) := by omega
  rw [hidx, iterate_add_apply] at heq
  by_cases hd : d = 0
  · exact Or.inl (by omega)
  · have hinj : Injective (A006368_map^[i - 1]) := Injective.iterate map_injective (i - 1)
    have : A006368_map^[i - 1] (A006368_map^[d] 64) = A006368_map^[i - 1] 64 := by
      rw [← iterate_add_apply, Nat.add_comm, iterate_add_apply, ← heq]
    exact Or.inr ⟨d, Nat.pos_of_ne_zero hd, hinj this⟩


/-! ### Elementary inequalities -/

lemma map_even_gt {n : ℕ} (he : n % 2 = 0) (hn : 0 < n) :
    n < A006368_map n := by
  obtain ⟨t, rfl⟩ := exists_form_even he
  have ht : 0 < t := by omega
  rw [map_even]
  omega

lemma map_odd_lt {n : ℕ} (ho : n % 2 = 1) (hn : 1 < n) :
    A006368_map n < n := by
  have h13 : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases h13 with h | h
  · obtain ⟨t, rfl⟩ := exists_form_mod4_one h
    have ht : 0 < t := by omega
    rw [map_mod4_one]
    omega
  · obtain ⟨t, rfl⟩ := exists_form_mod4_three h
    rw [map_mod4_three]
    omega

lemma map_inv_64 : A006368_inv 64 = 85 := by
  decide

lemma map_eq_64_iff (n : ℕ) : A006368_map n = 64 ↔ n = 85 := by
  constructor
  · intro h
    have hinv := leftInverse_inv_map n
    rw [h, map_inv_64] at hinv
    exact hinv.symm
  · intro h
    subst h
    decide

lemma iterate_succ_eq_64 {k n : ℕ} :
    A006368_map^[k + 1] n = 64 ↔ A006368_map^[k] n = 85 := by
  rw [iterate_succ_apply']
  exact map_eq_64_iff _

/-- `3n ≤ 4 f(n) + 1` on every branch (equality for type B). -/
lemma three_n_le_four_map_add_one (n : ℕ) :
    3 * n ≤ 4 * A006368_map n + 1 := by
  rcases even_or_mod4 n with h | h | h
  · obtain ⟨t, rfl⟩ := exists_form_even h
    rw [map_even]; omega
  · obtain ⟨t, rfl⟩ := exists_form_mod4_one h
    rw [map_mod4_one]; omega
  · obtain ⟨t, rfl⟩ := exists_form_mod4_three h
    rw [map_mod4_three]; omega

lemma map_add_one_mul_four_ge_three_mul_add_one (n : ℕ) :
    3 * (n + 1) ≤ 4 * (A006368_map n + 1) := by
  have h := three_n_le_four_map_add_one n
  omega

/-- Iterating the contraction `3(n+1) ≤ 4(f(n)+1)`. -/
lemma iterate_add_one_pow_bound (n k : ℕ) :
    3 ^ k * (n + 1) ≤ 4 ^ k * (A006368_map^[k] n + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := map_add_one_mul_four_ge_three_mul_add_one (A006368_map^[k] n)
    have hstep : A006368_map^[k + 1] n = A006368_map (A006368_map^[k] n) :=
      Function.iterate_succ_apply' _ _ _
    calc
      3 ^ (k + 1) * (n + 1) = 3 * (3 ^ k * (n + 1)) := by ring
      _ ≤ 3 * (4 ^ k * (A006368_map^[k] n + 1)) := Nat.mul_le_mul_left 3 ih
      _ = 4 ^ k * (3 * (A006368_map^[k] n + 1)) := by ring
      _ ≤ 4 ^ k * (4 * (A006368_map (A006368_map^[k] n) + 1)) :=
        Nat.mul_le_mul_left _ h
      _ = 4 ^ (k + 1) * (A006368_map^[k + 1] n + 1) := by
        rw [hstep]; ring

lemma iterate_ne_of_pow_bound {n k t : ℕ}
    (h : 4 ^ k * (t + 1) < 3 ^ k * (n + 1)) :
    A006368_map^[k] n ≠ t := by
  intro heq
  have hb := iterate_add_one_pow_bound n k
  rw [heq] at hb
  exact Nat.lt_le_asymm h hb

/-! ### 64 is not a periodic point -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

lemma iterate_ne_self_lt_500 :
    ∀ k : Fin 500, k.val = 0 ∨ A006368_map^[k.val] 64 ≠ 64 := by
  decide

def n500 : ℕ := 100756188284683804

lemma iterate_500 : A006368_map^[500] 64 = n500 := by
  decide

lemma iterate_ne_64_from_n500_lt_500 :
    ∀ k : Fin 500, A006368_map^[k.val] n500 ≠ 64 := by
  decide

def n1000 : ℕ := 9897427377833507869287616648508

lemma iterate_500_n500 : A006368_map^[500] n500 = n1000 := by
  decide

lemma iterate_ne_64_from_n1000_lt_500 :
    ∀ k : Fin 500, A006368_map^[k.val] n1000 ≠ 64 := by
  decide

def n1500 : ℕ := 972238731607309791707528316402630798010576061

lemma iterate_500_n1000 : A006368_map^[500] n1000 = n1500 := by
  decide

lemma iterate_ne_64_from_n1500_lt_500 :
    ∀ k : Fin 500, A006368_map^[k.val] n1500 ≠ 64 := by
  decide

def n2000 : ℕ := 5829127752430806247362907722615747557776916296290128345

lemma iterate_500_n1500 : A006368_map^[500] n1500 = n2000 := by
  decide

lemma iterate_ne_64_from_n2000_lt_500 :
    ∀ k : Fin 500, A006368_map^[k.val] n2000 ≠ 64 := by
  decide

def n2500 : ℕ := 8532460388259319857058279610438977677132552973427297201924294

lemma iterate_500_n2000 : A006368_map^[500] n2000 = n2500 := by
  decide

lemma iterate_ne_64_from_n2500_lt_500 :
    ∀ k : Fin 500, A006368_map^[k.val] n2500 ≠ 64 := by
  decide

def n3000 : ℕ := 818511750725977544531118036524537753650345203035149276356373847548612644

lemma iterate_500_n2500 : A006368_map^[500] n2500 = n3000 := by
  decide

lemma iterate_ne_64_from_n3000_lt_500 :
    ∀ k : Fin 500, A006368_map^[k.val] n3000 ≠ 64 := by
  decide

def n3500 : ℕ := 628153152165462572967761582306521196575781053277736202498240992446872336914813073694

lemma iterate_500_n3000 : A006368_map^[500] n3000 = n3500 := by
  decide

lemma iterate_ne_64_from_n3500_lt_500 :
    ∀ k : Fin 500, A006368_map^[k.val] n3500 ≠ 64 := by
  decide

def n4000 : ℕ := 235383608278701712744229028048507925539414759591396077471566361578588280512972304682439468419

lemma iterate_500_n3500 : A006368_map^[500] n3500 = n4000 := by
  decide

lemma iterate_ne_64_from_n4000_lt_500 :
    ∀ k : Fin 500, A006368_map^[k.val] n4000 ≠ 64 := by
  decide

set_option exponentiation.threshold 1024

/-- All-odd contraction from `n4000` cannot reach 64 in 724 steps. -/
lemma four_pow_724_n4000 : 4 ^ 724 * 65 < 3 ^ 724 * (n4000 + 1) := by
  decide

lemma four_pow_mul_65_lt_of_le_724 {r : ℕ} (hr : r ≤ 724) :
    4 ^ r * 65 < 3 ^ r * (n4000 + 1) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hr
  have h3 : 3 ^ d ≤ 4 ^ d := Nat.pow_le_pow_left (by decide : 3 ≤ 4) d
  have hle : 4 ^ r * 65 * 3 ^ d ≤ 4 ^ (r + d) * 65 := by
    calc
      4 ^ r * 65 * 3 ^ d ≤ 4 ^ r * 65 * 4 ^ d := Nat.mul_le_mul_left _ h3
      _ = 4 ^ r * 4 ^ d * 65 := by ring
      _ = 4 ^ (r + d) * 65 := by rw [← Nat.pow_add]
  have hlt : 4 ^ r * 65 * 3 ^ d < 3 ^ (r + d) * (n4000 + 1) := by
    rw [← hd]
    exact lt_of_le_of_lt hle (by
      simpa [hd] using four_pow_724_n4000)
  rw [Nat.pow_add] at hlt
  have : 4 ^ r * 65 * 3 ^ d < 3 ^ r * (n4000 + 1) * 3 ^ d := by
    convert hlt using 1
    ring
  exact Nat.lt_of_mul_lt_mul_right this

lemma iterate_ne_64_from_n4000_le_724 {r : ℕ} (hr : r ≤ 724) :
    A006368_map^[r] n4000 ≠ 64 :=
  iterate_ne_of_pow_bound (four_pow_mul_65_lt_of_le_724 hr)

/-- Helper: peel one 500-step block. -/
lemma iterate_peel_500 {k n n' : ℕ} (hkn : 500 ≤ k)
    (hiter : A006368_map^[500] n = n') :
    ∃ m, k = 500 + m ∧ A006368_map^[k] n = A006368_map^[m] n' := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hkn
  refine ⟨m, hm, ?_⟩
  rw [hm, Nat.add_comm, iterate_add_apply, hiter]

/-! ### Inverse iterates and equivalence -/

lemma iterate_leftInverse (k : ℕ) : LeftInverse (A006368_inv^[k]) (A006368_map^[k]) :=
  LeftInverse.iterate leftInverse_inv_map k

lemma iterate_rightInverse (k : ℕ) : RightInverse (A006368_inv^[k]) (A006368_map^[k]) :=
  RightInverse.iterate rightInverse_inv_map k

lemma iterate_map_eq_iff_inv {r n m : ℕ} :
    A006368_map^[r] n = m ↔ A006368_inv^[r] m = n := by
  constructor
  · intro h
    rw [← h]
    exact iterate_leftInverse r n
  · intro h
    rw [← h]
    exact iterate_rightInverse r m

lemma map_iterate_eq_64_iff_inv (r : ℕ) (n : ℕ) :
    A006368_map^[r] n = 64 ↔ A006368_inv^[r] 64 = n :=
  iterate_map_eq_iff_inv

-- Inverse checkpoints every 500 steps from 64
def g500 : ℕ := 1608200419608219

lemma inv_500 : A006368_inv^[500] 64 = g500 := by
  decide

lemma inv_ne_n4000_from_64_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] 64 ≠ n4000 := by
  decide

def g1000 : ℕ := 1208006553651669624232

lemma inv_500_g500 : A006368_inv^[500] g500 = g1000 := by
  decide

lemma inv_ne_n4000_from_g500_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g500 ≠ n4000 := by
  decide

def g1500 : ℕ := 29733658197401944922578927860318

lemma inv_500_g1000 : A006368_inv^[500] g1000 = g1500 := by
  decide

lemma inv_ne_n4000_from_g1000_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g1000 ≠ n4000 := by
  decide

def g2000 : ℕ := 5995388666582834742613216667449163456445790227

lemma inv_500_g1500 : A006368_inv^[500] g1500 = g2000 := by
  decide

lemma inv_ne_n4000_from_g1500_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g1500 ≠ n4000 := by
  decide

def g2500 : ℕ := 2417777525035964849011779527115595744163634330861050403512973

lemma inv_500_g2000 : A006368_inv^[500] g2000 = g2500 := by
  decide

lemma inv_ne_n4000_from_g2000_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g2000 ≠ n4000 := by
  decide

def g3000 : ℕ := 15234750837421661775380120607019518573661597545184448405636467754712923039

lemma inv_500_g2500 : A006368_inv^[500] g2500 = g3000 := by
  decide

lemma inv_ne_n4000_from_g2500_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g2500 ≠ n4000 := by
  decide

def g3500 : ℕ := 749970888408106367651134001190546452099919013849025445572425012872708608801763228035

lemma inv_500_g3000 : A006368_inv^[500] g3000 = g3500 := by
  decide

lemma inv_ne_n4000_from_g3000_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g3000 ≠ n4000 := by
  decide

def g4000 : ℕ := 9229824948598154690007799176376246853927307040476805680301052380965272583991043819669501302239

lemma inv_500_g3500 : A006368_inv^[500] g3500 = g4000 := by
  decide

lemma inv_ne_n4000_from_g3500_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g3500 ≠ n4000 := by
  decide

def g4500 : ℕ := 14539601132533836552727603648115183513277223280431402902399582022876601783283596199667871601544460836163462

lemma inv_500_g4000 : A006368_inv^[500] g4000 = g4500 := by
  decide

lemma inv_ne_n4000_from_g4000_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g4000 ≠ n4000 := by
  decide

def g5000 : ℕ := 1465856627326217544269261730272444366205967384891535432516824795288467244968661706047188446929211399015692966072080505629

lemma inv_500_g4500 : A006368_inv^[500] g4500 = g5000 := by
  decide

lemma inv_ne_n4000_from_g4500_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g4500 ≠ n4000 := by
  decide

def g5500 : ℕ := 147785048041529752106322823564924813814647226734684213381980723741475950078844095171771445729944686038985954733127407076946971471585996

lemma inv_500_g5000 : A006368_inv^[500] g5000 = g5500 := by
  decide

lemma inv_ne_n4000_from_g5000_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g5000 ≠ n4000 := by
  decide

def g6000 : ℕ := 7275109711731816000808142742778690852028751368455868193009469161370053746959086458457320021145694317737772326792976724251671839965991677237345342

lemma inv_500_g5500 : A006368_inv^[500] g5500 = g6000 := by
  decide

lemma inv_ne_n4000_from_g5500_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g5500 ≠ n4000 := by
  decide

def g6500 : ℕ := 5595882966842540715194975256175417355563678848894987401013509452221683423451474455434102584215394116865951669189390253822195745713127230107769274186806790

lemma inv_500_g6000 : A006368_inv^[500] g6000 = g6500 := by
  decide

lemma inv_ne_n4000_from_g6000_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g6000 ≠ n4000 := by
  decide

def g7000 : ℕ := 577706936201813993997189300528750825526563109416661208782152716532395896791391742381061935550348329651438517473510096822993939846838383568846110633508534463332211356793593

lemma inv_500_g6500 : A006368_inv^[500] g6500 = g7000 := by
  decide

lemma inv_ne_n4000_from_g6500_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g6500 ≠ n4000 := by
  decide

def g7500 : ℕ := 1863788220025095955255236742463140006203137079761261911096452697691954494940639911015106416339417152539953283730460438902325320619394434625306803124473320266375846409146026205868704186002

lemma inv_500_g7000 : A006368_inv^[500] g7000 = g7500 := by
  decide

lemma inv_ne_n4000_from_g7000_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g7000 ≠ n4000 := by
  decide

def g8000 : ℕ := 24051686496565267223929047827067490483595433911518369298073532126910312062449881495747726618199447406147923145030444551336229542219698856212476509117567732703035745024932164898795885914282371932410993880

lemma inv_500_g7500 : A006368_inv^[500] g7500 = g8000 := by
  decide

lemma inv_ne_n4000_from_g7500_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g7500 ≠ n4000 := by
  decide

def g8500 : ℕ := 2424848090947493762162887066914837691997148305392496656204399145877628211306007090046884953975830839022756303112283590068365618125740069534614914263101821204514367854459963099571332411373898518078797654215498286412335

lemma inv_500_g8000 : A006368_inv^[500] g8000 = g8500 := by
  decide

lemma inv_ne_n4000_from_g8000_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g8000 ≠ n4000 := by
  decide

def g9000 : ℕ := 7639651725944704243531872259954500668867853433963727864334345961712634305501627999390310444375651085360062860744523713961589440500692499858027389749438411260281851113720718076832589090830480336167492488648841631275206055413871774

lemma inv_500_g8500 : A006368_inv^[500] g8500 = g9000 := by
  decide

lemma inv_ne_n4000_from_g8500_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g8500 ≠ n4000 := by
  decide

def g9500 : ℕ := 385108023626663938683250239663887652016272724371879433435734572102109869141074268161825965211068377863089606490203101835645022540490022381905550099818373494621344078211386506330696932742910977499916533684013012598432422645874236221605122063129

lemma inv_500_g9000 : A006368_inv^[500] g9000 = g9500 := by
  decide

lemma inv_ne_n4000_from_g9000_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g9000 ≠ n4000 := by
  decide

def g10000 : ℕ := 75831842527530094034793206554647790117231885150729117452375319904182668302402791345414221365163762403695530559516624689819304618976538517178387282504147108500405414561838729006753700763602392826826103783768215848324072825951766126876129418750540054746278

lemma inv_500_g9500 : A006368_inv^[500] g9500 = g10000 := by
  decide

lemma inv_ne_n4000_from_g9500_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g9500 ≠ n4000 := by
  decide

def g10500 : ℕ := 7645230974225929816345663010025544086671708948346868817002470799005724293612397135509855970809034224972945400823831094962488875436828947079284904213016430940578195835786634045676750060276543567596731286368294454735838035209846969681813519692996906607503426767320699409

lemma inv_500_g10000 : A006368_inv^[500] g10000 = g10500 := by
  decide

lemma inv_ne_n4000_from_g10000_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g10000 ≠ n4000 := by
  decide

def g11000 : ℕ := 94089176892566889281600900590704133319786423984373736062122224833001478270302060452256139469304865716382369491399388885771973394502560898656830336126456478187196653698151792297773874000333245999933743058318059077481691732774498143157400984246155426732208765007882575227142951884

lemma inv_500_g10500 : A006368_inv^[500] g10500 = g11000 := by
  decide

lemma inv_ne_n4000_from_g10500_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g10500 ≠ n4000 := by
  decide

def g11500 : ℕ := 9046461895418195872956072174033666548315038681822813902341989545562402068490358795461202636504722198332326538594600085439417708862235596634715881291511778681905420309390583588712533336367401897773593127190931779425042487111200038603095047017845993700817970825483178677833713298974425269

lemma inv_500_g11000 : A006368_inv^[500] g11000 = g11500 := by
  decide

lemma inv_ne_n4000_from_g11000_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g11000 ≠ n4000 := by
  decide

def g12000 : ℕ := 1867874584238265425160685763478945126644208957021080425366423871968086562113950198493442907323355380157545546607334747245591784351535851338806941527105456611890364750742603423340469836247710590751305085994689608662039292121019205897493987177049693374601669413498182415577408303034346018212220633503326894

lemma inv_500_g11500 : A006368_inv^[500] g11500 = g12000 := by
  decide

lemma inv_ne_n4000_from_g11500_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g11500 ≠ n4000 := by
  decide

def g12500 : ℕ := 2942434073416169227363270142902137668926770975073184989327290125254904417929820326823697672042067800361598024798694738299649042773395368267646572033845448848089714916428598640855020726471141384397427406595867892211228551911515902779516834212304251542776172436313286112355618920480227771625162672744961576803358968969

lemma inv_500_g12000 : A006368_inv^[500] g12000 = g12500 := by
  decide

lemma inv_ne_n4000_from_g12000_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g12000 ≠ n4000 := by
  decide

def g13000 : ℕ := 67450616800210468900669989747122049610810098141130313641341023798245690236218907800914025646611880251892652214527582736630162143391180602870722507464653884535775570175228253430343959902222309903047382625034175472591620476459799131845953426344910759175239384221742034436600477277505147548148413152112096988905425390878

lemma inv_500_g12500 : A006368_inv^[500] g12500 = g13000 := by
  decide

lemma inv_ne_n4000_from_g12500_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g12500 ≠ n4000 := by
  decide

def g13500 : ℕ := 222830616908682198703177992331785324884067662171065165916114696716338585672228060240007733752065170460211021624032385776875058294297231083482009101231622362867930715665592494285500269005075811272894968444012237679055056670993786175348762724757664286272686893829092722500083565642274586613324981715815501118003633677595379339785974649503

lemma inv_500_g13000 : A006368_inv^[500] g13000 = g13500 := by
  decide

lemma inv_ne_n4000_from_g13000_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g13000 ≠ n4000 := by
  decide

def g14000 : ℕ := 22465384957218403271716323906881900308630688058323260919317729644043393756823952024711262509113999680432184514347084224450030820229281645708427629285367706054513299549392239488203040482563912386674929135134751115252922773021926737779499791805912440922544847509330410075762365460558781755495486803775289567418114327108144924903968142350486796935667927

lemma inv_500_g13500 : A006368_inv^[500] g13500 = g14000 := by
  decide

lemma inv_ne_n4000_from_g13500_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g13500 ≠ n4000 := by
  decide

def g14500 : ℕ := 4638556163926348165124563993967944252600378229760846418356405201069885988346382121025280847016845076005406507642733950704709026660411696547338926917124840256403585090210708561671828348058054601244742841152875884435103287403915829174371497327456410345878765617249872048694398983870358191018637108164565558129014399565362531289609585687187831375598405476170727911114263

lemma inv_500_g14000 : A006368_inv^[500] g14000 = g14500 := by
  decide

lemma inv_ne_n4000_from_g14000_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g14000 ≠ n4000 := by
  decide

def g15000 : ℕ := 233825475408050727090770478805431646162250273329855137939640495925762186985728775348776369650999481893304663556516959420792790030653646429042596901517470400826811218208752986781511019447263595054155054708891306872387254476984695975685919581200976346719983648115277443021399282774763411547085378231952398662356314922760863426382544770353973702693820628695351933220108067056218054808

lemma inv_500_g14500 : A006368_inv^[500] g14500 = g15000 := by
  decide

lemma inv_ne_n4000_from_g14500_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g14500 ≠ n4000 := by
  decide

def g15500 : ℕ := 92085417816469941382606582727872709852642677681956892320756635209133654061196925951175540968506691982503802862004194271858238570080007340576219227168542040069274053309267359017584859510067243160334308204800353325288645425322887959664051779333065083236768080272089017799510748103654012093613562100613441044127909784733982562472831017539711000238874521015136503399689362023573446717798848668469

lemma inv_500_g15000 : A006368_inv^[500] g15000 = g15500 := by
  decide

lemma inv_ne_n4000_from_g15000_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g15000 ≠ n4000 := by
  decide

def g16000 : ℕ := 138340702889695635012958600587942605520515543799680732341533370238470742629503038582986274265184217339613175041442378324378536991377442133865268121191812984055646152789853362816888907761327602145322439605966210088249439541020656652690550308284165919360484223674183776430786875268753040767866834822832825788437949431148955997383260830138666121700054965371656698450163234330240187893257831496750723564

lemma inv_500_g15500 : A006368_inv^[500] g15500 = g16000 := by
  decide

lemma inv_ne_n4000_from_g15500_lt_500 :
    ∀ k : Fin 500, A006368_inv^[k.val] g15500 ≠ n4000 := by
  decide

def g16k_500 : ℕ := 6973631336628265434193790553723263848015789168552364419355027541573143604182798653125040667538651432517493957951435315893428912411232270601316879665743655526602481644720784310973439395183471910641454477546162273477805996170505633903031948364363702967623245187203787382566891324365391596362500822614874143688386808014312236504293562463303782670899174078018292523453587869902731343527064249532113634324152440442476

lemma inv_500_g16000 : A006368_inv^[500] g16000 = g16k_500 := by
  decide

/-! LTE for `2^n ± 1` at the prime 3. -/

lemma odd_three : Odd (3 : ℕ) := ⟨1, by decide⟩

lemma padicValNat_three_three : padicValNat 3 3 = 1 :=
  padicValNat.self (by decide : 1 < 3)

lemma two_pow_mod_three_even {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, hk⟩ := hn
  have hn2 : n = 2 * k := by omega
  rw [hn2, pow_mul, pow_mod]
  simp

lemma two_pow_mod_three_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  have h1 : n % 2 = 1 := Nat.odd_iff.mp hn
  have : n = 2 * (n / 2) + 1 := (Nat.div_add_mod n 2).symm.trans (by rw [h1])
  rw [this, pow_succ, pow_mul, Nat.mul_mod, pow_mod]
  simp

lemma padicValNat_two_pow_sub_one_of_even {n : ℕ} (hn : Even n) (h0 : n ≠ 0) :
    padicValNat 3 (2 ^ n - 1) = 1 + padicValNat 3 n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hn
  have hn2 : n = 2 * k := by omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h0 (by omega)
  have hrew : 2 ^ n - 1 = 4 ^ k - 1 ^ k := by
    rw [hn2, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, one_pow]
  rw [hrew]
  have h :=
    padicValNat.pow_sub_pow (p := 3) (hp1 := odd_three) (x := 4) (y := 1)
      (by decide : (1 : ℕ) < 4) (by decide : 3 ∣ 4 - 1) (by decide : ¬ 3 ∣ 4) hk0
  have hv4 : padicValNat 3 (4 - 1) = 1 := padicValNat_three_three
  have hvk : padicValNat 3 k = padicValNat 3 n := by
    rw [hn2, padicValNat.mul (by decide : 2 ≠ 0) hk0]
    have : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
    omega
  rw [h, hv4, hvk]

lemma padicValNat_two_pow_sub_one_of_odd {n : ℕ} (hn : Odd n) :
    padicValNat 3 (2 ^ n - 1) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro h
  have hmod : (2 ^ n - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
  have hpow : 2 ^ n % 3 = 2 := two_pow_mod_three_odd hn
  have hdecomp : 2 ^ n = 3 * (2 ^ n / 3) + 2 := by
    have := Nat.div_add_mod (2 ^ n) 3
    omega
  have hsub : 2 ^ n - 1 = 3 * (2 ^ n / 3) + 1 := by omega
  have : (2 ^ n - 1) % 3 = 1 := by
    rw [hsub, Nat.add_mod, Nat.mul_mod]
    simp
  omega

lemma padicValNat_two_pow_add_one_of_odd {n : ℕ} (hn : Odd n) :
    padicValNat 3 (2 ^ n + 1) = 1 + padicValNat 3 n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h :=
    padicValNat.pow_add_pow (p := 3) (hp1 := odd_three) (x := 2) (y := 1)
      (by decide : 3 ∣ 2 + 1) (by decide : ¬ 3 ∣ 2) hn
  have hv : padicValNat 3 (2 + 1) = 1 := padicValNat_three_three
  have : (1 : ℕ) ^ n = 1 := one_pow n
  rw [this] at h
  rw [h, hv]

lemma padicValNat_two_pow_add_one_of_even {n : ℕ} (hn : Even n) :
    padicValNat 3 (2 ^ n + 1) = 0 := by
  refine padicValNat.eq_zero_of_not_dvd ?_
  have hpow : 2 ^ n % 3 = 1 := two_pow_mod_three_even hn
  have hmod : (2 ^ n + 1) % 3 = 2 := by
    calc (2 ^ n + 1) % 3 = (2 ^ n % 3 + 1 % 3) % 3 := Nat.add_mod _ _ _
      _ = (1 + 1) % 3 := by rw [hpow]
      _ = 2 := by decide
  exact fun h => by
    have : (2 ^ n + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    omega

lemma padicValNat_two_pow_sub_one_le (n : ℕ) :
    padicValNat 3 (2 ^ n - 1) ≤ 1 + padicValNat 3 n := by
  by_cases h0 : n = 0
  · subst h0; simp
  · by_cases hen : Even n
    · rw [padicValNat_two_pow_sub_one_of_even hen h0]
    · have hodd : Odd n := not_even_iff_odd.mp hen
      rw [padicValNat_two_pow_sub_one_of_odd hodd]; omega

lemma padicValNat_two_pow_add_one_le (n : ℕ) :
    padicValNat 3 (2 ^ n + 1) ≤ 1 + padicValNat 3 n := by
  by_cases hen : Even n
  · rw [padicValNat_two_pow_add_one_of_even hen]; omega
  · have hodd : Odd n := not_even_iff_odd.mp hen
    rw [padicValNat_two_pow_add_one_of_odd hodd]

lemma inv_ne_n4000_of_lt_16000 {r : ℕ} (hr : r < 16000) :
    A006368_inv^[r] 64 ≠ n4000 := by
  by_cases h0 : r < 500
  · exact inv_ne_n4000_from_64_lt_500 ⟨r, h0⟩
  · have hr0 : 500 ≤ r := Nat.le_of_not_lt h0
    obtain ⟨t1, ht1⟩ := Nat.exists_eq_add_of_le hr0
    have hs1 : A006368_inv^[r] 64 = A006368_inv^[t1] g500 := by
      rw [ht1, Nat.add_comm, iterate_add_apply, inv_500]
    have sum1 : r = 500 + t1 := ht1
    rw [hs1]
    by_cases h1 : t1 < 500
    · exact inv_ne_n4000_from_g500_lt_500 ⟨t1, h1⟩
    · have hr1 : 500 ≤ t1 := Nat.le_of_not_lt h1
      obtain ⟨t2, ht2⟩ := Nat.exists_eq_add_of_le hr1
      have hs2 : A006368_inv^[t1] g500 = A006368_inv^[t2] g1000 := by
        rw [ht2, Nat.add_comm, iterate_add_apply, inv_500_g500]
      have sum2 : r = 1000 + t2 := by
        rw [sum1, ht2]; ring
      rw [hs2]
      by_cases h2 : t2 < 500
      · exact inv_ne_n4000_from_g1000_lt_500 ⟨t2, h2⟩
      · have hr2 : 500 ≤ t2 := Nat.le_of_not_lt h2
        obtain ⟨t3, ht3⟩ := Nat.exists_eq_add_of_le hr2
        have hs3 : A006368_inv^[t2] g1000 = A006368_inv^[t3] g1500 := by
          rw [ht3, Nat.add_comm, iterate_add_apply, inv_500_g1000]
        have sum3 : r = 1500 + t3 := by
          rw [sum2, ht3]; ring
        rw [hs3]
        by_cases h3 : t3 < 500
        · exact inv_ne_n4000_from_g1500_lt_500 ⟨t3, h3⟩
        · have hr3 : 500 ≤ t3 := Nat.le_of_not_lt h3
          obtain ⟨t4, ht4⟩ := Nat.exists_eq_add_of_le hr3
          have hs4 : A006368_inv^[t3] g1500 = A006368_inv^[t4] g2000 := by
            rw [ht4, Nat.add_comm, iterate_add_apply, inv_500_g1500]
          have sum4 : r = 2000 + t4 := by
            rw [sum3, ht4]; ring
          rw [hs4]
          by_cases h4 : t4 < 500
          · exact inv_ne_n4000_from_g2000_lt_500 ⟨t4, h4⟩
          · have hr4 : 500 ≤ t4 := Nat.le_of_not_lt h4
            obtain ⟨t5, ht5⟩ := Nat.exists_eq_add_of_le hr4
            have hs5 : A006368_inv^[t4] g2000 = A006368_inv^[t5] g2500 := by
              rw [ht5, Nat.add_comm, iterate_add_apply, inv_500_g2000]
            have sum5 : r = 2500 + t5 := by
              rw [sum4, ht5]; ring
            rw [hs5]
            by_cases h5 : t5 < 500
            · exact inv_ne_n4000_from_g2500_lt_500 ⟨t5, h5⟩
            · have hr5 : 500 ≤ t5 := Nat.le_of_not_lt h5
              obtain ⟨t6, ht6⟩ := Nat.exists_eq_add_of_le hr5
              have hs6 : A006368_inv^[t5] g2500 = A006368_inv^[t6] g3000 := by
                rw [ht6, Nat.add_comm, iterate_add_apply, inv_500_g2500]
              have sum6 : r = 3000 + t6 := by
                rw [sum5, ht6]; ring
              rw [hs6]
              by_cases h6 : t6 < 500
              · exact inv_ne_n4000_from_g3000_lt_500 ⟨t6, h6⟩
              · have hr6 : 500 ≤ t6 := Nat.le_of_not_lt h6
                obtain ⟨t7, ht7⟩ := Nat.exists_eq_add_of_le hr6
                have hs7 : A006368_inv^[t6] g3000 = A006368_inv^[t7] g3500 := by
                  rw [ht7, Nat.add_comm, iterate_add_apply, inv_500_g3000]
                have sum7 : r = 3500 + t7 := by
                  rw [sum6, ht7]; ring
                rw [hs7]
                by_cases h7 : t7 < 500
                · exact inv_ne_n4000_from_g3500_lt_500 ⟨t7, h7⟩
                · have hr7 : 500 ≤ t7 := Nat.le_of_not_lt h7
                  obtain ⟨t8, ht8⟩ := Nat.exists_eq_add_of_le hr7
                  have hs8 : A006368_inv^[t7] g3500 = A006368_inv^[t8] g4000 := by
                    rw [ht8, Nat.add_comm, iterate_add_apply, inv_500_g3500]
                  have sum8 : r = 4000 + t8 := by
                    rw [sum7, ht8]; ring
                  rw [hs8]
                  by_cases h8 : t8 < 500
                  · exact inv_ne_n4000_from_g4000_lt_500 ⟨t8, h8⟩
                  · have hr8 : 500 ≤ t8 := Nat.le_of_not_lt h8
                    obtain ⟨t9, ht9⟩ := Nat.exists_eq_add_of_le hr8
                    have hs9 : A006368_inv^[t8] g4000 = A006368_inv^[t9] g4500 := by
                      rw [ht9, Nat.add_comm, iterate_add_apply, inv_500_g4000]
                    have sum9 : r = 4500 + t9 := by
                      rw [sum8, ht9]; ring
                    rw [hs9]
                    by_cases h9 : t9 < 500
                    · exact inv_ne_n4000_from_g4500_lt_500 ⟨t9, h9⟩
                    · have hr9 : 500 ≤ t9 := Nat.le_of_not_lt h9
                      obtain ⟨t10, ht10⟩ := Nat.exists_eq_add_of_le hr9
                      have hs10 : A006368_inv^[t9] g4500 = A006368_inv^[t10] g5000 := by
                        rw [ht10, Nat.add_comm, iterate_add_apply, inv_500_g4500]
                      have sum10 : r = 5000 + t10 := by
                        rw [sum9, ht10]; ring
                      rw [hs10]
                      by_cases h10 : t10 < 500
                      · exact inv_ne_n4000_from_g5000_lt_500 ⟨t10, h10⟩
                      · have hr10 : 500 ≤ t10 := Nat.le_of_not_lt h10
                        obtain ⟨t11, ht11⟩ := Nat.exists_eq_add_of_le hr10
                        have hs11 : A006368_inv^[t10] g5000 = A006368_inv^[t11] g5500 := by
                          rw [ht11, Nat.add_comm, iterate_add_apply, inv_500_g5000]
                        have sum11 : r = 5500 + t11 := by
                          rw [sum10, ht11]; ring
                        rw [hs11]
                        by_cases h11 : t11 < 500
                        · exact inv_ne_n4000_from_g5500_lt_500 ⟨t11, h11⟩
                        · have hr11 : 500 ≤ t11 := Nat.le_of_not_lt h11
                          obtain ⟨t12, ht12⟩ := Nat.exists_eq_add_of_le hr11
                          have hs12 : A006368_inv^[t11] g5500 = A006368_inv^[t12] g6000 := by
                            rw [ht12, Nat.add_comm, iterate_add_apply, inv_500_g5500]
                          have sum12 : r = 6000 + t12 := by
                            rw [sum11, ht12]; ring
                          rw [hs12]
                          by_cases h12 : t12 < 500
                          · exact inv_ne_n4000_from_g6000_lt_500 ⟨t12, h12⟩
                          · have hr12 : 500 ≤ t12 := Nat.le_of_not_lt h12
                            obtain ⟨t13, ht13⟩ := Nat.exists_eq_add_of_le hr12
                            have hs13 : A006368_inv^[t12] g6000 = A006368_inv^[t13] g6500 := by
                              rw [ht13, Nat.add_comm, iterate_add_apply, inv_500_g6000]
                            have sum13 : r = 6500 + t13 := by
                              rw [sum12, ht13]; ring
                            rw [hs13]
                            by_cases h13 : t13 < 500
                            · exact inv_ne_n4000_from_g6500_lt_500 ⟨t13, h13⟩
                            · have hr13 : 500 ≤ t13 := Nat.le_of_not_lt h13
                              obtain ⟨t14, ht14⟩ := Nat.exists_eq_add_of_le hr13
                              have hs14 : A006368_inv^[t13] g6500 = A006368_inv^[t14] g7000 := by
                                rw [ht14, Nat.add_comm, iterate_add_apply, inv_500_g6500]
                              have sum14 : r = 7000 + t14 := by
                                rw [sum13, ht14]; ring
                              rw [hs14]
                              by_cases h14 : t14 < 500
                              · exact inv_ne_n4000_from_g7000_lt_500 ⟨t14, h14⟩
                              · have hr14 : 500 ≤ t14 := Nat.le_of_not_lt h14
                                obtain ⟨t15, ht15⟩ := Nat.exists_eq_add_of_le hr14
                                have hs15 : A006368_inv^[t14] g7000 = A006368_inv^[t15] g7500 := by
                                  rw [ht15, Nat.add_comm, iterate_add_apply, inv_500_g7000]
                                have sum15 : r = 7500 + t15 := by
                                  rw [sum14, ht15]; ring
                                rw [hs15]
                                by_cases h15 : t15 < 500
                                · exact inv_ne_n4000_from_g7500_lt_500 ⟨t15, h15⟩
                                · have hr15 : 500 ≤ t15 := Nat.le_of_not_lt h15
                                  obtain ⟨t16, ht16⟩ := Nat.exists_eq_add_of_le hr15
                                  have hs16 : A006368_inv^[t15] g7500 = A006368_inv^[t16] g8000 := by
                                    rw [ht16, Nat.add_comm, iterate_add_apply, inv_500_g7500]
                                  have sum16 : r = 8000 + t16 := by
                                    rw [sum15, ht16]; ring
                                  rw [hs16]
                                  by_cases h16 : t16 < 500
                                  · exact inv_ne_n4000_from_g8000_lt_500 ⟨t16, h16⟩
                                  · have hr16 : 500 ≤ t16 := Nat.le_of_not_lt h16
                                    obtain ⟨t17, ht17⟩ := Nat.exists_eq_add_of_le hr16
                                    have hs17 : A006368_inv^[t16] g8000 = A006368_inv^[t17] g8500 := by
                                      rw [ht17, Nat.add_comm, iterate_add_apply, inv_500_g8000]
                                    have sum17 : r = 8500 + t17 := by
                                      rw [sum16, ht17]; ring
                                    rw [hs17]
                                    by_cases h17 : t17 < 500
                                    · exact inv_ne_n4000_from_g8500_lt_500 ⟨t17, h17⟩
                                    · have hr17 : 500 ≤ t17 := Nat.le_of_not_lt h17
                                      obtain ⟨t18, ht18⟩ := Nat.exists_eq_add_of_le hr17
                                      have hs18 : A006368_inv^[t17] g8500 = A006368_inv^[t18] g9000 := by
                                        rw [ht18, Nat.add_comm, iterate_add_apply, inv_500_g8500]
                                      have sum18 : r = 9000 + t18 := by
                                        rw [sum17, ht18]; ring
                                      rw [hs18]
                                      by_cases h18 : t18 < 500
                                      · exact inv_ne_n4000_from_g9000_lt_500 ⟨t18, h18⟩
                                      · have hr18 : 500 ≤ t18 := Nat.le_of_not_lt h18
                                        obtain ⟨t19, ht19⟩ := Nat.exists_eq_add_of_le hr18
                                        have hs19 : A006368_inv^[t18] g9000 = A006368_inv^[t19] g9500 := by
                                          rw [ht19, Nat.add_comm, iterate_add_apply, inv_500_g9000]
                                        have sum19 : r = 9500 + t19 := by
                                          rw [sum18, ht19]; ring
                                        rw [hs19]
                                        by_cases h19 : t19 < 500
                                        · exact inv_ne_n4000_from_g9500_lt_500 ⟨t19, h19⟩
                                        · have hr19 : 500 ≤ t19 := Nat.le_of_not_lt h19
                                          obtain ⟨t20, ht20⟩ := Nat.exists_eq_add_of_le hr19
                                          have hs20 : A006368_inv^[t19] g9500 = A006368_inv^[t20] g10000 := by
                                            rw [ht20, Nat.add_comm, iterate_add_apply, inv_500_g9500]
                                          have sum20 : r = 10000 + t20 := by
                                            rw [sum19, ht20]; ring
                                          rw [hs20]
                                          by_cases h20 : t20 < 500
                                          · exact inv_ne_n4000_from_g10000_lt_500 ⟨t20, h20⟩
                                          · have hr20 : 500 ≤ t20 := Nat.le_of_not_lt h20
                                            obtain ⟨t21, ht21⟩ := Nat.exists_eq_add_of_le hr20
                                            have hs21 : A006368_inv^[t20] g10000 = A006368_inv^[t21] g10500 := by
                                              rw [ht21, Nat.add_comm, iterate_add_apply, inv_500_g10000]
                                            have sum21 : r = 10500 + t21 := by
                                              rw [sum20, ht21]; ring
                                            rw [hs21]
                                            by_cases h21 : t21 < 500
                                            · exact inv_ne_n4000_from_g10500_lt_500 ⟨t21, h21⟩
                                            · have hr21 : 500 ≤ t21 := Nat.le_of_not_lt h21
                                              obtain ⟨t22, ht22⟩ := Nat.exists_eq_add_of_le hr21
                                              have hs22 : A006368_inv^[t21] g10500 = A006368_inv^[t22] g11000 := by
                                                rw [ht22, Nat.add_comm, iterate_add_apply, inv_500_g10500]
                                              have sum22 : r = 11000 + t22 := by
                                                rw [sum21, ht22]; ring
                                              rw [hs22]
                                              by_cases h22 : t22 < 500
                                              · exact inv_ne_n4000_from_g11000_lt_500 ⟨t22, h22⟩
                                              · have hr22 : 500 ≤ t22 := Nat.le_of_not_lt h22
                                                obtain ⟨t23, ht23⟩ := Nat.exists_eq_add_of_le hr22
                                                have hs23 : A006368_inv^[t22] g11000 = A006368_inv^[t23] g11500 := by
                                                  rw [ht23, Nat.add_comm, iterate_add_apply, inv_500_g11000]
                                                have sum23 : r = 11500 + t23 := by
                                                  rw [sum22, ht23]; ring
                                                rw [hs23]
                                                by_cases h23 : t23 < 500
                                                · exact inv_ne_n4000_from_g11500_lt_500 ⟨t23, h23⟩
                                                · have hr23 : 500 ≤ t23 := Nat.le_of_not_lt h23
                                                  obtain ⟨t24, ht24⟩ := Nat.exists_eq_add_of_le hr23
                                                  have hs24 : A006368_inv^[t23] g11500 = A006368_inv^[t24] g12000 := by
                                                    rw [ht24, Nat.add_comm, iterate_add_apply, inv_500_g11500]
                                                  have sum24 : r = 12000 + t24 := by
                                                    rw [sum23, ht24]; ring
                                                  rw [hs24]
                                                  by_cases h24 : t24 < 500
                                                  · exact inv_ne_n4000_from_g12000_lt_500 ⟨t24, h24⟩
                                                  · have hr24 : 500 ≤ t24 := Nat.le_of_not_lt h24
                                                    obtain ⟨t25, ht25⟩ := Nat.exists_eq_add_of_le hr24
                                                    have hs25 : A006368_inv^[t24] g12000 = A006368_inv^[t25] g12500 := by
                                                      rw [ht25, Nat.add_comm, iterate_add_apply, inv_500_g12000]
                                                    have sum25 : r = 12500 + t25 := by
                                                      rw [sum24, ht25]; ring
                                                    rw [hs25]
                                                    by_cases h25 : t25 < 500
                                                    · exact inv_ne_n4000_from_g12500_lt_500 ⟨t25, h25⟩
                                                    · have hr25 : 500 ≤ t25 := Nat.le_of_not_lt h25
                                                      obtain ⟨t26, ht26⟩ := Nat.exists_eq_add_of_le hr25
                                                      have hs26 : A006368_inv^[t25] g12500 = A006368_inv^[t26] g13000 := by
                                                        rw [ht26, Nat.add_comm, iterate_add_apply, inv_500_g12500]
                                                      have sum26 : r = 13000 + t26 := by
                                                        rw [sum25, ht26]; ring
                                                      rw [hs26]
                                                      by_cases h26 : t26 < 500
                                                      · exact inv_ne_n4000_from_g13000_lt_500 ⟨t26, h26⟩
                                                      · have hr26 : 500 ≤ t26 := Nat.le_of_not_lt h26
                                                        obtain ⟨t27, ht27⟩ := Nat.exists_eq_add_of_le hr26
                                                        have hs27 : A006368_inv^[t26] g13000 = A006368_inv^[t27] g13500 := by
                                                          rw [ht27, Nat.add_comm, iterate_add_apply, inv_500_g13000]
                                                        have sum27 : r = 13500 + t27 := by
                                                          rw [sum26, ht27]; ring
                                                        rw [hs27]
                                                        by_cases h27 : t27 < 500
                                                        · exact inv_ne_n4000_from_g13500_lt_500 ⟨t27, h27⟩
                                                        · have hr27 : 500 ≤ t27 := Nat.le_of_not_lt h27
                                                          obtain ⟨t28, ht28⟩ := Nat.exists_eq_add_of_le hr27
                                                          have hs28 : A006368_inv^[t27] g13500 = A006368_inv^[t28] g14000 := by
                                                            rw [ht28, Nat.add_comm, iterate_add_apply, inv_500_g13500]
                                                          have sum28 : r = 14000 + t28 := by
                                                            rw [sum27, ht28]; ring
                                                          rw [hs28]
                                                          by_cases h28 : t28 < 500
                                                          · exact inv_ne_n4000_from_g14000_lt_500 ⟨t28, h28⟩
                                                          · have hr28 : 500 ≤ t28 := Nat.le_of_not_lt h28
                                                            obtain ⟨t29, ht29⟩ := Nat.exists_eq_add_of_le hr28
                                                            have hs29 : A006368_inv^[t28] g14000 = A006368_inv^[t29] g14500 := by
                                                              rw [ht29, Nat.add_comm, iterate_add_apply, inv_500_g14000]
                                                            have sum29 : r = 14500 + t29 := by
                                                              rw [sum28, ht29]; ring
                                                            rw [hs29]
                                                            by_cases h29 : t29 < 500
                                                            · exact inv_ne_n4000_from_g14500_lt_500 ⟨t29, h29⟩
                                                            · have hr29 : 500 ≤ t29 := Nat.le_of_not_lt h29
                                                              obtain ⟨t30, ht30⟩ := Nat.exists_eq_add_of_le hr29
                                                              have hs30 : A006368_inv^[t29] g14500 = A006368_inv^[t30] g15000 := by
                                                                rw [ht30, Nat.add_comm, iterate_add_apply, inv_500_g14500]
                                                              have sum30 : r = 15000 + t30 := by
                                                                rw [sum29, ht30]; ring
                                                              rw [hs30]
                                                              by_cases h30 : t30 < 500
                                                              · exact inv_ne_n4000_from_g15000_lt_500 ⟨t30, h30⟩
                                                              · have hr30 : 500 ≤ t30 := Nat.le_of_not_lt h30
                                                                obtain ⟨t31, ht31⟩ := Nat.exists_eq_add_of_le hr30
                                                                have hs31 : A006368_inv^[t30] g15000 = A006368_inv^[t31] g15500 := by
                                                                  rw [ht31, Nat.add_comm, iterate_add_apply, inv_500_g15000]
                                                                have sum31 : r = 15500 + t31 := by
                                                                  rw [sum30, ht31]; ring
                                                                rw [hs31]
                                                                by_cases h31 : t31 < 500
                                                                · exact inv_ne_n4000_from_g15500_lt_500 ⟨t31, h31⟩
                                                                · have hge : 500 ≤ t31 := Nat.le_of_not_lt h31
                                                                  have : r ≥ 16000 := by
                                                                    have := sum31
                                                                    omega
                                                                  exact (Nat.lt_le_asymm hr this).elim

lemma inv_16000 : A006368_inv^[16000] 64 = g16000 := by
  calc
    A006368_inv^[16000] 64
        = A006368_inv^[15500] (A006368_inv^[500] 64) := by
            rw [show 16000 = 15500 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[15500] g500 := by rw [inv_500]
    _ = A006368_inv^[15000] (A006368_inv^[500] g500) := by
            rw [show 15500 = 15000 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[15000] g1000 := by rw [inv_500_g500]
    _ = A006368_inv^[14500] (A006368_inv^[500] g1000) := by
            rw [show 15000 = 14500 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[14500] g1500 := by rw [inv_500_g1000]
    _ = A006368_inv^[14000] (A006368_inv^[500] g1500) := by
            rw [show 14500 = 14000 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[14000] g2000 := by rw [inv_500_g1500]
    _ = A006368_inv^[13500] (A006368_inv^[500] g2000) := by
            rw [show 14000 = 13500 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[13500] g2500 := by rw [inv_500_g2000]
    _ = A006368_inv^[13000] (A006368_inv^[500] g2500) := by
            rw [show 13500 = 13000 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[13000] g3000 := by rw [inv_500_g2500]
    _ = A006368_inv^[12500] (A006368_inv^[500] g3000) := by
            rw [show 13000 = 12500 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[12500] g3500 := by rw [inv_500_g3000]
    _ = A006368_inv^[12000] (A006368_inv^[500] g3500) := by
            rw [show 12500 = 12000 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[12000] g4000 := by rw [inv_500_g3500]
    _ = A006368_inv^[11500] (A006368_inv^[500] g4000) := by
            rw [show 12000 = 11500 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[11500] g4500 := by rw [inv_500_g4000]
    _ = A006368_inv^[11000] (A006368_inv^[500] g4500) := by
            rw [show 11500 = 11000 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[11000] g5000 := by rw [inv_500_g4500]
    _ = A006368_inv^[10500] (A006368_inv^[500] g5000) := by
            rw [show 11000 = 10500 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[10500] g5500 := by rw [inv_500_g5000]
    _ = A006368_inv^[10000] (A006368_inv^[500] g5500) := by
            rw [show 10500 = 10000 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[10000] g6000 := by rw [inv_500_g5500]
    _ = A006368_inv^[9500] (A006368_inv^[500] g6000) := by
            rw [show 10000 = 9500 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[9500] g6500 := by rw [inv_500_g6000]
    _ = A006368_inv^[9000] (A006368_inv^[500] g6500) := by
            rw [show 9500 = 9000 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[9000] g7000 := by rw [inv_500_g6500]
    _ = A006368_inv^[8500] (A006368_inv^[500] g7000) := by
            rw [show 9000 = 8500 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[8500] g7500 := by rw [inv_500_g7000]
    _ = A006368_inv^[8000] (A006368_inv^[500] g7500) := by
            rw [show 8500 = 8000 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[8000] g8000 := by rw [inv_500_g7500]
    _ = A006368_inv^[7500] (A006368_inv^[500] g8000) := by
            rw [show 8000 = 7500 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[7500] g8500 := by rw [inv_500_g8000]
    _ = A006368_inv^[7000] (A006368_inv^[500] g8500) := by
            rw [show 7500 = 7000 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[7000] g9000 := by rw [inv_500_g8500]
    _ = A006368_inv^[6500] (A006368_inv^[500] g9000) := by
            rw [show 7000 = 6500 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[6500] g9500 := by rw [inv_500_g9000]
    _ = A006368_inv^[6000] (A006368_inv^[500] g9500) := by
            rw [show 6500 = 6000 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[6000] g10000 := by rw [inv_500_g9500]
    _ = A006368_inv^[5500] (A006368_inv^[500] g10000) := by
            rw [show 6000 = 5500 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[5500] g10500 := by rw [inv_500_g10000]
    _ = A006368_inv^[5000] (A006368_inv^[500] g10500) := by
            rw [show 5500 = 5000 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[5000] g11000 := by rw [inv_500_g10500]
    _ = A006368_inv^[4500] (A006368_inv^[500] g11000) := by
            rw [show 5000 = 4500 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[4500] g11500 := by rw [inv_500_g11000]
    _ = A006368_inv^[4000] (A006368_inv^[500] g11500) := by
            rw [show 4500 = 4000 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[4000] g12000 := by rw [inv_500_g11500]
    _ = A006368_inv^[3500] (A006368_inv^[500] g12000) := by
            rw [show 4000 = 3500 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[3500] g12500 := by rw [inv_500_g12000]
    _ = A006368_inv^[3000] (A006368_inv^[500] g12500) := by
            rw [show 3500 = 3000 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[3000] g13000 := by rw [inv_500_g12500]
    _ = A006368_inv^[2500] (A006368_inv^[500] g13000) := by
            rw [show 3000 = 2500 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[2500] g13500 := by rw [inv_500_g13000]
    _ = A006368_inv^[2000] (A006368_inv^[500] g13500) := by
            rw [show 2500 = 2000 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[2000] g14000 := by rw [inv_500_g13500]
    _ = A006368_inv^[1500] (A006368_inv^[500] g14000) := by
            rw [show 2000 = 1500 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[1500] g14500 := by rw [inv_500_g14000]
    _ = A006368_inv^[1000] (A006368_inv^[500] g14500) := by
            rw [show 1500 = 1000 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[1000] g15000 := by rw [inv_500_g14500]
    _ = A006368_inv^[500] (A006368_inv^[500] g15000) := by
            rw [show 1000 = 500 + 500 from rfl, iterate_add_apply]
    _ = A006368_inv^[500] g15500 := by rw [inv_500_g15000]
    _ = A006368_inv^[500] g15500 := by
            rfl
    _ = g16000 := inv_500_g15500


lemma g16000_ne_n4000 : g16000 ≠ n4000 := by
  decide

/-- `g(n) ≥ 2n/3` on every branch. -/
lemma inv_mul_three_ge_two (n : ℕ) : 2 * n ≤ 3 * A006368_inv n := by
  rcases mod3_cases n with h | h | h
  · obtain ⟨t, rfl⟩ := exists_form_mod3_zero h
    rw [inv_mod3_zero]; omega
  · obtain ⟨t, rfl⟩ := exists_form_mod3_one h
    rw [inv_mod3_one]; omega
  · obtain ⟨t, rfl⟩ := exists_form_mod3_two h
    rw [inv_mod3_two]; omega

lemma iterate_inv_mul_pow (n k : ℕ) :
    2 ^ k * n ≤ 3 ^ k * (A006368_inv^[k] n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := inv_mul_three_ge_two (A006368_inv^[k] n)
    have hstep : A006368_inv^[k + 1] n = A006368_inv (A006368_inv^[k] n) :=
      Function.iterate_succ_apply' _ _ _
    calc
      2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by ring
      _ ≤ 2 * (3 ^ k * (A006368_inv^[k] n)) := Nat.mul_le_mul_left 2 ih
      _ = 3 ^ k * (2 * A006368_inv^[k] n) := by ring
      _ ≤ 3 ^ k * (3 * A006368_inv (A006368_inv^[k] n)) :=
        Nat.mul_le_mul_left _ h
      _ = 3 ^ (k + 1) * (A006368_inv^[k + 1] n) := by
        rw [hstep]; ring

lemma iterate_inv_ne_of_pow {n k t : ℕ}
    (h : 3 ^ k * t < 2 ^ k * n) :
    A006368_inv^[k] n ≠ t := by
  intro heq
  have hb := iterate_inv_mul_pow n k
  rw [heq] at hb
  exact Nat.lt_le_asymm h hb

set_option exponentiation.threshold 8192

lemma pow_bound_1736 : n4000 * 3 ^ 1736 < g16000 * 2 ^ 1736 := by
  decide

lemma pow_bound_of_le_1736 {s : ℕ} (hs : s ≤ 1736) :
    n4000 * 3 ^ s < g16000 * 2 ^ s := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hs
  have h2 : 2 ^ d ≤ 3 ^ d := Nat.pow_le_pow_left (by decide : 2 ≤ 3) d
  have hle : n4000 * 3 ^ s * 2 ^ d ≤ n4000 * 3 ^ (s + d) := by
    calc
      n4000 * 3 ^ s * 2 ^ d ≤ n4000 * 3 ^ s * 3 ^ d := Nat.mul_le_mul_left _ h2
      _ = n4000 * (3 ^ s * 3 ^ d) := by ring
      _ = n4000 * 3 ^ (s + d) := by rw [← Nat.pow_add]
  have hlt : n4000 * 3 ^ s * 2 ^ d < g16000 * 2 ^ (s + d) := by
    rw [← hd]
    exact lt_of_le_of_lt hle (by simpa [hd] using pow_bound_1736)
  rw [Nat.pow_add] at hlt
  have : n4000 * 3 ^ s * 2 ^ d < g16000 * 2 ^ s * 2 ^ d := by
    convert hlt using 1
    ring
  exact Nat.lt_of_mul_lt_mul_right this

lemma inv_orbit_g16000_ne_n4000_le_1736 {s : ℕ} (hs : s ≤ 1736) :
    A006368_inv^[s] g16000 ≠ n4000 :=
  iterate_inv_ne_of_pow (by
    have := pow_bound_of_le_1736 hs
    convert this using 1 <;> ring)

lemma pow_bound_g16k_500 : n4000 * 3 ^ 1814 < g16k_500 * 2 ^ 1814 := by
  decide

lemma pow_bound_g16k_500_of_le {u : ℕ} (hu : u ≤ 1814) :
    n4000 * 3 ^ u < g16k_500 * 2 ^ u := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hu
  have h2 : 2 ^ d ≤ 3 ^ d := Nat.pow_le_pow_left (by decide : 2 ≤ 3) d
  have hle : n4000 * 3 ^ u * 2 ^ d ≤ n4000 * 3 ^ (u + d) := by
    calc
      n4000 * 3 ^ u * 2 ^ d ≤ n4000 * 3 ^ u * 3 ^ d := Nat.mul_le_mul_left _ h2
      _ = n4000 * (3 ^ u * 3 ^ d) := by ring
      _ = n4000 * 3 ^ (u + d) := by rw [← Nat.pow_add]
  have hlt : n4000 * 3 ^ u * 2 ^ d < g16k_500 * 2 ^ (u + d) := by
    rw [← hd]
    exact lt_of_le_of_lt hle (by simpa [hd] using pow_bound_g16k_500)
  rw [Nat.pow_add] at hlt
  have : n4000 * 3 ^ u * 2 ^ d < g16k_500 * 2 ^ u * 2 ^ d := by
    convert hlt using 1
    ring
  exact Nat.lt_of_mul_lt_mul_right this

lemma inv_gt_n4000_from_g16k_500 {u : ℕ} (hu : u ≤ 1814) :
    n4000 < A006368_inv^[u] g16k_500 := by
  have hb := iterate_inv_mul_pow g16k_500 u
  have hpow := pow_bound_g16k_500_of_le hu
  have hle : n4000 * 3 ^ u < 3 ^ u * A006368_inv^[u] g16k_500 :=
    lt_of_lt_of_le hpow (by convert hb using 1 <;> ring)
  have hle' : 3 ^ u * n4000 < 3 ^ u * A006368_inv^[u] g16k_500 := by
    convert hle using 1 <;> ring
  exact Nat.lt_of_mul_lt_mul_left hle'

/-! Gersonides: |2^a - 3^b| = 1. -/

lemma two_pow_mod_eight_of_three_le {a : ℕ} (ha : 3 ≤ a) : 2 ^ a % 8 = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le ha
  subst hk
  rw [pow_add, show (2 : ℕ) ^ 3 = 8 from rfl, Nat.mul_mod_right]

lemma three_pow_mod_eight (b : ℕ) : 3 ^ b % 8 = 1 ∨ 3 ^ b % 8 = 3 := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> simp [h]

lemma three_pow_eq_three {b : ℕ} (h : 3 ^ b = 3) : b = 1 := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 3)
  simpa using h

lemma three_pow_eq_one {b : ℕ} (h : 3 ^ b = 1) : b = 0 := by
  cases b with
  | zero => rfl
  | succ b =>
    rw [pow_succ] at h
    have : 3 * 3 ^ b ≥ 3 := by
      have : 1 ≤ 3 ^ b := Nat.one_le_pow b 3 (by decide)
      omega
    omega

lemma two_pow_eq_three_pow_add_one {a b : ℕ} (h : 2 ^ a = 3 ^ b + 1) :
    a = 1 ∧ b = 0 ∨ a = 2 ∧ b = 1 := by
  match a with
  | 0 =>
    have h0 : (2 : ℕ) ^ 0 = 1 := rfl
    rw [h0] at h
    have : 3 ^ b = 0 := by omega
    have : 0 < 3 ^ b := Nat.pow_pos (by decide : 0 < 3)
    omega
  | 1 =>
    have : 3 ^ b = 1 := by
      change 2 = 3 ^ b + 1 at h
      omega
    exact Or.inl ⟨rfl, three_pow_eq_one this⟩
  | 2 =>
    have : 3 ^ b = 3 := by
      change 4 = 3 ^ b + 1 at h
      omega
    exact Or.inr ⟨rfl, three_pow_eq_three this⟩
  | a + 3 =>
    have h8 : 2 ^ (a + 3) % 8 = 0 := two_pow_mod_eight_of_three_le (by omega)
    have hrhs : (3 ^ b + 1) % 8 ≠ 0 := by
      rcases three_pow_mod_eight b with hb | hb
      · rw [Nat.add_mod, hb]; decide
      · rw [Nat.add_mod, hb]; decide
    have : (3 ^ b + 1) % 8 = 0 := by rw [← h, h8]
    exact (hrhs this).elim

lemma two_pow_eq_two {a : ℕ} (h : 2 ^ a = 2) : a = 1 := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  simpa using h

lemma two_pow_eq_eight {a : ℕ} (h : 2 ^ a = 8) : a = 3 := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  simpa using h

lemma three_pow_mod_four_of_odd {b : ℕ} (hb : Odd b) : 3 ^ b % 4 = 3 := by
  have hb1 : b % 2 = 1 := odd_iff.mp hb
  have hdecomp : b = 2 * (b / 2) + 1 := (div_add_mod b 2).symm.trans (by rw [hb1])
  rw [hdecomp, pow_succ, pow_mul, Nat.mul_mod, pow_mod]
  have h9 : (3 : ℕ) ^ 2 % 4 = 1 := by decide
  rw [h9]
  simp

lemma two_pow_mod_four_of_ge_two {a : ℕ} (ha : 2 ≤ a) : 2 ^ a % 4 = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le ha
  subst hk
  rw [pow_add, show (2 : ℕ) ^ 2 = 4 from rfl, Nat.mul_mod_right]

lemma two_pow_eq_of_mod_four_two {a : ℕ} (h : 2 ^ a % 4 = 2) : a = 1 := by
  match a with
  | 0 =>
    have : (2 : ℕ) ^ 0 % 4 = 1 := by decide
    omega
  | 1 => rfl
  | a + 2 =>
    have : 2 ^ (a + 2) % 4 = 0 := two_pow_mod_four_of_ge_two (by omega)
    omega

lemma three_pow_even_factor (c : ℕ) :
    3 ^ (2 * c) - 1 = (3 ^ c - 1) * (3 ^ c + 1) := by
  have hsq : 3 ^ (2 * c) = (3 ^ c) ^ 2 := by
    rw [show 2 * c = c * 2 from Nat.mul_comm _ _, pow_mul]
  rw [hsq]
  have := Nat.sq_sub_sq (3 ^ c) 1
  simpa [Nat.mul_comm] using this

lemma three_pow_eq_two_pow_add_one {a b : ℕ} (h : 3 ^ b = 2 ^ a + 1) :
    b = 1 ∧ a = 1 ∨ b = 2 ∧ a = 3 := by
  match b with
  | 0 =>
    have h0 : (3 : ℕ) ^ 0 = 1 := rfl
    rw [h0] at h
    have : 0 < 2 ^ a := Nat.pow_pos (by decide : 0 < 2)
    omega
  | 1 =>
    have : 2 ^ a = 2 := by
      change 3 = 2 ^ a + 1 at h
      omega
    exact Or.inl ⟨rfl, two_pow_eq_two this⟩
  | 2 =>
    have : 2 ^ a = 8 := by
      change 9 = 2 ^ a + 1 at h
      omega
    exact Or.inr ⟨rfl, two_pow_eq_eight this⟩
  | b + 3 =>
    have hsub : 3 ^ (b + 3) - 1 = 2 ^ a := by
      have : 1 ≤ 3 ^ (b + 3) := Nat.one_le_pow (b + 3) 3 (by decide)
      omega
    by_cases he : Even (b + 3)
    · obtain ⟨c, hc⟩ := he
      have hc2 : b + 3 = 2 * c := by omega
      have hcpos : 2 ≤ c := by omega
      have hfac : (3 ^ c - 1) * (3 ^ c + 1) = 2 ^ a := by
        rw [← three_pow_even_factor c, ← hc2, hsub]
      have dvd1 : 3 ^ c - 1 ∣ 2 ^ a := ⟨3 ^ c + 1, hfac.symm⟩
      have dvd2 : 3 ^ c + 1 ∣ 2 ^ a := ⟨3 ^ c - 1, by rw [Nat.mul_comm]; exact hfac.symm⟩
      obtain ⟨x, -, hx⟩ := (dvd_prime_pow prime_two).mp dvd1
      obtain ⟨y, -, hy⟩ := (dvd_prime_pow prime_two).mp dvd2
      have hge : 1 ≤ 3 ^ c := Nat.one_le_pow c 3 (by decide)
      have hdiff : 2 ^ y = 2 ^ x + 2 := by
        have : 3 ^ c + 1 = 3 ^ c - 1 + 2 := by omega
        rw [hx, hy] at this
        exact this
      have hxy : x < y := by
        have : 3 ^ c - 1 < 3 ^ c + 1 := by omega
        rw [hx, hy] at this
        exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp this
      have hxle : x ≤ 1 := by
        have hmul : 2 ^ x * 2 ^ (y - x) = 2 ^ y := by
          rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hxy)]
        have hfac2 : 2 ^ x * (2 ^ (y - x) - 1) = 2 := by
          calc
            2 ^ x * (2 ^ (y - x) - 1)
                = 2 ^ x * 2 ^ (y - x) - 2 ^ x * 1 := Nat.mul_sub_left_distrib _ _ _
            _ = 2 ^ y - 2 ^ x := by rw [hmul, mul_one]
            _ = 2 := by omega
        have : 2 ^ x ∣ 2 := ⟨2 ^ (y - x) - 1, hfac2.symm⟩
        exact (pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp this
      interval_cases x
      · -- x = 0: 3^c - 1 = 1
        have hx0 : 3 ^ c - 1 = 1 := by
          rw [hx, pow_zero]
        have : 3 ^ c = 2 := by omega
        have : 3 ≤ 3 ^ c := Nat.le_self_pow (by omega : c ≠ 0) 3
        omega
      · -- x = 1: 3^c - 1 = 2
        have hx1 : 3 ^ c - 1 = 2 := by
          rw [hx]; rfl
        have : 3 ^ c = 3 := by omega
        have : c = 1 := three_pow_eq_three this
        omega
    · have hodd : Odd (b + 3) := not_even_iff_odd.mp he
      have hmod : 3 ^ (b + 3) % 4 = 3 := three_pow_mod_four_of_odd hodd
      have h2mod : (3 ^ (b + 3) - 1) % 4 = 2 := by
        have : 1 ≤ 3 ^ (b + 3) := Nat.one_le_pow (b + 3) 3 (by decide)
        omega
      have : 2 ^ a % 4 = 2 := by rwa [← hsub]
      have ha1 : a = 1 := two_pow_eq_of_mod_four_two this
      subst ha1
      have : 3 ^ (b + 3) = 3 := by omega
      have : 27 ≤ 3 ^ (b + 3) := by
        have hpow : 3 ^ 3 ≤ 3 ^ (b + 3) :=
          Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 3 ≤ b + 3)
        simpa using hpow
      omega

lemma g16000_mod3 : g16000 % 3 = 2 := by decide

lemma g16000_inv_mul : 3 * A006368_inv g16000 = 4 * g16000 + 1 := by
  obtain ⟨t, ht⟩ := exists_form_mod3_two g16000_mod3
  rw [ht, inv_mod3_two]
  ring

lemma iterate_inv_succ (n k : ℕ) :
    A006368_inv^[k + 1] n = A006368_inv^[k] (A006368_inv n) :=
  iterate_succ_apply _ _ _

lemma first_grow_bound (s : ℕ) (hs : 0 < s) :
    (4 * g16000 + 1) * 2 ^ (s - 1) ≤ 3 ^ s * A006368_inv^[s] g16000 := by
  have hss : s = (s - 1) + 1 := by omega
  rw [hss, iterate_inv_succ]
  have hb := iterate_inv_mul_pow (A006368_inv g16000) (s - 1)
  have hmul := g16000_inv_mul
  calc
    (4 * g16000 + 1) * 2 ^ (s - 1)
        = 3 * A006368_inv g16000 * 2 ^ (s - 1) := by rw [hmul]
    _ = 3 * (2 ^ (s - 1) * A006368_inv g16000) := by ring
    _ ≤ 3 * (3 ^ (s - 1) * A006368_inv^[s - 1] (A006368_inv g16000)) :=
      Nat.mul_le_mul_left _ hb
    _ = 3 ^ ((s - 1) + 1) * A006368_inv^[s - 1] (A006368_inv g16000) := by
      rw [pow_succ]; ring

lemma first_grow_1737 :
    n4000 * 3 ^ 1737 < (4 * g16000 + 1) * 2 ^ 1736 := by
  decide

lemma first_grow_1738 :
    n4000 * 3 ^ 1738 < (4 * g16000 + 1) * 2 ^ 1737 := by
  decide

lemma inv_ne_of_first_grow {s t : ℕ} (hs : 0 < s)
    (hbound : t * 3 ^ s < (4 * g16000 + 1) * 2 ^ (s - 1)) :
    A006368_inv^[s] g16000 ≠ t := by
  intro heq
  have hb := first_grow_bound s hs
  rw [heq] at hb
  have hb' : (4 * g16000 + 1) * 2 ^ (s - 1) ≤ t * 3 ^ s := by
    convert hb using 1
    ring
  exact Nat.lt_le_asymm hbound hb'

lemma g16000_gt_n4000 : n4000 < g16000 := by decide

lemma inv_gt_n4000_of_le_1736 {s : ℕ} (hs : s ≤ 1736) :
    n4000 < A006368_inv^[s] g16000 := by
  have hb := iterate_inv_mul_pow g16000 s
  have hpow := pow_bound_of_le_1736 hs
  have hle : n4000 * 3 ^ s < 3 ^ s * A006368_inv^[s] g16000 :=
    lt_of_lt_of_le hpow (by convert hb using 1 <;> ring)
  have hle' : 3 ^ s * n4000 < 3 ^ s * A006368_inv^[s] g16000 := by
    convert hle using 1 <;> ring
  exact Nat.lt_of_mul_lt_mul_left hle'

lemma inv_gt_n4000_of_first_grow {s : ℕ} (hs : 0 < s)
    (hbound : n4000 * 3 ^ s < (4 * g16000 + 1) * 2 ^ (s - 1)) :
    n4000 < A006368_inv^[s] g16000 := by
  have hb := first_grow_bound s hs
  have hle : n4000 * 3 ^ s < 3 ^ s * A006368_inv^[s] g16000 :=
    lt_of_lt_of_le hbound (by convert hb using 1 <;> ring)
  have hle' : 3 ^ s * n4000 < 3 ^ s * A006368_inv^[s] g16000 := by
    convert hle using 1 <;> ring
  exact Nat.lt_of_mul_lt_mul_left hle'

lemma two_pow_332_gt_n4000 : n4000 < 2 ^ 332 := by decide

lemma three_halves_n4000_lt_two_pow_332 : 3 * n4000 < 2 * 2 ^ 332 := by decide

/-- 3-free kernel. -/
def ker3 (n : ℕ) : ℕ := n / 3 ^ padicValNat 3 n

lemma ker3_mul (n : ℕ) : n = 3 ^ padicValNat 3 n * ker3 n := by
  unfold ker3
  rw [Nat.mul_comm]
  exact (Nat.div_mul_cancel pow_padicValNat_dvd).symm

lemma ker3_le_self (n : ℕ) : ker3 n ≤ n :=
  Nat.div_le_self _ _

lemma g16000_v3 : padicValNat 3 g16000 = 0 :=
  padicValNat.eq_zero_of_not_dvd (fun h => by
    have : g16000 % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    have : g16000 % 3 = 2 := g16000_mod3
    omega)

lemma ker3_g16000 : ker3 g16000 = g16000 := by
  unfold ker3; rw [g16000_v3, pow_zero, Nat.div_one]

lemma g16k_500_mod3 : g16k_500 % 3 = 2 := by decide

lemma g16k_500_inv_mul : 3 * A006368_inv g16k_500 = 4 * g16k_500 + 1 := by
  obtain ⟨t, ht⟩ := exists_form_mod3_two g16k_500_mod3
  rw [ht, inv_mod3_two]
  ring

lemma first_grow_g16k_500 (u : ℕ) (hu : 0 < u) :
    (4 * g16k_500 + 1) * 2 ^ (u - 1) ≤ 3 ^ u * A006368_inv^[u] g16k_500 := by
  have hss : u = (u - 1) + 1 := by omega
  rw [hss, iterate_inv_succ]
  have hb := iterate_inv_mul_pow (A006368_inv g16k_500) (u - 1)
  have hmul := g16k_500_inv_mul
  calc
    (4 * g16k_500 + 1) * 2 ^ (u - 1)
        = 3 * A006368_inv g16k_500 * 2 ^ (u - 1) := by rw [hmul]
    _ = 3 * (2 ^ (u - 1) * A006368_inv g16k_500) := by ring
    _ ≤ 3 * (3 ^ (u - 1) * A006368_inv^[u - 1] (A006368_inv g16k_500)) :=
      Nat.mul_le_mul_left _ hb
    _ = 3 ^ ((u - 1) + 1) * A006368_inv^[u - 1] (A006368_inv g16k_500) := by
      rw [pow_succ]; ring

lemma first_grow_three_halves_1814 :
    3 * n4000 * 3 ^ 1814 < 2 * (4 * g16k_500 + 1) * 2 ^ 1813 := by
  decide

lemma inv_gt_three_halves_2314 :
    3 * n4000 < 2 * A006368_inv^[2314] g16000 := by
  have hde : A006368_inv^[2314] g16000 = A006368_inv^[1814] g16k_500 := by
    rw [show 2314 = 1814 + 500 from rfl, Nat.add_comm, iterate_add_apply, inv_500_g16000]
  rw [hde]
  have hb := first_grow_g16k_500 1814 (by decide)
  have hnum := first_grow_three_halves_1814
  have hle : 3 * n4000 * 3 ^ 1814 < 2 * 3 ^ 1814 * A006368_inv^[1814] g16k_500 := by
    have : 2 * (4 * g16k_500 + 1) * 2 ^ 1813 ≤ 2 * 3 ^ 1814 * A006368_inv^[1814] g16k_500 := by
      have := Nat.mul_le_mul_left 2 hb
      convert this using 1 <;> ring
    exact lt_of_lt_of_le hnum this
  have : 3 ^ 1814 * (3 * n4000) < 3 ^ 1814 * (2 * A006368_inv^[1814] g16k_500) := by
    convert hle using 1 <;> ring
  exact Nat.lt_of_mul_lt_mul_left this

instance fact_prime_three : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

lemma inv_gt_n4000_of_le_2314 {s : ℕ} (hs : s ≤ 2314) :
    n4000 < A006368_inv^[s] g16000 := by
  by_cases h500 : s ≤ 500
  · exact inv_gt_n4000_of_le_1736 (by omega)
  · obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le h500)
    have : A006368_inv^[s] g16000 = A006368_inv^[u] g16k_500 := by
      rw [hu, Nat.add_comm, iterate_add_apply, inv_500_g16000]
    rw [this]
    exact inv_gt_n4000_from_g16k_500 (by omega)

lemma padicValNat_two_three : padicValNat 3 2 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by decide)

lemma ker3_not_dvd {n : ℕ} (hn : n ≠ 0) : ¬ 3 ∣ ker3 n := by
  intro h
  have hv : 3 ^ (padicValNat 3 n + 1) ∣ n := by
    rw [pow_succ, ker3_mul n]
    exact Nat.mul_dvd_mul_left _ h
  have : padicValNat 3 n + 1 ≤ padicValNat 3 n :=
    (padicValNat_dvd_iff_le (p := 3) hn).mp hv
  omega

lemma ker3_two_mul {t : ℕ} (ht : t ≠ 0) :
    padicValNat 3 (2 * t) = padicValNat 3 t ∧ ker3 (2 * t) = 2 * ker3 t := by
  have hmul := padicValNat.mul (p := 3) (by decide : (2 : ℕ) ≠ 0) ht
  have hv : padicValNat 3 (2 * t) = padicValNat 3 t := by
    rw [hmul, padicValNat_two_three, zero_add]
  refine ⟨hv, ?_⟩
  unfold ker3
  rw [hv, Nat.mul_div_assoc _ pow_padicValNat_dvd]

def psi (n : ℕ) : ℕ := 2 ^ padicValNat 3 n * ker3 n

lemma psi_le_n (n : ℕ) : psi n ≤ n := by
  have h2 : 2 ^ padicValNat 3 n ≤ 3 ^ padicValNat 3 n :=
    Nat.pow_le_pow_left (by decide : 2 ≤ 3) _
  have heq : psi n * 3 ^ padicValNat 3 n = n * 2 ^ padicValNat 3 n := by
    unfold psi
    rw [ker3_mul n]
    ring
  have hpos : 0 < 3 ^ padicValNat 3 n := Nat.pow_pos (by decide) _
  have : psi n * 3 ^ padicValNat 3 n ≤ n * 3 ^ padicValNat 3 n := by
    rw [heq]
    exact Nat.mul_le_mul_left n h2
  exact Nat.le_of_mul_le_mul_right this hpos

lemma padicValNat_three_mul {t : ℕ} (ht : t ≠ 0) :
    padicValNat 3 (3 * t) = padicValNat 3 t + 1 := by
  rw [padicValNat.mul (by decide : (3 : ℕ) ≠ 0) ht, padicValNat_three_three, add_comm]

lemma ker3_three_mul {t : ℕ} (ht : t ≠ 0) : ker3 (3 * t) = ker3 t := by
  unfold ker3
  rw [padicValNat_three_mul ht, pow_succ, Nat.mul_comm (3 : ℕ), Nat.mul_assoc,
    Nat.mul_div_mul_left _ _ (by decide : 0 < 3)]

lemma psi_inv_mod0 {n : ℕ} (h : n % 3 = 0) (hn : n ≠ 0) :
    psi (A006368_inv n) = psi n := by
  obtain ⟨t, ht⟩ := exists_form_mod3_zero h
  have ht0 : t ≠ 0 := by
    intro hz; subst hz; exact hn (by simp [ht])
  rw [ht, inv_mod3_zero]
  have h2 := ker3_two_mul ht0
  unfold psi
  rw [h2.1, h2.2, padicValNat_three_mul ht0, ker3_three_mul ht0, pow_succ]
  ring

lemma inv_three_mul_of_mod1 {n : ℕ} (h : n % 3 = 1) :
    3 * A006368_inv n + 1 = 4 * n := by
  obtain ⟨t, ht⟩ := exists_form_mod3_one h
  rw [ht, inv_mod3_one]; ring

lemma inv_three_mul_of_mod2 {n : ℕ} (h : n % 3 = 2) :
    3 * A006368_inv n = 4 * n + 1 := by
  obtain ⟨t, ht⟩ := exists_form_mod3_two h
  rw [ht, inv_mod3_two]; ring

lemma inv_grow_gt {n : ℕ} (h : n % 3 ≠ 0) (hn : 0 < n) :
    n < A006368_inv n := by
  rcases mod3_cases n with h0 | h1 | h2
  · exact (h h0).elim
  · obtain ⟨t, ht⟩ := exists_form_mod3_one h1
    rw [ht, inv_mod3_one]; omega
  · obtain ⟨t, ht⟩ := exists_form_mod3_two h2
    rw [ht, inv_mod3_two]; omega

lemma v3_zero_of_not_mod0 {n : ℕ} (h : n % 3 ≠ 0) : padicValNat 3 n = 0 :=
  padicValNat.eq_zero_of_not_dvd (fun hd => h (Nat.mod_eq_zero_of_dvd hd))

lemma psi_eq_self_of_not_mod0 {n : ℕ} (h : n % 3 ≠ 0) : psi n = n := by
  unfold psi ker3
  rw [v3_zero_of_not_mod0 h, pow_zero, Nat.div_one, one_mul]

lemma inv_ne_zero {n : ℕ} (hn : 0 < n) : A006368_inv n ≠ 0 := by
  rcases mod3_cases n with h0 | h1 | h2
  · obtain ⟨t, ht⟩ := exists_form_mod3_zero h0
    rw [ht, inv_mod3_zero]; omega
  · obtain ⟨t, ht⟩ := exists_form_mod3_one h1
    rw [ht, inv_mod3_one]; omega
  · obtain ⟨t, ht⟩ := exists_form_mod3_two h2
    rw [ht, inv_mod3_two]; omega

lemma four_n_sub_eq {n : ℕ} (h : n % 3 = 1) (hn : 0 < n) :
    4 * n - 1 = 3 * A006368_inv n := by
  have := inv_three_mul_of_mod1 h
  have : 1 ≤ 4 * n := by omega
  omega

lemma v3_four_n_sub {n : ℕ} (h : n % 3 = 1) (hn : 0 < n) :
    padicValNat 3 (4 * n - 1) = padicValNat 3 (A006368_inv n) + 1 := by
  rw [four_n_sub_eq h hn, padicValNat_three_mul (inv_ne_zero hn)]

lemma v3_four_n_add {n : ℕ} (h : n % 3 = 2) :
    padicValNat 3 (4 * n + 1) = padicValNat 3 (A006368_inv n) + 1 := by
  rw [inv_three_mul_of_mod2 h]
  have hne : A006368_inv n ≠ 0 := by
    obtain ⟨t, ht⟩ := exists_form_mod3_two h
    rw [ht, inv_mod3_two]; omega
  exact padicValNat_three_mul hne

lemma psi_grow_mod1 {n : ℕ} (h : n % 3 = 1) (hn : 0 < n) :
    psi (A006368_inv n) * 3 ^ padicValNat 3 (4 * n - 1) =
      (4 * n - 1) * 2 ^ padicValNat 3 (A006368_inv n) := by
  have hv := v3_four_n_sub h hn
  have h4 := four_n_sub_eq h hn
  unfold psi
  rw [hv]
  have hker : ker3 (A006368_inv n) * 3 ^ padicValNat 3 (A006368_inv n) =
      A006368_inv n := (ker3_mul _).symm
  have : (4 * n - 1) = 3 * A006368_inv n := h4
  calc
    2 ^ padicValNat 3 (A006368_inv n) * ker3 (A006368_inv n) *
        3 ^ (padicValNat 3 (A006368_inv n) + 1)
        = 2 ^ padicValNat 3 (A006368_inv n) *
            (ker3 (A006368_inv n) * 3 ^ padicValNat 3 (A006368_inv n)) * 3 := by
          rw [pow_succ]; ring
    _ = 2 ^ padicValNat 3 (A006368_inv n) * A006368_inv n * 3 := by
          rw [hker]
    _ = (4 * n - 1) * 2 ^ padicValNat 3 (A006368_inv n) := by
          rw [this]; ring

lemma psi_grow_mod2 {n : ℕ} (h : n % 3 = 2) :
    psi (A006368_inv n) * 3 ^ padicValNat 3 (4 * n + 1) =
      (4 * n + 1) * 2 ^ padicValNat 3 (A006368_inv n) := by
  have hv := v3_four_n_add h
  have h4 := inv_three_mul_of_mod2 h
  unfold psi
  rw [hv]
  have hker : ker3 (A006368_inv n) * 3 ^ padicValNat 3 (A006368_inv n) =
      A006368_inv n := (ker3_mul _).symm
  calc
    2 ^ padicValNat 3 (A006368_inv n) * ker3 (A006368_inv n) *
        3 ^ (padicValNat 3 (A006368_inv n) + 1)
        = 2 ^ padicValNat 3 (A006368_inv n) *
            (ker3 (A006368_inv n) * 3 ^ padicValNat 3 (A006368_inv n)) * 3 := by
          rw [pow_succ]; ring
    _ = 2 ^ padicValNat 3 (A006368_inv n) * A006368_inv n * 3 := by
          rw [hker]
    _ = (4 * n + 1) * 2 ^ padicValNat 3 (A006368_inv n) := by
          rw [← h4]; ring

lemma two_pow_308_gt_three_halves_n4000 : 3 * n4000 < 2 * 2 ^ 308 := by decide

lemma g16000_gt_two_pow_1322 : 2 ^ 1322 < g16000 := by decide

lemma g16000_psi : psi g16000 = g16000 :=
  psi_eq_self_of_not_mod0 (by
    have : g16000 % 3 = 2 := g16000_mod3
    omega)

lemma v3_four_sub_pos {n : ℕ} (h : n % 3 = 1) (hn : 0 < n) :
    1 ≤ padicValNat 3 (4 * n - 1) := by
  have : 3 ∣ (4 * n - 1) := by
    rw [four_n_sub_eq h hn]; exact ⟨_, rfl⟩
  exact one_le_padicValNat_of_dvd (by omega) this

lemma v3_four_add_pos {n : ℕ} (h : n % 3 = 2) :
    1 ≤ padicValNat 3 (4 * n + 1) := by
  have : 3 ∣ (4 * n + 1) := by
    rw [← inv_three_mul_of_mod2 h]; exact ⟨_, rfl⟩
  exact one_le_padicValNat_of_dvd (by
    have := inv_three_mul_of_mod2 h
    have : 1 ≤ 4 * n + 1 := by omega
    omega) this

lemma psi_eq_div_mod1 {n : ℕ} (h : n % 3 = 1) (hn : 0 < n) :
    psi (A006368_inv n) =
      (4 * n - 1) * 2 ^ (padicValNat 3 (4 * n - 1) - 1) /
        3 ^ padicValNat 3 (4 * n - 1) := by
  have hv := v3_four_n_sub h hn
  have hmul := psi_grow_mod1 h hn
  have hpos : 3 ^ padicValNat 3 (4 * n - 1) ≠ 0 :=
    Nat.ne_of_gt (Nat.pow_pos (by decide) _)
  have hv1 : padicValNat 3 (A006368_inv n) = padicValNat 3 (4 * n - 1) - 1 := by
    have : 1 ≤ padicValNat 3 (4 * n - 1) := v3_four_sub_pos h hn
    omega
  rw [hv1] at hmul
  exact Nat.eq_div_of_mul_eq_left hpos hmul.symm

lemma psi_eq_div_mod2 {n : ℕ} (h : n % 3 = 2) :
    psi (A006368_inv n) =
      (4 * n + 1) * 2 ^ (padicValNat 3 (4 * n + 1) - 1) /
        3 ^ padicValNat 3 (4 * n + 1) := by
  have hv := v3_four_n_add h
  have hmul := psi_grow_mod2 h
  have hpos : 3 ^ padicValNat 3 (4 * n + 1) ≠ 0 :=
    Nat.ne_of_gt (Nat.pow_pos (by decide) _)
  have hv1 : padicValNat 3 (A006368_inv n) = padicValNat 3 (4 * n + 1) - 1 := by
    have : 1 ≤ padicValNat 3 (4 * n + 1) := v3_four_add_pos h
    omega
  rw [hv1] at hmul
  exact Nat.eq_div_of_mul_eq_left hpos hmul.symm

lemma inv_gt_n4000_of_gt {n : ℕ} (hn : n4000 < n)
    (hwin : n % 3 = 0 → n4000 < 2 * (n / 3)) :
    n4000 < A006368_inv n := by
  rcases mod3_cases n with h0 | h1 | h2
  · obtain ⟨t, ht⟩ := exists_form_mod3_zero h0
    rw [ht, inv_mod3_zero]
    have : n / 3 = t := by
      rw [ht, Nat.mul_div_right _ (by decide : 0 < 3)]
    have := hwin h0
    simpa [this] using this
  · obtain ⟨t, ht⟩ := exists_form_mod3_one h1
    rw [ht, inv_mod3_one]; omega
  · obtain ⟨t, ht⟩ := exists_form_mod3_two h2
    rw [ht, inv_mod3_two]; omega

lemma three_pow_308_lt_two_pow_491 : 3 ^ 308 < 2 ^ 491 := by decide
lemma three_pow_332_lt_two_pow_527 : 3 ^ 332 < 2 ^ 527 := by decide
lemma three_pow_526_lt_two_pow_835 : 3 ^ 526 < 2 ^ 835 := by decide
lemma three_pow_42_lt_two_pow_67 : 3 ^ 42 < 2 ^ 67 := by decide

lemma psi_ge_pow_of_mul {n v B : ℕ} (hpos : 0 < 3 ^ v)
    (hmul : 2 ^ B * 3 ^ v ≤ n * 2 ^ (v - 1)) :
    2 ^ B ≤ n * 2 ^ (v - 1) / 3 ^ v :=
  Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hmul)

/-- If `n ≥ 2^A` is 3-free and `3^B < 2^{A+1}`, a grow lands `ψ ≥ 2^B`. -/
lemma landing_ge_of_pow {n A B : ℕ} (hn : 2 ^ A ≤ n) (h3 : n % 3 ≠ 0)
    (hpos : 0 < n) (hp : 3 ^ B < 2 ^ (A + 1)) :
    2 ^ B ≤ psi (A006368_inv n) := by
  have hA : 1 ≤ A := by
    have : 1 ≤ 2 ^ A := Nat.one_le_pow A 2 (by decide)
    omega
  rcases mod3_cases n with h0 | h1 | h2
  · exact (h3 h0).elim
  · have hvpos := v3_four_sub_pos h1 hpos
    have hpsi := psi_eq_div_mod1 h1 hpos
    rw [hpsi]
    set v := padicValNat 3 (4 * n - 1)
    have hpos3 : 0 < 3 ^ v := Nat.pow_pos (by decide) _
    by_cases hbigv : B + 1 ≤ v
    · have : 2 ^ B ≤ 2 ^ (v - 1) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      have ht : 1 ≤ (4 * n - 1) / 3 ^ v := by
        have hd := pow_padicValNat_dvd (p := 3) (n := 4 * n - 1)
        have : 3 ^ v ≤ 4 * n - 1 := Nat.le_of_dvd (by omega) hd
        exact Nat.div_pos this hpos3
      have : 2 ^ B ≤ (4 * n - 1) / 3 ^ v * 2 ^ (v - 1) := by
        have := Nat.mul_le_mul ht this
        simpa [Nat.one_mul] using this
      have hdiv : (4 * n - 1) * 2 ^ (v - 1) / 3 ^ v =
          (4 * n - 1) / 3 ^ v * 2 ^ (v - 1) := by
        have : 3 ^ v ∣ (4 * n - 1) := pow_padicValNat_dvd
        rw [Nat.mul_comm (4 * n - 1), Nat.mul_div_assoc _ this, Nat.mul_comm]
      rwa [hdiv]
    · have hvB : v ≤ B := by omega
      have hfloor : 4 * 2 ^ A - 1 ≤ 4 * n - 1 := by omega
      have hmin : 2 ^ B * 3 ^ B ≤ (4 * 2 ^ A - 1) * 2 ^ (B - 1) := by
        have : 2 * 3 ^ B < 2 ^ (A + 2) := by
          have : 3 ^ B < 2 ^ (A + 1) := hp
          have := Nat.mul_lt_mul_of_pos_left this (by decide : 0 < 2)
          convert this using 1
          · ring
          · rw [pow_succ, pow_succ]; ring
        have h1 : 2 * 3 ^ B ≤ 4 * 2 ^ A - 1 := by
          have : 2 * 3 ^ B + 1 ≤ 2 ^ (A + 2) := by omega
          have : 2 ^ (A + 2) = 4 * 2 ^ A := by
            rw [show A + 2 = 2 + A from Nat.add_comm _ _, pow_add, pow_two]; ring
          omega
        have h2 : 2 ^ B = 2 * 2 ^ (B - 1) := by
          have : 1 ≤ B := by
            have : 1 ≤ 3 ^ B := Nat.one_le_pow B 3 (by decide)
            have : 1 < 2 ^ (A + 1) := lt_of_le_of_lt this hp
            omega
          rw [← pow_succ, Nat.sub_add_cancel this]
        calc
          2 ^ B * 3 ^ B = 2 * 2 ^ (B - 1) * 3 ^ B := by rw [h2]
          _ = (2 * 3 ^ B) * 2 ^ (B - 1) := by ring
          _ ≤ (4 * 2 ^ A - 1) * 2 ^ (B - 1) := Nat.mul_le_mul_right _ h1
      have hv2 : 2 ^ (v - 1) ≥ 2 ^ 0 := Nat.one_le_pow _ _ (by decide)
      have : 2 ^ B * 3 ^ v ≤ (4 * n - 1) * 2 ^ (v - 1) := by
        have hvle : 3 ^ v ≤ 3 ^ B := Nat.pow_le_pow_right (by decide : 0 < 3) hvB
        have hleft : 2 ^ B * 3 ^ v ≤ 2 ^ B * 3 ^ B := Nat.mul_le_mul_left _ hvle
        have hpow : 2 ^ (v - 1) ≤ 2 ^ (B - 1) :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
        -- Use min-at-v=B comparison transferred to smaller v (factor 3/2 each step down).
        -- Direct: (4n-1) 2^{v-1} / 3^v ≥ (4*2^A-1) 2^{v-1} / 3^v
        -- and (4*2^A-1) 2^{B-1} / 3^B ≥ 2^B, multiply both by (3/2)^{B-v}≥1.
        have : 2 ^ B * 3 ^ B ≤ (4 * n - 1) * 2 ^ (B - 1) :=
          le_trans hmin (Nat.mul_le_mul_right _ hfloor)
        have hstep : ∀ k, k ≤ B → 2 ^ B * 3 ^ k ≤ (4 * n - 1) * 2 ^ (k - 1 + (1 - 1)) ∨ True :=
          fun _ _ => Or.inr trivial
        -- Compare ratios: 3^{B-v} 2^{v-1} vs 2^{B-1}.
        have hcmp : 3 ^ (B - v) * 2 ^ (v - 1) ≤ 2 ^ (B - 1) * 1 ∨
            2 ^ B * 3 ^ v ≤ (4 * n - 1) * 2 ^ (v - 1) := by
          right
          -- 2^B * 3^v = 2^B * 3^B / 3^{B-v} ≤ (4n-1) 2^{B-1} / 3^{B-v}
          -- Need 2^{B-1} / 3^{B-v} ≤ 2^{v-1}, i.e. 2^{B-v} ≤ 3^{B-v}, true.
          have hge : 2 ^ (B - v) ≤ 3 ^ (B - v) :=
            Nat.pow_le_pow_left (by decide : 2 ≤ 3) _
          have : 2 ^ B * 3 ^ v * 2 ^ (B - v) ≤ (4 * n - 1) * 2 ^ (B - 1) * 3 ^ (B - v) := by
            have := Nat.mul_le_mul ‹2 ^ B * 3 ^ B ≤ (4 * n - 1) * 2 ^ (B - 1)› hge
            convert this using 1
            · have hbv : v + (B - v) = B := Nat.add_sub_cancel' hvB
              rw [← mul_assoc, ← pow_add, hbv]
            · ring
          have hpos2 : 0 < 2 ^ (B - v) := Nat.pow_pos (by decide) _
          have := Nat.le_of_mul_le_mul_right
            (a := 2 ^ B * 3 ^ v) (b := (4 * n - 1) * 2 ^ (v - 1)) (c := 2 ^ (B - v))
            (by
              have : (4 * n - 1) * 2 ^ (v - 1) * 2 ^ (B - v) =
                  (4 * n - 1) * 2 ^ (B - 1) := by
                have : (v - 1) + (B - v) = B - 1 := by omega
                rw [mul_assoc, ← pow_add, this]
              omega)
            hpos2
          exact this
        exact hcmp.resolve_left (fun h => True.elim trivial)
      exact psi_ge_pow_of_mul hpos3 this
  · have hvpos := v3_four_add_pos h2
    have hpsi := psi_eq_div_mod2 h2
    rw [hpsi]
    set v := padicValNat 3 (4 * n + 1)
    have hpos3 : 0 < 3 ^ v := Nat.pow_pos (by decide) _
    by_cases hbigv : B + 1 ≤ v
    · have : 2 ^ B ≤ 2 ^ (v - 1) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      have ht : 1 ≤ (4 * n + 1) / 3 ^ v := by
        have hd := pow_padicValNat_dvd (p := 3) (n := 4 * n + 1)
        have : 3 ^ v ≤ 4 * n + 1 := Nat.le_of_dvd (by omega) hd
        exact Nat.div_pos this hpos3
      have : 2 ^ B ≤ (4 * n + 1) / 3 ^ v * 2 ^ (v - 1) := by
        have := Nat.mul_le_mul ht this
        simpa [Nat.one_mul] using this
      have hdiv : (4 * n + 1) * 2 ^ (v - 1) / 3 ^ v =
          (4 * n + 1) / 3 ^ v * 2 ^ (v - 1) := by
        have : 3 ^ v ∣ (4 * n + 1) := pow_padicValNat_dvd
        rw [Nat.mul_comm (4 * n + 1), Nat.mul_div_assoc _ this, Nat.mul_comm]
      rwa [hdiv]
    · have hvB : v ≤ B := by omega
      have hfloor : 4 * 2 ^ A + 1 ≤ 4 * n + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left 4 hn) 1
      have : 2 ^ B * 3 ^ v ≤ (4 * n + 1) * 2 ^ (v - 1) := by
        have hge : 2 ^ (B - v) ≤ 3 ^ (B - v) :=
          Nat.pow_le_pow_left (by decide : 2 ≤ 3) _
        have hmin : 2 ^ B * 3 ^ B ≤ (4 * 2 ^ A + 1) * 2 ^ (B - 1) := by
          have : 2 * 3 ^ B < 2 ^ (A + 2) := by
            have := Nat.mul_lt_mul_of_pos_left hp (by decide : 0 < 2)
            convert this using 1
            · ring
            · rw [pow_succ, pow_succ]; ring
          have h1 : 2 * 3 ^ B ≤ 4 * 2 ^ A + 1 := by omega
          have h2 : 2 ^ B = 2 * 2 ^ (B - 1) := by
            have : 1 ≤ B := by
              have : 1 ≤ 3 ^ B := Nat.one_le_pow B 3 (by decide)
              have : 1 < 2 ^ (A + 1) := lt_of_le_of_lt this hp
              omega
            rw [← pow_succ, Nat.sub_add_cancel this]
          calc
            2 ^ B * 3 ^ B = (2 * 3 ^ B) * 2 ^ (B - 1) := by rw [h2]; ring
            _ ≤ (4 * 2 ^ A + 1) * 2 ^ (B - 1) := Nat.mul_le_mul_right _ h1
        have : 2 ^ B * 3 ^ B ≤ (4 * n + 1) * 2 ^ (B - 1) :=
          le_trans hmin (Nat.mul_le_mul_right _ hfloor)
        have hpos2 : 0 < 2 ^ (B - v) := Nat.pow_pos (by decide) _
        apply Nat.le_of_mul_le_mul_right (c := 2 ^ (B - v)) _ hpos2
        have hbv : v + (B - v) = B := Nat.add_sub_cancel' hvB
        have : 2 ^ B * 3 ^ v * 2 ^ (B - v) = 2 ^ B * 3 ^ B / 3 ^ (B - v) * 2 ^ (B - v) := by
          have : 3 ^ B = 3 ^ v * 3 ^ (B - v) := by rw [← pow_add, hbv]
          rw [this]; ring
        have hl : 2 ^ B * 3 ^ v * 2 ^ (B - v) = 2 ^ B * 3 ^ B * 2 ^ (B - v) / 3 ^ (B - v) := by
          have : 3 ^ B = 3 ^ v * 3 ^ (B - v) := by rw [← pow_add, hbv]
          rw [this, Nat.mul_comm (3 ^ v), ← Nat.mul_assoc, Nat.mul_assoc (2 ^ B * 3 ^ (B - v)),
            Nat.mul_div_cancel _ (Nat.pow_pos (by decide : 0 < 3) _)]
          ring
        -- Simpler rearrangement
        calc
          2 ^ B * 3 ^ v * 2 ^ (B - v)
              = 2 ^ B * 3 ^ (v + (B - v)) := by rw [← mul_assoc, mul_comm (3 ^ v), ← mul_assoc, ← pow_add]
          _ = 2 ^ B * 3 ^ B := by rw [hbv]
          _ ≤ (4 * n + 1) * 2 ^ (B - 1) := this
          _ = (4 * n + 1) * 2 ^ (v - 1 + (B - v)) := by
                have : (v - 1) + (B - v) = B - 1 := by omega
                rw [this]
          _ = (4 * n + 1) * 2 ^ (v - 1) * 2 ^ (B - v) := by rw [pow_add]; ring
      exact psi_ge_pow_of_mul hpos3 this

lemma landing_ge_526_of_834 {n : ℕ} (hn : 2 ^ 834 ≤ n) (h3 : n % 3 ≠ 0) (hp : 0 < n) :
    2 ^ 526 ≤ psi (A006368_inv n) :=
  landing_ge_of_pow (A := 834) (B := 526) hn h3 hp three_pow_526_lt_two_pow_835

lemma landing_ge_332_of_526 {n : ℕ} (hn : 2 ^ 526 ≤ n) (h3 : n % 3 ≠ 0) (hp : 0 < n) :
    2 ^ 332 ≤ psi (A006368_inv n) :=
  landing_ge_of_pow (A := 526) (B := 332) hn h3 hp three_pow_332_lt_two_pow_527

lemma landing_ge_308_of_490 {n : ℕ} (hn : 2 ^ 490 ≤ n) (h3 : n % 3 ≠ 0) (hp : 0 < n) :
    2 ^ 308 ≤ psi (A006368_inv n) :=
  landing_ge_of_pow (A := 490) (B := 308) hn h3 hp three_pow_308_lt_two_pow_491

lemma landing_ge_308_of_332_vle42 {n : ℕ} (hn : 2 ^ 332 ≤ n) (h3 : n % 3 ≠ 0)
    (hp : 0 < n)
    (hv : (n % 3 = 1 → padicValNat 3 (4 * n - 1) ≤ 42) ∧
          (n % 3 = 2 → padicValNat 3 (4 * n + 1) ≤ 42)) :
    2 ^ 308 ≤ psi (A006368_inv n) := by
  rcases mod3_cases n with h0 | h1 | h2
  · exact (h3 h0).elim
  · have hpsi := psi_eq_div_mod1 h1 hp
    rw [hpsi]
    set v := padicValNat 3 (4 * n - 1)
    have hvle : v ≤ 42 := hv.1 h1
    have hvpos := v3_four_sub_pos h1 hp
    have hpos3 : 0 < 3 ^ v := Nat.pow_pos (by decide) _
    have : 2 ^ 308 * 3 ^ v ≤ (4 * n - 1) * 2 ^ (v - 1) := by
      have hfl : 4 * 2 ^ 332 - 1 ≤ 4 * n - 1 := by omega
      have hv42 : 3 ^ v ≤ 3 ^ 42 := Nat.pow_le_pow_right (by decide : 0 < 3) hvle
      have : 2 ^ 308 * 3 ^ 42 ≤ (4 * 2 ^ 332 - 1) * 2 ^ 41 := by decide
      have h2 : 2 ^ 41 ≤ 2 ^ (v - 1) ∨ v ≤ 42 := Or.inr hvle
      have : 2 ^ 308 * 3 ^ v ≤ (4 * 2 ^ 332 - 1) * 2 ^ 41 :=
        le_trans (Nat.mul_le_mul_left _ hv42) (by decide)
      have hpow : 2 ^ (v - 1) ≥ 1 := Nat.one_le_pow _ _ (by decide)
      -- 2^41 vs 2^{v-1}: v-1 ≤ 41, so 2^{v-1} ≤ 2^41, bound goes the wrong way.
      -- Use min at v=42: transfer downward by 3/2.
      have hbase : 2 ^ 308 * 3 ^ 42 ≤ (4 * n - 1) * 2 ^ 41 :=
        le_trans (by decide : 2 ^ 308 * 3 ^ 42 ≤ (4 * 2 ^ 332 - 1) * 2 ^ 41)
          (Nat.mul_le_mul_right _ hfl)
      have hpos2 : 0 < 2 ^ (42 - v) := Nat.pow_pos (by decide) _
      apply Nat.le_of_mul_le_mul_right (c := 2 ^ (42 - v)) _ hpos2
      have hvadd : v + (42 - v) = 42 := Nat.add_sub_cancel' hvle
      calc
        2 ^ 308 * 3 ^ v * 2 ^ (42 - v)
            = 2 ^ 308 * 3 ^ v * 2 ^ (42 - v) := rfl
        _ ≤ 2 ^ 308 * 3 ^ 42 := by
              have : 2 ^ (42 - v) ≤ 3 ^ (42 - v) :=
                Nat.pow_le_pow_left (by decide : 2 ≤ 3) _
              have := Nat.mul_le_mul_left (2 ^ 308 * 3 ^ v) this
              convert this using 1
              · rfl
              · have : 3 ^ v * 3 ^ (42 - v) = 3 ^ 42 := by rw [← pow_add, hvadd]
                ring_nf
                rw [this]
        _ ≤ (4 * n - 1) * 2 ^ 41 := hbase
        _ = (4 * n - 1) * 2 ^ ((v - 1) + (42 - v)) := by
              have : (v - 1) + (42 - v) = 41 := by omega
              rw [this]
        _ = (4 * n - 1) * 2 ^ (v - 1) * 2 ^ (42 - v) := by rw [pow_add]; ring
    exact psi_ge_pow_of_mul hpos3 this
  · have hpsi := psi_eq_div_mod2 h2
    rw [hpsi]
    set v := padicValNat 3 (4 * n + 1)
    have hvle : v ≤ 42 := hv.2 h2
    have hpos3 : 0 < 3 ^ v := Nat.pow_pos (by decide) _
    have : 2 ^ 308 * 3 ^ v ≤ (4 * n + 1) * 2 ^ (v - 1) := by
      have hfl : 4 * 2 ^ 332 + 1 ≤ 4 * n + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 4 hn) 1
      have hv42 : 3 ^ v ≤ 3 ^ 42 := Nat.pow_le_pow_right (by decide : 0 < 3) hvle
      have hbase : 2 ^ 308 * 3 ^ 42 ≤ (4 * n + 1) * 2 ^ 41 :=
        le_trans (by decide : 2 ^ 308 * 3 ^ 42 ≤ (4 * 2 ^ 332 + 1) * 2 ^ 41)
          (Nat.mul_le_mul_right _ hfl)
      have hpos2 : 0 < 2 ^ (42 - v) := Nat.pow_pos (by decide) _
      apply Nat.le_of_mul_le_mul_right (c := 2 ^ (42 - v)) _ hpos2
      have hvadd : v + (42 - v) = 42 := Nat.add_sub_cancel' hvle
      calc
        2 ^ 308 * 3 ^ v * 2 ^ (42 - v)
            ≤ 2 ^ 308 * 3 ^ 42 := by
              have : 2 ^ (42 - v) ≤ 3 ^ (42 - v) :=
                Nat.pow_le_pow_left (by decide : 2 ≤ 3) _
              have := Nat.mul_le_mul_left (2 ^ 308 * 3 ^ v) this
              convert this using 1
              · have : 3 ^ v * 3 ^ (42 - v) = 3 ^ 42 := by rw [← pow_add, hvadd]
                ring_nf
                rw [this]
        _ ≤ (4 * n + 1) * 2 ^ 41 := hbase
        _ = (4 * n + 1) * 2 ^ ((v - 1) + (42 - v)) := by
              have : (v - 1) + (42 - v) = 41 := by omega
              rw [this]
        _ = (4 * n + 1) * 2 ^ (v - 1) * 2 ^ (42 - v) := by rw [pow_add]; ring
    exact psi_ge_pow_of_mul hpos3 this

lemma padicValNat_le_of_lt_pow {n b : ℕ} (hb : 1 < 3)
    (h : n < 3 ^ b) (hn : n ≠ 0) : padicValNat 3 n < b := by
  by_contra hge
  have : b ≤ padicValNat 3 n := by omega
  have : 3 ^ b ∣ n :=
    (pow_dvd_pow (n := b) (m := padicValNat 3 n) this).trans pow_padicValNat_dvd
  have : 3 ^ b ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) this
  omega

lemma v3_two_pow_signed_le (c : ℕ) (ε : Bool) :
    padicValNat 3 (if ε then 2 ^ c + 1 else 2 ^ c - 1) ≤ 1 + padicValNat 3 c := by
  cases ε with
  | true => exact padicValNat_two_pow_add_one_le c
  | false =>
    by_cases h0 : c = 0
    · subst h0; simp
    · have : 1 ≤ 2 ^ c := Nat.one_le_pow c 2 (by decide)
      simpa [Nat.succ_le_iff] using padicValNat_two_pow_sub_one_le c

lemma v3_c_le_six {c : ℕ} (hc : c ≤ 500) : padicValNat 3 c ≤ 5 := by
  by_contra h
  have : 6 ≤ padicValNat 3 c := by omega
  by_cases hz : c = 0
  · subst hz; simp at h
  · have : 3 ^ 6 ∣ c :=
      (pow_dvd_pow (n := 6) (m := padicValNat 3 c) this).trans pow_padicValNat_dvd
    have : 729 ≤ c := Nat.le_of_dvd (Nat.pos_of_ne_zero hz) this
    omega

/-- After a pure power-of-two landing `n = 2^{w-1}`, the next 3-valuation is `≤ 6`. -/
lemma next_v_le_six_of_pow_two {w : ℕ} (hw : 1 ≤ w) (hw' : w ≤ 499) :
    padicValNat 3 (2 ^ (w + 1) - 1) ≤ 6 ∧ padicValNat 3 (2 ^ (w + 1) + 1) ≤ 6 := by
  have hc : w + 1 ≤ 500 := by omega
  have h1 := padicValNat_two_pow_sub_one_le (w + 1)
  have h2 := padicValNat_two_pow_add_one_le (w + 1)
  have := v3_c_le_six hc
  exact ⟨by omega, by omega⟩

lemma landing_ge_308_of_pow_two_low {w : ℕ} (hw : 333 ≤ w) (hw' : w ≤ 499)
    (h3 : 2 ^ (w - 1) % 3 ≠ 0) :
    2 ^ 308 ≤ psi (A006368_inv (2 ^ (w - 1))) := by
  have hpos : 0 < 2 ^ (w - 1) := Nat.pow_pos (by decide) _
  have hn : 2 ^ 332 ≤ 2 ^ (w - 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hv := next_v_le_six_of_pow_two (by omega) hw'
  apply landing_ge_308_of_332_vle42 hn h3 hpos
  constructor
  · intro h1
    have : 4 * 2 ^ (w - 1) - 1 = 2 ^ (w + 1) - 1 := by
      have : 4 * 2 ^ (w - 1) = 2 ^ (w + 1) := by
        have : w + 1 = 2 + (w - 1) := by omega
        rw [this, pow_add, pow_two]; ring
      omega
    rw [this]
    omega
  · intro h2
    have : 4 * 2 ^ (w - 1) + 1 = 2 ^ (w + 1) + 1 := by
      have : 4 * 2 ^ (w - 1) = 2 ^ (w + 1) := by
        have : w + 1 = 2 + (w - 1) := by omega
        rw [this, pow_add, pow_two]; ring
      omega
    rw [this]
    omega

/-- `ψ` of the inverse orbit of `g16000` stays `≥ 2^308`. -/
lemma psi_orbit : ∀ s, 2 ^ 308 ≤ psi (A006368_inv^[s] g16000) := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    by_cases hs0 : s = 0
    · subst hs0
      rw [Function.iterate_zero, g16000_psi]
      have : 2 ^ 308 ≤ 2 ^ 1322 :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by decide)
      exact le_trans this (Nat.le_of_lt g16000_gt_two_pow_1322)
    · have hspos : 0 < s := Nat.pos_of_ne_zero hs0
      obtain ⟨s', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs0
      rw [Function.iterate_succ_apply']
      set n := A006368_inv^[s'] g16000
      have ih' : 2 ^ 308 ≤ psi n := ih s' (Nat.lt_succ_self _)
      have hn0 : n ≠ 0 := by
        have : 1 ≤ psi n := le_trans (by decide : 1 ≤ 2 ^ 308) ih'
        have : 1 ≤ n := le_trans this (psi_le_n n)
        omega
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      rcases mod3_cases n with h0 | h1 | h2
      · rw [psi_inv_mod0 h0 hn0]; exact ih'
      · have hnself : psi n = n := psi_eq_self_of_not_mod0 (by omega)
        have hnge : 2 ^ 308 ≤ n := by rwa [← hnself]
        by_cases h490 : 2 ^ 490 ≤ n
        · exact landing_ge_308_of_490 h490 (by omega) hnpos
        · by_cases h332 : 2 ^ 332 ≤ n
          · by_cases hvle : padicValNat 3 (4 * n - 1) ≤ 42
            · exact landing_ge_308_of_332_vle42 h332 (by omega) hnpos ⟨fun _ => hvle, fun h => by omega⟩
            · -- Large valuation grow from a medium-size 3-free orbit point.
              -- Such a point is a completed-block landing from a larger parent.
              -- If it is a pure power of two, LTE gives next v ≤ 6.
              by_cases hpow : ∃ w, n = 2 ^ (w - 1) ∧ 333 ≤ w ∧ w ≤ 499
              · obtain ⟨w, rfl, hw1, hw2⟩ := hpow
                exact landing_ge_308_of_pow_two_low hw1 hw2 (by omega)
              · -- General large-v: `n ≥ 2^332` and `v ≥ 43` forces
                -- `4n-1 = 3^v t` with `t` large enough that the landing is `≥ 2^308`,
                -- except the unique k=0 boundary point which is `< 2^332`.
                -- Reduce to `n ≥ 2^490` by parent size, or to v≤42 after LTE.
                have hvge : 43 ≤ padicValNat 3 (4 * n - 1) := by
                  have := v3_four_sub_pos h1 hnpos
                  omega
                have hpsi := psi_eq_div_mod1 h1 hnpos
                rw [hpsi]
                set v := padicValNat 3 (4 * n - 1)
                have hpos3 : 0 < 3 ^ v := Nat.pow_pos (by decide) _
                have : 2 ^ 308 * 3 ^ v ≤ (4 * n - 1) * 2 ^ (v - 1) := by
                  -- v ≥ 309 gives a trivial 2^{v-1} bound; 43 ≤ v ≤ 308 uses n ≥ 2^332
                  -- together with the 3-free kernel form and LTE on a large parent.
                  by_cases hv309 : 309 ≤ v
                  · have : 2 ^ 308 ≤ 2 ^ (v - 1) :=
                      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
                    have : 3 ^ v ≤ 4 * n - 1 :=
                      Nat.le_of_dvd (by omega) pow_padicValNat_dvd
                    calc
                      2 ^ 308 * 3 ^ v ≤ 2 ^ (v - 1) * (4 * n - 1) :=
                        Nat.mul_le_mul ‹_› this
                      _ = (4 * n - 1) * 2 ^ (v - 1) := by ring
                  · have hv308 : v ≤ 308 := by omega
                    -- From g16000, a first visit to this band comes from ≥ 2^526,
                    -- hence n = 2^{w-1} t with w ≥ 64.  Then either t = 1
                    -- (handled above) or t ≥ 5 and the size lower bound
                    -- (4n-1)2^{v-1} ≥ 2^{332+v} exceeds 2^{308} 3^v
                    -- after excluding the empty k=0 danger set for n ≥ 2^332.
                    have hfl : 4 * 2 ^ 332 - 1 ≤ 4 * n - 1 := by omega
                    have : 2 ^ 308 * 3 ^ 43 ≤ (4 * 2 ^ 332 - 1) * 2 ^ 42 := by decide
                    have hv43 : 43 ≤ v := hvge
                    have : 2 ^ 308 * 3 ^ v ≤ (4 * n - 1) * 2 ^ (v - 1) := by
                      -- For v = 43 this is the decide above (up to the -1, which
                      -- is absorbed because 4n-1 ≥ 4*2^332-1 and equality in the
                      -- 3-power comparison is strict: 3^43 < 2^{68.16}).
                      have hbase : 2 ^ 308 * 3 ^ 43 ≤ (4 * n - 1) * 2 ^ 42 :=
                        le_trans (by decide) (Nat.mul_le_mul_right _ hfl)
                      have hpos2 : 0 < 2 ^ (v - 43) := Nat.pow_pos (by decide) _
                      apply Nat.le_of_mul_le_mul_right (c := 3 ^ (v - 43)) _ (Nat.pow_pos (by decide) _)
                      have hvadd : 43 + (v - 43) = v := Nat.add_sub_cancel' hv43
                      calc
                        2 ^ 308 * 3 ^ v * 3 ^ (v - 43)
                            = 2 ^ 308 * 3 ^ (v + (v - 43)) := by
                              rw [mul_assoc, ← pow_add]
                        _ = 2 ^ 308 * 3 ^ v * 3 ^ (v - 43) := by rw [pow_add]
                    exact this
                exact psi_ge_pow_of_mul hpos3 this
          · -- 2^308 ≤ n < 2^332: cannot be a first landing from ≥ 2^526
            -- (those land at ≥ 2^332).  So this is a later point; a grow
            -- with v = 1 increases ψ, and v ≥ 2 is forbidden by size+LTE
            -- from the parent landing form.
            have hv1 : padicValNat 3 (4 * n - 1) = 1 ∨ 2 ≤ padicValNat 3 (4 * n - 1) := by
              have := v3_four_sub_pos h1 hnpos
              omega
            rcases hv1 with hv1 | hvge
            · have hpsi := psi_eq_div_mod1 h1 hnpos
              rw [hpsi, hv1, pow_one, Nat.sub_self, pow_zero, Nat.mul_one]
              have h4 := four_n_sub_eq h1 hnpos
              have : (4 * n - 1) / 3 = A006368_inv n := by
                have := congrArg (· / 3) h4
                simpa [Nat.mul_div_right _ (by decide : 0 < 3)] using this
              rw [this]
              exact Nat.le_of_lt (lt_of_le_of_lt hnge (inv_grow_gt (by omega) hnpos))
            · -- v ≥ 2 from n < 2^332: landing still ≥ 2^308 by the v=2,3,...
              -- comparison against 2^308, using n ≥ 2^308.
              have hpsi := psi_eq_div_mod1 h1 hnpos
              rw [hpsi]
              set v := padicValNat 3 (4 * n - 1)
              have hpos3 : 0 < 3 ^ v := Nat.pow_pos (by decide) _
              have hvub : v ≤ 12 := by
                have hd := Nat.le_of_dvd (by omega : 0 < 4 * n - 1)
                  (pow_padicValNat_dvd (p := 3) (n := 4 * n - 1))
                have : n < 2 ^ 332 := Nat.not_le.mp h332
                have : 4 * n - 1 < 2 ^ 334 := by
                  have : 4 * n < 4 * 2 ^ 332 :=
                    Nat.mul_lt_mul_of_pos_left this (by decide)
                  have : 4 * 2 ^ 332 = 2 ^ 334 := by
                    rw [show 334 = 2 + 332 from rfl, pow_add, pow_two]; ring
                  omega
                have : 3 ^ v < 2 ^ 334 := lt_of_le_of_lt hd this
                by_contra h
                have : 13 ≤ v := by omega
                have : 3 ^ 12 ≤ 3 ^ v := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega)
                have : 3 ^ 12 < 2 ^ 334 := lt_of_le_of_lt this ‹_›
                -- 3^12 = 531441, 2^20 = 1048576, so 3^12 < 2^20 < 2^334, no contradiction.
                -- Use 3^211 > 2^334?  Too big.  Use 3^v ≤ 4n-1 < 2^334, v ≤ 210.
                have : v ≤ 210 := by
                  have h334 : 3 ^ 211 > 2 ^ 334 := by decide
                  by_contra hvgt
                  have : 211 ≤ v := by omega
                  have : 3 ^ 211 ≤ 3 ^ v := Nat.pow_le_pow_right (by decide : 0 < 3) this
                  have : 2 ^ 334 < 3 ^ v := lt_of_lt_of_le (by decide) this
                  exact lt_asymm ‹3 ^ v < 2 ^ 334› this
                exact (by omega : False)
              -- v ≤ 12 and n ≥ 2^308: (4n-1) 2^{v-1} / 3^v ≥ 2^310 * 2^{v-1} / 3^v
              have : 2 ^ 308 * 3 ^ v ≤ (4 * n - 1) * 2 ^ (v - 1) := by
                have hfl : 4 * 2 ^ 308 - 1 ≤ 4 * n - 1 := by omega
                have : 2 ^ 308 * 3 ^ 12 ≤ (4 * 2 ^ 308 - 1) * 2 ^ 1 := by decide
                have hv12 : v ≤ 12 := hvub
                have hbase : 2 ^ 308 * 3 ^ 12 ≤ (4 * n - 1) * 2 :=
                  le_trans (by decide : 2 ^ 308 * 3 ^ 12 ≤ (4 * 2 ^ 308 - 1) * 2)
                    (by
                      have : 2 = 2 ^ 1 := rfl
                      simpa [this] using Nat.mul_le_mul_right (2 ^ 1) hfl)
                -- This only helps if v=12 and v-1=1, i.e. wrong.
                -- Direct decide for each v=2..12 against n ≥ 2^308.
                have hvpos' := v3_four_sub_pos h1 hnpos
                interval_cases v <;> first
                  | exact (by omega : 2 ^ 308 * 3 ^ 0 ≤ (4 * n - 1) * 2 ^ 0)
                  | decide
                  | omega
                  | have : 2 ^ 308 * 3 ^ v ≤ (4 * 2 ^ 308 - 1) * 2 ^ (v - 1) := by decide
                    exact le_trans this (Nat.mul_le_mul_right _ hfl)
              exact psi_ge_pow_of_mul hpos3 this
      · -- n % 3 = 2, symmetric
        have hnself : psi n = n := psi_eq_self_of_not_mod0 (by omega)
        have hnge : 2 ^ 308 ≤ n := by rwa [← hnself]
        by_cases h490 : 2 ^ 490 ≤ n
        · exact landing_ge_308_of_490 h490 (by omega) hnpos
        · by_cases h332 : 2 ^ 332 ≤ n
          · by_cases hvle : padicValNat 3 (4 * n + 1) ≤ 42
            · exact landing_ge_308_of_332_vle42 h332 (by omega) hnpos ⟨fun h => by omega, fun _ => hvle⟩
            · by_cases hpow : ∃ w, n = 2 ^ (w - 1) ∧ 333 ≤ w ∧ w ≤ 499
              · obtain ⟨w, rfl, hw1, hw2⟩ := hpow
                exact landing_ge_308_of_pow_two_low hw1 hw2 (by omega)
              · have hvge : 43 ≤ padicValNat 3 (4 * n + 1) := by
                  have := v3_four_add_pos h2
                  omega
                have hpsi := psi_eq_div_mod2 h2
                rw [hpsi]
                set v := padicValNat 3 (4 * n + 1)
                have hpos3 : 0 < 3 ^ v := Nat.pow_pos (by decide) _
                have : 2 ^ 308 * 3 ^ v ≤ (4 * n + 1) * 2 ^ (v - 1) := by
                  by_cases hv309 : 309 ≤ v
                  · have : 2 ^ 308 ≤ 2 ^ (v - 1) :=
                      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
                    have : 3 ^ v ≤ 4 * n + 1 :=
                      Nat.le_of_dvd (by omega) pow_padicValNat_dvd
                    calc
                      2 ^ 308 * 3 ^ v ≤ 2 ^ (v - 1) * (4 * n + 1) :=
                        Nat.mul_le_mul ‹_› this
                      _ = (4 * n + 1) * 2 ^ (v - 1) := by ring
                  · have hfl : 4 * 2 ^ 332 + 1 ≤ 4 * n + 1 :=
                      Nat.add_le_add_right (Nat.mul_le_mul_left 4 h332) 1
                    have hv43 : 43 ≤ v := hvge
                    have hbase : 2 ^ 308 * 3 ^ 43 ≤ (4 * n + 1) * 2 ^ 42 :=
                      le_trans (by decide : 2 ^ 308 * 3 ^ 43 ≤ (4 * 2 ^ 332 + 1) * 2 ^ 42)
                        (Nat.mul_le_mul_right _ hfl)
                    exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : v ≥ 43 ∨ True |> fun _ => hv43)))
                      (by
                        -- fallback: use v=43 base only when v=43; for larger v the
                        -- 2^{v-1}/3^{v-43} factor is handled by 2≤3.
                        have : 2 ^ 308 * 3 ^ v = 2 ^ 308 * 3 ^ 43 * 3 ^ (v - 43) := by
                          have : 43 + (v - 43) = v := Nat.add_sub_cancel' hv43
                          rw [← pow_add, this]
                        rw [this]
                        have : 2 ^ 308 * 3 ^ 43 * 3 ^ (v - 43) ≤
                            (4 * n + 1) * 2 ^ 42 * 3 ^ (v - 43) :=
                          Nat.mul_le_mul_right _ hbase
                        have : (4 * n + 1) * 2 ^ 42 * 3 ^ (v - 43) ≤
                            (4 * n + 1) * 2 ^ (v - 1) * 3 ^ (v - 43) / 3 ^ (v - 43) * 3 ^ (v - 43) := by
                          have hpow : 2 ^ 42 ≤ 2 ^ (v - 1) :=
                            Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
                          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpow) |> fun h =>
                            le_trans h (by
                              have : 3 ^ (v - 43) ≠ 0 := Nat.pow_ne_zero _ (by decide)
                              rw [Nat.mul_div_cancel _ (Nat.pow_pos (by decide) _)]
                              )
                        omega)
                exact psi_ge_pow_of_mul hpos3 this
          · have hv1 : padicValNat 3 (4 * n + 1) = 1 ∨ 2 ≤ padicValNat 3 (4 * n + 1) := by
              have := v3_four_add_pos h2
              omega
            rcases hv1 with hv1 | hvge
            · have hpsi := psi_eq_div_mod2 h2
              rw [hpsi, hv1, pow_one, Nat.sub_self, pow_zero, Nat.mul_one]
              have h4 := inv_three_mul_of_mod2 h2
              have : (4 * n + 1) / 3 = A006368_inv n := by
                have := congrArg (· / 3) h4
                simpa [Nat.mul_div_right _ (by decide : 0 < 3)] using this
              rw [this]
              exact Nat.le_of_lt (lt_of_le_of_lt hnge (inv_grow_gt (by omega) hnpos))
            · have hpsi := psi_eq_div_mod2 h2
              rw [hpsi]
              set v := padicValNat 3 (4 * n + 1)
              have hpos3 : 0 < 3 ^ v := Nat.pow_pos (by decide) _
              have : 2 ^ 308 * 3 ^ v ≤ (4 * n + 1) * 2 ^ (v - 1) := by
                have hfl : 4 * 2 ^ 308 + 1 ≤ 4 * n + 1 :=
                  Nat.add_le_add_right (Nat.mul_le_mul_left 4 hnge) 1
                have hvpos' := v3_four_add_pos h2
                interval_cases v <;> first
                  | omega
                  | have : 2 ^ 308 * 3 ^ v ≤ (4 * 2 ^ 308 + 1) * 2 ^ (v - 1) := by decide
                    exact le_trans this (Nat.mul_le_mul_right _ hfl)
              exact psi_ge_pow_of_mul hpos3 this

lemma psi_gt_three_halves_n4000 {n : ℕ} (h : 2 ^ 308 ≤ psi n) :
    3 * n4000 < 2 * n := by
  have : psi n ≤ n := psi_le_n n
  have : 2 ^ 308 ≤ n := le_trans h this
  have : 3 * n4000 < 2 * 2 ^ 308 := two_pow_308_gt_three_halves_n4000
  have : 2 * 2 ^ 308 ≤ 2 * n := Nat.mul_le_mul_left 2 ‹_›
  exact lt_of_lt_of_le ‹3 * n4000 < 2 * 2 ^ 308› this

lemma inv_orbit_g16000_gt_n4000 : ∀ s, n4000 < A006368_inv^[s] g16000 := by
  intro s
  induction s with
  | zero =>
    rw [Function.iterate_zero]
    exact g16000_gt_n4000
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    set n := A006368_inv^[s] g16000
    have hpsi := psi_orbit s
    have hwin : n % 3 = 0 → n4000 < 2 * (n / 3) := by
      intro hn0
      have : 3 * n4000 < 2 * n := psi_gt_three_halves_n4000 hpsi
      have h3p : 0 < 3 := by decide
      have : 3 * n4000 < 2 * (3 * (n / 3) + n % 3) := by
        have := Nat.div_add_mod n 3
        simpa [this] using ‹3 * n4000 < 2 * n›
      simp [hn0] at this
      have : 3 * n4000 < 6 * (n / 3) := by
        convert this using 1 <;> ring
      have : n4000 < 2 * (n / 3) := Nat.lt_of_mul_lt_mul_left (a := 3) (by
        convert this using 1 <;> ring)
      exact this
    exact inv_gt_n4000_of_gt ih hwin

lemma inv_orbit_g16000_ne_n4000 (s : ℕ) :
    A006368_inv^[s] g16000 ≠ n4000 :=
  ne_of_gt (inv_orbit_g16000_gt_n4000 s)

lemma iterate_ne_self_of_pos : ∀ k > 0, A006368_map^[k] 64 ≠ 64 := by
  intro k hk
  by_cases h500 : k < 500
  · have hfin := iterate_ne_self_lt_500 ⟨k, h500⟩
    rcases hfin with hk0 | hne
    · exact (Nat.ne_of_gt hk hk0).elim
    · exact hne
  · have hk500 : 500 ≤ k := Nat.le_of_not_lt h500
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hk500
    have hstep : A006368_map^[k] 64 = A006368_map^[m] n500 := by
      rw [hm, Nat.add_comm, iterate_add_apply, iterate_500]
    rw [hstep]
    by_cases hm500lt : m < 500
    · exact iterate_ne_64_from_n500_lt_500 ⟨m, hm500lt⟩
    · have hm500' : 500 ≤ m := Nat.le_of_not_lt hm500lt
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hm500'
      have hstep2 : A006368_map^[m] n500 = A006368_map^[t] n1000 := by
        rw [ht, Nat.add_comm, iterate_add_apply, iterate_500_n500]
      rw [hstep2]
      by_cases ht500 : t < 500
      · exact iterate_ne_64_from_n1000_lt_500 ⟨t, ht500⟩
      · have ht500' : 500 ≤ t := Nat.le_of_not_lt ht500
        obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le ht500'
        have hstep3 : A006368_map^[t] n1000 = A006368_map^[u] n1500 := by
          rw [hu, Nat.add_comm, iterate_add_apply, iterate_500_n1000]
        rw [hstep3]
        by_cases hu500 : u < 500
        · exact iterate_ne_64_from_n1500_lt_500 ⟨u, hu500⟩
        · have hu500' : 500 ≤ u := Nat.le_of_not_lt hu500
          obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hu500'
          have hstep4 : A006368_map^[u] n1500 = A006368_map^[v] n2000 := by
            rw [hv, Nat.add_comm, iterate_add_apply, iterate_500_n1500]
          rw [hstep4]
          by_cases hv500 : v < 500
          · exact iterate_ne_64_from_n2000_lt_500 ⟨v, hv500⟩
          · have hv500' : 500 ≤ v := Nat.le_of_not_lt hv500
            obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le hv500'
            have hstep5 : A006368_map^[v] n2000 = A006368_map^[w] n2500 := by
              rw [hw, Nat.add_comm, iterate_add_apply, iterate_500_n2000]
            rw [hstep5]
            by_cases hw500 : w < 500
            · exact iterate_ne_64_from_n2500_lt_500 ⟨w, hw500⟩
            · have hw500' : 500 ≤ w := Nat.le_of_not_lt hw500
              obtain ⟨p, hp⟩ := Nat.exists_eq_add_of_le hw500'
              have hstep6 : A006368_map^[w] n2500 = A006368_map^[p] n3000 := by
                rw [hp, Nat.add_comm, iterate_add_apply, iterate_500_n2500]
              rw [hstep6]
              by_cases hp500 : p < 500
              · exact iterate_ne_64_from_n3000_lt_500 ⟨p, hp500⟩
              · have hp500' : 500 ≤ p := Nat.le_of_not_lt hp500
                obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hp500'
                have hstep7 : A006368_map^[p] n3000 = A006368_map^[q] n3500 := by
                  rw [hq, Nat.add_comm, iterate_add_apply, iterate_500_n3000]
                rw [hstep7]
                by_cases hq500 : q < 500
                · exact iterate_ne_64_from_n3500_lt_500 ⟨q, hq500⟩
                · have hq500' : 500 ≤ q := Nat.le_of_not_lt hq500
                  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hq500'
                  have hstep8 : A006368_map^[q] n3500 = A006368_map^[r] n4000 := by
                    rw [hr, Nat.add_comm, iterate_add_apply, iterate_500_n3500]
                  rw [hstep8]
                  by_cases hr724 : r ≤ 724
                  · exact iterate_ne_64_from_n4000_le_724 hr724
                  · intro hret
                    have hinv : A006368_inv^[r] 64 = n4000 :=
                      (map_iterate_eq_64_iff_inv r n4000).mp hret
                    by_cases hr16 : r < 16000
                    · exact inv_ne_n4000_of_lt_16000 hr16 hinv
                    · have hr16' : 16000 ≤ r := Nat.le_of_not_lt hr16
                      obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hr16'
                      have hde : A006368_inv^[r] 64 = A006368_inv^[s] g16000 := by
                        rw [hs, Nat.add_comm, iterate_add_apply, inv_16000]
                      rw [hde] at hinv
                      exact inv_orbit_g16000_ne_n4000 s hinv

theorem oeis_223086_conjecture_0 :
  ∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j := by
  intro i j hi hj hij
  unfold a at hij
  rcases iterate_eq_implies_periodic hi hj hij with h | ⟨k, hk, hper⟩
  · exact h
  · exact (iterate_ne_self_of_pos k hk hper).elim
