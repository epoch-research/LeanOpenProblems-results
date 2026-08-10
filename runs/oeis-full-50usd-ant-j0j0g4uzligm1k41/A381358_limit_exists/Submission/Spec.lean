import FormalConjectures.Util.ProblemImports
open List Nat
private def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => x = h)
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
termination_by l => l.length

theorem tw_replicate (a : ℕ) (L : List ℕ) :
    L.takeWhile (fun x => x = a) = List.replicate (L.takeWhile (fun x => x = a)).length a := by
  have : ∀ y ∈ L.takeWhile (fun x => x = a), y = a := by
    intro y hy; have := List.mem_takeWhile_imp hy; simpa using this
  rw [List.eq_replicate_iff]; exact ⟨rfl, this⟩

theorem drop_tw_len (p : ℕ → Bool)(l:List ℕ) : l.drop (l.takeWhile p).length = l.dropWhile p := by
  have key := List.takeWhile_append_dropWhile (p:=p) (l:=l)
  calc l.drop (l.takeWhile p).length
      = (l.takeWhile p ++ l.dropWhile p).drop (l.takeWhile p).length := by rw [key]
    _ = l.dropWhile p := by rw [List.drop_append_of_le_length (Nat.le_refl _)]; simp

theorem rl_append_neq : ∀ (A : List ℕ) (hne : A ≠ []) (b : ℕ) (B' : List ℕ),
    A.getLast hne ≠ b → run_lengths_nat (A ++ b :: B') = run_lengths_nat A ++ run_lengths_nat (b :: B') := by
  intro A
  induction A using run_lengths_nat.induct with
  | case1 => intro hne; exact absurd rfl hne
  | case2 h tail rp rest ih =>
    intro hne b B' hlast
    -- k and rest
    have hkle : rp.length ≤ (h::tail).length := (List.takeWhile_sublist _).length_le
    have hrl : run_lengths_nat (h::tail) = rp.length :: run_lengths_nat rest := by
      conv_lhs => rw [run_lengths_nat]
    have hdrop_app : ((h::tail) ++ b :: B').drop rp.length = rest ++ b :: B' := by
      rw [List.drop_append_of_le_length hkle]
    -- first run length of appended list equals rp.length
    have htw_app : (((h::tail) ++ b :: B').takeWhile (fun x => x = h)).length = rp.length := by
      rw [List.takeWhile_append]
      by_cases hcase : (((h::tail).takeWhile (fun x => x = h)).length = (h::tail).length)
      · -- whole h::tail is one run; then rest = []
        simp only [hcase, if_true]
        -- rest = drop (length) (h::tail) = []
        have hrestnil : rest = [] := by
          have : rest = (h::tail).drop ((h::tail).takeWhile (fun x => x = h)).length := rfl
          rw [this, hcase]; simp
        -- getLast (h::tail) = h since it's a replicate run
        have hreplen : (h::tail) = List.replicate ((h::tail).takeWhile (fun x => x=h)).length h := by
          conv_lhs => rw [← List.takeWhile_append_dropWhile (p := fun x => x = h) (l := h::tail)]
          have hdw : (h::tail).dropWhile (fun x => x = h) = [] := by
            rw [← drop_tw_len]
            have : rest = (h::tail).drop ((h::tail).takeWhile (fun x => x = h)).length := rfl
            rw [← this, hrestnil]
          rw [hdw, List.append_nil]; exact tw_replicate h (h::tail)
        have hgl : (h::tail).getLast hne = h := by
          have hm := List.getLast_mem hne
          have hmem : (h::tail).getLast hne ∈ List.replicate ((h::tail).takeWhile (fun x => x=h)).length h := by
            rw [← hreplen]; exact hm
          exact List.eq_of_mem_replicate hmem
        have hbh : ¬ ((b:ℕ) = h) := by rw [hgl] at hlast; exact fun hh => hlast hh.symm
        have hbnil : ((b::B').takeWhile (fun x => x = h)) = [] := by
          rw [List.takeWhile_cons]; simp [hbh]
        rw [hbnil, List.append_nil]
        exact hcase.symm
      · rw [if_neg hcase]
    -- now compute rl of appended
    have e1 : (h::tail) ++ b :: B' = h :: (tail ++ b :: B') := rfl
    rw [e1] at htw_app hdrop_app
    have hrl_app : run_lengths_nat ((h::tail) ++ b :: B')
        = rp.length :: run_lengths_nat (rest ++ b :: B') := by
      rw [e1]
      conv_lhs => rw [run_lengths_nat]
      rw [htw_app, hdrop_app]
    rw [hrl_app, hrl]
    -- split on rest empty
    by_cases hr : rest = []
    · rw [hr]; simp [run_lengths_nat]
    · have hglrest : rest.getLast hr = (h::tail).getLast hne := List.getLast_drop hr
      have hib := ih hr b B' (by rw [hglrest]; exact hlast)
      rw [hib, List.cons_append]

theorem rl_replicate (k h : ℕ) : run_lengths_nat (List.replicate (k+1) h) = [k+1] := by
  rw [List.replicate_succ]
  conv_lhs => rw [run_lengths_nat]
  have htw : ((h :: List.replicate k h).takeWhile (fun x => x = h)) = List.replicate (k+1) h := by
    rw [← List.replicate_succ, List.takeWhile_replicate]; simp
  rw [htw]
  simp only [List.length_replicate]
  rw [← List.replicate_succ, List.drop_replicate]
  simp [run_lengths_nat]

theorem head_dropWhile_ne (a : ℕ) (L : List ℕ) (hL : L.dropWhile (fun x => x = a) ≠ []) :
    (L.dropWhile (fun x => x = a)).head hL ≠ a := by
  intro hc
  have hlen : 0 < (L.dropWhile (fun x => x = a)).length := List.length_pos_of_ne_nil hL
  have hz := List.dropWhile_get_zero_not (p := fun x => x = a) L hlen
  apply hz
  simp only [List.get_eq_getElem]
  rw [List.head_eq_getElem] at hc
  simp [hc]

theorem rl_reverse : ∀ (L : List ℕ), run_lengths_nat (L.reverse) = (run_lengths_nat L).reverse := by
  intro L
  induction L using run_lengths_nat.induct with
  | case1 => simp [run_lengths_nat]
  | case2 h tail rp rest ih =>
    have hkpos : 1 ≤ rp.length := by
      have : rp = (h::tail).takeWhile (fun x => x = h) := rfl
      rw [this, List.takeWhile_cons]; simp
    have hrl : run_lengths_nat (h::tail) = rp.length :: run_lengths_nat rest := by
      conv_lhs => rw [run_lengths_nat]
    have e : rest = (h::tail).dropWhile (fun x => x = h) := by
      show (h::tail).drop _ = _; rw [drop_tw_len]
    have hdecomp : (h::tail) = List.replicate rp.length h ++ rest := by
      rw [e]
      conv_lhs => rw [← List.takeWhile_append_dropWhile (p := fun x => x = h) (l := h::tail)]
      congr 1
      exact tw_replicate h (h::tail)
    have hrev : (h::tail).reverse = rest.reverse ++ List.replicate rp.length h := by
      rw [hdecomp]; rw [List.reverse_append, List.reverse_replicate]
    rw [hrev]
    by_cases hr : rest = []
    · rw [hr]
      simp only [List.reverse_nil, List.nil_append]
      obtain ⟨k, hk⟩ : ∃ k, rp.length = k + 1 := ⟨rp.length - 1, by omega⟩
      rw [hk, rl_replicate, hrl, hr]
      simp [run_lengths_nat, hk]
    · have hrevne : rest.reverse ≠ [] := by simp [hr]
      have hheadne : rest.reverse.getLast hrevne ≠ h := by
        have hdwne : (h::tail).dropWhile (fun x => x = h) ≠ [] := by rw [← e]; exact hr
        have key := head_dropWhile_ne h (h::tail) hdwne
        rw [List.getLast_reverse]
        intro hc
        apply key
        have heq : rest.head hr = ((h::tail).dropWhile (fun x => x = h)).head hdwne := by
          congr 1
        rw [← heq]
        exact hc
      obtain ⟨k, hk⟩ : ∃ k, rp.length = k + 1 := ⟨rp.length - 1, by omega⟩
      have hrepl : List.replicate rp.length h = h :: List.replicate k h := by rw [hk, List.replicate_succ]
      rw [hrepl, rl_append_neq rest.reverse hrevne h (List.replicate k h) hheadne, ih]
      have hrr : run_lengths_nat (h :: List.replicate k h) = [rp.length] := by
        rw [← List.replicate_succ, rl_replicate k h, hk]
      rw [hrr, hrl]
      simp [List.reverse_cons]

theorem rl_ne_nil {L : List ℕ} (h : L ≠ []) : run_lengths_nat L ≠ [] := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h
  rw [run_lengths_nat]; simp

-- basic unfold at a literal cons
theorem rl_unfold (h : ℕ) (t : List ℕ) :
    run_lengths_nat (h :: t)
      = ((h::t).takeWhile (fun x=>x=h)).length
        :: run_lengths_nat ((h::t).drop ((h::t).takeWhile (fun x=>x=h)).length) := by
  conv_lhs => rw [run_lengths_nat]

-- rl(replicate k h ++ h::B') = (k + head(rl(h::B'))) :: tail(rl(h::B'))
theorem rl_replicate_merge (k h : ℕ) (hk : 1 ≤ k) (B' : List ℕ) :
    run_lengths_nat (List.replicate k h ++ h :: B')
      = (k + (run_lengths_nat (h :: B')).head (rl_ne_nil (by simp)))
        :: (run_lengths_nat (h :: B')).tail := by
  have hunf := rl_unfold h B'
  set j := ((h::B').takeWhile (fun x => x = h)).length with hj
  have hjpos : 1 ≤ j := by rw [hj, List.takeWhile_cons]; simp
  simp only [hunf, List.head_cons, List.tail_cons]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hcons : List.replicate (k'+1) h ++ h :: B' = h :: (List.replicate k' h ++ h :: B') := by
    rw [List.replicate_succ]; rfl
  rw [hcons, rl_unfold]
  have htwlen : ((h :: (List.replicate k' h ++ h :: B')).takeWhile (fun x => x = h)).length = (k'+1) + j := by
    rw [← hcons, List.takeWhile_append]
    have hall : ((List.replicate (k'+1) h).takeWhile (fun x => x = h)).length = (List.replicate (k'+1) h).length := by
      rw [List.takeWhile_replicate]; simp
    rw [if_pos hall]
    simp only [List.length_append, List.length_replicate]
    rw [← hj]
  rw [htwlen]
  have hdrop : (h :: (List.replicate k' h ++ h :: B')).drop ((k'+1)+j) = (h::B').drop j := by
    rw [← hcons, show (k'+1)+j = (List.replicate (k'+1) h).length + j from by simp, List.drop_append]
    simp
  rw [hdrop]

theorem rl_append_eq : ∀ (A : List ℕ) (hne : A ≠ []) (b : ℕ) (B' : List ℕ),
    A.getLast hne = b →
    run_lengths_nat (A ++ b :: B')
      = (run_lengths_nat A).dropLast
        ++ ((run_lengths_nat A).getLast (rl_ne_nil hne)
            + (run_lengths_nat (b::B')).head (rl_ne_nil (by simp)))
          :: (run_lengths_nat (b::B')).tail := by
  intro A
  induction A using run_lengths_nat.induct with
  | case1 => intro hne; exact absurd rfl hne
  | case2 h tail rp rest ih =>
    intro hne b B' hlast
    have hkpos : 1 ≤ rp.length := by
      have : rp = (h::tail).takeWhile (fun x => x = h) := rfl
      rw [this, List.takeWhile_cons]; simp
    have hrl : run_lengths_nat (h::tail) = rp.length :: run_lengths_nat rest := by
      conv_lhs => rw [run_lengths_nat]
    have e : rest = (h::tail).dropWhile (fun x => x = h) := by
      show (h::tail).drop _ = _; rw [drop_tw_len]
    have hdecomp : (h::tail) = List.replicate rp.length h ++ rest := by
      rw [e]
      conv_lhs => rw [← List.takeWhile_append_dropWhile (p := fun x => x = h) (l := h::tail)]
      congr 1; exact tw_replicate h (h::tail)
    by_cases hr : rest = []
    · -- single run
      have hdec2 : (h::tail) = List.replicate rp.length h := by rw [hdecomp, hr, List.append_nil]
      have hgl : (h::tail).getLast hne = h := by
        have hm := List.getLast_mem hne
        have : (h::tail).getLast hne ∈ List.replicate rp.length h := by rw [← hdec2]; exact hm
        exact List.eq_of_mem_replicate this
      have hbh : b = h := by rw [← hlast, hgl]
      subst hbh
      have hrlA : run_lengths_nat (List.replicate rp.length b) = [rp.length] := by
        obtain ⟨k, hk⟩ : ∃ k, rp.length = k + 1 := ⟨rp.length - 1, by omega⟩
        rw [hk, rl_replicate]
      simp only [hdec2]
      rw [rl_replicate_merge rp.length b hkpos B']
      simp [hrlA]
    · -- rest ≠ []
      have hglrest : rest.getLast hr = b := by rw [← hlast]; exact List.getLast_drop hr
      have hle : rp.length ≤ (h::tail).length := (List.takeWhile_sublist _).length_le
      have hlen : rest.length = (h::tail).length - rp.length := by
        have : rest = (h::tail).drop rp.length := rfl
        rw [this, List.length_drop]
      have hlt : rp.length < (h::tail).length := by
        have hpos : 0 < rest.length := List.length_pos_of_ne_nil hr
        omega
      have e1 : (h::tail) ++ b :: B' = h :: (tail ++ b :: B') := rfl
      have htw_app : (((h::tail) ++ b :: B').takeWhile (fun x => x = h)).length = rp.length := by
        rw [List.takeWhile_append, if_neg (by
          show ¬ (((h::tail).takeWhile (fun x => x = h)).length = (h::tail).length)
          intro hc
          rw [show ((h::tail).takeWhile (fun x => x = h)).length = rp.length from rfl] at hc
          omega)]
      have hdrop_app : ((h::tail) ++ b :: B').drop rp.length = rest ++ b :: B' := by
        rw [List.drop_append_of_le_length hle]
      rw [e1] at htw_app hdrop_app
      have hrl_app : run_lengths_nat ((h::tail) ++ b :: B')
          = rp.length :: run_lengths_nat (rest ++ b :: B') := by
        rw [e1, rl_unfold, htw_app, hdrop_app]
      have hib := ih hr b B' hglrest
      have hrne : run_lengths_nat rest ≠ [] := rl_ne_nil hr
      obtain ⟨x, xs, hxs⟩ := List.exists_cons_of_ne_nil hrne
      rw [hrl_app, hib]
      simp only [hrl, hxs, List.dropLast_cons₂, List.getLast_cons_cons, List.cons_append]

theorem rl_single (v : ℕ) : run_lengths_nat [v] = [1] := by
  have := rl_replicate 0 v; simpa using this

theorem rl_cons_new (v w : ℕ) (t : List ℕ) (h : v ≠ w) :
    run_lengths_nat (v :: w :: t) = 1 :: run_lengths_nat (w :: t) := by
  rw [rl_unfold]
  have htw : ((v::w::t).takeWhile (fun x=>x=v)).length = 1 := by
    rw [List.takeWhile_cons]
    simp only [decide_true, List.takeWhile_cons]
    have : ¬ (w = v) := fun hh => h hh.symm
    simp [this]
  rw [htw]
  norm_num

theorem rl_repl_one (B : ℕ) (hB : 1 ≤ B) : run_lengths_nat (List.replicate B 1) = [B] := by
  obtain ⟨k, rfl⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
  exact rl_replicate k 1

-- L1: form of rl(Φ X)
theorem G3_L1 (X a' : List ℕ) (B : ℕ) (hB : 2 ≤ B) (hXne : X ≠ [])
    (hXhead : X.head hXne = 1)
    (had : run_lengths_nat X = List.replicate B 1 ++ a') :
    run_lengths_nat ((run_lengths_nat X).reverse ++ X)
      = (run_lengths_nat (run_lengths_nat X)).tail.reverse
        ++ ((run_lengths_nat (run_lengths_nat X)).head (rl_ne_nil (rl_ne_nil hXne)) + 1)
          :: (run_lengths_nat X).tail := by
  obtain ⟨xh, xt, hX⟩ := List.exists_cons_of_ne_nil hXne
  subst hX
  have hxh : xh = 1 := by simpa using hXhead
  subst hxh
  set a := run_lengths_nat (1 :: xt) with ha
  have hane : a ≠ [] := rl_ne_nil (by simp)
  have harevne : a.reverse ≠ [] := by simp [hane]
  have hahead : a.head hane = 1 := by
    have hh : a.head? = some 1 := by
      rw [had]
      obtain ⟨B', rfl⟩ : ∃ B', B = B'+1 := ⟨B-1, by omega⟩
      simp [List.replicate_succ]
    rw [List.head?_eq_head hane] at hh
    simpa using hh
  have hgl : a.reverse.getLast harevne = 1 := by rw [List.getLast_reverse]; exact hahead
  have hahead' : (run_lengths_nat (1::xt)).head (rl_ne_nil (List.cons_ne_nil 1 xt)) = 1 := hahead
  rw [rl_append_eq a.reverse harevne 1 xt hgl]
  simp only [rl_reverse, List.dropLast_reverse, List.getLast_reverse]
  simp only [hahead', ha]

-- ==== nruns and sum ====
def nruns (L : List ℕ) : ℕ := (run_lengths_nat L).length

theorem rln_sum (L : List ℕ) : (run_lengths_nat L).sum = L.length := by
  induction L using run_lengths_nat.induct with
  | case1 => simp [run_lengths_nat]
  | case2 h tail rp rest ih =>
    rw [run_lengths_nat]
    simp only [List.sum_cons]
    rw [ih]
    have hrest : rest.length = (h::tail).length - ((h::tail).takeWhile (fun x => x = h)).length :=
      by exact List.length_drop
    have hk : ((h::tail).takeWhile (fun x => x = h)).length ≤ (h::tail).length :=
      (List.takeWhile_sublist _).length_le
    omega

theorem nruns_reverse (L : List ℕ) : nruns L.reverse = nruns L := by
  unfold nruns; rw [rl_reverse, List.length_reverse]

theorem nruns_dup (a:ℕ)(t:List ℕ) : nruns (a::a::t) = nruns (a::t) := by
  unfold nruns
  conv_lhs => rw [run_lengths_nat]
  conv_rhs => rw [run_lengths_nat]
  have htw : ((a::a::t).takeWhile (fun x => x = a)).length
           = ((a::t).takeWhile (fun x => x = a)).length + 1 := by
    rw [List.takeWhile_cons]; simp [Nat.add_comm]
  have hrest : (a::a::t).drop ((a::a::t).takeWhile (fun x => x = a)).length
             = (a::t).drop ((a::t).takeWhile (fun x => x = a)).length := by
    rw [htw, List.drop_succ_cons]
  simp only [List.length_cons, hrest]

theorem nruns_neq (a b:ℕ)(t:List ℕ)(hab : a ≠ b) : nruns (a::b::t) = nruns (b::t) + 1 := by
  unfold nruns
  conv_lhs => rw [run_lengths_nat]
  have htw : (a::b::t).takeWhile (fun x => x = a) = [a] := by
    rw [List.takeWhile_cons, List.takeWhile_cons]
    have hba : ¬ (b = a) := fun h => hab h.symm
    simp [hba]
  rw [htw]; simp [List.length_cons]

theorem nruns_cons2 (a b : ℕ) (t : List ℕ) :
    nruns (a :: b :: t) = nruns (b :: t) + (if a = b then 0 else 1) := by
  by_cases hab : a = b
  · subst hab; rw [nruns_dup]; simp
  · rw [nruns_neq a b t hab]; simp [hab]

theorem nruns_cons_pos (a:ℕ)(t:List ℕ) : 1 ≤ nruns (a::t) := by
  unfold nruns; rw [run_lengths_nat]; simp

theorem nruns_singleton (x:ℕ) : nruns [x] = 1 := by
  simp [nruns, run_lengths_nat]

theorem nruns_append_cons (b : ℕ) (B : List ℕ) : ∀ (A : List ℕ) (hA : A ≠ []),
    nruns (A ++ b :: B) = nruns A + nruns (b :: B) - (if A.getLast hA = b then 1 else 0) := by
  intro A
  induction A with
  | nil => intro hA; exact absurd rfl hA
  | cons a A' ih =>
    intro _
    cases A' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.getLast_singleton]
      rw [nruns_cons2 a b B, nruns_singleton a]
      have := nruns_cons_pos b B
      by_cases hab : a = b <;> simp [hab] <;> omega
    | cons a2 A'' =>
      have hne : (a2 :: A'') ≠ [] := by simp
      have hcons : (a :: a2 :: A'') ++ b :: B = a :: ((a2 :: A'') ++ b :: B) := rfl
      rw [hcons]
      have hform : (a2 :: A'') ++ b :: B = a2 :: (A'' ++ b :: B) := rfl
      rw [hform, nruns_cons2 a a2 (A'' ++ b :: B), ← hform, ih hne]
      rw [nruns_cons2 a a2 A'']
      have hlast : (a :: a2 :: A'').getLast (by simp) = (a2 :: A'').getLast hne := by
        rw [List.getLast_cons]
      rw [hlast]
      have h1 := nruns_cons_pos a2 A''
      have h2 := nruns_cons_pos b B
      by_cases hg : (a2 :: A'').getLast hne = b <;>
        by_cases hab : a = a2 <;> simp [hg, hab] <;> omega

theorem rl_L2 (a' : List ℕ) (B : ℕ) (hB : 2 ≤ B) (ha'ne : a' ≠ [])
    (ha'head : a'.head ha'ne ≠ 1)
    (hg1 : (run_lengths_nat a').head (rl_ne_nil ha'ne) ≠ B + 1)
    (hgB : (run_lengths_nat a').head (rl_ne_nil ha'ne) ≠ B) :
    run_lengths_nat ((run_lengths_nat a').reverse ++ (B+1) :: (List.replicate (B-1) 1 ++ a'))
      = (run_lengths_nat (run_lengths_nat a')).reverse ++ 1 :: (B-1) :: run_lengths_nat a' := by
  set p := run_lengths_nat a' with hp
  have hpne : p ≠ [] := rl_ne_nil ha'ne
  have hprevne : p.reverse ≠ [] := by simp [hpne]
  have hgl : p.reverse.getLast hprevne ≠ B + 1 := by
    rw [List.getLast_reverse]; exact hg1
  rw [rl_append_neq p.reverse hprevne (B+1) (List.replicate (B-1) 1 ++ a') hgl]
  rw [rl_reverse]
  -- second piece
  obtain ⟨B'', rfl⟩ : ∃ B'', B = B'' + 2 := ⟨B - 2, by omega⟩
  have hBm1 : B'' + 2 - 1 = B'' + 1 := by omega
  rw [hBm1]
  have hrepl : List.replicate (B''+1) 1 = 1 :: List.replicate B'' 1 := by
    rw [List.replicate_succ]
  rw [hrepl]
  have hne1 : (B''+2) + 1 ≠ 1 := by omega
  rw [show ((B''+2)+1) :: (1 :: List.replicate B'' 1 ++ a')
        = ((B''+2)+1) :: 1 :: (List.replicate B'' 1 ++ a') from rfl]
  rw [rl_cons_new _ 1 _ hne1]
  rw [show (1 :: (List.replicate B'' 1 ++ a')) = (1 :: List.replicate B'' 1) ++ a' from rfl, ← hrepl]
  -- rl(replicate (B''+1) 1 ++ a')
  have hAne : List.replicate (B''+1) 1 ≠ [] := by simp
  have hAgl : (List.replicate (B''+1) 1).getLast hAne = 1 := by
    apply List.eq_of_mem_replicate; exact List.getLast_mem hAne
  obtain ⟨ah, at', hat⟩ := List.exists_cons_of_ne_nil ha'ne
  have hahead' : ah ≠ 1 := by
    have hh : a'.head? = some ah := by rw [hat]; rfl
    rw [List.head?_eq_head ha'ne] at hh
    simp only [Option.some.injEq] at hh
    rw [hh] at ha'head; exact ha'head
  rw [hat]
  rw [rl_append_neq (List.replicate (B''+1) 1) hAne ah at' (by rw [hAgl]; exact fun h => hahead' h.symm)]
  rw [rl_repl_one (B''+1) (by omega)]
  rw [← hat]
  simp only [List.cons_append, List.nil_append, hp]


theorem rl_L3 (a' : List ℕ) (B : ℕ) (hB : 3 ≤ B) (ha'ne : a' ≠ [])
    (hgB1 : (run_lengths_nat a').head (rl_ne_nil ha'ne) ≠ B - 1)
    (hpp1 : (run_lengths_nat (run_lengths_nat a')).head (rl_ne_nil (rl_ne_nil ha'ne)) ≠ 1) :
    run_lengths_nat ((run_lengths_nat (run_lengths_nat a')).reverse ++ 1 :: (B-1) :: run_lengths_nat a')
      = (run_lengths_nat (run_lengths_nat (run_lengths_nat a'))).reverse
        ++ 1 :: 1 :: run_lengths_nat (run_lengths_nat a') := by
  set p := run_lengths_nat a' with hp
  set pp := run_lengths_nat p with hpp
  have hpne : p ≠ [] := rl_ne_nil ha'ne
  have hppne : pp ≠ [] := rl_ne_nil hpne
  have hpprevne : pp.reverse ≠ [] := by simp [hppne]
  have hgl : pp.reverse.getLast hpprevne ≠ 1 := by
    rw [List.getLast_reverse]; exact hpp1
  rw [rl_append_neq pp.reverse hpprevne 1 ((B-1) :: p) hgl]
  rw [rl_reverse]
  -- second piece rl(1 :: (B-1) :: p)
  obtain ⟨ph, pt, hpt⟩ := List.exists_cons_of_ne_nil hpne
  have hphead : p.head hpne = ph := by
    have hh : p.head? = some ph := by rw [hpt]; rfl
    rw [List.head?_eq_head hpne] at hh
    simp only [Option.some.injEq] at hh; exact hh
  have hB1 : (1:ℕ) ≠ B - 1 := by omega
  rw [rl_cons_new 1 (B-1) p hB1]
  rw [hpt]
  have hphB : B - 1 ≠ ph := by
    rw [← hphead]; exact fun h => hgB1 h.symm
  rw [rl_cons_new (B-1) ph pt hphB]
  rw [← hpt]


theorem rl_repl_head (a' : List ℕ) (B : ℕ) (hB : 1 ≤ B) (ha'ne : a' ≠ [])
    (ha'head : a'.head ha'ne ≠ 1) :
    run_lengths_nat (List.replicate B 1 ++ a') = B :: run_lengths_nat a' := by
  obtain ⟨ah, at', hat⟩ := List.exists_cons_of_ne_nil ha'ne
  have hahead' : ah ≠ 1 := by
    have hh : a'.head? = some ah := by rw [hat]; rfl
    rw [List.head?_eq_head ha'ne] at hh
    simp only [Option.some.injEq] at hh; rw [hh] at ha'head; exact ha'head
  have hAne : List.replicate B 1 ≠ [] := by
    obtain ⟨k, rfl⟩ : ∃ k, B = k+1 := ⟨B-1, by omega⟩; simp
  have hAgl : (List.replicate B 1).getLast hAne = 1 := by
    apply List.eq_of_mem_replicate; exact List.getLast_mem hAne
  rw [hat, rl_append_neq (List.replicate B 1) hAne ah at' (by rw [hAgl]; exact fun h => hahead' h.symm)]
  rw [rl_repl_one B hB, ← hat]; rfl

theorem G3 (X a' : List ℕ) (B : ℕ) (hB : 3 ≤ B) (hXne : X ≠ [])
    (hXhead : X.head hXne = 1)
    (had : run_lengths_nat X = List.replicate B 1 ++ a')
    (ha'ne : a' ≠ [])
    (ha'head : a'.head ha'ne ≠ 1)
    (hgBm1 : (run_lengths_nat a').head (rl_ne_nil ha'ne) ≠ B - 1)
    (hgB : (run_lengths_nat a').head (rl_ne_nil ha'ne) ≠ B)
    (hgB1 : (run_lengths_nat a').head (rl_ne_nil ha'ne) ≠ B + 1)
    (hpp1 : (run_lengths_nat (run_lengths_nat a')).head (rl_ne_nil (rl_ne_nil ha'ne)) ≠ 1) :
    run_lengths_nat (run_lengths_nat (run_lengths_nat ((run_lengths_nat X).reverse ++ X)))
      = (run_lengths_nat (run_lengths_nat (run_lengths_nat (run_lengths_nat X)))).reverse
        ++ run_lengths_nat (run_lengths_nat (run_lengths_nat X)) := by
  have hb : run_lengths_nat (run_lengths_nat X) = B :: run_lengths_nat a' := by
    rw [had]; exact rl_repl_head a' B (by omega) ha'ne ha'head
  have hatail : (run_lengths_nat X).tail = List.replicate (B-1) 1 ++ a' := by
    rw [had]
    obtain ⟨k, hk⟩ : ∃ k, B = k+1 := ⟨B-1, by omega⟩
    subst hk
    simp [List.replicate_succ, Nat.add_sub_cancel]
  have e1 : run_lengths_nat ((run_lengths_nat X).reverse ++ X)
      = (run_lengths_nat a').reverse ++ (B+1) :: (List.replicate (B-1) 1 ++ a') := by
    rw [G3_L1 X a' B (by omega) hXne hXhead had]
    simp only [hb, List.tail_cons, List.head_cons, hatail]
  have e2 : run_lengths_nat (run_lengths_nat ((run_lengths_nat X).reverse ++ X))
      = (run_lengths_nat (run_lengths_nat a')).reverse ++ 1 :: (B-1) :: run_lengths_nat a' := by
    rw [e1]; exact rl_L2 a' B (by omega) ha'ne ha'head hgB1 hgB
  have e3 : run_lengths_nat (run_lengths_nat (run_lengths_nat ((run_lengths_nat X).reverse ++ X)))
      = (run_lengths_nat (run_lengths_nat (run_lengths_nat a'))).reverse
        ++ 1 :: 1 :: run_lengths_nat (run_lengths_nat a') := by
    rw [e2]; exact rl_L3 a' B hB ha'ne hgBm1 hpp1
  have hc : run_lengths_nat (run_lengths_nat (run_lengths_nat X))
      = 1 :: run_lengths_nat (run_lengths_nat a') := by
    rw [hb]
    obtain ⟨ph, pt, hpt⟩ := List.exists_cons_of_ne_nil (rl_ne_nil ha'ne)
    have hphead : (run_lengths_nat a').head (rl_ne_nil ha'ne) = ph := by
      have hh : (run_lengths_nat a').head? = some ph := by rw [hpt]; rfl
      rw [List.head?_eq_head (rl_ne_nil ha'ne)] at hh; simpa using hh
    rw [hpt, rl_cons_new B ph pt (by rw [← hphead]; exact fun h => hgB h.symm), ← hpt]
  have hd : run_lengths_nat (run_lengths_nat (run_lengths_nat (run_lengths_nat X)))
      = 1 :: run_lengths_nat (run_lengths_nat (run_lengths_nat a')) := by
    rw [hc]
    obtain ⟨pph, ppt, hppt⟩ := List.exists_cons_of_ne_nil (rl_ne_nil (rl_ne_nil ha'ne))
    have hpphead : (run_lengths_nat (run_lengths_nat a')).head (rl_ne_nil (rl_ne_nil ha'ne)) = pph := by
      have hh : (run_lengths_nat (run_lengths_nat a')).head? = some pph := by rw [hppt]; rfl
      rw [List.head?_eq_head (rl_ne_nil (rl_ne_nil ha'ne))] at hh; simpa using hh
    rw [hppt, rl_cons_new 1 pph ppt (by rw [← hpphead]; exact fun h => hpp1 h.symm), ← hppt]
  rw [e3, hd, hc]
  simp [List.reverse_cons]


-- ============ A381587_T and prefix/suffix stability ============
set_option maxRecDepth 1000000

private def A381587_T : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 =>
    let prev_T := A381587_T (k + 3)
    run_lengths_nat prev_T.reverse ++ prev_T

theorem rl_nil : run_lengths_nat [] = [] := by conv_lhs => rw [run_lengths_nat]

theorem T_rec (n : ℕ) (hn : 3 ≤ n) :
    A381587_T (n+1) = run_lengths_nat ((A381587_T n).reverse) ++ A381587_T n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+3 := ⟨n-3, by omega⟩
  rfl

def FP : List ℕ := [1,3,1,3,1,3,1,1,1,5,1,1,1,1,1,7,1,3,1,1,1,1,1,7]
def Sfx : List ℕ := [7,1,1,1,1,1,3,1,7,1,1,1,1,1,5,1,1,1,3,1,3,1,3,1]

theorem T_suffix : ∀ m, 5 ≤ m → ∃ W, A381587_T m = W ++ [1,2] := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ p ih =>
    intro hm
    rcases Nat.lt_or_ge 5 (p+1) with hp | hp
    · obtain ⟨W, hW⟩ := ih (by omega)
      refine ⟨run_lengths_nat ((A381587_T p).reverse) ++ W, ?_⟩
      rw [T_rec p (by omega)]
      nth_rewrite 2 [hW]
      rw [List.append_assoc]
    · have : p = 4 := by omega
      subst this
      refine ⟨[1,1], ?_⟩
      simp only [A381587_T]; simp [run_lengths_nat, rl_nil, List.reverse_cons]

theorem T_ne_nil (m : ℕ) (hm : 3 ≤ m) : A381587_T m ≠ [] := by
  rcases Nat.lt_or_ge m 5 with h | h
  · interval_cases m <;> · simp only [A381587_T]; simp [run_lengths_nat, rl_nil, List.reverse_cons]
  · obtain ⟨W, hW⟩ := T_suffix m h; rw [hW]; simp

theorem inv : ∀ n, 12 ≤ n →
    (∃ D, A381587_T n = FP ++ D) ∧
    (∃ M, M ≠ [] ∧ run_lengths_nat (A381587_T n) = M ++ Sfx) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ p ih =>
    intro hm
    rcases Nat.lt_or_ge 12 (p+1) with hp | hp
    · -- p ≥ 12
      obtain ⟨⟨D, hD⟩, ⟨M, hMne, hM⟩⟩ := ih (by omega)
      have hTp_ne : A381587_T p ≠ [] := by rw [hD]; simp [FP]
      have hTrec := T_rec p (by omega)
      have hrlrev : run_lengths_nat ((A381587_T p).reverse) = (run_lengths_nat (A381587_T p)).reverse := rl_reverse _
      have hTp : A381587_T p = 1 :: (List.tail FP ++ D) := by rw [hD]; rfl
      -- prefix part
      have hpre : ∃ D', A381587_T (p+1) = FP ++ D' := by
        refine ⟨M.reverse ++ A381587_T p, ?_⟩
        rw [hTrec, hrlrev, hM, List.reverse_append,
            show Sfx.reverse = FP from by decide, List.append_assoc]
      refine ⟨hpre, ?_⟩
      -- suffix part
      have hrlfold : run_lengths_nat (1 :: (List.tail FP ++ D)) = M ++ Sfx := by
        rw [show (1 :: (List.tail FP ++ D)) = A381587_T p from hTp.symm]; exact hM
      have hhead? : (run_lengths_nat (A381587_T p)).head? = some 1 := by
        rw [hTp, show (1 :: (List.tail FP ++ D)) = 1 :: 3 :: (List.drop 2 FP ++ D) from rfl,
            rl_cons_new 1 3 _ (by decide)]
        rfl
      have hAne : (run_lengths_nat (A381587_T p)).reverse ≠ [] := by simp [rl_ne_nil hTp_ne]
      have hlast : (run_lengths_nat (A381587_T p)).reverse.getLast hAne = 1 := by
        rw [List.getLast_reverse]
        have h := hhead?
        rw [List.head?_eq_head (rl_ne_nil hTp_ne)] at h
        simpa using h
      have hTp_appform : A381587_T (p+1)
          = (run_lengths_nat (A381587_T p)).reverse ++ 1 :: (List.tail FP ++ D) := by
        rw [hTrec, hrlrev, hTp]
      obtain ⟨m0, ms, hMcons⟩ := List.exists_cons_of_ne_nil hMne
      have htail_eq : (run_lengths_nat (1 :: (List.tail FP ++ D))).tail = ms ++ Sfx := by
        rw [hrlfold, hMcons]; rfl
      refine ⟨(run_lengths_nat ((run_lengths_nat (A381587_T p)).reverse)).dropLast
          ++ ((run_lengths_nat ((run_lengths_nat (A381587_T p)).reverse)).getLast (rl_ne_nil hAne)
              + (run_lengths_nat (1 :: (List.tail FP ++ D))).head (rl_ne_nil (by simp))) :: ms,
          by simp, ?_⟩
      rw [hTp_appform, rl_append_eq _ hAne 1 (List.tail FP ++ D) hlast, htail_eq,
          List.append_assoc, List.cons_append]
    · -- p+1 = 12
      have : p + 1 = 12 := by omega
      rw [this]
      refine ⟨⟨(A381587_T 12).drop 24, ?_⟩, (run_lengths_nat (A381587_T 12)).take 30, ?_, ?_⟩
      · conv_lhs => rw [← List.take_append_drop 24 (A381587_T 12)]
        congr 1
        simp only [A381587_T]; simp [run_lengths_nat, rl_nil, List.reverse_cons, FP]
      · -- take 30 ≠ []
        intro hc
        have : (run_lengths_nat (A381587_T 12)).length = 30 → False := by
          intro; simp_all
        simp only [A381587_T] at hc
        simp [run_lengths_nat, rl_nil, List.reverse_cons] at hc
      · conv_lhs => rw [← List.take_append_drop 30 (run_lengths_nat (A381587_T 12))]
        congr 1
        simp only [A381587_T]; simp [run_lengths_nat, rl_nil, List.reverse_cons, Sfx]

def FP23 : List ℕ := [1,3,1,3,1,3,1,1,1,5,1,1,1,1,1,7,1,3,1,1,1,1,1]

theorem G3_T (n : ℕ) (hn : 12 ≤ n) :
    run_lengths_nat (run_lengths_nat (run_lengths_nat (A381587_T (n+1))))
      = (run_lengths_nat (run_lengths_nat (run_lengths_nat (run_lengths_nat (A381587_T n))))).reverse
        ++ run_lengths_nat (run_lengths_nat (run_lengths_nat (A381587_T n))) := by
  obtain ⟨⟨D, hD⟩, _⟩ := inv n hn
  set E := run_lengths_nat (7 :: D) with hEdef
  set a' := [3,1,5,1,1,1,5] ++ E with ha'def
  have hTne : A381587_T n ≠ [] := T_ne_nil n (by omega)
  -- rl T_n
  have hrlTn : run_lengths_nat (A381587_T n) = [1,1,1,1,1,1,3,1,5,1,1,1,5] ++ E := by
    rw [hD, show FP ++ D = FP23 ++ 7 :: D from by rw [show FP = FP23 ++ [7] from by decide, List.append_assoc]; rfl]
    rw [rl_append_neq FP23 (by decide) 7 D (by decide)]
    rw [show run_lengths_nat FP23 = [1,1,1,1,1,1,3,1,5,1,1,1,5] from by simp [FP23, run_lengths_nat, rl_nil]]
  have had : run_lengths_nat (A381587_T n) = List.replicate 6 1 ++ a' := by
    rw [hrlTn, ha'def]; rfl
  have ha'ne : a' ≠ [] := by rw [ha'def]; simp
  have hrla' : run_lengths_nat a' = [1,1,1,3] ++ run_lengths_nat (5 :: E) := by
    rw [ha'def, show ([3,1,5,1,1,1,5]:List ℕ) ++ E = [3,1,5,1,1,1] ++ 5 :: E from rfl]
    rw [rl_append_neq [3,1,5,1,1,1] (by decide) 5 E (by decide)]
    rw [show run_lengths_nat [3,1,5,1,1,1] = [1,1,1,3] from by simp [run_lengths_nat, rl_nil]]
  have hrl2a' : run_lengths_nat (run_lengths_nat a') = [3] ++ run_lengths_nat (3 :: run_lengths_nat (5 :: E)) := by
    rw [hrla', show ([1,1,1,3]:List ℕ) ++ run_lengths_nat (5 :: E) = [1,1,1] ++ 3 :: run_lengths_nat (5 :: E) from rfl]
    rw [rl_append_neq [1,1,1] (by decide) 3 (run_lengths_nat (5 :: E)) (by decide)]
    rw [show run_lengths_nat [1,1,1] = [3] from by simp [run_lengths_nat, rl_nil]]
  have ha'head : a'.head ha'ne ≠ 1 := by
    have h : a'.head? = some 3 := by rw [ha'def]; rfl
    rw [List.head?_eq_head ha'ne] at h; simp only [Option.some.injEq] at h; omega
  have ghead : (run_lengths_nat a').head (rl_ne_nil ha'ne) = 1 := by
    have h : (run_lengths_nat a').head? = some 1 := by rw [hrla']; rfl
    rw [List.head?_eq_head (rl_ne_nil ha'ne)] at h; simpa using h
  have pphead : (run_lengths_nat (run_lengths_nat a')).head (rl_ne_nil (rl_ne_nil ha'ne)) = 3 := by
    have h : (run_lengths_nat (run_lengths_nat a')).head? = some 3 := by rw [hrl2a']; rfl
    rw [List.head?_eq_head (rl_ne_nil (rl_ne_nil ha'ne))] at h; simpa using h
  have hXhead : (A381587_T n).head hTne = 1 := by
    have h : (A381587_T n).head? = some 1 := by rw [hD]; simp [FP]
    rw [List.head?_eq_head hTne] at h; simpa using h
  have hTeq : A381587_T (n+1) = (run_lengths_nat (A381587_T n)).reverse ++ A381587_T n := by
    rw [T_rec n (by omega), rl_reverse]
  rw [hTeq]
  exact G3 (A381587_T n) a' 6 (by norm_num) hTne hXhead had ha'ne ha'head
    (by rw [ghead]; decide) (by rw [ghead]; decide) (by rw [ghead]; decide) (by rw [pphead]; decide)

theorem keyFromKeyPrime (n : ℕ) (hn : 9 ≤ n)
    (hkp : run_lengths_nat (run_lengths_nat (run_lengths_nat (A381587_T n))) = (A381587_T (n-4)).dropLast ++ [6]) :
    run_lengths_nat (run_lengths_nat (run_lengths_nat (run_lengths_nat (A381587_T n))))
      = run_lengths_nat (A381587_T (n-4)) := by
  obtain ⟨W, hW⟩ := T_suffix (n-4) (by omega)
  have hdl : (A381587_T (n-4)).dropLast = W ++ [1] := by rw [hW]; simp
  have hne1 : W ++ [1] ≠ [] := by simp
  have hgl : (W++[1]).getLast hne1 = 1 := List.getLast_append_singleton W
  have key_eq : ∀ x : ℕ, x ≠ 1 → run_lengths_nat ((W++[1]) ++ [x]) = run_lengths_nat (W++[1]) ++ [1] := by
    intro x hx
    rw [rl_append_neq (W++[1]) hne1 x [] (by rw [hgl]; omega), rl_single]
  have hreassoc : (W:List ℕ)++[1,2] = (W++[1])++[2] := by simp [List.append_assoc]
  rw [hkp, hdl, hW, hreassoc, key_eq 6 (by omega), key_eq 2 (by omega)]

theorem keyPrime : ∀ n, 12 ≤ n →
    run_lengths_nat (run_lengths_nat (run_lengths_nat (A381587_T n))) = (A381587_T (n-4)).dropLast ++ [6] := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ p ih =>
    intro hm
    rcases Nat.lt_or_ge 12 (p+1) with hp | hp
    · have ihp := ih (by omega)
      have hkey := keyFromKeyPrime p (by omega) ihp
      have hg3 := G3_T p (by omega)
      have hTpne : A381587_T (p-4) ≠ [] := T_ne_nil (p-4) (by omega)
      have hTp3 : A381587_T ((p+1)-4) = (run_lengths_nat (A381587_T (p-4))).reverse ++ A381587_T (p-4) := by
        rw [show (p+1)-4 = (p-4)+1 from by omega, T_rec (p-4) (by omega), rl_reverse]
      rw [hg3, hkey, ihp, hTp3, List.dropLast_append_of_ne_nil hTpne, List.append_assoc]
    · have h12 : p + 1 = 12 := by omega
      rw [h12]
      simp only [A381587_T]
      simp [run_lengths_nat, rl_nil, List.reverse_cons]

theorem R1 (n : ℕ) (hn : 3 ≤ n) :
    (A381587_T (n+1)).length = (A381587_T n).length + (run_lengths_nat (A381587_T n)).length := by
  rw [T_rec n hn, List.length_append, rl_reverse, List.length_reverse]; omega

theorem R2 (n : ℕ) (hn : 12 ≤ n) :
    (run_lengths_nat (A381587_T (n+1))).length
      = (run_lengths_nat (run_lengths_nat (A381587_T n))).length + (run_lengths_nat (A381587_T n)).length - 1 := by
  obtain ⟨⟨D, hD⟩, _⟩ := inv n hn
  have hTnne : A381587_T n ≠ [] := T_ne_nil n (by omega)
  have hTn : A381587_T n = 1 :: (List.tail FP ++ D) := by rw [hD]; rfl
  have hAne : (run_lengths_nat (A381587_T n)).reverse ≠ [] := by simp [rl_ne_nil hTnne]
  have hhead? : (run_lengths_nat (A381587_T n)).head? = some 1 := by
    rw [hTn, show (1 :: (List.tail FP ++ D)) = 1 :: 3 :: (List.drop 2 FP ++ D) from rfl,
        rl_cons_new 1 3 _ (by decide)]; rfl
  have hlast : (run_lengths_nat (A381587_T n)).reverse.getLast hAne = 1 := by
    rw [List.getLast_reverse]
    have h := hhead?; rw [List.head?_eq_head (rl_ne_nil hTnne)] at h; simpa using h
  have hTeq : A381587_T (n+1) = (run_lengths_nat (A381587_T n)).reverse ++ 1 :: (List.tail FP ++ D) := by
    rw [T_rec n (by omega), rl_reverse]; nth_rewrite 2 [hTn]; rfl
  have key : nruns (A381587_T (n+1))
      = nruns (run_lengths_nat (A381587_T n)) + nruns (A381587_T n) - 1 := by
    rw [hTeq, nruns_append_cons 1 (List.tail FP ++ D) _ hAne, hlast, if_pos rfl, nruns_reverse, ← hTn]
  exact key

theorem rl_all_pos (L : List ℕ) : ∀ x ∈ run_lengths_nat L, 1 ≤ x := by
  induction L using run_lengths_nat.induct with
  | case1 => simp [run_lengths_nat]
  | case2 h tail rp rest ih =>
    rw [run_lengths_nat]; intro x hx
    rcases List.mem_cons.mp hx with h1 | h2
    · subst h1
      show 1 ≤ ((h::tail).takeWhile (fun y => y = h)).length
      rw [List.takeWhile_cons]; simp
    · exact ih x h2

theorem length_le_sum (L : List ℕ) (h : ∀ x ∈ L, 1 ≤ x) : L.length ≤ L.sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.length_cons, List.sum_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    omega

theorem nruns_le_length (L : List ℕ) : (run_lengths_nat L).length ≤ L.length := by
  rw [← rln_sum L]; exact length_le_sum _ (rl_all_pos L)

theorem Qval (m : ℕ) (hm : 12 ≤ m) :
    (run_lengths_nat (run_lengths_nat (A381587_T m))).length = (A381587_T (m-4)).dropLast.sum + 6 := by
  have h1 : (run_lengths_nat (run_lengths_nat (A381587_T m))).length
      = (run_lengths_nat (run_lengths_nat (run_lengths_nat (A381587_T m)))).sum := (rln_sum _).symm
  rw [h1, keyPrime m hm, List.sum_append]; simp

theorem R3 (n : ℕ) (hn : 8 ≤ n) :
    (run_lengths_nat (run_lengths_nat (A381587_T (n+5)))).length
      = (run_lengths_nat (run_lengths_nat (A381587_T (n+4)))).length + (A381587_T n).length := by
  rw [Qval (n+5) (by omega), Qval (n+4) (by omega),
      show (n+5)-4 = n+1 from by omega, show (n+4)-4 = n from by omega]
  have hTnne : A381587_T n ≠ [] := T_ne_nil n (by omega)
  have hTrec : A381587_T (n+1) = (run_lengths_nat (A381587_T n)).reverse ++ A381587_T n := by
    rw [T_rec n (by omega), rl_reverse]
  rw [hTrec, List.dropLast_append_of_ne_nil hTnne, List.sum_append, List.sum_reverse, rln_sum]
  omega

theorem T_pos : ∀ n, ∀ x ∈ A381587_T n, 1 ≤ x := by
  intro n
  induction n with
  | zero => simp [A381587_T]
  | succ p ih =>
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p <;> (intro x hx; simp only [A381587_T] at hx; simp at hx; omega)
    · intro x hx
      rw [T_rec p h] at hx
      rcases List.mem_append.mp hx with h1 | h2
      · exact rl_all_pos _ x h1
      · exact ih x h2

def A381358 (n : ℕ) : ℕ := (A381587_T n).sum

theorem a_rec (n : ℕ) (hn : 3 ≤ n) : A381358 (n+1) = (A381587_T n).length + A381358 n := by
  unfold A381358
  rw [T_rec n hn, List.sum_append, rl_reverse, List.sum_reverse, rln_sum]
open Filter
open List Nat Filter

/-! Abstract analysis: from a positive 3-variable linear system with bounded perturbation,
derive two-sided geometric bounds and the limit of the n-th root. -/

namespace Dev

/-- The eigenvalue: a real root > 1 of x^4 (x-1)^3 = 1. -/
theorem exists_lambda : ∃ l : ℝ, 1 < l ∧ l < 2 ∧ l^4 * (l-1)^3 = 1 := by
  have hcont : ContinuousOn (fun x : ℝ => x^4 * (x-1)^3 - 1) (Set.Icc 1 2) := by fun_prop
  have h1 : (fun x : ℝ => x^4 * (x-1)^3 - 1) 1 ≤ 0 := by norm_num
  have h2 : (0:ℝ) ≤ (fun x : ℝ => x^4 * (x-1)^3 - 1) 2 := by norm_num
  obtain ⟨c, hc, hroot⟩ := intermediate_value_Icc (by norm_num) hcont (Set.mem_Icc.2 ⟨h1, h2⟩)
  refine ⟨c, ?_, ?_, by linarith [hroot]⟩
  · rcases hc.1.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hroot; norm_num at hroot
  · rcases hc.2.lt_or_eq with h | h
    · exact h
    · exfalso; rw [h] at hroot; norm_num at hroot

section Analysis
variable (lam : ℝ) (ell r q : ℕ → ℝ)

/-- The linear functional (left eigenvector applied to the state). -/
noncomputable def Y (n : ℕ) : ℝ :=
  ell (n+4) + (lam-1)*ell (n+3) + lam*(lam-1)*ell (n+2) + lam^2*(lam-1)*ell (n+1)
    + lam^3*(lam-1)*ell n + (1/(lam-1)) * r (n+4) + lam^4*(lam-1) * q (n+4)

variable {lam ell r q}

/-- Key step: Y satisfies an affine recurrence Y(n+1) = lam * Y n - 1/(lam-1). -/
theorem Y_step (hlam1 : 1 < lam) (key : lam^4*(lam-1)^3 = 1) {N n : ℕ} (hn : N ≤ n)
    (hR1 : ∀ m, N ≤ m → ell (m+1) = ell m + r m)
    (hR2 : ∀ m, N ≤ m → r (m+1) = r m + q m - 1)
    (hR3 : ∀ m, N ≤ m → q (m+5) = q (m+4) + ell m) :
    Y lam ell r q (n+1) = lam * Y lam ell r q n - 1/(lam-1) := by
  have hlne : lam - 1 ≠ 0 := by linarith
  have e1 : ell (n+5) = ell (n+4) + r (n+4) := hR1 (n+4) (by omega)
  have e2 : r (n+5) = r (n+4) + q (n+4) - 1 := hR2 (n+4) (by omega)
  have e3 : q (n+5) = q (n+4) + ell n := hR3 n hn
  show ell (n+5) + (lam-1)*ell (n+4) + lam*(lam-1)*ell (n+3) + lam^2*(lam-1)*ell (n+2)
        + lam^3*(lam-1)*ell (n+1) + (1/(lam-1)) * r (n+5) + lam^4*(lam-1) * q (n+5)
       = lam * (ell (n+4) + (lam-1)*ell (n+3) + lam*(lam-1)*ell (n+2) + lam^2*(lam-1)*ell (n+1)
        + lam^3*(lam-1)*ell n + (1/(lam-1)) * r (n+4) + lam^4*(lam-1) * q (n+4)) - 1/(lam-1)
  rw [e1, e2, e3]
  field_simp
  linear_combination (-(q (n+4))) * key

/-- Closed form: Y(N+k) = lam^k * (Y N - c0) + c0, with c0 = 1/(lam-1)^2. -/
theorem Y_closed (hlam1 : 1 < lam) (key : lam^4*(lam-1)^3 = 1) {N : ℕ}
    (hR1 : ∀ m, N ≤ m → ell (m+1) = ell m + r m)
    (hR2 : ∀ m, N ≤ m → r (m+1) = r m + q m - 1)
    (hR3 : ∀ m, N ≤ m → q (m+5) = q (m+4) + ell m) (k : ℕ) :
    Y lam ell r q (N+k) - 1/(lam-1)^2 = lam^k * (Y lam ell r q N - 1/(lam-1)^2) := by
  have hlne : lam - 1 ≠ 0 := by linarith
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := Y_step hlam1 key (N := N) (n := N+k) (by omega) hR1 hR2 hR3
    have hY : Y lam ell r q (N+(k+1)) = lam * Y lam ell r q (N+k) - 1/(lam-1) := by
      rw [show N+(k+1) = (N+k)+1 from by ring]; exact hstep
    rw [hY, pow_succ]
    have ihv : Y lam ell r q (N+k) = lam^k * (Y lam ell r q N - 1/(lam-1)^2) + 1/(lam-1)^2 := by
      linarith [ih]
    rw [ihv]
    field_simp
    ring

/-- Monotonicity helper. -/
theorem ell_mono_add {N : ℕ} (hmono : ∀ m, N ≤ m → ell m ≤ ell (m+1))
    (a : ℕ) (ha : N ≤ a) : ∀ d, ell a ≤ ell (a+d) := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    calc ell a ≤ ell (a+d) := ih
      _ ≤ ell (a+d+1) := hmono (a+d) (by omega)

/-- Main two-sided geometric bound for ell. -/
theorem ell_geom_bounds (hlam1 : 1 < lam) (hlam2 : lam < 2) (key : lam^4*(lam-1)^3 = 1)
    {N : ℕ}
    (hR1 : ∀ m, N ≤ m → ell (m+1) = ell m + r m)
    (hR2 : ∀ m, N ≤ m → r (m+1) = r m + q m - 1)
    (hR3 : ∀ m, N ≤ m → q (m+5) = q (m+4) + ell m)
    (hpos : ∀ m, N ≤ m → 0 ≤ q m ∧ q m ≤ r m ∧ r m ≤ ell m)
    (hmono : ∀ m, N ≤ m → ell m ≤ ell (m+1))
    (hbase : (17:ℝ) ≤ ell (N+4)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m, N+4 ≤ m → c * lam^m ≤ ell m ∧ ell m ≤ C * lam^m := by
  have hlne : (0:ℝ) < lam - 1 := by linarith
  have hl0 : (0:ℝ) < lam := by linarith
  set c0 : ℝ := 1/(lam-1)^2 with hc0def
  -- c0 < 16
  have hsq : (lam-1)^2 = 1/(lam^4*(lam-1)) := by
    have : lam^4 * (lam-1) ≠ 0 := by positivity
    field_simp
    linear_combination key
  have c0pos : 0 < c0 := by rw [hc0def]; positivity
  have hlam2sq : lam^2 < 4 := by nlinarith
  have hlam4 : lam^4 < 16 := by nlinarith [hlam2sq, sq_nonneg lam]
  have hprod : lam^4*(lam-1) < 16 := by nlinarith [hlam4, hlne, (show lam-1<1 by linarith), hl0]
  have hprodpos : (0:ℝ) < lam^4*(lam-1) := by positivity
  have hsqlb : (lam-1)^2 > 1/16 := by
    rw [hsq, gt_iff_lt]; exact one_div_lt_one_div_of_lt hprodpos hprod
  have hc0 : c0 < 16 := by
    rw [hc0def]
    calc 1/(lam-1)^2 < 1/(1/16) := one_div_lt_one_div_of_lt (by norm_num) hsqlb
      _ = 16 := by norm_num
  -- Y N ≥ ell (N+4)
  have hellnn : ∀ m, N ≤ m → 0 ≤ ell m := fun m hm => le_trans (le_trans (hpos m hm).1 (hpos m hm).2.1) (hpos m hm).2.2
  have hYN_ge : ell (N+4) ≤ Y lam ell r q N := by
    simp only [Y]
    have h3 := hellnn (N+3) (by omega)
    have h2 := hellnn (N+2) (by omega)
    have h1 := hellnn (N+1) (by omega)
    have h0 := hellnn N (by omega)
    have hr := (hpos (N+4) (by omega)).2.2
    have hq := (hpos (N+4) (by omega)).1
    have hrnn : 0 ≤ r (N+4) := le_trans hq (hpos (N+4) (by omega)).2.1
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ lam-1) h3,
      mul_nonneg (by positivity : (0:ℝ) ≤ lam*(lam-1)) h2,
      mul_nonneg (by positivity : (0:ℝ) ≤ lam^2*(lam-1)) h1,
      mul_nonneg (by positivity : (0:ℝ) ≤ lam^3*(lam-1)) h0,
      mul_nonneg (by positivity : (0:ℝ) ≤ 1/(lam-1)) hrnn,
      mul_nonneg (by positivity : (0:ℝ) ≤ lam^4*(lam-1)) hq]
  set d : ℝ := Y lam ell r q N - c0 with hddef
  have hd : 0 < d := by rw [hddef]; linarith [hYN_ge, hbase, hc0]
  -- S coefficient sum
  set S : ℝ := 1 + (lam-1) + lam*(lam-1) + lam^2*(lam-1) + lam^3*(lam-1) + 1/(lam-1) + lam^4*(lam-1) with hSdef
  have hS : 0 < S := by rw [hSdef]; positivity
  refine ⟨d/(S*lam^(N+4)), (d+c0)/lam^(N+4), by positivity, by positivity, ?_⟩
  intro m hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 4 := ⟨m-4, by omega⟩
  have hnN : N ≤ n := by omega
  -- Y n closed form
  have hclosed : Y lam ell r q n = lam^(n-N) * d + c0 := by
    have := Y_closed hlam1 key hR1 hR2 hR3 (n-N)
    rw [show N + (n-N) = n from by omega] at this
    rw [hddef]; linarith [this]
  have hpow1 : (1:ℝ) ≤ lam^(n-N) := one_le_pow₀ (le_of_lt hlam1)
  have hpowsplit : lam^(n+4) = lam^(N+4) * lam^(n-N) := by
    rw [← pow_add]; congr 1; omega
  have hYpos : 0 < Y lam ell r q n := by rw [hclosed]; positivity
  -- ell (n+4) ≤ Y n
  have hupper1 : ell (n+4) ≤ Y lam ell r q n := by
    simp only [Y]
    have h3 := hellnn (n+3) (by omega)
    have h2 := hellnn (n+2) (by omega)
    have h1 := hellnn (n+1) (by omega)
    have h0 := hellnn n (by omega)
    have hq := (hpos (n+4) (by omega)).1
    have hrnn : 0 ≤ r (n+4) := le_trans hq (hpos (n+4) (by omega)).2.1
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ lam-1) h3,
      mul_nonneg (by positivity : (0:ℝ) ≤ lam*(lam-1)) h2,
      mul_nonneg (by positivity : (0:ℝ) ≤ lam^2*(lam-1)) h1,
      mul_nonneg (by positivity : (0:ℝ) ≤ lam^3*(lam-1)) h0,
      mul_nonneg (by positivity : (0:ℝ) ≤ 1/(lam-1)) hrnn,
      mul_nonneg (by positivity : (0:ℝ) ≤ lam^4*(lam-1)) hq]
  -- Y n ≤ S * ell (n+4)
  have hlower1 : Y lam ell r q n ≤ S * ell (n+4) := by
    have m3 : ell (n+3) ≤ ell (n+4) := by have := ell_mono_add hmono (n+3) (by omega) 1; simpa using this
    have m2 : ell (n+2) ≤ ell (n+4) := by have := ell_mono_add hmono (n+2) (by omega) 2; simpa using this
    have m1 : ell (n+1) ≤ ell (n+4) := by have := ell_mono_add hmono (n+1) (by omega) 3; simpa using this
    have m0 : ell n ≤ ell (n+4) := by have := ell_mono_add hmono n (by omega) 4; simpa using this
    have hrle : r (n+4) ≤ ell (n+4) := (hpos (n+4) (by omega)).2.2
    have hqle : q (n+4) ≤ ell (n+4) := le_trans (hpos (n+4) (by omega)).2.1 hrle
    have expand : S * ell (n+4) = ell (n+4) + (lam-1)*ell (n+4) + lam*(lam-1)*ell (n+4)
        + lam^2*(lam-1)*ell (n+4) + lam^3*(lam-1)*ell (n+4) + (1/(lam-1))*ell (n+4)
        + lam^4*(lam-1)*ell (n+4) := by rw [hSdef]; ring
    rw [expand]
    simp only [Y]
    linarith [mul_le_mul_of_nonneg_left m3 (by positivity : (0:ℝ) ≤ lam-1),
      mul_le_mul_of_nonneg_left m2 (by positivity : (0:ℝ) ≤ lam*(lam-1)),
      mul_le_mul_of_nonneg_left m1 (by positivity : (0:ℝ) ≤ lam^2*(lam-1)),
      mul_le_mul_of_nonneg_left m0 (by positivity : (0:ℝ) ≤ lam^3*(lam-1)),
      mul_le_mul_of_nonneg_left hrle (by positivity : (0:ℝ) ≤ 1/(lam-1)),
      mul_le_mul_of_nonneg_left hqle (by positivity : (0:ℝ) ≤ lam^4*(lam-1))]
  constructor
  · -- lower: d/(S lam^(N+4)) * lam^(n+4) ≤ ell(n+4)
    have hYlb : lam^(n-N) * d ≤ Y lam ell r q n := by rw [hclosed]; linarith [c0pos]
    have : d/(S*lam^(N+4)) * lam^(n+4) ≤ Y lam ell r q n / S := by
      rw [hpowsplit]
      rw [div_mul_eq_mul_div, le_div_iff₀ hS]
      have : d * (lam^(N+4)*lam^(n-N)) / (S*lam^(N+4)) * S = d * lam^(n-N) := by
        field_simp
      rw [this]
      calc d * lam^(n-N) = lam^(n-N)*d := by ring
        _ ≤ Y lam ell r q n := hYlb
    calc d/(S*lam^(N+4)) * lam^(n+4) ≤ Y lam ell r q n / S := this
      _ ≤ ell (n+4) := by rw [div_le_iff₀ hS]; linarith [hlower1]
  · -- upper: ell(n+4) ≤ (d+c0)/lam^(N+4) * lam^(n+4)
    have hYub : Y lam ell r q n ≤ lam^(n-N) * (d+c0) := by
      have hmul : c0 ≤ lam^(n-N) * c0 := le_mul_of_one_le_left c0pos.le hpow1
      have hexp : lam^(n-N) * (d+c0) = lam^(n-N) * d + lam^(n-N) * c0 := by ring
      rw [hclosed, hexp]; linarith [hmul]
    calc ell (n+4) ≤ Y lam ell r q n := hupper1
      _ ≤ lam^(n-N) * (d+c0) := hYub
      _ = (d+c0)/lam^(N+4) * lam^(n+4) := by rw [hpowsplit]; field_simp; try ring

/-- `a^(1/n) → 1` for `a > 0`. -/
theorem tendsto_rpow_inv_one {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => a^((n:ℝ)⁻¹)) atTop (nhds 1) := by
  have h0 : Tendsto (fun n : ℕ => Real.log a * (n:ℝ)⁻¹) atTop (nhds 0) := by
    have hb : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_nhds_zero_nat
    have := (tendsto_const_nhds (x := Real.log a)).mul hb
    simpa using this
  have hcont : Tendsto (fun x : ℝ => Real.exp x) (nhds 0) (nhds 1) := by
    have := Real.continuous_exp.tendsto 0
    simpa using this
  have := hcont.comp h0
  refine this.congr (fun n => ?_)
  simp only [Function.comp]
  rw [Real.rpow_def_of_pos ha]

/-- Geometric two-sided bounds give the limit of the n-th root. -/
theorem tendsto_rpow_of_geom_bounds {lam c C : ℝ} (hlam : 1 < lam) (hc : 0 < c) (hC : 0 < C)
    {M : ℕ} {f : ℕ → ℝ} (hb : ∀ m, M ≤ m → c * lam^m ≤ f m ∧ f m ≤ C * lam^m) :
    Tendsto (fun n : ℕ => (f n)^((n:ℝ)⁻¹)) atTop (nhds lam) := by
  have hl0 : (0:ℝ) ≤ lam := by linarith
  have hlow : Tendsto (fun n : ℕ => c^((n:ℝ)⁻¹) * lam) atTop (nhds lam) := by
    have := (tendsto_rpow_inv_one hc).mul_const lam
    simpa using this
  have hupp : Tendsto (fun n : ℕ => C^((n:ℝ)⁻¹) * lam) atTop (nhds lam) := by
    have := (tendsto_rpow_inv_one hC).mul_const lam
    simpa using this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [eventually_ge_atTop (max M 1)] with n hn
    have hnM : M ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hfpos : 0 < f n := lt_of_lt_of_le (by positivity) (hb n hnM).1
    -- c^(1/n) * lam = (c * lam^n)^(1/n) ≤ (f n)^(1/n)
    have hrw : c^((n:ℝ)⁻¹) * lam = (c * lam^n)^((n:ℝ)⁻¹) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      rw [← Real.rpow_natCast lam n, ← Real.rpow_mul hl0]
      rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (by omega))]
      simp
    rw [hrw]
    exact Real.rpow_le_rpow (by positivity) (hb n hnM).1 (by positivity)
  · filter_upwards [eventually_ge_atTop (max M 1)] with n hn
    have hnM : M ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hfpos : 0 ≤ f n := le_trans (by positivity) (hb n hnM).1
    have hrw : C^((n:ℝ)⁻¹) * lam = (C * lam^n)^((n:ℝ)⁻¹) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      rw [← Real.rpow_natCast lam n, ← Real.rpow_mul hl0]
      rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (by omega))]
      simp
    rw [hrw]
    exact Real.rpow_le_rpow hfpos (hb n hnM).2 (by positivity)

end Analysis

end Dev

theorem A381358_limit_exists :
    ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) := by
  obtain ⟨lam, hlam1, hlam2, hkey⟩ := Dev.exists_lambda
  set ell : ℕ → ℝ := fun m => ((A381587_T m).length : ℝ) with hell
  set r : ℕ → ℝ := fun m => ((run_lengths_nat (A381587_T m)).length : ℝ) with hr
  set q : ℕ → ℝ := fun m => ((run_lengths_nat (run_lengths_nat (A381587_T m))).length : ℝ) with hq
  have hR1 : ∀ m, 12 ≤ m → ell (m+1) = ell m + r m := by
    intro m hm; simp only [hell, hr]; exact_mod_cast R1 m (by omega)
  have hR2 : ∀ m, 12 ≤ m → r (m+1) = r m + q m - 1 := by
    intro m hm; simp only [hell, hr, hq]
    have hRpos : 1 ≤ (run_lengths_nat (A381587_T m)).length := by
      obtain ⟨a,t,hc⟩ := List.exists_cons_of_ne_nil (T_ne_nil m (by omega))
      rw [hc]; exact nruns_cons_pos a t
    have h2 : (run_lengths_nat (A381587_T (m+1))).length + 1
        = (run_lengths_nat (run_lengths_nat (A381587_T m))).length + (run_lengths_nat (A381587_T m)).length := by
      have := R2 m hm; omega
    have h2c : ((run_lengths_nat (A381587_T (m+1))).length:ℝ) + 1
        = ((run_lengths_nat (run_lengths_nat (A381587_T m))).length:ℝ) + ((run_lengths_nat (A381587_T m)).length:ℝ) := by
      exact_mod_cast h2
    linarith
  have hR3 : ∀ m, 12 ≤ m → q (m+5) = q (m+4) + ell m := by
    intro m hm; simp only [hq, hell]; exact_mod_cast R3 m (by omega)
  have hpos : ∀ m, 12 ≤ m → 0 ≤ q m ∧ q m ≤ r m ∧ r m ≤ ell m := by
    intro m hm; simp only [hell, hr, hq]
    refine ⟨by positivity, ?_, ?_⟩
    · exact_mod_cast nruns_le_length (run_lengths_nat (A381587_T m))
    · exact_mod_cast nruns_le_length (A381587_T m)
  have hmono : ∀ m, 12 ≤ m → ell m ≤ ell (m+1) := by
    intro m hm
    have h := hR1 m hm
    have hrp : 0 ≤ r m := by simp only [hr]; positivity
    linarith
  have hbase : (17:ℝ) ≤ ell (12+4) := by
    have h12 : ell 12 = ((A381587_T 12).length : ℝ) := rfl
    have hlen : (A381587_T 12).length = 102 := by
      simp only [A381587_T]; simp [run_lengths_nat, rl_nil, List.reverse_cons]
    have hmono4 : ell 12 ≤ ell 16 := by
      have a := hmono 12 (by omega); have b := hmono 13 (by omega)
      have c := hmono 14 (by omega); have d := hmono 15 (by omega); linarith
    rw [h12, hlen] at hmono4; norm_num at hmono4 ⊢; linarith
  obtain ⟨c, C, hcpos, hCpos, hbounds⟩ :=
    Dev.ell_geom_bounds hlam1 hlam2 hkey hR1 hR2 hR3 hpos hmono hbase
  -- upper bound for a(n)
  set abase : ℝ := (A381358 16 : ℝ) with habase
  set C' : ℝ := abase / lam^16 + C / (lam - 1) with hC'def
  have hCC' : C + C' ≤ C' * lam := by
    have hne : lam - 1 ≠ 0 := by linarith
    have hkey2 : C / (lam - 1) * (lam - 1) = C := div_mul_cancel₀ C hne
    have habnn : (0:ℝ) ≤ abase / lam^16 := by rw [habase]; positivity
    rw [hC'def]
    nlinarith [hkey2, habnn, mul_nonneg habnn (show (0:ℝ) ≤ lam - 1 by linarith)]
  have hupper : ∀ n, 16 ≤ n → (A381358 n : ℝ) ≤ C' * lam^n := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ p ih =>
      intro hn
      rcases Nat.lt_or_ge 16 (p+1) with hp | hp
      · have ihp := ih (by omega)
        have harec : (A381358 (p+1):ℝ) = ((A381587_T p).length : ℝ) + (A381358 p:ℝ) := by
          exact_mod_cast a_rec p (by omega)
        have hellp : ell p ≤ C * lam^p := (hbounds p (by omega)).2
        have hpp : lam^(p+1) = lam * lam^p := by rw [pow_succ]; ring
        rw [harec]
        have hep : ((A381587_T p).length : ℝ) = ell p := rfl
        rw [hep, hpp]
        nlinarith [ihp, hellp, hCC', pow_pos (show (0:ℝ) < lam by linarith) p]
      · have h16 : p + 1 = 16 := by omega
        rw [h16, ← habase]
        have hsplit : C' * lam^16 = abase + C / (lam-1) * lam^16 := by
          rw [hC'def, add_mul]
          congr 1
          exact div_mul_cancel₀ abase (by positivity : (0:ℝ) < lam^16).ne'
        rw [hsplit]
        have : (0:ℝ) ≤ C / (lam-1) * lam^16 :=
          mul_nonneg (div_nonneg hCpos.le (by linarith)) (by positivity)
        linarith
  have hC'pos : 0 < C' := by
    rw [hC'def]
    have : 0 < C / (lam-1) := div_pos hCpos (by linarith)
    have : (0:ℝ) ≤ abase / lam^16 := by rw [habase]; positivity
    linarith
  have hfbounds : ∀ m, 16 ≤ m → c * lam^m ≤ (A381358 m : ℝ) ∧ (A381358 m : ℝ) ≤ C' * lam^m := by
    intro m hm
    refine ⟨?_, hupper m hm⟩
    have h1 : c * lam^m ≤ ell m := (hbounds m hm).1
    have h2 : ell m ≤ (A381358 m : ℝ) := by
      have hle := length_le_sum (A381587_T m) (T_pos m)
      simp only [hell]
      calc ((A381587_T m).length : ℝ) ≤ ((A381587_T m).sum : ℝ) := by exact_mod_cast hle
        _ = (A381358 m : ℝ) := by rw [A381358]
    linarith
  exact ⟨lam, Dev.tendsto_rpow_of_geom_bounds hlam1 hcpos hC'pos hfbounds⟩
