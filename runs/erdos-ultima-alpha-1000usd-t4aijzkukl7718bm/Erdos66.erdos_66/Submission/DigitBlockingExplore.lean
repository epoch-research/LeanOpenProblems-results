import Submission.LayeredPathExplore

/-! Grouping a fixed number of adjacent digits preserves the width of
position-dependent nondeterministic programs. The grouping identity is
proved for the ordinary natural-number encoding. -/
namespace Erdos66DigitBlocking
open Erdos66LayeredPath Erdos66LayeredDigitProgram Erdos66DigitBoxEnergy
  Erdos66DfaCounting Erdos66DigitLoopPeak
open scoped Classical
set_option maxHeartbeats 2600000
variable {b : ℕ} {σ : Type*}

lemma code_ofFn {k : ℕ} (x : Fin k → Fin b) : code (List.ofFn x)=encode x := by
  simp only [code,encode,List.map_ofFn,Function.comp_def]

lemma full_box_eq_range (hb : 1 < b) (k : ℕ) :
    box (fun _ : Fin k ↦ (Finset.univ : Finset (Fin b)))=Finset.range (b^k) := by
  apply Finset.eq_of_subset_of_card_le
  · intro n hn
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (encode_lt hb x)
  · simp [box_card hb]

lemma exists_encode (hb : 1 < b) {k n : ℕ} (hn : n<b^k) :
    ∃ x : Fin k → Fin b, encode x=n := by
  have hmem : n∈box (fun _ : Fin k ↦ (Finset.univ : Finset (Fin b))) := by
    rw [full_box_eq_range hb]
    exact Finset.mem_range.mpr hn
  obtain ⟨x,hx,hx'⟩ := Finset.mem_image.mp hmem
  exact ⟨x,hx'⟩

lemma ofFn_eq_finWord (hb : 1 < b) {k : ℕ} (x : Fin k → Fin b) :
    List.ofFn x=finWord hb k (encode x) := by
  apply code_inj hb
  · rw [List.length_ofFn,length_finWord hb _ _ (encode_lt hb x)]
  · rw [code_ofFn,code_finWord]

def fromEdge (E : ℕ → σ → Fin b → σ → Prop) (k : ℕ) (a : σ) (T : Set σ) :
    Program b k σ := ⟨fun i ↦ E i.val,a,T⟩

lemma mem_fromEdge_encode [Fintype σ] (hb : 1 < b)
    (E : ℕ → σ → Fin b → σ → Prop) {k : ℕ} (a : σ) (T : Set σ) (x : Fin k → Fin b) :
    encode x∈accepted (fromEdge E k a T) ↔
      ∃ z∈T, Path E 0 (List.ofFn x) a z := by
  rw [mem_accepted_encode hb]
  simp only [fromEdge]
  constructor
  · rintro ⟨q,hq0,hqz,hq⟩
    refine ⟨q (Fin.last k),hqz,(path_ofFn_iff E x 0 a _).mpr ⟨q,hq0,rfl,?_⟩⟩
    simpa only [Nat.zero_add] using hq
  · rintro ⟨z,hz,hpath⟩
    obtain ⟨q,hq0,hqz,hq⟩ := (path_ofFn_iff E x 0 a z).mp hpath
    exact ⟨q,hq0,by simpa only [hqz] using hz,by simpa only [Nat.zero_add] using hq⟩

lemma mem_fromEdge [Fintype σ] (hb : 1 < b)
    (E : ℕ → σ → Fin b → σ → Prop) {k n : ℕ} (a : σ) (T : Set σ)
    (hn : n<b^k) :
    n∈accepted (fromEdge E k a T) ↔ ∃ z∈T, Path E 0 (finWord hb k n) a z := by
  obtain ⟨x,rfl⟩ := exists_encode hb hn
  rw [mem_fromEdge_encode hb,ofFn_eq_finWord hb]

def expand (hb : 1 < b) (d : ℕ) (w : List (Fin (b^d))) : List (Fin b) :=
  w.flatMap (fun a ↦ finWord hb d a.val)

lemma expand_length (hb : 1 < b) (d : ℕ) (w : List (Fin (b^d))) :
    (expand hb d w).length=d*w.length := by
  induction w with
  | nil => simp [expand]
  | cons a w ih =>
    simp only [expand,List.flatMap_cons,List.length_append,length_finWord hb _ _ a.isLt]
    change d+(expand hb d w).length=d*(w.length+1)
    rw [ih]
    ring

lemma expand_code (hb : 1 < b) (d : ℕ) (w : List (Fin (b^d))) :
    code (expand hb d w)=code w := by
  induction w with
  | nil => simp [expand,code]
  | cons a w ih =>
    change code (finWord hb d a.val++expand hb d w)=code (a::w)
    rw [code_append,code_finWord,length_finWord hb _ _ a.isLt,ih]
    simp [code,Nat.ofDigits]

def blockEdge (hb : 1 < b) (d : ℕ) (E : ℕ → σ → Fin b → σ → Prop) :
    ℕ → σ → Fin (b^d) → σ → Prop :=
  fun i a x z ↦ Path E (d*i) (finWord hb d x.val) a z

lemma path_expand (hb : 1 < b) (d : ℕ) (E : ℕ → σ → Fin b → σ → Prop)
    (w : List (Fin (b^d))) (i : ℕ) (a z : σ) :
    Path E (d*i) (expand hb d w) a z ↔ Path (blockEdge hb d E) i w a z := by
  induction w generalizing i a with
  | nil => simp [expand,Erdos66LayeredPath.Path]
  | cons x w ih =>
    change Path E (d*i) (finWord hb d x.val++expand hb d w) a z ↔
      ∃ t, Path E (d*i) (finWord hb d x.val) a t ∧
        Path (blockEdge hb d E) (i+1) w t z
    rw [path_append,length_finWord hb _ _ x.isLt]
    have he : d*i+d=d*(i+1) := by ring
    simp only [he,ih]

lemma expand_finWord (hb : 1 < b) {d : ℕ} (hbd : 1 < b^d) (k n : ℕ)
    (hn : n<(b^d)^k) :
    expand hb d (finWord hbd k n)=finWord hb (d*k) n := by
  apply code_inj hb
  · rw [expand_length,length_finWord hbd _ _ hn,
      length_finWord hb _ _ (by simpa only [pow_mul] using hn)]
  · rw [expand_code,code_finWord,code_finWord]

lemma mem_block_program [Fintype σ] (hb : 1 < b) {d : ℕ} (hbd : 1 < b^d)
    (E : ℕ → σ → Fin b → σ → Prop) (k n : ℕ) (a : σ) (T : Set σ)
    (hn : n<(b^d)^k) :
    n∈accepted (fromEdge (blockEdge hb d E) k a T) ↔
      ∃ z∈T, Path E 0 (finWord hb (d*k) n) a z := by
  rw [mem_fromEdge hbd _ _ _ hn,←expand_finWord hb hbd k n hn]
  simp only [←path_expand hb d E, Nat.mul_zero]

end Erdos66DigitBlocking
