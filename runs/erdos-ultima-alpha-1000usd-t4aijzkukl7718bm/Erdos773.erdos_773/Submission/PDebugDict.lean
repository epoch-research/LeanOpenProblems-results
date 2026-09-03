import FormalConjecturesUtil

/-!
An auxiliary test of a digit construction, not a settlement of Erdős 773.
The definitions below track rational rotations through affine digit words.
-/
namespace Erdos773.ParametricSphere

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option Elab.async false

structure Step where
  constant : Fin 4 → ℕ
  slope : Fin 4 → ℕ
  next : ℤ × ℤ

def base (t : ℕ) : ℕ := 256 + 124160 * t

def digit (s : Step) (j : Fin 4) (t : ℕ) : ℕ :=
  2 * s.constant j + 256 * s.slope j * t

def value (ss : List Step) (j : Fin 4) (t : ℕ) : ℕ :=
  ss.foldr (fun s n => digit s j t + base t * n) 1

def ivalue (ss : List Step) (j : Fin 4) (t : ℕ) : ℤ :=
  ss.foldr (fun s n =>
    2 * (s.constant j : ℤ) + 256 * (s.slope j : ℤ) * t + (256 + 124160 * (t : ℤ)) * n) 1

lemma cast_value (ss : List Step) (j : Fin 4) (t : ℕ) :
    (value ss j t : ℤ) = ivalue ss j t := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [value, ivalue, List.foldr_cons, digit, base, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat] at ih ⊢
    rw [ih]

def checkStep (s : Step) (k l : ℤ) : Bool := decide (
  485 * (s.constant 2 : ℤ) = 476 * s.constant 0 + 93 * s.constant 1 - k + 256 * s.next.1 ∧
  485 * (s.constant 3 : ℤ) = -93 * s.constant 0 + 476 * s.constant 1 - l + 256 * s.next.2 ∧
  485 * (s.slope 2 : ℤ) = 476 * s.slope 0 + 93 * s.slope 1 + 970 * s.next.1 ∧
  485 * (s.slope 3 : ℤ) = -93 * s.slope 0 + 476 * s.slope 1 + 970 * s.next.2)

def checkPath : List Step → ℤ → ℤ → Bool
  | [], k, l => decide (k = 42 ∧ l = -51)
  | s :: ss, k, l => checkStep s k l && checkPath ss s.next.1 s.next.2

lemma rotation_of_checkPath (ss : List Step) (t : ℕ) (k l : ℤ)
    (h : checkPath ss k l = true) :
    485 * ivalue ss 2 t - 476 * ivalue ss 0 t - 93 * ivalue ss 1 t = -2 * k ∧
    485 * ivalue ss 3 t + 93 * ivalue ss 0 t - 476 * ivalue ss 1 t = -2 * l := by
  induction ss generalizing k l with
  | nil =>
    have hk : k = 42 ∧ l = -51 := of_decide_eq_true h
    rcases hk with ⟨rfl, rfl⟩
    norm_num [ivalue]
  | cons s ss ih =>
    have hh : checkStep s k l = true ∧ checkPath ss s.next.1 s.next.2 = true := by
      simpa only [checkPath, Bool.and_eq_true_iff] using h
    obtain ⟨hs, ht⟩ := hh
    have hs' := of_decide_eq_true hs
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hs'
    obtain ⟨hi₁, hi₂⟩ := ih _ _ ht
    simp only [ivalue, List.foldr_cons] at hi₁ hi₂ ⊢
    constructor
    · linear_combination 2 * h₁ + 256 * (t : ℤ) * h₃ +
        (256 + 124160 * (t : ℤ)) * hi₁
    · linear_combination 2 * h₂ + 256 * (t : ℤ) * h₄ +
        (256 + 124160 * (t : ℤ)) * hi₂

lemma norm_collision_of_checkPath (ss : List Step)
    (h : checkPath ss 0 0 = true) (t : ℕ) :
    value ss 0 t ^ 2 + value ss 1 t ^ 2 = value ss 2 t ^ 2 + value ss 3 t ^ 2 := by
  have hi := rotation_of_checkPath ss t 0 0 h
  have h₁ : 485 * ivalue ss 2 t = 476 * ivalue ss 0 t + 93 * ivalue ss 1 t := by
    linarith [hi.1]
  have h₂ : 485 * ivalue ss 3 t = -93 * ivalue ss 0 t + 476 * ivalue ss 1 t := by
    linarith [hi.2]
  have hsq₁ := congrArg (fun x : ℤ => x ^ 2) h₁
  have hsq₂ := congrArg (fun x : ℤ => x ^ 2) h₂
  have he : ivalue ss 0 t ^ 2 + ivalue ss 1 t ^ 2 =
      ivalue ss 2 t ^ 2 + ivalue ss 3 t ^ 2 := by nlinarith only [hsq₁, hsq₂]
  simp only [← cast_value] at he
  exact_mod_cast he

lemma sum_digits (ss : List Step) (j : Fin 4) (t : ℕ) :
    (ss.map (fun s => digit s j t)).sum =
      2 * (ss.map (fun s => s.constant j)).sum +
        256 * t * (ss.map (fun s => s.slope j)).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp only [digit]
    ring

lemma sum_square_digits (ss : List Step) (j : Fin 4) (t : ℕ) :
    (ss.map (fun s => digit s j t ^ 2)).sum =
      4 * (ss.map (fun s => s.constant j ^ 2)).sum +
        1024 * t * (ss.map (fun s => s.constant j * s.slope j)).sum +
        65536 * t ^ 2 * (ss.map (fun s => s.slope j ^ 2)).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp only [digit]
    ring



-- A shared dictionary keeps the explicit finite certificate compact.
def mkStep (a b c d u v w z : ℕ) (k l : ℤ) : Step :=
  ⟨![a, b, c, d], ![u, v, w, z], (k, l)⟩

def step0 : Step := mkStep 1 45 17 35 47 161 105 115 14 (-17)
def step1 : Step := mkStep 60 48 10 33 205 145 9 93 (-110) (-5)
def step2 : Step := mkStep 63 19 5 62 228 69 7 234 (-115) 105
def step3 : Step := mkStep 58 6 5 41 200 35 1 172 (-101) 88
def step4 : Step := mkStep 56 61 22 12 165 235 37 59 (-85) (-70)
def step5 : Step := mkStep 28 58 43 10 58 209 113 36 8 (-79)
def step6 : Step := mkStep 40 28 52 11 13 189 77 149 14 (-17)
def step7 : Step := mkStep 59 24 6 26 211 83 9 93 (-107) 26
def step8 : Step := mkStep 60 27 2 54 222 131 7 234 (-118) 74
def step9 : Step := mkStep 59 32 2 59 222 131 7 234 (-118) 74
def step10 : Step := mkStep 47 2 4 63 203 4 38 231 (-81) 133
def step11 : Step := mkStep 62 5 34 45 107 26 4 203 (-53) 99
def step12 : Step := mkStep 4 15 56 9 11 48 206 27 93 (-9)
def step13 : Step := mkStep 59 56 3 50 230 210 18 186 (-124) 12
def step14 : Step := mkStep 34 26 46 10 61 178 122 129 14 (-17)
def step15 : Step := mkStep 58 52 22 3 216 193 79 8 (-85) (-70)
def step16 : Step := mkStep 58 21 15 47 214 52 46 152 (-87) 71
def step17 : Step := mkStep 63 24 55 62 169 32 128 191 (-22) 96
def step18 : Step := mkStep 62 0 6 18 205 145 21 217 (-104) 57
def step19 : Step := mkStep 62 52 4 29 236 148 6 62 (-127) (-19)
def step20 : Step := mkStep 21 56 39 42 55 240 128 191 14 (-17)
def step21 : Step := mkStep 16 60 39 5 10 220 96 22 22 (-96)
def step22 : Step := mkStep 34 38 48 22 87 71 127 19 14 (-17)
def step23 : Step := mkStep 57 58 0 36 230 210 12 124 (-127) (-19)
def step24 : Step := mkStep 55 62 12 6 227 241 65 25 (-102) (-84)
def step25 : Step := mkStep 36 16 46 0 84 102 130 50 14 (-17)
def step26 : Step := mkStep 54 19 45 59 200 35 159 188 (-22) 96
def step27 : Step := mkStep 56 63 15 23 174 142 0 0 (-99) (-53)
def step28 : Step := mkStep 15 14 25 2 42 51 79 8 14 (-17)
def step29 : Step := mkStep 4 54 62 31 36 113 237 24 90 (-40)
def step30 : Step := mkStep 61 24 2 51 222 131 7 234 (-118) 74
def step31 : Step := mkStep 48 9 30 59 93 9 21 217 (-36) 113
def step32 : Step := mkStep 29 23 15 2 196 238 170 140 (-34) (-28)
def step33 : Step := mkStep 63 2 0 29 242 86 18 186 (-118) 74
def step34 : Step := mkStep 41 48 57 30 13 189 77 149 14 (-17)
def step35 : Step := mkStep 39 34 52 17 132 91 175 30 14 (-17)
def step36 : Step := mkStep 32 12 10 16 217 21 127 19 (-45) 20
def step37 : Step := mkStep 51 1 6 45 169 32 4 203 (-84) 102
def step38 : Step := mkStep 57 12 60 17 112 136 142 174 3 31
def step39 : Step := mkStep 63 15 4 58 231 38 4 203 (-115) 105
def step40 : Step := mkStep 55 3 3 55 203 4 4 203 (-98) 119
def step41 : Step := mkStep 21 14 52 48 25 65 145 205 54 73
def step42 : Step := mkStep 29 17 39 2 5 110 54 73 14 (-17)
def step43 : Step := mkStep 20 51 37 37 143 139 195 75 14 (-17)
def step44 : Step := mkStep 21 6 16 27 194 97 187 154 (-11) 48
def step45 : Step := mkStep 48 39 62 20 39 82 82 39 14 (-17)
def step46 : Step := mkStep 44 34 17 28 152 46 34 28 (-62) 6
def step47 : Step := mkStep 33 37 47 21 55 240 128 191 14 (-17)
def step48 : Step := mkStep 54 7 1 43 197 66 4 203 (-101) 88
def step49 : Step := mkStep 8 21 30 34 13 189 117 239 34 28
def step50 : Step := mkStep 26 53 43 38 87 71 127 19 14 (-17)
def step51 : Step := mkStep 55 6 11 49 197 66 38 231 (-84) 102
def step52 : Step := mkStep 45 46 59 11 33 144 82 39 11 (-48)
def step53 : Step := mkStep 33 43 48 27 70 85 113 36 14 (-17)
def step54 : Step := mkStep 50 45 7 23 213 224 60 135 (-96) (-22)
def step55 : Step := mkStep 29 29 49 5 75 195 167 109 28 (-34)
def step56 : Step := mkStep 61 10 10 61 203 4 4 203 (-98) 119
def step57 : Step := mkStep 13 3 27 57 14 17 69 228 26 107
def step58 : Step := mkStep 62 5 19 63 203 4 38 231 (-81) 133
def step59 : Step := mkStep 23 8 57 0 90 40 220 10 62 (-6)
def step60 : Step := mkStep 2 62 0 4 55 240 48 11 (-26) (-107)
def step61 : Step := mkStep 15 20 26 8 132 91 175 30 14 (-17)
def step62 : Step := mkStep 49 21 3 16 188 159 29 138 (-93) 9
def step63 : Step := mkStep 35 46 27 40 134 232 114 208 (-31) 3
def step64 : Step := mkStep 27 23 22 10 227 241 235 165 (-17) (-14)
def step65 : Step := mkStep 63 20 5 63 228 69 7 234 (-115) 105
def step66 : Step := mkStep 42 4 29 30 107 26 60 135 (-25) 65
def step67 : Step := mkStep 49 21 30 38 95 150 38 231 (-42) 51
def step68 : Step := mkStep 61 2 16 44 169 32 4 203 (-84) 102
def step69 : Step := mkStep 5 63 54 16 13 189 189 13 70 (-85)
def step70 : Step := mkStep 62 53 7 63 216 193 7 234 (-121) 43
def step71 : Step := mkStep 57 29 38 28 84 102 12 124 (-45) 20
def step72 : Step := mkStep 47 47 48 46 199 207 207 199 (-14) 17
def step73 : Step := mkStep 38 38 52 21 81 133 133 81 14 (-17)
def step74 : Step := mkStep 48 61 63 9 151 218 206 27 8 (-79)
def step75 : Step := mkStep 27 4 32 48 93 9 111 177 9 93
def step76 : Step := mkStep 52 5 24 47 217 21 111 177 (-53) 99
def step77 : Step := mkStep 56 5 4 57 200 35 7 234 (-98) 119
def step78 : Step := mkStep 48 18 12 37 228 69 91 132 (-73) 54
def step79 : Step := mkStep 15 56 33 43 92 181 153 126 14 (-17)
def step80 : Step := mkStep 47 15 21 58 200 35 97 194 (-53) 99
def step81 : Step := mkStep 45 28 2 40 233 179 83 211 (-90) 40
def step82 : Step := mkStep 25 62 44 47 103 229 173 171 14 (-17)
def step83 : Step := mkStep 44 25 11 61 149 77 21 217 (-70) 85
def step84 : Step := mkStep 28 26 40 11 30 175 91 132 14 (-17)
def step85 : Step := mkStep 42 50 36 59 30 175 7 234 (-28) 34
def step86 : Step := mkStep 59 57 33 15 154 187 51 42 (-68) (-56)
def step87 : Step := mkStep 51 8 0 61 217 21 21 217 (-98) 119
def step88 : Step := mkStep 40 42 4 13 236 148 96 22 (-82) (-39)
def step89 : Step := mkStep 19 25 31 12 72 226 142 174 14 (-17)
def step90 : Step := mkStep 39 39 13 34 208 114 102 84 (-62) 6
def step91 : Step := mkStep 33 37 47 21 25 65 65 25 14 (-17)
def step92 : Step := mkStep 37 12 18 48 155 15 77 149 (-39) 82
def step93 : Step := mkStep 62 24 27 40 242 86 108 146 (-73) 54
def step94 : Step := mkStep 36 49 3 37 160 125 23 76 (-79) (-8)
def step95 : Step := mkStep 0 62 49 16 44 192 220 10 70 (-85)
def step96 : Step := mkStep 35 46 12 58 228 69 119 98 (-59) 37
def step97 : Step := mkStep 29 21 40 6 64 147 119 98 14 (-17)
def step98 : Step := mkStep 34 22 8 51 118 74 18 186 (-56) 68
def step99 : Step := mkStep 63 60 8 53 227 241 21 217 (-124) 12
def step100 : Step := mkStep 33 50 24 28 95 150 54 73 (-34) (-28)
def step101 : Step := mkStep 20 27 16 15 104 57 79 8 (-17) (-14)
def step102 : Step := mkStep 15 53 62 4 24 237 209 58 70 (-85)
def step103 : Step := mkStep 11 60 61 28 27 206 212 89 73 (-54)
def step104 : Step := mkStep 61 58 17 1 213 224 48 11 (-102) (-84)
def step105 : Step := mkStep 31 22 56 63 118 74 210 230 40 90
def step106 : Step := mkStep 46 55 63 36 55 240 128 191 14 (-17)
def step107 : Step := mkStep 33 29 11 0 151 218 88 101 (-51) (-42)
def step108 : Step := mkStep 31 63 50 47 134 232 204 168 14 (-17)
def step109 : Step := mkStep 22 11 18 32 203 4 178 61 (-11) 48
def step110 : Step := mkStep 34 22 45 6 163 94 206 27 14 (-17)
def step111 : Step := mkStep 32 56 2 61 222 131 91 132 (-76) 23
def step112 : Step := mkStep 60 36 48 9 222 131 175 30 (-34) (-28)
def step113 : Step := mkStep 18 21 29 8 39 82 82 39 14 (-17)
def step114 : Step := mkStep 31 63 5 10 165 235 65 25 (-71) (-87)
def step115 : Step := mkStep 51 23 62 4 118 74 158 16 14 (-17)
def step116 : Step := mkStep 31 23 29 42 143 139 145 205 (-11) 48
def step117 : Step := mkStep 30 51 45 19 19 127 65 25 11 (-48)
def step118 : Step := mkStep 30 39 1 3 199 207 99 53 (-68) (-56)
def step119 : Step := mkStep 29 36 10 24 135 60 48 11 (-48) (-11)
def step120 : Step := mkStep 37 59 15 54 120 215 35 200 (-62) 6
def step121 : Step := mkStep 26 46 0 27 163 94 48 11 (-65) (-25)
def step122 : Step := mkStep 51 58 27 34 132 91 17 14 (-65) (-25)
def step123 : Step := mkStep 58 19 0 63 231 38 4 203 (-115) 105
def step124 : Step := mkStep 25 1 10 14 186 18 130 50 (-28) 34
def step125 : Step := mkStep 21 41 9 5 75 195 37 59 (-37) (-59)
def step126 : Step := mkStep 42 59 60 41 30 175 91 132 14 (-17)
def step127 : Step := mkStep 26 37 31 15 36 113 51 42 (-3) (-31)
def step128 : Step := mkStep 62 47 6 57 216 193 7 234 (-121) 43
def step129 : Step := mkStep 3 2 59 62 31 3 241 227 105 115
def step130 : Step := mkStep 61 56 63 52 39 82 26 107 (-14) 17
def step131 : Step := mkStep 26 28 62 3 81 133 223 41 59 (-37)
def step132 : Step := mkStep 50 1 18 11 208 114 108 146 (-59) 37
def step133 : Step := mkStep 26 6 24 59 203 4 190 185 (-5) 110
def step134 : Step := mkStep 59 59 8 11 196 238 6 62 (-116) (-67)
def step135 : Step := mkStep 25 20 36 6 84 102 130 50 14 (-17)
def step136 : Step := mkStep 25 43 9 48 149 77 71 87 (-45) 20
def step137 : Step := mkStep 24 62 56 13 55 240 178 61 39 (-82)
def step138 : Step := mkStep 12 54 59 6 13 189 189 13 70 (-85)
def step139 : Step := mkStep 24 19 5 41 112 136 52 214 (-42) 51
def step140 : Step := mkStep 14 1 59 35 31 3 201 137 85 70
def step141 : Step := mkStep 55 8 11 51 169 32 4 203 (-84) 102
def step142 : Step := mkStep 6 34 20 23 25 65 65 25 14 (-17)
def step143 : Step := mkStep 23 47 21 18 106 198 102 84 (-20) (-45)
def step144 : Step := mkStep 59 60 4 54 213 224 4 203 (-124) 12
def step145 : Step := mkStep 23 7 45 50 90 40 176 202 40 90
def step146 : Step := mkStep 13 4 24 25 124 12 164 78 20 45
def step147 : Step := mkStep 49 29 61 10 104 57 141 2 14 (-17)
def step148 : Step := mkStep 21 60 2 0 72 226 0 0 (-57) (-104)
def step149 : Step := mkStep 36 54 59 12 106 198 192 44 25 (-65)
def step150 : Step := mkStep 57 41 40 40 236 148 170 140 (-45) 20
def step151 : Step := mkStep 21 41 39 60 118 74 170 140 20 45
def step152 : Step := mkStep 1 19 3 2 106 198 136 112 (-3) (-31)
def step153 : Step := mkStep 25 16 35 2 10 220 80 180 14 (-17)
def step154 : Step := mkStep 21 20 26 32 132 91 153 126 3 31
def step155 : Step := mkStep 13 19 24 7 129 122 178 61 14 (-17)
def step156 : Step := mkStep 20 48 42 9 41 223 133 81 25 (-65)
def step157 : Step := mkStep 19 2 0 58 200 35 131 222 (-36) 113
def step158 : Step := mkStep 27 26 2 56 115 105 21 217 (-56) 68
def step159 : Step := mkStep 12 42 2 24 112 136 68 56 (-34) (-28)
def step160 : Step := mkStep 2 62 45 41 67 116 206 27 59 (-37)
def step161 : Step := mkStep 24 27 36 13 22 96 68 56 14 (-17)
def step162 : Step := mkStep 39 15 37 49 228 69 221 182 (-8) 79
def step163 : Step := mkStep 13 20 24 8 39 82 82 39 14 (-17)
def step164 : Step := mkStep 18 42 60 51 13 189 179 233 65 25
def step165 : Step := mkStep 63 60 3 4 230 210 0 0 (-133) (-81)
def step166 : Step := mkStep 1 54 19 44 118 74 158 16 14 (-17)
def step167 : Step := mkStep 63 60 3 4 227 241 3 31 (-133) (-81)
def step168 : Step := mkStep 21 54 53 22 75 195 195 75 42 (-51)
def step169 : Step := mkStep 20 16 30 3 104 57 141 2 14 (-17)
def step170 : Step := mkStep 17 18 56 44 67 116 224 213 68 56
def step171 : Step := mkStep 20 6 18 60 200 35 193 216 (-5) 110
def step172 : Step := mkStep 50 10 51 0 64 147 91 132 0 0
def step173 : Step := mkStep 35 17 45 1 41 223 111 177 14 (-17)
def step174 : Step := mkStep 39 13 26 23 172 1 113 36 (-28) 34
def step175 : Step := mkStep 3 3 59 63 31 3 241 227 105 115
def step176 : Step := mkStep 16 3 21 49 203 4 218 151 9 93
def step177 : Step := mkStep 10 48 19 45 87 71 99 53 0 0
def step178 : Step := mkStep 15 40 6 38 103 229 83 211 (-31) 3
def step179 : Step := mkStep 56 3 29 61 172 1 69 228 (-50) 130
def step180 : Step := mkStep 21 38 28 33 134 232 176 202 0 0
def step181 : Step := mkStep 23 47 61 6 89 212 240 55 56 (-68)
def step182 : Step := mkStep 62 2 2 62 234 7 7 234 (-112) 136
def step183 : Step := mkStep 54 11 11 54 169 32 4 203 (-84) 102
def step184 : Step := mkStep 14 63 63 14 13 189 189 13 70 (-85)
def step185 : Step := mkStep 21 38 4 44 155 15 65 25 (-45) 20
def step186 : Step := mkStep 14 28 46 47 11 48 122 129 51 42
def step187 : Step := mkStep 61 3 16 45 197 66 38 231 (-84) 102
def step188 : Step := mkStep 35 60 41 3 24 237 51 42 (-9) (-93)
def step189 : Step := mkStep 36 17 46 1 55 240 128 191 14 (-17)
def step190 : Step := mkStep 11 61 34 7 10 220 96 22 22 (-96)
def step191 : Step := mkStep 13 56 62 24 50 130 220 10 73 (-54)
def step192 : Step := mkStep 50 0 3 28 183 49 15 155 (-87) 71
def step193 : Step := mkStep 27 25 0 39 177 111 77 149 (-59) 37
def step194 : Step := mkStep 13 44 18 8 213 224 240 55 (-6) (-62)
def step195 : Step := mkStep 54 12 2 48 228 69 35 200 (-101) 88
def step196 : Step := mkStep 13 13 11 52 234 7 215 120 (-8) 79
def step197 : Step := mkStep 12 62 40 57 87 71 161 47 31 (-3)
def step198 : Step := mkStep 22 11 40 5 28 34 96 22 31 (-3)
def step199 : Step := mkStep 6 28 17 1 92 181 147 64 11 (-48)
def step200 : Step := mkStep 12 32 58 17 24 237 221 182 76 (-23)
def step201 : Step := mkStep 60 62 2 23 233 179 3 31 (-130) (-50)
def step202 : Step := mkStep 42 58 60 40 42 51 79 8 14 (-17)
def step203 : Step := mkStep 11 38 36 50 169 32 240 55 34 28
def step204 : Step := mkStep 11 8 54 10 73 54 240 55 79 8
def step205 : Step := mkStep 50 38 43 62 121 43 77 149 (-25) 65
def step206 : Step := mkStep 43 34 19 61 146 108 52 214 (-56) 68
def step207 : Step := mkStep 10 54 8 11 134 232 130 50 (-23) (-76)
def step208 : Step := mkStep 54 27 54 58 194 97 193 216 (-8) 79
def step209 : Step := mkStep 10 23 1 55 121 43 77 149 (-25) 65
def step210 : Step := mkStep 7 36 3 10 188 159 175 30 (-20) (-45)
def step211 : Step := mkStep 14 50 22 30 137 201 167 109 (-3) (-31)
def step212 : Step := mkStep 10 14 32 43 36 113 131 222 37 59
def step213 : Step := mkStep 60 10 9 61 203 4 4 203 (-98) 119
def step214 : Step := mkStep 8 48 26 53 177 111 229 103 17 14
def step215 : Step := mkStep 63 5 20 63 203 4 38 231 (-81) 133
def step216 : Step := mkStep 10 45 26 33 39 82 82 39 14 (-17)
def step217 : Step := mkStep 6 52 38 23 106 198 226 72 42 (-51)
def step218 : Step := mkStep 11 37 31 0 123 184 206 27 25 (-65)
def step219 : Step := mkStep 30 22 41 7 149 77 189 13 14 (-17)
def step220 : Step := mkStep 6 12 62 55 31 3 235 165 102 84
def step221 : Step := mkStep 44 42 60 40 149 77 195 75 17 14
def step222 : Step := mkStep 6 0 18 39 8 79 69 228 23 76
def step223 : Step := mkStep 29 20 37 63 124 12 142 174 9 93
def step224 : Step := mkStep 5 58 16 56 58 209 97 194 0 0
def step225 : Step := mkStep 5 49 47 44 58 209 221 182 62 (-6)
def step226 : Step := mkStep 0 56 18 46 2 141 57 104 14 (-17)
def step227 : Step := mkStep 5 37 3 28 42 51 17 14 (-17) (-14)
def step228 : Step := mkStep 1 62 59 23 30 175 237 24 87 (-71)
def step229 : Step := mkStep 53 32 49 14 233 179 229 103 (-17) (-14)
def step230 : Step := mkStep 45 34 5 62 177 111 21 217 (-87) 71
def step231 : Step := mkStep 60 0 13 26 166 63 1 172 (-87) 71
def step232 : Step := mkStep 5 28 34 16 109 167 229 103 45 (-20)
def step233 : Step := mkStep 62 41 0 2 233 179 3 31 (-130) (-50)
def step234 : Step := mkStep 32 43 13 14 165 235 105 115 (-51) (-42)
def step235 : Step := mkStep 48 36 27 4 78 164 6 62 (-51) (-42)
def step236 : Step := mkStep 3 53 59 14 27 206 240 55 87 (-71)
def step237 : Step := mkStep 10 10 61 3 42 51 237 24 93 (-9)
def step238 : Step := mkStep 52 8 45 7 157 156 156 157 (-14) 17
def step239 : Step := mkStep 3 22 52 58 39 82 224 213 85 70
def step240 : Step := mkStep 19 1 44 3 0 0 96 22 48 11
def step241 : Step := mkStep 62 8 0 35 222 131 7 234 (-118) 74
def step242 : Step := mkStep 20 56 38 42 146 108 192 44 14 (-17)
def step243 : Step := mkStep 3 10 8 42 183 49 201 137 6 62
def step244 : Step := mkStep 8 14 48 58 56 68 210 230 71 87
def step245 : Step := mkStep 61 59 4 36 239 117 3 31 (-127) (-19)
def step246 : Step := mkStep 2 38 24 19 13 189 105 115 28 (-34)
def step247 : Step := mkStep 60 49 7 1 216 193 17 14 (-116) (-67)
def step248 : Step := mkStep 54 29 11 39 225 100 60 135 (-90) 40
def step249 : Step := mkStep 1 56 56 1 24 237 237 24 84 (-102)
def step250 : Step := mkStep 3 40 40 3 10 220 164 78 56 (-68)
def step251 : Step := mkStep 48 42 3 4 199 207 37 59 (-99) (-53)
def step252 : Step := mkStep 12 10 60 61 28 34 210 230 88 101
def step253 : Step := mkStep 23 22 34 8 11 48 48 11 14 (-17)
def step254 : Step := mkStep 46 1 41 34 121 43 111 177 (-8) 79
def step255 : Step := mkStep 2 29 55 7 2 141 209 58 90 (-40)
def step256 : Step := mkStep 12 5 59 56 31 3 207 199 88 101
def step257 : Step := mkStep 22 40 56 57 78 164 210 230 51 42
def step258 : Step := mkStep 2 7 17 63 138 29 193 216 26 107
def step259 : Step := mkStep 0 9 51 4 28 34 220 10 93 (-9)
def step260 : Step := mkStep 19 16 59 58 28 34 176 202 71 87
def step261 : Step := mkStep 15 55 6 20 41 223 9 93 (-37) (-59)
def step262 : Step := mkStep 25 61 6 0 72 226 0 0 (-57) (-104)
def step263 : Step := mkStep 23 0 57 9 33 144 190 185 65 25
def step264 : Step := mkStep 18 1 24 63 155 15 179 233 12 124
def step265 : Step := mkStep 24 63 43 48 2 141 57 104 14 (-17)
def step266 : Step := mkStep 1 44 2 52 165 235 179 233 (-14) 17
def step267 : Step := mkStep 24 21 35 7 89 212 156 157 14 (-17)
def step268 : Step := mkStep 1 37 63 6 2 141 237 24 104 (-57)
def step269 : Step := mkStep 42 2 34 3 56 68 40 90 (-14) 17
def step270 : Step := mkStep 1 35 33 40 27 206 162 219 48 11
def step271 : Step := mkStep 51 2 6 46 231 38 66 197 (-84) 102
def step272 : Step := mkStep 35 40 48 7 171 173 223 41 11 (-48)
def step273 : Step := mkStep 1 5 51 0 16 158 232 134 93 (-9)
def step274 : Step := mkStep 13 55 2 4 89 212 48 11 (-40) (-90)
def step275 : Step := mkStep 63 58 6 35 227 241 15 155 (-127) (-19)
def step276 : Step := mkStep 2 40 39 3 44 192 192 44 56 (-68)
def step277 : Step := mkStep 2 0 63 35 0 0 232 134 116 67
def step278 : Step := mkStep 17 10 2 8 166 63 113 36 (-31) 3
def step279 : Step := mkStep 11 1 5 24 146 108 142 174 (-11) 48
def step280 : Step := mkStep 0 63 49 17 41 223 223 41 70 (-85)
def step281 : Step := mkStep 5 6 36 60 90 40 210 230 57 104
def step282 : Step := mkStep 19 63 38 49 55 240 128 191 14 (-17)
def step283 : Step := mkStep 3 31 61 58 11 48 218 151 99 53
def step284 : Step := mkStep 21 48 37 34 58 209 125 160 14 (-17)
def step285 : Step := mkStep 1 14 60 0 8 79 237 24 107 (-26)
def step286 : Step := mkStep 62 27 60 40 90 40 74 118 (-11) 48
def step287 : Step := mkStep 0 60 14 1 24 237 79 8 5 (-110)
def step288 : Step := mkStep 43 20 55 19 160 125 215 120 17 14
def step289 : Step := mkStep 30 58 21 20 47 161 3 31 (-37) (-59)
def step290 : Step := mkStep 0 2 60 21 0 0 226 72 113 36
def step291 : Step := mkStep 63 4 27 53 138 29 7 234 (-67) 116
def step292 : Step := mkStep 62 56 39 46 109 167 15 155 (-62) 6
def step293 : Step := mkStep 61 17 8 35 194 97 1 172 (-104) 57
def step294 : Step := mkStep 31 53 48 37 16 158 74 118 14 (-17)
def step295 : Step := mkStep 16 3 58 4 45 20 206 27 79 8
def step296 : Step := mkStep 13 22 17 19 182 221 221 182 0 0
def step297 : Step := mkStep 4 42 18 15 106 198 164 78 11 (-48)
def step298 : Step := mkStep 12 13 38 0 8 79 113 36 45 (-20)
def step299 : Step := mkStep 3 18 14 8 163 94 206 27 14 (-17)
def step300 : Step := mkStep 57 55 14 15 230 210 68 56 (-99) (-53)
def step301 : Step := mkStep 53 41 0 11 236 148 34 28 (-113) (-36)
def step302 : Step := mkStep 59 59 4 53 213 224 4 203 (-124) 12
def step303 : Step := mkStep 9 3 35 7 45 20 144 33 48 11
def step304 : Step := mkStep 2 40 17 30 104 57 141 2 14 (-17)
def step305 : Step := mkStep 27 58 49 1 24 237 113 36 22 (-96)
def step306 : Step := mkStep 23 53 4 9 89 212 20 45 (-54) (-73)
def step307 : Step := mkStep 12 53 59 5 44 192 220 10 70 (-85)
def step308 : Step := mkStep 20 54 25 0 58 209 79 8 (-9) (-93)
def step309 : Step := mkStep 35 63 0 2 134 232 0 0 (-88) (-101)
def step310 : Step := mkStep 50 41 17 43 219 162 94 163 (-76) 23
def step311 : Step := mkStep 36 58 54 41 25 65 65 25 14 (-17)
def step312 : Step := mkStep 8 54 2 53 183 49 127 19 (-31) 3
def step313 : Step := mkStep 0 61 56 6 24 237 237 24 84 (-102)
def step314 : Step := mkStep 23 5 25 17 231 38 240 55 3 31
def step315 : Step := mkStep 2 37 49 24 41 223 235 165 76 (-23)
def step316 : Step := mkStep 10 52 33 15 154 187 237 24 25 (-65)
def step317 : Step := mkStep 16 21 48 56 76 23 187 154 54 73
def step318 : Step := mkStep 25 24 38 26 62 6 96 22 17 14
def step319 : Step := mkStep 14 21 25 9 8 79 51 42 14 (-17)
def step320 : Step := mkStep 13 1 56 19 25 65 201 137 82 39
def step321 : Step := mkStep 55 10 4 62 203 4 4 203 (-98) 119
def step322 : Step := mkStep 9 57 0 23 41 223 9 93 (-37) (-59)
def step323 : Step := mkStep 3 59 42 5 10 220 158 16 53 (-99)
def step324 : Step := mkStep 9 23 58 58 31 3 201 137 85 70
def step325 : Step := mkStep 47 0 36 58 203 4 162 219 (-19) 127
def step326 : Step := mkStep 40 59 58 41 72 226 142 174 14 (-17)
def step327 : Step := mkStep 30 5 53 63 62 6 148 236 43 121
def step328 : Step := mkStep 21 60 41 62 42 51 85 70 17 14
def step329 : Step := mkStep 2 6 61 8 0 0 220 10 110 5
def step330 : Step := mkStep 39 29 51 12 42 51 79 8 14 (-17)
def step331 : Step := mkStep 1 1 40 63 0 0 148 236 74 118
def step332 : Step := mkStep 26 43 41 28 5 110 54 73 14 (-17)
def step333 : Step := mkStep 0 29 56 40 11 48 212 89 96 22
def step334 : Step := mkStep 63 16 4 59 228 69 7 234 (-115) 105
def step335 : Step := mkStep 16 61 44 55 14 17 79 8 31 (-3)
def step336 : Step := mkStep 1 63 32 2 24 237 141 2 36 (-113)
def step337 : Step := mkStep 31 17 41 2 118 74 158 16 14 (-17)
def step338 : Step := mkStep 22 6 57 15 107 26 240 55 65 25

def firstStep : Step := step0



end Erdos773.ParametricSphere
