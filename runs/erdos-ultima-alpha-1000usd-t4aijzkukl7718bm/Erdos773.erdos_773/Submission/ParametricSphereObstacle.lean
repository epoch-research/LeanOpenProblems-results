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


def checkPrefix : List Step → ℤ → ℤ → ℤ → ℤ → Bool
  | [], k, l, m, n => decide (k = m ∧ l = n)
  | s :: ss, k, l, m, n => checkStep s k l && checkPrefix ss s.next.1 s.next.2 m n

lemma checkPath_append (xs ys : List Step) (k l m n : ℤ)
    (h : checkPrefix xs k l m n = true) (hy : checkPath ys m n = true) :
    checkPath (xs ++ ys) k l = true := by
  induction xs generalizing k l with
  | nil =>
    have he : k = m ∧ l = n := of_decide_eq_true h
    rcases he with ⟨rfl, rfl⟩
    exact hy
  | cons x xs ih =>
    have hh : checkStep x k l = true ∧ checkPrefix xs x.next.1 x.next.2 m n = true := by
      simpa only [checkPrefix, Bool.and_eq_true_iff] using h
    simp only [List.cons_append, checkPath, Bool.and_eq_true_iff]
    exact ⟨hh.1, ih _ _ hh.2⟩


def block0 : List Step := [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step9, step9, step9, step9, step9, step9, step9, step10, step11, step12]
lemma block0_checked : checkPrefix block0 (0) (0) (93) (-9) = true := by decide +kernel
def block1 : List Step := [step13, step14, step15, step5, step6, step15, step5, step6, step15, step5, step6, step15, step5, step6, step15, step5, step6, step16, step17, step18]
lemma block1_checked : checkPrefix block1 (93) (-9) (-104) (57) = true := by decide +kernel
def block2 : List Step := [step19, step20, step16, step17, step18, step19, step20, step16, step21, step22, step16, step21, step22, step16, step21, step22, step16, step21, step22, step16]
lemma block2_checked : checkPrefix block2 (-104) (57) (-87) (71) = true := by decide +kernel
def block3 : List Step := [step21, step22, step23, step20, step23, step20, step23, step20, step23, step20, step23, step20, step23, step20, step24, step25, step24, step25, step24, step25]
lemma block3_checked : checkPrefix block3 (-87) (71) (14) (-17) = true := by decide +kernel
def block4 : List Step := [step24, step25, step24, step25, step26, step18, step27, step28, step26, step18, step27, step28, step26, step18, step29, step30, step10, step31, step32, step33]
lemma block4_checked : checkPrefix block4 (14) (-17) (-118) (74) = true := by decide +kernel
def block5 : List Step := [step10, step31, step32, step33, step10, step31, step32, step33, step10, step31, step32, step33, step10, step34, step26, step18, step29, step35, step26, step18]
lemma block5_checked : checkPrefix block5 (-118) (74) (-104) (57) = true := by decide +kernel
def block6 : List Step := [step29, step35, step26, step36, step37, step38, step39, step3, step4, step5, step6, step26, step36, step37, step40, step41, step42, step26, step36, step37]
lemma block6_checked : checkPrefix block6 (-104) (57) (-84) (102) = true := by decide +kernel
def block7 : List Step := [step40, step43, step26, step36, step37, step40, step43, step26, step36, step37, step40, step43, step26, step36, step37, step40, step43, step26, step36, step37]
lemma block7_checked : checkPrefix block7 (-84) (102) (-84) (102) = true := by decide +kernel
def block8 : List Step := [step40, step43, step26, step44, step45, step26, step44, step46, step47, step26, step44, step46, step47, step48, step4, step49, step50, step48, step4, step49]
lemma block8_checked : checkPrefix block8 (-84) (102) (34) (28) = true := by decide +kernel
def block9 : List Step := [step50, step48, step4, step49, step50, step48, step51, step40, step43, step48, step51, step40, step43, step48, step51, step40, step43, step48, step51, step40]
lemma block9_checked : checkPrefix block9 (34) (28) (-98) (119) = true := by decide +kernel

def block10 : List Step := [step43, step48, step52, step53, step54, step55, step56, step43, step54, step55, step56, step43, step54, step55, step56, step43, step54, step55, step57, step58]
lemma block10_checked : checkPrefix block10 (-98) (119) (-81) (133) = true := by decide +kernel
def block11 : List Step := [step34, step54, step55, step57, step58, step34, step54, step55, step57, step58, step34, step54, step55, step57, step58, step59, step60, step61, step62, step63]
lemma block11_checked : checkPrefix block11 (-81) (133) (-31) (3) = true := by decide +kernel
def block12 : List Step := [step64, step65, step3, step66, step67, step68, step40, step43, step62, step63, step64, step65, step3, step66, step67, step68, step40, step43, step62, step63]
lemma block12_checked : checkPrefix block12 (-31) (3) (-31) (3) = true := by decide +kernel
def block13 : List Step := [step64, step65, step3, step66, step67, step68, step40, step43, step62, step63, step69, step70, step71, step37, step40, step43, step62, step63, step69, step70]
lemma block13_checked : checkPrefix block13 (-31) (3) (-121) (43) = true := by decide +kernel
def block14 : List Step := [step72, step73, step74, step75, step76, step12, step13, step14, step74, step75, step76, step12, step13, step14, step74, step75, step76, step12, step77, step43]
lemma block14_checked : checkPrefix block14 (-121) (43) (14) (-17) = true := by decide +kernel
def block15 : List Step := [step78, step79, step80, step12, step77, step43, step80, step12, step77, step43, step80, step12, step77, step43, step80, step12, step77, step43, step81, step82]
lemma block15_checked : checkPrefix block15 (14) (-17) (14) (-17) = true := by decide +kernel
def block16 : List Step := [step83, step84, step83, step84, step83, step84, step83, step84, step83, step84, step83, step84, step83, step84, step85, step86, step87, step43, step85, step86]
lemma block16_checked : checkPrefix block16 (14) (-17) (-68) (-56) = true := by decide +kernel
def block17 : List Step := [step87, step43, step85, step86, step87, step43, step85, step86, step87, step43, step88, step89, step90, step91, step90, step91, step90, step91, step90, step91]
lemma block17_checked : checkPrefix block17 (-68) (-56) (14) (-17) = true := by decide +kernel
def block18 : List Step := [step90, step91, step90, step91, step90, step91, step90, step91, step90, step91, step92, step93, step79, step94, step95, step70, step72, step73, step96, step97]
lemma block18_checked : checkPrefix block18 (14) (-17) (14) (-17) = true := by decide +kernel
def block19 : List Step := [step96, step97, step96, step97, step96, step97, step96, step97, step96, step97, step96, step97, step96, step97, step96, step97, step96, step97, step96, step97]
lemma block19_checked : checkPrefix block19 (14) (-17) (14) (-17) = true := by decide +kernel

def block20 : List Step := [step96, step97, step96, step97, step96, step97, step96, step97, step98, step99, step14, step98, step99, step14, step98, step99, step14, step98, step99, step14]
lemma block20_checked : checkPrefix block20 (14) (-17) (14) (-17) = true := by decide +kernel
def block21 : List Step := [step100, step33, step10, step101, step65, step3, step66, step67, step68, step40, step43, step100, step33, step10, step102, step70, step72, step73, step100, step33]
lemma block21_checked : checkPrefix block21 (14) (-17) (-118) (74) = true := by decide +kernel
def block22 : List Step := [step10, step103, step104, step25, step100, step33, step10, step103, step104, step25, step100, step33, step10, step103, step104, step25, step100, step33, step10, step103]
lemma block22_checked : checkPrefix block22 (-118) (74) (73) (-54) = true := by decide +kernel
def block23 : List Step := [step104, step25, step100, step33, step10, step103, step104, step25, step100, step33, step105, step106, step107, step108, step107, step108, step107, step108, step107, step108]
lemma block23_checked : checkPrefix block23 (73) (-54) (14) (-17) = true := by decide +kernel
def block24 : List Step := [step107, step108, step107, step108, step107, step108, step107, step108, step107, step108, step107, step108, step107, step108, step107, step109, step46, step91, step107, step109]
lemma block24_checked : checkPrefix block24 (14) (-17) (-11) (48) = true := by decide +kernel
def block25 : List Step := [step110, step111, step112, step33, step105, step113, step111, step112, step33, step105, step113, step114, step115, step116, step110, step116, step110, step116, step110, step116]
lemma block25_checked : checkPrefix block25 (-11) (48) (-11) (48) = true := by decide +kernel
def block26 : List Step := [step110, step116, step110, step116, step110, step116, step110, step117, step53, step117, step53, step117, step53, step117, step53, step117, step53, step117, step53, step118]
lemma block26_checked : checkPrefix block26 (-11) (48) (-68) (-56) = true := by decide +kernel
def block27 : List Step := [step87, step43, step118, step87, step43, step118, step87, step43, step118, step87, step43, step118, step87, step43, step118, step87, step43, step119, step120, step91]
lemma block27_checked : checkPrefix block27 (-68) (-56) (14) (-17) = true := by decide +kernel
def block28 : List Step := [step119, step120, step91, step119, step120, step91, step119, step120, step91, step121, step122, step122, step123, step3, step66, step124, step125, step126, step127, step128]
lemma block28_checked : checkPrefix block28 (14) (-17) (-121) (43) = true := by decide +kernel
def block29 : List Step := [step72, step73, step127, step128, step72, step73, step127, step128, step72, step73, step127, step128, step129, step130, step73, step127, step128, step129, step130, step73]
lemma block29_checked : checkPrefix block29 (-121) (43) (14) (-17) = true := by decide +kernel

def block30 : List Step := [step131, step132, step97, step131, step132, step97, step131, step132, step97, step131, step132, step97, step131, step132, step97, step133, step134, step135, step133, step134]
lemma block30_checked : checkPrefix block30 (14) (-17) (-116) (-67) = true := by decide +kernel
def block31 : List Step := [step135, step133, step134, step135, step136, step37, step40, step43, step137, step138, step70, step129, step130, step73, step139, step68, step40, step140, step141, step40]
lemma block31_checked : checkPrefix block31 (-116) (-67) (-98) (119) = true := by decide +kernel
def block32 : List Step := [step142, step139, step68, step40, step142, step139, step68, step40, step142, step139, step68, step40, step142, step139, step68, step40, step142, step139, step68, step40]
lemma block32_checked : checkPrefix block32 (-98) (119) (-98) (119) = true := by decide +kernel
def block33 : List Step := [step142, step139, step68, step40, step142, step143, step144, step14, step143, step144, step14, step143, step144, step14, step145, step113, step145, step113, step145, step113]
lemma block33_checked : checkPrefix block33 (-98) (119) (14) (-17) = true := by decide +kernel
def block34 : List Step := [step145, step146, step147, step145, step146, step147, step148, step149, step150, step37, step40, step142, step151, step147, step151, step147, step151, step147, step151, step152]
lemma block34_checked : checkPrefix block34 (14) (-17) (-3) (-31) = true := by decide +kernel
def block35 : List Step := [step153, step151, step152, step153, step151, step152, step153, step154, step39, step3, step155, step156, step150, step37, step40, step142, step156, step150, step37, step40]
lemma block35_checked : checkPrefix block35 (-3) (-31) (-98) (119) = true := by decide +kernel
def block36 : List Step := [step142, step157, step32, step33, step105, step146, step152, step153, step157, step32, step33, step105, step146, step152, step153, step157, step158, step99, step14, step157]
lemma block36_checked : checkPrefix block36 (-98) (119) (-36) (113) = true := by decide +kernel
def block37 : List Step := [step158, step99, step14, step157, step158, step99, step14, step157, step158, step99, step14, step157, step158, step99, step14, step157, step158, step99, step14, step157]
lemma block37_checked : checkPrefix block37 (-36) (113) (-36) (113) = true := by decide +kernel
def block38 : List Step := [step158, step159, step33, step105, step146, step152, step160, step161, step157, step158, step159, step162, step163, step164, step165, step166, step164, step165, step166, step164]
lemma block38_checked : checkPrefix block38 (-36) (113) (65) (25) = true := by decide +kernel
def block39 : List Step := [step165, step166, step164, step165, step166, step164, step165, step166, step164, step165, step166, step164, step167, step166, step164, step167, step166, step164, step168, step169]
lemma block39_checked : checkPrefix block39 (65) (25) (14) (-17) = true := by decide +kernel

def block40 : List Step := [step164, step168, step169, step170, step171, step134, step135, step170, step171, step134, step135, step170, step171, step172, step173, step170, step171, step172, step173, step170]
lemma block40_checked : checkPrefix block40 (14) (-17) (68) (56) = true := by decide +kernel
def block41 : List Step := [step171, step172, step173, step170, step171, step174, step125, step126, step170, step171, step174, step125, step126, step170, step171, step174, step125, step126, step170, step171]
lemma block41_checked : checkPrefix block41 (68) (56) (-5) (110) = true := by decide +kernel
def block42 : List Step := [step174, step175, step130, step73, step170, step171, step174, step175, step130, step73, step176, step76, step12, step77, step142, step176, step76, step12, step77, step142]
lemma block42_checked : checkPrefix block42 (-5) (110) (14) (-17) = true := by decide +kernel
def block43 : List Step := [step176, step76, step12, step77, step142, step176, step177, step173, step176, step177, step173, step176, step177, step173, step178, step69, step70, step129, step130, step73]
lemma block43_checked : checkPrefix block43 (14) (-17) (14) (-17) = true := by decide +kernel
def block44 : List Step := [step178, step69, step179, step180, step173, step178, step69, step181, step182, step183, step40, step142, step178, step69, step181, step182, step183, step40, step142, step178]
lemma block44_checked : checkPrefix block44 (14) (-17) (-31) (3) = true := by decide +kernel
def block45 : List Step := [step69, step181, step182, step183, step40, step142, step178, step69, step181, step182, step184, step181, step182, step184, step185, step37, step40, step142, step186, step187]
lemma block45_checked : checkPrefix block45 (-31) (3) (-84) (102) = true := by decide +kernel
def block46 : List Step := [step40, step142, step186, step187, step40, step142, step186, step188, step189, step186, step188, step189, step186, step188, step189, step186, step188, step189, step186, step190]
lemma block46_checked : checkPrefix block46 (-84) (102) (22) (-96) = true := by decide +kernel
def block47 : List Step := [step22, step186, step190, step22, step191, step104, step25, step191, step104, step25, step191, step192, step21, step22, step191, step193, step97, step191, step193, step97]
lemma block47_checked : checkPrefix block47 (22) (-96) (14) (-17) = true := by decide +kernel
def block48 : List Step := [step191, step193, step97, step191, step193, step97, step191, step193, step97, step194, step195, step155, step194, step195, step155, step194, step195, step155, step194, step195]
lemma block48_checked : checkPrefix block48 (14) (-17) (-101) (88) = true := by decide +kernel
def block49 : List Step := [step155, step196, step163, step196, step163, step196, step163, step196, step163, step196, step163, step196, step163, step197, step198, step198, step198, step198, step199, step53]
lemma block49_checked : checkPrefix block49 (-101) (88) (14) (-17) = true := by decide +kernel

def block50 : List Step := [step197, step199, step53, step197, step199, step53, step197, step199, step53, step200, step201, step202, step200, step201, step202, step200, step201, step202, step200, step201]
lemma block50_checked : checkPrefix block50 (14) (-17) (-130) (-50) = true := by decide +kernel
def block51 : List Step := [step202, step200, step201, step202, step200, step201, step202, step203, step50, step203, step50, step203, step50, step203, step50, step203, step50, step203, step50, step203]
lemma block51_checked : checkPrefix block51 (-130) (-50) (34) (28) = true := by decide +kernel
def block52 : List Step := [step50, step203, step50, step204, step205, step124, step175, step130, step73, step204, step206, step159, step162, step163, step204, step206, step159, step162, step163, step207]
lemma block52_checked : checkPrefix block52 (34) (28) (-23) (-76) = true := by decide +kernel
def block53 : List Step := [step208, step163, step207, step208, step163, step207, step208, step163, step209, step124, step175, step210, step144, step14, step209, step124, step175, step210, step144, step14]
lemma block53_checked : checkPrefix block53 (-23) (-76) (14) (-17) = true := by decide +kernel
def block54 : List Step := [step209, step124, step175, step210, step144, step14, step209, step124, step175, step210, step144, step14, step209, step124, step175, step210, step144, step211, step160, step161]
lemma block54_checked : checkPrefix block54 (14) (-17) (14) (-17) = true := by decide +kernel
def block55 : List Step := [step209, step124, step175, step210, step144, step211, step160, step161, step209, step124, step175, step210, step144, step211, step160, step161, step212, step213, step142, step212]
lemma block55_checked : checkPrefix block55 (14) (-17) (37) (59) = true := by decide +kernel
def block56 : List Step := [step213, step142, step212, step213, step142, step212, step213, step142, step214, step215, step216, step214, step215, step216, step214, step215, step216, step217, step169, step217]
lemma block56_checked : checkPrefix block56 (37) (59) (42) (-51) = true := by decide +kernel
def block57 : List Step := [step169, step217, step169, step217, step169, step217, step218, step150, step37, step40, step142, step217, step218, step150, step37, step40, step142, step217, step218, step150]
lemma block57_checked : checkPrefix block57 (42) (-51) (-45) (20) = true := by decide +kernel
def block58 : List Step := [step37, step40, step142, step217, step218, step219, step217, step218, step219, step217, step218, step219, step217, step218, step219, step220, step221, step215, step216, step220]
lemma block58_checked : checkPrefix block58 (-45) (20) (102) (84) = true := by decide +kernel
def block59 : List Step := [step221, step215, step216, step220, step221, step215, step216, step220, step221, step215, step216, step220, step221, step215, step216, step220, step221, step215, step216, step220]
lemma block59_checked : checkPrefix block59 (102) (84) (102) (84) = true := by decide +kernel

def block60 : List Step := [step221, step215, step216, step220, step221, step215, step216, step222, step223, step177, step173, step224, step173, step224, step173, step224, step173, step224, step173, step224]
lemma block60_checked : checkPrefix block60 (102) (84) (0) (0) = true := by decide +kernel
def block61 : List Step := [step173, step224, step173, step224, step173, step224, step173, step224, step173, step224, step173, step224, step173, step224, step173, step224, step173, step225, step226, step225]
lemma block61_checked : checkPrefix block61 (0) (0) (62) (-6) = true := by decide +kernel
def block62 : List Step := [step226, step225, step226, step227, step65, step3, step155, step227, step65, step3, step155, step227, step65, step3, step155, step227, step65, step3, step155, step227]
lemma block62_checked : checkPrefix block62 (62) (-6) (-17) (-14) = true := by decide +kernel
def block63 : List Step := [step65, step3, step155, step227, step65, step3, step155, step227, step65, step3, step155, step227, step65, step3, step228, step229, step65, step3, step228, step229]
lemma block63_checked : checkPrefix block63 (-17) (-14) (-17) (-14) = true := by decide +kernel
def block64 : List Step := [step65, step3, step228, step229, step65, step3, step228, step229, step65, step3, step228, step229, step65, step230, step21, step22, step227, step231, step21, step22]
lemma block64_checked : checkPrefix block64 (-17) (-14) (14) (-17) = true := by decide +kernel
def block65 : List Step := [step227, step231, step21, step22, step232, step233, step202, step232, step233, step202, step232, step233, step234, step109, step110, step232, step233, step234, step109, step110]
lemma block65_checked : checkPrefix block65 (14) (-17) (14) (-17) = true := by decide +kernel
def block66 : List Step := [step232, step235, step109, step110, step232, step235, step109, step110, step232, step235, step109, step110, step236, step229, step231, step21, step22, step236, step229, step231]
lemma block66_checked : checkPrefix block66 (14) (-17) (-87) (71) = true := by decide +kernel
def block67 : List Step := [step21, step22, step236, step229, step231, step237, step77, step142, step236, step238, step73, step236, step238, step73, step236, step238, step73, step239, step141, step40]
lemma block67_checked : checkPrefix block67 (-87) (71) (-98) (119) = true := by decide +kernel
def block68 : List Step := [step142, step239, step141, step40, step142, step239, step141, step40, step142, step239, step141, step40, step142, step239, step141, step40, step142, step239, step141, step40]
lemma block68_checked : checkPrefix block68 (-98) (119) (-98) (119) = true := by decide +kernel
def block69 : List Step := [step142, step239, step141, step40, step142, step239, step240, step241, step242, step243, step244, step245, step20, step246, step57, step247, step135, step246, step57, step248]
lemma block69_checked : checkPrefix block69 (-98) (119) (-90) (40) = true := by decide +kernel

def block70 : List Step := [step82, step246, step249, step250, step182, step184, step185, step37, step40, step142, step246, step249, step250, step182, step184, step185, step251, step28, step246, step249]
lemma block70_checked : checkPrefix block70 (-90) (40) (84) (-102) = true := by decide +kernel
def block71 : List Step := [step250, step182, step184, step185, step251, step28, step246, step249, step250, step182, step184, step185, step251, step28, step246, step249, step250, step182, step184, step185]
lemma block71_checked : checkPrefix block71 (84) (-102) (-45) (20) = true := by decide +kernel
def block72 : List Step := [step251, step28, step246, step249, step250, step182, step184, step252, step253, step246, step249, step250, step254, step163, step255, step35, step255, step256, step257, step190]
lemma block72_checked : checkPrefix block72 (-45) (20) (22) (-96) = true := by decide +kernel
def block73 : List Step := [step22, step255, step256, step257, step190, step22, step258, step248, step82, step258, step248, step259, step260, step245, step20, step258, step248, step259, step260, step245]
lemma block73_checked : checkPrefix block73 (22) (-96) (-127) (-19) = true := by decide +kernel
def block74 : List Step := [step261, step126, step258, step248, step259, step260, step245, step261, step126, step258, step248, step259, step260, step245, step261, step126, step258, step248, step259, step260]
lemma block74_checked : checkPrefix block74 (-127) (-19) (71) (87) = true := by decide +kernel
def block75 : List Step := [step245, step261, step126, step258, step248, step259, step260, step245, step261, step126, step258, step248, step259, step260, step262, step263, step168, step218, step219, step258]
lemma block75_checked : checkPrefix block75 (71) (87) (26) (107) = true := by decide +kernel
def block76 : List Step := [step248, step259, step264, step265, step266, step73, step266, step267, step266, step267, step266, step267, step266, step268, step269, step267, step270, step241, step242, step270]
lemma block76_checked : checkPrefix block76 (26) (107) (48) (11) = true := by decide +kernel
def block77 : List Step := [step241, step242, step270, step241, step242, step270, step241, step242, step270, step241, step242, step270, step271, step272, step53, step273, step274, step275, step261, step126]
lemma block77_checked : checkPrefix block77 (48) (11) (14) (-17) = true := by decide +kernel
def block78 : List Step := [step273, step276, step254, step163, step273, step276, step254, step163, step273, step276, step254, step163, step273, step276, step254, step163, step273, step276, step254, step163]
lemma block78_checked : checkPrefix block78 (14) (-17) (14) (-17) = true := by decide +kernel
def block79 : List Step := [step273, step276, step254, step163, step273, step276, step254, step163, step273, step277, step278, step69, step252, step257, step190, step22, step273, step277, step278, step69]
lemma block79_checked : checkPrefix block79 (14) (-17) (70) (-85) = true := by decide +kernel

def block80 : List Step := [step252, step279, step110, step273, step277, step278, step69, step252, step279, step110, step273, step277, step278, step69, step252, step279, step110, step280, step281, step282]
lemma block80_checked : checkPrefix block80 (70) (-85) (14) (-17) = true := by decide +kernel
def block81 : List Step := [step280, step283, step284, step280, step285, step286, step110, step280, step285, step286, step110, step280, step285, step286, step110, step280, step287, step288, step215, step216]
lemma block81_checked : checkPrefix block81 (14) (-17) (14) (-17) = true := by decide +kernel
def block82 : List Step := [step280, step287, step288, step289, step126, step280, step287, step288, step289, step126, step280, step287, step288, step289, step126, step280, step287, step288, step289, step126]
lemma block82_checked : checkPrefix block82 (14) (-17) (14) (-17) = true := by decide +kernel
def block83 : List Step := [step280, step287, step288, step289, step126, step290, step291, step292, step91, step290, step291, step292, step91, step290, step291, step292, step91, step290, step291, step292]
lemma block83_checked : checkPrefix block83 (14) (-17) (-62) (6) = true := by decide +kernel
def block84 : List Step := [step91, step290, step291, step292, step91, step290, step291, step292, step91, step290, step291, step292, step91, step290, step291, step292, step91, step290, step293, step29]
lemma block84_checked : checkPrefix block84 (-62) (6) (90) (-40) = true := by decide +kernel
def block85 : List Step := [step256, step279, step294, step290, step293, step29, step256, step279, step295, step206, step159, step162, step163, step290, step293, step29, step256, step279, step296, step173]
lemma block85_checked : checkPrefix block85 (90) (-40) (14) (-17) = true := by decide +kernel
def block86 : List Step := [step290, step293, step29, step256, step279, step296, step173, step290, step293, step297, step53, step290, step293, step297, step53, step290, step293, step297, step298, step235]
lemma block86_checked : checkPrefix block86 (14) (-17) (-51) (-42) = true := by decide +kernel
def block87 : List Step := [step109, step296, step173, step290, step293, step299, step290, step300, step28, step290, step300, step28, step290, step300, step28, step290, step300, step28, step290, step300]
lemma block87_checked : checkPrefix block87 (-51) (-42) (-99) (-53) = true := by decide +kernel
def block88 : List Step := [step28, step290, step300, step28, step290, step300, step28, step290, step301, step302, step303, step271, step272, step304, step290, step305, step22, step290, step305, step22]
lemma block88_checked : checkPrefix block88 (-99) (-53) (14) (-17) = true := by decide +kernel
def block89 : List Step := [step290, step305, step22, step290, step305, step22, step290, step306, step307, step287, step288, step289, step126, step290, step308, step309, step310, step112, step162, step163]
lemma block89_checked : checkPrefix block89 (14) (-17) (14) (-17) = true := by decide +kernel

def block90 : List Step := [step290, step308, step309, step310, step311, step290, step308, step309, step310, step311, step290, step308, step309, step310, step311, step290, step308, step309, step310, step311]
lemma block90_checked : checkPrefix block90 (14) (-17) (14) (-17) = true := by decide +kernel
def block91 : List Step := [step290, step308, step309, step310, step312, step69, step287, step288, step313, step250, step314, step39, step230, step237, step277, step278, step69, step287, step288, step313]
lemma block91_checked : checkPrefix block91 (14) (-17) (84) (-102) = true := by decide +kernel
def block92 : List Step := [step315, step201, step234, step109, step296, step173, step290, step308, step309, step310, step312, step69, step287, step288, step313, step315, step201, step234, step109, step296]
lemma block92_checked : checkPrefix block92 (84) (-102) (0) (0) = true := by decide +kernel
def block93 : List Step := [step173, step290, step308, step316, step219, step290, step317, step318, step313, step315, step319, step290, step320, step321, step142, step290, step322, step126, step290, step322]
lemma block93_checked : checkPrefix block93 (0) (0) (-37) (-59) = true := by decide +kernel
def block94 : List Step := [step126, step290, step322, step126, step290, step322, step126, step290, step322, step126, step290, step323, step324, step240, step271, step272, step304, step290, step323, step324]
lemma block94_checked : checkPrefix block94 (-37) (-59) (85) (70) = true := by decide +kernel
def block95 : List Step := [step240, step271, step272, step304, step290, step323, step324, step240, step325, step326, step290, step323, step324, step240, step327, step328, step313, step315, step319, step290]
lemma block95_checked : checkPrefix block95 (85) (70) (113) (36) = true := by decide +kernel
def block96 : List Step := [step323, step324, step329, step330, step290, step331, step332, step290, step333, step334, step335, step336, step337, step290, step308, step316, step338, step168, step218, step338]
lemma block96_checked : checkPrefix block96 (113) (36) (65) (25) = true := by decide +kernel
def block97 : List Step := [step168, step218, step338, step168, step218, step338, step168]
lemma block97_checked : checkPrefix block97 (65) (25) (42) (-51) = true := by decide +kernel
def tail98 : List Step := []
lemma tail98_checked : checkPath tail98 42 (-51) = true := by decide +kernel
attribute [irreducible] checkPath checkPrefix checkStep
def tail97 : List Step := block97 ++ tail98
lemma tail97_checked : checkPath tail97 (65) (25) = true :=
  checkPath_append block97 tail98 (65) (25) (42) (-51) block97_checked tail98_checked
def tail96 : List Step := block96 ++ tail97
lemma tail96_checked : checkPath tail96 (113) (36) = true :=
  checkPath_append block96 tail97 (113) (36) (65) (25) block96_checked tail97_checked
def tail95 : List Step := block95 ++ tail96
lemma tail95_checked : checkPath tail95 (85) (70) = true :=
  checkPath_append block95 tail96 (85) (70) (113) (36) block95_checked tail96_checked
def tail94 : List Step := block94 ++ tail95
lemma tail94_checked : checkPath tail94 (-37) (-59) = true :=
  checkPath_append block94 tail95 (-37) (-59) (85) (70) block94_checked tail95_checked
def tail93 : List Step := block93 ++ tail94
lemma tail93_checked : checkPath tail93 (0) (0) = true :=
  checkPath_append block93 tail94 (0) (0) (-37) (-59) block93_checked tail94_checked
def tail92 : List Step := block92 ++ tail93
lemma tail92_checked : checkPath tail92 (84) (-102) = true :=
  checkPath_append block92 tail93 (84) (-102) (0) (0) block92_checked tail93_checked
def tail91 : List Step := block91 ++ tail92
lemma tail91_checked : checkPath tail91 (14) (-17) = true :=
  checkPath_append block91 tail92 (14) (-17) (84) (-102) block91_checked tail92_checked
def tail90 : List Step := block90 ++ tail91
lemma tail90_checked : checkPath tail90 (14) (-17) = true :=
  checkPath_append block90 tail91 (14) (-17) (14) (-17) block90_checked tail91_checked
def tail89 : List Step := block89 ++ tail90
lemma tail89_checked : checkPath tail89 (14) (-17) = true :=
  checkPath_append block89 tail90 (14) (-17) (14) (-17) block89_checked tail90_checked
def tail88 : List Step := block88 ++ tail89
lemma tail88_checked : checkPath tail88 (-99) (-53) = true :=
  checkPath_append block88 tail89 (-99) (-53) (14) (-17) block88_checked tail89_checked
def tail87 : List Step := block87 ++ tail88
lemma tail87_checked : checkPath tail87 (-51) (-42) = true :=
  checkPath_append block87 tail88 (-51) (-42) (-99) (-53) block87_checked tail88_checked
def tail86 : List Step := block86 ++ tail87
lemma tail86_checked : checkPath tail86 (14) (-17) = true :=
  checkPath_append block86 tail87 (14) (-17) (-51) (-42) block86_checked tail87_checked
def tail85 : List Step := block85 ++ tail86
lemma tail85_checked : checkPath tail85 (90) (-40) = true :=
  checkPath_append block85 tail86 (90) (-40) (14) (-17) block85_checked tail86_checked
def tail84 : List Step := block84 ++ tail85
lemma tail84_checked : checkPath tail84 (-62) (6) = true :=
  checkPath_append block84 tail85 (-62) (6) (90) (-40) block84_checked tail85_checked
def tail83 : List Step := block83 ++ tail84
lemma tail83_checked : checkPath tail83 (14) (-17) = true :=
  checkPath_append block83 tail84 (14) (-17) (-62) (6) block83_checked tail84_checked
def tail82 : List Step := block82 ++ tail83
lemma tail82_checked : checkPath tail82 (14) (-17) = true :=
  checkPath_append block82 tail83 (14) (-17) (14) (-17) block82_checked tail83_checked
def tail81 : List Step := block81 ++ tail82
lemma tail81_checked : checkPath tail81 (14) (-17) = true :=
  checkPath_append block81 tail82 (14) (-17) (14) (-17) block81_checked tail82_checked
def tail80 : List Step := block80 ++ tail81
lemma tail80_checked : checkPath tail80 (70) (-85) = true :=
  checkPath_append block80 tail81 (70) (-85) (14) (-17) block80_checked tail81_checked
def tail79 : List Step := block79 ++ tail80
lemma tail79_checked : checkPath tail79 (14) (-17) = true :=
  checkPath_append block79 tail80 (14) (-17) (70) (-85) block79_checked tail80_checked
def tail78 : List Step := block78 ++ tail79
lemma tail78_checked : checkPath tail78 (14) (-17) = true :=
  checkPath_append block78 tail79 (14) (-17) (14) (-17) block78_checked tail79_checked
def tail77 : List Step := block77 ++ tail78
lemma tail77_checked : checkPath tail77 (48) (11) = true :=
  checkPath_append block77 tail78 (48) (11) (14) (-17) block77_checked tail78_checked
def tail76 : List Step := block76 ++ tail77
lemma tail76_checked : checkPath tail76 (26) (107) = true :=
  checkPath_append block76 tail77 (26) (107) (48) (11) block76_checked tail77_checked
def tail75 : List Step := block75 ++ tail76
lemma tail75_checked : checkPath tail75 (71) (87) = true :=
  checkPath_append block75 tail76 (71) (87) (26) (107) block75_checked tail76_checked
def tail74 : List Step := block74 ++ tail75
lemma tail74_checked : checkPath tail74 (-127) (-19) = true :=
  checkPath_append block74 tail75 (-127) (-19) (71) (87) block74_checked tail75_checked
def tail73 : List Step := block73 ++ tail74
lemma tail73_checked : checkPath tail73 (22) (-96) = true :=
  checkPath_append block73 tail74 (22) (-96) (-127) (-19) block73_checked tail74_checked
def tail72 : List Step := block72 ++ tail73
lemma tail72_checked : checkPath tail72 (-45) (20) = true :=
  checkPath_append block72 tail73 (-45) (20) (22) (-96) block72_checked tail73_checked
def tail71 : List Step := block71 ++ tail72
lemma tail71_checked : checkPath tail71 (84) (-102) = true :=
  checkPath_append block71 tail72 (84) (-102) (-45) (20) block71_checked tail72_checked
def tail70 : List Step := block70 ++ tail71
lemma tail70_checked : checkPath tail70 (-90) (40) = true :=
  checkPath_append block70 tail71 (-90) (40) (84) (-102) block70_checked tail71_checked
def tail69 : List Step := block69 ++ tail70
lemma tail69_checked : checkPath tail69 (-98) (119) = true :=
  checkPath_append block69 tail70 (-98) (119) (-90) (40) block69_checked tail70_checked
def tail68 : List Step := block68 ++ tail69
lemma tail68_checked : checkPath tail68 (-98) (119) = true :=
  checkPath_append block68 tail69 (-98) (119) (-98) (119) block68_checked tail69_checked
def tail67 : List Step := block67 ++ tail68
lemma tail67_checked : checkPath tail67 (-87) (71) = true :=
  checkPath_append block67 tail68 (-87) (71) (-98) (119) block67_checked tail68_checked
def tail66 : List Step := block66 ++ tail67
lemma tail66_checked : checkPath tail66 (14) (-17) = true :=
  checkPath_append block66 tail67 (14) (-17) (-87) (71) block66_checked tail67_checked
def tail65 : List Step := block65 ++ tail66
lemma tail65_checked : checkPath tail65 (14) (-17) = true :=
  checkPath_append block65 tail66 (14) (-17) (14) (-17) block65_checked tail66_checked
def tail64 : List Step := block64 ++ tail65
lemma tail64_checked : checkPath tail64 (-17) (-14) = true :=
  checkPath_append block64 tail65 (-17) (-14) (14) (-17) block64_checked tail65_checked
def tail63 : List Step := block63 ++ tail64
lemma tail63_checked : checkPath tail63 (-17) (-14) = true :=
  checkPath_append block63 tail64 (-17) (-14) (-17) (-14) block63_checked tail64_checked
def tail62 : List Step := block62 ++ tail63
lemma tail62_checked : checkPath tail62 (62) (-6) = true :=
  checkPath_append block62 tail63 (62) (-6) (-17) (-14) block62_checked tail63_checked
def tail61 : List Step := block61 ++ tail62
lemma tail61_checked : checkPath tail61 (0) (0) = true :=
  checkPath_append block61 tail62 (0) (0) (62) (-6) block61_checked tail62_checked
def tail60 : List Step := block60 ++ tail61
lemma tail60_checked : checkPath tail60 (102) (84) = true :=
  checkPath_append block60 tail61 (102) (84) (0) (0) block60_checked tail61_checked
def tail59 : List Step := block59 ++ tail60
lemma tail59_checked : checkPath tail59 (102) (84) = true :=
  checkPath_append block59 tail60 (102) (84) (102) (84) block59_checked tail60_checked
def tail58 : List Step := block58 ++ tail59
lemma tail58_checked : checkPath tail58 (-45) (20) = true :=
  checkPath_append block58 tail59 (-45) (20) (102) (84) block58_checked tail59_checked
def tail57 : List Step := block57 ++ tail58
lemma tail57_checked : checkPath tail57 (42) (-51) = true :=
  checkPath_append block57 tail58 (42) (-51) (-45) (20) block57_checked tail58_checked
def tail56 : List Step := block56 ++ tail57
lemma tail56_checked : checkPath tail56 (37) (59) = true :=
  checkPath_append block56 tail57 (37) (59) (42) (-51) block56_checked tail57_checked
def tail55 : List Step := block55 ++ tail56
lemma tail55_checked : checkPath tail55 (14) (-17) = true :=
  checkPath_append block55 tail56 (14) (-17) (37) (59) block55_checked tail56_checked
def tail54 : List Step := block54 ++ tail55
lemma tail54_checked : checkPath tail54 (14) (-17) = true :=
  checkPath_append block54 tail55 (14) (-17) (14) (-17) block54_checked tail55_checked
def tail53 : List Step := block53 ++ tail54
lemma tail53_checked : checkPath tail53 (-23) (-76) = true :=
  checkPath_append block53 tail54 (-23) (-76) (14) (-17) block53_checked tail54_checked
def tail52 : List Step := block52 ++ tail53
lemma tail52_checked : checkPath tail52 (34) (28) = true :=
  checkPath_append block52 tail53 (34) (28) (-23) (-76) block52_checked tail53_checked
def tail51 : List Step := block51 ++ tail52
lemma tail51_checked : checkPath tail51 (-130) (-50) = true :=
  checkPath_append block51 tail52 (-130) (-50) (34) (28) block51_checked tail52_checked
def tail50 : List Step := block50 ++ tail51
lemma tail50_checked : checkPath tail50 (14) (-17) = true :=
  checkPath_append block50 tail51 (14) (-17) (-130) (-50) block50_checked tail51_checked
def tail49 : List Step := block49 ++ tail50
lemma tail49_checked : checkPath tail49 (-101) (88) = true :=
  checkPath_append block49 tail50 (-101) (88) (14) (-17) block49_checked tail50_checked
def tail48 : List Step := block48 ++ tail49
lemma tail48_checked : checkPath tail48 (14) (-17) = true :=
  checkPath_append block48 tail49 (14) (-17) (-101) (88) block48_checked tail49_checked
def tail47 : List Step := block47 ++ tail48
lemma tail47_checked : checkPath tail47 (22) (-96) = true :=
  checkPath_append block47 tail48 (22) (-96) (14) (-17) block47_checked tail48_checked
def tail46 : List Step := block46 ++ tail47
lemma tail46_checked : checkPath tail46 (-84) (102) = true :=
  checkPath_append block46 tail47 (-84) (102) (22) (-96) block46_checked tail47_checked
def tail45 : List Step := block45 ++ tail46
lemma tail45_checked : checkPath tail45 (-31) (3) = true :=
  checkPath_append block45 tail46 (-31) (3) (-84) (102) block45_checked tail46_checked
def tail44 : List Step := block44 ++ tail45
lemma tail44_checked : checkPath tail44 (14) (-17) = true :=
  checkPath_append block44 tail45 (14) (-17) (-31) (3) block44_checked tail45_checked
def tail43 : List Step := block43 ++ tail44
lemma tail43_checked : checkPath tail43 (14) (-17) = true :=
  checkPath_append block43 tail44 (14) (-17) (14) (-17) block43_checked tail44_checked
def tail42 : List Step := block42 ++ tail43
lemma tail42_checked : checkPath tail42 (-5) (110) = true :=
  checkPath_append block42 tail43 (-5) (110) (14) (-17) block42_checked tail43_checked
def tail41 : List Step := block41 ++ tail42
lemma tail41_checked : checkPath tail41 (68) (56) = true :=
  checkPath_append block41 tail42 (68) (56) (-5) (110) block41_checked tail42_checked
def tail40 : List Step := block40 ++ tail41
lemma tail40_checked : checkPath tail40 (14) (-17) = true :=
  checkPath_append block40 tail41 (14) (-17) (68) (56) block40_checked tail41_checked
def tail39 : List Step := block39 ++ tail40
lemma tail39_checked : checkPath tail39 (65) (25) = true :=
  checkPath_append block39 tail40 (65) (25) (14) (-17) block39_checked tail40_checked
def tail38 : List Step := block38 ++ tail39
lemma tail38_checked : checkPath tail38 (-36) (113) = true :=
  checkPath_append block38 tail39 (-36) (113) (65) (25) block38_checked tail39_checked
def tail37 : List Step := block37 ++ tail38
lemma tail37_checked : checkPath tail37 (-36) (113) = true :=
  checkPath_append block37 tail38 (-36) (113) (-36) (113) block37_checked tail38_checked
def tail36 : List Step := block36 ++ tail37
lemma tail36_checked : checkPath tail36 (-98) (119) = true :=
  checkPath_append block36 tail37 (-98) (119) (-36) (113) block36_checked tail37_checked
def tail35 : List Step := block35 ++ tail36
lemma tail35_checked : checkPath tail35 (-3) (-31) = true :=
  checkPath_append block35 tail36 (-3) (-31) (-98) (119) block35_checked tail36_checked
def tail34 : List Step := block34 ++ tail35
lemma tail34_checked : checkPath tail34 (14) (-17) = true :=
  checkPath_append block34 tail35 (14) (-17) (-3) (-31) block34_checked tail35_checked
def tail33 : List Step := block33 ++ tail34
lemma tail33_checked : checkPath tail33 (-98) (119) = true :=
  checkPath_append block33 tail34 (-98) (119) (14) (-17) block33_checked tail34_checked
def tail32 : List Step := block32 ++ tail33
lemma tail32_checked : checkPath tail32 (-98) (119) = true :=
  checkPath_append block32 tail33 (-98) (119) (-98) (119) block32_checked tail33_checked
def tail31 : List Step := block31 ++ tail32
lemma tail31_checked : checkPath tail31 (-116) (-67) = true :=
  checkPath_append block31 tail32 (-116) (-67) (-98) (119) block31_checked tail32_checked
def tail30 : List Step := block30 ++ tail31
lemma tail30_checked : checkPath tail30 (14) (-17) = true :=
  checkPath_append block30 tail31 (14) (-17) (-116) (-67) block30_checked tail31_checked
def tail29 : List Step := block29 ++ tail30
lemma tail29_checked : checkPath tail29 (-121) (43) = true :=
  checkPath_append block29 tail30 (-121) (43) (14) (-17) block29_checked tail30_checked
def tail28 : List Step := block28 ++ tail29
lemma tail28_checked : checkPath tail28 (14) (-17) = true :=
  checkPath_append block28 tail29 (14) (-17) (-121) (43) block28_checked tail29_checked
def tail27 : List Step := block27 ++ tail28
lemma tail27_checked : checkPath tail27 (-68) (-56) = true :=
  checkPath_append block27 tail28 (-68) (-56) (14) (-17) block27_checked tail28_checked
def tail26 : List Step := block26 ++ tail27
lemma tail26_checked : checkPath tail26 (-11) (48) = true :=
  checkPath_append block26 tail27 (-11) (48) (-68) (-56) block26_checked tail27_checked
def tail25 : List Step := block25 ++ tail26
lemma tail25_checked : checkPath tail25 (-11) (48) = true :=
  checkPath_append block25 tail26 (-11) (48) (-11) (48) block25_checked tail26_checked
def tail24 : List Step := block24 ++ tail25
lemma tail24_checked : checkPath tail24 (14) (-17) = true :=
  checkPath_append block24 tail25 (14) (-17) (-11) (48) block24_checked tail25_checked
def tail23 : List Step := block23 ++ tail24
lemma tail23_checked : checkPath tail23 (73) (-54) = true :=
  checkPath_append block23 tail24 (73) (-54) (14) (-17) block23_checked tail24_checked
def tail22 : List Step := block22 ++ tail23
lemma tail22_checked : checkPath tail22 (-118) (74) = true :=
  checkPath_append block22 tail23 (-118) (74) (73) (-54) block22_checked tail23_checked
def tail21 : List Step := block21 ++ tail22
lemma tail21_checked : checkPath tail21 (14) (-17) = true :=
  checkPath_append block21 tail22 (14) (-17) (-118) (74) block21_checked tail22_checked
def tail20 : List Step := block20 ++ tail21
lemma tail20_checked : checkPath tail20 (14) (-17) = true :=
  checkPath_append block20 tail21 (14) (-17) (14) (-17) block20_checked tail21_checked
def tail19 : List Step := block19 ++ tail20
lemma tail19_checked : checkPath tail19 (14) (-17) = true :=
  checkPath_append block19 tail20 (14) (-17) (14) (-17) block19_checked tail20_checked
def tail18 : List Step := block18 ++ tail19
lemma tail18_checked : checkPath tail18 (14) (-17) = true :=
  checkPath_append block18 tail19 (14) (-17) (14) (-17) block18_checked tail19_checked
def tail17 : List Step := block17 ++ tail18
lemma tail17_checked : checkPath tail17 (-68) (-56) = true :=
  checkPath_append block17 tail18 (-68) (-56) (14) (-17) block17_checked tail18_checked
def tail16 : List Step := block16 ++ tail17
lemma tail16_checked : checkPath tail16 (14) (-17) = true :=
  checkPath_append block16 tail17 (14) (-17) (-68) (-56) block16_checked tail17_checked
def tail15 : List Step := block15 ++ tail16
lemma tail15_checked : checkPath tail15 (14) (-17) = true :=
  checkPath_append block15 tail16 (14) (-17) (14) (-17) block15_checked tail16_checked
def tail14 : List Step := block14 ++ tail15
lemma tail14_checked : checkPath tail14 (-121) (43) = true :=
  checkPath_append block14 tail15 (-121) (43) (14) (-17) block14_checked tail15_checked
def tail13 : List Step := block13 ++ tail14
lemma tail13_checked : checkPath tail13 (-31) (3) = true :=
  checkPath_append block13 tail14 (-31) (3) (-121) (43) block13_checked tail14_checked
def tail12 : List Step := block12 ++ tail13
lemma tail12_checked : checkPath tail12 (-31) (3) = true :=
  checkPath_append block12 tail13 (-31) (3) (-31) (3) block12_checked tail13_checked
def tail11 : List Step := block11 ++ tail12
lemma tail11_checked : checkPath tail11 (-81) (133) = true :=
  checkPath_append block11 tail12 (-81) (133) (-31) (3) block11_checked tail12_checked
def tail10 : List Step := block10 ++ tail11
lemma tail10_checked : checkPath tail10 (-98) (119) = true :=
  checkPath_append block10 tail11 (-98) (119) (-81) (133) block10_checked tail11_checked
def tail9 : List Step := block9 ++ tail10
lemma tail9_checked : checkPath tail9 (34) (28) = true :=
  checkPath_append block9 tail10 (34) (28) (-98) (119) block9_checked tail10_checked
def tail8 : List Step := block8 ++ tail9
lemma tail8_checked : checkPath tail8 (-84) (102) = true :=
  checkPath_append block8 tail9 (-84) (102) (34) (28) block8_checked tail9_checked
def tail7 : List Step := block7 ++ tail8
lemma tail7_checked : checkPath tail7 (-84) (102) = true :=
  checkPath_append block7 tail8 (-84) (102) (-84) (102) block7_checked tail8_checked
def tail6 : List Step := block6 ++ tail7
lemma tail6_checked : checkPath tail6 (-104) (57) = true :=
  checkPath_append block6 tail7 (-104) (57) (-84) (102) block6_checked tail7_checked
def tail5 : List Step := block5 ++ tail6
lemma tail5_checked : checkPath tail5 (-118) (74) = true :=
  checkPath_append block5 tail6 (-118) (74) (-104) (57) block5_checked tail6_checked
def tail4 : List Step := block4 ++ tail5
lemma tail4_checked : checkPath tail4 (14) (-17) = true :=
  checkPath_append block4 tail5 (14) (-17) (-118) (74) block4_checked tail5_checked
def tail3 : List Step := block3 ++ tail4
lemma tail3_checked : checkPath tail3 (-87) (71) = true :=
  checkPath_append block3 tail4 (-87) (71) (14) (-17) block3_checked tail4_checked
def tail2 : List Step := block2 ++ tail3
lemma tail2_checked : checkPath tail2 (-104) (57) = true :=
  checkPath_append block2 tail3 (-104) (57) (-87) (71) block2_checked tail3_checked
def tail1 : List Step := block1 ++ tail2
lemma tail1_checked : checkPath tail1 (93) (-9) = true :=
  checkPath_append block1 tail2 (93) (-9) (-104) (57) block1_checked tail2_checked
def tail0 : List Step := block0 ++ tail1
lemma tail0_checked : checkPath tail0 (0) (0) = true :=
  checkPath_append block0 tail1 (0) (0) (93) (-9) block0_checked tail1_checked

def steps : List Step := tail0
lemma path_verified : checkPath steps 0 0 = true := tail0_checked


abbrev Stats := ℕ × ℕ × ℕ × ℕ × ℕ

def stats (xs : List Step) (j : Fin 4) : Stats :=
  ((xs.map (fun s => s.constant j)).sum,
   (xs.map (fun s => s.slope j)).sum,
   (xs.map (fun s => s.constant j ^ 2)).sum,
   (xs.map (fun s => s.constant j * s.slope j)).sum,
   (xs.map (fun s => s.slope j ^ 2)).sum)

def addStats (a b : Stats) : Stats :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1,
    a.2.2.2.1 + b.2.2.2.1, a.2.2.2.2 + b.2.2.2.2)

lemma stats_append (xs ys : List Step) (j : Fin 4) :
    stats (xs ++ ys) j = addStats (stats xs j) (stats ys j) := by
  simp [stats, addStats, List.map_append, List.sum_append]

lemma stats_eq_iff (xs : List Step) (j : Fin 4) (a b c d e : ℕ) :
    stats xs j = (a,b,c,d,e) ↔
    (xs.map (fun s => s.constant j)).sum = a ∧
    (xs.map (fun s => s.slope j)).sum = b ∧
    (xs.map (fun s => s.constant j ^ 2)).sum = c ∧
    (xs.map (fun s => s.constant j * s.slope j)).sum = d ∧
    (xs.map (fun s => s.slope j ^ 2)).sum = e := by
  simp only [stats, Prod.mk.injEq]

def bounded (s : Step) : Bool := decide (∀ j : Fin 4,
  s.constant j ≤ 63 ∧ s.slope j ≤ 242)


lemma block0_info : block0.length = 20 ∧
    block0.all bounded = true ∧ ∀ j : Fin 4, stats block0 j = (![(1010, 3446, 57452, 196467, 707832), (594, 2383, 22346, 87398, 351893), (272, 669, 9856, 23596, 75641), (873, 3518, 45719, 180794, 729944)]) j := by decide +kernel
lemma block1_info : block1.length = 20 ∧
    block1.all bounded = true ∧ ∀ j : Fin 4, stats block1 j = (![(906, 2314, 44554, 124773, 423948), (817, 3572, 39089, 155498, 683792), (710, 1680, 30596, 66527, 158844), (307, 1840, 10127, 43597, 275716)]) j := by decide +kernel
lemma block2_info : block2.length = 20 ∧
    block2.all bounded = true ∧ ∀ j : Fin 4, stats block2 j = (![(839, 2628, 42215, 141875, 493480), (758, 2429, 35078, 113184, 411045), (585, 1585, 22785, 60698, 163741), (612, 1990, 24668, 80364, 306224)]) j := by decide +kernel
lemma block3_info : block3.length = 20 ∧
    block3.all bounded = true ∧ ∀ j : Fin 4, stats block3 j = (![(791, 2740, 36515, 135235, 518974), (1016, 4020, 56344, 219340, 869096), (495, 1648, 19731, 60072, 187888), (513, 2156, 18977, 75894, 321362)]) j := by decide +kernel
lemma block4_info : block4.length = 20 ∧
    block4.all bounded = true ∧ ∀ j : Fin 4, stats block4 j = (![(924, 3261, 48704, 170917, 624743), (481, 2193, 21723, 69444, 343317), (462, 1579, 17392, 57353, 219225), (528, 2413, 24410, 91034, 463655)]) j := by decide +kernel
lemma block5_info : block5.length = 20 ∧
    block5.all bounded = true ∧ ∀ j : Fin 4, stats block5 j = (![(924, 3396, 46916, 167191, 664662), (284, 1768, 8956, 36811, 293698), (424, 1628, 17358, 52893, 238938), (754, 3566, 38614, 149363, 705842)]) j := by decide +kernel
lemma block6_info : block6.length = 20 ∧
    block6.all bounded = true ∧ ∀ j : Fin 4, stats block6 j = (![(861, 2938, 41569, 140137, 544192), (398, 1489, 14358, 48996, 201253), (577, 1859, 25943, 77017, 275277), (662, 2558, 29568, 108489, 448828)]) j := by decide +kernel
lemma block7_info : block7.length = 20 ∧
    block7.all bounded = true ∧ ∀ j : Fin 4, stats block7 j = (![(848, 3728, 39864, 161552, 709232), (344, 924, 12464, 32200, 88108), (404, 1956, 14156, 62704, 317868), (848, 2752, 40624, 137884, 494992)]) j := by decide +kernel
lemma block8_info : block8.length = 20 ∧
    block8.all bounded = true ∧ ∀ j : Fin 4, stats block8 j = (![(764, 2818, 34758, 119751, 488320), (541, 2244, 21603, 76223, 373040), (562, 2086, 21680, 70057, 306872), (684, 2802, 27616, 105908, 504048)]) j := by decide +kernel
lemma block9_info : block9.length = 20 ∧
    block9.all bounded = true ∧ ∀ j : Fin 4, stats block9 j = (![(886, 3366, 44532, 163638, 617996), (412, 1593, 18008, 51039, 198259), (310, 1181, 9714, 38631, 167311), (864, 3312, 39244, 152184, 662524)]) j := by decide +kernel

lemma block10_info : block10.length = 20 ∧
    block10.all bounded = true ∧ ∀ j : Fin 4, stats block10 j = (![(786, 2850, 36170, 127090, 495602), (634, 2560, 26216, 102228, 462758), (556, 2006, 22452, 76243, 303818), (644, 2622, 28772, 100528, 415922)]) j := by decide +kernel
lemma block11_info : block11.length = 20 ∧
    block11.all bounded = true ∧ ∀ j : Fin 4, stats block11 j = (![(709, 2153, 31489, 96440, 359553), (547, 2649, 22477, 105665, 519267), (590, 1819, 25030, 66986, 226035), (602, 2953, 27952, 117819, 536385)]) j := by decide +kernel
lemma block12_info : block12.length = 20 ∧
    block12.all bounded = true ∧ ∀ j : Fin 4, stats block12 j = (![(918, 3388, 45998, 158956, 615012), (394, 2174, 13186, 63126, 373418), (354, 1374, 9294, 37092, 224426), (748, 3528, 32560, 139344, 667004)]) j := by decide +kernel
lemma block13_info : block13.length = 20 ∧
    block13.all bounded = true ∧ ∀ j : Fin 4, stats block13 j = (![(860, 3073, 43638, 147726, 551731), (580, 2519, 26158, 99937, 442519), (413, 1437, 14173, 49928, 235791), (753, 3209, 33789, 136647, 609079)]) j := by decide +kernel
lemma block14_info : block14.length = 20 ∧
    block14.all bounded = true ∧ ∀ j : Fin 4, stats block14 j = (![(740, 2621, 33722, 121040, 455833), (560, 2178, 25864, 97300, 383702), (764, 2724, 36758, 127617, 457570), (620, 2443, 26400, 100051, 401365)]) j := by decide +kernel
lemma block15_info : block15.length = 20 ∧
    block15.all bounded = true ∧ ∀ j : Fin 4, stats block15 j = (![(641, 2872, 28223, 119400, 527626), (508, 1686, 20392, 64624, 218304), (563, 2520, 23021, 97183, 428184), (811, 2760, 39279, 137211, 502046)]) j := by decide +kernel
lemma block16_info : block16.length = 20 ∧
    block16.all bounded = true ∧ ∀ j : Fin 4, stats block16 j = (![(777, 1981, 32531, 86391, 278477), (630, 2648, 23270, 91400, 406828), (532, 1116, 18186, 38182, 104820), (750, 3287, 39396, 147707, 617345)]) j := by decide +kernel
lemma block17_info : block17.length = 20 ∧
    block17.all bounded = true ∧ ∀ j : Fin 4, stats block17 j = (![(762, 2688, 31894, 109029, 488282), (762, 2294, 33442, 99859, 332338), (524, 1670, 19366, 47825, 208594), (687, 2060, 29383, 92806, 332666)]) j := by decide +kernel
lemma block18_info : block18.length = 20 ∧
    block18.all bounded = true ∧ ∀ j : Fin 4, stats block18 j = (![(721, 2646, 29347, 108223, 486932), (788, 2243, 33570, 95937, 303133), (589, 2001, 23243, 65194, 251985), (653, 1762, 25289, 70156, 223800)]) j := by decide +kernel
lemma block19_info : block19.length = 20 ∧
    block19.all bounded = true ∧ ∀ j : Fin 4, stats block19 j = (![(640, 2920, 20660, 98360, 560800), (670, 2160, 25570, 62610, 263700), (520, 2380, 17440, 61880, 283220), (640, 1960, 34000, 62720, 192080)]) j := by decide +kernel

lemma block20_info : block20.length = 20 ∧
    block20.all bounded = true ∧ ∀ j : Fin 4, stats block20 j = (![(780, 2792, 33388, 120892, 501016), (700, 2836, 29268, 107908, 486444), (456, 1596, 15952, 48448, 175884), (712, 2912, 35640, 114196, 470136)]) j := by decide +kernel
lemma block21_info : block21.length = 20 ∧
    block21.all bounded = true ∧ ∀ j : Fin 4, stats block21 j = (![(912, 3186, 46358, 161935, 592072), (485, 1998, 21027, 74153, 296448), (390, 1236, 14342, 45526, 166268), (754, 3072, 33904, 134863, 574812)]) j := by decide +kernel
lemma block22_info : block22.length = 20 ∧
    block22.all bounded = true ∧ ∀ j : Fin 4, stats block22 j = (![(811, 2822, 39545, 142546, 527794), (626, 2526, 32788, 116360, 441236), (521, 1750, 23891, 76612, 252884), (538, 2240, 23890, 90527, 372766)]) j := by decide +kernel
lemma block23_info : block23.length = 20 ∧
    block23.all bounded = true ∧ ∀ j : Fin 4, stats block23 j = (![(777, 2811, 33757, 121370, 461943), (759, 3448, 38601, 155540, 691872), (602, 2256, 27288, 93764, 349200), (494, 2457, 22106, 84893, 389455)]) j := by decide +kernel
lemma block24_info : block24.length = 20 ∧
    block24.all bounded = true ∧ ∀ j : Fin 4, stats block24 j = (![(635, 2880, 20521, 90370, 437048), (795, 3705, 38119, 163267, 810857), (549, 2675, 21735, 90153, 429757), (442, 2260, 18736, 60485, 298228)]) j := by decide +kernel
lemma block25_info : block25.length = 20 ∧
    block25.all bounded = true ∧ ∀ j : Fin 4, stats block25 j = (![(750, 3193, 31786, 131093, 574375), (540, 2249, 19272, 68715, 281165), (633, 2779, 27903, 109461, 463141), (546, 2203, 24668, 92438, 386579)]) j := by decide +kernel
lemma block26_info : block26.length = 20 ∧
    block26.all bounded = true ∧ ∀ j : Fin 4, stats block26 j = (![(637, 1814, 20341, 58717, 238790), (760, 2272, 31744, 86728, 276280), (826, 2426, 36598, 99888, 344584), (429, 1142, 11985, 35319, 143326)]) j := by decide +kernel
lemma block27_info : block27.length = 20 ∧
    block27.all bounded = true ∧ ∀ j : Fin 4, stats block27 j = (![(675, 3435, 25805, 122592, 636483), (681, 2335, 29741, 101157, 386867), (299, 1939, 10753, 47845, 287555), (702, 2253, 34518, 108456, 371075)]) j := by decide +kernel
lemma block28_info : block28.length = 20 ∧
    block28.all bounded = true ∧ ∀ j : Fin 4, stats block28 j = (![(759, 2348, 31617, 96547, 355050), (772, 2089, 36436, 99256, 309885), (420, 907, 14704, 23559, 58961), (658, 1774, 26766, 80282, 291694)]) j := by decide +kernel
lemma block29_info : block29.length = 20 ∧
    block29.all bounded = true ∧ ∀ j : Fin 4, stats block29 j = (![(811, 2150, 39387, 105705, 348380), (783, 2680, 34439, 116661, 430530), (796, 2052, 39320, 102594, 345106), (759, 2774, 35545, 131115, 503644)]) j := by decide +kernel

lemma block30_info : block30.length = 20 ∧
    block30.all bounded = true ∧ ∀ j : Fin 4, stats block30 j = (![(720, 2647, 29024, 107594, 435911), (400, 2556, 13564, 64797, 385194), (700, 2772, 31416, 116546, 466942), (246, 1969, 8070, 35079, 241643)]) j := by decide +kernel
lemma block31_info : block31.length = 20 ∧
    block31.all bounded = true ∧ ∀ j : Fin 4, stats block31 j = (![(750, 2553, 35364, 112885, 418095), (504, 1749, 23378, 76488, 279335), (552, 1773, 25448, 78050, 300103), (765, 2801, 37053, 131584, 496267)]) j := by decide +kernel
lemma block32_info : block32.length = 20 ∧
    block32.all bounded = true ∧ ∀ j : Fin 4, stats block32 j = (![(730, 2545, 36790, 121560, 414695), (290, 1185, 7650, 24350, 118805), (220, 625, 3450, 8180, 34805), (815, 3225, 35855, 147230, 644195)]) j := by decide +kernel
lemma block33_info : block33.length = 20 ∧
    block33.all bounded = true ∧ ∀ j : Fin 4, stats block33 j = (![(623, 2061, 25451, 84015, 293405), (575, 2468, 23611, 95208, 416150), (499, 1648, 17407, 57140, 200198), (606, 2641, 25412, 102549, 451157)]) j := by decide +kernel
lemma block34_info : block34.length = 20 ∧
    block34.all bounded = true ∧ ∀ j : Fin 4, stats block34 j = (![(628, 2337, 25814, 81576, 310475), (543, 1556, 20783, 57393, 198290), (732, 2636, 35430, 113109, 419266), (617, 1857, 28477, 85027, 289319)]) j := by decide +kernel
lemma block35_info : block35.length = 20 ∧
    block35.all bounded = true ∧ ∀ j : Fin 4, stats block35 j = (![(646, 2493, 29288, 104782, 432965), (448, 2369, 15020, 64912, 409965), (450, 1875, 15246, 56891, 266569), (589, 2885, 27329, 95446, 469661)]) j := by decide +kernel
lemma block36_info : block36.length = 20 ∧
    block36.all bounded = true ∧ ∀ j : Fin 4, stats block36 j = (![(530, 2820, 20466, 87942, 504332), (326, 2385, 9424, 53516, 424443), (342, 2309, 12926, 50030, 338867), (620, 3328, 30924, 122418, 624828)]) j := by decide +kernel
lemma block37_info : block37.length = 20 ∧
    block37.all bounded = true ∧ ∀ j : Fin 4, stats block37 j = (![(715, 3015, 31075, 116400, 542375), (570, 2795, 24780, 109440, 510075), (280, 1475, 10920, 29110, 164635), (885, 3925, 47045, 189095, 800515)]) j := by decide +kernel
lemma block38_info : block38.length = 20 ∧
    block38.all bounded = true ∧ ∀ j : Fin 4, stats block38 j = (![(465, 2335, 18389, 73299, 383271), (663, 2385, 29271, 92029, 352959), (457, 2267, 20543, 76547, 365783), (697, 2409, 32249, 110048, 457747)]) j := by decide +kernel
lemma block39_info : block39.length = 20 ∧
    block39.all bounded = true ∧ ∀ j : Fin 4, stats block39 j = (![(533, 2339, 26605, 92329, 415657), (1006, 3152, 52852, 162366, 581018), (575, 2364, 27529, 97035, 399954), (619, 1633, 27811, 77426, 334821)]) j := by decide +kernel

lemma block40_info : block40.length = 20 ∧
    block40.all bounded = true ∧ ∀ j : Fin 4, stats block40 j = (![(562, 2097, 19872, 62182, 301553), (438, 2581, 15240, 73346, 425947), (775, 3083, 36257, 130649, 564899), (572, 3081, 27490, 114557, 583581)]) j := by decide +kernel
lemma block41_info : block41.length = 20 ∧
    block41.all bounded = true ∧ ∀ j : Fin 4, stats block41 j = (![(559, 2204, 18059, 57820, 332060), (468, 2122, 17858, 69662, 337240), (695, 2786, 31861, 103375, 474808), (684, 2922, 32450, 122070, 530112)]) j := by decide +kernel
lemma block42_info : block42.length = 20 ∧
    block42.all bounded = true ∧ ∀ j : Fin 4, stats block42 j = (![(587, 2225, 26375, 81507, 379831), (368, 935, 12756, 28078, 79949), (724, 2657, 34258, 107652, 478965), (792, 2559, 37760, 126868, 454175)]) j := by decide +kernel
lemma block43_info : block43.length = 20 ∧
    block43.all bounded = true ∧ ∀ j : Fin 4, stats block43 j = (![(501, 2132, 20159, 63137, 346898), (518, 1896, 22208, 65803, 322402), (621, 2570, 26205, 87994, 434598), (722, 2630, 34408, 104064, 450042)]) j := by decide +kernel
lemma block44_info : block44.length = 20 ∧
    block44.all bounded = true ∧ ∀ j : Fin 4, stats block44 j = (![(587, 2238, 26477, 94248, 358308), (601, 2579, 27047, 110075, 520997), (482, 1895, 21052, 76554, 306589), (695, 2930, 32055, 128527, 584356)]) j := by decide +kernel
lemma block45_info : block45.length = 20 ∧
    block45.all bounded = true ∧ ∀ j : Fin 4, stats block45 j = (![(631, 2281, 29783, 107505, 403061), (594, 1973, 28804, 93662, 347719), (558, 1951, 28344, 97858, 351787), (693, 2377, 32207, 114447, 455253)]) j := by decide +kernel
lemma block46_info : block46.length = 20 ∧
    block46.all bounded = true ∧ ∀ j : Fin 4, stats block46 j = (![(562, 1045, 21224, 46961, 137707), (614, 2620, 26320, 99326, 530138), (720, 1720, 30114, 72084, 184386), (506, 2415, 22476, 71675, 390339)]) j := by decide +kernel
lemma block47_info : block47.length = 20 ∧
    block47.all bounded = true ∧ ∀ j : Fin 4, stats block47 j = (![(564, 1801, 20560, 67002, 244717), (783, 2568, 37489, 113430, 390148), (782, 2558, 38944, 122265, 402516), (365, 1051, 10515, 25941, 112069)]) j := by decide +kernel
lemma block48_info : block48.length = 20 ∧
    block48.all bounded = true ∧ ∀ j : Fin 4, stats block48 j = (![(514, 3024, 18064, 87210, 553110), (587, 2702, 22009, 89116, 416890), (458, 2882, 19372, 85576, 535822), (452, 1974, 16018, 61358, 278978)]) j := by decide +kernel
lemma block49_info : block49.length = 20 ∧
    block49.all bounded = true ∧ ∀ j : Fin 4, stats block49 j = (![(308, 2128, 5402, 29341, 378372), (394, 1129, 10736, 27325, 105173), (499, 2765, 15351, 59993, 446541), (472, 1250, 20736, 43894, 108784)]) j := by decide +kernel

lemma block50_info : block50.length = 20 ∧
    block50.all bounded = true ∧ ∀ j : Fin 4, stats block50 j = (![(567, 1901, 24075, 74082, 287551), (949, 2828, 48995, 122977, 495724), (735, 2396, 36851, 108605, 395020), (535, 1317, 20009, 27333, 159335)]) j := by decide +kernel
lemma block51_info : block51.length = 20 ∧
    block51.all bounded = true ∧ ∀ j : Fin 4, stats block51 j = (![(503, 2345, 17683, 60413, 360363), (946, 1635, 46790, 77328, 221637), (810, 3127, 37702, 133114, 616397), (778, 949, 32600, 32156, 91703)]) j := by decide +kernel
lemma block52_info : block52.length = 20 ∧
    block52.all bounded = true ∧ ∀ j : Fin 4, stats block52 j = (![(497, 2204, 17601, 60424, 310652), (580, 1637, 23294, 57991, 183563), (683, 2797, 30529, 109404, 504619), (663, 1904, 30487, 85154, 276716)]) j := by decide +kernel
lemma block53_info : block53.length = 20 ∧
    block53.all bounded = true ∧ ∀ j : Fin 4, stats block53 j = (![(497, 2567, 20295, 79449, 422647), (547, 2251, 21441, 87449, 374693), (496, 2583, 22050, 82748, 418589), (632, 2441, 31138, 111116, 419491)]) j := by decide +kernel
lemma block54_info : block54.length = 20 ∧
    block54.all bounded = true ∧ ∀ j : Fin 4, stats block54 j = (![(420, 2565, 15880, 66236, 423917), (560, 2110, 24730, 89630, 359358), (426, 2566, 18858, 75027, 439370), (692, 2427, 33568, 111059, 404045)]) j := by decide +kernel
lemma block55_info : block55.length = 20 ∧
    block55.all bounded = true ∧ ∀ j : Fin 4, stats block55 j = (![(374, 2230, 13916, 57882, 353732), (596, 2015, 26664, 85442, 311203), (453, 2467, 17353, 72778, 411563), (730, 2374, 33860, 111176, 408572)]) j := by decide +kernel
lemma block56_info : block56.length = 20 ∧
    block56.all bounded = true ∧ ∀ j : Fin 4, stats block56 j = (![(493, 2329, 23979, 84847, 383559), (574, 1477, 22886, 58532, 177101), (473, 2109, 12535, 60336, 350905), (834, 2393, 41116, 125181, 430915)]) j := by decide +kernel
lemma block57_info : block57.length = 20 ∧
    block57.all bounded = true ∧ ∀ j : Fin 4, stats block57 j = (![(518, 2713, 22814, 93703, 441893), (618, 2359, 25770, 97352, 383577), (551, 2827, 18493, 97860, 537545), (490, 1729, 18630, 66848, 253005)]) j := by decide +kernel
lemma block58_info : block58.length = 20 ∧
    block58.all bounded = true ∧ ∀ j : Fin 4, stats block58 j = (![(429, 2362, 15967, 65877, 331512), (598, 2106, 23496, 84462, 333908), (699, 3342, 29153, 135960, 677832), (489, 1554, 20599, 64853, 222328)]) j := by decide +kernel
lemma block59_info : block59.length = 20 ∧
    block59.all bounded = true ∧ ∀ j : Fin 4, stats block59 j = (![(615, 2110, 30205, 99605, 329460), (520, 830, 19790, 34900, 63390), (840, 2750, 42600, 145810, 507090), (955, 2550, 48415, 139575, 438660)]) j := by decide +kernel

lemma block60_info : block60.length = 20 ∧
    block60.all bounded = true ∧ ∀ j : Fin 4, stats block60 j = (![(485, 1527, 19273, 52795, 179057), (639, 2651, 28741, 97137, 503823), (653, 2215, 26655, 84866, 290987), (759, 3165, 39541, 124199, 578133)]) j := by decide +kernel
lemma block61_info : block61.length = 20 ∧
    block61.all bounded = true ∧ ∀ j : Fin 4, stats block61 j = (![(365, 951, 11275, 15815, 48773), (771, 4238, 37451, 159473, 904252), (645, 2274, 25015, 79171, 287092), (591, 3613, 31085, 109305, 660113)]) j := by decide +kernel
lemma block62_info : block62.length = 20 ∧
    block62.all bounded = true ∧ ∀ j : Fin 4, stats block62 j = (![(566, 2500, 30158, 111904, 446692), (526, 1650, 18706, 51100, 179928), (234, 1164, 5406, 29942, 183720), (720, 2328, 32884, 108420, 407980)]) j := by decide +kernel
lemma block63_info : block63.length = 20 ∧
    block63.all bounded = true ∧ ∀ j : Fin 4, stats block63 j = (![(767, 3179, 42867, 160239, 625513), (486, 1747, 17106, 53721, 207717), (347, 1557, 13769, 63577, 313389), (699, 2509, 32199, 115415, 455821)]) j := by decide +kernel
lemma block64_info : block64.length = 20 ∧
    block64.all bounded = true ∧ ∀ j : Fin 4, stats block64 j = (![(798, 2880, 42872, 153764, 569490), (647, 2250, 28925, 93341, 336490), (554, 1914, 25674, 95616, 377450), (656, 2318, 29416, 105480, 419890)]) j := by decide +kernel
lemma block65_info : block65.length = 20 ∧
    block65.all bounded = true ∧ ∀ j : Fin 4, stats block65 j = (![(643, 2819, 29369, 107356, 495203), (679, 2557, 27909, 96195, 433087), (511, 2305, 20863, 78206, 418207), (337, 1185, 8721, 20320, 112383)]) j := by decide +kernel
lemma block66_info : block66.length = 20 ∧
    block66.all bounded = true ∧ ∀ j : Fin 4, stats block66 j = (![(609, 2608, 26155, 90789, 430046), (559, 2474, 20765, 87266, 401244), (701, 3020, 28629, 121894, 625220), (309, 1460, 6641, 25926, 143990)]) j := by decide +kernel
lemma block67_info : block67.length = 20 ∧
    block67.all bounded = true ∧ ∀ j : Fin 4, stats block67 j = (![(630, 1996, 29632, 91824, 299740), (562, 2493, 23666, 89171, 401085), (827, 2821, 41477, 147011, 544913), (454, 2152, 16412, 65779, 330512)]) j := by decide +kernel
lemma block68_info : block68.length = 20 ∧
    block68.all bounded = true ∧ ∀ j : Fin 4, stats block68 j = (![(595, 2180, 30475, 103635, 359580), (335, 915, 8565, 21410, 59945), (430, 1485, 16170, 65020, 272165), (935, 3220, 47595, 172235, 642060)]) j := by decide +kernel
lemma block69_info : block69.length = 20 ∧
    block69.all bounded = true ∧ ∀ j : Fin 4, stats block69 j = (![(491, 1980, 22467, 82035, 346500), (507, 1850, 20015, 66040, 259750), (495, 1978, 17699, 68389, 308218), (724, 2656, 33376, 121653, 492032)]) j := by decide +kernel

lemma block70_info : block70.length = 20 ∧
    block70.all bounded = true ∧ ∀ j : Fin 4, stats block70 j = (![(409, 1676, 17811, 68791, 282704), (724, 2728, 34744, 129804, 547616), (559, 2238, 25329, 95892, 377160), (482, 1786, 20864, 67839, 280500)]) j := by decide +kernel
lemma block71_info : block71.length = 20 ∧
    block71.all bounded = true ∧ ∀ j : Fin 4, stats block71 j = (![(432, 1792, 18538, 74389, 321370), (729, 2661, 34131, 123597, 527865), (543, 2191, 25459, 91979, 350281), (421, 1462, 18719, 52994, 219594)]) j := by decide +kernel
lemma block72_info : block72.length = 20 ∧
    block72.all bounded = true ∧ ∀ j : Fin 4, stats block72 j = (![(333, 1036, 11833, 39048, 139624), (640, 2713, 27462, 114183, 497181), (803, 2881, 38771, 138789, 511161), (390, 1802, 16628, 66006, 284724)]) j := by decide +kernel
lemma block73_info : block73.length = 20 ∧
    block73.all bounded = true ∧ ∀ j : Fin 4, stats block73 j = (![(489, 2132, 21055, 79348, 362306), (605, 1896, 26361, 81933, 279834), (695, 2834, 32289, 118583, 499734), (762, 2448, 37246, 124072, 441166)]) j := by decide +kernel
lemma block74_info : block74.length = 20 ∧
    block74.all bounded = true ∧ ∀ j : Fin 4, stats block74 j = (![(518, 1948, 23252, 73657, 335696), (643, 2019, 30161, 93435, 307899), (620, 2253, 30416, 93201, 385779), (747, 2426, 35445, 115935, 397496)]) j := by decide +kernel
lemma block75_info : block75.length = 20 ∧
    block75.all bounded = true ∧ ∀ j : Fin 4, stats block75 j = (![(498, 2048, 20602, 69057, 330150), (649, 2279, 30967, 99913, 364855), (621, 2477, 29313, 100723, 446723), (623, 2154, 29077, 95048, 353042)]) j := by decide +kernel
lemma block76_info : block76.length = 20 ∧
    block76.all bounded = true ∧ ∀ j : Fin 4, stats block76 j = (![(362, 2152, 13580, 46527, 325006), (617, 3306, 24803, 113535, 643054), (532, 2968, 21518, 83452, 509698), (629, 3186, 28201, 119625, 621322)]) j := by decide +kernel
lemma block77_info : block77.length = 20 ∧
    block77.all bounded = true ∧ ∀ j : Fin 4, stats block77 j = (![(585, 2455, 28023, 104269, 435105), (713, 3085, 34073, 116893, 531985), (511, 2241, 21053, 84624, 384197), (648, 2787, 24572, 98254, 528573)]) j := by decide +kernel
lemma block78_info : block78.length = 20 ∧
    block78.all bounded = true ∧ ∀ j : Fin 4, stats block78 j = (![(310, 1100, 11450, 30885, 91770), (330, 2375, 10130, 50765, 352005), (775, 3085, 31895, 129195, 548665), (225, 1970, 6145, 32310, 263710)]) j := by decide +kernel
lemma block79_info : block79.length = 20 ∧
    block79.all bounded = true ∧ ∀ j : Fin 4, stats block79 j = (![(253, 1033, 7123, 23280, 107207), (437, 2259, 19105, 69978, 351603), (848, 3409, 41934, 159158, 645287), (355, 1923, 13051, 51008, 286883)]) j := by decide +kernel

lemma block80_info : block80.length = 20 ∧
    block80.all bounded = true ∧ ∀ j : Fin 4, stats block80 j = (![(245, 1587, 5287, 29753, 214775), (387, 2031, 17917, 63611, 303205), (793, 3767, 41071, 164851, 742589), (517, 2389, 22379, 89332, 417531)]) j := by decide +kernel
lemma block81_info : block81.length = 20 ∧
    block81.all bounded = true ∧ ∀ j : Fin 4, stats block81 j = (![(431, 1483, 21371, 54700, 184995), (713, 2459, 33387, 114957, 423195), (953, 3423, 49067, 172171, 684671), (431, 1421, 16293, 50457, 171839)]) j := by decide +kernel
lemma block82_info : block82.length = 20 ∧
    block82.all bounded = true ∧ ∀ j : Fin 4, stats block82 j = (![(460, 1208, 18052, 38200, 123864), (1040, 3684, 59256, 201728, 712276), (796, 2444, 38652, 117524, 441940), (392, 1328, 10928, 36068, 138120)]) j := by decide +kernel
lemma block83_info : block83.length = 20 ∧
    block83.all bounded = true ∧ ∀ j : Fin 4, stats block83 j = (![(714, 1365, 39032, 73833, 156541), (619, 1900, 31545, 95519, 305664), (844, 1798, 39690, 95882, 328560), (641, 2251, 25519, 94768, 372265)]) j := by decide +kernel
lemma block84_info : block84.length = 20 ∧
    block84.all bounded = true ∧ ∀ j : Fin 4, stats block84 j = (![(730, 1343, 40434, 77911, 165757), (506, 1319, 22678, 57648, 158223), (869, 1781, 41953, 100873, 333771), (672, 2237, 26296, 95077, 374329)]) j := by decide +kernel
lemma block85_info : block85.length = 20 ∧
    block85.all bounded = true ∧ ∀ j : Fin 4, stats block85 j = (![(401, 1800, 14563, 51928, 269146), (370, 1770, 13632, 45017, 244954), (702, 3010, 35826, 130814, 575498), (617, 2650, 24899, 94249, 443002)]) j := by decide +kernel
lemma block86_info : block86.length = 20 ∧
    block86.all bounded = true ∧ ∀ j : Fin 4, stats block86 j = (![(457, 1756, 21233, 62991, 258578), (436, 2063, 15342, 60663, 325847), (675, 2663, 32073, 114801, 503683), (458, 2136, 13848, 55529, 299962)]) j := by decide +kernel
lemma block87_info : block87.length = 20 ∧
    block87.all bounded = true ∧ ∀ j : Fin 4, stats block87 j = (![(479, 2101, 22753, 88660, 411775), (428, 1893, 17440, 72644, 347735), (632, 2729, 27978, 108868, 489823), (304, 1363, 6462, 25159, 145527)]) j := by decide +kernel
lemma block88_info : block88.length = 20 ∧
    block88.all bounded = true ∧ ∀ j : Fin 4, stats block88 j = (![(490, 1808, 21144, 78776, 323890), (539, 1849, 24649, 86750, 325525), (707, 2595, 33547, 117448, 437021), (341, 1110, 9681, 30903, 119274)]) j := by decide +kernel
lemma block89_info : block89.length = 20 ∧
    block89.all bounded = true ∧ ∀ j : Fin 4, stats block89 j = (![(489, 1516, 18371, 58856, 227502), (732, 2603, 36582, 130618, 484963), (798, 2663, 39732, 131138, 472923), (336, 1166, 9682, 32240, 121202)]) j := by decide +kernel

lemma block90_info : block90.length = 20 ∧
    block90.all bounded = true ∧ ∀ j : Fin 4, stats block90 j = (![(564, 1744, 21684, 70800, 279624), (872, 2672, 47736, 145256, 511896), (624, 1856, 29720, 82572, 281512), (428, 1072, 15900, 38184, 129768)]) j := by decide +kernel
lemma block91_info : block91.length = 20 ∧
    block91.all bounded = true ∧ ∀ j : Fin 4, stats block91 j = (![(372, 1893, 14862, 63257, 324083), (736, 2749, 38072, 135832, 523697), (662, 2977, 33024, 132185, 578709), (389, 1339, 15215, 46255, 179831)]) j := by decide +kernel
lemma block92_info : block92.length = 20 ∧
    block92.all bounded = true ∧ ∀ j : Fin 4, stats block92 j = (![(454, 2504, 17850, 78992, 446428), (785, 3387, 38799, 150785, 711267), (526, 2841, 22190, 98485, 532527), (386, 1712, 11130, 35731, 235228)]) j := by decide +kernel
lemma block93_info : block93.length = 20 ∧
    block93.all bounded = true ∧ ∀ j : Fin 4, stats block93 j = (![(286, 978, 8862, 25203, 109624), (537, 2019, 24197, 89551, 385561), (800, 2931, 40482, 147058, 577097), (440, 1672, 14458, 47320, 207148)]) j := by decide +kernel
lemma block94_info : block94.length = 20 ∧
    block94.all bounded = true ∧ ∀ j : Fin 4, stats block94 j = (![(326, 831, 11670, 24739, 104183), (664, 2083, 34916, 114807, 403127), (855, 2765, 47221, 143949, 502659), (550, 1735, 20368, 61152, 200591)]) j := by decide +kernel
lemma block95_info : block95.length = 20 ∧
    block95.all bounded = true ∧ ∀ j : Fin 4, stats block95 j = (![(323, 1040, 10443, 33949, 149862), (498, 1540, 23876, 76165, 297308), (901, 3174, 44805, 154896, 575104), (544, 1758, 24744, 73721, 263946)]) j := by decide +kernel
lemma block96_info : block96.length = 20 ∧
    block96.all bounded = true ∧ ∀ j : Fin 4, stats block96 j = (![(297, 1107, 9509, 30683, 140383), (562, 1656, 25802, 77640, 283992), (906, 3332, 45306, 164800, 652204), (462, 1289, 18946, 51152, 171811)]) j := by decide +kernel
lemma block97_info : block97.length = 7 ∧
    block97.all bounded = true ∧ ∀ j : Fin 4, stats block97 j = (![(129, 685, 2533, 12139, 70031), (248, 1005, 11558, 45518, 183139), (335, 1477, 16847, 71137, 314147), (96, 389, 1902, 6600, 24383)]) j := by decide +kernel

lemma tail98_info : tail98.length = 0 ∧ tail98.all bounded = true ∧
    ∀ j : Fin 4, stats tail98 j = (0, 0, 0, 0, 0) := by decide +kernel
section
attribute [local irreducible] stats

lemma tail97_info : tail97.length = 7 ∧ tail97.all bounded = true ∧
    ∀ j : Fin 4, stats tail97 j = (![(129, 685, 2533, 12139, 70031), (248, 1005, 11558, 45518, 183139), (335, 1477, 16847, 71137, 314147), (96, 389, 1902, 6600, 24383)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block97_info
  obtain ⟨hlt, hbt, hst⟩ := tail98_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail97, List.length_append, hlb, hlt]
  · simp only [tail97, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail97, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail96_info : tail96.length = 27 ∧ tail96.all bounded = true ∧
    ∀ j : Fin 4, stats tail96 j = (![(426, 1792, 12042, 42822, 210414), (810, 2661, 37360, 123158, 467131), (1241, 4809, 62153, 235937, 966351), (558, 1678, 20848, 57752, 196194)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block96_info
  obtain ⟨hlt, hbt, hst⟩ := tail97_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail96, List.length_append, hlb, hlt]
  · simp only [tail96, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail96, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail95_info : tail95.length = 47 ∧ tail95.all bounded = true ∧
    ∀ j : Fin 4, stats tail95 j = (![(749, 2832, 22485, 76771, 360276), (1308, 4201, 61236, 199323, 764439), (2142, 7983, 106958, 390833, 1541455), (1102, 3436, 45592, 131473, 460140)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block95_info
  obtain ⟨hlt, hbt, hst⟩ := tail96_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail95, List.length_append, hlb, hlt]
  · simp only [tail95, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail95, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail94_info : tail94.length = 67 ∧ tail94.all bounded = true ∧
    ∀ j : Fin 4, stats tail94 j = (![(1075, 3663, 34155, 101510, 464459), (1972, 6284, 96152, 314130, 1167566), (2997, 10748, 154179, 534782, 2044114), (1652, 5171, 65960, 192625, 660731)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block94_info
  obtain ⟨hlt, hbt, hst⟩ := tail95_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail94, List.length_append, hlb, hlt]
  · simp only [tail94, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail94, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail93_info : tail93.length = 87 ∧ tail93.all bounded = true ∧
    ∀ j : Fin 4, stats tail93 j = (![(1361, 4641, 43017, 126713, 574083), (2509, 8303, 120349, 403681, 1553127), (3797, 13679, 194661, 681840, 2621211), (2092, 6843, 80418, 239945, 867879)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block93_info
  obtain ⟨hlt, hbt, hst⟩ := tail94_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail93, List.length_append, hlb, hlt]
  · simp only [tail93, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail93, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail92_info : tail92.length = 107 ∧ tail92.all bounded = true ∧
    ∀ j : Fin 4, stats tail92 j = (![(1815, 7145, 60867, 205705, 1020511), (3294, 11690, 159148, 554466, 2264394), (4323, 16520, 216851, 780325, 3153738), (2478, 8555, 91548, 275676, 1103107)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block92_info
  obtain ⟨hlt, hbt, hst⟩ := tail93_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail92, List.length_append, hlb, hlt]
  · simp only [tail92, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail92, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail91_info : tail91.length = 127 ∧ tail91.all bounded = true ∧
    ∀ j : Fin 4, stats tail91 j = (![(2187, 9038, 75729, 268962, 1344594), (4030, 14439, 197220, 690298, 2788091), (4985, 19497, 249875, 912510, 3732447), (2867, 9894, 106763, 321931, 1282938)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block91_info
  obtain ⟨hlt, hbt, hst⟩ := tail92_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail91, List.length_append, hlb, hlt]
  · simp only [tail91, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail91, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail90_info : tail90.length = 147 ∧ tail90.all bounded = true ∧
    ∀ j : Fin 4, stats tail90 j = (![(2751, 10782, 97413, 339762, 1624218), (4902, 17111, 244956, 835554, 3299987), (5609, 21353, 279595, 995082, 4013959), (3295, 10966, 122663, 360115, 1412706)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block90_info
  obtain ⟨hlt, hbt, hst⟩ := tail91_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail90, List.length_append, hlb, hlt]
  · simp only [tail90, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail90, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail89_info : tail89.length = 167 ∧ tail89.all bounded = true ∧
    ∀ j : Fin 4, stats tail89 j = (![(3240, 12298, 115784, 398618, 1851720), (5634, 19714, 281538, 966172, 3784950), (6407, 24016, 319327, 1126220, 4486882), (3631, 12132, 132345, 392355, 1533908)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block89_info
  obtain ⟨hlt, hbt, hst⟩ := tail90_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail89, List.length_append, hlb, hlt]
  · simp only [tail89, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail89, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail88_info : tail88.length = 187 ∧ tail88.all bounded = true ∧
    ∀ j : Fin 4, stats tail88 j = (![(3730, 14106, 136928, 477394, 2175610), (6173, 21563, 306187, 1052922, 4110475), (7114, 26611, 352874, 1243668, 4923903), (3972, 13242, 142026, 423258, 1653182)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block88_info
  obtain ⟨hlt, hbt, hst⟩ := tail89_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail88, List.length_append, hlb, hlt]
  · simp only [tail88, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail88, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail87_info : tail87.length = 207 ∧ tail87.all bounded = true ∧
    ∀ j : Fin 4, stats tail87 j = (![(4209, 16207, 159681, 566054, 2587385), (6601, 23456, 323627, 1125566, 4458210), (7746, 29340, 380852, 1352536, 5413726), (4276, 14605, 148488, 448417, 1798709)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block87_info
  obtain ⟨hlt, hbt, hst⟩ := tail88_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail87, List.length_append, hlb, hlt]
  · simp only [tail87, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail87, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail86_info : tail86.length = 227 ∧ tail86.all bounded = true ∧
    ∀ j : Fin 4, stats tail86 j = (![(4666, 17963, 180914, 629045, 2845963), (7037, 25519, 338969, 1186229, 4784057), (8421, 32003, 412925, 1467337, 5917409), (4734, 16741, 162336, 503946, 2098671)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block86_info
  obtain ⟨hlt, hbt, hst⟩ := tail87_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail86, List.length_append, hlb, hlt]
  · simp only [tail86, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail86, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail85_info : tail85.length = 247 ∧ tail85.all bounded = true ∧
    ∀ j : Fin 4, stats tail85 j = (![(5067, 19763, 195477, 680973, 3115109), (7407, 27289, 352601, 1231246, 5029011), (9123, 35013, 448751, 1598151, 6492907), (5351, 19391, 187235, 598195, 2541673)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block85_info
  obtain ⟨hlt, hbt, hst⟩ := tail86_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail85, List.length_append, hlb, hlt]
  · simp only [tail85, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail85, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail84_info : tail84.length = 267 ∧ tail84.all bounded = true ∧
    ∀ j : Fin 4, stats tail84 j = (![(5797, 21106, 235911, 758884, 3280866), (7913, 28608, 375279, 1288894, 5187234), (9992, 36794, 490704, 1699024, 6826678), (6023, 21628, 213531, 693272, 2916002)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block84_info
  obtain ⟨hlt, hbt, hst⟩ := tail85_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail84, List.length_append, hlb, hlt]
  · simp only [tail84, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail84, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail83_info : tail83.length = 287 ∧ tail83.all bounded = true ∧
    ∀ j : Fin 4, stats tail83 j = (![(6511, 22471, 274943, 832717, 3437407), (8532, 30508, 406824, 1384413, 5492898), (10836, 38592, 530394, 1794906, 7155238), (6664, 23879, 239050, 788040, 3288267)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block83_info
  obtain ⟨hlt, hbt, hst⟩ := tail84_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail83, List.length_append, hlb, hlt]
  · simp only [tail83, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail83, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail82_info : tail82.length = 307 ∧ tail82.all bounded = true ∧
    ∀ j : Fin 4, stats tail82 j = (![(6971, 23679, 292995, 870917, 3561271), (9572, 34192, 466080, 1586141, 6205174), (11632, 41036, 569046, 1912430, 7597178), (7056, 25207, 249978, 824108, 3426387)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block82_info
  obtain ⟨hlt, hbt, hst⟩ := tail83_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail82, List.length_append, hlb, hlt]
  · simp only [tail82, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail82, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail81_info : tail81.length = 327 ∧ tail81.all bounded = true ∧
    ∀ j : Fin 4, stats tail81 j = (![(7402, 25162, 314366, 925617, 3746266), (10285, 36651, 499467, 1701098, 6628369), (12585, 44459, 618113, 2084601, 8281849), (7487, 26628, 266271, 874565, 3598226)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block81_info
  obtain ⟨hlt, hbt, hst⟩ := tail82_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail81, List.length_append, hlb, hlt]
  · simp only [tail81, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail81, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail80_info : tail80.length = 347 ∧ tail80.all bounded = true ∧
    ∀ j : Fin 4, stats tail80 j = (![(7647, 26749, 319653, 955370, 3961041), (10672, 38682, 517384, 1764709, 6931574), (13378, 48226, 659184, 2249452, 9024438), (8004, 29017, 288650, 963897, 4015757)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block80_info
  obtain ⟨hlt, hbt, hst⟩ := tail81_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail80, List.length_append, hlb, hlt]
  · simp only [tail80, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail80, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail79_info : tail79.length = 367 ∧ tail79.all bounded = true ∧
    ∀ j : Fin 4, stats tail79 j = (![(7900, 27782, 326776, 978650, 4068248), (11109, 40941, 536489, 1834687, 7283177), (14226, 51635, 701118, 2408610, 9669725), (8359, 30940, 301701, 1014905, 4302640)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block79_info
  obtain ⟨hlt, hbt, hst⟩ := tail80_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail79, List.length_append, hlb, hlt]
  · simp only [tail79, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail79, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail78_info : tail78.length = 387 ∧ tail78.all bounded = true ∧
    ∀ j : Fin 4, stats tail78 j = (![(8210, 28882, 338226, 1009535, 4160018), (11439, 43316, 546619, 1885452, 7635182), (15001, 54720, 733013, 2537805, 10218390), (8584, 32910, 307846, 1047215, 4566350)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block78_info
  obtain ⟨hlt, hbt, hst⟩ := tail79_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail78, List.length_append, hlb, hlt]
  · simp only [tail78, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail78, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail77_info : tail77.length = 407 ∧ tail77.all bounded = true ∧
    ∀ j : Fin 4, stats tail77 j = (![(8795, 31337, 366249, 1113804, 4595123), (12152, 46401, 580692, 2002345, 8167167), (15512, 56961, 754066, 2622429, 10602587), (9232, 35697, 332418, 1145469, 5094923)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block77_info
  obtain ⟨hlt, hbt, hst⟩ := tail78_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail77, List.length_append, hlb, hlt]
  · simp only [tail77, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail77, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail76_info : tail76.length = 427 ∧ tail76.all bounded = true ∧
    ∀ j : Fin 4, stats tail76 j = (![(9157, 33489, 379829, 1160331, 4920129), (12769, 49707, 605495, 2115880, 8810221), (16044, 59929, 775584, 2705881, 11112285), (9861, 38883, 360619, 1265094, 5716245)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block76_info
  obtain ⟨hlt, hbt, hst⟩ := tail77_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail76, List.length_append, hlb, hlt]
  · simp only [tail76, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail76, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail75_info : tail75.length = 447 ∧ tail75.all bounded = true ∧
    ∀ j : Fin 4, stats tail75 j = (![(9655, 35537, 400431, 1229388, 5250279), (13418, 51986, 636462, 2215793, 9175076), (16665, 62406, 804897, 2806604, 11559008), (10484, 41037, 389696, 1360142, 6069287)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block75_info
  obtain ⟨hlt, hbt, hst⟩ := tail76_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail75, List.length_append, hlb, hlt]
  · simp only [tail75, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail75, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail74_info : tail74.length = 467 ∧ tail74.all bounded = true ∧
    ∀ j : Fin 4, stats tail74 j = (![(10173, 37485, 423683, 1303045, 5585975), (14061, 54005, 666623, 2309228, 9482975), (17285, 64659, 835313, 2899805, 11944787), (11231, 43463, 425141, 1476077, 6466783)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block74_info
  obtain ⟨hlt, hbt, hst⟩ := tail75_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail74, List.length_append, hlb, hlt]
  · simp only [tail74, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail74, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail73_info : tail73.length = 487 ∧ tail73.all bounded = true ∧
    ∀ j : Fin 4, stats tail73 j = (![(10662, 39617, 444738, 1382393, 5948281), (14666, 55901, 692984, 2391161, 9762809), (17980, 67493, 867602, 3018388, 12444521), (11993, 45911, 462387, 1600149, 6907949)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block73_info
  obtain ⟨hlt, hbt, hst⟩ := tail74_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail73, List.length_append, hlb, hlt]
  · simp only [tail73, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail73, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail72_info : tail72.length = 507 ∧ tail72.all bounded = true ∧
    ∀ j : Fin 4, stats tail72 j = (![(10995, 40653, 456571, 1421441, 6087905), (15306, 58614, 720446, 2505344, 10259990), (18783, 70374, 906373, 3157177, 12955682), (12383, 47713, 479015, 1666155, 7192673)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block72_info
  obtain ⟨hlt, hbt, hst⟩ := tail73_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail72, List.length_append, hlb, hlt]
  · simp only [tail72, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail72, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail71_info : tail71.length = 527 ∧ tail71.all bounded = true ∧
    ∀ j : Fin 4, stats tail71 j = (![(11427, 42445, 475109, 1495830, 6409275), (16035, 61275, 754577, 2628941, 10787855), (19326, 72565, 931832, 3249156, 13305963), (12804, 49175, 497734, 1719149, 7412267)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block71_info
  obtain ⟨hlt, hbt, hst⟩ := tail72_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail71, List.length_append, hlb, hlt]
  · simp only [tail71, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail71, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail70_info : tail70.length = 547 ∧ tail70.all bounded = true ∧
    ∀ j : Fin 4, stats tail70 j = (![(11836, 44121, 492920, 1564621, 6691979), (16759, 64003, 789321, 2758745, 11335471), (19885, 74803, 957161, 3345048, 13683123), (13286, 50961, 518598, 1786988, 7692767)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block70_info
  obtain ⟨hlt, hbt, hst⟩ := tail71_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail70, List.length_append, hlb, hlt]
  · simp only [tail70, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail70, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail69_info : tail69.length = 567 ∧ tail69.all bounded = true ∧
    ∀ j : Fin 4, stats tail69 j = (![(12327, 46101, 515387, 1646656, 7038479), (17266, 65853, 809336, 2824785, 11595221), (20380, 76781, 974860, 3413437, 13991341), (14010, 53617, 551974, 1908641, 8184799)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block69_info
  obtain ⟨hlt, hbt, hst⟩ := tail70_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail69, List.length_append, hlb, hlt]
  · simp only [tail69, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail69, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail68_info : tail68.length = 587 ∧ tail68.all bounded = true ∧
    ∀ j : Fin 4, stats tail68 j = (![(12922, 48281, 545862, 1750291, 7398059), (17601, 66768, 817901, 2846195, 11655166), (20810, 78266, 991030, 3478457, 14263506), (14945, 56837, 599569, 2080876, 8826859)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block68_info
  obtain ⟨hlt, hbt, hst⟩ := tail69_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail68, List.length_append, hlb, hlt]
  · simp only [tail68, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail68, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail67_info : tail67.length = 607 ∧ tail67.all bounded = true ∧
    ∀ j : Fin 4, stats tail67 j = (![(13552, 50277, 575494, 1842115, 7697799), (18163, 69261, 841567, 2935366, 12056251), (21637, 81087, 1032507, 3625468, 14808419), (15399, 58989, 615981, 2146655, 9157371)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block67_info
  obtain ⟨hlt, hbt, hst⟩ := tail68_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail67, List.length_append, hlb, hlt]
  · simp only [tail67, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail67, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail66_info : tail66.length = 627 ∧ tail66.all bounded = true ∧
    ∀ j : Fin 4, stats tail66 j = (![(14161, 52885, 601649, 1932904, 8127845), (18722, 71735, 862332, 3022632, 12457495), (22338, 84107, 1061136, 3747362, 15433639), (15708, 60449, 622622, 2172581, 9301361)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block66_info
  obtain ⟨hlt, hbt, hst⟩ := tail67_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail66, List.length_append, hlb, hlt]
  · simp only [tail66, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail66, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail65_info : tail65.length = 647 ∧ tail65.all bounded = true ∧
    ∀ j : Fin 4, stats tail65 j = (![(14804, 55704, 631018, 2040260, 8623048), (19401, 74292, 890241, 3118827, 12890582), (22849, 86412, 1081999, 3825568, 15851846), (16045, 61634, 631343, 2192901, 9413744)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block65_info
  obtain ⟨hlt, hbt, hst⟩ := tail66_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail65, List.length_append, hlb, hlt]
  · simp only [tail65, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail65, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail64_info : tail64.length = 667 ∧ tail64.all bounded = true ∧
    ∀ j : Fin 4, stats tail64 j = (![(15602, 58584, 673890, 2194024, 9192538), (20048, 76542, 919166, 3212168, 13227072), (23403, 88326, 1107673, 3921184, 16229296), (16701, 63952, 660759, 2298381, 9833634)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block64_info
  obtain ⟨hlt, hbt, hst⟩ := tail65_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail64, List.length_append, hlb, hlt]
  · simp only [tail64, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail64, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail63_info : tail63.length = 687 ∧ tail63.all bounded = true ∧
    ∀ j : Fin 4, stats tail63 j = (![(16369, 61763, 716757, 2354263, 9818051), (20534, 78289, 936272, 3265889, 13434789), (23750, 89883, 1121442, 3984761, 16542685), (17400, 66461, 692958, 2413796, 10289455)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block63_info
  obtain ⟨hlt, hbt, hst⟩ := tail64_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail63, List.length_append, hlb, hlt]
  · simp only [tail63, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail63, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail62_info : tail62.length = 707 ∧ tail62.all bounded = true ∧
    ∀ j : Fin 4, stats tail62 j = (![(16935, 64263, 746915, 2466167, 10264743), (21060, 79939, 954978, 3316989, 13614717), (23984, 91047, 1126848, 4014703, 16726405), (18120, 68789, 725842, 2522216, 10697435)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block62_info
  obtain ⟨hlt, hbt, hst⟩ := tail63_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail62, List.length_append, hlb, hlt]
  · simp only [tail62, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail62, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail61_info : tail61.length = 727 ∧ tail61.all bounded = true ∧
    ∀ j : Fin 4, stats tail61 j = (![(17300, 65214, 758190, 2481982, 10313516), (21831, 84177, 992429, 3476462, 14518969), (24629, 93321, 1151863, 4093874, 17013497), (18711, 72402, 756927, 2631521, 11357548)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block61_info
  obtain ⟨hlt, hbt, hst⟩ := tail62_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail61, List.length_append, hlb, hlt]
  · simp only [tail61, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail61, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail60_info : tail60.length = 747 ∧ tail60.all bounded = true ∧
    ∀ j : Fin 4, stats tail60 j = (![(17785, 66741, 777463, 2534777, 10492573), (22470, 86828, 1021170, 3573599, 15022792), (25282, 95536, 1178518, 4178740, 17304484), (19470, 75567, 796468, 2755720, 11935681)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block60_info
  obtain ⟨hlt, hbt, hst⟩ := tail61_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail60, List.length_append, hlb, hlt]
  · simp only [tail60, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail60, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail59_info : tail59.length = 767 ∧ tail59.all bounded = true ∧
    ∀ j : Fin 4, stats tail59 j = (![(18400, 68851, 807668, 2634382, 10822033), (22990, 87658, 1040960, 3608499, 15086182), (26122, 98286, 1221118, 4324550, 17811574), (20425, 78117, 844883, 2895295, 12374341)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block59_info
  obtain ⟨hlt, hbt, hst⟩ := tail60_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail59, List.length_append, hlb, hlt]
  · simp only [tail59, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail59, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail58_info : tail58.length = 787 ∧ tail58.all bounded = true ∧
    ∀ j : Fin 4, stats tail58 j = (![(18829, 71213, 823635, 2700259, 11153545), (23588, 89764, 1064456, 3692961, 15420090), (26821, 101628, 1250271, 4460510, 18489406), (20914, 79671, 865482, 2960148, 12596669)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block58_info
  obtain ⟨hlt, hbt, hst⟩ := tail59_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail58, List.length_append, hlb, hlt]
  · simp only [tail58, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail58, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail57_info : tail57.length = 807 ∧ tail57.all bounded = true ∧
    ∀ j : Fin 4, stats tail57 j = (![(19347, 73926, 846449, 2793962, 11595438), (24206, 92123, 1090226, 3790313, 15803667), (27372, 104455, 1268764, 4558370, 19026951), (21404, 81400, 884112, 3026996, 12849674)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block57_info
  obtain ⟨hlt, hbt, hst⟩ := tail58_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail57, List.length_append, hlb, hlt]
  · simp only [tail57, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail57, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail56_info : tail56.length = 827 ∧ tail56.all bounded = true ∧
    ∀ j : Fin 4, stats tail56 j = (![(19840, 76255, 870428, 2878809, 11978997), (24780, 93600, 1113112, 3848845, 15980768), (27845, 106564, 1281299, 4618706, 19377856), (22238, 83793, 925228, 3152177, 13280589)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block56_info
  obtain ⟨hlt, hbt, hst⟩ := tail57_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail56, List.length_append, hlb, hlt]
  · simp only [tail56, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail56, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail55_info : tail55.length = 847 ∧ tail55.all bounded = true ∧
    ∀ j : Fin 4, stats tail55 j = (![(20214, 78485, 884344, 2936691, 12332729), (25376, 95615, 1139776, 3934287, 16291971), (28298, 109031, 1298652, 4691484, 19789419), (22968, 86167, 959088, 3263353, 13689161)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block55_info
  obtain ⟨hlt, hbt, hst⟩ := tail56_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail55, List.length_append, hlb, hlt]
  · simp only [tail55, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail55, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail54_info : tail54.length = 867 ∧ tail54.all bounded = true ∧
    ∀ j : Fin 4, stats tail54 j = (![(20634, 81050, 900224, 3002927, 12756646), (25936, 97725, 1164506, 4023917, 16651329), (28724, 111597, 1317510, 4766511, 20228789), (23660, 88594, 992656, 3374412, 14093206)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block54_info
  obtain ⟨hlt, hbt, hst⟩ := tail55_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail54, List.length_append, hlb, hlt]
  · simp only [tail54, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail54, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail53_info : tail53.length = 887 ∧ tail53.all bounded = true ∧
    ∀ j : Fin 4, stats tail53 j = (![(21131, 83617, 920519, 3082376, 13179293), (26483, 99976, 1185947, 4111366, 17026022), (29220, 114180, 1339560, 4849259, 20647378), (24292, 91035, 1023794, 3485528, 14512697)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block53_info
  obtain ⟨hlt, hbt, hst⟩ := tail54_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail53, List.length_append, hlb, hlt]
  · simp only [tail53, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail53, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail52_info : tail52.length = 907 ∧ tail52.all bounded = true ∧
    ∀ j : Fin 4, stats tail52 j = (![(21628, 85821, 938120, 3142800, 13489945), (27063, 101613, 1209241, 4169357, 17209585), (29903, 116977, 1370089, 4958663, 21151997), (24955, 92939, 1054281, 3570682, 14789413)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block52_info
  obtain ⟨hlt, hbt, hst⟩ := tail53_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail52, List.length_append, hlb, hlt]
  · simp only [tail52, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail52, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail51_info : tail51.length = 927 ∧ tail51.all bounded = true ∧
    ∀ j : Fin 4, stats tail51 j = (![(22131, 88166, 955803, 3203213, 13850308), (28009, 103248, 1256031, 4246685, 17431222), (30713, 120104, 1407791, 5091777, 21768394), (25733, 93888, 1086881, 3602838, 14881116)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block51_info
  obtain ⟨hlt, hbt, hst⟩ := tail52_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail51, List.length_append, hlb, hlt]
  · simp only [tail51, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail51, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail50_info : tail50.length = 947 ∧ tail50.all bounded = true ∧
    ∀ j : Fin 4, stats tail50 j = (![(22698, 90067, 979878, 3277295, 14137859), (28958, 106076, 1305026, 4369662, 17926946), (31448, 122500, 1444642, 5200382, 22163414), (26268, 95205, 1106890, 3630171, 15040451)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block50_info
  obtain ⟨hlt, hbt, hst⟩ := tail51_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail50, List.length_append, hlb, hlt]
  · simp only [tail50, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail50, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail49_info : tail49.length = 967 ∧ tail49.all bounded = true ∧
    ∀ j : Fin 4, stats tail49 j = (![(23006, 92195, 985280, 3306636, 14516231), (29352, 107205, 1315762, 4396987, 18032119), (31947, 125265, 1459993, 5260375, 22609955), (26740, 96455, 1127626, 3674065, 15149235)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block49_info
  obtain ⟨hlt, hbt, hst⟩ := tail50_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail49, List.length_append, hlb, hlt]
  · simp only [tail49, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail49, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail48_info : tail48.length = 987 ∧ tail48.all bounded = true ∧
    ∀ j : Fin 4, stats tail48 j = (![(23520, 95219, 1003344, 3393846, 15069341), (29939, 109907, 1337771, 4486103, 18449009), (32405, 128147, 1479365, 5345951, 23145777), (27192, 98429, 1143644, 3735423, 15428213)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block48_info
  obtain ⟨hlt, hbt, hst⟩ := tail49_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail48, List.length_append, hlb, hlt]
  · simp only [tail48, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail48, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail47_info : tail47.length = 1007 ∧ tail47.all bounded = true ∧
    ∀ j : Fin 4, stats tail47 j = (![(24084, 97020, 1023904, 3460848, 15314058), (30722, 112475, 1375260, 4599533, 18839157), (33187, 130705, 1518309, 5468216, 23548293), (27557, 99480, 1154159, 3761364, 15540282)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block47_info
  obtain ⟨hlt, hbt, hst⟩ := tail48_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail47, List.length_append, hlb, hlt]
  · simp only [tail47, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail47, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail46_info : tail46.length = 1027 ∧ tail46.all bounded = true ∧
    ∀ j : Fin 4, stats tail46 j = (![(24646, 98065, 1045128, 3507809, 15451765), (31336, 115095, 1401580, 4698859, 19369295), (33907, 132425, 1548423, 5540300, 23732679), (28063, 101895, 1176635, 3833039, 15930621)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block46_info
  obtain ⟨hlt, hbt, hst⟩ := tail47_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail46, List.length_append, hlb, hlt]
  · simp only [tail46, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail46, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail45_info : tail45.length = 1047 ∧ tail45.all bounded = true ∧
    ∀ j : Fin 4, stats tail45 j = (![(25277, 100346, 1074911, 3615314, 15854826), (31930, 117068, 1430384, 4792521, 19717014), (34465, 134376, 1576767, 5638158, 24084466), (28756, 104272, 1208842, 3947486, 16385874)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block45_info
  obtain ⟨hlt, hbt, hst⟩ := tail46_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail45, List.length_append, hlb, hlt]
  · simp only [tail45, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail45, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail44_info : tail44.length = 1067 ∧ tail44.all bounded = true ∧
    ∀ j : Fin 4, stats tail44 j = (![(25864, 102584, 1101388, 3709562, 16213134), (32531, 119647, 1457431, 4902596, 20238011), (34947, 136271, 1597819, 5714712, 24391055), (29451, 107202, 1240897, 4076013, 16970230)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block44_info
  obtain ⟨hlt, hbt, hst⟩ := tail45_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail44, List.length_append, hlb, hlt]
  · simp only [tail44, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail44, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail43_info : tail43.length = 1087 ∧ tail43.all bounded = true ∧
    ∀ j : Fin 4, stats tail43 j = (![(26365, 104716, 1121547, 3772699, 16560032), (33049, 121543, 1479639, 4968399, 20560413), (35568, 138841, 1624024, 5802706, 24825653), (30173, 109832, 1275305, 4180077, 17420272)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block43_info
  obtain ⟨hlt, hbt, hst⟩ := tail44_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail43, List.length_append, hlb, hlt]
  · simp only [tail43, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail43, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail42_info : tail42.length = 1107 ∧ tail42.all bounded = true ∧
    ∀ j : Fin 4, stats tail42 j = (![(26952, 106941, 1147922, 3854206, 16939863), (33417, 122478, 1492395, 4996477, 20640362), (36292, 141498, 1658282, 5910358, 25304618), (30965, 112391, 1313065, 4306945, 17874447)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block42_info
  obtain ⟨hlt, hbt, hst⟩ := tail43_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail42, List.length_append, hlb, hlt]
  · simp only [tail42, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail42, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail41_info : tail41.length = 1127 ∧ tail41.all bounded = true ∧
    ∀ j : Fin 4, stats tail41 j = (![(27511, 109145, 1165981, 3912026, 17271923), (33885, 124600, 1510253, 5066139, 20977602), (36987, 144284, 1690143, 6013733, 25779426), (31649, 115313, 1345515, 4429015, 18404559)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block41_info
  obtain ⟨hlt, hbt, hst⟩ := tail42_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail41, List.length_append, hlb, hlt]
  · simp only [tail41, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail41, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail40_info : tail40.length = 1147 ∧ tail40.all bounded = true ∧
    ∀ j : Fin 4, stats tail40 j = (![(28073, 111242, 1185853, 3974208, 17573476), (34323, 127181, 1525493, 5139485, 21403549), (37762, 147367, 1726400, 6144382, 26344325), (32221, 118394, 1373005, 4543572, 18988140)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block40_info
  obtain ⟨hlt, hbt, hst⟩ := tail41_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail40, List.length_append, hlb, hlt]
  · simp only [tail40, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail40, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail39_info : tail39.length = 1167 ∧ tail39.all bounded = true ∧
    ∀ j : Fin 4, stats tail39 j = (![(28606, 113581, 1212458, 4066537, 17989133), (35329, 130333, 1578345, 5301851, 21984567), (38337, 149731, 1753929, 6241417, 26744279), (32840, 120027, 1400816, 4620998, 19322961)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block39_info
  obtain ⟨hlt, hbt, hst⟩ := tail40_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail39, List.length_append, hlb, hlt]
  · simp only [tail39, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail39, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail38_info : tail38.length = 1187 ∧ tail38.all bounded = true ∧
    ∀ j : Fin 4, stats tail38 j = (![(29071, 115916, 1230847, 4139836, 18372404), (35992, 132718, 1607616, 5393880, 22337526), (38794, 151998, 1774472, 6317964, 27110062), (33537, 122436, 1433065, 4731046, 19780708)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block38_info
  obtain ⟨hlt, hbt, hst⟩ := tail39_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail38, List.length_append, hlb, hlt]
  · simp only [tail38, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail38, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail37_info : tail37.length = 1207 ∧ tail37.all bounded = true ∧
    ∀ j : Fin 4, stats tail37 j = (![(29786, 118931, 1261922, 4256236, 18914779), (36562, 135513, 1632396, 5503320, 22847601), (39074, 153473, 1785392, 6347074, 27274697), (34422, 126361, 1480110, 4920141, 20581223)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block37_info
  obtain ⟨hlt, hbt, hst⟩ := tail38_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail37, List.length_append, hlb, hlt]
  · simp only [tail37, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail37, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail36_info : tail36.length = 1227 ∧ tail36.all bounded = true ∧
    ∀ j : Fin 4, stats tail36 j = (![(30316, 121751, 1282388, 4344178, 19419111), (36888, 137898, 1641820, 5556836, 23272044), (39416, 155782, 1798318, 6397104, 27613564), (35042, 129689, 1511034, 5042559, 21206051)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block36_info
  obtain ⟨hlt, hbt, hst⟩ := tail37_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail36, List.length_append, hlb, hlt]
  · simp only [tail36, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail36, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail35_info : tail35.length = 1247 ∧ tail35.all bounded = true ∧
    ∀ j : Fin 4, stats tail35 j = (![(30962, 124244, 1311676, 4448960, 19852076), (37336, 140267, 1656840, 5621748, 23682009), (39866, 157657, 1813564, 6453995, 27880133), (35631, 132574, 1538363, 5138005, 21675712)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block35_info
  obtain ⟨hlt, hbt, hst⟩ := tail36_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail35, List.length_append, hlb, hlt]
  · simp only [tail35, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail35, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail34_info : tail34.length = 1267 ∧ tail34.all bounded = true ∧
    ∀ j : Fin 4, stats tail34 j = (![(31590, 126581, 1337490, 4530536, 20162551), (37879, 141823, 1677623, 5679141, 23880299), (40598, 160293, 1848994, 6567104, 28299399), (36248, 134431, 1566840, 5223032, 21965031)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block34_info
  obtain ⟨hlt, hbt, hst⟩ := tail35_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail34, List.length_append, hlb, hlt]
  · simp only [tail34, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail34, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail33_info : tail33.length = 1287 ∧ tail33.all bounded = true ∧
    ∀ j : Fin 4, stats tail33 j = (![(32213, 128642, 1362941, 4614551, 20455956), (38454, 144291, 1701234, 5774349, 24296449), (41097, 161941, 1866401, 6624244, 28499597), (36854, 137072, 1592252, 5325581, 22416188)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block33_info
  obtain ⟨hlt, hbt, hst⟩ := tail34_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail33, List.length_append, hlb, hlt]
  · simp only [tail33, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail33, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail32_info : tail32.length = 1307 ∧ tail32.all bounded = true ∧
    ∀ j : Fin 4, stats tail32 j = (![(32943, 131187, 1399731, 4736111, 20870651), (38744, 145476, 1708884, 5798699, 24415254), (41317, 162566, 1869851, 6632424, 28534402), (37669, 140297, 1628107, 5472811, 23060383)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block32_info
  obtain ⟨hlt, hbt, hst⟩ := tail33_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail32, List.length_append, hlb, hlt]
  · simp only [tail32, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail32, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail31_info : tail31.length = 1327 ∧ tail31.all bounded = true ∧
    ∀ j : Fin 4, stats tail31 j = (![(33693, 133740, 1435095, 4848996, 21288746), (39248, 147225, 1732262, 5875187, 24694589), (41869, 164339, 1895299, 6710474, 28834505), (38434, 143098, 1665160, 5604395, 23556650)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block31_info
  obtain ⟨hlt, hbt, hst⟩ := tail32_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail31, List.length_append, hlb, hlt]
  · simp only [tail31, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail31, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail30_info : tail30.length = 1347 ∧ tail30.all bounded = true ∧
    ∀ j : Fin 4, stats tail30 j = (![(34413, 136387, 1464119, 4956590, 21724657), (39648, 149781, 1745826, 5939984, 25079783), (42569, 167111, 1926715, 6827020, 29301447), (38680, 145067, 1673230, 5639474, 23798293)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block30_info
  obtain ⟨hlt, hbt, hst⟩ := tail31_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail30, List.length_append, hlb, hlt]
  · simp only [tail30, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail30, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail29_info : tail29.length = 1367 ∧ tail29.all bounded = true ∧
    ∀ j : Fin 4, stats tail29 j = (![(35224, 138537, 1503506, 5062295, 22073037), (40431, 152461, 1780265, 6056645, 25510313), (43365, 169163, 1966035, 6929614, 29646553), (39439, 147841, 1708775, 5770589, 24301937)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block29_info
  obtain ⟨hlt, hbt, hst⟩ := tail30_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail29, List.length_append, hlb, hlt]
  · simp only [tail29, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail29, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail28_info : tail28.length = 1387 ∧ tail28.all bounded = true ∧
    ∀ j : Fin 4, stats tail28 j = (![(35983, 140885, 1535123, 5158842, 22428087), (41203, 154550, 1816701, 6155901, 25820198), (43785, 170070, 1980739, 6953173, 29705514), (40097, 149615, 1735541, 5850871, 24593631)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block28_info
  obtain ⟨hlt, hbt, hst⟩ := tail29_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail28, List.length_append, hlb, hlt]
  · simp only [tail28, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail28, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail27_info : tail27.length = 1407 ∧ tail27.all bounded = true ∧
    ∀ j : Fin 4, stats tail27 j = (![(36658, 144320, 1560928, 5281434, 23064570), (41884, 156885, 1846442, 6257058, 26207065), (44084, 172009, 1991492, 7001018, 29993069), (40799, 151868, 1770059, 5959327, 24964706)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block27_info
  obtain ⟨hlt, hbt, hst⟩ := tail28_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail27, List.length_append, hlb, hlt]
  · simp only [tail27, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail27, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail26_info : tail26.length = 1427 ∧ tail26.all bounded = true ∧
    ∀ j : Fin 4, stats tail26 j = (![(37295, 146134, 1581269, 5340151, 23303360), (42644, 159157, 1878186, 6343786, 26483345), (44910, 174435, 2028090, 7100906, 30337653), (41228, 153010, 1782044, 5994646, 25108032)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block26_info
  obtain ⟨hlt, hbt, hst⟩ := tail27_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail26, List.length_append, hlb, hlt]
  · simp only [tail26, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail26, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail25_info : tail25.length = 1447 ∧ tail25.all bounded = true ∧
    ∀ j : Fin 4, stats tail25 j = (![(38045, 149327, 1613055, 5471244, 23877735), (43184, 161406, 1897458, 6412501, 26764510), (45543, 177214, 2055993, 7210367, 30800794), (41774, 155213, 1806712, 6087084, 25494611)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block25_info
  obtain ⟨hlt, hbt, hst⟩ := tail26_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail25, List.length_append, hlb, hlt]
  · simp only [tail25, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail25, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail24_info : tail24.length = 1467 ∧ tail24.all bounded = true ∧
    ∀ j : Fin 4, stats tail24 j = (![(38680, 152207, 1633576, 5561614, 24314783), (43979, 165111, 1935577, 6575768, 27575367), (46092, 179889, 2077728, 7300520, 31230551), (42216, 157473, 1825448, 6147569, 25792839)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block24_info
  obtain ⟨hlt, hbt, hst⟩ := tail25_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail24, List.length_append, hlb, hlt]
  · simp only [tail24, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail24, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail23_info : tail23.length = 1487 ∧ tail23.all bounded = true ∧
    ∀ j : Fin 4, stats tail23 j = (![(39457, 155018, 1667333, 5682984, 24776726), (44738, 168559, 1974178, 6731308, 28267239), (46694, 182145, 2105016, 7394284, 31579751), (42710, 159930, 1847554, 6232462, 26182294)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block23_info
  obtain ⟨hlt, hbt, hst⟩ := tail24_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail23, List.length_append, hlb, hlt]
  · simp only [tail23, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail23, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail22_info : tail22.length = 1507 ∧ tail22.all bounded = true ∧
    ∀ j : Fin 4, stats tail22 j = (![(40268, 157840, 1706878, 5825530, 25304520), (45364, 171085, 2006966, 6847668, 28708475), (47215, 183895, 2128907, 7470896, 31832635), (43248, 162170, 1871444, 6322989, 26555060)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block22_info
  obtain ⟨hlt, hbt, hst⟩ := tail23_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail22, List.length_append, hlb, hlt]
  · simp only [tail22, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail22, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail21_info : tail21.length = 1527 ∧ tail21.all bounded = true ∧
    ∀ j : Fin 4, stats tail21 j = (![(41180, 161026, 1753236, 5987465, 25896592), (45849, 173083, 2027993, 6921821, 29004923), (47605, 185131, 2143249, 7516422, 31998903), (44002, 165242, 1905348, 6457852, 27129872)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block21_info
  obtain ⟨hlt, hbt, hst⟩ := tail22_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail21, List.length_append, hlb, hlt]
  · simp only [tail21, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail21, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail20_info : tail20.length = 1547 ∧ tail20.all bounded = true ∧
    ∀ j : Fin 4, stats tail20 j = (![(41960, 163818, 1786624, 6108357, 26397608), (46549, 175919, 2057261, 7029729, 29491367), (48061, 186727, 2159201, 7564870, 32174787), (44714, 168154, 1940988, 6572048, 27600008)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block20_info
  obtain ⟨hlt, hbt, hst⟩ := tail21_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail20, List.length_append, hlb, hlt]
  · simp only [tail20, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail20, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail19_info : tail19.length = 1567 ∧ tail19.all bounded = true ∧
    ∀ j : Fin 4, stats tail19 j = (![(42600, 166738, 1807284, 6206717, 26958408), (47219, 178079, 2082831, 7092339, 29755067), (48581, 189107, 2176641, 7626750, 32458007), (45354, 170114, 1974988, 6634768, 27792088)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block19_info
  obtain ⟨hlt, hbt, hst⟩ := tail20_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail19, List.length_append, hlb, hlt]
  · simp only [tail19, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail19, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail18_info : tail18.length = 1587 ∧ tail18.all bounded = true ∧
    ∀ j : Fin 4, stats tail18 j = (![(43321, 169384, 1836631, 6314940, 27445340), (48007, 180322, 2116401, 7188276, 30058200), (49170, 191108, 2199884, 7691944, 32709992), (46007, 171876, 2000277, 6704924, 28015888)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block18_info
  obtain ⟨hlt, hbt, hst⟩ := tail19_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail18, List.length_append, hlb, hlt]
  · simp only [tail18, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail18, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail17_info : tail17.length = 1607 ∧ tail17.all bounded = true ∧
    ∀ j : Fin 4, stats tail17 j = (![(44083, 172072, 1868525, 6423969, 27933622), (48769, 182616, 2149843, 7288135, 30390538), (49694, 192778, 2219250, 7739769, 32918586), (46694, 173936, 2029660, 6797730, 28348554)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block17_info
  obtain ⟨hlt, hbt, hst⟩ := tail18_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail17, List.length_append, hlb, hlt]
  · simp only [tail17, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail17, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail16_info : tail16.length = 1627 ∧ tail16.all bounded = true ∧
    ∀ j : Fin 4, stats tail16 j = (![(44860, 174053, 1901056, 6510360, 28212099), (49399, 185264, 2173113, 7379535, 30797366), (50226, 193894, 2237436, 7777951, 33023406), (47444, 177223, 2069056, 6945437, 28965899)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block16_info
  obtain ⟨hlt, hbt, hst⟩ := tail17_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail16, List.length_append, hlb, hlt]
  · simp only [tail16, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail16, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail15_info : tail15.length = 1647 ∧ tail15.all bounded = true ∧
    ∀ j : Fin 4, stats tail15 j = (![(45501, 176925, 1929279, 6629760, 28739725), (49907, 186950, 2193505, 7444159, 31015670), (50789, 196414, 2260457, 7875134, 33451590), (48255, 179983, 2108335, 7082648, 29467945)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block15_info
  obtain ⟨hlt, hbt, hst⟩ := tail16_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail15, List.length_append, hlb, hlt]
  · simp only [tail15, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail15, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail14_info : tail14.length = 1667 ∧ tail14.all bounded = true ∧
    ∀ j : Fin 4, stats tail14 j = (![(46241, 179546, 1963001, 6750800, 29195558), (50467, 189128, 2219369, 7541459, 31399372), (51553, 199138, 2297215, 8002751, 33909160), (48875, 182426, 2134735, 7182699, 29869310)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block14_info
  obtain ⟨hlt, hbt, hst⟩ := tail15_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail14, List.length_append, hlb, hlt]
  · simp only [tail14, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail14, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail13_info : tail13.length = 1687 ∧ tail13.all bounded = true ∧
    ∀ j : Fin 4, stats tail13 j = (![(47101, 182619, 2006639, 6898526, 29747289), (51047, 191647, 2245527, 7641396, 31841891), (51966, 200575, 2311388, 8052679, 34144951), (49628, 185635, 2168524, 7319346, 30478389)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block13_info
  obtain ⟨hlt, hbt, hst⟩ := tail14_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail13, List.length_append, hlb, hlt]
  · simp only [tail13, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail13, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail12_info : tail12.length = 1707 ∧ tail12.all bounded = true ∧
    ∀ j : Fin 4, stats tail12 j = (![(48019, 186007, 2052637, 7057482, 30362301), (51441, 193821, 2258713, 7704522, 32215309), (52320, 201949, 2320682, 8089771, 34369377), (50376, 189163, 2201084, 7458690, 31145393)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block12_info
  obtain ⟨hlt, hbt, hst⟩ := tail13_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail12, List.length_append, hlb, hlt]
  · simp only [tail12, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail12, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail11_info : tail11.length = 1727 ∧ tail11.all bounded = true ∧
    ∀ j : Fin 4, stats tail11 j = (![(48728, 188160, 2084126, 7153922, 30721854), (51988, 196470, 2281190, 7810187, 32734576), (52910, 203768, 2345712, 8156757, 34595412), (50978, 192116, 2229036, 7576509, 31681778)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block11_info
  obtain ⟨hlt, hbt, hst⟩ := tail12_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail11, List.length_append, hlb, hlt]
  · simp only [tail11, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail11, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail10_info : tail10.length = 1747 ∧ tail10.all bounded = true ∧
    ∀ j : Fin 4, stats tail10 j = (![(49514, 191010, 2120296, 7281012, 31217456), (52622, 199030, 2307406, 7912415, 33197334), (53466, 205774, 2368164, 8233000, 34899230), (51622, 194738, 2257808, 7677037, 32097700)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block10_info
  obtain ⟨hlt, hbt, hst⟩ := tail11_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail10, List.length_append, hlb, hlt]
  · simp only [tail10, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail10, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail9_info : tail9.length = 1767 ∧ tail9.all bounded = true ∧
    ∀ j : Fin 4, stats tail9 j = (![(50400, 194376, 2164828, 7444650, 31835452), (53034, 200623, 2325414, 7963454, 33395593), (53776, 206955, 2377878, 8271631, 35066541), (52486, 198050, 2297052, 7829221, 32760224)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block9_info
  obtain ⟨hlt, hbt, hst⟩ := tail10_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail9, List.length_append, hlb, hlt]
  · simp only [tail9, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail9, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail8_info : tail8.length = 1787 ∧ tail8.all bounded = true ∧
    ∀ j : Fin 4, stats tail8 j = (![(51164, 197194, 2199586, 7564401, 32323772), (53575, 202867, 2347017, 8039677, 33768633), (54338, 209041, 2399558, 8341688, 35373413), (53170, 200852, 2324668, 7935129, 33264272)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block8_info
  obtain ⟨hlt, hbt, hst⟩ := tail9_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail8, List.length_append, hlb, hlt]
  · simp only [tail8, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail8, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail7_info : tail7.length = 1807 ∧ tail7.all bounded = true ∧
    ∀ j : Fin 4, stats tail7 j = (![(52012, 200922, 2239450, 7725953, 33033004), (53919, 203791, 2359481, 8071877, 33856741), (54742, 210997, 2413714, 8404392, 35691281), (54018, 203604, 2365292, 8073013, 33759264)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block7_info
  obtain ⟨hlt, hbt, hst⟩ := tail8_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail7, List.length_append, hlb, hlt]
  · simp only [tail7, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail7, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail6_info : tail6.length = 1827 ∧ tail6.all bounded = true ∧
    ∀ j : Fin 4, stats tail6 j = (![(52873, 203860, 2281019, 7866090, 33577196), (54317, 205280, 2373839, 8120873, 34057994), (55319, 212856, 2439657, 8481409, 35966558), (54680, 206162, 2394860, 8181502, 34208092)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block6_info
  obtain ⟨hlt, hbt, hst⟩ := tail7_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail6, List.length_append, hlb, hlt]
  · simp only [tail6, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail6, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail5_info : tail5.length = 1847 ∧ tail5.all bounded = true ∧
    ∀ j : Fin 4, stats tail5 j = (![(53797, 207256, 2327935, 8033281, 34241858), (54601, 207048, 2382795, 8157684, 34351692), (55743, 214484, 2457015, 8534302, 36205496), (55434, 209728, 2433474, 8330865, 34913934)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block5_info
  obtain ⟨hlt, hbt, hst⟩ := tail6_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail5, List.length_append, hlb, hlt]
  · simp only [tail5, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail5, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail4_info : tail4.length = 1867 ∧ tail4.all bounded = true ∧
    ∀ j : Fin 4, stats tail4 j = (![(54721, 210517, 2376639, 8204198, 34866601), (55082, 209241, 2404518, 8227128, 34695009), (56205, 216063, 2474407, 8591655, 36424721), (55962, 212141, 2457884, 8421899, 35377589)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block4_info
  obtain ⟨hlt, hbt, hst⟩ := tail5_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail4, List.length_append, hlb, hlt]
  · simp only [tail4, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail4, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail3_info : tail3.length = 1887 ∧ tail3.all bounded = true ∧
    ∀ j : Fin 4, stats tail3 j = (![(55512, 213257, 2413154, 8339433, 35385575), (56098, 213261, 2460862, 8446468, 35564105), (56700, 217711, 2494138, 8651727, 36612609), (56475, 214297, 2476861, 8497793, 35698951)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block3_info
  obtain ⟨hlt, hbt, hst⟩ := tail4_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail3, List.length_append, hlb, hlt]
  · simp only [tail3, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail3, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail2_info : tail2.length = 1907 ∧ tail2.all bounded = true ∧
    ∀ j : Fin 4, stats tail2 j = (![(56351, 215885, 2455369, 8481308, 35879055), (56856, 215690, 2495940, 8559652, 35975150), (57285, 219296, 2516923, 8712425, 36776350), (57087, 216287, 2501529, 8578157, 36005175)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block2_info
  obtain ⟨hlt, hbt, hst⟩ := tail3_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail2, List.length_append, hlb, hlt]
  · simp only [tail2, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail2, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail1_info : tail1.length = 1927 ∧ tail1.all bounded = true ∧
    ∀ j : Fin 4, stats tail1 j = (![(57257, 218199, 2499923, 8606081, 36303003), (57673, 219262, 2535029, 8715150, 36658942), (57995, 220976, 2547519, 8778952, 36935194), (57394, 218127, 2511656, 8621754, 36280891)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block1_info
  obtain ⟨hlt, hbt, hst⟩ := tail2_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail1, List.length_append, hlb, hlt]
  · simp only [tail1, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail1, stats_append, hsb, hst]
    fin_cases j <;> rfl
lemma tail0_info : tail0.length = 1947 ∧ tail0.all bounded = true ∧
    ∀ j : Fin 4, stats tail0 j = (![(58267, 221645, 2557375, 8802548, 37010835), (58267, 221645, 2557375, 8802548, 37010835), (58267, 221645, 2557375, 8802548, 37010835), (58267, 221645, 2557375, 8802548, 37010835)]) j := by
  obtain ⟨hlb, hbb, hsb⟩ := block0_info
  obtain ⟨hlt, hbt, hst⟩ := tail1_info
  refine ⟨?_, ?_, ?_⟩
  · simp only [tail0, List.length_append, hlb, hlt]
  · simp only [tail0, List.all_append, hbb, hbt, Bool.true_and]
  · intro j
    rw [tail0, stats_append, hsb, hst]
    fin_cases j <;> rfl

end

lemma length_verified : steps.length = 1947 := tail0_info.1

lemma bounds_verified : steps.all (fun s =>
    decide (∀ j : Fin 4, s.constant j ≤ 63 ∧ s.slope j ≤ 242)) = true := tail0_info.2.1

lemma moments_verified (j : Fin 4) :
    (steps.map (fun s => s.constant j)).sum = 58267 ∧
    (steps.map (fun s => s.slope j)).sum = 221645 ∧
    (steps.map (fun s => s.constant j ^ 2)).sum = 2557375 ∧
    (steps.map (fun s => s.constant j * s.slope j)).sum = 8802548 ∧
    (steps.map (fun s => s.slope j ^ 2)).sum = 37010835 := by
  have hv : (![(58267, 221645, 2557375, 8802548, 37010835),
      (58267, 221645, 2557375, 8802548, 37010835),
      (58267, 221645, 2557375, 8802548, 37010835),
      (58267, 221645, 2557375, 8802548, 37010835)] : Fin 4 → Stats) j =
      (58267, 221645, 2557375, 8802548, 37010835) := by
    fin_cases j <;> rfl
  have h : stats steps j = (58267, 221645, 2557375, 8802548, 37010835) :=
    (tail0_info.2.2 j).trans hv
  exact (stats_eq_iff steps j 58267 221645 2557375 8802548 37010835).mp h

def word (j : Fin 4) (t : ℕ) : List ℕ :=
  steps.map (fun s => digit s j t) ++ [1]

lemma word_moments (j : Fin 4) (t : ℕ) :
    (word j t).sum = 116535 + 56741120 * t ∧
    ((word j t).map (fun x => x ^ 2)).sum =
      10229501 + 9013809152 * t + 2425542082560 * t ^ 2 := by
  obtain ⟨hc, hs, hcq, hcs, hsq⟩ := moments_verified j
  constructor
  · simp only [word, List.sum_append, List.sum_cons, List.sum_nil, sum_digits]
    rw [hc, hs]
    ring
  · simp only [word, List.map_append, List.map_map, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, Function.comp_def]
    rw [sum_square_digits, hcq, hcs, hsq]
    norm_num
    ring

lemma word_conditions (j : Fin 4) (t : ℕ) :
    (word j t).length = 1948 ∧ (word j t).getLast? = some 1 ∧
    (word j t).headD 0 % 4 = 2 ∧
    (∀ x ∈ (word j t).dropLast, 2 ∣ x) ∧
    ∀ x ∈ word j t, 2 * x < base t := by
  have hb (s : Step) (hs : s ∈ steps) :=
    of_decide_eq_true (((List.all_eq_true (l := steps) (p := bounded)).mp bounds_verified) s hs)
  have hn : steps ≠ [] := by intro h; have := length_verified; simp [h] at this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [word, length_verified]
  · simp [word]
  · change (digit firstStep j t) % 4 = 2
    fin_cases j <;> simp [digit, firstStep, step0, mkStep, Nat.add_mod, Nat.mul_mod]
  · intro x hx
    have hm : x ∈ steps.map (fun s => digit s j t) := by
      simpa [word] using hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
    refine ⟨s.constant j + 128 * s.slope j * t, ?_⟩
    dsimp [digit]
    ring
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
      obtain ⟨hc, hsl⟩ := hb s hs j
      dsimp [digit, base]
      nlinarith [Nat.mul_le_mul_right t hsl]
    · have hx1 : x = 1 := by simpa using hx
      subst x
      unfold base
      omega

lemma value_mod_cons (s : Step) (ss : List Step) (j : Fin 4) (t : ℕ) :
    value (s :: ss) j t % 256 = 2 * s.constant j % 256 := by
  simp [value, digit, base, Nat.add_mod, Nat.mul_mod]

lemma value_mod (j : Fin 4) (t : ℕ) :
    value steps j t % 256 = 2 * firstStep.constant j % 256 := by
  exact value_mod_cons firstStep steps.tail j t

lemma values_injective (t : ℕ) : Function.Injective (fun j : Fin 4 => value steps j t) := by
  intro i j h
  have hm : value steps i t % 256 = value steps j t % 256 :=
    congrArg (fun x : ℕ => x % 256) h
  clear h
  rw [value_mod, value_mod] at hm
  have hi : Function.Injective (fun j : Fin 4 => 2 * firstStep.constant j % 256) := by
    decide +kernel
  exact hi hm

lemma family_collision (t : ℕ) :
    value steps 0 t ^ 2 + value steps 1 t ^ 2 =
      value steps 2 t ^ 2 + value steps 3 t ^ 2 :=
  norm_collision_of_checkPath steps path_verified t

lemma not_sidon_of_four (f : Fin 4 → ℕ) (hf : Function.Injective f)
    (he : f 0 ^ 2 + f 1 ^ 2 = f 2 ^ 2 + f 3 ^ 2) :
    ¬ IsSidon (((Finset.univ : Finset (Fin 4)).image
      (fun j => f j ^ 2)) : Set ℕ) := by
  intro h
  have hm (j : Fin 4) : f j ^ 2 ∈
      ((Finset.univ : Finset (Fin 4)).image (fun j => f j ^ 2) : Set ℕ) := by
    simp only [Finset.mem_coe, Finset.mem_image]
    exact ⟨j, Finset.mem_univ j, rfl⟩
  have hh := h _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) he
  have hinj := (Nat.pow_left_injective (by decide : 2 ≠ 0)).comp hf
  rcases hh with hh | hh
  · have : (0 : Fin 4) = 2 := hinj hh.1
    exact (by decide : (0 : Fin 4) ≠ 2) this
  · have : (0 : Fin 4) = 3 := hinj hh.1
    exact (by decide : (0 : Fin 4) ≠ 3) this

lemma family_not_sidon (t : ℕ) :
    ¬ IsSidon (((Finset.univ : Finset (Fin 4)).image
      (fun j => value steps j t ^ 2)) : Set ℕ) :=
  not_sidon_of_four (fun j => value steps j t) (values_injective t) (family_collision t)

lemma mod_value (ss : List Step) (j : Fin 4) (t : ℕ) :
    value ss j t % (255 + 124160 * t) =
      ((ss.map (fun s => digit s j t)).sum + 1) % (255 + 124160 * t) := by
  have hb : base t % (255 + 124160 * t) = 1 := by
    have he : base t = (255 + 124160 * t) + 1 := by unfold base; omega
    rw [he, Nat.add_mod, Nat.mod_self, zero_add]
    simpa only [Nat.mod_mod] using (Nat.mod_eq_of_lt (show 1 < 255 + 124160 * t by omega))
  induction ss with
  | nil => simp [value]
  | cons s ss ih =>
    change (digit s j t + base t * value ss j t) % _ = _
    rw [Nat.add_mod, Nat.mul_mod, hb, one_mul, ih]
    simp only [List.map_cons, List.sum_cons, Nat.mod_mod]
    rw [← Nat.add_mod]
    congr 1

lemma bases_unbounded (B : ℕ) : B ≤ base B := by unfold base; omega

lemma family_common_divisor (j : Fin 4) (t : ℕ) :
    255 + 124160 * t ∣ value steps j t := by
  apply Nat.dvd_of_mod_eq_zero
  rw [mod_value, sum_digits]
  obtain ⟨hc, hs, _, _, _⟩ := moments_verified j
  rw [hc, hs]
  have he : 2 * 58267 + 256 * t * 221645 + 1 = 457 * (255 + 124160 * t) := by ring
  rw [he]
  simp

#print axioms family_common_divisor
#print axioms family_not_sidon
#print axioms word_conditions
#print axioms word_moments

end Erdos773.ParametricSphere
