import FormalConjecturesUtil

/-! Exact finite rational row data for a prime-19 backward candidate.
This verifies ONLY finite scalar checks. Continuum interpolation, geometric
series identities, and the arithmetic family connection remain separate. -/
namespace Erdos7Capped19Rows
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def evaluate (f : List ℚ) (x : ℚ) : ℚ :=
  f[0]?.getD 0 + (f[1]?.getD 0)*(x-1) +
    ((List.range 8).map (fun (j : ℕ) => (f[j+2]?.getD 0)*max 0 (x-(j+2)))).sum

def slope (f : List ℚ) : ℚ := f.tail.sum

def retention (p c k : ℚ) : ℚ := max 0 (min 1 (c*(1-k/(p-1))))

def mixture (p c h : ℚ) (f : List ℚ) (n : ℚ) : ℚ :=
  h*evaluate f n + ((List.range 9).map (fun (j : ℕ) =>
    min h (c/p^(j+1))*(evaluate f ((j+2)*n)-evaluate f ((j+1)*n)))).sum +
      c/(p^9*(p-1))*slope f*n

def firstMoment (p c h : ℚ) : ℚ := h +
  ((List.range 4).map (fun (j : ℕ) => min h (c/p^(j+1)))).sum + c/(p^4*(p-1))

structure Stage where
  p : ℚ
  cap : ℚ
  cut : ℚ
  rows : List ℚ
  U : List ℚ
  V : List ℚ
  F : List ℚ
  deriving DecidableEq

def Valid (s : Stage) (future : List ℚ) : Prop :=
  s.U.length=10 ∧ s.V.length=10 ∧ s.F=s.U.zipWith (·+·) s.V ∧
  (∀ a ∈ s.U++s.V, 0 ≤ a) ∧
  1 ≤ evaluate s.U s.cut + evaluate s.V 1 ∧
  ∀ k ∈ s.rows,
    s.cap/s.p^4 ≤ retention s.p s.cap k ∧
    slope future*firstMoment s.p s.cap (retention s.p s.cap k) ≤ slope s.V ∧
    ∀ (n : ℕ), n ∈ List.range 9 →
      1-retention s.p s.cap k +
        mixture s.p s.cap (retention s.p s.cap k) future (n+1) ≤
          evaluate s.U k + evaluate s.V (n+1)

instance (s : Stage) (future : List ℚ) : Decidable (Valid s future) := by
  unfold Valid
  infer_instance

def stage5 : Stage := {
  p := 5, cap := (4/3 : ℚ), cut := (2496/625 : ℚ)
  rows := [1, 2, 3, (16/5 : ℚ), (96/25 : ℚ), (496/125 : ℚ), (2496/625 : ℚ)]
  U := [(13949/100000 : ℚ), (29023/100000 : ℚ), (437/25000 : ℚ), 0, 0, 0, 0, 0, 0, 0]
  V := [0, (18427/50000 : ℚ), (47217/100000 : ℚ), (17019/100000 : ℚ), (5529/25000 : ℚ), (867/25000 : ℚ), (1113/12500 : ℚ), (1/100000 : ℚ), (5171/100000 : ℚ), (507/12500 : ℚ)]
  F := [(13949/100000 : ℚ), (65877/100000 : ℚ), (9793/20000 : ℚ), (17019/100000 : ℚ), (5529/25000 : ℚ), (867/25000 : ℚ), (1113/12500 : ℚ), (1/100000 : ℚ), (5171/100000 : ℚ), (507/12500 : ℚ)] }

def stage7 : Stage := {
  p := 7, cap := (3/2 : ℚ), cut := (14400/2401 : ℚ)
  rows := [1, 2, 3, 4, 5, (36/7 : ℚ), (288/49 : ℚ), (2052/343 : ℚ), (14400/2401 : ℚ)]
  U := [(1539/20000 : ℚ), 0, (2249/10000 : ℚ), (839/100000 : ℚ), 0, 0, 0, 0, 0, 0]
  V := [0, (5247/100000 : ℚ), (15189/100000 : ℚ), (3137/25000 : ℚ), (24447/100000 : ℚ), (3119/100000 : ℚ), (6071/50000 : ℚ), 0, (1763/25000 : ℚ), (5531/100000 : ℚ)]
  F := [(1539/20000 : ℚ), (5247/100000 : ℚ), (37679/100000 : ℚ), (13387/100000 : ℚ), (24447/100000 : ℚ), (3119/100000 : ℚ), (6071/50000 : ℚ), 0, (1763/25000 : ℚ), (5531/100000 : ℚ)] }

def stage11 : Stage := {
  p := 11, cap := (5/3 : ℚ), cut := (146400/14641 : ℚ)
  rows := [1, 2, 3, 4, 5, 6, 7, 8, 9, (100/11 : ℚ), (1200/121 : ℚ), (13300/1331 : ℚ), (146400/14641 : ℚ)]
  U := [(6687/100000 : ℚ), 0, 0, 0, (15599/100000 : ℚ), 0, 0, 0, 0, 0]
  V := [0, (1/50000 : ℚ), (839/25000 : ℚ), (1449/25000 : ℚ), (4837/50000 : ℚ), (93/4000 : ℚ), (7727/50000 : ℚ), 0, (359/4000 : ℚ), (7039/100000 : ℚ)]
  F := [(6687/100000 : ℚ), (1/50000 : ℚ), (839/25000 : ℚ), (1449/25000 : ℚ), (25273/100000 : ℚ), (93/4000 : ℚ), (7727/50000 : ℚ), 0, (359/4000 : ℚ), (7039/100000 : ℚ)] }

def stage13 : Stage := {
  p := 13, cap := 2, cut := (342720/28561 : ℚ)
  rows := [1, 2, 3, 4, 5, 6, 7, 8, 9, (144/13 : ℚ), (2016/169 : ℚ), (26352/2197 : ℚ), (342720/28561 : ℚ)]
  U := [(801/12500 : ℚ), 0, 0, 0, 0, 0, (3983/25000 : ℚ), 0, 0, 0]
  V := [0, (1/50000 : ℚ), 0, 0, (6621/100000 : ℚ), (1393/100000 : ℚ), (1141/50000 : ℚ), 0, (10577/100000 : ℚ), (1037/12500 : ℚ)]
  F := [(801/12500 : ℚ), (1/50000 : ℚ), 0, 0, (6621/100000 : ℚ), (1393/100000 : ℚ), (9107/50000 : ℚ), 0, (10577/100000 : ℚ), (1037/12500 : ℚ)] }

def stage17 : Stage := {
  p := 17, cap := 2, cut := (1336320/83521 : ℚ)
  rows := [1, 2, 3, 4, 5, 6, 7, 8, 9, (256/17 : ℚ), (4608/289 : ℚ), (78592/4913 : ℚ), (1336320/83521 : ℚ)]
  U := [(429/25000 : ℚ), (1/100000 : ℚ), 0, 0, 0, 0, 0, 0, (1/8 : ℚ), 0]
  V := [0, 0, 0, 0, 0, (2697/100000 : ℚ), 0, 0, 0, (1961/20000 : ℚ)]
  F := [(429/25000 : ℚ), (1/100000 : ℚ), 0, 0, 0, (2697/100000 : ℚ), 0, 0, (1/8 : ℚ), (1961/20000 : ℚ)] }

def stage19 : Stage := {
  p := 19, cap := (9/4 : ℚ), cut := (2345760/130321 : ℚ)
  rows := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, (324/19 : ℚ), (6480/361 : ℚ), (123444/6859 : ℚ), (2345760/130321 : ℚ)]
  U := [0, 0, 0, 0, 0, 0, 0, 0, 0, (1389/12500 : ℚ)]
  V := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  F := [0, 0, 0, 0, 0, 0, 0, 0, 0, (1389/12500 : ℚ)] }

def terminal : List ℚ := List.replicate 10 0

theorem stage5_valid : Valid stage5 stage7.F := by decide +kernel
#print axioms stage5_valid

theorem stage7_valid : Valid stage7 stage11.F := by decide +kernel
#print axioms stage7_valid

theorem stage11_valid : Valid stage11 stage13.F := by decide +kernel
#print axioms stage11_valid

theorem stage13_valid : Valid stage13 stage17.F := by decide +kernel
#print axioms stage13_valid

theorem stage17_valid : Valid stage17 stage19.F := by decide +kernel
#print axioms stage17_valid

theorem stage19_valid : Valid stage19 terminal := by decide +kernel
#print axioms stage19_valid

def rootValue : ℚ := evaluate stage5.F 1/3 +
  ((List.range 8).map (fun (j : ℕ) => 4*evaluate stage5.F (j+2)/3^(j+2))).sum +
    (2/3^9)*(evaluate stage5.F 9-9*slope stage5.F+(21/2)*slope stage5.F)

theorem rootValue_exact : rootValue = (108191129/109350000 : ℚ) := by decide +kernel
theorem rootValue_lt_one : rootValue < 1 := by rw [rootValue_exact]; norm_num
#print axioms rootValue_lt_one
end Erdos7Capped19Rows
