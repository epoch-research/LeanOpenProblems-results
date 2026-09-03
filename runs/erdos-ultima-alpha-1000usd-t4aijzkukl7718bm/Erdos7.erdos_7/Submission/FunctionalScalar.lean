import Submission.GridFunctionalCore
namespace Erdos7FunctionalGrid
set_option maxRecDepth 200000
set_option maxHeartbeats 100000000

def benchmarkControls : List Control := [⟨5,4,3,35,1,1⟩]
def benchmarkInitial : State := ⟨100000000000000,450000000000000,fun j => (if j < 123 then (if j < 61 then (if j < 30 then (if j < 15 then (if j < 7 then (if j < 3 then (if j < 1 then 150000000000000 else (if j < 2 then 50000000000000 else 0)) else 0) else 0) else 0) else 0) else 0) else 0)⟩
def benchmarkState : State := ⟨83333333333333,2006250000000000,fun j => (if j < 123 then (if j < 61 then (if j < 30 then (if j < 15 then (if j < 7 then (if j < 3 then (if j < 1 then 183333333333357 else (if j < 2 then 100000000000024 else 36666666666689)) else (if j < 5 then (if j < 4 then 20666666666684 else 6800000000023) else (if j < 6 then 4026666666689 else 1338666666687))) else (if j < 11 then (if j < 9 then (if j < 8 then 801066666690 else 266880000023) else (if j < 10 then 160042666686 else 53341866689)) else (if j < 13 then (if j < 12 then 32001706688 else 10667008020) else (if j < 14 then 6400068287 else 2133347007)))) else (if j < 22 then (if j < 18 then (if j < 16 then 1280002750 else (if j < 17 then 426667231 else 256000128)) else (if j < 20 then (if j < 19 then 85333375 else 51200023) else (if j < 21 then 17066685 else 10240018))) else (if j < 26 then (if j < 24 then (if j < 23 then 3413353 else 2048017) else (if j < 25 then 682685 else 409617)) else (if j < 28 then (if j < 27 then 136552 else 81938) else (if j < 29 then 27324 else 16401))))) else (if j < 45 then (if j < 37 then (if j < 33 then (if j < 31 then 5478 else (if j < 32 then 3294 else 1109)) else (if j < 35 then (if j < 34 then 672 else 234) else (if j < 36 then 146 else 59))) else (if j < 41 then (if j < 39 then (if j < 38 then 41 else 24) else (if j < 40 then 20 else 17)) else (if j < 43 then (if j < 42 then 16 else 15) else (if j < 44 then 15 else 14)))) else (if j < 53 then (if j < 49 then (if j < 47 then (if j < 46 then 14 else 13) else (if j < 48 then 13 else 12)) else (if j < 51 then (if j < 50 then 12 else 11) else (if j < 52 then 11 else 10))) else (if j < 57 then (if j < 55 then (if j < 54 then 10 else 9) else (if j < 56 then 9 else 8)) else (if j < 59 then (if j < 58 then 8 else 7) else (if j < 60 then 7 else 6)))))) else (if j < 92 then (if j < 76 then (if j < 68 then (if j < 64 then (if j < 62 then 6 else 5) else (if j < 66 then 4 else 3)) else (if j < 72 then (if j < 70 then 2 else 1) else 1)) else 1) else 1)) else 1)⟩

theorem benchmark_certificate : rawValue ⟨5,4,3,35,1,1⟩ benchmarkInitial.values 0=200000000000016 := by
  decide +kernel

#print axioms benchmark_certificate
end Erdos7FunctionalGrid
