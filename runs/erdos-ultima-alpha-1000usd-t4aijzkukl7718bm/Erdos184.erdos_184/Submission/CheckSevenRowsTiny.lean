import Submission.PureSevenRowModel
namespace Erdos184Work.PureSevenRowModel
example (a0 a1 a2 a3 a4 a5 x : Fin 60) :
    rows a0 a1 a2 a3 a4 a5 x (0 : Fin 7) = a0 := by rfl
#eval IO.eprintln "zero done"
example (a0 a1 a2 a3 a4 a5 x : Fin 60) :
    rows a0 a1 a2 a3 a4 a5 x (5 : Fin 7) = a5 := by rfl
#eval IO.eprintln "five done"
example (a0 a1 a2 a3 a4 a5 x : Fin 60) :
    rows a0 a1 a2 a3 a4 a5 x (5 : Fin 6).castSucc = a5 := by rfl
#eval IO.eprintln "cast five done"
end Erdos184Work.PureSevenRowModel
