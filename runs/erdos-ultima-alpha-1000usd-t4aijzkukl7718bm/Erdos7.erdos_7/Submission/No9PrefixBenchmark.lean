import Submission.No9CertificateCore
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 100000000
def oldState : State := ⟨1000000000000000000,4500000000000000000,fun j => (if j < 85 then (if j < 42 then (if j < 21 then (if j < 10 then (if j < 5 then (if j < 2 then (if j < 1 then 1500000000000000000 else 500000000000000000) else 0) else 0) else 0) else 0) else 0) else 0)⟩
def newState : State := ⟨833333333333333333,20062500000000000000,fun j => (if j < 85 then (if j < 42 then (if j < 21 then (if j < 10 then (if j < 5 then (if j < 2 then (if j < 1 then 1833333333333682867 else 1000000000000349534) else (if j < 3 then 366666666667365726 else (if j < 4 then 206666666667715243 else 68000000001398109))) else (if j < 7 then (if j < 6 then 40266666668414301 else 13386666668763820) else (if j < 8 then 8010666669113351 else (if j < 9 then 2668800002796209 else 1600426669812396)))) else (if j < 15 then (if j < 12 then (if j < 11 then 533418670161926 else 320017070511451) else (if j < 13 then 106670084194306 else (if j < 14 then 64000687210501 else 21333474760026))) else (if j < 18 then (if j < 16 then 12800032549549 else (if j < 17 then 4266677720409 else 2560007034201)) else (if j < 19 then 853339843246 else (if j < 20 then 512006684675 else 170673526104))))) else (if j < 31 then (if j < 26 then (if j < 23 then (if j < 22 then 102407034200 else 34140542296) else (if j < 24 then 20487383725 else (if j < 25 then 6834225154 else 4103733250))) else (if j < 28 then (if j < 27 then 1373241346 else 827282775) else (if j < 29 then 281324204 else (if j < 30 then 172272300 else 63220396)))) else (if j < 36 then (if j < 33 then (if j < 32 then 41549825 else 19879254) else (if j < 34 then 11490646 else 10092544)) else 10092544))) else 10092544) else 10092544)⟩
def testControl : PrefixControl := ⟨5,4,3,18,1,1⟩
theorem benchmark_certificate : checkState (step testControl oldState) newState=true := by
  decide +kernel

#print axioms benchmark_certificate
end Erdos7No9Certificate
