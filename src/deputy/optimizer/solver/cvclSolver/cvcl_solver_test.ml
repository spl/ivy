

module C = Cvcl

let test () =
    let flags = C.createFlags () in
    let vc = C.createVC flags in
    let x = C.varExpr vc "x" (C.intType vc) in
    let y = C.varExpr vc "y" (C.intType vc) in
    let xpy = C.plusExpr vc x y in
    let xpygtten = C.gtExpr vc xpy (C.ratExpr vc 10 1) in
    let neg = C.notExpr vc xpygtten in
    if C.query vc neg <> 1 then
        let ces = C.getCounterExample vc in
        List.iter (C.printExpr vc) ces
    else
        print_string "Satisfiable"


let _ = test ();


