module Sp = Smtlibprover
module S = Smtlib
module P = Proverapi

let _ =
  Verifast.register_prover "Archsat"
    "\brun the Archsat SMT sol ver."
    (
      fun client ->
      let archsat_ctxt =
        Sp.external_smtlib_ctxt
          "archsat"
          ["archsat"; "I"; "Q"; "NDT"]
      in
      client#run archsat_ctxt
    )
