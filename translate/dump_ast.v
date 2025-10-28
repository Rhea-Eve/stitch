(* q_inc_verified = *)
tLambda (nNamed "n") (tInd (mkInd (<nat>) 0) []) (
  tApp
    (tConst "Coq.Init.Specif.exist" [])
    (tConst "Coq.Init.Datatypes.nat" []) (* type arg *)
    (tApp (tConst "Coq.Init.Datatypes.S" []) (tRel 0))
    (tConst "Coq.Init.Logic.eq_refl" [])
)
