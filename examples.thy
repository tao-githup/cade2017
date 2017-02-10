theory examples
imports Main   "quantum_hoare_logic" "lt"
begin

lemma grover:  "valid I  
               (((Init 2 0;Init 2 1;Init 2 2;Init 4 3;
               Utrans Delta 2;Utrans H 0;Utrans H 1;Utrans H 2);
              While M0 M1 (Utrans Or (10);Utrans H 0;Utrans H 1;Utrans Ph 10;
         Utrans H 0; Utrans H 1) Q);
           Cond [(N0,SKIP,P),(N1,SKIP,P),(N2,SKIP,P),(N3,SKIP,P)] )             
               P"
apply(rule_tac Q="sum1 [(N0,SKIP,P),(N1,SKIP,P),(N2,SKIP,P),(N3,SKIP,P)]" in Seq)
prefer 2
apply(rule  Measure)
apply quantum_oracle
apply (simp add:Skip)+
apply(rule_tac Q="(mat_add (uu M0   (mat_add (mat_mult (mat_mult (dag N0) P) N0)
       (mat_add (mat_mult (mat_mult (dag N1) P) N1) (mat_add (mat_mult (mat_mult (dag N2) P) N2) (mat_mult (mat_mult (dag N3) P) N3))))) (uu M1 Q))" in Seq)
prefer 2
apply(rule While)
apply quantum_oracle
apply(vcg,auto)
prefer 7
apply(vcg,auto)
apply quantum_oracle+
done
(*
lemma shor:"valid P  (Init 2 0;Utrans H 0;Utrans U 1;Utrans (dag U) 1;Utrans (dag H) 0;
                    Cond [(M0,SKIP,Q),(M1,SKIP,Q)])   Q"
apply(rule ord_wlp,auto)
apply quantum_oracle+
apply (metis fst_conv fsts.cases snd_conv snds.cases wellDefined.simps(1))
apply (metis fst_conv fsts.cases snd_conv snds.cases wellDefined.simps(1))
apply quantum_oracle
done*)
end​
