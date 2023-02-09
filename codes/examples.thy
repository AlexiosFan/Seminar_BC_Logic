theory examples
  imports BC_Logic

begin

section \<open>Evaluation of BC-logic terms\<close>

value "T_eval (ITE 
                (EQ (ATOM ''msg'') (ATOM ''msg'')) 
                (Cons (ATOM ''fst'') (ATOM ''snd'')) 
                EMPTY)"

thm linear_complexity

value "T_eval (Cons (ATOM ''fst'') 
          (ITE (EQL (ATOM ''msg'') (ATOM ''msg'')) (ATOM ''snd'') (ATOM ''thd'')))"

value "T_bval (EQ (ATOM ''msg'') (ATOM ''msg''))"

value "T_bval (EQL (ATOM ''msg'') (ATOM ''msg''))"

section \<open>Folding protocols\<close>
value "fold (Rt [(\<theta>1, Nd m1 []), 
            (\<theta>2, Nd m2 [(\<eta>1, Nd n1 [])]), 
            (\<theta>3, Nd m3 [(\<eta>2, Nd n2 []), 
                       (\<eta>3, Nd n3 [])])])"

value "T_fold (Rt [(\<theta>1, Nd m1 []), 
            (\<theta>2, Nd m2 [(\<eta>1, Nd n1 [])]), 
            (\<theta>3, Nd m3 [(\<eta>2, Nd n2 []), 
                       (\<eta>3, Nd n3 [])])])"

value "let proc = (Rt [(\<theta>1, Nd m1 []), 
            (\<theta>2, Nd m2 [(\<eta>1, Nd n1 [])]), 
            (\<theta>3, Nd m3 [(\<eta>2, Nd n2 []), 
                       (\<eta>3, Nd n3 [])])]) in
              (T_fold proc - sz proc - nd proc)"

(*
A potential problem would be that the abstract terms are not explicitly stated
to be non-identical. In this example, the proposed property still hold though.
*)

end