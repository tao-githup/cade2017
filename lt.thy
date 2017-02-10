theory lt
imports Main     "quantum_hoare_logic"
begin
ML
{*
fun translate t =
  let
    fun trans t =
      (case t of
      Free (n,@{typ Mat })=>
        Buffer.add n
       | @{term "op \<Longrightarrow>:: prop \<Rightarrow> prop \<Rightarrow> prop"} $ t $ u  =>  
        Buffer.add "#" #>(* ( *)
        trans t #>
        Buffer.add " \<Rightarrow> " #>
        trans u #>
        Buffer.add "@"
       | @{term "op \<in>:: Mat \<Rightarrow> Mat set \<Rightarrow> bool"} $ t $ u  =>  
        Buffer.add "#" #>(* ( *)
        trans t #>
        Buffer.add " in " #>
        trans u #>
        Buffer.add "@"
       | @{term "less::Mat\<Rightarrow>Mat\<Rightarrow>bool"}$t $u=>
        Buffer.add "order#"#>
        trans u#>
         Buffer.add ","#>
        trans t#>
         Buffer.add "@"
       | Free (n,@{typ bool})=>
        Buffer.add n
     | @{prop "less zero a"}   =>  
        Buffer.add "less zero a"
      | _ =>Buffer.add "1")  (*error "inacceptable term ")*)
  in Buffer.content (trans t Buffer.empty) 
end;


fun translate1 t =
  let
    fun trans t =
      (case t of
       @{term "op = :: Mat\<Rightarrow>Mat\<Rightarrow>bool"} $ t $ u  =>
           Buffer.add "check_I#"#>
           trans t#>
           Buffer.add "@"
       | @{term " sum_1 :: nat list \<Rightarrow> nT \<Rightarrow> Mat"} $ t $ u  =>  
        Buffer.add "I" 
       | @{term " sum_2 :: nat list \<Rightarrow> nT \<Rightarrow> Mat"} $ t $ u  =>  
        Buffer.add "I" 
     | @{term " wellDefined ::com\<Rightarrow>bool"} $ t  =>  
        Buffer.add "0" 
      | @{term " mat_add :: Mat \<Rightarrow> Mat \<Rightarrow> Mat"} $ t $ u  =>  
        Buffer.add "#" #>(* ( *)
        trans t #>
        Buffer.add "+" #>
        trans u #>
        Buffer.add "@"(* ) *)
      | @{term " matsum::nat\<Rightarrow>nat\<Rightarrow>Mat\<Rightarrow>Mat"}$t $u $ v =>
         Buffer.add "matsum#" #>
         trans u#>
         Buffer.add ","#>
         trans v#>
         Buffer.add"@"
      | @{term "matUtrans::Mat\<Rightarrow>nat\<Rightarrow>Mat\<Rightarrow>Mat"}$t $u $v=>
         Buffer.add "matUtrans#"#>
         trans t#>
         Buffer.add ","#>
         trans u#>
         Buffer.add ","#>
         trans v#>
         Buffer.add"@"
      | @{term "less::Mat\<Rightarrow>Mat\<Rightarrow>bool"}$t $u=>
        Buffer.add "order#"#>
        trans u#>
         Buffer.add ","#>
        trans t#>
         Buffer.add "@"
      | @{term " mat_mult :: Mat \<Rightarrow> Mat \<Rightarrow> Mat"} $ t $ u  =>  
        trans t #>
        Buffer.add ".dot#" #>
        trans u #>
        Buffer.add "@"
      | @{term " dag :: Mat \<Rightarrow> Mat"} $ t  =>  
        Buffer.add "adjoint#" #>
        trans t #>
        Buffer.add "@"
      | @{term " Suc :: nat \<Rightarrow>nat"} $ t  =>  
        Buffer.add "1" 
      | @{term " 0 :: nat"}  =>  
        Buffer.add "0"
      | @{term " 1 :: nat"}  =>  
        Buffer.add "1"
      | @{term " 2 :: nat"}  =>  
        Buffer.add "2"
      | @{term " 3 :: nat"}  =>  
        Buffer.add "3"
      | @{term " 4 :: nat"}  =>  
        Buffer.add "4"
      | @{term " 5 :: nat"}  =>  
        Buffer.add "5"
      | @{term " 6 :: nat"}  =>  
        Buffer.add "6"
      | @{term " 7 :: nat"}  =>  
        Buffer.add "7"
      | @{term " 8 :: nat"}  =>  
        Buffer.add "8"
      | @{term " 9 :: nat"}  =>  
        Buffer.add "9"
      | @{term " 10 :: nat"}  =>  
        Buffer.add "10"
      | @{term " zero :: Mat"}  =>  
        Buffer.add "mat0"
      | @{term " I:: Mat"}  =>  
        Buffer.add "I"
       |  @{term "positive :: Mat\<Rightarrow>bool"} $ t   =>
           Buffer.add "check#"#>
           trans t#>
           Buffer.add ",rho"#>
           Buffer.add "@"
      |  @{term "UMat :: Mat\<Rightarrow>bool"} $ t   =>
           Buffer.add "check#"#>
           trans t#>
           Buffer.add ",uMat"#>
           Buffer.add "@"
      | Free (n,@{typ int})=>
        Buffer.add n
      | Free (n,@{typ nat})=>
        Buffer.add n
      | Free (n,@{typ string})=>
        Buffer.add n
      | Free (n,@{typ bool})=>
        Buffer.add n
      | Free (n,@{typ Mat })=>
        Buffer.add n
      | _ =>  Buffer.add "error") (*error "inacceptable term tao")*)
  in Buffer.content (trans t Buffer.empty) 
end;
fun isTrue x = 
      if x="True\n" then true
      else false   
fun decide p = "~/quantum.py"^" "^p^""
    |> Isabelle_System.bash_output
    |>fst
    |> isTrue;

*}
oracle quantum_oracle = {* fn ct =>
  if decide   (translate1 (HOLogic.dest_Trueprop (Thm.term_of ct)))   
  then ct
  else error "Proof failed."*}

ML{*

  (translate1 @{term " Matrix.less I
     (matsum 2 0
       (matsum 2 (Suc 0) (matsum 2 2 (matsum 4 3 (matUtrans Delta 2 (matUtrans H 0 (matUtrans H (Suc 0) (matUtrans H 2 zero)))))))) "});




val quantum_oracle_tac =
  CSUBGOAL (fn (goal, i) =>
  (case try quantum_oracle goal of
    NONE => no_tac
  | SOME thm => rtac thm i))
*}
method_setup quantum_oracle = {*
  Scan.succeed (K (Method.SIMPLE_METHOD' quantum_oracle_tac))
*} 
end​
