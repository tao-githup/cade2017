theory temp
imports Main   
begin
ML
{*
fun translate t =
  let
    fun trans t =
      (case t of
      @{term "\<forall>a.\<forall>b. positive a\<longrightarrow>positive b\<longrightarrow>positive (mat_add a b)"}   =>  
        Buffer.add "0"
      | _ =>Buffer.add "error") 
  in Buffer.content (trans t Buffer.empty) 
end;
fun isTrue x = 
      if x="True\n" then true
      else false   
fun decide p = "~/mat.py"^" "^p^""
    |> Isabelle_System.bash_output
    |>fst
    |> isTrue;
*}
oracle mat_oracle = {* fn ct =>
  if decide   (translate (HOLogic.dest_Trueprop (Thm.term_of ct)))   
  then ct
  else error "Proof failed.."*}
oracle mat = {* fn ct =>
  if true 
  then ct
  else error "Proof failed.."*}
ML{*
val mat_oracle_tac =
  CSUBGOAL (fn (goal, i) =>
  (case try mat_oracle goal of
    NONE => no_tac
  | SOME thm => rtac thm i))
  
  val mat_tac =
  CSUBGOAL (fn (goal, i) =>
  (case try mat goal of
    NONE => no_tac
  | SOME thm => rtac thm i))
*}
method_setup mat_oracle = {*
  Scan.succeed (K (Method.SIMPLE_METHOD' mat_oracle_tac))
*} 
method_setup mat = {*
  Scan.succeed (K (Method.SIMPLE_METHOD' mat_tac))
*} 
end​
